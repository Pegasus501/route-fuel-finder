#!/usr/bin/env python3
"""Route fuel finder: finds fuel stations (E85, diesel, SP95, SP95-E10, SP98) along a car route in France.

Data sources (all free, no API key):
  - Prices + stock outages: official French government feed (prix-carburants, "instantane_ruptures"), refreshed every 10 min
  - Geocoding:   api-adresse.data.gouv.fr
  - Routing:     IGN Géoplateforme (fallback: OSRM public server)

Serves HTTP and HTTPS on the same port (auto-detected per connection). If a certificate is present in
certs/, plain-HTTP requests for DOMAIN are redirected to HTTPS. A second small listener (ACME_PORT)
answers Let's Encrypt challenges for certificate renewal.
"""
import bisect
import ipaddress
import re
import io
import json
import math
import os
import socket
import ssl
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from zoneinfo import ZoneInfo

import ev

PORT = int(os.environ.get("PORT", "8085"))
ACME_PORT = int(os.environ.get("ACME_PORT", "8086"))
DOMAIN = os.environ.get("DOMAIN", "")   # your public hostname, e.g. myname.freeboxos.fr (enables http->https redirect)
HERE = os.path.dirname(os.path.abspath(__file__))
STATIC = os.path.join(HERE, "static")
ACME_ROOT = os.path.join(HERE, "acme-webroot")
CERT = os.path.join(HERE, "certs", "fullchain.pem")
KEY = os.path.join(HERE, "certs", "key.pem")
CACHE_FILE = os.path.join(HERE, "cache", "instantane_ruptures.zip")
FEED_URL = "https://donnees.roulez-eco.fr/opendata/instantane_ruptures"
REFRESH_SECONDS = 600
UA = {"User-Agent": "route-fuel-finder/2.0"}
PARIS = ZoneInfo("Europe/Paris")
FUELS = {"E85", "Gazole", "SP95", "E10", "SP98"}


def _config():
    """Optional local settings in config.json (not committed), e.g. {"tomtom_key": "..."}."""
    try:
        with open(os.path.join(HERE, "config.json")) as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


TOMTOM_KEY = os.environ.get("TOMTOM_KEY") or _config().get("tomtom_key", "")

# "SP95E10" = either SP95 or SP95-E10, whichever the station has in stock at the best price
COMBINED = {"SP95E10": ("E10", "SP95")}
FUEL_CHOICES = FUELS | set(COMBINED)

# EV charging: a "fuel" written EV:<min kW>:<plug>, e.g. EV:50:CCS (plug "" = any)
EV = ev.EVData(os.path.join(HERE, "cache"), UA, os.path.join(HERE, "ev_prices.json"))


def valid_choice(fuel):
    if fuel in FUEL_CHOICES:
        return True
    parts = fuel.split(":")
    return len(parts) == 3 and parts[0] == "EV" and parts[1].isdigit() and parts[2] in ("", "CCS", "Type 2", "CHAdeMO", "EF")


def choice_from(q):
    fuel = q.get("fuel", ["E85"])[0]
    if fuel == "EV":
        fuel = "EV:%d:%s" % (int(float(q.get("minkw", ["0"])[0] or 0)), q.get("plug", [""])[0])
    return fuel


def get_station(sid):
    with _lock:
        found = _stations.get(sid)
    return found if found is not None else EV.stations.get(sid)


ADDR_RX = re.compile(r"(\d{5}),?\s*([^,\d][^,]*)$")


def ev_view(g, manual):
    price, src = EV.price_of(g, manual)
    m = ADDR_RX.search(g["address"])
    st = {"id": g["id"], "lat": g["lat"], "lon": g["lon"], "address": ADDR_RX.sub("", g["address"]).strip(" ,") or g["address"],
          "cp": m.group(1) if m else "", "city": (m.group(2).strip().title() if m else ""), "motorway": g["motorway"],
          "h24": g["hours"] in ("24/7", "Mo-Su 00:00-23:59"), "ev": True, "kw": g["kw"], "plugs": g["plugs"], "cb": g["cb"],
          "free": g["free"], "operator": g["operator"], "network": g["network"], "chain": g["chain"], "tarif": g["tarif"],
          "price": price, "price_src": src, "status": EV.status_of(g), "npdc": len(g["pdc"]),
          "brand": g["chain"] or g["network"] or None, "name": g["name"] or None}
    if g["updated"]:
        st["updated"] = g["updated"] + "T12:00:00+00:00"
    stt = st["status"]
    if stt and stt["known"] and stt["oos"] == stt["known"]:
        st["out_since"] = stt["at"]            # every charge point reported out of service
    return st


def candidates(fuel):
    """(raw station, view-maker) for every station offering this choice."""
    if fuel.startswith("EV:"):
        _, minkw, plug = fuel.split(":")
        minkw = float(minkw)
        manual = EV.manual_prices()
        with EV.lock:
            stations = list(EV.stations.values())
        return [(g, (lambda g=g: ev_view(g, manual))) for g in stations
                if g["kw"] >= minkw and (not plug or plug in g["plugs"])]
    with _lock:
        stations = list(_stations.values())
    out = []
    for s in stations:
        f = fuel_info(s, fuel)
        if f:
            out.append((s, (lambda s=s, f=f: station_view(s, f))))
    return out


def fuel_info(s, fuel):
    if fuel not in COMBINED:
        return s["fuels"].get(fuel)
    opts = [(name, s["fuels"][name]) for name in COMBINED[fuel] if name in s["fuels"]]
    if not opts:
        return None

    def rank(o):
        f = o[1]
        in_stock = f.get("price") is not None and not (f.get("out_since") and not f.get("maybe_restocked"))
        try:
            fresh = time.time() - datetime.fromisoformat(f["updated"]).timestamp() <= 7 * 86400
        except (KeyError, TypeError, ValueError):
            fresh = False
        return (not in_stock, not fresh, f.get("price") if f.get("price") is not None else 99)

    opts.sort(key=rank)
    best = dict(opts[0][1], variant=opts[0][0])
    if len(opts) > 1 and opts[1][1].get("price") is not None:
        o = opts[1][1]
        best["other"] = {"variant": opts[1][0], "price": o["price"],
                         "out": bool(o.get("out_since") and not o.get("maybe_restocked"))}
    return best

_stations = {}          # id -> station dict
_stations_loaded_at = 0.0
_lock = threading.Lock()


# ================================================================ fuel feed
def iso(paris_local):
    """Feed timestamps are Paris local time -> ISO 8601 with offset."""
    try:
        return datetime.strptime(paris_local, "%Y-%m-%d %H:%M:%S").replace(tzinfo=PARIS).isoformat()
    except (TypeError, ValueError):
        return None


def parse_feed(zip_bytes):
    z = zipfile.ZipFile(io.BytesIO(zip_bytes))
    root = ET.fromstring(z.read(z.namelist()[0]))
    out = {}
    for pdv in root.iter("pdv"):
        try:
            lat = float(pdv.get("latitude")) / 100000
            lon = float(pdv.get("longitude")) / 100000
        except (TypeError, ValueError):
            continue
        if not (41 < lat < 52 and -6 < lon < 10):   # metropolitan France only
            continue
        prices = {}
        for p in pdv.findall("prix"):
            name = p.get("nom")
            if name in FUELS:
                try:
                    v = float(p.get("valeur"))
                except (TypeError, ValueError):
                    continue
                prices[name] = (v / 1000 if v > 10 else v, p.get("maj") or "")
        fuels = {}
        ruptures = {r.get("nom"): r for r in pdv.findall("rupture") if r.get("nom") in FUELS and not r.get("fin")}
        for name in FUELS:
            pr, ru = prices.get(name), ruptures.get(name)
            info = {}
            if pr:
                info.update(price=round(pr[0], 3), updated=iso(pr[1]))
            if ru is not None:
                since = ru.get("debut") or ""
                price_is_newer = pr is not None and pr[1] > since
                if ru.get("type") == "definitive" and not price_is_newer:
                    continue                      # station no longer sells this fuel
                if ru.get("type") == "temporaire":
                    if not price_is_newer and since and since < (datetime.now(PARIS) - timedelta(days=30)).strftime("%Y-%m-%d %H:%M:%S"):
                        continue                  # "temporary" outage for over a month: effectively not sold here
                    info["out_since"] = iso(since)
                    info["maybe_restocked"] = price_is_newer
            if info:
                fuels[name] = info
        if not fuels:
            continue
        h = pdv.find("horaires")
        sid = pdv.get("id")
        out[sid] = {
            "id": sid, "lat": lat, "lon": lon,
            "address": (pdv.findtext("adresse") or "").strip(),
            "city": (pdv.findtext("ville") or "").strip().title(),
            "cp": pdv.get("cp"),
            "motorway": pdv.get("pop") == "A",
            "h24": h is not None and h.get("automate-24-24") == "1",
            "fuels": fuels,
        }
    return out


def refresh_feed():
    global _stations, _stations_loaded_at
    try:
        data = urllib.request.urlopen(urllib.request.Request(FEED_URL, headers=UA), timeout=90).read()
        stations = parse_feed(data)
        os.makedirs(os.path.dirname(CACHE_FILE), exist_ok=True)
        with open(CACHE_FILE + ".tmp", "wb") as f:
            f.write(data)
        os.replace(CACHE_FILE + ".tmp", CACHE_FILE)
        with _lock:
            _stations, _stations_loaded_at = stations, time.time()
        print(f"[feed] {len(stations)} stations loaded", flush=True)
    except Exception as e:
        print(f"[feed] refresh failed: {e}", flush=True)


def feed_loop():
    global _stations, _stations_loaded_at
    if os.path.exists(CACHE_FILE):   # start from disk cache so the site works right after a reboot
        try:
            with open(CACHE_FILE, "rb") as f:
                _stations = parse_feed(f.read())
            _stations_loaded_at = os.path.getmtime(CACHE_FILE)
        except Exception as e:
            print(f"[feed] cache unreadable: {e}", flush=True)
    while True:
        if time.time() - _stations_loaded_at > REFRESH_SECONDS - 5:
            refresh_feed()
        time.sleep(60)


# ================================================================ brands (OpenStreetMap)
OSM_FILE = os.path.join(HERE, "cache", "osm_fuel.json")
OSM_REFRESH = 7 * 86400
OVERPASS = ["https://overpass-api.de/api/interpreter", "https://overpass.kumi.systems/api/interpreter"]
OVERPASS_Q = '[out:json][timeout:600];area["ISO3166-1"="FR"][admin_level=2]->.fr;nwr["amenity"="fuel"](area.fr);out center tags;'
_brands = {}            # station id -> {"brand":..., "name":...}


def build_brand_index(osm):
    """Match government station ids to OSM fuel stations: exact ref:FR:prix-carburants tag, else nearest within 150 m."""
    by_ref, grid = {}, {}
    for el in osm.get("elements", []):
        tags = el.get("tags", {})
        lat = el.get("lat", el.get("center", {}).get("lat"))
        lon = el.get("lon", el.get("center", {}).get("lon"))
        brand = (tags.get("brand") or "").strip()
        name = (tags.get("name") or "").strip()
        if lat is None or not (brand or name):
            continue
        info = {"brand": brand or None, "name": name or None}
        for ref in (tags.get("ref:FR:prix-carburants") or "").split(";"):
            if ref.strip():
                by_ref[ref.strip()] = info
        grid.setdefault((round(lat * 100), round(lon * 100)), []).append((lat, lon, info))
    with _lock:
        stations = list(_stations.values())
    out, exact = {}, 0
    for s in stations:
        if s["id"] in by_ref:
            out[s["id"]] = by_ref[s["id"]]
            exact += 1
            continue
        gy, gx = round(s["lat"] * 100), round(s["lon"] * 100)
        best = None
        for dy in (-1, 0, 1):
            for dx in (-1, 0, 1):
                for lat, lon, info in grid.get((gy + dy, gx + dx), ()):
                    d = math.hypot((lat - s["lat"]) * 111.0, (lon - s["lon"]) * 111.0 * math.cos(math.radians(lat)))
                    if d < 0.15 and (best is None or d < best[0]):
                        best = (d, info)
        if best:
            out[s["id"]] = best[1]
    print(f"[brands] matched {len(out)}/{len(stations)} stations ({exact} by exact id)", flush=True)
    return out


def brands_loop():
    global _brands
    while not _stations:
        time.sleep(5)
    while True:
        age = time.time() - os.path.getmtime(OSM_FILE) if os.path.exists(OSM_FILE) else 1e12
        if age > OSM_REFRESH:
            for url in OVERPASS:
                try:
                    data = urllib.parse.urlencode({"data": OVERPASS_Q}).encode()
                    raw = urllib.request.urlopen(urllib.request.Request(url, data=data, headers=UA), timeout=900).read()
                    json.loads(raw)
                    with open(OSM_FILE + ".tmp", "wb") as f:
                        f.write(raw)
                    os.replace(OSM_FILE + ".tmp", OSM_FILE)
                    print("[brands] OpenStreetMap fuel stations downloaded", flush=True)
                    break
                except Exception as e:
                    print(f"[brands] download from {url} failed: {e}", flush=True)
        try:
            if os.path.exists(OSM_FILE):
                with open(OSM_FILE) as f:
                    _brands = build_brand_index(json.load(f))
        except Exception as e:
            print(f"[brands] cannot read OSM data: {e}", flush=True)
        time.sleep(6 * 3600)   # re-match periodically (new stations appear in the price feed)


# ================================================================ external APIs
_prio = threading.local()       # .high = True on threads doing user-visible priority work (Ideal stops)


class RateLimiter:
    def __init__(self, per_second):
        self.interval, self.next, self.lock = 1.0 / per_second, 0.0, threading.Lock()
        self.high_waiting = 0

    def wait(self):
        high = getattr(_prio, "high", False)
        if high:
            with self.lock:
                self.high_waiting += 1
        else:
            while self.high_waiting > 0:          # background work yields to priority requests
                time.sleep(0.05)
        try:
            self._wait()
        finally:
            if high:
                with self.lock:
                    self.high_waiting -= 1

    def _wait(self):
        with self.lock:
            now = time.monotonic()
            t = max(now, self.next)
            self.next = t + self.interval
        if t > now:
            time.sleep(t - now)


IGN_LIMIT = RateLimiter(4)
OSRM_LIMIT = RateLimiter(1)


def get_json(url, timeout=30):
    return json.loads(urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=timeout).read())


def geocode(q, limit=5):
    url = "https://api-adresse.data.gouv.fr/search/?" + urllib.parse.urlencode({"q": q, "limit": limit})
    return [_feat(f) for f in get_json(url, 10).get("features", [])]


def reverse(lon, lat):
    url = "https://api-adresse.data.gouv.fr/reverse/?" + urllib.parse.urlencode({"lon": lon, "lat": lat, "limit": 1})
    feats = get_json(url, 10).get("features", [])
    return _feat(feats[0]) if feats else None


def _feat(f):
    p = f["properties"]
    label = p["label"] + (f" ({p.get('postcode', '')})" if p.get("type") == "municipality" else "")
    return {"label": label, "lon": f["geometry"]["coordinates"][0], "lat": f["geometry"]["coordinates"][1]}


def ign_route(points, steps):
    params = {
        "resource": "bdtopo-osrm", "profile": "car", "optimization": "fastest",
        "start": "%.6f,%.6f" % points[0], "end": "%.6f,%.6f" % points[-1],
        "geometryFormat": "geojson", "getSteps": "true" if steps else "false",
        "distanceUnit": "meter", "timeUnit": "second",
    }
    if len(points) > 2:
        params["intermediates"] = "|".join("%.6f,%.6f" % p for p in points[1:-1])
    url = "https://data.geopf.fr/navigation/itineraire?" + urllib.parse.urlencode(params)
    for attempt in range(4):
        IGN_LIMIT.wait()
        try:
            return get_json(url, 45)
        except urllib.error.HTTPError as e:
            if e.code != 429 or attempt == 3:
                raise
            time.sleep(1.0 + attempt)


def osrm_route(points, annotations):
    OSRM_LIMIT.wait()
    coords = ";".join("%.6f,%.6f" % p for p in points)
    extra = "&annotations=duration" if annotations else ""
    return get_json(f"https://router.project-osrm.org/route/v1/driving/{coords}?overview=full&geometries=geojson{extra}", 45)["routes"][0]


def full_route(points):
    """Returns dict(coords, tcum [s at each vertex], distance, duration, router)."""
    try:
        r = ign_route(points, steps=True)
        coords, tcum = [], []
        t = 0.0
        for portion in r["portions"]:
            for st in portion["steps"]:
                g = st["geometry"]["coordinates"]
                if len(g) < 2:
                    t += st.get("duration", 0)
                    continue
                seg = [math.dist(g[i], g[i + 1]) for i in range(len(g) - 1)]
                total = sum(seg) or 1.0
                if not coords:
                    coords.append(g[0]); tcum.append(t)
                acc = t
                for i in range(len(seg)):
                    acc += st["duration"] * seg[i] / total
                    coords.append(g[i + 1]); tcum.append(acc)
                t += st["duration"]
        if len(coords) < 2:
            raise ValueError("empty IGN geometry")
        return {"coords": coords, "tcum": tcum, "distance": r["distance"], "duration": r["duration"], "router": "IGN"}
    except Exception as e:
        print(f"[route] IGN failed ({e}), trying OSRM", flush=True)
    rt = osrm_route(points, annotations=True)
    coords, tcum, t = rt["geometry"]["coordinates"], [0.0], 0.0
    for leg in rt["legs"]:
        for d in leg["annotation"]["duration"]:
            t += d
            tcum.append(t)
    tcum = (tcum + [t] * len(coords))[:len(coords)]
    return {"coords": coords, "tcum": tcum, "distance": rt["distance"], "duration": rt["duration"], "router": "OSRM"}


def via_route(points):
    """(duration_s, distance_m, coords) for a route through points."""
    try:
        r = ign_route(points, steps=False)
        return r["duration"], r["distance"], r["geometry"]["coordinates"]
    except Exception as e:
        print(f"[detour] IGN failed ({e}), trying OSRM", flush=True)
        rt = osrm_route(points, annotations=False)
        return rt["duration"], rt["distance"], rt["geometry"]["coordinates"]


# ================================================================ geometry
class RouteIndex:
    """Route projected to local km coordinates, with a grid index of segments."""

    def __init__(self, route):
        self.route = route
        coords = route["coords"]
        lat0 = sum(c[1] for c in coords) / len(coords)
        self.kx, self.ky = 111.320 * math.cos(math.radians(lat0)), 110.574
        self.pts = [(c[0] * self.kx, c[1] * self.ky) for c in coords]
        self.cum = [0.0]
        for i in range(1, len(self.pts)):
            self.cum.append(self.cum[-1] + math.dist(self.pts[i - 1], self.pts[i]))
        self.cell = 2.0
        self.grid = {}
        for i in range(len(self.pts) - 1):
            (x1, y1), (x2, y2) = self.pts[i], self.pts[i + 1]
            for gx in range(int(math.floor(min(x1, x2) / self.cell)), int(math.floor(max(x1, x2) / self.cell)) + 1):
                for gy in range(int(math.floor(min(y1, y2) / self.cell)), int(math.floor(max(y1, y2) / self.cell)) + 1):
                    self.grid.setdefault((gx, gy), []).append(i)

    def nearest(self, lon, lat, max_km):
        px, py = lon * self.kx, lat * self.ky
        gx, gy = int(math.floor(px / self.cell)), int(math.floor(py / self.cell))
        r = int(math.ceil(max_km / self.cell))
        best = None
        seen = set()
        for dx in range(-r, r + 1):
            for dy in range(-r, r + 1):
                for i in self.grid.get((gx + dx, gy + dy), ()):
                    if i in seen:
                        continue
                    seen.add(i)
                    (x1, y1), (x2, y2) = self.pts[i], self.pts[i + 1]
                    vx, vy = x2 - x1, y2 - y1
                    L2 = vx * vx + vy * vy
                    t = 0.0 if L2 == 0 else max(0.0, min(1.0, ((px - x1) * vx + (py - y1) * vy) / L2))
                    d = math.hypot(px - (x1 + t * vx), py - (y1 + t * vy))
                    if best is None or d < best[0]:
                        cross = vx * (py - y1) - vy * (px - x1)     # > 0: station is left of travel direction
                        best = (d, i, t, cross)
        if best is None or best[0] > max_km:
            return None
        d, i, t, cross = best
        along = self.cum[i] + t * (self.cum[i + 1] - self.cum[i])
        seg_km = self.cum[i + 1] - self.cum[i]
        seg_s = self.route["tcum"][i + 1] - self.route["tcum"][i]
        speed = seg_km / seg_s * 3600 if seg_s > 0 else 0
        return {"off_km": d, "along_km": along, "left": cross > 0, "speed_kmh": speed}

    def point_at(self, along_km):
        """(lon, lat, time_s) at a distance along the route."""
        along_km = max(0.0, min(along_km, self.cum[-1]))
        i = max(0, min(bisect.bisect_right(self.cum, along_km) - 1, len(self.cum) - 2))
        L = self.cum[i + 1] - self.cum[i]
        f = 0.0 if L == 0 else (along_km - self.cum[i]) / L
        c, tc = self.route["coords"], self.route["tcum"]
        return (c[i][0] + f * (c[i + 1][0] - c[i][0]), c[i][1] + f * (c[i + 1][1] - c[i][1]),
                tc[i] + f * (tc[i + 1] - tc[i]))


def simplify(coords, max_points=3000):
    if len(coords) <= max_points:
        return coords
    step = len(coords) / max_points
    return [coords[int(i * step)] for i in range(max_points)] + [coords[-1]]


# ================================================================ tolls (IGN pgRouting engine exposes "acces_vehicule_leger" = "A péage")
class TollIndex:
    """Toll / free status of the roads of a route, looked up by position."""

    def __init__(self, segments):
        self.cell = 0.01          # degrees
        self.grid = {}
        for (x1, y1), (x2, y2), toll in segments:
            for gx in range(int(math.floor(min(x1, x2) / self.cell)), int(math.floor(max(x1, x2) / self.cell)) + 1):
                for gy in range(int(math.floor(min(y1, y2) / self.cell)), int(math.floor(max(y1, y2) / self.cell)) + 1):
                    self.grid.setdefault((gx, gy), []).append(((x1, y1), (x2, y2), toll))

    def is_toll(self, lon, lat, max_km=0.3):
        kx = 111.32 * math.cos(math.radians(lat))
        gx, gy = int(math.floor(lon / self.cell)), int(math.floor(lat / self.cell))
        best = None
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for (x1, y1), (x2, y2), toll in self.grid.get((gx + dx, gy + dy), ()):
                    ax, ay, bx, by = (x1 - lon) * kx, (y1 - lat) * 110.574, (x2 - lon) * kx, (y2 - lat) * 110.574
                    vx, vy = bx - ax, by - ay
                    L2 = vx * vx + vy * vy
                    t = 0.0 if L2 == 0 else max(0.0, min(1.0, -(ax * vx + ay * vy) / L2))
                    d = math.hypot(ax + t * vx, ay + t * vy)
                    if d <= max_km and (best is None or d < best[0]):
                        best = (d, toll)
        return bool(best and best[1])


def build_toll_index(points):
    params = {
        "resource": "bdtopo-pgr", "profile": "car", "optimization": "fastest",
        "start": "%.6f,%.6f" % points[0], "end": "%.6f,%.6f" % points[-1],
        "geometryFormat": "geojson", "getSteps": "true", "waysAttributes": "acces_vehicule_leger",
    }
    if len(points) > 2:
        params["intermediates"] = "|".join("%.6f,%.6f" % p for p in points[1:-1])
    IGN_LIMIT.wait()
    r = get_json("https://data.geopf.fr/navigation/itineraire?" + urllib.parse.urlencode(params, safe="|,"), 90)
    segs = []
    for portion in r["portions"]:
        for st in portion["steps"]:
            toll = st.get("attributes", {}).get("acces_vehicule_leger") == "A péage"
            g = st["geometry"]["coordinates"]
            segs.extend((tuple(g[i]), tuple(g[i + 1]), toll) for i in range(len(g) - 1))
    return TollIndex(segs)


# ================================================================ live traffic (optional, TomTom free tier)
def tomtom_route(points):
    """Route with live traffic. points: [(lon, lat)...]. Returns dict or raises."""
    if not tomtom_allow():
        raise RuntimeError("TomTom daily cap reached")
    locs = ":".join("%.6f,%.6f" % (lat, lon) for lon, lat in points)
    params = {"key": TOMTOM_KEY, "traffic": "true", "travelMode": "car", "routeType": "fastest",
              "sectionType": "traffic", "computeTravelTimeFor": "all", "departAt": "now"}
    r = get_json(f"https://api.tomtom.com/routing/1/calculateRoute/{locs}/json?" + urllib.parse.urlencode(params), 30)
    rt = r["routes"][0]
    pts = [[p["longitude"], p["latitude"]] for leg in rt["legs"] for p in leg["points"]]
    jams = []
    for s in rt.get("sections", []):
        if s.get("sectionType") == "TRAFFIC":
            seg = pts[s["startPointIndex"]:s["endPointIndex"] + 1]
            jams.append({"coords": simplify(seg, 300), "delay_s": s.get("delayInSeconds", 0),
                         "kind": s.get("simpleCategory", "OTHER"), "speed": s.get("effectiveSpeedInKmh")})
    sm = rt["summary"]
    return {"duration_s": sm["travelTimeInSeconds"], "delay_s": sm.get("trafficDelayInSeconds", 0),
            "no_traffic_s": sm.get("noTrafficTravelTimeInSeconds"), "distance_m": sm["lengthInMeters"], "jams": jams}


_bg_pool = ThreadPoolExecutor(4)


# ================================================================ trip cache
class Trip:
    def __init__(self, key, points):
        self.key, self.points = key, points
        self.route = full_route(points)
        self.index = RouteIndex(self.route)
        self.detours = {}            # station id -> dict
        self.created = time.time()
        self.tolls = _bg_pool.submit(build_toll_index, points)
        self.traffic = _bg_pool.submit(tomtom_route, points) if TOMTOM_KEY else None
        self.traffic_via = {}        # station id -> seconds with traffic via that station
        self.alts = None             # alternative routes (computed on demand)
        self.detour_geom = {}        # station id -> geometry of the trip through that station
        self.main_toll_km = None
        self.lock = threading.Lock()

    def exits_toll(self, s, tolls):
        """True if stopping at s means leaving a toll motorway (and paying to get back on)."""
        if s["motorway"]:
            return False          # motorway service area: stays on the toll road
        n = self.index.nearest(s["lon"], s["lat"], 30)
        if n is None:
            return False
        a = self.index.point_at(n["along_km"] - 1.5)
        b = self.index.point_at(n["along_km"] + 1.5)
        return tolls.is_toll(a[0], a[1]) and tolls.is_toll(b[0], b[1])


_trips = OrderedDict()
_trips_lock = threading.Lock()


def get_trip(points):
    key = "|".join("%.5f,%.5f" % p for p in points)
    with _trips_lock:
        if key in _trips:
            _trips.move_to_end(key)
            return _trips[key]
    trip = Trip(key, points)
    with _trips_lock:
        _trips[key] = trip
        while len(_trips) > 30:
            _trips.popitem(last=False)
    return trip


def find_trip(key):
    with _trips_lock:
        return _trips.get(key)


def station_view(s, fuel_info):
    st = {k: s[k] for k in ("id", "lat", "lon", "address", "city", "cp", "motorway", "h24")}
    st.update(fuel_info)
    b = _brands.get(s["id"])
    if b:
        st.update(brand=b["brand"], name=b["name"])
    return st


# ================================================================ nearby search
def crow_km(lon1, lat1, lon2, lat2):
    p1, p2 = math.radians(lat1), math.radians(lat2)
    a = math.sin((p2 - p1) / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(math.radians(lon2 - lon1) / 2) ** 2
    return 12742 * math.asin(math.sqrt(a))


def point_in_ring(x, y, ring):
    inside, j = False, len(ring) - 1
    for i in range(len(ring)):
        xi, yi = ring[i][0], ring[i][1]
        xj, yj = ring[j][0], ring[j][1]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / (yj - yi) + xi:
            inside = not inside
        j = i
    return inside


def point_in_geom(x, y, geom):
    polys = [geom["coordinates"]] if geom["type"] == "Polygon" else geom["coordinates"]
    return any(point_in_ring(x, y, p[0]) and not any(point_in_ring(x, y, h) for h in p[1:]) for p in polys)


def isodistance(lon, lat, km):
    params = {"resource": "bdtopo-valhalla", "point": "%.6f,%.6f" % (lon, lat), "costValue": km, "costType": "distance",
              "distanceUnit": "kilometer", "profile": "car", "direction": "departure", "geometryFormat": "geojson"}
    url = "https://data.geopf.fr/navigation/isochrone?" + urllib.parse.urlencode(params)
    for attempt in range(3):
        IGN_LIMIT.wait()
        try:
            return get_json(url, 60)["geometry"]
        except urllib.error.HTTPError as e:
            if e.code != 429 or attempt == 2:
                raise
            time.sleep(1.5)


class Nearby:
    def __init__(self, key, lon, lat, radius, mode):
        self.key, self.lon, self.lat, self.radius, self.mode = key, lon, lat, radius, mode
        self.area = isodistance(lon, lat, radius) if mode == "drive" else None
        self.drives = {}         # station id -> {"s", "km"} driving time/distance from the centre


_nearby = OrderedDict()


def get_nearby(lon, lat, radius, mode):
    key = "n|%.5f,%.5f|%g|%s" % (lon, lat, radius, mode)
    with _trips_lock:
        if key in _nearby:
            return _nearby[key]
    n = Nearby(key, lon, lat, radius, mode)
    with _trips_lock:
        _nearby[key] = n
        while len(_nearby) > 30:
            _nearby.popitem(last=False)
    return n


def stations_near(nb, fuel):
    out = []
    for s, view in candidates(fuel):
        d = crow_km(nb.lon, nb.lat, s["lon"], s["lat"])
        if d > nb.radius:
            continue          # a driving distance is never shorter than the straight line
        if nb.area is not None and not point_in_geom(s["lon"], s["lat"], nb.area):
            continue
        st = view()
        st["crow_km"] = round(d, 2)
        if s["id"] in nb.drives:
            st["drive"] = nb.drives[s["id"]]
        out.append(st)
    out.sort(key=lambda s: s["crow_km"])
    return out


def compute_drive(nb, sid):
    if sid in nb.drives:
        return nb.drives[sid]
    s = get_station(sid)
    if s is None:
        return None
    dur, dist, _ = via_route([(nb.lon, nb.lat), (s["lon"], s["lat"])])
    nb.drives[sid] = res = {"s": round(dur), "km": round(dist / 1000, 1)}
    return res


def stations_for(trip, fuel, corridor_km):
    out = []
    total_km = trip.index.cum[-1]
    for s, view in candidates(fuel):
        n = trip.index.nearest(s["lon"], s["lat"], corridor_km)
        if n is None:
            continue
        # Motorway service station on the left of a fast stretch = other carriageway: not reachable.
        opposite = s["motorway"] and n["left"] and n["off_km"] < 1.0 and n["speed_kmh"] > 80
        st = view()
        st.update(off_route_km=round(n["off_km"], 2), along_km=round(n["along_km"], 1), opposite=opposite,
                  at_s=round(trip.index.point_at(n["along_km"])[2]),
                  pct=round(n["along_km"] / total_km, 4) if total_km else 0)
        if s["id"] in trip.detours:
            st["detour"] = trip.detours[s["id"]]
        out.append(st)
    out.sort(key=lambda s: s["along_km"])
    return out


def compute_detour(trip, sid):
    """Added time/distance = (whole trip start -> station -> destination) - (fastest direct route).
    The route through the station is free to take any path, so this is exact even far from the main route."""
    if sid in trip.detours:
        return trip.detours[sid]
    s = get_station(sid)
    if s is None:
        return None
    dur, dist, coords = via_route(points_via(trip, s))
    res = {"s": max(0, round(dur - trip.route["duration"])), "km": round(max(0.0, (dist - trip.route["distance"]) / 1000), 1)}
    trip.detour_geom[sid] = simplify(coords, 1500)
    trip.detours[sid] = res
    return res


_detour_pool = ThreadPoolExecutor(6)
_ideal_pool = ThreadPoolExecutor(6)


def _high(fn, *args):
    _prio.high = True
    try:
        return fn(*args)
    finally:
        _prio.high = False


def is_usable(st, max_age_days=7):
    """In stock, has a recent price, reachable in the direction of travel."""
    if st.get("price") is None or st.get("opposite"):
        return False
    if st.get("out_since") and not st.get("maybe_restocked"):
        return False
    if st.get("ev"):
        return True
    try:
        age = time.time() - datetime.fromisoformat(st["updated"]).timestamp()
    except (TypeError, ValueError, KeyError):
        return False
    return age <= max_age_days * 86400


# ================================================================ alternative routes
def _route_coords_tomtom(points):
    if not tomtom_allow():
        raise RuntimeError("TomTom daily cap reached")
    locs = ":".join("%.6f,%.6f" % (lat, lon) for lon, lat in points)
    params = {"key": TOMTOM_KEY, "maxAlternatives": 3, "alternativeType": "anyRoute", "traffic": "true",
              "travelMode": "car", "routeType": "fastest"}
    r = get_json(f"https://api.tomtom.com/routing/1/calculateRoute/{locs}/json?" + urllib.parse.urlencode(params), 30)
    return [[[p["longitude"], p["latitude"]] for leg in rt["legs"] for p in leg["points"]] for rt in r["routes"][1:]]


def _route_coords_osrm(points):
    OSRM_LIMIT.wait()
    coords = ";".join("%.6f,%.6f" % p for p in points)
    r = get_json(f"https://router.project-osrm.org/route/v1/driving/{coords}?alternatives=3&overview=full&geometries=geojson", 45)
    return [rt["geometry"]["coordinates"] for rt in r["routes"][1:]]


def _route_coords_forced(trip):
    """Force genuinely different corridors: route through points well to the left and right of the main route's middle."""
    idx = trip.index
    total = idx.cum[-1]
    (sx, sy), (ex, ey) = idx.pts[0], idx.pts[-1]
    dx, dy = ex - sx, ey - sy
    L = math.hypot(dx, dy) or 1.0
    nx, ny = -dy / L, dx / L                        # unit normal (km space)
    off = max(15.0, min(60.0, 0.12 * total))
    out = []
    for frac in (0.5,):
        mx, my, _ = idx.point_at(total * frac)
        for sign in (1, -1):
            lon = mx + sign * nx * off / idx.kx
            lat = my + sign * ny * off / idx.ky
            pts = list(trip.points[:-1]) + [(lon, lat)] + [trip.points[-1]]
            try:
                r = ign_route(pts, steps=False)
                out.append(r["geometry"]["coordinates"])
            except Exception as e:
                print(f"[alt] forced route failed: {e!r}", flush=True)
    return out


def _overlap(coords, indexes, tol_km=1.5):
    """Share of the route (sampled ~every 2 km) lying within tol_km of any of the given routes."""
    lat0 = coords[len(coords) // 2][1]
    kx = 111.32 * math.cos(math.radians(lat0))
    sample, acc, last = [], 0.0, None
    for c in coords:
        if last is not None:
            acc += math.hypot((c[0] - last[0]) * kx, (c[1] - last[1]) * 110.574)
        if last is None or acc >= 2:
            sample.append(c); acc = 0.0
        last = c
    near = sum(1 for c in sample if any(ix.nearest(c[0], c[1], tol_km) for ix in indexes))
    return near / max(1, len(sample))


def alternative_routes(trip, max_alts=3):
    """Genuinely different paths to the destination (each <60% shared with the main route and with each other)."""
    with trip.lock:
        if trip.alts is not None:
            return trip.alts
        cands = []
        sources = ([_route_coords_tomtom] if TOMTOM_KEY else []) + [_route_coords_osrm]
        for src in sources:
            try:
                cands += src(trip.points)
            except Exception as e:
                print(f"[alt] {src.__name__} failed: {e!r}", flush=True)
        kept = []
        def consider(coords):
            if len(coords) < 2 or len(kept) >= max_alts:
                return
            if _overlap(coords, [trip.index] + [k["index"] for k in kept]) < 0.6:
                kept.append({"coords": coords, "index": RouteIndex({"coords": coords, "tcum": [0.0] * len(coords)})})
        for c in cands:
            consider(c)
        if len(kept) < 2:
            for c in _route_coords_forced(trip):
                consider(c)
        for k in kept:
            c = k["coords"]
            mids = [tuple(c[int(len(c) * f)][:2]) for f in (0.25, 0.5, 0.75)]
            try:
                d, dist, _ = via_route([trip.points[0]] + mids + [trip.points[-1]])
                k["duration"], k["distance"] = d, dist
            except Exception as e:
                print(f"[alt] timing failed: {e!r}", flush=True)
                k["duration"] = k["distance"] = None
        trip.alts = kept
        print(f"[alt] {len(cands)} candidate alternatives, kept {len(kept)}", flush=True)
        return kept


compute_full_detour = compute_detour


def ideal_candidates(trip, fuel, band_km, alt_band_km=10):
    """Stations worth checking for the time-vs-price trade-off list: along the main route (up to band_km) AND along
    genuinely different alternative paths (up to alt_band_km). Each gets its real extra trip time."""
    pool = [dict(s, route=0) for s in stations_for(trip, fuel, band_km) if is_usable(s)]
    cheapest = sorted(pool, key=lambda s: s["price"])[:20]
    closest = sorted(pool, key=lambda s: s["off_route_km"])[:8]
    fastest = sorted(pool, key=lambda s: -s.get("kw", 0))[:6] if fuel.startswith("EV:") else []
    chosen = {s["id"]: s for s in cheapest + closest + fastest}
    jobs = {sid: (compute_detour, trip, sid) for sid in chosen}

    _prio.high = True
    try:
        alts = alternative_routes(trip)
    finally:
        _prio.high = False
    in_main = {s["id"] for s in pool}
    cands = candidates(fuel)
    for i, alt in enumerate(alts, start=1):
        found = []
        for s, view in cands:
            if s["id"] in in_main or s["id"] in chosen:
                continue
            n = alt["index"].nearest(s["lon"], s["lat"], alt_band_km)
            if n is None:
                continue
            st = view()
            if not is_usable(st):
                continue
            st.update(route=i, along_km=round(n["along_km"], 1), alt_off_km=round(n["off_km"], 2),
                      off_route_km=None, opposite=False)
            found.append(st)
        for st in sorted(found, key=lambda x: x["price"])[:6]:
            chosen[st["id"]] = st
            jobs[st["id"]] = (compute_full_detour, trip, st["id"])

    futures = {sid: _ideal_pool.submit(_high, *job) for sid, job in jobs.items()}
    out = []
    for sid, f in futures.items():
        try:
            d = f.result(timeout=180)
        except Exception as e:
            print(f"[ideal] {sid}: {e!r}", flush=True)
            continue
        if d is not None:
            out.append(dict(chosen[sid], detour=d))
    return out, [{"coords": simplify(a["coords"], 800), "duration_s": a.get("duration"), "distance_m": a.get("distance")} for a in alts]


def points_via(trip, s):
    """Trip waypoints with the station inserted where it falls along the route."""
    pts = list(trip.points)
    n = trip.index.nearest(s["lon"], s["lat"], 30)
    along = n["along_km"] if n else 0
    pos = len(pts) - 1
    for i in range(1, len(pts) - 1):
        m = trip.index.nearest(pts[i][0], pts[i][1], 50)
        if m and along < m["along_km"]:
            pos = i
            break
    pts.insert(pos, (s["lon"], s["lat"]))
    return pts


TOLL_EUR_PER_KM = 0.11      # average French class-1 (car) toll rate
TOLL_REENTRY_EUR = 1.20     # a new ticket when you get back on: minimum charge + per-ticket rounding


def toll_km(coords, tolls):
    km = 0.0
    for a, b in zip(coords, coords[1:]):
        if tolls.is_toll((a[0] + b[0]) / 2, (a[1] + b[1]) / 2, 0.15):
            km += math.hypot((b[0] - a[0]) * 111.32 * math.cos(math.radians(a[1])), (b[1] - a[1]) * 110.574)
    return km


def toll_estimate(trip, sid, tolls):
    """Extra péage when the stop makes you leave the toll motorway: a re-entry ticket, minus the toll km the detour skips."""
    coords = trip.detour_geom.get(sid)
    if coords is None:
        return None
    if trip.main_toll_km is None:
        trip.main_toll_km = toll_km(trip.route["coords"], tolls)
    skipped = max(0.0, trip.main_toll_km - toll_km(coords, tolls))
    return round(TOLL_REENTRY_EUR - skipped * TOLL_EUR_PER_KM, 2)   # negative = the detour avoids enough toll km to save money


def toll_exits(trip, fuel):
    """Stations (up to 25 km from the route) that make you leave a toll motorway, with the estimated extra péage."""
    tolls = trip.tolls.result(timeout=90)
    ids = [s["id"] for s in stations_for(trip, fuel, 25) if trip.exits_toll(s, tolls)]
    cost = {}
    for sid in ids:
        e = toll_estimate(trip, sid, tolls)
        if e is not None:
            cost[sid] = e
    return {"exits": ids, "cost": cost}


def traffic_via(trip, sid):
    if sid in trip.traffic_via:
        return trip.traffic_via[sid]
    s = get_station(sid)
    if s is None:
        return None
    trip.traffic_via[sid] = r = tomtom_route(points_via(trip, s))["duration_s"]
    return r


def via_station_route(trip, sid):
    """Full route geometry start -> (vias) -> station -> end, for drawing the alternative path."""
    s = get_station(sid)
    if s is None:
        return None
    pts = points_via(trip, s)
    try:
        r = ign_route(pts, steps=False)
        coords, dur, dist = r["geometry"]["coordinates"], r["duration"], r["distance"]
    except Exception as e:
        print(f"[via] IGN failed ({e}), trying OSRM", flush=True)
        rt = osrm_route(pts, annotations=False)
        coords, dur, dist = rt["geometry"]["coordinates"], rt["duration"], rt["distance"]
    return {"route": simplify(coords, 2000), "duration_s": dur, "distance_m": dist}


# ================================================================ abuse protection
# Every visitor (IP) has a budget of "work units" that refills over time; expensive endpoints cost more.
# A normal trip search with detours, ideal stops and traffic costs ~150 units, so a person never notices it,
# while a bot hammering the site gets HTTP 429 instead of burning the IGN / TomTom quotas.
BUDGET_MAX = 1800                 # units (burst: ~8 full trip searches)
BUDGET_REFILL = 2.0               # units per second (~7200/hour, about one full search every 2 min)
COSTS = {"/api/route": 15, "/api/nearby": 15, "/api/ideal": 40, "/api/via": 4, "/api/detours": 3, "/api/tolls": 2,
         "/api/traffic": 5, "/api/traffic_via": 8, "/api/geocode": 1, "/api/reverse": 1, "/api/ev_chains": 1}
MAX_CONN_PER_IP = 24
MAX_CONN_TOTAL = 300
TRUSTED_NETS = [ipaddress.ip_network(n) for n in (
    "127.0.0.0/8", "10.0.0.0/8", "172.16.0.0/12", "192.168.0.0/16", "100.64.0.0/10",   # loopback, LAN, Tailscale
    "::1/128", "fe80::/10", "fc00::/7", *os.environ.get("TRUSTED_EXTRA", "").split())]   # IPv6 loopback, local; home LAN via TRUSTED_EXTRA env

_buckets = {}                     # ip -> [units, last_ts]
_conns = {}                       # ip -> open connections
_abuse_lock = threading.Lock()
_total_conns = 0


def client_key(addr):
    try:
        ip = ipaddress.ip_address(addr)
    except ValueError:
        return addr, False
    if ip.version == 6 and ip.ipv4_mapped:
        ip = ip.ipv4_mapped
    trusted = any(ip in n for n in TRUSTED_NETS)
    if ip.version == 6:                       # one budget per /64 (a single home or phone gets many IPv6 addresses)
        ip = ipaddress.ip_network(f"{ip}/64", strict=False).network_address
    return str(ip), trusted


def spend(addr, cost):
    """True if this visitor may do `cost` units of work now."""
    key, trusted = client_key(addr)
    if trusted or cost <= 0:
        return True
    now = time.monotonic()
    with _abuse_lock:
        units, last = _buckets.get(key, (BUDGET_MAX, now))
        units = min(BUDGET_MAX, units + (now - last) * BUDGET_REFILL)
        ok = units >= cost
        _buckets[key] = [units - cost if ok else units, now]
        if len(_buckets) > 20000:              # forget idle visitors
            for k in [k for k, v in _buckets.items() if now - v[1] > 3600]:
                del _buckets[k]
    if not ok:
        print(f"[abuse] rate limited {key}", flush=True)
    return ok


# TomTom free tier = 2,500 requests/day: stop at 2,200 so the key is never blocked or billed (the site then works without traffic)
TOMTOM_DAILY_CAP = 2200
TOMTOM_USAGE_FILE = os.path.join(HERE, "cache", "tomtom_usage.json")
_tt_lock = threading.Lock()


def tomtom_allow():
    today = datetime.now(PARIS).strftime("%Y-%m-%d")
    with _tt_lock:
        try:
            with open(TOMTOM_USAGE_FILE) as f:
                u = json.load(f)
        except (OSError, ValueError):
            u = {}
        if u.get("date") != today:
            u = {"date": today, "count": 0}
        if u["count"] >= TOMTOM_DAILY_CAP:
            return False
        u["count"] += 1
        os.makedirs(os.path.dirname(TOMTOM_USAGE_FILE), exist_ok=True)
        with open(TOMTOM_USAGE_FILE, "w") as f:
            json.dump(u, f)
        return True


# ================================================================ HTTP
class Handler(BaseHTTPRequestHandler):
    server_version = "fuel-route"
    is_tls = False

    def log_message(self, fmt, *args):
        pass

    def end_headers(self):
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
        self.send_header("Permissions-Policy", "geolocation=(self), camera=(), microphone=()")
        super().end_headers()

    def send_json(self, obj, code=200):
        body = json.dumps(obj, separators=(",", ":")).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def redirect(self, url):
        self.send_response(301)
        self.send_header("Location", url)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        host = (self.headers.get("Host") or "").split(":")[0].lower()
        if not self.is_tls and DOMAIN and host == DOMAIN and tls.available():
            return self.redirect(f"https://{DOMAIN}:{PORT}{self.path}")
        u = urllib.parse.urlparse(self.path)
        q = urllib.parse.parse_qs(u.query)
        if not spend(self.client_address[0], COSTS.get(u.path, 0)):
            self.send_response(429)
            self.send_header("Retry-After", "60")
            body = json.dumps({"error": "Too many requests from your connection, please wait a minute."}).encode()
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        try:
            if u.path == "/api/geocode":
                text = q.get("q", [""])[0][:200].strip()
                return self.send_json(geocode(text) if len(text) >= 3 else [])
            if u.path == "/api/reverse":
                lon, lat = float(q["lon"][0]), float(q["lat"][0])
                return self.send_json(reverse(lon, lat))
            if u.path == "/api/route":
                return self.api_route(q)
            if u.path == "/api/detours":
                return self.api_detours(q)
            if u.path == "/api/nearby":
                return self.api_nearby(q)
            if u.path in ("/api/ideal", "/api/via", "/api/tolls", "/api/traffic", "/api/traffic_via"):
                trip = find_trip(q.get("trip", [""])[0])
                if trip is None:
                    return self.send_json({"error": "Trip expired, search again"}, 410)
                if u.path == "/api/tolls":
                    fuel = choice_from(q)
                    return self.send_json(toll_exits(trip, fuel if valid_choice(fuel) else "E85"))
                if u.path == "/api/traffic":
                    if trip.traffic is None:
                        return self.send_json({"enabled": False})
                    return self.send_json(dict(trip.traffic.result(timeout=60), enabled=True))
                if u.path == "/api/traffic_via":
                    if trip.traffic is None:
                        return self.send_json({"enabled": False})
                    base = trip.traffic.result(timeout=60)["duration_s"]
                    ids = [i for i in q.get("ids", [""])[0].split(",") if i][:6]
                    futs = {i: _detour_pool.submit(traffic_via, trip, i) for i in ids}
                    out = {}
                    for i, f in futs.items():
                        try:
                            v = f.result(timeout=60)
                            out[i] = None if v is None else max(0, v - base)
                        except Exception as e:
                            print(f"[traffic] {i}: {e!r}", flush=True)
                            out[i] = None
                    return self.send_json({"enabled": True, "detour_s": out})
                if u.path == "/api/via":
                    return self.send_json(via_station_route(trip, q["id"][0]) or {"error": "Unknown station"})
                fuel = choice_from(q)
                if not valid_choice(fuel):
                    return self.send_json({"error": "Unknown fuel"}, 400)
                band = min(max(float(q.get("band", ["15"])[0]), 1), 25)
                cands, alts = ideal_candidates(trip, fuel, band)
                return self.send_json({"band": band, "stations": cands, "alternatives": alts,
                                       "fastest_s": trip.route["duration"], "fastest_m": trip.route["distance"]})
            if u.path == "/api/status":
                return self.send_json({"stations": len(_stations), "feed_updated": _stations_loaded_at, "https": tls.available(),
                                       "ev_stations": len(EV.stations), "ev_status_updated": EV.status_at})
            if u.path == "/api/ev_chains":
                return self.send_json(ev_chains())
            return self.serve_static(u.path)
        except (KeyError, ValueError):
            return self.send_json({"error": "Bad request"}, 400)
        except Exception as e:
            print(f"[http] {u.path}: {e!r}", flush=True)
            return self.send_json({"error": "A data service didn't answer, please retry."}, 502)

    def api_route(self, q):
        pts = []
        for p in q.get("p", []):
            lon, lat = (float(v) for v in p.split(","))
            if not (-10 < lon < 12 and 40 < lat < 53):
                return self.send_json({"error": "Point outside France"}, 400)
            pts.append((lon, lat))
        if not 2 <= len(pts) <= 6:
            return self.send_json({"error": "Need a start and an end"}, 400)
        fuel = choice_from(q)
        if not valid_choice(fuel):
            return self.send_json({"error": "Unknown fuel"}, 400)
        if "detour_min" in q:
            # stations that could be within N minutes of added time: generous distance band, exact filter client-side
            minutes = min(max(float(q["detour_min"][0]), 1), 60)
            corridor = min(20.0, 0.6 * minutes + 0.5)
        else:
            corridor = min(max(float(q.get("corridor", ["3"])[0]), 0.5), 25)
        trip = get_trip(pts)
        return self.send_json({
            "trip": trip.key, "route": simplify(trip.route["coords"]),
            "distance_m": trip.route["distance"], "duration_s": trip.route["duration"], "router": trip.route["router"],
            "stations": stations_for(trip, fuel, corridor), "feed_updated": _stations_loaded_at,
        })

    def api_nearby(self, q):
        lon, lat = float(q["lon"][0]), float(q["lat"][0])
        if not (-10 < lon < 12 and 40 < lat < 53):
            return self.send_json({"error": "Point outside France"}, 400)
        fuel = choice_from(q)
        if not valid_choice(fuel):
            return self.send_json({"error": "Unknown fuel"}, 400)
        radius = min(max(float(q.get("radius", ["10"])[0]), 1), 50)
        mode = "drive" if q.get("mode", ["crow"])[0] == "drive" else "crow"
        nb = get_nearby(lon, lat, radius, mode)
        return self.send_json({"trip": nb.key, "area": nb.area, "radius": radius, "mode": mode,
                               "stations": stations_near(nb, fuel), "feed_updated": _stations_loaded_at})

    def api_detours(self, q):
        key = q.get("trip", [""])[0]
        ids = [i for i in q.get("ids", [""])[0].split(",") if i][:8]
        if key.startswith("n|"):
            with _trips_lock:
                nb = _nearby.get(key)
            if nb is None:
                return self.send_json({"error": "Search expired, search again"}, 410)
            futures = {i: _detour_pool.submit(compute_drive, nb, i) for i in ids}
        else:
            trip = find_trip(key)
            if trip is None:
                return self.send_json({"error": "Trip expired, search again"}, 410)
            futures = {i: _detour_pool.submit(compute_detour, trip, i) for i in ids}
        out = {}
        for i, f in futures.items():
            try:
                out[i] = f.result(timeout=90)
            except Exception as e:
                print(f"[detour] {i}: {e!r}", flush=True)
                out[i] = None
        return self.send_json(out)

    def serve_static(self, path):
        name = "index.html" if path in ("/", "") else os.path.basename(path)
        fp = os.path.join(STATIC, name)
        if not os.path.isfile(fp):
            self.send_error(404)
            return
        ctype = {"html": "text/html", "js": "application/javascript", "css": "text/css", "svg": "image/svg+xml",
                 "json": "application/json", "webmanifest": "application/manifest+json"}.get(name.rsplit(".", 1)[-1], "application/octet-stream")
        with open(fp, "rb") as f:
            body = f.read()
        self.send_response(200)
        self.send_header("Content-Type", ctype + "; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-cache")      # phones must always get the latest page after an update
        if self.is_tls:
            self.send_header("Strict-Transport-Security", "max-age=86400")
        self.end_headers()
        self.wfile.write(body)


class TLS:
    """Loads the certificate lazily and reloads it when the file changes (renewals)."""

    def __init__(self):
        self.ctx, self.mtime, self.lock = None, None, threading.Lock()

    def context(self):
        try:
            m = (os.path.getmtime(CERT), os.path.getmtime(KEY))
        except OSError:
            return None
        with self.lock:
            if m != self.mtime:
                try:
                    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
                    ctx.load_cert_chain(CERT, KEY)
                    self.ctx, self.mtime = ctx, m
                    print("[tls] certificate loaded", flush=True)
                except Exception as e:
                    print(f"[tls] cannot load certificate: {e}", flush=True)
                    self.ctx, self.mtime = None, m
            return self.ctx

    def available(self):
        return self.context() is not None


tls = TLS()


class DualServer(ThreadingHTTPServer):
    daemon_threads = True

    def finish_request(self, request, client_address):
        # Runs in the per-connection thread. Limit simultaneous connections per visitor and in total.
        global _total_conns
        key, trusted = client_key(client_address[0])
        with _abuse_lock:
            if not trusted and (_conns.get(key, 0) >= MAX_CONN_PER_IP or _total_conns >= MAX_CONN_TOTAL):
                return                                  # just close it
            _conns[key] = _conns.get(key, 0) + 1
            _total_conns += 1
        try:
            self._serve(request, client_address)
        finally:
            with _abuse_lock:
                _total_conns -= 1
                _conns[key] -= 1
                if _conns[key] <= 0:
                    del _conns[key]

    def _serve(self, request, client_address):
        # sniff first byte; 0x16 = TLS ClientHello
        try:
            request.settimeout(10)
            first = request.recv(1, socket.MSG_PEEK)
            ctx = tls.context()
            if first == b"\x16" and ctx is not None:
                request = ctx.wrap_socket(request, server_side=True)
                handler = type("TLSHandler", (Handler,), {"is_tls": True})
            else:
                handler = Handler
            request.settimeout(30)                      # idle connections (slowloris) get dropped
            handler(request, client_address, self)
        except (ssl.SSLError, OSError):
            pass


class AcmeHandler(BaseHTTPRequestHandler):
    """Port forwarded from public :80 -- answers Let's Encrypt challenges, redirects everything else."""

    def log_message(self, fmt, *args):
        pass

    def do_GET(self):
        prefix = "/.well-known/acme-challenge/"
        if self.path.startswith(prefix):
            token = os.path.basename(self.path[len(prefix):].split("?")[0])
            fp = os.path.join(ACME_ROOT, ".well-known", "acme-challenge", token)
            if token and os.path.isfile(fp):
                with open(fp, "rb") as f:
                    body = f.read()
                self.send_response(200)
                self.send_header("Content-Type", "text/plain")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            self.send_error(404)
            return
        self.send_response(301)
        host = DOMAIN or (self.headers.get("Host") or "localhost").split(":")[0]
        self.send_header("Location", f"https://{host}:{PORT}/")
        self.send_header("Content-Length", "0")
        self.end_headers()


def ev_chains():
    """Known chains with their number of stations and typical price (for the chain filter)."""
    manual = EV.manual_prices()
    out = {}
    with EV.lock:
        stations = list(EV.stations.values())
    for g in stations:
        if g["chain"]:
            c = out.setdefault(g["chain"], {"name": g["chain"], "stations": 0, "fast": None, "slow": None})
            c["stations"] += 1
    for name, c in out.items():
        for fast in (True, False):
            m = manual.get(name)
            v = (m.get("fast" if fast else "slow") if isinstance(m, dict) else m) if m is not None else None
            c["fast" if fast else "slow"] = v if v is not None else EV.typical.get((name, fast))
    return sorted(out.values(), key=lambda c: -c["stations"])


if __name__ == "__main__":
    threading.Thread(target=feed_loop, daemon=True).start()
    threading.Thread(target=EV.loop, daemon=True).start()
    threading.Thread(target=brands_loop, daemon=True).start()
    try:
        acme = ThreadingHTTPServer(("0.0.0.0", ACME_PORT), AcmeHandler)
        acme.daemon_threads = True
        threading.Thread(target=acme.serve_forever, daemon=True).start()
    except OSError as e:
        print(f"[acme] cannot listen on port {ACME_PORT} ({e}); certificate renewal won't work", flush=True)
    print(f"Fuel route finder listening on :{PORT} (http+https), ACME on :{ACME_PORT}", flush=True)
    DualServer(("0.0.0.0", PORT), Handler).serve_forever()
