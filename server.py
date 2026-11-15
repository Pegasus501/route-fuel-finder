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
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from zoneinfo import ZoneInfo

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
class RateLimiter:
    def __init__(self, per_second):
        self.interval, self.next, self.lock = 1.0 / per_second, 0.0, threading.Lock()

    def wait(self):
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
    """(duration_s, distance_m) for a route through points."""
    try:
        r = ign_route(points, steps=False)
        return r["duration"], r["distance"]
    except Exception as e:
        print(f"[detour] IGN failed ({e}), trying OSRM", flush=True)
        rt = osrm_route(points, annotations=False)
        return rt["duration"], rt["distance"]


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


# ================================================================ trip cache
class Trip:
    def __init__(self, key, points):
        self.key, self.points = key, points
        self.route = full_route(points)
        self.index = RouteIndex(self.route)
        self.detours = {}            # station id -> dict
        self.created = time.time()


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
    with _lock:
        stations = list(_stations.values())
    out = []
    for s in stations:
        f = s["fuels"].get(fuel)
        if not f:
            continue
        d = crow_km(nb.lon, nb.lat, s["lon"], s["lat"])
        if d > nb.radius:
            continue          # a driving distance is never shorter than the straight line
        if nb.area is not None and not point_in_geom(s["lon"], s["lat"], nb.area):
            continue
        st = station_view(s, f)
        st["crow_km"] = round(d, 2)
        if s["id"] in nb.drives:
            st["drive"] = nb.drives[s["id"]]
        out.append(st)
    out.sort(key=lambda s: s["crow_km"])
    return out


def compute_drive(nb, sid):
    if sid in nb.drives:
        return nb.drives[sid]
    with _lock:
        s = _stations.get(sid)
    if s is None:
        return None
    dur, dist = via_route([(nb.lon, nb.lat), (s["lon"], s["lat"])])
    nb.drives[sid] = res = {"s": round(dur), "km": round(dist / 1000, 1)}
    return res


def stations_for(trip, fuel, corridor_km):
    with _lock:
        stations = list(_stations.values())
    out = []
    total_km = trip.index.cum[-1]
    for s in stations:
        f = s["fuels"].get(fuel)
        if not f:
            continue
        n = trip.index.nearest(s["lon"], s["lat"], corridor_km)
        if n is None:
            continue
        # Motorway service station on the left of a fast stretch = other carriageway: not reachable.
        opposite = s["motorway"] and n["left"] and n["off_km"] < 1.0 and n["speed_kmh"] > 80
        st = station_view(s, f)
        st.update(off_route_km=round(n["off_km"], 2), along_km=round(n["along_km"], 1), opposite=opposite,
                  pct=round(n["along_km"] / total_km, 4) if total_km else 0)
        if s["id"] in trip.detours:
            st["detour"] = trip.detours[s["id"]]
        out.append(st)
    out.sort(key=lambda s: s["along_km"])
    return out


def compute_detour(trip, sid):
    if sid in trip.detours:
        return trip.detours[sid]
    with _lock:
        s = _stations.get(sid)
    if s is None:
        return None
    n = trip.index.nearest(s["lon"], s["lat"], 30)
    if n is None:
        return None
    window = 10 + 2 * n["off_km"]
    a_lon, a_lat, a_t = trip.index.point_at(n["along_km"] - window)
    b_lon, b_lat, b_t = trip.index.point_at(n["along_km"] + window)
    a_km = max(0.0, n["along_km"] - window)
    b_km = min(trip.index.cum[-1], n["along_km"] + window)
    dur, dist = via_route([(a_lon, a_lat), (s["lon"], s["lat"]), (b_lon, b_lat)])
    res = {"s": max(0, round(dur - (b_t - a_t))), "km": round(max(0.0, dist / 1000 - (b_km - a_km)), 1)}
    trip.detours[sid] = res
    return res


_detour_pool = ThreadPoolExecutor(6)


# ================================================================ HTTP
class Handler(BaseHTTPRequestHandler):
    server_version = "fuel-route"
    is_tls = False

    def log_message(self, fmt, *args):
        pass

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
            if u.path == "/api/status":
                return self.send_json({"stations": len(_stations), "feed_updated": _stations_loaded_at, "https": tls.available()})
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
        fuel = q.get("fuel", ["E85"])[0]
        if fuel not in FUELS:
            return self.send_json({"error": "Unknown fuel"}, 400)
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
        fuel = q.get("fuel", ["E85"])[0]
        if fuel not in FUELS:
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
        # Runs in the per-connection thread: sniff first byte; 0x16 = TLS ClientHello.
        try:
            request.settimeout(10)
            first = request.recv(1, socket.MSG_PEEK)
            ctx = tls.context()
            if first == b"\x16" and ctx is not None:
                request = ctx.wrap_socket(request, server_side=True)
                handler = type("TLSHandler", (Handler,), {"is_tls": True})
            else:
                handler = Handler
            request.settimeout(60)
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


if __name__ == "__main__":
    threading.Thread(target=feed_loop, daemon=True).start()
    threading.Thread(target=brands_loop, daemon=True).start()
    try:
        acme = ThreadingHTTPServer(("0.0.0.0", ACME_PORT), AcmeHandler)
        acme.daemon_threads = True
        threading.Thread(target=acme.serve_forever, daemon=True).start()
    except OSError as e:
        print(f"[acme] cannot listen on port {ACME_PORT} ({e}); certificate renewal won't work", flush=True)
    print(f"Fuel route finder listening on :{PORT} (http+https), ACME on :{ACME_PORT}", flush=True)
    DualServer(("0.0.0.0", PORT), Handler).serve_forever()
