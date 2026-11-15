"""EV charging stations for StationRat: the national IRVE database (static) + live availability (dynamic).

Sources (transport.data.gouv.fr, "Base nationale consolidée IRVE"):
  - static:  every public charge point with operator, power, connectors, payment and a free-text tariff
  - dynamic: per charge point status (en_service / hors_service) and occupation (libre / occupe), refreshed often

Prices are not structured in the national data, so each station gets, in order of preference:
  1. its own price, parsed from the tariff text ("0,29€ / kWh", "HPC 49cts/kWh", "0.3333€ par kwh"...)
  2. a manual price for its chain from ev_prices.json (optional, edit it yourself)
  3. the typical (median) price of its chain/network, computed from the stations of that network that do publish one
  otherwise the price is unknown.
"""
import csv
import io
import json
import os
import re
import statistics
import threading
import time
import urllib.request
from datetime import datetime, timezone

STATIC_URL = "https://transport.data.gouv.fr/resources/84013/download"
DYNAMIC_URL = "https://transport.data.gouv.fr/resources/84098/download"
STATIC_REFRESH = 24 * 3600
DYNAMIC_REFRESH = 5 * 60
STATUS_MAX_AGE = 48 * 3600          # older live statuses are treated as unknown

# Chains people recognise; first match wins (checked against brand, operator, owner and station name)
CHAINS = [
    ("Lidl", r"\blidl\b"), ("Aldi", r"\baldi\b"), ("McDonald's", r"mc ?do\b|mcdonald"), ("Leclerc", r"leclerc"),
    ("Intermarché", r"intermarch"), ("Super U", r"\b(super|hyper) ?u\b|syst[eè]me ?u\b|\bu express\b"),
    ("Carrefour", r"carrefour"), ("Auchan", r"auchan"), ("Tesla", r"tesla"), ("Ionity", r"ionity"),
    ("Fastned", r"fastned"), ("Electra", r"\belectra\b"), ("Power Dot", r"power ?dot"), ("TotalEnergies", r"total ?energies|\btotal\b"),
    ("Izivia", r"izivia"), ("Allego", r"allego"), ("Engie Vianeo", r"vianeo"), ("Freshmile", r"freshmile"),
]
CHAINS_RX = [(n, re.compile(rx, re.I)) for n, rx in CHAINS]
MOTORWAY_RX = re.compile(r"\baire\b|autoroute|\bA ?\d{1,3}\b|\baprr\b|\bsanef\b|vinci autoroutes", re.I)
PRICE_RX = re.compile(r"(\d+(?:\.\d+)?)\s*(€|eur|euros?|cts?|cents?|c€|centimes?)\s*(?:ttc|ht)?\s*(?:/|par|le|per)\s*(?:1\s*)?kwh")
PRICE_RX2 = re.compile(r"kwh\s*(?::|=|à|a)\s*(\d+(?:\.\d+)?)\s*(€|cts?|c€)")
TRUCK_RX = re.compile(r"truck|poids[ -]lourds?|\bPL\b|camion", re.I)
CODE_NAME_RX = re.compile(r"/[A-Z0-9]{6,}|^[A-Z]{2}\*?[A-Z0-9]{3}\*?[A-Z0-9]{6,}")
VAGUE_TARIF = re.compile(r"peuvent varier|consulter|^https?://|^inconnu$|^-$|grille tarifaire", re.I)


def kwh_prices(txt):
    if not txt:
        return []
    t = txt.lower().replace(",", ".")
    vals = []
    for m in PRICE_RX.finditer(t):
        v = float(m.group(1))
        vals.append(v / 100 if m.group(2).startswith("c") else v)
    for m in PRICE_RX2.finditer(t):
        v = float(m.group(1))
        vals.append(v / 100 if m.group(2).startswith("c") else v)
    return [v for v in vals if 0.05 <= v <= 1.5]


def _true(v):
    return str(v).strip().lower() in ("true", "1", "vrai", "oui")


def fix_text(t):
    """Repair UTF-8 text that was decoded as Latin-1 upstream ("RÃ©publique" -> "République")."""
    t = (t or "").strip()
    if "Ã" in t or "Â" in t:
        try:
            return t.encode("latin-1").decode("utf-8")
        except (UnicodeEncodeError, UnicodeDecodeError):
            pass
    return t


STREET_NAMES_RX = re.compile(r"(g[ée]n[ée]ral|mar[ée]chal|avenue|av\.?|rue|bd|boulevard|place|quai|all[ée]e)[\s\-]*(du[\s\-]+)?(g[ée]n[ée]ral[\s\-]+|mar[ée]chal[\s\-]+)?leclerc", re.I)


def chain_of(*texts):
    blob = STREET_NAMES_RX.sub(" ", " ".join(t for t in texts if t))
    for name, rx in CHAINS_RX:
        if rx.search(blob):
            return name
    return None


class EVData:
    def __init__(self, cache_dir, ua, manual_prices_file):
        self.cache_dir, self.ua, self.manual_file = cache_dir, ua, manual_prices_file
        self.stations = {}           # id -> station dict
        self.status = {}             # pdc id -> (etat, occupation, unix ts)
        self.typical = {}            # (group, fast) -> median €/kWh
        self.loaded_at = self.status_at = 0.0
        self.lock = threading.Lock()

    # ------------------------------------------------------------ static data
    def parse_static(self, path):
        groups = {}
        with open(path, encoding="utf-8", newline="") as f:
            for row in csv.DictReader(f):
                sid = row.get("id_station_itinerance") or row.get("id_station_local")
                try:
                    lon, lat = float(row["consolidated_longitude"]), float(row["consolidated_latitude"])
                except (KeyError, TypeError, ValueError):
                    continue
                if not (41 < lat < 52 and -6 < lon < 10) or not sid:
                    continue
                if (row.get("condition_acces") or "").lower().startswith("accès réservé"):
                    continue                         # customers / residents only
                if TRUCK_RX.search(row.get("nom_station") or ""):
                    continue                         # heavy-vehicle charging
                try:
                    kw = float(row.get("puissance_nominale") or 0)
                except ValueError:
                    kw = 0.0
                if kw > 1000:
                    kw /= 1000                       # some operators publish watts
                g = groups.get(sid)
                if g is None:
                    name = fix_text(row.get("nom_station"))
                    if CODE_NAME_RX.search(name):
                        name = ""                    # internal codes like "Freshmile France/PIY0KLXO2X"
                    g = groups[sid] = {
                        "id": sid, "lat": lat, "lon": lon, "name": name,
                        "network": fix_text(row.get("nom_enseigne") or row.get("nom_operateur")),
                        "operator": fix_text(row.get("nom_operateur")),
                        "address": re.sub(r",?\s*France$", "", fix_text(row.get("adresse_station")), flags=re.I),
                        "chain": chain_of(row.get("nom_enseigne"), row.get("nom_operateur"), row.get("nom_amenageur"), name),
                        "motorway": bool(MOTORWAY_RX.search(name + " " + (row.get("adresse_station") or ""))),
                        "hours": (row.get("horaires") or "").strip(), "kw": 0.0, "pdc": [], "plugs": set(),
                        "cb": False, "free": False, "tarif": "", "_prices": [],
                        "updated": (row.get("date_maj") or "")[:10],
                    }
                g["kw"] = max(g["kw"], kw)
                g["pdc"].append(row.get("id_pdc_itinerance") or "")
                for col, label in (("prise_type_combo_ccs", "CCS"), ("prise_type_2", "Type 2"), ("prise_type_chademo", "CHAdeMO"), ("prise_type_ef", "EF")):
                    if _true(row.get(col)):
                        g["plugs"].add(label)
                g["cb"] |= _true(row.get("paiement_cb"))
                g["free"] |= _true(row.get("gratuit"))
                tarif = (row.get("tarification") or "").strip()
                if tarif and not g["tarif"] and not VAGUE_TARIF.search(tarif):
                    g["tarif"] = fix_text(tarif)[:180]
                g["_prices"] += kwh_prices(tarif)
        for g in groups.values():
            p = g.pop("_prices")
            # with several prices (AC / DC), fast stations get the higher one, slow ones the lower one
            g["own_price"] = round((max(p) if g["kw"] >= 50 else min(p)), 3) if p else None
            g["plugs"] = sorted(g["plugs"])
            g["kw"] = round(g["kw"], 1)
        # typical price per chain (or network) and speed class, from stations that publish a price
        samples = {}
        for g in groups.values():
            if g["own_price"] is not None:
                samples.setdefault((g["chain"] or g["network"], g["kw"] >= 50), []).append(g["own_price"])
        typical = {k: round(statistics.median(v), 3) for k, v in samples.items() if len(v) >= 3}
        return groups, typical

    def manual_prices(self):
        try:
            with open(self.manual_file) as f:
                return {k: v for k, v in json.load(f).items() if not k.startswith("_")}
        except (OSError, ValueError):
            return {}

    def price_of(self, g, manual=None):
        """(€/kWh, source) with source in station | manual | network, or (None, None)."""
        if g["free"] and g["own_price"] is None:
            return 0.0, "station"
        if g["own_price"] is not None:
            return g["own_price"], "station"
        fast = g["kw"] >= 50
        key = g["chain"] or g["network"]
        m = (manual if manual is not None else self.manual_prices()).get(key)
        if m is not None:
            v = m.get("fast" if fast else "slow", m.get("fast") or m.get("slow")) if isinstance(m, dict) else m
            if v is not None:
                return float(v), "manual"
        v = self.typical.get((key, fast))
        return (v, "network") if v is not None else (None, None)

    # ------------------------------------------------------------ live availability
    def parse_dynamic(self, data):
        out = {}
        for row in csv.DictReader(io.StringIO(data.decode("utf-8", "replace"))):
            ts = row.get("horodatage") or ""
            try:
                t = datetime.fromisoformat(ts.replace(" ", "T")).timestamp()
            except ValueError:
                continue
            out[row.get("id_pdc_itinerance") or ""] = (row.get("etat_pdc"), row.get("occupation_pdc"), t)
        return out

    def status_of(self, g):
        now, free = time.time(), 0
        busy = oos = known = 0
        newest = 0.0
        for pid in g["pdc"]:
            st = self.status.get(pid)
            if not st or now - st[2] > STATUS_MAX_AGE:
                continue
            known += 1
            newest = max(newest, st[2])
            if st[0] == "hors_service":
                oos += 1
            elif st[1] == "libre":
                free += 1
            elif st[1] in ("occupe", "reserve"):
                busy += 1
        if not known:
            return None
        return {"free": free, "busy": busy, "oos": oos, "known": known, "total": len(g["pdc"]),
                "at": datetime.fromtimestamp(newest, timezone.utc).isoformat()}

    # ------------------------------------------------------------ refresh loops
    def _download(self, url, path, timeout):
        data = urllib.request.urlopen(urllib.request.Request(url, headers=self.ua), timeout=timeout).read()
        with open(path + ".tmp", "wb") as f:
            f.write(data)
        os.replace(path + ".tmp", path)
        return data

    def loop(self):
        os.makedirs(self.cache_dir, exist_ok=True)
        static = os.path.join(self.cache_dir, "irve_static.csv")
        dynamic = os.path.join(self.cache_dir, "irve_dynamic.csv")
        next_static = 0.0
        while True:
            try:
                stale = not os.path.exists(static) or time.time() - os.path.getmtime(static) > STATIC_REFRESH
                if stale:
                    self._download(STATIC_URL, static, 600)
                if stale or not self.stations:
                    groups, typical = self.parse_static(static)
                    with self.lock:
                        self.stations, self.typical, self.loaded_at = groups, typical, os.path.getmtime(static)
                    print(f"[ev] {len(groups)} charging stations loaded, {len(typical)} network prices", flush=True)
            except Exception as e:
                print(f"[ev] static refresh failed: {e!r}", flush=True)
            try:
                if time.time() - self.status_at > DYNAMIC_REFRESH - 5:
                    st = self.parse_dynamic(self._download(DYNAMIC_URL, dynamic, 120))
                    with self.lock:
                        self.status, self.status_at = st, time.time()
            except Exception as e:
                print(f"[ev] live status refresh failed: {e!r}", flush=True)
            time.sleep(60)
