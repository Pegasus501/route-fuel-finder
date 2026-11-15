# Rat-Station 🐭⛽

*Le système de recherche de station essence pour les gros rats.*

A small self-hosted website (French by default, with an English switch) that finds fuel stations in **France** — along a car trip or around a place —
with their latest official prices and stock outages.

- **Fuels:** E85 (Superéthanol), Diesel (Gazole), SP95-E10, SP95, SP98, or "SP95 + E10" (whichever of the two is in stock and cheaper at each station)
- **Trip mode:** enter a start, an end (and an optional stop). Stations within 1–20 km of the route are listed in
  driving order, with the **real detour time** (leave the route, refuel, come back), so stations on the wrong side of a dual
  carriageway show their true cost. Motorway service stations on the opposite carriageway are flagged and never suggested.
- **Ideal stops:** also explores up to 3 genuinely different routes to the destination (TomTom / OSRM alternatives, or forced
  detours left and right of the main route) and checks stations up to 15 km off the route and lists the best time-vs-price trade-offs (quickest stop,
  then each slower-but-cheaper option with its real saving for your fill, minus the fuel burnt on the extra km), and draws that path.
- **Toll roads:** flags stations that make you leave a toll motorway ("⚠ leaves toll motorway"), and counts the
  estimated extra péage (adjustable, default 1.50 €) in the savings, telling you when a cheaper station ends up costing more.
- **Live traffic (optional):** with a free [TomTom developer](https://developer.tomtom.com) key, shows the ETA with live traffic,
  jams in red on the map, and each ideal stop's detour with traffic. Put `{"tomtom_key": "..."}` in `config.json` next to `server.py`.
- **Around a place:** search a radius around your location or an address, measured **by road** or **à vol d'oiseau**.
- **Stock:** stations reporting a temporary outage are greyed out ("out of stock · 3 h"); prices older than 7 days are flagged.
- **Brand names** (Esso, TotalEnergies, Leclerc…) are matched from OpenStreetMap; the Maps button opens the station's
  Google Maps page, Waze navigates there.
- 📍 **Current location** (needs HTTPS, see below).

No dependencies beyond **Python 3.9+** standard library. No API keys.

## Data sources (all free & open)

| What | Source |
|---|---|
| Prices + outages | [prix-carburants](https://www.prix-carburants.gouv.fr/rubrique/opendata/) official feed (`instantane_ruptures`), refreshed every 10 min |
| Routing, detours, drive-distance areas | [IGN Géoplateforme](https://geoservices.ign.fr/services-geoplateforme-itineraire) (fallback: public OSRM) |
| Address search | [api-adresse.data.gouv.fr](https://adresse.data.gouv.fr/outils/api-doc/adresse) |
| Station brands | [OpenStreetMap](https://www.openstreetmap.org) via Overpass (`ref:FR:prix-carburants` tag), refreshed weekly |
| Toll / free road status | IGN Géoplateforme `bdtopo-pgr` engine (`acces_vehicule_leger`) |
| Live traffic (optional) | TomTom Routing API (free tier, needs a key) |
| Map | Leaflet + OpenStreetMap tiles |

## Run it

```bash
git clone <this repo> ~/e85-route
python3 ~/e85-route/server.py          # then open http://localhost:8085
```

The first start downloads the price feed (~1 MB) and the OpenStreetMap station list (~8 MB, can take a couple of minutes;
brand names appear once it's done).

Environment variables: `PORT` (default 8085), `DOMAIN` (your public hostname, for HTTPS), `ACME_PORT` (default 8086).

### Run it permanently (Linux, systemd)

See [`deploy/e85-route.service`](deploy/e85-route.service) — it runs as your normal user, starts at boot and restarts on crash.
Logs: `journalctl --user -u e85-route -f`.

### Make it reachable from your phone

Forward the port (TCP 8085) on your router/box to the machine, then use `http://<your-public-hostname>:8085`.
(Freebox: Paramètres → Mode avancé → Gestion des ports. Your box's free `xxx.freeboxos.fr` name works.)

### HTTPS (needed for the 📍 location button)

Browsers only share location with https sites. The server speaks HTTP and HTTPS **on the same port** and picks up
`certs/fullchain.pem` + `certs/key.pem` automatically (and reloads them after renewal). To get a free Let's Encrypt certificate:

1. Let the server listen on port 80 for the certificate check (one-time, as admin):
   ```bash
   echo 'net.ipv4.ip_unprivileged_port_start=80' | sudo tee /etc/sysctl.d/60-unprivileged-ports.conf && sudo sysctl --system
   ```
   and set `ACME_PORT=80` and `DOMAIN=your.host.name` in the service file.
2. Forward TCP port 80 on your router to the machine.
3. Get the certificate with [acme.sh](https://github.com/acmesh-official/acme.sh) (installs automatic renewal):
   ```bash
   git clone --depth 1 --branch 3.1.1 https://github.com/acmesh-official/acme.sh ~/acme-src && cd ~/acme-src && ./acme.sh --install --no-profile
   ~/.acme.sh/acme.sh --issue --server letsencrypt -d YOUR.HOST.NAME -w ~/e85-route/acme-webroot
   ~/.acme.sh/acme.sh --install-cert -d YOUR.HOST.NAME --key-file ~/e85-route/certs/key.pem --fullchain-file ~/e85-route/certs/fullchain.pem
   ```

## Notes

- Metropolitan France only. Outages are self-reported by stations, so a quick check on arrival is still wise.
- The IGN routing service is rate-limited, so detours/road distances fill in progressively a few seconds after a search.
- Be gentle with the free public services if you make many requests.
