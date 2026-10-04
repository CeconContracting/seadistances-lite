/* Sea Distances Lite - the "server" running in the visitor's browser.
 *
 * The UI (static/index.html) talks to /api/... endpoints. In the desktop
 * app a Python server answers them; in Lite this file does, through
 * window.LiteBackend.fetch(), which returns real Response objects so the
 * UI code is the same for both.
 *
 *   routing   Dijkstra on the searoute shipping-lane network (network.json).
 *             World ports carry their land-free network connections,
 *             precomputed against GSHHG by tools/build_lite.py. No
 *             optimizer and no coastline checks - the browser has no
 *             coastline data.
 *   storage   ports, waypoints, pilot points, settings: localStorage;
 *             background layers: IndexedDB. Everything stays in the
 *             visitor's own browser - nothing is sent anywhere.
 *   layers    KML, KMZ, GeoJSON, GPX, CSV/TXT, XLSX (WGS84 lat/lon only).
 *   export    GeoJSON, KML, GPX, CSV, DXF (WGS84 UTM).
 *
 * Built into dist/lite by tools/build_lite.py. See docs/LITE.md.
 */
(function () {
  'use strict';

  const CFG = window.SEADIST_CONFIG || {};
  const VERSION = '1.2.0';
  const DATA = 'static/lite/';
  const STATE_KEY = 'seadist-lite-state';
  const NM = 1.852;
  const EARTH_R = 6371.0;
  const CANDIDATES = 8;          // nearest network nodes tried for a custom point
  const CUSTOM_CONN_FACTOR = 1.5; // custom points: prefer near nodes (no land check)
  const PALETTE = ['#E91E63', '#7B1FA2', '#00838F', '#C2185B', '#5D4037',
                   '#0277BD', '#AD1457', '#00695C', '#4527A0', '#BF360C'];

  // ================================================================ helpers
  class ApiError extends Error {
    constructor(msg, status = 400) { super(msg); this.status = status; }
  }
  function json(data, status = 200) {
    return new Response(JSON.stringify(data), { status, headers: { 'Content-Type': 'application/json' } });
  }
  function body(init) {
    if (!init || init.body == null) return {};
    if (init.body instanceof FormData) return init.body;
    try { return JSON.parse(init.body); } catch (e) { return {}; }
  }
  const rad = d => d * Math.PI / 180, deg = r => r * 180 / Math.PI;
  const wrapLon = lon => ((lon + 180) % 360 + 360) % 360 - 180;

  function havKm(lat1, lon1, lat2, lon2) {
    const h = Math.sin(rad(lat2 - lat1) / 2) ** 2 +
      Math.cos(rad(lat1)) * Math.cos(rad(lat2)) * Math.sin(rad(lon2 - lon1) / 2) ** 2;
    return 2 * EARTH_R * Math.asin(Math.sqrt(Math.min(1, h)));
  }

  // Vincenty inverse on WGS84: {km, az} - the ellipsoidal distance the
  // desktop app uses (geopy), so Lite and the exe agree to the metre.
  function vincenty(lat1, lon1, lat2, lon2) {
    const a = 6378137, f = 1 / 298.257223563, b = a * (1 - f);
    const L = rad(wrapLon(lon2 - lon1));
    const U1 = Math.atan((1 - f) * Math.tan(rad(lat1))), U2 = Math.atan((1 - f) * Math.tan(rad(lat2)));
    const sU1 = Math.sin(U1), cU1 = Math.cos(U1), sU2 = Math.sin(U2), cU2 = Math.cos(U2);
    let lam = L, lamP, iter = 0, sS, cS, sig, sA, c2A, c2Sm;
    do {
      const sL = Math.sin(lam), cL = Math.cos(lam);
      sS = Math.sqrt((cU2 * sL) ** 2 + (cU1 * sU2 - sU1 * cU2 * cL) ** 2);
      if (sS === 0) return { km: 0, az: 0 };
      cS = sU1 * sU2 + cU1 * cU2 * cL;
      sig = Math.atan2(sS, cS);
      sA = cU1 * cU2 * sL / sS;
      c2A = 1 - sA * sA;
      c2Sm = c2A !== 0 ? cS - 2 * sU1 * sU2 / c2A : 0;
      const C = f / 16 * c2A * (4 + f * (4 - 3 * c2A));
      lamP = lam;
      lam = L + (1 - C) * f * sA * (sig + C * sS * (c2Sm + C * cS * (-1 + 2 * c2Sm * c2Sm)));
    } while (Math.abs(lam - lamP) > 1e-12 && ++iter < 200);
    if (iter >= 200) {                       // nearly antipodal: fall back
      return { km: havKm(lat1, lon1, lat2, lon2), az: bearing(lat1, lon1, lat2, lon2) };
    }
    const u2 = c2A * (a * a - b * b) / (b * b);
    const A = 1 + u2 / 16384 * (4096 + u2 * (-768 + u2 * (320 - 175 * u2)));
    const B = u2 / 1024 * (256 + u2 * (-128 + u2 * (74 - 47 * u2)));
    const dS = B * sS * (c2Sm + B / 4 * (cS * (-1 + 2 * c2Sm * c2Sm) -
               B / 6 * c2Sm * (-3 + 4 * sS * sS) * (-3 + 4 * c2Sm * c2Sm)));
    const s = b * A * (sig - dS);
    const az = Math.atan2(cU2 * Math.sin(lam), cU1 * sU2 - sU1 * cU2 * Math.cos(lam));
    return { km: s / 1000, az: (deg(az) + 360) % 360 };
  }
  function bearing(lat1, lon1, lat2, lon2) {
    const y = Math.sin(rad(lon2 - lon1)) * Math.cos(rad(lat2));
    const x = Math.cos(rad(lat1)) * Math.sin(rad(lat2)) -
              Math.sin(rad(lat1)) * Math.cos(rad(lat2)) * Math.cos(rad(lon2 - lon1));
    return (deg(Math.atan2(y, x)) + 360) % 360;
  }
  const geoKm = (p, q) => vincenty(p[0], p[1], q[0], q[1]).km;
  const pathKm = pts => pts.reduce((s, p, i) => i ? s + geoKm(pts[i - 1], p) : 0, 0);

  // ================================================================ state
  function defaultState() {
    return { locations: {}, temp_waypoints: {}, pilotage: {}, vessels: {},
             settings: { speed: 10.0, unit_index: 0, land_res: 'High (recommended)',
                         show_legend: true, aisstream_api_key: '' } };
  }
  let S = null;
  function state() {
    if (S) return S;
    S = defaultState();
    try {
      const saved = JSON.parse(localStorage.getItem(STATE_KEY) || 'null');
      if (saved) {
        for (const k of ['locations', 'temp_waypoints', 'pilotage'])
          if (saved[k] && typeof saved[k] === 'object') S[k] = saved[k];
        Object.assign(S.settings, saved.settings || {});
      }
    } catch (e) { /* private window / blocked storage: start empty */ }
    return S;
  }
  function save() {
    try {
      localStorage.setItem(STATE_KEY, JSON.stringify({
        locations: S.locations, temp_waypoints: S.temp_waypoints,
        pilotage: S.pilotage, settings: S.settings }));
    } catch (e) { /* storage full or blocked: keep working in memory */ }
  }
  function coordsOf(name) {
    const s = state();
    return s.locations[name] || s.temp_waypoints[name] || null;
  }

  // ================================================================ network
  let NET = null, netLoading = null;
  function loadNetwork() {
    if (NET) return Promise.resolve(NET);
    if (!netLoading) {
      netLoading = fetch(DATA + 'network.json').then(r => {
        if (!r.ok) throw new ApiError('Could not load the routing network', 500);
        return r.json();
      }).then(d => {
        const n = d.nodes.length, lon = new Float64Array(n), lat = new Float64Array(n);
        d.nodes.forEach((p, i) => { lon[i] = p[0]; lat[i] = p[1]; });
        // edges: flat [i, j, km, ...] - searoute's own weights (its date-line
        // links between lon 180 and -180 weigh 0)
        const e = d.edges, deg_ = new Int32Array(n);
        for (let k = 0; k < e.length; k += 3) { deg_[e[k]]++; deg_[e[k + 1]]++; }
        const start = new Int32Array(n + 1);
        for (let i = 0; i < n; i++) start[i + 1] = start[i] + deg_[i];
        const nbr = new Int32Array(start[n]), w = new Float64Array(start[n]), fill = start.slice(0, n);
        for (let k = 0; k < e.length; k += 3) {
          const i = e[k], j = e[k + 1], km = e[k + 2];
          nbr[fill[i]] = j; w[fill[i]++] = km;
          nbr[fill[j]] = i; w[fill[j]++] = km;
        }
        NET = { n, lon, lat, start, nbr, w, edges: e };
        return NET;
      });
      netLoading.catch(() => { netLoading = null; });
    }
    return netLoading;
  }

  // ---- world ports (search + their land-free network connections)
  let PORTS = null, portsLoading = null;
  const portKey = (lat, lon) => `${(+lat).toFixed(4)},${(+wrapLon(lon)).toFixed(4)}`;
  function loadPorts() {
    if (PORTS) return Promise.resolve(PORTS);
    if (!portsLoading) {
      portsLoading = fetch(DATA + 'ports.json').then(r => {
        if (!r.ok) throw new ApiError('Could not load the port list', 500);
        return r.json();
      }).then(d => {
        const list = d.ports.map(r => ({ name: r[0], country: r[1], code: r[2], lat: r[3], lon: r[4],
                                         nodes: r[5], key: (r[0] + ' ' + r[1] + ' ' + r[2]).toLowerCase() }));
        const byCoord = new Map(list.map(p => [portKey(p.lat, p.lon), p]));
        PORTS = { list, byCoord };
        return PORTS;
      });
      portsLoading.catch(() => { portsLoading = null; });
    }
    return portsLoading;
  }
  async function searchPorts(q, limit = 30) {
    const P = await loadPorts();
    const words = String(q || '').toLowerCase().split(/\s+/).filter(Boolean);
    if (!words.length) return [];
    const hits = [];
    for (const p of P.list) {
      if (words.every(w => p.key.includes(w))) {
        hits.push(p);
        if (hits.length >= limit * 4) break;
      }
    }
    const first = words[0];
    hits.sort((a, b) => (b.name.toLowerCase().startsWith(first) - a.name.toLowerCase().startsWith(first)) ||
                        a.name.localeCompare(b.name));
    return hits.slice(0, limit).map(p => ({ name: p.name, country: p.country, code: p.code,
                                             lat: p.lat, lon: p.lon }));
  }

  // ---- binary heap for Dijkstra
  class Heap {
    constructor() { this.k = []; this.v = []; }
    get size() { return this.k.length; }
    push(key, val) {
      const k = this.k, v = this.v; let i = k.length; k.push(key); v.push(val);
      while (i > 0) { const p = (i - 1) >> 1; if (k[p] <= k[i]) break;
        [k[p], k[i]] = [k[i], k[p]]; [v[p], v[i]] = [v[i], v[p]]; i = p; }
    }
    pop() {
      const k = this.k, v = this.v, top = [k[0], v[0]], lk = k.pop(), lv = v.pop();
      if (k.length) {
        k[0] = lk; v[0] = lv; let i = 0;
        for (;;) {
          const l = 2 * i + 1, r = l + 1; let m = i;
          if (l < k.length && k[l] < k[m]) m = l;
          if (r < k.length && k[r] < k[m]) m = r;
          if (m === i) break;
          [k[m], k[i]] = [k[i], k[m]]; [v[m], v[i]] = [v[i], v[m]]; i = m;
        }
      }
      return top;
    }
  }

  // Network nodes a point may connect to, with the connection cost.
  // World ports: their precomputed land-free nodes (nearest one if none).
  // Anything else: the nearest few, costed a little extra - there is no
  // coastline in the browser to check the connection against.
  function connections(p, NETW) {
    const port = PORTS && PORTS.byCoord.get(portKey(p[0], p[1]));
    const near = () => {
      const d = [];
      for (let i = 0; i < NETW.n; i++) d.push([havKm(p[0], p[1], NETW.lat[i], NETW.lon[i]), i]);
      d.sort((a, b) => a[0] - b[0]);
      return d;
    };
    if (port) {
      let ids = port.nodes;
      if (!ids.length) ids = [near()[0][1]];
      return ids.map(i => [i, havKm(p[0], p[1], NETW.lat[i], NETW.lon[i])]);
    }
    return near().slice(0, CANDIDATES).map(([km, i]) => [i, km * CUSTOM_CONN_FACTOR]);
  }

  function shortestPath(NETW, from, to) {
    const dist = new Float64Array(NETW.n).fill(Infinity), prev = new Int32Array(NETW.n).fill(-1);
    const done = new Uint8Array(NETW.n), exitCost = new Map(to.map(([i, c]) => [i, c]));
    const h = new Heap();
    for (const [i, c] of from) if (c < dist[i]) { dist[i] = c; h.push(c, i); }
    let best = Infinity, bestNode = -1;
    while (h.size) {
      const [d, u] = h.pop();
      if (done[u] || d > dist[u]) continue;
      if (d >= best) break;
      done[u] = 1;
      if (exitCost.has(u) && d + exitCost.get(u) < best) { best = d + exitCost.get(u); bestNode = u; }
      for (let k = NETW.start[u]; k < NETW.start[u + 1]; k++) {
        const v = NETW.nbr[k], nd = d + NETW.w[k];
        if (nd < dist[v]) { dist[v] = nd; prev[v] = u; h.push(nd, v); }
      }
    }
    if (bestNode < 0) return null;
    const path = [];
    for (let u = bestNode; u >= 0; u = prev[u]) path.push(u);
    return path.reverse();
  }

  // One leg between two points on the network: [start, connection,
  // network path, connection, end]. Direction-canonical like the exe:
  // A->B and B->A give the same route.
  async function rawLeg(start, end) {
    const k = p => `${(+p[0]).toFixed(6)},${(+p[1]).toFixed(6)}`;
    if (k(start) > k(end)) {
      const r = await rawLeg(end, start);
      return { segments: r.segments.slice().reverse().map(([c, st]) => [c.slice().reverse(), st]),
               dist: r.dist, raw: r.raw.slice().reverse() };
    }
    const s = [+start[0], +start[1]], e = [+end[0], +end[1]];
    if (k(s) === k(e)) return { segments: [[[s, e], 'dashed']], dist: 0, raw: [s, e] };
    const NETW = await loadNetwork();
    await loadPorts().catch(() => null);      // land-free connections, if available
    const path = shortestPath(NETW, connections(s, NETW), connections(e, NETW));
    if (!path) throw new ApiError('No sea route found between these points');
    const grid = path.map(i => [NETW.lat[i], wrapLon(NETW.lon[i])]);
    const connA = [s, grid[0]], connB = [grid[grid.length - 1], e];
    const segments = [[connA, 'dashed']];
    if (grid.length >= 2) segments.push([grid, 'solid']);
    segments.push([connB, 'dashed']);
    return { segments, dist: pathKm(connA) + pathKm(grid) + pathKm(connB), raw: [s, ...grid, e] };
  }

  function legPaths(a, b) {
    const s = state(), sc = coordsOf(a), ec = coordsOf(b);
    if (!sc) throw new ApiError(`Unknown location: ${a}`);
    if (!ec) throw new ApiError(`Unknown location: ${b}`);
    const dep = [sc, ...(s.pilotage[a] || [])];
    const arr = [...(s.pilotage[b] || []).slice().reverse(), ec];
    return [dep, arr];
  }
  function pathLines(path, lines) {
    let d = 0;
    for (let i = 0; i < path.length - 1; i++) {
      d += geoKm(path[i], path[i + 1]);
      lines.push([[path[i], path[i + 1]], 'pilot_dashed']);
    }
    return d;
  }

  async function calculate(names) {
    if (!Array.isArray(names) || names.length < 2) throw new ApiError('Need at least 2 route points');
    const lines = [], legs = [];
    let total = 0;
    for (let i = 0; i < names.length - 1; i++) {
      const [dep, arr] = legPaths(names[i], names[i + 1]);
      let d = pathLines(dep, lines);
      const leg = await rawLeg(dep[dep.length - 1], arr[0]);
      leg.segments.forEach(([c, st]) => lines.push([c, st === 'solid' ? 'raw_solid' : 'raw_ghost']));
      d += leg.dist + pathLines(arr, lines);
      legs.push({ start: names[i], end: names[i + 1], dist_km: d, raw_coords: leg.raw });
      total += d;
    }
    return { lines, legs, total_km: total };
  }

  async function networkGeoJSON() {
    const NETW = await loadNetwork();
    const lines = [];
    for (let k = 0; k < NETW.edges.length; k += 3) {
      const i = NETW.edges[k], j = NETW.edges[k + 1];
      const a = [wrapLon(NETW.lon[i]), NETW.lat[i]], b = [wrapLon(NETW.lon[j]), NETW.lat[j]];
      if (Math.abs(a[0] - b[0]) <= 180) lines.push([a, b]);
    }
    return { type: 'FeatureCollection', features: [{ type: 'Feature', properties: {},
             geometry: { type: 'MultiLineString', coordinates: lines } }] };
  }

  // ================================================================ UTM
  // Transverse Mercator on WGS84 (Snyder / USGS series) - same results as
  // the Python 'utm' package the exe uses, to well under a millimetre.
  const UTM = (() => {
    const a = 6378137, f = 1 / 298.257223563, k0 = 0.9996, e2 = f * (2 - f), ep2 = e2 / (1 - e2);
    const bands = 'CDEFGHJKLMNPQRSTUVWXX';
    function letter(lat) { return lat < -80 || lat > 84 ? null : bands[Math.floor((lat + 80) / 8)]; }
    function zoneOf(lat, lon) {
      lon = wrapLon(lon);
      if (lat >= 56 && lat < 64 && lon >= 3 && lon < 12) return 32;
      if (lat >= 72 && lat < 84 && lon >= 0) {
        if (lon < 9) return 31; if (lon < 21) return 33; if (lon < 33) return 35; if (lon < 42) return 37;
      }
      return Math.floor((lon + 180) / 6) + 1;
    }
    function forward(lat, lon, zone) {
      const lon0 = rad((zone - 1) * 6 - 180 + 3), phi = rad(lat);
      const dl = rad(wrapLon(deg(rad(lon) - lon0)));
      const N = a / Math.sqrt(1 - e2 * Math.sin(phi) ** 2), T = Math.tan(phi) ** 2;
      const C = ep2 * Math.cos(phi) ** 2, A = Math.cos(phi) * dl;
      const M = a * ((1 - e2 / 4 - 3 * e2 ** 2 / 64 - 5 * e2 ** 3 / 256) * phi -
                (3 * e2 / 8 + 3 * e2 ** 2 / 32 + 45 * e2 ** 3 / 1024) * Math.sin(2 * phi) +
                (15 * e2 ** 2 / 256 + 45 * e2 ** 3 / 1024) * Math.sin(4 * phi) -
                (35 * e2 ** 3 / 3072) * Math.sin(6 * phi));
      const x = k0 * N * (A + (1 - T + C) * A ** 3 / 6 + (5 - 18 * T + T * T + 72 * C - 58 * ep2) * A ** 5 / 120) + 500000;
      let y = k0 * (M + N * Math.tan(phi) * (A * A / 2 + (5 - T + 9 * C + 4 * C * C) * A ** 4 / 24 +
              (61 - 58 * T + T * T + 600 * C - 330 * ep2) * A ** 6 / 720));
      if (lat < 0) y += 10000000;
      return [x, y];
    }
    function inverse(x, y, zone, north) {
      x -= 500000; if (!north) y -= 10000000;
      const lon0 = rad((zone - 1) * 6 - 180 + 3), M = y / k0;
      const mu = M / (a * (1 - e2 / 4 - 3 * e2 ** 2 / 64 - 5 * e2 ** 3 / 256));
      const e1 = (1 - Math.sqrt(1 - e2)) / (1 + Math.sqrt(1 - e2));
      const phi1 = mu + (3 * e1 / 2 - 27 * e1 ** 3 / 32) * Math.sin(2 * mu) +
        (21 * e1 * e1 / 16 - 55 * e1 ** 4 / 32) * Math.sin(4 * mu) +
        (151 * e1 ** 3 / 96) * Math.sin(6 * mu) + (1097 * e1 ** 4 / 512) * Math.sin(8 * mu);
      const N1 = a / Math.sqrt(1 - e2 * Math.sin(phi1) ** 2), T1 = Math.tan(phi1) ** 2;
      const C1 = ep2 * Math.cos(phi1) ** 2, R1 = a * (1 - e2) / (1 - e2 * Math.sin(phi1) ** 2) ** 1.5;
      const D = x / (N1 * k0);
      const lat = phi1 - (N1 * Math.tan(phi1) / R1) * (D * D / 2 - (5 + 3 * T1 + 10 * C1 - 4 * C1 * C1 - 9 * ep2) * D ** 4 / 24 +
        (61 + 90 * T1 + 298 * C1 + 45 * T1 * T1 - 252 * ep2 - 3 * C1 * C1) * D ** 6 / 720);
      const lon = lon0 + (D - (1 + 2 * T1 + C1) * D ** 3 / 6 +
        (5 - 2 * C1 + 28 * T1 - 3 * C1 * C1 + 8 * ep2 + 24 * T1 * T1) * D ** 5 / 120) / Math.cos(phi1);
      return [deg(lat), wrapLon(deg(lon))];
    }
    return { letter, zoneOf, forward, inverse };
  })();

  function convert(d) {
    if (d.direction === 'to_utm') {
      const lat = +d.lat, lon = +d.lon;
      if (!isFinite(lat) || !isFinite(lon)) throw new ApiError('Lat and Lon must be numbers');
      const L = UTM.letter(lat);
      if (!L) throw new ApiError('latitude out of range (must be between 80 deg S and 84 deg N)');
      const zone = UTM.zoneOf(lat, lon), [e, n] = UTM.forward(lat, lon, zone);
      return { easting: Math.round(e * 100) / 100, northing: Math.round(n * 100) / 100, zone, letter: L };
    }
    const e = +d.easting, n = +d.northing, zone = parseInt(d.zone, 10);
    const letter = String(d.letter || '').trim().toUpperCase();
    if (!isFinite(e) || !isFinite(n) || !(zone >= 1 && zone <= 60) || !/^[C-HJ-NP-X]$/.test(letter))
      throw new ApiError('Give easting, northing, zone (1-60) and band letter (C-X)');
    const [lat, lon] = UTM.inverse(e, n, zone, letter >= 'N');
    return { lat: Math.round(lat * 1e6) / 1e6, lon: Math.round(lon * 1e6) / 1e6 };
  }

  // ================================================================ export
  const xml = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&apos;' })[c]);
  function ddm(v, isLat) {
    const hemi = isLat ? (v >= 0 ? 'N' : 'S') : (v >= 0 ? 'E' : 'W');
    const a = Math.abs(v); let d = Math.floor(a), m = (a - d) * 60;
    if (+m.toFixed(3) >= 60) { d += 1; m = 0; }
    return `${String(d).padStart(isLat ? 2 : 3, '0')}°${m.toFixed(3).padStart(6, '0')}'${hemi}`;
  }
  function cleanRoute(points, line) {
    const pts = (points || []).filter(p => p && isFinite(+p.lat) && isFinite(+p.lon))
      .map(p => ({ name: String(p.name || '').trim(), lat: +p.lat, lon: +p.lon }));
    let ln = (line || []).map(p => [+p[0], +p[1]]).filter(p => isFinite(p[0]) && isFinite(p[1]))
      .map(p => [p[0], wrapLon(p[1])])
      .filter((p, i, a) => !i || p[0] !== a[i - 1][0] || p[1] !== a[i - 1][1]);
    if (ln.length < 2) ln = pts.map(p => [p.lat, p.lon]);
    if (!pts.length && ln.length < 2) throw new ApiError('The route is empty');
    return [pts, ln];
  }
  function labelVertices(pts, line) {
    const labels = new Map();
    for (const p of pts) {
      let best = -1, bd = 0.05;
      line.forEach((q, i) => {
        const d = havKm(p.lat, p.lon, q[0], q[1]);
        if (d < bd && !labels.has(i)) { best = i; bd = d; }
      });
      if (best >= 0) labels.set(best, p.name);
    }
    return labels;
  }
  const safeName = n => (String(n || '').replace(/[<>:"/\\|?*\x00-\x1f]/g, '_').trim().slice(0, 80) || 'route');

  function toGeoJSON(name, pts, line) {
    const feats = [];
    if (line.length >= 2) {
      const km = pathKm(line);
      feats.push({ type: 'Feature', properties: { name, kind: 'route', length_km: +km.toFixed(3), length_nm: +(km / NM).toFixed(3) },
                   geometry: { type: 'LineString', coordinates: line.map(p => [+p[1].toFixed(7), +p[0].toFixed(7)]) } });
    }
    pts.forEach((p, i) => feats.push({ type: 'Feature', properties: { name: p.name, seq: i + 1, kind: 'route point' },
      geometry: { type: 'Point', coordinates: [+p.lon.toFixed(7), +p.lat.toFixed(7)] } }));
    return JSON.stringify({ type: 'FeatureCollection', name, features: feats }, null, 1);
  }
  function toKML(name, pts, line) {
    const o = ['<?xml version="1.0" encoding="UTF-8"?>', '<kml xmlns="http://www.opengis.net/kml/2.2"><Document>',
      `<name>${xml(name)}</name>`, '<Style id="route"><LineStyle><color>ff50af4c</color><width>3</width></LineStyle></Style>'];
    if (line.length >= 2) {
      const km = pathKm(line);
      o.push(`<Placemark><name>${xml(name)}</name><description>${(km / NM).toFixed(1)} NM (${km.toFixed(1)} km)</description>` +
        `<styleUrl>#route</styleUrl><LineString><tessellate>1</tessellate><coordinates>` +
        line.map(p => `${p[1].toFixed(7)},${p[0].toFixed(7)},0`).join(' ') + '</coordinates></LineString></Placemark>');
    }
    if (pts.length) {
      o.push('<Folder><name>Route points</name>');
      pts.forEach(p => o.push(`<Placemark><name>${xml(p.name)}</name><Point><coordinates>${p.lon.toFixed(7)},${p.lat.toFixed(7)},0</coordinates></Point></Placemark>`));
      o.push('</Folder>');
    }
    o.push('</Document></kml>');
    return o.join('\n');
  }
  function toGPX(name, pts, line) {
    const o = ['<?xml version="1.0" encoding="UTF-8"?>',
      '<gpx version="1.1" creator="Sea Distances Lite" xmlns="http://www.topografix.com/GPX/1/1">',
      `<metadata><name>${xml(name)}</name></metadata>`];
    pts.forEach(p => o.push(`<wpt lat="${p.lat.toFixed(7)}" lon="${p.lon.toFixed(7)}"><name>${xml(p.name)}</name></wpt>`));
    if (line.length >= 2) {
      const labels = labelVertices(pts, line);
      o.push(`<rte><name>${xml(name)}</name>`);
      line.forEach((p, i) => o.push(`<rtept lat="${p[0].toFixed(7)}" lon="${p[1].toFixed(7)}"><name>${xml(labels.get(i) || 'WP' + String(i + 1).padStart(3, '0'))}</name></rtept>`));
      o.push('</rte>');
    }
    o.push('</gpx>');
    return o.join('\n');
  }
  function toCSV(name, pts, line) {
    const labels = labelVertices(pts, line), q = v => /[",\r\n]/.test(v) ? `"${v.replace(/"/g, '""')}"` : v;
    const rows = [['Point', 'Name', 'Lat', 'Lon', 'Lat (DDM)', 'Lon (DDM)', 'Leg (NM)', 'Cum (NM)', 'Course to next (°T)']];
    let cum = 0;
    line.forEach((p, i) => {
      const leg = i ? vincenty(line[i - 1][0], line[i - 1][1], p[0], p[1]).km / NM : 0;
      cum += leg;
      const crs = i < line.length - 1 ? vincenty(p[0], p[1], line[i + 1][0], line[i + 1][1]).az.toFixed(1) : '';
      rows.push([String(i + 1), labels.get(i) || '', p[0].toFixed(7), p[1].toFixed(7), ddm(p[0], true), ddm(p[1], false),
                 leg.toFixed(3), cum.toFixed(3), crs]);
    });
    return '﻿' + rows.map(r => r.map(q).join(',')).join('\r\n') + '\r\n';
  }
  function toDXF(name, pts, line, epsg) {
    let zone, north;
    if (epsg) {
      const m = String(epsg).match(/^(?:EPSG:)?(32[67])(\d\d)$/i);
      if (!m || +m[2] < 1 || +m[2] > 60)
        throw new ApiError('Lite exports DXF in WGS84 / UTM only (EPSG:326xx or 327xx)');
      zone = +m[2]; north = m[1] === '326';
    } else {
      const lat = line.reduce((s, p) => s + p[0], 0) / line.length;
      const lon = line.reduce((s, p) => s + p[1], 0) / line.length;
      zone = Math.min(60, Math.max(1, Math.floor((lon + 180) / 6) + 1)); north = lat >= 0;
    }
    const code = (north ? 32600 : 32700) + zone;
    // one zone and hemisphere for the whole drawing (UTM.forward adds the
    // southern false northing per point - undo/apply it consistently)
    const proj = (lat, lon) => {
      const [x, y] = UTM.forward(lat, lon, zone);
      return [x, north && lat < 0 ? y - 10000000 : !north && lat >= 0 ? y + 10000000 : y];
    };
    const xy = line.length >= 2 ? line.map(p => proj(p[0], p[1])) : [];
    const pxy = pts.map(p => proj(p.lat, p.lon));
    const all = xy.concat(pxy);
    const xs = all.map(p => p[0]), ys = all.map(p => p[1]);
    const ext = all.length ? Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys), 1000) : 1000;
    const th = +(ext / 150).toFixed(1);
    const o = [];
    const g = (c, v) => { o.push(String(c), String(v)); };
    g(999, `Sea Distances route '${name}' - coordinates in EPSG:${code} (metres)`);
    g(0, 'SECTION'); g(2, 'HEADER'); g(9, '$ACADVER'); g(1, 'AC1009'); g(0, 'ENDSEC');
    g(0, 'SECTION'); g(2, 'TABLES'); g(0, 'TABLE'); g(2, 'LAYER'); g(70, 3);
    for (const [ln, col] of [['ROUTE', 3], ['ROUTE_POINTS', 1], ['LABELS', 7]]) { g(0, 'LAYER'); g(2, ln); g(70, 0); g(62, col); g(6, 'CONTINUOUS'); }
    g(0, 'ENDTAB'); g(0, 'ENDSEC');
    g(0, 'SECTION'); g(2, 'ENTITIES');
    if (xy.length) {
      g(0, 'POLYLINE'); g(8, 'ROUTE'); g(66, 1); g(10, '0.0'); g(20, '0.0'); g(30, '0.0'); g(70, 0);
      xy.forEach(([x, y]) => { g(0, 'VERTEX'); g(8, 'ROUTE'); g(10, x.toFixed(3)); g(20, y.toFixed(3)); g(30, '0.0'); });
      g(0, 'SEQEND'); g(8, 'ROUTE');
    }
    pts.forEach((p, i) => {
      const [x, y] = pxy[i];
      g(0, 'POINT'); g(8, 'ROUTE_POINTS'); g(10, x.toFixed(3)); g(20, y.toFixed(3)); g(30, '0.0');
      if (p.name) { g(0, 'TEXT'); g(8, 'LABELS'); g(10, (x + th / 2).toFixed(3)); g(20, (y + th / 2).toFixed(3)); g(30, '0.0'); g(40, th); g(1, p.name.replace(/\n/g, ' ')); }
    });
    g(0, 'ENDSEC'); g(0, 'EOF');
    return [o.join('\r\n') + '\r\n', code];
  }

  function exportRoute(d) {
    const fmt = String(d.format || '').toLowerCase(), name = String(d.name || '').trim().slice(0, 80) || 'Route';
    const [pts, line] = cleanRoute(d.points, d.line);
    const stem = safeName(name);
    const types = { geojson: ['.geojson', 'application/geo+json'], kml: ['.kml', 'application/vnd.google-earth.kml+xml'],
                    gpx: ['.gpx', 'application/gpx+xml'], csv: ['.csv', 'text/csv'], dxf: ['.dxf', 'application/dxf'] };
    if (!types[fmt]) throw new ApiError(fmt === 'shp' ? 'Shapefile export needs the desktop app' : `Unknown format: ${fmt}`);
    let text, fname = stem + types[fmt][0], epsg = null;
    if (fmt === 'geojson') text = toGeoJSON(name, pts, line);
    else if (fmt === 'kml') text = toKML(name, pts, line);
    else if (fmt === 'gpx') text = toGPX(name, pts, line);
    else if (fmt === 'csv') text = toCSV(name, pts, line);
    else { [text, epsg] = toDXF(name, pts, line, d.epsg); fname = `${stem}_EPSG${epsg}.dxf`; }
    const headers = { 'Content-Type': types[fmt][1], 'X-Export-Filename': encodeURIComponent(fname) };
    if (epsg) headers['X-Export-EPSG'] = String(epsg);
    return new Response(new Blob([text], { type: types[fmt][1] }), { status: 200, headers });
  }

  // ================================================================ layers
  // Files and their parsed features live in IndexedDB, in this browser only.
  const IDB = (() => {
    let dbp = null;
    function db() {
      if (!dbp) dbp = new Promise((res, rej) => {
        const r = indexedDB.open('seadist-lite', 1);
        r.onupgradeneeded = () => r.result.createObjectStore('layers', { keyPath: 'file' });
        r.onsuccess = () => res(r.result);
        r.onerror = () => rej(new ApiError('Browser storage is not available (private window?)', 500));
      });
      return dbp;
    }
    function tx(mode, fn) {
      return db().then(d => new Promise((res, rej) => {
        const t = d.transaction('layers', mode), st = t.objectStore('layers');
        const r = fn(st);
        t.oncomplete = () => res(r && r.result);
        t.onerror = () => rej(new ApiError('Could not save to browser storage (full?)', 500));
      }));
    }
    return {
      all: () => tx('readonly', st => st.getAll()),
      get: file => tx('readonly', st => st.get(file)),
      put: rec => tx('readwrite', st => st.put(rec)),
      del: file => tx('readwrite', st => st.delete(file)),
    };
  })();

  // ---- zip (KMZ, XLSX): central directory + DecompressionStream
  async function unzip(buf) {
    const dv = new DataView(buf), u8 = new Uint8Array(buf);
    let eocd = -1;
    for (let i = buf.byteLength - 22; i >= Math.max(0, buf.byteLength - 65557); i--)
      if (dv.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
    if (eocd < 0) throw new ApiError('Not a valid zip file');
    const count = dv.getUint16(eocd + 10, true);
    let p = dv.getUint32(eocd + 16, true);
    const files = {};
    for (let n = 0; n < count; n++) {
      if (dv.getUint32(p, true) !== 0x02014b50) break;
      const method = dv.getUint16(p + 10, true), csize = dv.getUint32(p + 20, true);
      const nlen = dv.getUint16(p + 28, true), xlen = dv.getUint16(p + 30, true), clen = dv.getUint16(p + 32, true);
      const off = dv.getUint32(p + 42, true);
      const name = new TextDecoder().decode(u8.subarray(p + 46, p + 46 + nlen));
      files[name] = async () => {
        const lnl = dv.getUint16(off + 26, true), lxl = dv.getUint16(off + 28, true);
        const data = u8.subarray(off + 30 + lnl + lxl, off + 30 + lnl + lxl + csize);
        if (method === 0) return data;
        if (method !== 8) throw new ApiError('Unsupported zip compression');
        const ds = new Blob([data]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
        return new Uint8Array(await new Response(ds).arrayBuffer());
      };
      p += 46 + nlen + xlen + clen;
    }
    return files;
  }
  const utf8 = b => new TextDecoder('utf-8').decode(b);

  function plainText(html) {
    if (!html) return '';
    const doc = new DOMParser().parseFromString(String(html).replace(/<br\s*\/?>/gi, '\n')
      .replace(/<\/(p|div|tr|li|h\d)>/gi, '\n').replace(/<\/t[dh]>/gi, '\t'), 'text/html');
    return (doc.body.textContent || '').replace(/[ \t]{2,}/g, ' ').replace(/\n{2,}/g, '\n').trim().slice(0, 2000);
  }
  const okLL = (lat, lon) => isFinite(lat) && isFinite(lon) && Math.abs(lat) <= 90 && Math.abs(lon) <= 180;

  function parseXML(text, what) {
    const doc = new DOMParser().parseFromString(text, 'application/xml');
    if (doc.getElementsByTagName('parsererror').length) throw new ApiError(`Not valid ${what}/XML`);
    return doc;
  }
  const kids = (el, tag) => [...el.getElementsByTagNameNS('*', tag)];
  const firstText = (el, tag) => { for (const c of el.children) if (c.localName === tag) return (c.textContent || '').trim(); return ''; };
  function kmlCoords(text) {
    return String(text || '').trim().split(/\s+/).map(t => t.split(',').map(Number))
      .filter(c => c.length >= 2 && okLL(c[1], c[0])).map(c => [c[1], c[0]]);
  }
  function kmlGeoms(node) {
    const out = [];
    for (const pt of kids(node, 'Point')) { const c = kmlCoords(kids(pt, 'coordinates')[0]?.textContent); if (c.length) out.push(['point', c.slice(0, 1)]); }
    for (const tag of ['LineString', 'LinearRing']) for (const ls of kids(node, tag)) {
      const c = kmlCoords(kids(ls, 'coordinates')[0]?.textContent); if (c.length >= 2) out.push(['line', c]);
    }
    return out;
  }
  function parseKML(text) {
    const doc = parseXML(text, 'KML'), feats = [];
    for (const pm of kids(doc, 'Placemark')) {
      const name = firstText(pm, 'name'), desc = plainText(firstText(pm, 'description'));
      for (const [kind, points] of kmlGeoms(pm)) feats.push({ name, description: desc, kind, points });
    }
    if (!feats.length) for (const [kind, points] of kmlGeoms(doc)) feats.push({ name: '', description: '', kind, points });
    return feats;
  }
  async function parseKMZ(buf) {
    const files = await unzip(buf);
    const names = Object.keys(files).filter(n => n.toLowerCase().endsWith('.kml'))
      .sort((a, b) => (a.split('/').pop().toLowerCase() !== 'doc.kml') - (b.split('/').pop().toLowerCase() !== 'doc.kml'));
    if (!names.length) throw new ApiError('KMZ contains no .kml file');
    return parseKML(utf8(await files[names[0]]()));
  }
  function parseGPX(text) {
    const doc = parseXML(text, 'GPX'), feats = [];
    const pt = el => { const lat = +el.getAttribute('lat'), lon = +el.getAttribute('lon'); return okLL(lat, lon) ? [lat, lon] : null; };
    for (const trk of kids(doc, 'trk')) for (const seg of kids(trk, 'trkseg')) {
      const pts = kids(seg, 'trkpt').map(pt).filter(Boolean);
      if (pts.length >= 2) feats.push({ name: firstText(trk, 'name'), description: plainText(firstText(trk, 'desc')), kind: 'line', points: pts });
    }
    for (const rte of kids(doc, 'rte')) {
      const pts = kids(rte, 'rtept').map(pt).filter(Boolean);
      if (pts.length >= 2) feats.push({ name: firstText(rte, 'name'), description: plainText(firstText(rte, 'desc')), kind: 'line', points: pts });
    }
    for (const w of kids(doc, 'wpt')) { const p = pt(w); if (p) feats.push({ name: firstText(w, 'name'), description: plainText(firstText(w, 'desc')), kind: 'point', points: [p] }); }
    return feats;
  }
  function geomParts(g) {
    if (!g) return [];
    const flip = c => (c && okLL(+c[1], +c[0])) ? [+c[1], +c[0]] : null;
    const line = cs => (cs || []).map(flip).filter(Boolean);
    switch (g.type) {
      case 'Point': { const p = flip(g.coordinates); return p ? [['point', [p]]] : []; }
      case 'MultiPoint': return line(g.coordinates).map(p => ['point', [p]]);
      case 'LineString': return [['line', line(g.coordinates)]];
      case 'MultiLineString': case 'Polygon': return (g.coordinates || []).map(r => ['line', line(r)]);
      case 'MultiPolygon': return (g.coordinates || []).flatMap(poly => poly.map(r => ['line', line(r)]));
      case 'GeometryCollection': return (g.geometries || []).flatMap(geomParts);
      default: return [];
    }
  }
  function parseGeoJSON(text) {
    let d;
    try { d = JSON.parse(text.replace(/^﻿/, '')); } catch (e) { throw new ApiError('Not valid GeoJSON: ' + e.message); }
    if (Array.isArray(d.route) && d.locations && typeof d.locations === 'object') return routeFileFeatures(d);
    const fs = d.type === 'FeatureCollection' ? d.features || [] : d.type === 'Feature' ? [d]
             : d.coordinates ? [{ type: 'Feature', properties: {}, geometry: d }] : null;
    if (!fs) throw new ApiError('GeoJSON has no features');
    const feats = [];
    for (const f of fs) {
      const p = f.properties || {}, name = String(p.name || p.Name || p.title || '').trim();
      const desc = plainText(String(p.description || p.Description || ''));
      for (const [kind, pts] of geomParts(f.geometry)) {
        if (kind === 'point' && pts.length === 1) feats.push({ name, description: desc, kind, points: pts });
        else if (kind === 'line' && pts.length >= 2) feats.push({ name, description: desc, kind, points: pts });
      }
    }
    return feats;
  }
  function routeFileFeatures(d) {
    const pil = d.pilotage || {}, line = [], feats = [];
    d.route.forEach((n, i) => {
      const c = d.locations[n]; if (!c) return;
      const p = [+c[0], +c[1]], pp = (pil[n] || []).map(x => [+x[0], +x[1]]);
      if (i > 0) line.push(...pp.slice().reverse());
      line.push(p);
      if (i < d.route.length - 1) line.push(...pp);
      feats.push({ name: n, description: '', kind: 'point', points: [p] });
    });
    if (line.length >= 2) feats.unshift({ name: 'Route', description: 'Straight lines between the route points', kind: 'line', points: line });
    return feats;
  }

  // ---- tables: CSV / TXT / XLSX
  const DM_RE = /^\s*([NSEW])?\s*(-?\d+(?:[.,]\d+)?)\s*[°º:d ]?\s*(?:(\d+(?:[.,]\d+)?)\s*['′m:]?\s*)?(?:(\d+(?:[.,]\d+)?)\s*(?:["″]|'')?\s*)?([NSEW])?\s*$/i;
  function parseCoord(v) {
    if (v == null) return null;
    const s = String(v).trim();
    if (!s) return null;
    const plain = Number(s.replace(',', '.'));
    if (isFinite(plain) && /^-?\d+([.,]\d+)?$/.test(s)) return plain;
    const m = s.match(DM_RE);
    if (!m) return null;
    let val = Math.abs(parseFloat(m[2].replace(',', '.')));
    if (m[3]) val += parseFloat(m[3].replace(',', '.')) / 60;
    if (m[4]) val += parseFloat(m[4].replace(',', '.')) / 3600;
    const hemi = (m[1] || m[5] || '').toUpperCase();
    return (m[2].startsWith('-') || hemi === 'S' || hemi === 'W') ? -val : val;
  }
  const norm = h => String(h).toLowerCase().replace(/[^a-z]/g, '');
  function pick(cols, exact, prefixes) {
    for (const e of exact) { const c = cols.find(c => norm(c) === e); if (c != null) return c; }
    return cols.find(c => prefixes.some(p => norm(c).startsWith(p))) ?? null;
  }
  function csvRows(text) {
    text = text.replace(/^﻿/, '');
    const head = text.split(/\r?\n/, 1)[0];
    const counts = [',', ';', '\t', '|'].map(d => [d, head.split(d).length]);
    counts.sort((a, b) => b[1] - a[1]);
    const delim = counts[0][1] > 1 ? counts[0][0] : ',';
    const rows = []; let row = [], cell = '', q = false;
    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (q) { if (ch === '"') { if (text[i + 1] === '"') { cell += '"'; i++; } else q = false; } else cell += ch; }
      else if (ch === '"') q = true;
      else if (ch === delim) { row.push(cell); cell = ''; }
      else if (ch === '\n' || ch === '\r') { if (ch === '\r' && text[i + 1] === '\n') i++; row.push(cell); rows.push(row); row = []; cell = ''; }
      else cell += ch;
    }
    if (cell || row.length) { row.push(cell); rows.push(row); }
    return rows.filter(r => r.some(c => String(c).trim()));
  }
  async function xlsxRows(buf) {
    const files = await unzip(buf);
    const get = async n => files[n] ? utf8(await files[n]()) : null;
    const shared = [];
    const ss = await get('xl/sharedStrings.xml');
    if (ss) for (const si of kids(parseXML(ss, 'XLSX'), 'si')) shared.push(kids(si, 't').map(t => t.textContent).join(''));
    let sheet = 'xl/worksheets/sheet1.xml';
    const wb = await get('xl/workbook.xml'), rels = await get('xl/_rels/workbook.xml.rels');
    if (wb && rels) {
      const first = kids(parseXML(wb, 'XLSX'), 'sheet')[0];
      const rid = first && (first.getAttributeNS('http://schemas.openxmlformats.org/officeDocument/2006/relationships', 'id') || first.getAttribute('r:id'));
      const rel = kids(parseXML(rels, 'XLSX'), 'Relationship').find(r => r.getAttribute('Id') === rid);
      if (rel) { const t = rel.getAttribute('Target').replace(/^\//, ''); sheet = t.startsWith('xl/') ? t : 'xl/' + t; }
    }
    const sx = await get(sheet);
    if (!sx) throw new ApiError('The workbook has no readable sheet');
    const colIdx = ref => { let n = 0; for (const ch of ref.replace(/\d+/g, '')) n = n * 26 + ch.charCodeAt(0) - 64; return n - 1; };
    const rows = [];
    for (const r of kids(parseXML(sx, 'XLSX'), 'row')) {
      const row = [];
      for (const c of kids(r, 'c')) {
        const t = c.getAttribute('t'), v = kids(c, 'v')[0]?.textContent;
        const val = t === 's' ? shared[+v] : t === 'inlineStr' ? kids(c, 't').map(x => x.textContent).join('') : (v ?? '');
        row[colIdx(c.getAttribute('r') || 'A1')] = val;
      }
      rows.push(Array.from(row, x => x ?? ''));
    }
    return rows.filter(r => r.some(c => String(c).trim()));
  }
  function tableFeatures(rows, stem) {
    if (rows.length < 2) throw new ApiError('The table needs a header row and at least one data row');
    const cols = rows[0].map((h, i) => String(h).trim() || `col${i}`);
    const data = rows.slice(1).map(r => Object.fromEntries(cols.map((c, i) => [c, r[i] ?? ''])));
    const latC = pick(cols, ['lat', 'latitude', 'latdd', 'latdeg', 'latdecimal'], ['lat']);
    const lonC = pick(cols, ['lon', 'long', 'longitude', 'londd', 'lng', 'londeg', 'londecimal'], ['lon', 'lng']);
    const nameC = pick(cols, ['name', 'point', 'wp', 'waypoint', 'id', 'label', 'station', 'kp'], []);
    if (!latC || !lonC) {
      if (pick(cols, ['easting', 'east', 'x', 'e'], ['easting']))
        throw new ApiError('Easting/Northing tables need the desktop app (coordinate systems). In Lite, use Lat / Lon columns.');
      throw new ApiError('Could not find coordinate columns. Use headers like Lat / Lon or Latitude / Longitude.');
    }
    const good = data.map(r => [r, parseCoord(r[latC]), parseCoord(r[lonC])])
      .filter(([, a, b]) => a != null && b != null && okLL(a, b));
    if (!good.length) throw new ApiError('No readable latitude/longitude in the table');
    const feats = [];
    if (good.length >= 2) feats.push({ name: stem, description: '', kind: 'line', points: good.map(([, a, b]) => [a, b]) });
    if (nameC && good.length <= 300) good.forEach(([r, a, b]) => {
      const n = String(r[nameC] ?? '').trim();
      if (n) feats.push({ name: n, description: '', kind: 'point', points: [[a, b]] });
    });
    else if (good.length === 1) feats.push({ name: '', description: '', kind: 'point', points: [[good[0][1], good[0][2]]] });
    return feats;
  }

  const LITE_EXT = ['.kml', '.kmz', '.geojson', '.json', '.gpx', '.csv', '.txt', '.xlsx'];
  async function parseLayerFile(file) {
    const fn = file.name || 'layer', ext = (fn.match(/\.[^.]+$/) || [''])[0].toLowerCase();
    if (!LITE_EXT.includes(ext)) {
      if (['.zip', '.shp', '.gpkg', '.dxf', '.gml', '.fgb'].includes(ext))
        throw new ApiError(`${ext.slice(1).toUpperCase()} files need the desktop app. Lite reads KML, KMZ, GeoJSON, GPX, CSV, TXT and XLSX.`);
      throw new ApiError('Unsupported file type. Lite reads KML, KMZ, GeoJSON, GPX, CSV, TXT and XLSX.');
    }
    const stem = fn.replace(/\.[^.]+$/, '');
    let feats;
    if (ext === '.kmz') feats = await parseKMZ(await file.arrayBuffer());
    else if (ext === '.xlsx') feats = tableFeatures(await xlsxRows(await file.arrayBuffer()), stem);
    else {
      const text = await file.text();
      if (ext === '.kml') feats = parseKML(text);
      else if (ext === '.gpx') feats = parseGPX(text);
      else if (ext === '.csv' || ext === '.txt') feats = tableFeatures(csvRows(text), stem);
      else feats = parseGeoJSON(text);
    }
    if (!feats.length) throw new ApiError('No lines or points found in the file');
    if (feats.reduce((s, f) => s + f.points.length, 0) > 500000)
      throw new ApiError('More than 500,000 points - too many to draw in a browser.');
    feats.forEach(f => { f.length_km = f.kind === 'line' ? f.points.reduce((s, p, i) => i ? s + havKm(f.points[i - 1][0], f.points[i - 1][1], p[0], p[1]) : 0, 0) : 0; });
    return feats;
  }
  function bounds(feats) {
    let a = 90, b = 180, c = -90, d = -180, any = false;
    for (const f of feats) for (const [la, lo] of f.points) { any = true; a = Math.min(a, la); c = Math.max(c, la); b = Math.min(b, lo); d = Math.max(d, lo); }
    return any ? [[a, b], [c, d]] : null;
  }
  function row(rec) {
    return { file: rec.file, name: rec.name, colour: rec.colour, crs: '', crs_required: false, size: rec.size,
             features: rec.features.length, length_km: rec.features.reduce((s, f) => s + f.length_km, 0),
             points: rec.features.reduce((s, f) => s + f.points.length, 0), bounds: bounds(rec.features) };
  }
  async function layerList() {
    const all = (await IDB.all()) || [];
    all.sort((a, b) => a.file.localeCompare(b.file));
    return all.map(row);
  }
  async function layerSave(file, name) {
    const features = await parseLayerFile(file);
    const all = (await IDB.all()) || [];
    const taken = new Set(all.map(r => r.file));
    let fn = safeName(file.name);
    const m = fn.match(/^(.*?)(\.[^.]+)?$/);
    for (let n = 2; taken.has(fn); n++) fn = `${m[1]} (${n})${m[2] || ''}`;
    const used = new Set(all.map(r => r.colour));
    const colour = PALETTE.find(c => !used.has(c)) || PALETTE[all.length % PALETTE.length];
    await IDB.put({ file: fn, name: (name || '').trim().slice(0, 80) || m[1], colour, size: file.size,
                    type: file.type || '', blob: file, features });
    return fn;
  }
  async function layerGet(file) {
    const rec = await IDB.get(file);
    if (!rec) throw new ApiError(`No such layer: ${file}`, 404);
    return rec;
  }

  // ================================================================ router
  async function handle(path, init) {
    const method = ((init && init.method) || 'GET').toUpperCase();
    const url = new URL(path, location.href), p = decodeURIComponent(url.pathname.replace(/^.*?\/api\//, '/api/'));
    const s = state();
    let m;

    if (p === '/api/state') return json({ version: VERSION, lite: true, ...s });
    if (p === '/api/settings' && method === 'POST') {
      const d = body(init);
      for (const k of ['unit_index', 'speed', 'land_res', 'show_legend']) if (k in d) s.settings[k] = d[k];
      save(); return json({ ok: true, settings: s.settings });
    }
    if (p === '/api/locations' && method === 'POST') {
      const d = body(init), name = String(d.name || '').trim();
      if (!name) throw new ApiError('Name is required');
      const lat = +d.lat, lon = +d.lon;
      if (!isFinite(lat) || !isFinite(lon)) throw new ApiError('Lat and Lon must be numbers');
      const old = d.old_name;
      if (old && old !== name && s.locations[old]) {
        delete s.locations[old];
        if (s.pilotage[old]) { s.pilotage[name] = s.pilotage[old]; delete s.pilotage[old]; }
      }
      s.locations[name] = [lat, lon]; save(); return json({ ok: true });
    }
    if ((m = p.match(/^\/api\/locations\/(.+)$/)) && method === 'DELETE') {
      delete s.locations[m[1]]; delete s.pilotage[m[1]]; save(); return json({ ok: true });
    }
    if (p === '/api/waypoints' && method === 'POST') {
      const d = body(init), taken = n => n in s.temp_waypoints || n in s.locations;
      let name = String(d.name || '').trim();
      if (!name) { let i = 1; while (taken(`Temp ${i}`)) i++; name = `Temp ${i}`; }
      else if (taken(name)) { let i = 2; while (taken(`${name} ${i}`)) i++; name = `${name} ${i}`; }
      s.temp_waypoints[name] = [+d.lat, +d.lon]; save(); return json({ ok: true, name });
    }
    if (p === '/api/waypoints' && method === 'DELETE') {
      const n = Object.keys(s.temp_waypoints).length; s.temp_waypoints = {}; save(); return json({ ok: true, removed: n });
    }
    if ((m = p.match(/^\/api\/waypoints\/(.+)$/)) && method === 'DELETE') {
      delete s.temp_waypoints[m[1]]; save(); return json({ ok: true });
    }
    if (p === '/api/pilotage' && method === 'POST') {
      const d = body(init);
      if (!(d.port in s.locations)) throw new ApiError('Unknown port');
      const pts = (d.points || []).map(x => [+x[0], +x[1]]);
      if (pts.some(x => !isFinite(x[0]) || !isFinite(x[1]))) throw new ApiError('Points must be [lat, lon] pairs');
      if (pts.length) s.pilotage[d.port] = pts; else delete s.pilotage[d.port];
      save(); return json({ ok: true });
    }
    if (p === '/api/pilotage/add' && method === 'POST') {
      const d = body(init);
      if (!(d.port in s.locations)) throw new ApiError('Unknown port');
      (s.pilotage[d.port] = s.pilotage[d.port] || []).push([+d.lat, +d.lon]); save(); return json({ ok: true });
    }
    if (p === '/api/route/calculate') return json(await calculate(body(init).names));
    if (p === '/api/route/optimize')
      throw new ApiError('The optimizer is in the desktop version of Sea Distances. Lite shows the shipping-lane route.');
    if (p === '/api/route/import') {
      const d = body(init);
      for (const [n, c] of Object.entries(d.locations || {})) if (!(n in s.locations)) s.temp_waypoints[n] = c;
      for (const [n, pts] of Object.entries(d.pilotage || {})) if (pts && pts.length) s.pilotage[n] = pts;
      save();
      return json({ ok: true, route: (d.route || []).filter(n => coordsOf(n)) });
    }
    if (p === '/api/route/export') return exportRoute(body(init));
    if (p === '/api/network') return json(await networkGeoJSON());
    if (p === '/api/convert') return json(convert(body(init)));
    if (p === '/api/layers' && method === 'GET') return json({ layers: await layerList() });
    if (p === '/api/layers' && method === 'POST') {
      const fd = body(init), f = fd.get && fd.get('file');
      if (!f || !f.name) throw new ApiError('No file was uploaded');
      if (!f.size) throw new ApiError('The uploaded file is empty');
      if (f.size > 64 * 1024 * 1024) throw new ApiError('File is larger than 64 MB');
      const file = await layerSave(f, fd.get('name'));
      return json({ ok: true, file, layers: await layerList() });
    }
    if (p === '/api/layers/from-route' && method === 'POST') {
      const d = body(init), r = exportRoute({ ...d, format: 'geojson' });
      const name = String(d.name || '').trim() || 'Route';
      const f = new File([await r.blob()], safeName(name) + '.geojson', { type: 'application/geo+json' });
      const file = await layerSave(f, name);
      return json({ ok: true, file, layers: await layerList() });
    }
    if ((m = p.match(/^\/api\/layers\/(.+)\/geometry$/))) {
      const rec = await layerGet(m[1]); return json({ file: rec.file, features: rec.features });
    }
    if ((m = p.match(/^\/api\/layers\/(.+)\/file$/))) {
      const rec = await layerGet(m[1]);
      return new Response(rec.blob, { headers: { 'Content-Type': rec.type || 'application/octet-stream',
                                                 'X-Export-Filename': encodeURIComponent(rec.file) } });
    }
    if ((m = p.match(/^\/api\/layers\/(.+)$/)) && method === 'POST') {
      const d = body(init), rec = await layerGet(m[1]);
      if (d.name != null) rec.name = String(d.name).trim().slice(0, 80) || rec.file.replace(/\.[^.]+$/, '');
      if (d.colour != null) {
        if (!/^#[0-9A-Fa-f]{6}$/.test(d.colour)) throw new ApiError('Colour must be a hex value like #E91E63');
        rec.colour = d.colour;
      }
      await IDB.put(rec); return json({ ok: true, layers: await layerList() });
    }
    if ((m = p.match(/^\/api\/layers\/(.+)$/)) && method === 'DELETE') {
      await layerGet(m[1]); await IDB.del(m[1]); return json({ ok: true, layers: await layerList() });
    }
    if (p.startsWith('/api/vessels') || p === '/api/depth' || p === '/api/land')
      throw new ApiError('Not available in Sea Distances Lite', 404);
    throw new ApiError(`Unknown request: ${p}`, 404);
  }

  window.LiteBackend = {
    config: CFG,
    async fetch(path, init) {
      try { return await handle(path, init); }
      catch (e) { return json({ error: e.message || String(e) }, e.status || 500); }
    },
    searchPorts,
    preload() { loadNetwork().catch(() => {}); loadPorts().catch(() => {}); },
    _test: { vincenty, UTM, parseCoord, csvRows, parseKML, parseGPX, parseGeoJSON, unzip },
  };
})();
