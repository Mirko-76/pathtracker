/* ============================================
   PathTracker — GPS Location Tracker
   GPS tracking, reverse geocoding, cross-street detection
   ============================================ */

(function () {
  'use strict';

  // ─── State ──────────────────────────────────
  const state = {
    tracking: false,
    watchId: null,
    currentPos: null,          // { lat, lng, heading, speed, accuracy, altitude, timestamp }
    trackPoints: [],           // Array of { lat, lng, timestamp, speed }
    totalDistance: 0,          // km
    lastGeocodeTime: 0,        // Throttle Nominatim
    lastCrossStreetTime: 0,    // Throttle Overpass
    currentAddress: null,      // { road, suburb, city, state, country }
    geocodePending: false,
    crossStreetPending: false,
    lastSaveTime: 0,           // Throttle localStorage writes
    lastRenderTime: 0,         // Throttle map render updates
    pendingLatLngs: [],        // Batched lat/lngs for incremental polyline update
  };

  // Track point limits to avoid unbounded growth
  const MAX_TRACK_POINTS = 5000;
  const DECIMATED_POINTS = 2500;

  // Load saved track from localStorage
  function loadSavedTrack() {
    try {
      const saved = localStorage.getItem('pathtracker_track');
      if (saved) {
        const parsed = JSON.parse(saved);
        if (Array.isArray(parsed) && parsed.length > 0) {
          state.trackPoints = parsed;
          state.totalDistance = calculateTotalDistance(parsed);
          return true;
        }
      }
    } catch (e) { /* ignore */ }
    return false;
  }

  function saveTrack() {
    try {
      localStorage.setItem('pathtracker_track', JSON.stringify(state.trackPoints));
    } catch (e) {
      // localStorage full — trim oldest points
      if (state.trackPoints.length > 1000) {
        state.trackPoints = state.trackPoints.slice(-500);
        state.totalDistance = calculateTotalDistance(state.trackPoints);
        try {
          localStorage.setItem('pathtracker_track', JSON.stringify(state.trackPoints));
        } catch (e2) { /* give up */ }
      }
    }
  }

  /** Iterative Douglas-Peucker decimation to avoid stack overflow */
  function decimatePoints(points, epsilon) {
    if (points.length <= 2) return points.slice();

    const kept = new Array(points.length).fill(false);
    kept[0] = true;
    kept[points.length - 1] = true;

    const stack = [[0, points.length - 1]];

    while (stack.length > 0) {
      const [start, end] = stack.pop();
      if (end - start <= 1) continue;

      let maxDist = 0;
      let maxIdx = start;

      for (let i = start + 1; i < end; i++) {
        const dist = perpendicularDistance(points[i], points[start], points[end]);
        if (dist > maxDist) {
          maxDist = dist;
          maxIdx = i;
        }
      }

      if (maxDist > epsilon) {
        kept[maxIdx] = true;
        stack.push([start, maxIdx]);
        stack.push([maxIdx, end]);
      }
    }

    return points.filter((_, i) => kept[i]);
  }

  function perpendicularDistance(point, lineStart, lineEnd) {
    const dx = lineEnd.lng - lineStart.lng;
    const dy = lineEnd.lat - lineStart.lat;
    const mag = Math.sqrt(dx * dx + dy * dy);
    if (mag === 0) return Math.sqrt(
      (point.lat - lineStart.lat) ** 2 + (point.lng - lineStart.lng) ** 2
    );
    const u = ((point.lng - lineStart.lng) * dx + (point.lat - lineStart.lat) * dy) / (mag * mag);
    const ix = lineStart.lng + u * dx;
    const iy = lineStart.lat + u * dy;
    return Math.sqrt((point.lng - ix) ** 2 + (point.lat - iy) ** 2);
  }

  // ─── DOM References ──────────────────────────
  const $ = (sel) => document.querySelector(sel);
  const mapEl = $('#map');
  const btnTrack = $('#btn-track');
  const btnCenter = $('#btn-center');
  const btnClear = $('#btn-clear');
  const btnShare = $('#btn-share');
  const btnPermission = $('#permission-btn');
  const overlay = $('#permission-overlay');
  const trackingBadge = $('#tracking-badge');
  const streetName = $('#street-name');
  const suburbName = $('#suburb-name');
  const crossBehind = $('#cross-behind');
  const crossAhead = $('#cross-ahead');
  const coordLat = $('#coord-lat');
  const coordLng = $('#coord-lng');
  const speedValue = $('#speed-value');
  const statDistance = $('#stat-distance');
  const statPoints = $('#stat-points');
  const statAccuracy = $('#stat-accuracy');
  const toastContainer = $('#toast-container');

  // ─── Leaflet Map Setup ──────────────────────
  const map = L.map('map', {
    zoomControl: true,
    attributionControl: false,
    zoom: 16,
    center: [0, 0],
    maxZoom: 19,
    minZoom: 3,
  });

  // Dark basemap tile layer
  L.tileLayer('https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png', {
    maxZoom: 19,
    subdomains: 'abcd',
  }).addTo(map);

  // Bright tile layer as fallback
  const lightLayer = L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
    maxZoom: 19,
    attribution: '© OpenStreetMap contributors',
  });

  // Track polyline
  const trackLine = L.polyline([], {
    color: '#4da6ff',
    weight: 3,
    opacity: 0.8,
    lineCap: 'round',
    lineJoin: 'round',
    className: 'track-line',
  }).addTo(map);

  // Current position marker (custom divIcon with pulse)
  const pulseIcon = L.divIcon({
    className: '',
    html: '<div class="pulse-marker"><div class="pulse-ring"></div><div class="pulse-dot"></div></div>',
    iconSize: [20, 20],
    iconAnchor: [10, 10],
  });

  const positionMarker = L.marker([0, 0], {
    icon: pulseIcon,
    zIndexOffset: 1000,
  }).addTo(map);

  // ─── Helper Functions ────────────────────────

  /** Haversine distance in km between two lat/lng points */
  function haversineKm(lat1, lon1, lat2, lon2) {
    const R = 6371;
    const dLat = (lat2 - lat1) * Math.PI / 180;
    const dLon = (lon2 - lon1) * Math.PI / 180;
    const a = Math.sin(dLat / 2) ** 2 +
      Math.cos(lat1 * Math.PI / 180) * Math.cos(lat2 * Math.PI / 180) *
      Math.sin(dLon / 2) ** 2;
    return R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  }

  /** Compute total distance of a track array */
  function calculateTotalDistance(points) {
    let total = 0;
    for (let i = 1; i < points.length; i++) {
      total += haversineKm(
        points[i - 1].lat, points[i - 1].lng,
        points[i].lat, points[i].lng
      );
    }
    return total;
  }

  /** Bearing from point A to point B (degrees, 0=North) */
  function bearingDeg(lat1, lon1, lat2, lon2) {
    const φ1 = lat1 * Math.PI / 180;
    const φ2 = lat2 * Math.PI / 180;
    const Δλ = (lon2 - lon1) * Math.PI / 180;
    const y = Math.sin(Δλ) * Math.cos(φ2);
    const x = Math.cos(φ1) * Math.sin(φ2) - Math.sin(φ1) * Math.cos(φ2) * Math.cos(Δλ);
    return (Math.atan2(y, x) * 180 / Math.PI + 360) % 360;
  }

  /** Angular difference between two bearings (0-180) */
  function bearingDiff(b1, b2) {
    const diff = Math.abs(b1 - b2) % 360;
    return diff > 180 ? 360 - diff : diff;
  }

  /** Format coordinates for display */
  function formatCoord(deg) {
    const d = Math.abs(deg);
    const degInt = Math.floor(d);
    const min = (d - degInt) * 60;
    const dir = deg >= 0;
    return `${degInt}° ${min.toFixed(3)}'`;
  }

  function formatLat(lat) {
    return formatCoord(lat) + (lat >= 0 ? ' N' : ' S');
  }

  function formatLng(lng) {
    return formatCoord(lng) + (lng >= 0 ? ' E' : ' W');
  }

  /** Show a toast notification */
  function showToast(message) {
    const toast = document.createElement('div');
    toast.className = 'toast';
    toast.textContent = message;
    toastContainer.appendChild(toast);
    setTimeout(() => {
      if (toast.parentNode) toast.remove();
    }, 2500);
  }

  // ─── Reverse Geocoding (Nominatim) ──────────
  async function reverseGeocode(lat, lng) {
    const now = Date.now();
    if (now - state.lastGeocodeTime < 2000) return; // Throttle: max 1 req per 2s
    if (state.geocodePending) return;

    state.geocodePending = true;
    state.lastGeocodeTime = now;

    try {
      const url = `https://nominatim.openstreetmap.org/reverse?format=json&lat=${lat}&lon=${lng}&zoom=18&addressdetails=1&accept-language=en`;
      const resp = await fetch(url, {
        headers: { 'User-Agent': 'PathTracker-PWA/1.0' },
      });
      if (!resp.ok) throw new Error(`HTTP ${resp.status}`);

      const data = await resp.json();
      if (data && data.address) {
        const addr = data.address;
        state.currentAddress = {
          road: addr.road || addr.pedestrian || addr.path || addr.footway || null,
          suburb: addr.suburb || addr.neighbourhood || addr.hamlet || null,
          city: addr.city || addr.town || addr.village || null,
          state: addr.state || null,
          country: addr.country || null,
        };
        updateAddressUI();
      }
    } catch (err) {
      console.warn('Reverse geocode failed:', err.message);
    } finally {
      state.geocodePending = false;
    }
  }

  function updateAddressUI() {
    const addr = state.currentAddress;
    if (!addr) return;

    const road = addr.road || 'Unnamed Road';
    streetName.textContent = road;

    const locality = addr.suburb || addr.city || addr.state || '';
    suburbName.textContent = locality ? `${locality}${addr.country ? ', ' + addr.country : ''}` : (addr.country || 'Unknown');
  }

  // ─── Cross Street Detection (Overpass API) ──
  async function findCrossStreets(lat, lng, heading) {
    const now = Date.now();
    if (now - state.lastCrossStreetTime < 5000) return; // Throttle: max 1 per 5s
    if (state.crossStreetPending) return;
    if (!state.currentAddress || !state.currentAddress.road) return;

    state.crossStreetPending = true;
    state.lastCrossStreetTime = now;

    try {
      const query = `
        [out:json][timeout:10];
        way(around:40,${lat},${lng})[highway~"^(primary|secondary|tertiary|residential|unclassified|living_street|service|pedestrian)$"];
        out tags center 15;
      `.replace(/\s+/g, ' ').trim();

      const resp = await fetch('https://overpass-api.de/api/interpreter', {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: 'data=' + encodeURIComponent(query),
      });

      if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
      const data = await resp.json();

      const currentRoad = state.currentAddress.road.toLowerCase().trim();
      const streets = [];

      for (const el of data.elements) {
        if (!el.tags || !el.tags.name) continue;
        const name = el.tags.name.trim();
        // Skip if same as current road
        if (name.toLowerCase() === currentRoad) continue;
        // Skip duplicates
        if (streets.some(s => s.name.toLowerCase() === name.toLowerCase())) continue;

        streets.push({
          name,
          lat: el.center ? el.center.lat : el.bounds.minlat,
          lng: el.center ? el.center.lon : el.bounds.minlon,
        });
      }

      updateCrossStreetsUI(streets, heading);
    } catch (err) {
      console.warn('Cross street query failed:', err.message);
    } finally {
      state.crossStreetPending = false;
    }
  }

  function updateCrossStreetsUI(streets, heading) {
    if (!state.currentPos) return;
    if (heading == null || heading < 0) {
      // No heading — just show nearest cross streets
      const names = streets.slice(0, 2).map(s => s.name);
      crossBehind.textContent = names[0] || '—';
      crossAhead.textContent = names[1] || '—';
      return;
    }

    // Classify streets as ahead (+/-90° of heading) or behind
    const ahead = [];
    const behind = [];

    for (const s of streets) {
      const b = bearingDeg(state.currentPos.lat, state.currentPos.lng, s.lat, s.lng);
      const diff = bearingDiff(heading, b);
      if (diff <= 100) {
        ahead.push(s);
      } else {
        behind.push(s);
      }
    }

    // Sort by distance (approximate by bearing diff from heading)
    ahead.sort((a, b) => {
      const diffA = bearingDiff(heading, bearingDeg(state.currentPos.lat, state.currentPos.lng, a.lat, a.lng));
      const diffB = bearingDiff(heading, bearingDeg(state.currentPos.lat, state.currentPos.lng, b.lat, b.lng));
      return diffA - diffB;
    });
    behind.sort((a, b) => {
      const diffA = bearingDiff((heading + 180) % 360, bearingDeg(state.currentPos.lat, state.currentPos.lng, a.lat, a.lng));
      const diffB = bearingDiff((heading + 180) % 360, bearingDeg(state.currentPos.lat, state.currentPos.lng, b.lat, b.lng));
      return diffA - diffB;
    });

    crossBehind.textContent = behind[0] ? behind[0].name : '—';
    crossAhead.textContent = ahead[0] ? ahead[0].name : '—';
  }

  // ─── UI Updates ─────────────────────────────
  function updateUI(pos) {
    // Coordinates
    coordLat.textContent = `Lat: ${formatLat(pos.lat)}`;
    coordLng.textContent = `Lng: ${formatLng(pos.lng)}`;

    // Speed
    const speedKmh = pos.speed != null && pos.speed >= 0 ? (pos.speed * 3.6) : null;
    if (speedKmh != null) {
      speedValue.textContent = speedKmh < 10 ? speedKmh.toFixed(1) : Math.round(speedKmh);
    } else {
      speedValue.textContent = '—';
    }

    // Stats
    statDistance.textContent = state.totalDistance.toFixed(2) + ' km';
    statPoints.textContent = state.trackPoints.length;
    if (pos.accuracy != null) {
      statAccuracy.textContent = `±${Math.round(pos.accuracy)}m`;
    } else {
      statAccuracy.textContent = '—';
    }
  }

  function updateMap(pos) {
    // Update marker position
    positionMarker.setLatLng([pos.lat, pos.lng]);

    // Add to track
    state.trackPoints.push({
      lat: pos.lat,
      lng: pos.lng,
      timestamp: pos.timestamp || Date.now(),
      speed: pos.speed,
    });

    // Update track distance
    if (state.trackPoints.length >= 2) {
      const prev = state.trackPoints[state.trackPoints.length - 2];
      state.totalDistance += haversineKm(prev.lat, prev.lng, pos.lat, pos.lng);
    }

    // Decimate if exceeding max points
    if (state.trackPoints.length > MAX_TRACK_POINTS) {
      const lastPoint = state.trackPoints[state.trackPoints.length - 1];
      state.trackPoints = decimatePoints(state.trackPoints, 0.0001);
      // Ensure we don't exceed the target after decimation
      if (state.trackPoints.length > DECIMATED_POINTS) {
        const step = Math.ceil(state.trackPoints.length / DECIMATED_POINTS);
        state.trackPoints = state.trackPoints.filter((_, i) => i % step === 0);
        // Always keep the last (current) point
        if (state.trackPoints[state.trackPoints.length - 1] !== lastPoint) {
          state.trackPoints.push(lastPoint);
        }
      }
      // Recalculate distance and full polyline rebuild after decimation
      state.totalDistance = calculateTotalDistance(state.trackPoints);
      state.pendingLatLngs = [];
      trackLine.setLatLngs(state.trackPoints.map(p => [p.lat, p.lng]));
    } else {
      // Incremental update: batch points and update every ~300ms
      state.pendingLatLngs.push([pos.lat, pos.lng]);
      const now = Date.now();
      if (now - state.lastRenderTime > 300) {
        // Add batched points to polyline
        for (const ll of state.pendingLatLngs) {
          trackLine.addLatLng(ll);
        }
        state.pendingLatLngs = [];
        state.lastRenderTime = now;
      }
    }

    // Throttle localStorage writes to every 3 seconds
    const nowSave = Date.now();
    if (nowSave - state.lastSaveTime > 3000) {
      state.lastSaveTime = nowSave;
      saveTrack();
    }
  }

  // ─── GPS Position Handler ───────────────────
  function onPosition(position) {
    const coords = position.coords;
    const pos = {
      lat: coords.latitude,
      lng: coords.longitude,
      heading: coords.heading != null ? coords.heading : null,
      speed: coords.speed != null && coords.speed >= 0 ? coords.speed : null,
      accuracy: coords.accuracy,
      altitude: coords.altitude,
      timestamp: position.timestamp || Date.now(),
    };

    // Compute heading fallback from last known point to new position if GPS heading is null
    let heading = pos.heading;
    if (heading == null && state.trackPoints.length >= 1) {
      const prev = state.trackPoints[state.trackPoints.length - 1];
      heading = bearingDeg(prev.lat, prev.lng, pos.lat, pos.lng);
    }

    state.currentPos = pos;

    // On first fix, center map
    if (state.trackPoints.length === 0) {
      map.setView([pos.lat, pos.lng], 17, { animate: true });
    }

    updateMap(pos);
    updateUI(pos);

    // Reverse geocode (throttled internally)
    reverseGeocode(pos.lat, pos.lng);

    // Cross streets — pass computed heading for front/back classification
    findCrossStreets(pos.lat, pos.lng, heading);
  }

  function onPositionError(err) {
    console.error('Geolocation error:', err.code, err.message);

    switch (err.code) {
      case err.PERMISSION_DENIED:
        showToast('Location permission denied. Check your device settings.');
        overlay.classList.remove('hidden');
        break;
      case err.POSITION_UNAVAILABLE:
        showToast('GPS signal unavailable. Check your location.');
        break;
      case err.TIMEOUT:
        showToast('GPS request timed out. Retrying...');
        break;
      default:
        showToast('GPS error: ' + err.message);
    }
  }

  // ─── Tracking Controls ──────────────────────
  function startTracking() {
    if (!navigator.geolocation) {
      showToast('Geolocation not supported on this device.');
      return;
    }

    state.watchId = navigator.geolocation.watchPosition(
      onPosition,
      onPositionError,
      {
        enableHighAccuracy: true,
        timeout: 15000,
        maximumAge: 0,
      }
    );

    state.tracking = true;
    updateTrackingUI();
  }

  function stopTracking() {
    if (state.watchId != null) {
      navigator.geolocation.clearWatch(state.watchId);
      state.watchId = null;
    }

    // Flush any pending polyline points
    if (state.pendingLatLngs.length > 0) {
      for (const ll of state.pendingLatLngs) {
        trackLine.addLatLng(ll);
      }
      state.pendingLatLngs = [];
    }

    // Final save
    saveTrack();

    state.tracking = false;
    state.currentPos = null;
    updateTrackingUI();
  }

  function toggleTracking() {
    if (state.tracking) {
      stopTracking();
    } else {
      startTracking();
    }
  }

  function updateTrackingUI() {
    if (state.tracking) {
      btnTrack.classList.remove('tracking-off');
      btnTrack.classList.add('tracking-on');
      btnTrack.querySelector('.btn-track-icon').textContent = '⏹';
      btnTrack.querySelector('.btn-track-text').textContent = 'Stop Tracking';
      trackingBadge.classList.remove('paused');
      trackingBadge.classList.add('active');
      trackingBadge.textContent = '● Tracking';
    } else {
      btnTrack.classList.remove('tracking-on');
      btnTrack.classList.add('tracking-off');
      btnTrack.querySelector('.btn-track-icon').textContent = '▶';
      btnTrack.querySelector('.btn-track-text').textContent = 'Start Tracking';
      trackingBadge.classList.remove('active');
      trackingBadge.classList.add('paused');
      trackingBadge.textContent = '● Paused';
    }
  }

  function centerOnMe() {
    if (state.currentPos) {
      map.setView([state.currentPos.lat, state.currentPos.lng], 17, { animate: true, duration: 0.5 });
    } else if (state.trackPoints.length > 0) {
      const last = state.trackPoints[state.trackPoints.length - 1];
      map.setView([last.lat, last.lng], 17, { animate: true, duration: 0.5 });
    } else {
      showToast('No position available yet.');
    }
  }

  function clearPath() {
    if (state.trackPoints.length === 0) {
      showToast('No path to clear.');
      return;
    }

    state.trackPoints = [];
    state.totalDistance = 0;
    state.pendingLatLngs = [];
    state.currentAddress = null;
    state.lastSaveTime = 0;
    state.lastRenderTime = 0;
    trackLine.setLatLngs([]);
    localStorage.removeItem('pathtracker_track');

    // Reset UI
    streetName.textContent = '—';
    suburbName.textContent = 'Waiting for GPS...';
    crossBehind.textContent = '—';
    crossAhead.textContent = '—';
    coordLat.textContent = 'Lat: —';
    coordLng.textContent = 'Lng: —';
    speedValue.textContent = '—';
    statDistance.textContent = '0.00 km';
    statPoints.textContent = '0';

    showToast('Path cleared.');
  }

  function shareTrack() {
    if (state.trackPoints.length < 2) {
      showToast('Not enough points to share.');
      return;
    }

    const last = state.trackPoints[state.trackPoints.length - 1];
    const text = [
      '📍 My GPS track from PathTracker',
      `Distance: ${state.totalDistance.toFixed(2)} km`,
      `Points: ${state.trackPoints.length}`,
      `Current: ${last.lat.toFixed(6)}, ${last.lng.toFixed(6)}`,
    ].join('\n');

    if (navigator.share) {
      navigator.share({
        title: 'My GPS Track',
        text: text,
      }).catch(() => { /* user cancelled */ });
    } else {
      // Fallback: copy to clipboard
      navigator.clipboard.writeText(text).then(() => {
        showToast('Track summary copied to clipboard!');
      }).catch(() => {
        showToast('Sharing not supported on this device.');
      });
    }
  }

  // ─── Permission Handling ────────────────────
  function requestPermission() {
    overlay.classList.add('hidden');

    // Try a one-shot position to trigger the permission prompt
    navigator.geolocation.getCurrentPosition(
      () => {
        // Permission granted — start tracking
        if (!state.tracking) {
          startTracking();
        }
      },
      (err) => {
        if (err.code === err.PERMISSION_DENIED) {
          showToast('Location access denied. Enable in Settings > Safari > Location.');
          overlay.classList.remove('hidden');
        } else {
          showToast('Could not get location. Try again.');
        }
      },
      { enableHighAccuracy: true, timeout: 10000, maximumAge: 0 }
    );
  }

  function checkPermission() {
    if (!navigator.permissions) {
      // Older browsers — just try to get position
      overlay.classList.remove('hidden');
      return;
    }

    navigator.permissions.query({ name: 'geolocation' }).then((result) => {
      if (result.state === 'granted') {
        overlay.classList.add('hidden');
        startTracking();
      } else if (result.state === 'prompt') {
        overlay.classList.remove('hidden');
      } else {
        overlay.classList.remove('hidden');
      }

      result.addEventListener('change', () => {
        if (result.state === 'granted') {
          overlay.classList.add('hidden');
          if (!state.tracking) startTracking();
        }
      });
    }).catch(() => {
      // iOS standalone PWA or older browser — try getCurrentPosition to check permission
      overlay.classList.remove('hidden');
    });
  }

  // ─── Event Listeners ────────────────────────
  btnTrack.addEventListener('click', toggleTracking);
  btnCenter.addEventListener('click', centerOnMe);
  btnClear.addEventListener('click', clearPath);
  btnShare.addEventListener('click', shareTrack);
  btnPermission.addEventListener('click', requestPermission);

  // ─── Keyboard Shortcuts ─────────────────────
  document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;
    switch (e.key.toLowerCase()) {
      case 's':
        e.preventDefault();
        toggleTracking();
        break;
      case 'c':
        e.preventDefault();
        centerOnMe();
        break;
    }
  });

  // ─── Initialization ─────────────────────────
  function init() {
    // Register service worker for PWA
    if ('serviceWorker' in navigator) {
      navigator.serviceWorker.register('/sw.js').catch((err) => {
        console.warn('SW registration failed:', err);
      });
    }

    // Load saved track
    const hasSaved = loadSavedTrack();
    if (hasSaved && state.trackPoints.length > 0) {
      trackLine.setLatLngs(state.trackPoints.map(p => [p.lat, p.lng]));
      statDistance.textContent = state.totalDistance.toFixed(2) + ' km';
      statPoints.textContent = state.trackPoints.length;

      // Center map on last known position
      const last = state.trackPoints[state.trackPoints.length - 1];
      map.setView([last.lat, last.lng], 16);
    }

    // Check permission and auto-start
    if (navigator.geolocation) {
      checkPermission();
    } else {
      showToast('Geolocation is not supported on this device.');
      overlay.classList.remove('hidden');
      overlay.querySelector('h2').textContent = 'Device Not Supported';
      overlay.querySelector('p').textContent = 'Your device does not support GPS geolocation. This app requires a GPS-enabled device.';
      btnPermission.style.display = 'none';
    }
  }

  init();

})();
