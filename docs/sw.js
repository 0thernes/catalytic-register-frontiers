// SPDX-License-Identifier: Apache-2.0
// Network-first with instant offline cache fallback Service Worker for the
// Catalytic Register Frontiers Adaptive Forking PWA.
// Zero telemetry, zero external network requests, 100% client-side computation.
const CACHE_NAME = 'catalytic-adaptive-fork-v1.9.0';
const CORE_ASSETS = [
  './',
  './index.html',
  './catalytic-engine.js',
  './manifest.webmanifest',
  './icon.svg'
];
const OPTIONAL_ASSETS = [
  './social-preview.svg',
  './blueprint/lean_axioms.txt',
  './blueprint/six_kernel_audit.txt',
  './blueprint/statement-fidelity.md'
];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME).then(async (cache) => {
      await cache.addAll(CORE_ASSETS);
      // Optional Pages-only assets are cached best-effort so local/self-hosted servers still install cleanly
      await Promise.allSettled(OPTIONAL_ASSETS.map((url) => cache.add(url)));
    }).then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((keys) =>
      Promise.all(keys.filter((k) => k !== CACHE_NAME).map((k) => caches.delete(k)))
    ).then(() => self.clients.claim())
  );
});

self.addEventListener('fetch', (event) => {
  if (event.request.method !== 'GET') return;
  const reqUrl = new URL(event.request.url);
  if (reqUrl.origin !== self.location.origin) return;

  // Network-first so returning users always receive fresh verified code while online,
  // falling back instantaneously to the precached offline bundle in Airplane Mode.
  event.respondWith(
    fetch(event.request)
      .then((resp) => {
        if (resp && resp.status === 200 && resp.type === 'basic') {
          const copy = resp.clone();
          caches.open(CACHE_NAME).then((cache) => cache.put(event.request, copy));
        }
        return resp;
      })
      .catch(() => caches.match(event.request).then((hit) => hit || caches.match('./index.html')))
  );
});
