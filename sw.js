'use strict';

// Версию нужно менять при изменении списка APP_FILES
const APP_CACHE = 'jackalizer-app-v2';
const CDN_CACHE = 'jackalizer-cdn-v1';
const SHARE_CACHE = 'jackalizer-share';

const APP_FILES = [
    '/',
    '/style.css',
    '/app.js',
    '/manifest.webmanifest',
    '/img/favicon.png',
    '/img/jackalizer2.webp',
    '/img/background-wide.webp',
    '/img/icon-192.png'
];

self.addEventListener('install', (event) => {
    event.waitUntil(caches.open(APP_CACHE).then(cache => cache.addAll(APP_FILES)));
    self.skipWaiting();
});

self.addEventListener('activate', (event) => {
    const keep = [APP_CACHE, CDN_CACHE, SHARE_CACHE];
    event.waitUntil(
        caches.keys()
            .then(keys => Promise.all(keys.filter(k => !keep.includes(k)).map(k => caches.delete(k))))
            .then(() => self.clients.claim())
    );
});

// Файлы приложения: сначала сеть (чтобы обновления приходили сразу), без сети — кэш
async function networkFirst(request) {
    const cache = await caches.open(APP_CACHE);
    try {
        const response = await fetch(request);
        if (response.ok) cache.put(request, response.clone());
        return response;
    } catch (err) {
        const cached = await cache.match(request, { ignoreSearch: request.mode === 'navigate' });
        if (cached) return cached;
        throw err;
    }
}

// Библиотека поиска лиц с CDN: адреса с версией не меняются, берём из кэша
async function cacheFirst(request) {
    const cache = await caches.open(CDN_CACHE);
    const cached = await cache.match(request);
    if (cached) return cached;
    const response = await fetch(request);
    if (response.ok) cache.put(request, response.clone());
    return response;
}

// «Поделиться» -> Jackalizer на телефоне: сохраняем картинку и открываем приложение
async function receiveShare(request) {
    const form = await request.formData();
    const file = form.get('image');
    if (file && typeof file !== 'string') {
        const cache = await caches.open(SHARE_CACHE);
        await cache.put('/shared-image', new Response(file, {
            headers: {
                'content-type': file.type || 'image/jpeg',
                'x-file-name': encodeURIComponent(file.name || 'image')
            }
        }));
    }
    return Response.redirect('/?shared=1', 303);
}

self.addEventListener('fetch', (event) => {
    const { request } = event;
    const url = new URL(request.url);

    if (request.method === 'POST' && url.origin === location.origin && url.pathname === '/share-target') {
        event.respondWith(receiveShare(request));
        return;
    }
    if (request.method !== 'GET') return;

    if (url.origin === location.origin) {
        if (url.pathname.startsWith('/_vercel/')) return;
        event.respondWith(networkFirst(request));
    } else if (url.hostname === 'cdn.jsdelivr.net' && url.pathname.includes('@vladmandic/face-api@')) {
        event.respondWith(cacheFirst(request));
    }
});
