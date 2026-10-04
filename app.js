'use strict';

// ============ КОНСТАНТЫ ============

const PREVIEW_MAX_SIDE = 1000;     // длинная сторона превью
const REF_SIDE = 800;              // ползунки заданы в пикселях изображения с длинной стороной 800
const EXPORT_MAX_PIXELS = 16000000; // ограничение площади canvas (iOS Safari ~16.7 Мп)
const HISTORY_LIMIT = 50;
const EFFECT_CACHE_LIMIT = 8;
const ZOOM_MAX = 8;

const FACE_API_URL = 'https://cdn.jsdelivr.net/npm/@vladmandic/face-api@1.7.15/dist/face-api.esm.js';
const FACE_MODEL_URL = 'https://cdn.jsdelivr.net/npm/@vladmandic/face-api@1.7.15/model/';

const EFFECTS = {
    pixelate: { name: 'Пикселизация', label: 'Степень пикселизации', min: 2, max: 100, value: 62 },
    blur: { name: 'Блюр', label: 'Сила блюра', min: 1, max: 50, value: 10 },
    glitch: { name: 'Глитч', label: 'Интенсивность глитча', min: 1, max: 50, value: 15 },
    jpeg: { name: 'Шакализация', label: 'Степень шакализации', min: 1, max: 100, value: 60 }
};
const EFFECT_ORDER = ['pixelate', 'blur', 'glitch', 'jpeg'];

// ============ ЭЛЕМЕНТЫ ============

const $ = (id) => document.getElementById(id);

const dropZone = $('dropZone');
const fileInput = $('fileInput');
const mainContainer = $('mainContainer');
const rightPanel = $('rightPanel');
const canvasWrap = $('canvasWrap');
const viewport = $('viewport');
const canvas = $('canvas');
const ctx = canvas.getContext('2d');
const brushCursor = $('brushCursor');
const zoomOutBtn = $('zoomOutBtn');
const zoomInBtn = $('zoomInBtn');
const zoomFitBtn = $('zoomFitBtn');
const toastEl = $('toast');

const effectButtons = document.querySelectorAll('[data-effect]');
const amountSlider = $('amount');
const amountLabel = $('amountLabel');
const amountValue = $('amountValue');
const reseedBtn = $('reseedBtn');
const facesBtn = $('facesBtn');
const brushBtn = $('brushBtn');
const eraserBtn = $('eraserBtn');
const brushSizeSlider = $('brushSize');
const softnessSlider = $('softness');
const eraseActiveOnly = $('eraseActiveOnly');
const undoBtn = $('undoBtn');
const redoBtn = $('redoBtn');
const compareBtn = $('compareBtn');
const clearMaskBtn = $('clearMaskBtn');
const applyFullBtn = $('applyFullBtn');
const newLayerBtn = $('newLayerBtn');
const layerList = $('layerList');
const formatSelect = $('formatSelect');
const downloadBtn = $('downloadBtn');
const shareBtn = $('shareBtn');
const copyBtn = $('copyBtn');
const resetBtn = $('resetBtn');

// ============ СОСТОЯНИЕ ============

let image = null;          // загруженное изображение (оригинал)
let imageUrl = null;       // object URL оригинала
let fileBaseName = 'image';
let pw = 0, ph = 0;        // размер превью
let unit = 1;              // пикселей превью на единицу ползунков
let srcCanvas = null;      // оригинал в размере превью
let srcData = null;

let currentEffect = 'pixelate';
let tool = 'brush';
// Сила эффекта для новых слоёв (запоминается последнее значение каждого эффекта)
const defaults = {};
EFFECT_ORDER.forEach(type => { defaults[type] = EFFECTS[type].value; });

// Слои: [{id, type, amount, seed, hidden, note, strokes}] — эффект + маска из векторных мазков.
// Мазки: {kind: 'paint'|'erase', r, hardness, points: [x0, y0, x1, y1, ...]},
//        {kind: 'ellipse', cx, cy, rx, ry, hardness} или {kind: 'fill'}.
// Координаты и радиус — в пикселях превью, при экспорте мазки перерисовываются в полном разрешении.
let layers = [];
let activeId = null;           // выбранный слой; null — следующий мазок создаст новый слой
let layerSeq = 0;
const masks = new Map();       // layerId -> canvas маски превью
const maskRevs = new Map();    // layerId -> счётчик изменений маски
const stackedEffects = new Map(); // layerId -> {sig, canvas}: эффект, посчитанный от слоёв под ним
const effectCache = new Map(); // ключ эффекта -> canvas превью
const undoStack = [];
const redoStack = [];

let live = null;               // текущий мазок {stroke, ctxs, carry, pointerId, ...}
let gesture = null;            // перемещение или масштабирование холста
const touches = new Map();     // активные касания: pointerId -> {x, y}
const view = { z: 1, x: 0, y: 0 };
let spaceDown = false;
let pointerOverCanvas = false;
let sliderInHistory = false;   // текущее перетаскивание ползунка уже записано в историю
let lastPointer = null;        // последнее положение мыши над холстом (для круга кисти)
let comparing = false;
let busy = false;
let detecting = false;
let docVersion = 0;            // меняется при любом изменении результата
let exportCache = null;        // {version, type, blob}

const tmpCanvas = document.createElement('canvas');
const tmpCtx = tmpCanvas.getContext('2d');

function newSeed() {
    return (Math.random() * 0x7fffffff) | 0;
}

const clamp = (v, min, max) => Math.min(Math.max(v, min), max);

// ============ ЭФФЕКТЫ ============
// Все эффекты работают с ImageData и параметром s — сколько пикселей
// результата приходится на единицу ползунка. Превью и экспорт используют
// одни и те же функции, поэтому скачанный файл совпадает с тем, что на экране.

function pixelateEffect(src, block) {
    const { width: w, height: h, data: d } = src;
    const out = new Uint8ClampedArray(d.length);
    if (block < 1.5) {
        out.set(d);
        return new ImageData(out, w, h);
    }

    for (let y0 = 0, by = 1; y0 < h; by++) {
        const y1 = Math.min(h, Math.round(by * block));
        for (let x0 = 0, bx = 1; x0 < w; bx++) {
            const x1 = Math.min(w, Math.round(bx * block));

            // Усредняем цвет блока с учётом прозрачности
            let r = 0, g = 0, b = 0, a = 0;
            for (let y = y0; y < y1; y++) {
                for (let i = (y * w + x0) * 4, end = (y * w + x1) * 4; i < end; i += 4) {
                    const al = d[i + 3];
                    r += d[i] * al;
                    g += d[i + 1] * al;
                    b += d[i + 2] * al;
                    a += al;
                }
            }
            const count = (x1 - x0) * (y1 - y0);
            if (a > 0) {
                r /= a; g /= a; b /= a;
            }
            a /= count;

            for (let y = y0; y < y1; y++) {
                for (let i = (y * w + x0) * 4, end = (y * w + x1) * 4; i < end; i += 4) {
                    out[i] = r;
                    out[i + 1] = g;
                    out[i + 2] = b;
                    out[i + 3] = a;
                }
            }
            x0 = x1;
        }
        y0 = y1;
    }
    return new ImageData(out, w, h);
}

// Размеры трёх box-фильтров, приближающих гауссово размытие
function boxesForGauss(sigma, n) {
    const wIdeal = Math.sqrt((12 * sigma * sigma / n) + 1);
    let wl = Math.floor(wIdeal);
    if (wl % 2 === 0) wl--;
    const wu = wl + 2;
    const mIdeal = (12 * sigma * sigma - n * wl * wl - 4 * n * wl - 3 * n) / (-4 * wl - 4);
    const m = Math.round(mIdeal);
    const sizes = [];
    for (let i = 0; i < n; i++) sizes.push(i < m ? wl : wu);
    return sizes;
}

// Горизонтальный box blur скользящим окном, края продлеваются
function boxBlurH(src, dst, w, h, rad) {
    const k = 1 / (rad + rad + 1);
    const wm = w - 1;
    for (let y = 0; y < h; y++) {
        const row = y * w * 4;
        let r = (rad + 1) * src[row];
        let g = (rad + 1) * src[row + 1];
        let b = (rad + 1) * src[row + 2];
        let a = (rad + 1) * src[row + 3];
        for (let j = 0; j < rad; j++) {
            const i = row + Math.min(j, wm) * 4;
            r += src[i]; g += src[i + 1]; b += src[i + 2]; a += src[i + 3];
        }
        for (let x = 0; x < w; x++) {
            const ai = row + Math.min(x + rad, wm) * 4;
            const si = row + Math.max(x - rad - 1, 0) * 4;
            r += src[ai] - src[si];
            g += src[ai + 1] - src[si + 1];
            b += src[ai + 2] - src[si + 2];
            a += src[ai + 3] - src[si + 3];
            const o = row + x * 4;
            dst[o] = r * k;
            dst[o + 1] = g * k;
            dst[o + 2] = b * k;
            dst[o + 3] = a * k;
        }
    }
}

// Вертикальный проход идёт построчно с суммами по столбцам — так быстрее для кэша
function boxBlurV(src, dst, w, h, rad) {
    const k = 1 / (rad + rad + 1);
    const hm = h - 1;
    const stride = w * 4;
    const acc = new Int32Array(stride);
    for (let i = 0; i < stride; i++) acc[i] = (rad + 1) * src[i];
    for (let j = 0; j < rad; j++) {
        const off = Math.min(j, hm) * stride;
        for (let i = 0; i < stride; i++) acc[i] += src[off + i];
    }
    for (let y = 0; y < h; y++) {
        const addOff = Math.min(y + rad, hm) * stride;
        const subOff = Math.max(y - rad - 1, 0) * stride;
        const outOff = y * stride;
        for (let i = 0; i < stride; i++) {
            acc[i] += src[addOff + i] - src[subOff + i];
            dst[outOff + i] = acc[i] * k;
        }
    }
}

// Гауссово размытие (sigma как у CSS blur()), не зависит от поддержки ctx.filter
function blurEffect(src, sigma) {
    const { width: w, height: h } = src;
    const a = new Uint8ClampedArray(src.data);
    if (sigma >= 0.5) {
        const b = new Uint8ClampedArray(a.length);
        for (const size of boxesForGauss(sigma, 3)) {
            const r = (size - 1) / 2;
            if (r < 1) continue;
            boxBlurH(a, b, w, h, r);
            boxBlurV(b, a, w, h, r);
        }
    }
    return new ImageData(a, w, h);
}

// Детерминированный генератор случайных чисел (mulberry32)
function seededRandom(seed) {
    let a = seed | 0;
    return () => {
        a = (a + 0x6D2B79F5) | 0;
        let t = Math.imul(a ^ (a >>> 15), 1 | a);
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
}

// Шум для ячейки сетки (одна ячейка = единица ползунка)
function cellNoise(cx, cy, seed) {
    const hash = (Math.imul(cx, 73856093) ^ Math.imul(cy, 19349663) ^ seed) >>> 0;
    if (hash % 10000 >= 1000) return 0;
    const noiseHash = Math.imul(hash, 2654435761) >>> 0;
    return Math.floor(((noiseHash % 10000) / 10000 - 0.5) * 100);
}

function glitchEffect(src, intensity, seed, s) {
    const { width: w, height: h, data: o } = src;
    const out = new Uint8ClampedArray(o);
    const rng = seededRandom(seed);
    const wm = w - 1;
    const hm = h - 1;
    const clampX = (x) => (x < 0 ? 0 : x > wm ? wm : x);

    // RGB-смещение
    const rgbOffset = Math.round(intensity / 2 * s);

    // Горизонтальные блоки искажений (в единицах ползунка)
    const blocks = [];
    const numBlocks = Math.floor(intensity / 5);
    for (let i = 0; i < numBlocks; i++) {
        blocks.push({
            y: rng() * (h / s),
            height: rng() * intensity * 2 + 5,
            shift: Math.round((rng() - 0.5) * intensity * 3 * s),
            type: rng()
        });
    }

    // Случайные сдвинутые линии с шумом
    const rows = Math.max(1, Math.ceil(h / s));
    const lineShift = new Int32Array(rows);
    const lineNoisy = new Uint8Array(rows);
    for (let row = 0; row < rows; row++) {
        if (rng() < intensity / 150) {
            lineNoisy[row] = 1;
            lineShift[row] = Math.round((rng() - 0.5) * intensity * 2 * s);
        }
    }

    // Вертикальные полосы
    const stripes = [];
    const numStripes = Math.floor(intensity / 8);
    for (let i = 0; i < numStripes; i++) {
        stripes.push({
            x: Math.floor(rng() * w),
            width: Math.max(1, Math.round((Math.floor(rng() * 5) + 1) * s)),
            shift: Math.round((rng() - 0.5) * intensity * s)
        });
    }

    for (let y = 0; y < h; y++) {
        const uy = y / s;
        const row = Math.min(rows - 1, Math.floor(uy));

        let blockShift = 0;
        let blockType = 1;
        for (const block of blocks) {
            if (uy >= block.y && uy < block.y + block.height) {
                blockShift = block.shift;
                if (blockShift !== 0) blockType = block.type;
                break;
            }
        }

        const shift = blockShift + lineShift[row];
        const noisy = lineNoisy[row] === 1;
        const base = y * w * 4;

        for (let x = 0; x < w; x++) {
            let r = o[base + clampX(x + shift + rgbOffset) * 4];
            let g = o[base + clampX(x + shift) * 4 + 1];
            let b = o[base + clampX(x + shift - rgbOffset) * 4 + 2];

            // Специальные эффекты в блоках
            if (blockType < 0.3) {
                r = 255 - r; g = 255 - g; b = 255 - b;          // инверсия
            } else if (blockType < 0.5) {
                r = r * 1.5;                                     // усиление красного
            } else if (blockType < 0.7) {
                g = g * 1.3; b = b * 1.3;                        // усиление cyan
            }

            if (noisy) {
                const noise = cellNoise(Math.floor(x / s), row, seed);
                r += noise; g += noise; b += noise;
            }

            const i = base + x * 4;
            out[i] = r;      // Uint8ClampedArray сам обрезает до 0..255
            out[i + 1] = g;
            out[i + 2] = b;
        }
    }

    for (const stripe of stripes) {
        const x1 = Math.min(w, stripe.x + stripe.width);
        for (let y = 0; y < h; y++) {
            const sy = Math.min(Math.max(y + stripe.shift, 0), hm);
            for (let x = stripe.x; x < x1; x++) {
                const i = (y * w + x) * 4;
                const j = (sy * w + x) * 4;
                out[i] = o[j];
                out[i + 1] = o[j + 1];
                out[i + 2] = o[j + 2];
            }
        }
    }

    return new ImageData(out, w, h);
}

// ---------- Шакализация: настоящее JPEG-сжатие с низким качеством ----------

const JPEG_LUMA = [
    16, 11, 10, 16, 24, 40, 51, 61, 12, 12, 14, 19, 26, 58, 60, 55,
    14, 13, 16, 24, 40, 57, 69, 56, 14, 17, 22, 29, 51, 87, 80, 62,
    18, 22, 37, 56, 68, 109, 103, 77, 24, 35, 55, 64, 81, 104, 113, 92,
    49, 64, 78, 87, 103, 121, 120, 101, 72, 92, 95, 98, 112, 100, 103, 99
];
const JPEG_CHROMA = [
    17, 18, 24, 47, 99, 99, 99, 99, 18, 21, 26, 66, 99, 99, 99, 99,
    24, 26, 56, 99, 99, 99, 99, 99, 47, 66, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99
];

// Коэффициенты DCT 8×8: DCT_COS[u * 8 + x]
const DCT_COS = (() => {
    const t = new Float64Array(64);
    for (let u = 0; u < 8; u++) {
        for (let x = 0; x < 8; x++) {
            t[u * 8 + x] = (u === 0 ? Math.SQRT1_2 : 1) * 0.5 * Math.cos((2 * x + 1) * u * Math.PI / 16);
        }
    }
    return t;
})();

// Таблица квантования для качества 1..100 (как в libjpeg)
function quantTable(base, quality) {
    const scale = quality < 50 ? 5000 / quality : 200 - quality * 2;
    return base.map(v => Math.min(255, Math.max(1, Math.floor((v * scale + 50) / 100))));
}

// Сжимает плоскость блоками 8×8 на месте; off сдвигает сетку блоков
function jpegPlane(plane, w, h, qt, off) {
    const blk = new Float64Array(64);
    const tmp = new Float64Array(64);
    const wm = w - 1;
    const hm = h - 1;

    for (let by = -off; by < h; by += 8) {
        for (let bx = -off; bx < w; bx += 8) {
            for (let y = 0; y < 8; y++) {
                const row = Math.min(Math.max(by + y, 0), hm) * w;
                for (let x = 0; x < 8; x++) {
                    blk[y * 8 + x] = plane[row + Math.min(Math.max(bx + x, 0), wm)] - 128;
                }
            }

            // Прямое DCT: по строкам, затем по столбцам
            for (let y = 0; y < 8; y++) {
                for (let u = 0; u < 8; u++) {
                    let sum = 0;
                    for (let x = 0; x < 8; x++) sum += blk[y * 8 + x] * DCT_COS[u * 8 + x];
                    tmp[y * 8 + u] = sum;
                }
            }
            for (let u = 0; u < 8; u++) {
                for (let v = 0; v < 8; v++) {
                    let sum = 0;
                    for (let y = 0; y < 8; y++) sum += tmp[y * 8 + u] * DCT_COS[v * 8 + y];
                    const q = qt[v * 8 + u];
                    blk[v * 8 + u] = Math.round(sum / q) * q;  // квантование — здесь теряется качество
                }
            }

            // Обратное DCT
            for (let u = 0; u < 8; u++) {
                for (let y = 0; y < 8; y++) {
                    let sum = 0;
                    for (let v = 0; v < 8; v++) sum += blk[v * 8 + u] * DCT_COS[v * 8 + y];
                    tmp[y * 8 + u] = sum;
                }
            }
            for (let y = 0; y < 8; y++) {
                const py = by + y;
                if (py < 0 || py > hm) continue;
                for (let x = 0; x < 8; x++) {
                    const px = bx + x;
                    if (px < 0 || px > wm) continue;
                    let sum = 0;
                    for (let u = 0; u < 8; u++) sum += tmp[y * 8 + u] * DCT_COS[u * 8 + x];
                    plane[py * w + px] = sum + 128;
                }
            }
        }
    }
}

// Отрезки исходных пикселей (с весами), из которых складывается каждый пиксель при уменьшении
function areaSpans(n, nn) {
    const scale = n / nn;
    const spans = [];
    for (let i = 0; i < nn; i++) {
        const a = i * scale;
        const b = a + scale;
        const idx = [];
        const wgt = [];
        for (let j = Math.floor(a); j < Math.min(n, Math.ceil(b)); j++) {
            idx.push(j);
            wgt.push((Math.min(j + 1, b) - Math.max(j, a)) / scale);
        }
        spans.push({ idx, wgt });
    }
    return spans;
}

// Уменьшение с усреднением по площади, результат — Float32Array RGBA
function resampleArea(d, w, h, nw, nh) {
    const xs = areaSpans(w, nw);
    const ys = areaSpans(h, nh);
    const tmp = new Float32Array(nw * h * 4);
    for (let y = 0; y < h; y++) {
        const srow = y * w * 4;
        const trow = y * nw * 4;
        for (let x = 0; x < nw; x++) {
            const { idx, wgt } = xs[x];
            let r = 0, g = 0, b = 0, a = 0;
            for (let k = 0; k < idx.length; k++) {
                const i = srow + idx[k] * 4;
                const f = wgt[k];
                r += d[i] * f; g += d[i + 1] * f; b += d[i + 2] * f; a += d[i + 3] * f;
            }
            const t = trow + x * 4;
            tmp[t] = r; tmp[t + 1] = g; tmp[t + 2] = b; tmp[t + 3] = a;
        }
    }
    const out = new Float32Array(nw * nh * 4);
    const stride = nw * 4;
    for (let y = 0; y < nh; y++) {
        const { idx, wgt } = ys[y];
        const orow = y * stride;
        for (let k = 0; k < idx.length; k++) {
            const trow = idx[k] * stride;
            const f = wgt[k];
            for (let i = 0; i < stride; i++) out[orow + i] += tmp[trow + i] * f;
        }
    }
    return out;
}

// Билинейное увеличение Float32 RGB (nw×nh) в Uint8 (w×h), альфа берётся из исходника
function upscaleBilinear(small, nw, nh, w, h, alphaSrc) {
    const out = new Uint8ClampedArray(w * h * 4);
    const x0s = new Int32Array(w);
    const x1s = new Int32Array(w);
    const txs = new Float32Array(w);
    for (let x = 0; x < w; x++) {
        const fx = Math.min(Math.max((x + 0.5) * nw / w - 0.5, 0), nw - 1);
        x0s[x] = Math.floor(fx);
        x1s[x] = Math.min(x0s[x] + 1, nw - 1);
        txs[x] = fx - x0s[x];
    }
    for (let y = 0; y < h; y++) {
        const fy = Math.min(Math.max((y + 0.5) * nh / h - 0.5, 0), nh - 1);
        const y0 = Math.floor(fy);
        const ty = fy - y0;
        const r0 = y0 * nw * 4;
        const r1 = Math.min(y0 + 1, nh - 1) * nw * 4;
        for (let x = 0; x < w; x++) {
            const a = r0 + x0s[x] * 4, b = r0 + x1s[x] * 4;
            const c = r1 + x0s[x] * 4, d = r1 + x1s[x] * 4;
            const tx = txs[x];
            const o = (y * w + x) * 4;
            for (let ch = 0; ch < 3; ch++) {
                const top = small[a + ch] + (small[b + ch] - small[a + ch]) * tx;
                const bottom = small[c + ch] + (small[d + ch] - small[c + ch]) * tx;
                out[o + ch] = top + (bottom - top) * ty;
            }
            out[o + 3] = alphaSrc[o + 3];
        }
    }
    return out;
}

function jpegEffect(src, amount, s) {
    const { width: w, height: h, data: d } = src;
    const t = (amount - 1) / 99;

    // Работаем в разрешении, привязанном к сетке ползунков, — поэтому превью совпадает с экспортом
    const shrink = Math.min(1, 1 / (s * (1 + t * 3)));
    const nw = Math.max(1, Math.round(w * shrink));
    const nh = Math.max(1, Math.round(h * shrink));
    const small = resampleArea(d, w, h, nw, nh);

    // RGB -> YCbCr с прореживанием цвета 4:2:0
    const n = nw * nh;
    const cw = Math.ceil(nw / 2);
    const chh = Math.ceil(nh / 2);
    const Y = new Float32Array(n);
    const Cb = new Float32Array(cw * chh);
    const Cr = new Float32Array(cw * chh);
    const cnt = new Float32Array(cw * chh);
    for (let y = 0; y < nh; y++) {
        for (let x = 0; x < nw; x++) {
            const i = y * nw + x;
            const r = small[i * 4], g = small[i * 4 + 1], b = small[i * 4 + 2];
            Y[i] = 0.299 * r + 0.587 * g + 0.114 * b;
            const c = (y >> 1) * cw + (x >> 1);
            Cb[c] += -0.168736 * r - 0.331264 * g + 0.5 * b + 128;
            Cr[c] += 0.5 * r - 0.418688 * g - 0.081312 * b + 128;
            cnt[c]++;
        }
    }
    for (let c = 0; c < cnt.length; c++) {
        Cb[c] /= cnt[c];
        Cr[c] /= cnt[c];
    }

    // Чем сильнее эффект, тем ниже качество и больше повторных пересжатий
    const quality = Math.max(1, Math.round(70 * Math.pow(1 - t, 1.5)));
    const qL = quantTable(JPEG_LUMA, quality);
    const qC = quantTable(JPEG_CHROMA, quality);
    const generations = 1 + Math.round(t * 2);
    for (let g = 0; g < generations; g++) {
        const off = (g * 3) % 8;
        jpegPlane(Y, nw, nh, qL, off);
        jpegPlane(Cb, cw, chh, qC, off);
        jpegPlane(Cr, cw, chh, qC, off);
    }

    for (let y = 0; y < nh; y++) {
        for (let x = 0; x < nw; x++) {
            const i = y * nw + x;
            const c = (y >> 1) * cw + (x >> 1);
            const yy = Y[i], cb = Cb[c] - 128, cr = Cr[c] - 128;
            small[i * 4] = yy + 1.402 * cr;
            small[i * 4 + 1] = yy - 0.344136 * cb - 0.714136 * cr;
            small[i * 4 + 2] = yy + 1.772 * cb;
        }
    }

    return new ImageData(upscaleBilinear(small, nw, nh, w, h, d), w, h);
}

function effectKey(layer) {
    return `${layer.type}:${layer.amount}${layer.type === 'glitch' ? ':' + layer.seed : ''}`;
}

function computeEffect(layer, src, s) {
    switch (layer.type) {
        case 'pixelate': return pixelateEffect(src, layer.amount * s);
        case 'blur': return blurEffect(src, layer.amount * s);
        case 'glitch': return glitchEffect(src, layer.amount, layer.seed, s);
        default: return jpegEffect(src, layer.amount, s);
    }
}

function getPreviewEffect(layer) {
    const key = effectKey(layer);
    let fx = effectCache.get(key);
    if (fx) {
        // LRU: переносим в конец
        effectCache.delete(key);
        effectCache.set(key, fx);
        return fx;
    }
    fx = createCanvas(pw, ph);
    fx.getContext('2d').putImageData(computeEffect(layer, srcData, unit), 0, 0);
    effectCache.set(key, fx);
    pruneEffectCache();
    return fx;
}

// Эффект слоя, лежащего над другими: обрабатывает то, что получилось под ним.
// Пересчитывается, только когда меняется что-то внизу или настройки самого слоя.
// Во время мазка не пересчитываем (дорого) — обновится, когда кисть отпустят.
function getStackedEffect(layer, below) {
    const sig = `${below}>${effectKey(layer)}`;
    const entry = stackedEffects.get(layer.id);
    if (entry && (entry.sig === sig || live)) return entry.canvas;
    const canvas = entry ? entry.canvas : createCanvas(pw, ph);
    const input = ctx.getImageData(0, 0, pw, ph);
    canvas.getContext('2d').putImageData(computeEffect(layer, input, unit), 0, 0);
    stackedEffects.set(layer.id, { sig, canvas });
    return canvas;
}

function bumpMask(layer) {
    maskRevs.set(layer.id, (maskRevs.get(layer.id) || 0) + 1);
}

// Вытесняем давно не нужные эффекты, но не те, что видны сейчас:
// иначе при большом числе слоёв они пересчитывались бы на каждом кадре
function pruneEffectCache() {
    if (effectCache.size <= EFFECT_CACHE_LIMIT) return;
    const visible = new Set(layers.filter(l => !l.hidden && l.strokes.length).map(effectKey));
    for (const key of effectCache.keys()) {
        if (effectCache.size <= EFFECT_CACHE_LIMIT) break;
        if (!visible.has(key)) effectCache.delete(key);
    }
}

// ============ МАСКИ И МАЗКИ ============

function createCanvas(w, h) {
    const c = document.createElement('canvas');
    c.width = w;
    c.height = h;
    return c;
}

function getMask(layer) {
    let mask = masks.get(layer.id);
    if (!mask) {
        mask = createCanvas(pw, ph);
        masks.set(layer.id, mask);
    }
    return mask;
}

function setStrokeComposite(c, stroke) {
    c.globalCompositeOperation = stroke.kind === 'erase' ? 'destination-out' : 'source-over';
}

function softFill(c, r, hardness) {
    if (hardness >= 1) return '#000';
    const g = c.createRadialGradient(0, 0, r * hardness, 0, 0, r);
    g.addColorStop(0, 'rgba(0,0,0,1)');
    g.addColorStop(1, 'rgba(0,0,0,0)');
    return g;
}

function drawDab(c, stroke, x, y) {
    c.save();
    c.translate(x, y);
    c.fillStyle = softFill(c, stroke.r, stroke.hardness);
    c.beginPath();
    c.arc(0, 0, stroke.r, 0, Math.PI * 2);
    c.fill();
    c.restore();
}

function drawEllipse(c, stroke) {
    c.save();
    c.translate(stroke.cx, stroke.cy);
    c.scale(1, stroke.ry / stroke.rx);
    c.fillStyle = softFill(c, stroke.rx, stroke.hardness);
    c.beginPath();
    c.arc(0, 0, stroke.rx, 0, Math.PI * 2);
    c.fill();
    c.restore();
}

// Рисует отрезок мазка; carry — расстояние от последнего отпечатка мягкой кисти
function drawSegment(c, stroke, x0, y0, x1, y1, carry) {
    if (stroke.hardness >= 1) {
        c.lineCap = 'round';
        c.lineWidth = stroke.r * 2;
        c.strokeStyle = '#000';
        c.beginPath();
        c.moveTo(x0, y0);
        c.lineTo(x1, y1);
        c.stroke();
        return 0;
    }

    const spacing = Math.max(0.5, stroke.r * 0.15);
    const dx = x1 - x0;
    const dy = y1 - y0;
    const len = Math.hypot(dx, dy);
    let t = spacing - carry;
    while (t <= len) {
        drawDab(c, stroke, x0 + dx * t / len, y0 + dy * t / len);
        t += spacing;
    }
    return len - (t - spacing);
}

// Полная отрисовка мазка (для пересборки масок и экспорта)
function replayStroke(c, stroke) {
    c.save();
    if (stroke.kind === 'fill') {
        c.globalCompositeOperation = 'source-over';
        c.fillStyle = '#000';
        c.fillRect(0, 0, pw, ph);
    } else if (stroke.kind === 'ellipse') {
        c.globalCompositeOperation = 'source-over';
        drawEllipse(c, stroke);
    } else {
        setStrokeComposite(c, stroke);
        const p = stroke.points;
        drawDab(c, stroke, p[0], p[1]);
        let carry = 0;
        for (let i = 2; i < p.length; i += 2) {
            carry = drawSegment(c, stroke, p[i - 2], p[i - 1], p[i], p[i + 1], carry);
        }
    }
    c.restore();
}

function rebuildMasks() {
    const ids = new Set(layers.map(l => l.id));
    for (const map of [masks, maskRevs, stackedEffects]) {
        for (const id of map.keys()) {
            if (!ids.has(id)) map.delete(id);
        }
    }
    for (const layer of layers) {
        bumpMask(layer);
        const c = getMask(layer).getContext('2d');
        c.clearRect(0, 0, pw, ph);
        layer.strokes.forEach(stroke => replayStroke(c, stroke));
    }
}

// ============ СЛОИ ============

function getActive() {
    return layers.find(l => l.id === activeId) || null;
}

function createLayer(type, extra) {
    const layer = {
        id: ++layerSeq,
        type,
        amount: defaults[type],
        seed: newSeed(),
        hidden: false,
        note: '',
        strokes: [],
        ...extra
    };
    layers.push(layer);
    activeId = layer.id;
    return layer;
}

// Слой, в который рисует кисть: выбранный, иначе новый
function targetLayer() {
    const active = getActive();
    if (active && active.type === currentEffect) {
        active.hidden = false;
        return active;
    }
    return createLayer(currentEffect);
}

function hasWork() {
    return layers.some(l => l.strokes.length);
}

function layerTitle(layer) {
    return `${EFFECTS[layer.type].name} · ${layer.amount}${layer.note ? ' · ' + layer.note : ''}`;
}

function selectLayer(id) {
    activeId = id;
    const layer = getActive();
    if (layer) currentEffect = layer.type;
    syncControls();
}

function renderLayerList() {
    const rows = [];

    if (activeId === null && layers.length) {
        const li = document.createElement('li');
        li.className = 'layer-row active pending';
        li.textContent = `＋ Новый слой: ${EFFECTS[currentEffect].name} — начните рисовать`;
        rows.push(li);
    }

    // Верхний слой — первым, как в графических редакторах
    for (let i = layers.length - 1; i >= 0; i--) {
        const layer = layers[i];
        const li = document.createElement('li');
        li.className = 'layer-row' + (layer.id === activeId ? ' active' : '') + (layer.hidden ? ' is-hidden' : '');
        li.dataset.id = layer.id;

        const handle = document.createElement('button');
        handle.className = 'drag-handle';
        handle.textContent = '⋮⋮';
        handle.title = 'Перетащите, чтобы изменить порядок (или стрелки ↑ ↓)';
        handle.setAttribute('aria-label', `Порядок слоя ${i + 1}: стрелки вверх и вниз`);
        handle.addEventListener('pointerdown', (e) => startLayerDrag(e, li));
        handle.addEventListener('keydown', (e) => {
            if (e.key === 'ArrowUp' || e.key === 'ArrowDown') {
                e.preventDefault();
                moveLayer(layer.id, e.key === 'ArrowUp' ? 1 : -1);
            }
        });

        const name = document.createElement('button');
        name.className = 'layer-name';
        name.textContent = `${i + 1}. ${layerTitle(layer)}`;
        name.setAttribute('aria-pressed', layer.id === activeId);
        name.addEventListener('click', () => selectLayer(layer.id));

        const eye = document.createElement('button');
        eye.className = 'icon-btn';
        eye.textContent = layer.hidden ? '🙈' : '👁';
        eye.title = layer.hidden ? 'Показать слой' : 'Скрыть слой';
        eye.setAttribute('aria-label', eye.title);
        eye.addEventListener('click', () => {
            pushHistory();
            layer.hidden = !layer.hidden;
            changed();
            renderLayerList();
        });

        const del = document.createElement('button');
        del.className = 'icon-btn';
        del.textContent = '✕';
        del.title = 'Удалить слой';
        del.setAttribute('aria-label', del.title);
        del.addEventListener('click', () => {
            pushHistory();
            layers = layers.filter(l => l !== layer);
            if (activeId === layer.id) activeId = null;
            rebuildMasks();
            changed();
            syncControls();
        });

        li.append(handle, name, eye, del);
        rows.push(li);
    }

    if (!rows.length) {
        const li = document.createElement('li');
        li.className = 'layer-empty';
        li.textContent = 'Пока пусто — закрасьте область кистью';
        rows.push(li);
    }

    layerList.replaceChildren(...rows);
    newLayerBtn.disabled = activeId === null;
}

// Новый порядок слоёв: ids снизу вверх
function setLayerOrder(ids) {
    if (ids.join() === layers.map(l => l.id).join()) return false;
    pushHistory();
    layers = ids.map(id => layers.find(l => l.id === id));
    changed();
    return true;
}

// Перемещение слоя клавишами: delta = +1 — выше, -1 — ниже
function moveLayer(id, delta) {
    const ids = layers.map(l => l.id);
    const from = ids.indexOf(id);
    const to = from + delta;
    if (to < 0 || to >= ids.length) return;
    ids.splice(from, 1);
    ids.splice(to, 0, id);
    setLayerOrder(ids);
    renderLayerList();
    const handle = layerList.querySelector(`[data-id="${id}"] .drag-handle`);
    if (handle) handle.focus();
}

// Перетаскивание строки за ручку ⋮⋮. Строка едет за пальцем/мышью, линия показывает,
// куда она встанет; сам порядок меняется только при отпускании.
function startLayerDrag(e, row) {
    if (e.button !== 0 || live || busy) return;
    e.preventDefault();
    const handle = e.currentTarget;
    handle.setPointerCapture(e.pointerId);
    const startY = e.clientY;
    const others = [...layerList.querySelectorAll('.layer-row[data-id]')].filter(r => r !== row);
    let insertAt = -1; // позиция среди остальных строк (сверху вниз)
    row.classList.add('dragging');

    const onMove = (ev) => {
        row.style.transform = `translateY(${ev.clientY - startY}px)`;
        insertAt = others.filter(r => {
            const rect = r.getBoundingClientRect();
            return rect.top + rect.height / 2 < ev.clientY;
        }).length;
        others.forEach((r, k) => {
            r.classList.toggle('drop-before', k === insertAt);
            r.classList.toggle('drop-after', k === others.length - 1 && insertAt === others.length);
        });
    };

    const onEnd = () => {
        handle.removeEventListener('pointermove', onMove);
        handle.removeEventListener('pointerup', onEnd);
        handle.removeEventListener('pointercancel', onEnd);
        if (insertAt >= 0) {
            const order = others.map(r => +r.dataset.id);
            order.splice(insertAt, 0, +row.dataset.id);
            setLayerOrder(order.reverse());
        }
        renderLayerList();
    };

    handle.addEventListener('pointermove', onMove);
    handle.addEventListener('pointerup', onEnd);
    handle.addEventListener('pointercancel', onEnd);
}

// ============ ИСТОРИЯ ============

function snapshot() {
    return {
        activeId,
        layers: layers.map(l => ({ ...l, strokes: l.strokes.slice() }))
    };
}

function pushHistory() {
    sliderInHistory = false;
    undoStack.push(snapshot());
    if (undoStack.length > HISTORY_LIMIT) undoStack.shift();
    redoStack.length = 0;
    updateHistoryButtons();
}

function applySnapshot(snap) {
    layers = snap.layers;
    activeId = snap.activeId;
    const active = getActive();
    if (active) currentEffect = active.type;
    rebuildMasks();
    changed();
    syncControls();
}

function restore(from, to) {
    if (live || busy || !from.length) return;
    to.push(snapshot());
    applySnapshot(from.pop());
    updateHistoryButtons();
}

const undo = () => restore(undoStack, redoStack);
const redo = () => restore(redoStack, undoStack);

function updateHistoryButtons() {
    undoBtn.disabled = !undoStack.length;
    redoBtn.disabled = !redoStack.length;
}

// ============ РЕНДЕРИНГ ============

let renderQueued = false;

function requestRender() {
    if (renderQueued) return;
    renderQueued = true;
    requestAnimationFrame(render);
}

function changed() {
    docVersion++;
    requestRender();
}

function render() {
    renderQueued = false;
    if (!srcCanvas) return;

    ctx.globalCompositeOperation = 'source-over';
    ctx.clearRect(0, 0, pw, ph);
    ctx.drawImage(srcCanvas, 0, 0);
    if (comparing) return;

    // Слои накладываются снизу вверх: эффект каждого обрабатывает результат слоёв под ним
    // и виден только внутри своей маски. Нижний видимый слой работает с оригиналом.
    let below = '';
    for (const layer of layers) {
        if (layer.hidden || !layer.strokes.length) continue;
        const fx = below ? getStackedEffect(layer, below) : getPreviewEffect(layer);
        below += `|${layer.id}:${effectKey(layer)}#${maskRevs.get(layer.id) || 0}`;
        tmpCtx.globalCompositeOperation = 'source-over';
        tmpCtx.clearRect(0, 0, pw, ph);
        tmpCtx.drawImage(fx, 0, 0);
        tmpCtx.globalCompositeOperation = 'destination-in';
        tmpCtx.drawImage(getMask(layer), 0, 0);
        ctx.drawImage(tmpCanvas, 0, 0);
    }
}

// ============ ЗАГРУЗКА ============

function isProcessing() {
    if (!busy && !detecting) return false;
    toast('Дождитесь окончания обработки');
    return true;
}

function loadFile(file) {
    if (!file || isProcessing()) return;
    if (file.type && !file.type.startsWith('image/')) {
        toast('Это не изображение', true);
        return;
    }
    if (hasWork() && !confirm('Открыть новое изображение? Текущие изменения будут потеряны.')) {
        return;
    }

    const url = URL.createObjectURL(file);
    const img = new Image();
    img.onload = () => {
        if (!img.naturalWidth || !img.naturalHeight) {
            img.onerror();
            return;
        }
        if (imageUrl) URL.revokeObjectURL(imageUrl);
        imageUrl = url;
        fileBaseName = (file.name || 'image').replace(/\.[^.]+$/, '').replace(/[\\/:*?"<>|]+/g, '_') || 'image';
        formatSelect.value = /jpe?g|heic|heif/i.test(file.type) ? 'image/jpeg' : 'image/png';
        setImage(img);
    };
    img.onerror = () => {
        URL.revokeObjectURL(url);
        toast('Не удалось открыть изображение. Попробуйте JPG, PNG или WebP.', true);
    };
    img.src = url;
}

function clearDocument() {
    layers = [];
    activeId = null;
    masks.clear();
    maskRevs.clear();
    stackedEffects.clear();
    effectCache.clear();
    undoStack.length = 0;
    redoStack.length = 0;
    exportCache = null;
    updateHistoryButtons();
}

function setImage(img) {
    image = img;
    const w = img.naturalWidth;
    const h = img.naturalHeight;
    const scale = Math.min(1, PREVIEW_MAX_SIDE / Math.max(w, h));
    pw = Math.max(1, Math.round(w * scale));
    ph = Math.max(1, Math.round(h * scale));
    unit = Math.max(pw, ph) / REF_SIDE;

    canvas.width = tmpCanvas.width = pw;
    canvas.height = tmpCanvas.height = ph;
    canvasWrap.style.setProperty('--ar', pw / ph);

    srcCanvas = createCanvas(pw, ph);
    const srcCtx = srcCanvas.getContext('2d');
    srcCtx.imageSmoothingQuality = 'high';
    srcCtx.drawImage(img, 0, 0, pw, ph);
    srcData = srcCtx.getImageData(0, 0, pw, ph);

    clearDocument();

    dropZone.classList.add('hidden');
    canvasWrap.classList.remove('hidden');
    rightPanel.classList.remove('hidden');
    mainContainer.classList.add('two-panels');
    setView(1, 0, 0);
    syncControls();
    changed();
}

function resetApp() {
    if (isProcessing()) return;
    if (hasWork() && !confirm('Начать заново? Текущие изменения будут потеряны.')) return;

    if (imageUrl) URL.revokeObjectURL(imageUrl);
    image = imageUrl = srcCanvas = srcData = null;
    clearDocument();
    fileInput.value = '';

    dropZone.classList.remove('hidden');
    canvasWrap.classList.add('hidden');
    rightPanel.classList.add('hidden');
    mainContainer.classList.remove('two-panels');
}

dropZone.addEventListener('click', () => fileInput.click());
dropZone.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        fileInput.click();
    }
});

fileInput.addEventListener('change', () => {
    loadFile(fileInput.files[0]);
    fileInput.value = ''; // чтобы можно было снова выбрать тот же файл
});

// Перетаскивание файла в любое место страницы
document.addEventListener('dragover', (e) => {
    if (!e.dataTransfer || !Array.from(e.dataTransfer.types).includes('Files')) return;
    e.preventDefault();
    document.body.classList.add('dragging');
});
document.addEventListener('dragleave', (e) => {
    if (!e.relatedTarget) document.body.classList.remove('dragging');
});
document.addEventListener('drop', (e) => {
    document.body.classList.remove('dragging');
    if (!e.dataTransfer) return;
    // Иначе браузер откроет перетащенную ссылку вместо приложения и работа пропадёт
    e.preventDefault();
    const file = e.dataTransfer.files[0];
    if (file) loadFile(file);
    else toast('Перетащите файл изображения с компьютера', true);
});

// Вставка из буфера обмена (скриншоты)
document.addEventListener('paste', (e) => {
    const files = e.clipboardData ? Array.from(e.clipboardData.files) : [];
    const file = files.find(f => f.type.startsWith('image/'));
    if (file) {
        e.preventDefault();
        loadFile(file);
    }
});

// ============ МАСШТАБ ============

function setView(z, x, y) {
    z = clamp(z, 1, ZOOM_MAX);
    const w = canvas.offsetWidth;
    const h = canvas.offsetHeight;
    view.z = z;
    view.x = z === 1 ? 0 : clamp(x, w - w * z, 0);
    view.y = z === 1 ? 0 : clamp(y, h - h * z, 0);
    canvas.style.transform = z === 1 ? '' : `translate(${view.x}px, ${view.y}px) scale(${z})`;
    viewport.classList.toggle('zoomed', z > 1);
    zoomFitBtn.textContent = `${Math.round(z * 100)}%`;
    zoomOutBtn.disabled = z <= 1;
    zoomInBtn.disabled = z >= ZOOM_MAX;
    refreshBrushCursor();
}

// Масштабирование вокруг точки экрана (она остаётся на месте)
function zoomAt(clientX, clientY, z) {
    const rect = viewport.getBoundingClientRect();
    const px = clientX - rect.left;
    const py = clientY - rect.top;
    const cx = (px - view.x) / view.z;
    const cy = (py - view.y) / view.z;
    z = clamp(z, 1, ZOOM_MAX);
    setView(z, px - cx * z, py - cy * z);
}

function zoomCenter(factor) {
    const rect = viewport.getBoundingClientRect();
    zoomAt(rect.left + rect.width / 2, rect.top + rect.height / 2, view.z * factor);
}

zoomInBtn.addEventListener('click', () => zoomCenter(1.5));
zoomOutBtn.addEventListener('click', () => zoomCenter(1 / 1.5));
zoomFitBtn.addEventListener('click', () => setView(1, 0, 0));
window.addEventListener('resize', () => setView(view.z, view.x, view.y));

viewport.addEventListener('wheel', (e) => {
    if (!image) return;
    const k = e.deltaMode === 1 ? 16 : 1;
    if (e.ctrlKey || e.metaKey) {
        // Ctrl + колесо или щипок на тачпаде
        e.preventDefault();
        const delta = clamp(e.deltaY * k, -50, 50);
        zoomAt(e.clientX, e.clientY, view.z * Math.exp(-delta * 0.01));
    } else if (view.z > 1) {
        e.preventDefault();
        setView(view.z, view.x - e.deltaX * k, view.y - e.deltaY * k);
    }
}, { passive: false });

viewport.addEventListener('pointerenter', () => { pointerOverCanvas = true; });
viewport.addEventListener('pointerleave', () => {
    pointerOverCanvas = false;
    brushCursor.classList.remove('visible');
});

// ============ РИСОВАНИЕ ============

function canvasPoint(e) {
    const rect = canvas.getBoundingClientRect();
    const z = view.z;
    return {
        x: (e.clientX - rect.left - canvas.clientLeft * z) * pw / (canvas.clientWidth * z),
        y: (e.clientY - rect.top - canvas.clientTop * z) * ph / (canvas.clientHeight * z)
    };
}

function brushRadius() {
    return +brushSizeSlider.value * unit;
}

function beginStroke(e) {
    const { x, y } = canvasPoint(e);
    const stroke = {
        kind: tool === 'eraser' ? 'erase' : 'paint',
        r: brushRadius(),
        hardness: 1 - softnessSlider.value / 100,
        points: [x, y]
    };

    const savedRedo = redoStack.slice();
    let targets;
    if (stroke.kind === 'erase') {
        if (eraseActiveOnly.checked) {
            const active = getActive();
            targets = active && !active.hidden ? [active] : [];
            if (!targets.length) {
                toast('Выберите в списке слой, который нужно стереть');
                return;
            }
        } else {
            // Ластик стирает со всех видимых слоёв одновременно
            targets = layers.filter(l => !l.hidden && l.strokes.length);
            if (!targets.length) return;
        }
        pushHistory();
    } else {
        pushHistory();
        targets = [targetLayer()];
        syncControls();
    }

    targets.forEach(l => {
        l.strokes.push(stroke);
        bumpMask(l);
    });
    const ctxs = targets.map(l => getMask(l).getContext('2d'));
    ctxs.forEach(c => {
        c.save();
        setStrokeComposite(c, stroke);
        drawDab(c, stroke, x, y);
        c.restore();
    });

    live = { stroke, targets, ctxs, carry: 0, pointerId: e.pointerId, started: performance.now(), savedRedo };
    changed();
}

function extendStroke(x, y) {
    const p = live.stroke.points;
    const px = p[p.length - 2];
    const py = p[p.length - 1];
    if (px === x && py === y) return;
    p.push(x, y);

    let carry = live.carry;
    live.ctxs.forEach(c => {
        c.save();
        setStrokeComposite(c, live.stroke);
        carry = drawSegment(c, live.stroke, px, py, x, y, live.carry);
        c.restore();
    });
    live.carry = carry;
    live.targets.forEach(bumpMask);
}

// Отмена только что начатого мазка (второй палец = жест, а не рисование)
function cancelStroke() {
    const savedRedo = live.savedRedo;
    live = null;
    applySnapshot(undoStack.pop());
    redoStack.splice(0, redoStack.length, ...savedRedo);
    updateHistoryButtons();
}

function startPinch() {
    const [a, b] = [...touches.values()];
    gesture = {
        type: 'pinch',
        d0: Math.hypot(a.x - b.x, a.y - b.y) || 1,
        mx: (a.x + b.x) / 2,
        my: (a.y + b.y) / 2,
        view0: { ...view }
    };
}

function updatePinch() {
    const [a, b] = [...touches.values()];
    const { view0 } = gesture;
    const rect = viewport.getBoundingClientRect();
    const z = clamp(view0.z * Math.hypot(a.x - b.x, a.y - b.y) / gesture.d0, 1, ZOOM_MAX);
    // Точка изображения под начальной серединой пальцев следует за текущей серединой
    const cx = (gesture.mx - rect.left - view0.x) / view0.z;
    const cy = (gesture.my - rect.top - view0.y) / view0.z;
    const mx = (a.x + b.x) / 2 - rect.left;
    const my = (a.y + b.y) / 2 - rect.top;
    setView(z, mx - cx * z, my - cy * z);
}

canvas.addEventListener('pointerdown', (e) => {
    if (!image || busy) return;
    e.preventDefault();
    canvas.setPointerCapture(e.pointerId);

    if (e.pointerType === 'touch') {
        touches.set(e.pointerId, { x: e.clientX, y: e.clientY });
        if (touches.size === 2) {
            // Два пальца — масштаб и перемещение. Только что начатый мазок отменяем.
            if (live && performance.now() - live.started < 350) cancelStroke();
            if (!live) startPinch();
            return;
        }
        if (touches.size > 2) return;
    }
    if (live || gesture) return;

    if (e.button === 1 || (e.button === 0 && spaceDown)) {
        gesture = { type: 'pan', pointerId: e.pointerId, sx: e.clientX, sy: e.clientY, x0: view.x, y0: view.y };
        viewport.classList.add('panning');
        return;
    }
    if (e.button !== 0) return;
    beginStroke(e);
});

canvas.addEventListener('pointermove', (e) => {
    if (touches.has(e.pointerId)) touches.set(e.pointerId, { x: e.clientX, y: e.clientY });

    if (gesture) {
        if (gesture.type === 'pinch' && touches.size >= 2) updatePinch();
        if (gesture.type === 'pan' && e.pointerId === gesture.pointerId) {
            setView(view.z, gesture.x0 + e.clientX - gesture.sx, gesture.y0 + e.clientY - gesture.sy);
        }
        return;
    }

    updateBrushCursor(e);
    if (!live || e.pointerId !== live.pointerId) return;
    // Промежуточные события дают более плавную линию при быстром движении
    const events = (e.getCoalescedEvents && e.getCoalescedEvents()) || [];
    (events.length ? events : [e]).forEach(ev => {
        const { x, y } = canvasPoint(ev);
        extendStroke(x, y);
    });
    changed();
});

function pointerEnd(e) {
    touches.delete(e.pointerId);
    if (gesture) {
        if ((gesture.type === 'pinch' && touches.size < 2) ||
            (gesture.type === 'pan' && e.pointerId === gesture.pointerId)) {
            gesture = null;
            viewport.classList.remove('panning');
        }
    }
    if (live && e.pointerId === live.pointerId) {
        live = null;
        requestRender(); // пересчитать слои, лежащие над изменённым
    }
}

canvas.addEventListener('pointerup', pointerEnd);
canvas.addEventListener('pointercancel', pointerEnd);
canvas.addEventListener('lostpointercapture', pointerEnd);
canvas.addEventListener('contextmenu', (e) => e.preventDefault());

// Круг-превью кисти под курсором
function updateBrushCursor(e) {
    lastPointer = { clientX: e.clientX, clientY: e.clientY, pointerType: e.pointerType };
    if (e.pointerType === 'touch' || spaceDown) {
        brushCursor.classList.remove('visible');
        return;
    }
    const rect = viewport.getBoundingClientRect();
    const size = brushRadius() * 2 * canvas.clientWidth * view.z / pw;
    brushCursor.style.width = brushCursor.style.height = `${size}px`;
    brushCursor.style.transform =
        `translate(${e.clientX - rect.left - size / 2}px, ${e.clientY - rect.top - size / 2}px)`;
    brushCursor.classList.add('visible');
}

// ============ УПРАВЛЕНИЕ ============

// Приводит кнопки и ползунок в соответствие с текущим эффектом и выбранным слоем
function syncControls() {
    effectButtons.forEach(btn => {
        const active = btn.dataset.effect === currentEffect;
        btn.classList.toggle('active', active);
        btn.setAttribute('aria-pressed', active);
    });

    const info = EFFECTS[currentEffect];
    const active = getActive();
    amountSlider.min = info.min;
    amountSlider.max = info.max;
    amountSlider.value = active ? active.amount : defaults[currentEffect];
    amountLabel.textContent = info.label;
    amountValue.textContent = amountSlider.value;
    reseedBtn.classList.toggle('hidden', currentEffect !== 'glitch');
    reseedBtn.disabled = !(active && active.type === 'glitch');

    renderLayerList();
}

function setEffect(effect) {
    currentEffect = effect;
    const active = getActive();
    if (active && active.type !== effect) activeId = null;
    syncControls();
}

function setTool(value) {
    tool = value;
    brushBtn.classList.toggle('active', tool === 'brush');
    eraserBtn.classList.toggle('active', tool === 'eraser');
    brushBtn.setAttribute('aria-pressed', tool === 'brush');
    eraserBtn.setAttribute('aria-pressed', tool === 'eraser');
}

function setBrushSize(value) {
    brushSizeSlider.value = value;
    $('brushSizeValue').textContent = brushSizeSlider.value;
    refreshBrushCursor();
}

function refreshBrushCursor() {
    if (lastPointer && pointerOverCanvas) updateBrushCursor(lastPointer);
}

function startNewLayer() {
    activeId = null;
    syncControls();
}

effectButtons.forEach(btn => btn.addEventListener('click', () => setEffect(btn.dataset.effect)));
brushBtn.addEventListener('click', () => setTool('brush'));
eraserBtn.addEventListener('click', () => setTool('eraser'));
newLayerBtn.addEventListener('click', startNewLayer);

// Ползунок меняет выбранный слой; одно перетаскивание = один шаг истории
amountSlider.addEventListener('input', () => {
    const value = +amountSlider.value;
    amountValue.textContent = value;
    defaults[currentEffect] = value;
    const layer = getActive();
    if (!layer) return;
    if (!sliderInHistory) {
        pushHistory();
        sliderInHistory = true;
    }
    layer.amount = value;
    renderLayerList();
    changed();
});
// 'change' не приходит, если ползунок вернули в исходное значение, поэтому
// новое перетаскивание начинаем и по нажатию
['change', 'pointerdown', 'keydown'].forEach(type => {
    amountSlider.addEventListener(type, () => { sliderInHistory = false; });
});

reseedBtn.addEventListener('click', () => {
    const layer = getActive();
    if (!layer || layer.type !== 'glitch') return;
    pushHistory();
    layer.seed = newSeed();
    changed();
});

brushSizeSlider.addEventListener('input', () => setBrushSize(brushSizeSlider.value));
softnessSlider.addEventListener('input', () => {
    $('softnessValue').textContent = softnessSlider.value;
});

undoBtn.addEventListener('click', undo);
redoBtn.addEventListener('click', redo);

clearMaskBtn.addEventListener('click', () => {
    if (!layers.length) return;
    pushHistory();
    layers = [];
    activeId = null;
    rebuildMasks();
    changed();
    syncControls();
});

applyFullBtn.addEventListener('click', () => {
    pushHistory();
    const layer = targetLayer();
    const stroke = { kind: 'fill' };
    layer.strokes.push(stroke);
    bumpMask(layer);
    replayStroke(getMask(layer).getContext('2d'), stroke);
    changed();
    syncControls();
});

// Сравнение с оригиналом: пока кнопка зажата
function setComparing(value) {
    if (comparing === value) return;
    comparing = value;
    compareBtn.classList.toggle('active', value);
    requestRender();
}

compareBtn.addEventListener('pointerdown', (e) => {
    e.preventDefault();
    compareBtn.setPointerCapture(e.pointerId);
    setComparing(true);
});
['pointerup', 'pointercancel', 'lostpointercapture'].forEach(type => {
    compareBtn.addEventListener(type, () => setComparing(false));
});
compareBtn.addEventListener('contextmenu', (e) => e.preventDefault());

resetBtn.addEventListener('click', resetApp);

// ============ ПОИСК ЛИЦ ============

let faceApiPromise = null;
let faceApiAttempt = 0;

// Библиотека (~0.5 МБ) загружается только при первом использовании.
// При обрыве связи пробуем ещё раз. Неудачный import() браузер запоминает
// для адреса до перезагрузки страницы, поэтому повтор идёт по новому адресу.
function loadFaceApi() {
    if (!faceApiPromise) {
        faceApiPromise = (async () => {
            let lastError;
            for (let i = 0; i < 3; i++) {
                if (i) await new Promise(resolve => setTimeout(resolve, 1000 * i));
                const attempt = faceApiAttempt++;
                try {
                    const api = await import(attempt ? `${FACE_API_URL}?retry=${attempt}` : FACE_API_URL);
                    await api.nets.tinyFaceDetector.loadFromUri(FACE_MODEL_URL);
                    return api;
                } catch (err) {
                    lastError = err;
                }
            }
            throw lastError;
        })();
        faceApiPromise.catch(() => { faceApiPromise = null; });
    }
    return faceApiPromise;
}

function boxIoU(a, b) {
    const x0 = Math.max(a.x, b.x);
    const y0 = Math.max(a.y, b.y);
    const x1 = Math.min(a.x + a.w, b.x + b.w);
    const y1 = Math.min(a.y + a.h, b.y + b.h);
    const inter = Math.max(0, x1 - x0) * Math.max(0, y1 - y0);
    // Делим на меньшую площадь: лицо, найденное целиком и во фрагменте, считается одним
    return inter / Math.min(a.w * a.h, b.w * b.h);
}

async function detectFaces(api) {
    // Лёгкая модель нестабильна: лицо, уверенно найденное при одном размере входа,
    // может потеряться при другом. Поэтому прогоняем несколько масштабов и голосуем.
    const candidates = [];
    let source = 0;
    // fine — прогон с высоким разрешением: рамки точнее, чем на грубых масштабах
    const detect = async (input, ox, oy, inputSize, fine) => {
        const options = new api.TinyFaceDetectorOptions({ inputSize, scoreThreshold: 0.25 });
        const result = await api.detectAllFaces(input, options);
        source++;
        result.forEach(d => candidates.push({
            x: ox + d.box.x,
            y: oy + d.box.y,
            w: d.box.width,
            h: d.box.height,
            score: d.score,
            source,
            fine
        }));
    };

    for (const size of [320, 416, 512, 608]) {
        await detect(srcCanvas, 0, 0, size, size >= 512);
    }

    // Мелкие лица (групповые фото): дополнительно ищем во фрагментах 2×2 с перекрытием
    const tw = Math.round(pw * 0.6);
    const th = Math.round(ph * 0.6);
    const tile = createCanvas(tw, th);
    const tileCtx = tile.getContext('2d');
    for (const fy of [0, 1]) {
        for (const fx of [0, 1]) {
            const ox = fx * (pw - tw);
            const oy = fy * (ph - th);
            tileCtx.clearRect(0, 0, tw, th);
            tileCtx.drawImage(srcCanvas, ox, oy, tw, th, 0, 0, tw, th);
            await detect(tile, ox, oy, 416, true);
        }
    }

    // Группируем совпадающие находки, начиная с самых уверенных
    candidates.sort((a, b) => b.score - a.score);
    const clusters = [];
    for (const box of candidates) {
        const cluster = clusters.find(c => boxIoU(c.best, box) > 0.5);
        if (cluster) {
            cluster.sources.add(box.source);
            if (box.fine && !cluster.fine) cluster.fine = box;
        } else {
            clusters.push({ best: box, fine: box.fine ? box : null, sources: new Set([box.source]) });
        }
    }

    // Лицо принимаем, если оно уверенное хотя бы раз или стабильно повторяется
    const accepted = clusters.filter(c =>
        c.best.score >= 0.5 || (c.best.score >= 0.3 && c.sources.size >= 2));

    // Сначала находки с точных масштабов, потом остальные. Грубые масштабы иногда дают
    // рамку «между» соседними лицами — такую, задевающую уже принятые лица, отбрасываем.
    accepted.sort((a, b) => (!!b.fine - !!a.fine) || (b.best.score - a.best.score));
    const faces = [];
    for (const c of accepted) {
        const box = c.fine || c.best;
        const overlaps = faces.map(f => boxIoU(f, box));
        if (overlaps.some(o => o > 0.2) || overlaps.filter(o => o > 0.02).length >= 2) continue;
        faces.push(box);
    }
    return faces;
}

facesBtn.addEventListener('click', async () => {
    if (!image || detecting || busy) return;
    detecting = true;
    const label = facesBtn.textContent;
    facesBtn.disabled = true;
    facesBtn.textContent = faceApiPromise ? 'Поиск лиц…' : 'Загрузка модели…';
    try {
        const api = await loadFaceApi();
        facesBtn.textContent = 'Поиск лиц…';
        await nextFrame();
        const faces = await detectFaces(api);
        if (!faces.length) {
            toast('Лица не найдены — закрасьте нужные области кистью');
            return;
        }

        pushHistory();
        const layer = createLayer(currentEffect, { note: `лица: ${faces.length}` });
        const hardness = 1 - softnessSlider.value / 100;
        faces.forEach(f => {
            // Эллипс с запасом: рамка детектора не захватывает лоб, волосы и подбородок
            layer.strokes.push({
                kind: 'ellipse',
                cx: f.x + f.w / 2,
                cy: f.y + f.h * 0.45,
                rx: f.w * 0.7,
                ry: f.h * 0.85,
                hardness
            });
        });
        rebuildMasks();
        changed();
        syncControls();
        toast(`Найдено лиц: ${faces.length}. Проверьте результат — пропущенные закрасьте кистью`);
    } catch (err) {
        console.error(err);
        toast('Не удалось загрузить модель поиска лиц. Проверьте подключение к интернету.', true);
    } finally {
        detecting = false;
        facesBtn.disabled = false;
        facesBtn.textContent = label;
    }
});

// ============ ГОРЯЧИЕ КЛАВИШИ ============
// По коду клавиши, чтобы работало в русской раскладке

document.addEventListener('keydown', (e) => {
    if (!image || (e.target.matches && e.target.matches('input[type="text"], textarea, select'))) return;
    const mod = e.metaKey || e.ctrlKey;

    if (mod && e.code === 'KeyZ') {
        e.preventDefault();
        e.shiftKey ? redo() : undo();
        return;
    }
    if (mod && e.code === 'KeyY') {
        e.preventDefault();
        redo();
        return;
    }
    if (mod || e.altKey) return;

    // Пробел + перетаскивание — перемещение увеличенного холста
    if (e.code === 'Space' && pointerOverCanvas) {
        e.preventDefault();
        spaceDown = true;
        viewport.classList.add('grab');
        brushCursor.classList.remove('visible');
        return;
    }

    switch (e.code) {
        case 'KeyB': setTool('brush'); break;
        case 'KeyE': setTool('eraser'); break;
        case 'KeyN': startNewLayer(); break;
        case 'BracketLeft': setBrushSize(+brushSizeSlider.value - 5); break;
        case 'BracketRight': setBrushSize(+brushSizeSlider.value + 5); break;
        case 'Digit1': case 'Digit2': case 'Digit3': case 'Digit4':
            setEffect(EFFECT_ORDER[+e.code.slice(5) - 1]);
            break;
        case 'Equal': case 'NumpadAdd': zoomCenter(1.5); break;
        case 'Minus': case 'NumpadSubtract': zoomCenter(1 / 1.5); break;
        case 'Digit0': case 'Numpad0': setView(1, 0, 0); break;
        case 'KeyC': setComparing(true); break;
        default: return;
    }
    e.preventDefault();
});

document.addEventListener('keyup', (e) => {
    if (e.code === 'KeyC') setComparing(false);
    if (e.code === 'Space' && spaceDown) {
        e.preventDefault();
        spaceDown = false;
        viewport.classList.remove('grab');
    }
});
window.addEventListener('blur', () => {
    setComparing(false);
    spaceDown = false;
    viewport.classList.remove('grab');
});

// ============ ЭКСПОРТ ============

// Даёт браузеру отрисовать «Обработка…». В фоновой вкладке requestAnimationFrame
// не срабатывает, поэтому продолжаем и по таймеру
const nextFrame = () => new Promise(resolve => {
    const timer = setTimeout(resolve, 50);
    requestAnimationFrame(() => {
        clearTimeout(timer);
        setTimeout(resolve, 0);
    });
});

function exportSize() {
    let w = image.naturalWidth;
    let h = image.naturalHeight;
    if (w * h > EXPORT_MAX_PIXELS) {
        const f = Math.sqrt(EXPORT_MAX_PIXELS / (w * h));
        w = Math.floor(w * f);
        h = Math.floor(h * f);
    }
    return { w, h };
}

async function renderFullSize(type) {
    const { w, h } = exportSize();
    const sx = w / pw;
    const sy = h / ph;

    const out = createCanvas(w, h);
    const outCtx = out.getContext('2d');
    outCtx.imageSmoothingQuality = 'high';
    outCtx.drawImage(image, 0, 0, w, h);

    // Снимок слоёв: пока идёт сохранение, их можно менять, файл от этого не пострадает
    const used = snapshot().layers.filter(l => !l.hidden && l.strokes.length);
    if (used.length) {
        const fx = createCanvas(w, h);
        const fxCtx = fx.getContext('2d');
        const mask = createCanvas(w, h);
        const maskCtx = mask.getContext('2d');

        for (const layer of used) {
            await nextFrame();
            // Как и в превью, эффект обрабатывает результат всех слоёв под ним
            const data = computeEffect(layer, outCtx.getImageData(0, 0, w, h), unit * sx);

            maskCtx.setTransform(1, 0, 0, 1, 0, 0);
            maskCtx.clearRect(0, 0, w, h);
            maskCtx.setTransform(sx, 0, 0, sy, 0, 0);
            layer.strokes.forEach(stroke => replayStroke(maskCtx, stroke));

            fxCtx.globalCompositeOperation = 'source-over';
            fxCtx.putImageData(data, 0, 0);
            fxCtx.globalCompositeOperation = 'destination-in';
            fxCtx.drawImage(mask, 0, 0);
            outCtx.drawImage(fx, 0, 0);
        }
        // Освобождаем память (важно для мобильных)
        fx.width = fx.height = mask.width = mask.height = 0;
    }

    if (type === 'image/jpeg') {
        // JPEG без прозрачности: подкладываем белый фон
        outCtx.globalCompositeOperation = 'destination-over';
        outCtx.fillStyle = '#fff';
        outCtx.fillRect(0, 0, w, h);
    }

    const blob = await new Promise(resolve => out.toBlob(resolve, type, 0.92));
    out.width = out.height = 0;
    if (!blob) throw new Error('toBlob failed');
    return blob;
}

async function getExportBlob(type) {
    if (exportCache && exportCache.version === docVersion && exportCache.type === type) {
        return exportCache.blob;
    }
    const version = docVersion;
    const blob = await renderFullSize(type);
    exportCache = { version, type, blob };
    const { w, h } = exportSize();
    if (w !== image.naturalWidth) {
        toast(`Изображение уменьшено до ${w}×${h} — ограничение браузера`);
    }
    return blob;
}

function exportFileName(type) {
    return `${fileBaseName}-jackalized.${type === 'image/jpeg' ? 'jpg' : 'png'}`;
}

const exportButtons = [downloadBtn, shareBtn, copyBtn, resetBtn];

async function runBusy(btn, task) {
    if (busy || !image) return;
    busy = true;
    const label = btn.textContent;
    btn.textContent = 'Обработка…';
    exportButtons.forEach(b => { b.disabled = true; });
    try {
        await task();
    } catch (err) {
        if (err && err.name !== 'AbortError') {
            console.error(err);
            toast('Не удалось сохранить изображение', true);
        }
    } finally {
        busy = false;
        btn.textContent = label;
        exportButtons.forEach(b => { b.disabled = false; });
    }
}

downloadBtn.addEventListener('click', () => runBusy(downloadBtn, async () => {
    const type = formatSelect.value;
    const blob = await getExportBlob(type);
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.download = exportFileName(type);
    link.href = url;
    document.body.appendChild(link);
    link.click();
    link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 30000);
}));

// «Поделиться» — на телефонах позволяет сохранить сразу в галерею
const canShareFiles = (() => {
    try {
        return !!navigator.canShare &&
            navigator.canShare({ files: [new File([''], 'test.png', { type: 'image/png' })] }) &&
            matchMedia('(pointer: coarse)').matches;
    } catch (e) {
        return false;
    }
})();

if (canShareFiles) shareBtn.classList.remove('hidden');

shareBtn.addEventListener('click', () => runBusy(shareBtn, async () => {
    const type = formatSelect.value;
    const blob = await getExportBlob(type);
    const file = new File([blob], exportFileName(type), { type });
    try {
        await navigator.share({ files: [file] });
    } catch (err) {
        // Пока шла обработка, браузер мог «забыть» нажатие — повторное будет мгновенным
        if (err.name === 'NotAllowedError') {
            toast('Изображение готово — нажмите «Поделиться» ещё раз');
            return;
        }
        throw err;
    }
}));

const canCopy = !!(navigator.clipboard && navigator.clipboard.write && window.ClipboardItem);

if (canCopy) copyBtn.classList.remove('hidden');

copyBtn.addEventListener('click', () => runBusy(copyBtn, async () => {
    // Promise внутри ClipboardItem сохраняет разрешение Safari на запись
    await navigator.clipboard.write([new ClipboardItem({ 'image/png': getExportBlob('image/png') })]);
    toast('Скопировано в буфер обмена');
}));

// ============ УВЕДОМЛЕНИЯ ============

let toastTimer = null;

function toast(message, isError) {
    toastEl.textContent = message;
    toastEl.classList.toggle('error', !!isError);
    toastEl.classList.add('visible');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => toastEl.classList.remove('visible'), 4000);
}

// ============ ПРИЛОЖЕНИЕ (PWA) ============

if ('serviceWorker' in navigator && (location.protocol === 'https:' || location.hostname === 'localhost')) {
    navigator.serviceWorker.register('/sw.js').catch(err => console.warn('SW:', err));
}

// Открытие файлов через установленное приложение («Открыть с помощью» на компьютере)
if ('launchQueue' in window) {
    window.launchQueue.setConsumer(async (params) => {
        if (params.files && params.files.length) loadFile(await params.files[0].getFile());
    });
}

// Картинка, присланная через «Поделиться» на телефоне (сохраняется в sw.js)
if (new URLSearchParams(location.search).has('shared') && 'caches' in window) {
    history.replaceState(null, '', '/');
    caches.open('jackalizer-share').then(async (cache) => {
        const response = await cache.match('/shared-image');
        if (!response) return;
        await cache.delete('/shared-image');
        const blob = await response.blob();
        const name = decodeURIComponent(response.headers.get('x-file-name') || 'image');
        loadFile(new File([blob], name, { type: blob.type }));
    });
}

// ============ ИНИЦИАЛИЗАЦИЯ ============

setTool('brush');
syncControls();
updateHistoryButtons();
