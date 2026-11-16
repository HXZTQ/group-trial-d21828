/* Lock shell: download the sealed package, ask for the passphrase (or use the key this device remembered),
   decrypt in memory, then hand the page over to the original site unchanged. After unlock the only network request allowed is POST to the relay /turn (lock/relay.json). */
(function () {
  'use strict';
  /* Shared by the browser shell (inlined into l/app.*.js at build) and by Node (lock/lib/common.mjs loads this file in a vm).
   Plain ES5-ish script, no imports. Everything here is pure: no DOM, no network. */
var CRL = (function () {
  'use strict';

  var MAGIC = [0x43, 0x52, 0x4c, 0x31];   // "CRL1"
  var HEADER_LEN = 64;
  var TAG_LEN = 16;
  var MANIFEST_PLAIN_LEN = 131072;        // manifest JSON is space-padded to exactly this many bytes (hides file count)
  var LEGACY_MANIFEST_PLAIN_LEN = 65536;  // packages built before 2026-11-16 (455 files no longer fit); still readable, never written
  var BLOCK = 262144;                      // the whole .bin is a multiple of 256 KiB
  var INFO = 'chat-room-lock v1 aes-256-gcm';

  // Header limits. Anything outside is refused before any KDF work starts.
  var LIMITS = {
    mMin: 8192, mMax: 262144,              // KiB
    tMin: 1, tMax: 10,
    pMin: 1, pMax: 4,
    metaLen: MANIFEST_PLAIN_LEN + TAG_LEN, // exact (written)
    legacyMetaLen: LEGACY_MANIFEST_PLAIN_LEN + TAG_LEN, // exact (read only)
    dataMin: TAG_LEN + 1, dataMax: 64 * 1024 * 1024,
    totalMax: 80 * 1024 * 1024
  };

  // Password normalisation (fixed; documented in lock/README.md):
  // 1. Unicode NFKC  2. drop every whitespace and zero-width / invisible formatting char  3. ASCII A-Z -> a-z.
  // Empty result = refused.
  var DROP = /[\s­᠎​-‏‪-‮⁠-⁤⁪-⁯﻿]/g;
  function normalize(s) {
    s = String(s == null ? '' : s);
    if (s.normalize) s = s.normalize('NFKC');
    s = s.replace(DROP, '');
    s = s.replace(/[A-Z]/g, function (c) { return c.toLowerCase(); });
    return s;
  }

  function u32(b, o) { return (b[o] | (b[o + 1] << 8) | (b[o + 2] << 16) | (b[o + 3] << 24)) >>> 0; }
  function u16(b, o) { return (b[o] | (b[o + 1] << 8)) >>> 0; }
  function hex(b) { var s = ''; for (var i = 0; i < b.length; i++) s += (b[i] < 16 ? '0' : '') + b[i].toString(16); return s; }

  // Parse and validate the 64-byte clear header. `total` is the real byte length of the downloaded file.
  // Throws Error with .code = 'format' on anything unexpected.
  function parseHeader(b, total) {
    function bad(why) { var e = new Error('bad header: ' + why); e.code = 'format'; throw e; }
    if (!b || b.length < HEADER_LEN) bad('short');
    for (var i = 0; i < 4; i++) if (b[i] !== MAGIC[i]) bad('magic');
    if (b[4] !== 1) bad('version');
    if (b[5] !== 1) bad('kdf');
    if (b[6] !== 1) bad('aead');
    if (b[7] !== 0) bad('flags');
    var m = u32(b, 8), t = u16(b, 12), p = u16(b, 14);
    if (!(m >= LIMITS.mMin && m <= LIMITS.mMax)) bad('m');
    if (!(t >= LIMITS.tMin && t <= LIMITS.tMax)) bad('t');
    if (!(p >= LIMITS.pMin && p <= LIMITS.pMax)) bad('p');
    if (m < 8 * p) bad('m<8p');
    var salt = b.slice(16, 32), nMeta = b.slice(32, 44), nData = b.slice(44, 56);
    var same = true;
    for (var j = 0; j < 12; j++) if (nMeta[j] !== nData[j]) { same = false; break; }
    if (same) bad('nonce reuse');
    var metaLen = u32(b, 56), dataLen = u32(b, 60);
    if (metaLen !== LIMITS.metaLen && metaLen !== LIMITS.legacyMetaLen) bad('metaLen');
    if (!(dataLen >= LIMITS.dataMin && dataLen <= LIMITS.dataMax)) bad('dataLen');
    var want = HEADER_LEN + metaLen + dataLen;
    if (want > LIMITS.totalMax) bad('total');
    if (total !== want) bad('length mismatch');
    if (total % BLOCK !== 0) bad('padding');
    return { m: m, t: t, p: p, salt: salt, saltHex: hex(salt), nonceMeta: nMeta, nonceData: nData, metaLen: metaLen, dataLen: dataLen, header: b.slice(0, HEADER_LEN) };
  }

  // Total length the header CLAIMS for the whole file (header + manifest + data); -1 if it cannot be read or is
  // beyond the hard limit. Used to stop a download early, before the real validation in parseHeader().
  function declaredLen(b) {
    if (!b || b.length < HEADER_LEN) return -1;
    var want = HEADER_LEN + u32(b, 56) + u32(b, 60);
    return want > LIMITS.totalMax ? -1 : want;
  }

  // Additional data for the two AEAD sections: header || 0x01 (manifest) and header || 0x02 (data).
  function aad(header, which) {
    var a = new Uint8Array(HEADER_LEN + 1);
    for (var i = 0; i < HEADER_LEN; i++) a[i] = header[i];
    a[HEADER_LEN] = which;
    return a;
  }

  // Validate a decrypted manifest object against the decrypted data length.
  function checkManifest(man, dataLen) {
    function bad(why) { var e = new Error('bad manifest: ' + why); e.code = 'format'; throw e; }
    if (!man || man.v !== 1 || !man.files || typeof man.files.length !== 'number') bad('shape');
    var seen = {};
    for (var i = 0; i < man.files.length; i++) {
      var f = man.files[i];
      if (!f || typeof f.p !== 'string' || !f.p || f.p.charAt(0) === '/' || f.p.indexOf('..') >= 0) bad('path');
      if (seen[f.p]) bad('dup');
      seen[f.p] = 1;
      if (!(f.o >= 0 && f.n >= 0 && f.o + f.n <= dataLen) || f.o % 1 || f.n % 1) bad('range');
      if (typeof f.t !== 'string') bad('type');
    }
    return man;
  }

  // Rewrite every url(...) in a CSS text. `map(value)` returns a replacement URL string, or null to leave the
  // original text untouched. Quoted values are skipped as a whole, so url(...) nested inside a data: SVG stays as is.
  function rewriteCssUrls(css, map) {
    var out = '', last = 0, pos = 0, low = css.toLowerCase();
    for (;;) {
      var k = low.indexOf('url(', pos);
      if (k < 0) break;
      var s = k + 4;
      while (s < css.length && /\s/.test(css.charAt(s))) s++;
      var q = css.charAt(s), val, end;
      if (q === '"' || q === "'") {
        var j = s + 1;
        while (j < css.length && css.charAt(j) !== q) { if (css.charAt(j) === '\\') j++; j++; }
        val = css.slice(s + 1, j);
        end = css.indexOf(')', j + 1);
      } else {
        end = css.indexOf(')', s);
        val = end < 0 ? '' : css.slice(s, end).replace(/\s+$/, '');
      }
      if (end < 0) break;
      var rep = map(val);
      if (rep != null) { out += css.slice(last, k) + 'url("' + rep + '")'; last = end + 1; }
      pos = end + 1;
    }
    return out + css.slice(last);
  }

  return {
    MAGIC: MAGIC, HEADER_LEN: HEADER_LEN, TAG_LEN: TAG_LEN, MANIFEST_PLAIN_LEN: MANIFEST_PLAIN_LEN, BLOCK: BLOCK,
    INFO: INFO, LIMITS: LIMITS, normalize: normalize, parseHeader: parseHeader, aad: aad,
    checkManifest: checkManifest, rewriteCssUrls: rewriteCssUrls, hex: hex, declaredLen: declaredLen
  };
})();

  var KDF_FILES = [{"u":"l/kdf.401cd2ee.js","i":"sha384-kCquTiLsZ8u0lhjzl1P8c7aoAjar89hdffVsXNIoNjcP9c73l/flvf/TWDNFtmnp","k":"wasm"},{"u":"l/kdf2.fcaf5d59.js","i":"sha384-dOZ07E4m/d09MEzfZuzhMjGo1Mwz4imy7Tlb/a/gcKr5fPFwwojJKk8R8tnG4HqG","k":"js"}];
  var RELAY_TURN = "https://group-relay.hxzroom.workers.dev/turn";   // exact URL string, or null: nothing may leave the device
  var CSP2 = "default-src 'none'; script-src blob:; style-src blob: 'unsafe-inline'; img-src blob: data:; font-src blob: data:; media-src blob: data:; connect-src https://group-relay.hxzroom.workers.dev/turn";

  var T = (window.__LOCK_TEST && typeof window.__LOCK_TEST === 'object') ? window.__LOCK_TEST : {};
  var STAT = window.__LOCK_STAT = { kdf: null, kdfMs: null, kdfTried: [], style: null, cspDynamic: null, fontsMs: null, fontFail: null, hashFail: null, bootMs: null, remembered: null };
  var de = document.documentElement;
  var subtle = window.crypto && window.crypto.subtle;
  var MSG = { wrong: '口令不对，再试一次', busy: '正在开门', broken: '没加载完整，请刷新再试', slow: '这台设备慢一些，请稍等', clearfail: '没能清掉这台设备上的记录，请在浏览器设置里清除本站数据后再试' };

  function $(id) { return document.getElementById(id); }
  var form = $('crl-f'), input = $('crl-pw'), btn = $('crl-go'), msg = $('crl-msg'), rem = $('crl-rm');
  function state(s) { de.setAttribute('data-lock', s); }
  function say(k) { msg.textContent = k ? MSG[k] : ''; msg.setAttribute('data-k', k || ''); }
  function broken() { state('broken'); say('broken'); }

  // 1. Framed by someone else's page: never show the input.
  var framed = false;
  try { framed = window.top !== window.self; } catch (e) { framed = true; }
  if (framed) { state('framed'); return; }
  if (!subtle || !window.fetch || !window.Uint8Array) { broken(); return; }

  // 2. ?lock=1 forgets this device and is removed from the address bar.
  var qs = new URLSearchParams(location.search);
  var forget = qs.get('lock') === '1';
  if (forget) {
    qs.delete('lock');
    var rest = qs.toString();
    try { history.replaceState(history.state, '', location.pathname + (rest ? '?' + rest : '') + location.hash); } catch (e) { }
  }

  // Read a response body but stop as soon as it is longer than the header says (or longer than the hard limit).
  function readLimited(r) {
    function over() { var e = new Error('size'); e.code = 'format'; return e; }
    if (!r.body || !r.body.getReader) {
      return r.arrayBuffer().then(function (b) { if (b.byteLength > CRL.LIMITS.totalMax) throw over(); return b; });
    }
    var rd = r.body.getReader(), chunks = [], got = 0, want = 0;   // want 0 = header not read yet
    function join(n) {
      var out = new Uint8Array(n), o = 0;
      for (var i = 0; i < chunks.length && o < n; i++) { var c = chunks[i].subarray(0, n - o); out.set(c, o); o += c.length; }
      return out;
    }
    function stop() { try { rd.cancel(); } catch (e) { } return over(); }
    return (function pump() {
      return rd.read().then(function (x) {
        if (x.done) return join(got).buffer;
        chunks.push(x.value); got += x.value.length;
        if (!want && got >= CRL.HEADER_LEN) {
          want = CRL.declaredLen(join(CRL.HEADER_LEN));
          if (want < 0) throw stop();
        }
        if (got > (want || CRL.LIMITS.totalMax)) throw stop();
        return pump();
      });
    })();
  }

  // 3. Start the download right away; check length and SHA-256 before anything else touches it.
  var metaEl = document.querySelector('meta[name="crl-data"]');
  var spec = (metaEl && metaEl.getAttribute('content') || '').split(/\s+/);
  var binPath = spec[0], binHash = (spec[1] || '').replace(/^sha256-/, '');
  var pkgP = (function () {
    if (!binPath || !/^[0-9a-f]{64}$/.test(binHash)) return Promise.reject(new Error('meta'));
    return fetch(binPath, { credentials: 'omit', referrerPolicy: 'no-referrer', cache: 'no-cache' })
      .then(function (r) { if (!r.ok) throw new Error('http ' + r.status); return readLimited(r); })
      .then(function (buf) {
        return subtle.digest('SHA-256', buf).then(function (d) {
          if (CRL.hex(new Uint8Array(d)) !== binHash) throw new Error('hash');
          var u8 = new Uint8Array(buf);
          var h = CRL.parseHeader(u8.subarray(0, CRL.HEADER_LEN), u8.length);
          h.buf = buf;
          h.metaCt = u8.subarray(CRL.HEADER_LEN, CRL.HEADER_LEN + h.metaLen);
          h.dataCt = u8.subarray(CRL.HEADER_LEN + h.metaLen);
          return h;
        });
      });
  })();
  pkgP.catch(function () { });   // handled where awaited

  // ---------- small IndexedDB helper (store "k", key = salt hex, value = { key: CryptoKey, at }) ----------
  var IDB = {
    db: null,
    open: function () {
      return new Promise(function (ok, no) {
        if (!window.indexedDB) return no(new Error('no idb'));
        var r = indexedDB.open('crl', 1);
        r.onupgradeneeded = function () { r.result.createObjectStore('k'); };
        r.onsuccess = function () { IDB.db = r.result; ok(r.result); };
        r.onerror = function () { no(r.error); };
        r.onblocked = function () { no(new Error('blocked')); };
      });
    },
    tx: function (mode, fn) {
      return new Promise(function (ok, no) {
        var t = IDB.db.transaction('k', mode), st = t.objectStore('k'), res;
        try { res = fn(st); } catch (e) { return no(e); }
        t.oncomplete = function () { ok(res && 'result' in res ? res.result : undefined); };
        t.onerror = t.onabort = function () { no(t.error || new Error('idb')); };
      });
    },
    all: function () {
      return Promise.all([IDB.tx('readonly', function (s) { return s.getAllKeys(); }), IDB.tx('readonly', function (s) { return s.getAll(); })])
        .then(function (r) { return r[0].map(function (k, i) { return { k: k, v: r[1][i] }; }); });
    },
    get: function (k) { return IDB.tx('readonly', function (s) { return s.get(k); }); },
    put: function (k, v) { return IDB.tx('readwrite', function (s) { return s.put(v, k); }); },
    del: function (k) { return IDB.tx('readwrite', function (s) { return s['delete'](k); }); },
    clear: function () { return IDB.tx('readwrite', function (s) { return s.clear(); }); }
  };

  // ---------- crypto ----------
  function utf8(s) { return new TextEncoder().encode(s); }
  function deriveKey(root, salt) {
    return subtle.importKey('raw', root, 'HKDF', false, ['deriveKey']).then(function (ikm) {
      return subtle.deriveKey({ name: 'HKDF', hash: 'SHA-256', salt: salt, info: utf8(CRL.INFO) }, ikm, { name: 'AES-GCM', length: 256 }, false, ['decrypt']);
    });
  }
  function openManifest(pkg, key) {
    return subtle.decrypt({ name: 'AES-GCM', iv: pkg.nonceMeta, additionalData: CRL.aad(pkg.header, 1), tagLength: 128 }, key, pkg.metaCt)
      .then(function (pt) {
        var man;
        try { man = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(pt)); } catch (e) { var er = new Error('manifest json'); er.code = 'format'; throw er; }
        return CRL.checkManifest(man, pkg.dataLen - CRL.TAG_LEN);
      }, function () { var e = new Error('tag'); e.code = 'wrong'; throw e; });
  }
  function openData(pkg, key) {
    return subtle.decrypt({ name: 'AES-GCM', iv: pkg.nonceData, additionalData: CRL.aad(pkg.header, 2), tagLength: 128 }, key, pkg.dataCt);
  }

  // ---------- Argon2id: Web Worker first, main thread second; WASM first, pure JS second ----------
  var fileCache = {};
  function kdfBytes(i) {
    if (!fileCache[i]) {
      var f = KDF_FILES[i];
      fileCache[i] = fetch(f.u, { credentials: 'omit', referrerPolicy: 'no-referrer' })
        .then(function (r) { if (!r.ok) throw new Error('http'); return r.arrayBuffer(); })
        .then(function (b) {
          return subtle.digest('SHA-384', b).then(function (d) {
            var s = '', u = new Uint8Array(d);
            for (var j = 0; j < u.length; j++) s += String.fromCharCode(u[j]);
            if ('sha384-' + btoa(s) !== f.i) throw new Error('integrity');
            return b;
          });
        });
      fileCache[i].catch(function () { delete fileCache[i]; });
    }
    return fileCache[i];
  }
  function kdfInWorker(i, job) {
    if (T.noWorker || typeof Worker !== 'function') return Promise.reject(new Error('no worker'));
    return kdfBytes(i).then(function (bytes) {
      return new Promise(function (ok, no) {
        var url = URL.createObjectURL(new Blob([bytes], { type: 'text/javascript' })), w;
        function done() { try { w.terminate(); } catch (e) { } URL.revokeObjectURL(url); }
        try { w = new Worker(url); } catch (e) { URL.revokeObjectURL(url); return no(e); }
        w.onmessage = function (e) {
          done();
          if (e.data && e.data.ok) ok(new Uint8Array(e.data.out)); else no(new Error(e.data && e.data.err || 'worker'));
        };
        w.onerror = function (e) { done(); no(new Error('worker error ' + (e && e.message || ''))); };
        w.postMessage({ pw: job.pw, salt: job.salt, m: job.m, t: job.t, p: job.p });
      });
    });
  }
  function kdfOnMain(i, job) {
    var f = KDF_FILES[i];
    var ready = window.__crlKdf && window.__crlKdf[f.k] ? Promise.resolve() : new Promise(function (ok, no) {
      var s = document.createElement('script');
      s.src = f.u; s.integrity = f.i; s.crossOrigin = 'anonymous';
      s.onload = ok; s.onerror = function () { no(new Error('script')); };
      document.head.appendChild(s);
    });
    return ready.then(function () {
      var api = window.__crlKdf && window.__crlKdf[f.k];
      if (!api) throw new Error('kdf missing');
      return api.runAsync(job);
    }).then(function (out) { return new Uint8Array(out); });
  }
  function kdf(job) {
    var order = T.forceJsKdf ? [1] : [0, 1];
    var steps = [];
    order.forEach(function (i) {
      steps.push({ i: i, where: 'worker' });
      steps.push({ i: i, where: 'main' });
    });
    var t0 = performance.now();
    return steps.reduce(function (p, st) {
      return p.catch(function () {
        if (KDF_FILES[st.i].k === 'js') say('slow');
        STAT.kdfTried.push(KDF_FILES[st.i].k + '-' + st.where);
        return (st.where === 'worker' ? kdfInWorker : kdfOnMain)(st.i, job).then(function (out) {
          STAT.kdf = KDF_FILES[st.i].k + '-' + st.where;
          STAT.kdfMs = Math.round(performance.now() - t0);
          return out;
        });
      });
    }, Promise.reject(new Error('start')));
  }

  function frames(n) { return new Promise(function (done) { (function f(k) { if (!k) return done(); requestAnimationFrame(function () { f(k - 1); }); })(n); }); }

  // ---------- UI ----------
  var busy = false, composing = false;
  input.addEventListener('compositionstart', function () { composing = true; });
  input.addEventListener('compositionend', function () { composing = false; });
  input.addEventListener('keydown', function (e) {
    if ((e.key === 'Enter' || e.keyCode === 13 || e.keyCode === 229) && (e.isComposing || composing || e.keyCode === 229)) e.preventDefault();
  });
  form.addEventListener('submit', function (e) { e.preventDefault(); submit(); });

  // A broken download is reported as soon as it is known, not only after the passphrase is typed.
  // It can fail before the form is first shown (local check of the remembered key still running), so ask() looks too.
  var pkgBad = false;
  pkgP.catch(function () { pkgBad = true; if (!busy && de.getAttribute('data-lock') === 'ask') broken(); });

  function ask(k) {
    if (pkgBad) { busy = false; broken(); return; }
    busy = false;
    state('ask');
    say(k || '');
    input.readOnly = false; btn.disabled = false;
    if (k === 'wrong') { try { input.focus(); input.select(); } catch (e) { } }
  }

  function submit() {
    if (busy) return;
    var pw = CRL.normalize(input.value);
    if (!pw) { say('wrong'); return; }
    busy = true; input.readOnly = true; btn.disabled = true;
    state('busy'); say('busy');
    var pkg, key;
    frames(2).then(function () { return pkgP; }).then(function (p) {
      pkg = p;
      return kdf({ pw: utf8(pw), salt: pkg.salt, m: pkg.m, t: pkg.t, p: pkg.p });
    }, function (e) { e.code = 'broken'; throw e; }).then(function (root) {
      return deriveKey(root, pkg.salt).then(function (k) { root.fill(0); return k; });
    }).then(function (k) {
      key = k;
      return openManifest(pkg, key);
    }).then(function (man) {
      input.value = '';
      return remember(pkg, key).then(function () { return boot(pkg, key, man); });
    }).catch(function (e) {
      if (e && e.code === 'wrong') ask('wrong'); else broken();
    });
  }

  // Store the non-extractable key, read it back and prove it still decrypts; otherwise act as if not remembered.
  function remember(pkg, key) {
    if (!IDB.db) { STAT.remembered = false; return Promise.resolve(); }
    var drop = IDB.all().then(function (rs) {
      return Promise.all(rs.filter(function (r) { return r.k !== pkg.saltHex; }).map(function (r) { return IDB.del(r.k); }));
    }).catch(function () { });
    if (!rem.checked) { STAT.remembered = false; return drop.then(function () { return IDB.del(pkg.saltHex); }).catch(function () { }); }
    return drop.then(function () { return IDB.put(pkg.saltHex, { key: key, at: Date.now() }); })
      .then(function () { return IDB.get(pkg.saltHex); })
      .then(function (v) {
        if (!v || !v.key) throw new Error('readback');
        return openManifest(pkg, v.key);
      })
      .then(function () { STAT.remembered = true; }, function () { STAT.remembered = false; return IDB.del(pkg.saltHex).catch(function () { }); });
  }

  // ---------- after unlock: run the original site from memory ----------
  function boot(pkg, key, man) {
    var tBoot = performance.now();
    state('loading');
    return openData(pkg, key).then(function (data) {
      return verifyFiles(data, man).then(function () { return start(data, man); }).then(function () { STAT.bootMs = Math.round(performance.now() - tBoot); });
    }, function () { var e = new Error('data'); e.code = 'broken'; throw e; });
  }

  // Every file inside the decrypted data must match the SHA-256 the manifest lists for it, or nothing runs.
  function verifyFiles(data, man) {
    STAT.hashFail = 0;
    return Promise.all(man.files.map(function (f) {
      var ok = typeof f.h === 'string' && /^[0-9a-f]{64}$/.test(f.h);
      if (!ok) { STAT.hashFail++; return null; }
      return subtle.digest('SHA-256', new Uint8Array(data, f.o, f.n)).then(function (d) {
        if (CRL.hex(new Uint8Array(d)) !== f.h) STAT.hashFail++;
      });
    })).then(function () {
      if (STAT.hashFail) { var e = new Error('file hash'); e.code = 'broken'; throw e; }
    });
  }

  function start(data, man) {
    var ROOT = new URL('.', location.href);
    var files = {}, urls = {};
    man.files.forEach(function (f) { files[f.p] = f; });
    function bytes(p) { var f = files[p]; return new Uint8Array(data, f.o, f.n); }
    function text(p) { return new TextDecoder('utf-8').decode(bytes(p)); }
    function blobOf(p) { return new Blob([bytes(p)], { type: files[p].t }); }
    function urlOf(p) { if (!urls[p]) urls[p] = URL.createObjectURL(blobOf(p)); return urls[p]; }
    var MISS = 'data:,';

    // Site-relative path for anything that points inside the site folder, else null.
    function relOf(u, base) {
      var x;
      try { x = new URL(u, base || document.baseURI); } catch (e) { return null; }
      if (x.origin !== ROOT.origin || x.pathname.indexOf(ROOT.pathname) !== 0) return null;
      var rel;
      try { rel = decodeURIComponent(x.pathname.slice(ROOT.pathname.length)); } catch (e) { return null; }
      return rel;
    }
    // Returns the string to really use. data:/blob:/empty pass through; files from the package become blob:;
    // everything else (unknown site path or any other origin) becomes "data:," so nothing ever leaves the device.
    function mapUrl(v, base) {
      if (v == null) return v;
      var s = String(v);
      if (s === '' || /^\s*(data|blob):/i.test(s)) return v;
      var rel = relOf(s, base);
      if (rel && rel !== 'index.html' && files[rel]) return urlOf(rel);
      return MISS;
    }
    function fixCss(v, base) {
      var s = String(v);
      if (s.indexOf('url(') < 0 && s.toLowerCase().indexOf('url(') < 0) return v;
      return CRL.rewriteCssUrls(s, function (u) {
        if (!u || /^\s*(data|blob):/i.test(u) || u.charAt(0) === '#') return null;
        return mapUrl(u, base);
      });
    }

    // --- the original index.html, parsed (not executed) ---
    var doc = new DOMParser().parseFromString(text('index.html'), 'text/html');
    var sheets = [].map.call(doc.querySelectorAll('link[rel~="stylesheet"][href]'), function (l) { return relOf(l.getAttribute('href'), ROOT.href); });
    var scripts = [].map.call(doc.querySelectorAll('script[src]'), function (s) { return relOf(s.getAttribute('src'), ROOT.href); });
    if (sheets.some(function (p) { return !p || !files[p]; }) || scripts.some(function (p) { return !p || !files[p]; })) {
      return Promise.reject(Object.assign(new Error('index refs'), { code: 'broken' }));
    }

    // --- second CSP: from here on the page can reach exactly one network address, the relay's /turn (or none) ---
    var csp = document.createElement('meta');
    csp.httpEquiv = 'Content-Security-Policy';
    csp.content = CSP2;
    document.head.appendChild(csp);
    // Is the second policy really enforced? It drops 'wasm-unsafe-eval', so compiling the smallest valid
    // module must now be refused. No network either way. true = enforced, false = ignored, null = cannot tell.
    STAT.cspDynamic = (function () {
      if (!window.WebAssembly || typeof WebAssembly.Module !== 'function') return null;
      try { new WebAssembly.Module(new Uint8Array([0, 97, 115, 109, 1, 0, 0, 0])); return false; } catch (e) { return true; }
    })();

    // --- interception layer (installed before any original script runs) ---
    var dImg = Object.getOwnPropertyDescriptor(HTMLImageElement.prototype, 'src');
    Object.defineProperty(HTMLImageElement.prototype, 'src', { configurable: true, enumerable: dImg.enumerable, get: dImg.get, set: function (v) { dImg.set.call(this, mapUrl(v)); } });
    var dMed = Object.getOwnPropertyDescriptor(HTMLMediaElement.prototype, 'src');
    Object.defineProperty(HTMLMediaElement.prototype, 'src', { configurable: true, enumerable: dMed.enumerable, get: dMed.get, set: function (v) { dMed.set.call(this, mapUrl(v)); } });
    if (window.HTMLSourceElement) {
      var dSrc = Object.getOwnPropertyDescriptor(HTMLSourceElement.prototype, 'src');
      if (dSrc && dSrc.set) Object.defineProperty(HTMLSourceElement.prototype, 'src', { configurable: true, enumerable: dSrc.enumerable, get: dSrc.get, set: function (v) { dSrc.set.call(this, mapUrl(v)); } });
    }
    var nSetAttr = Element.prototype.setAttribute;
    Element.prototype.setAttribute = function (n, v) {
      var ln = String(n).toLowerCase();
      if (ln === 'src' && (this instanceof HTMLImageElement || this instanceof HTMLMediaElement || (window.HTMLSourceElement && this instanceof HTMLSourceElement))) v = mapUrl(v);
      else if (ln === 'style' && String(v).indexOf('url(') >= 0) v = fixCss(v);
      return nSetAttr.call(this, n, v);
    };
    var NAudio = window.Audio;
    var Audio2 = function Audio(src) { var a = new NAudio(); if (arguments.length && src !== undefined) a.src = src; return a; };
    Audio2.prototype = NAudio.prototype;
    window.Audio = Audio2;
    var nFetch = window.fetch;
    // The only request that may leave the device: POST <relay>/turn, rebuilt here from the body alone (the caller's
    // headers, credentials, mode, redirect and referrer settings are never forwarded). Anything else gets the 404 below.
    var NOPE = function () { return Promise.resolve(new Response('', { status: 404, statusText: 'Not Found' })); };
    function relayPost(init) {
      if (!init || String(init.method || '').toUpperCase() !== 'POST' || typeof init.body !== 'string') return NOPE();
      if (new TextEncoder().encode(init.body).length > 32768) return NOPE();
      var opt = { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: init.body, mode: 'cors', credentials: 'omit',
        redirect: 'error', referrerPolicy: 'no-referrer', cache: 'no-store' };
      if (window.AbortSignal && init.signal instanceof AbortSignal) opt.signal = init.signal;
      return nFetch.call(window, RELAY_TURN, opt);
    }
    window.fetch = function (input, init) {
      var u = typeof input === 'string' ? input : input && input.url != null ? input.url : String(input);
      if (/^\s*(data|blob):/i.test(u)) return nFetch.apply(this, arguments);
      if (RELAY_TURN && typeof input === 'string' && input === RELAY_TURN) return relayPost(init);
      var rel = relOf(u);
      if (rel && rel !== 'index.html' && files[rel]) return Promise.resolve(new Response(blobOf(rel), { status: 200, statusText: 'OK', headers: { 'Content-Type': files[rel].t } }));
      return NOPE();
    };

    // Inline styles: accessors on the prototype that owns them (CSSStyleDeclaration or CSSStyleProperties).
    var CSS_PROPS = ['backgroundImage', 'background', 'cssText', 'maskImage', 'webkitMaskImage', 'borderImage', 'borderImageSource', 'listStyleImage', 'listStyle', 'content', 'cursor'];
    function ownerOf(prop) { var o = de.style; while (o && !Object.prototype.hasOwnProperty.call(o, prop)) o = Object.getPrototypeOf(o); return o; }
    var protoOk = false;
    if (!T.forceStyleObserver) {
      var bgOwner = ownerOf('backgroundImage'), bgD = bgOwner && Object.getOwnPropertyDescriptor(bgOwner, 'backgroundImage');
      protoOk = !!(bgD && bgD.set && bgD.configurable);
      if (protoOk) {
        CSS_PROPS.forEach(function (prop) {
          var o = ownerOf(prop), d = o && Object.getOwnPropertyDescriptor(o, prop);
          if (!d || !d.set || !d.configurable) return;
          Object.defineProperty(o, prop, { configurable: true, enumerable: d.enumerable, get: d.get, set: function (v) { d.set.call(this, fixCss(v)); } });
        });
        var spOwner = ownerOf('setProperty'), nSP = spOwner && spOwner.setProperty;
        if (nSP) spOwner.setProperty = function (n, v, p) { if (v != null && String(v).indexOf('url(') >= 0) v = fixCss(v); return arguments.length > 2 ? nSP.call(this, n, v, p) : nSP.call(this, n, v); };
      }
    }
    STAT.style = protoOk ? 'prototype' : 'observer';
    if (!protoOk) {
      // Fallback for engines without accessors on the prototype: fix style attributes as they appear.
      // Mutation callbacks run as microtasks, before style is resolved, so the original URL is never requested;
      // if it ever were, the second CSP blocks it.
      var fixEl = function (el) {
        if (!el || el.nodeType !== 1) return;
        var s = el.getAttribute('style');
        if (s && s.indexOf('url(') >= 0) { var f = fixCss(s); if (f !== s) nSetAttr.call(el, 'style', f); }
      };
      new MutationObserver(function (list) {
        list.forEach(function (m) {
          if (m.type === 'attributes') fixEl(m.target);
          else [].forEach.call(m.addedNodes, function (n) {
            if (n.nodeType !== 1) return;
            fixEl(n);
            if (n.querySelectorAll) [].forEach.call(n.querySelectorAll('[style]'), fixEl);
          });
        });
      }).observe(document, { subtree: true, childList: true, attributes: true, attributeFilter: ['style'] });
    }

    // --- hand the document over ---
    [].forEach.call(doc.documentElement.attributes, function (a) { if (a.name !== 'data-lock') de.setAttribute(a.name, a.value); });
    if (doc.title) document.title = doc.title;
    [].forEach.call(doc.head.querySelectorAll('meta[name]'), function (m) {
      var name = m.getAttribute('name'), mine = document.head.querySelector('meta[name="' + name + '"]');
      if (mine) mine.setAttribute('content', m.getAttribute('content') || '');
      else document.head.appendChild(document.importNode(m, true));
    });
    var shellCss = $('crl-css');

    function addSheet(p) {
      return new Promise(function (done) {
        var base = new URL(p, ROOT.href).href;   // url() in a sheet is relative to the sheet itself
        var css = fixCss(text(p), base);
        var l = document.createElement('link');
        l.rel = 'stylesheet';
        l.href = URL.createObjectURL(new Blob([css], { type: 'text/css' }));
        l.onload = l.onerror = function () { done(); };
        document.head.appendChild(l);
      });
    }
    function addScript(p) {
      return new Promise(function (done) {
        var s = document.createElement('script');
        s.async = false;
        s.src = urlOf(p);
        s.onload = s.onerror = function () { done(); };
        document.body.appendChild(s);
      });
    }

    var t0 = performance.now();
    return sheets.reduce(function (pr, p) { return pr.then(function () { return addSheet(p); }); }, Promise.resolve())
      .then(function () {
        // Fonts declared by the sheets: load them all from memory before any script measures text or draws.
        // The original scripts only start once every one of these loads has ended; a failure is counted, not hidden.
        var list = [];
        STAT.fontFail = 0;
        if (document.fonts && document.fonts.forEach) document.fonts.forEach(function (f) {
          list.push(f.load().then(null, function () { STAT.fontFail++; }));
        });
        return Promise.all(list);
      })
      .then(function () {
        STAT.fontsMs = Math.round(performance.now() - t0);
        if (shellCss) shellCss.parentNode.removeChild(shellCss);
        var shell = $('crl');
        if (shell) shell.parentNode.removeChild(shell);
        [].forEach.call(doc.body.attributes, function (a) { document.body.setAttribute(a.name, a.value); });
        [].forEach.call(doc.body.childNodes, function (n) {
          if (n.nodeType === 1 && n.tagName === 'SCRIPT') return;
          document.body.appendChild(document.importNode(n, true));
        });
        state('starting');
        return scripts.reduce(function (pr, p) { return pr.then(function () { return addScript(p); }); }, Promise.resolve());
      })
      .then(function () { state('running'); });   // all original scripts have been loaded and have run
  }

  var clearFailed = false;   // ?lock=1 could not empty the store: say so instead of silently resuming
  // 4. Remembered key for this exact package? Then open without ever showing the form.
  IDB.open().catch(function () { return null; }).then(function () {
    if (!IDB.db) return [];
    return (forget ? IDB.clear() : Promise.resolve()).then(function () { return IDB.all(); }, function () { clearFailed = true; return []; }).catch(function () { return []; });
  }).then(function (recs) {
    if (clearFailed) { ask('clearfail'); return; }
    if (!recs.length) { ask(); return; }
    state('resume'); say('busy');
    return pkgP.then(function (pkg) {
      var hit = null;
      recs.forEach(function (r) { if (r.k === pkg.saltHex && r.v && r.v.key) hit = r; });
      return Promise.all(recs.filter(function (r) { return r !== hit; }).map(function (r) { return IDB.del(r.k).catch(function () { }); }))
        .then(function () {
          if (!hit) { ask(); return; }
          return openManifest(pkg, hit.v.key).then(function (man) {
            STAT.remembered = true;
            return boot(pkg, hit.v.key, man);
          }, function (e) {
            if (e && e.code === 'wrong') return IDB.del(hit.k).catch(function () { }).then(function () { ask(); });
            throw e;
          });
        });
    }, function () { broken(); }).catch(function () { broken(); });
  });
})();
