/* Milgram maze — game logic */
(function () {
  'use strict';
  var C = window.MAZE_CONFIG || {};
  var $ = function (s) { return document.querySelector(s); };
  var GATES = C.GATES || [];
  var NG = GATES.length;
  var VMAX = 450;
  var inFrame = (function () { try { return window.self !== window.top; } catch (e) { return true; } })();

  /* ---------- storage-safe prefs ---------- */
  function pget(k, d) { try { var v = localStorage.getItem('mm_' + k); return v === null ? d : v; } catch (e) { return d; } }
  function pset(k, v) { try { localStorage.setItem('mm_' + k, v); } catch (e) {} }

  /* ---------- sound (WebAudio, synthesized) ---------- */
  var muted = pget('muted', C.SOUND_ON_BY_DEFAULT === false ? '1' : '0') === '1';
  var AC = null;
  function ac() {
    if (!AC) { try { AC = new (window.AudioContext || window.webkitAudioContext)(); } catch (e) { AC = null; } }
    if (AC && AC.state === 'suspended') { try { AC.resume(); } catch (e) {} }
    return AC;
  }
  function tone(f, dur, type, vol, when, slideTo) {
    if (muted) return; var a = ac(); if (!a) return;
    var t = a.currentTime + (when || 0);
    var o = a.createOscillator(), g = a.createGain();
    o.type = type || 'sine'; o.frequency.setValueAtTime(f, t);
    if (slideTo) o.frequency.exponentialRampToValueAtTime(slideTo, t + dur);
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(vol || 0.12, t + 0.012);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(a.destination); o.start(t); o.stop(t + dur + 0.02);
  }
  function noise(dur, vol, when) {
    if (muted) return; var a = ac(); if (!a) return;
    var t = a.currentTime + (when || 0), n = Math.floor(a.sampleRate * dur);
    var b = a.createBuffer(1, n, a.sampleRate), d = b.getChannelData(0);
    for (var i = 0; i < n; i++) d[i] = (Math.random() * 2 - 1) * (1 - i / n);
    var s = a.createBufferSource(), g = a.createGain(), f = a.createBiquadFilter();
    f.type = 'bandpass'; f.frequency.value = 2400; f.Q.value = 0.8;
    s.buffer = b; g.gain.value = vol || 0.15; s.connect(f); f.connect(g); g.connect(a.destination); s.start(t);
  }
  var SFX = {
    step: function () { tone(880, 0.035, 'triangle', 0.025); },
    bump: function () { tone(140, 0.08, 'square', 0.04); },
    zap: function () { noise(0.28, 0.22); tone(90, 0.3, 'sawtooth', 0.09, 0, 900); },
    wrong: function () { tone(220, 0.16, 'square', 0.06); tone(165, 0.22, 'square', 0.06, 0.12); },
    right: function () { tone(660, 0.12, 'sine', 0.12); tone(990, 0.18, 'sine', 0.12, 0.09); },
    note: function () { tone(1320, 0.08, 'sine', 0.08); tone(1760, 0.12, 'sine', 0.07, 0.07); },
    gate: function () { tone(330, 0.14, 'triangle', 0.1); tone(440, 0.14, 'triangle', 0.1, 0.1); tone(660, 0.24, 'triangle', 0.1, 0.2); },
    win: function () { [523, 659, 784, 1046, 1318].forEach(function (f, i) { tone(f, 0.25, 'triangle', 0.11, i * 0.11); }); noise(0.5, 0.18, 0.6); tone(80, 0.6, 'sawtooth', 0.1, 0.6, 1200); }
  };
  function setMuteIcon() { var b = $('#mute'); b.textContent = muted ? '🔇' : '🔊'; b.setAttribute('aria-label', muted ? 'הפעלת צלילים' : 'השתקה'); }

  /* ---------- maze generation ---------- */
  var DIRS = { N: [0, -1, 1, 4], E: [1, 0, 2, 8], S: [0, 1, 4, 1], W: [-1, 0, 8, 2] };
  var DKEYS = ['N', 'E', 'S', 'W'];
  var cols = 15, rows = 9, grid = null, startI = 0, exitI = 0, path = [], gates = [], notes = [], visited = null;

  function generate(c, r) {
    var g = new Uint8Array(c * r); g.fill(15);
    var seen = new Uint8Array(c * r), st = [startI]; seen[startI] = 1;
    while (st.length) {
      var cur = st[st.length - 1], x = cur % c, y = (cur / c) | 0, nb = [];
      for (var k = 0; k < 4; k++) {
        var D = DIRS[DKEYS[k]], nx = x + D[0], ny = y + D[1];
        if (nx >= 0 && ny >= 0 && nx < c && ny < r && !seen[ny * c + nx]) nb.push([ny * c + nx, D[2], D[3]]);
      }
      if (!nb.length) { st.pop(); continue; }
      var pick = nb[(Math.random() * nb.length) | 0];
      g[cur] &= ~pick[1]; g[pick[0]] &= ~pick[2]; seen[pick[0]] = 1; st.push(pick[0]);
    }
    return g;
  }
  function neighbors(i, g) {
    var out = [], x = i % cols, y = (i / cols) | 0;
    for (var k = 0; k < 4; k++) { var D = DIRS[DKEYS[k]]; if (!(g[i] & D[2])) out.push((y + D[1]) * cols + x + D[0]); }
    return out;
  }
  function bfs(from, to, blocked) {
    var prev = new Int32Array(cols * rows).fill(-1), q = [from], h = 0; prev[from] = from;
    while (h < q.length) {
      var c = q[h++]; if (c === to) break;
      var nb = neighbors(c, grid);
      for (var j = 0; j < nb.length; j++) {
        var n = nb[j]; if (prev[n] !== -1) continue;
        if (blocked && n !== to && blocked(n)) continue;
        prev[n] = c; q.push(n);
      }
    }
    if (prev[to] === -1) return null;
    var p = [to]; while (p[p.length - 1] !== from) p.push(prev[p[p.length - 1]]);
    return p.reverse();
  }
  function chooseSize() {
    var r = $('#mazewrap').getBoundingClientRect();
    var asp = Math.max(0.45, Math.min(2.4, (r.width || 16) / (r.height || 9)));
    var target = r.width < 500 && r.height < 500 ? 104 : 140;
    cols = Math.round(Math.sqrt(target * asp)); rows = Math.round(target / cols);
    cols = Math.max(7, Math.min(21, cols)); rows = Math.max(7, Math.min(17, rows));
  }
  function noteList() {
    return (C.NOTES || []).map(function (n) { return typeof n === 'string' ? { src: '', text: n } : { src: n.src || '', text: n.text || '' }; });
  }
  var NOTE_DEFS = noteList(), NM = NOTE_DEFS.length;
  function segOfNote(k) { if (NM <= 1) return NG - 1; return Math.min(NG - 1, Math.round(k * (NG - 1) / (NM - 1))); }
  function placeGatesNotes() {
    var L = path.length, N = cols * rows, gIdx = [];
    gates = [];
    for (var i = 0; i < NG; i++) {
      var idx = (i === NG - 1) ? L - 2 : Math.round(3 + (i + 1) * (L - 8) / NG);
      gIdx.push(idx); gates.push({ cell: path[idx], open: false, n: i, anim: 0, idx: idx });
    }
    // every off-route cell hangs on the route at exactly one cell (the maze is a tree): find it + its depth
    var pos = new Int32Array(N).fill(-1), att = new Int32Array(N).fill(-1), dep = new Int32Array(N).fill(-1), q = [], h = 0;
    for (var p = 0; p < L; p++) { pos[path[p]] = p; att[path[p]] = p; dep[path[p]] = 0; q.push(path[p]); }
    while (h < q.length) {
      var c = q[h++], nb = neighbors(c, grid);
      for (var j = 0; j < nb.length; j++) { var n = nb[j]; if (dep[n] !== -1) continue; dep[n] = dep[c] + 1; att[n] = att[c]; q.push(n); }
    }
    function segOfIdx(a) { for (var s = 0; s < NG; s++) { if (a === gIdx[s]) return -1; if (a < gIdx[s]) return s; } return -1; }
    var fallbacks = 0, sx = startI % cols, sy = (startI / cols) | 0;
    notes = [];
    for (var k = 0; k < NM; k++) {
      var seg = segOfNote(k), lo = seg === 0 ? 1 : gIdx[seg - 1] + 1, hi = gIdx[seg] - 1;
      var best = -1, bestS = 1e9;
      for (var cc = 0; cc < N; cc++) {
        if (dep[cc] < 1 || segOfIdx(att[cc]) !== seg) continue;
        var dead = neighbors(cc, grid).length === 1, d = dep[cc];
        var sc = Math.abs(d - 3) * 1.2 + (d > 6 ? (d - 6) * 3 : 0) + (dead ? 0 : 2.5) + Math.random() * 0.8;
        var x = cc % cols, y = (cc / cols) | 0;
        if (Math.abs(x - sx) + Math.abs(y - sy) < 3) sc += 6;
        for (var m = 0; m < notes.length; m++) { var nx = notes[m].cell % cols, ny = (notes[m].cell / cols) | 0; if (Math.abs(nx - x) + Math.abs(ny - y) < 3) sc += 4; }
        if (sc < bestS) { bestS = sc; best = cc; }
      }
      if (best < 0 || bestS > 8) fallbacks++;
      if (best < 0) { // no side branch in this stretch: put it right on the route (always reachable)
        best = path[Math.max(1, Math.min(L - 3, Math.round((lo + hi) / 2)))]; fallbacks += 3;
      }
      notes.push({ cell: best, k: k, seg: seg, dep: dep[best], src: NOTE_DEFS[k].src, text: NOTE_DEFS[k].text, taken: false, read: false });
    }
    return fallbacks;
  }
  function buildMaze() {
    chooseSize();
    startI = cols - 1; exitI = (rows - 1) * cols;
    var best = null, bestScore = 1e9, N = cols * rows;
    for (var t = 0; t < 30; t++) {
      var g = generate(cols, rows); grid = g;
      path = bfs(startI, exitI);
      var sc = Math.abs(path.length - 0.42 * N) + placeGatesNotes() * 12;
      if (sc < bestScore) { bestScore = sc; best = { g: g, p: path, gates: gates, notes: notes }; }
    }
    grid = best.g; path = best.p; gates = best.gates; notes = best.notes;
    visited = new Uint8Array(N); visited[startI] = 1;
    hintPath = null; hintOn = false; lastProgress = performance.now();
  }
  function notesLeft() { return notes.filter(function (n) { return !n.read; }).length; }
  function missingFor(G) { return notes.filter(function (n) { return !n.read && (G.n === NG - 1 || n.seg <= G.n); }).length; }
  var hintPath = null, hintFrom = -1, hintOn = false, hintToastShown = false, lastProgress = 0;
  function gateAt(i) { for (var k = 0; k < gates.length; k++) if (gates[k].cell === i) return gates[k]; return null; }
  function closedGate(i) { var g = gateAt(i); return g && !g.open; }
  function noteAt(i) { for (var k = 0; k < notes.length; k++) if (notes[k].cell === i && !notes[k].taken) return notes[k]; return null; }

  /* ---------- canvas rendering ---------- */
  var cv = $('#maze'), ctx = cv.getContext('2d'), layer = document.createElement('canvas'), lctx = layer.getContext('2d');
  var dpr = 1, W = 0, H = 0, cell = 20, ox = 0, oy = 0;
  function layout() {
    var r = $('#mazewrap').getBoundingClientRect();
    dpr = Math.min(2.5, window.devicePixelRatio || 1);
    W = Math.max(50, r.width); H = Math.max(50, r.height);
    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
    layer.width = cv.width; layer.height = cv.height;
    var pad = Math.max(8, Math.min(W, H) * 0.035);
    cell = Math.floor(Math.min((W - pad * 2) / cols, (H - pad * 2) / rows));
    ox = Math.round((W - cell * cols) / 2); oy = Math.round((H - cell * rows) / 2);
    drawLayer();
  }
  function cxy(i) { return [ox + (i % cols + 0.5) * cell, oy + (((i / cols) | 0) + 0.5) * cell]; }
  function drawLayer() {
    if (!grid) return;
    var g = lctx; g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, W, H);
    // floor
    g.fillStyle = 'rgba(40,231,255,0.035)';
    for (var i = 0; i < cols * rows; i++) { var x = ox + (i % cols) * cell, y = oy + ((i / cols) | 0) * cell; g.fillRect(x + cell * 0.46, y + cell * 0.46, cell * 0.08, cell * 0.08); }
    // walls
    function walls(width, color, blur) {
      g.save(); g.lineCap = 'round'; g.lineJoin = 'round'; g.strokeStyle = color; g.lineWidth = width; g.shadowColor = '#28e7ff'; g.shadowBlur = blur;
      g.beginPath();
      for (var i = 0; i < cols * rows; i++) {
        var x = ox + (i % cols) * cell, y = oy + ((i / cols) | 0) * cell, w = grid[i];
        if (w & 1) { g.moveTo(x, y); g.lineTo(x + cell, y); }
        if (w & 8) { g.moveTo(x, y); g.lineTo(x, y + cell); }
        if ((i % cols) === cols - 1 && (w & 2)) { g.moveTo(x + cell, y); g.lineTo(x + cell, y + cell); }
        if (((i / cols) | 0) === rows - 1 && (w & 4)) { g.moveTo(x, y + cell); g.lineTo(x + cell, y + cell); }
      }
      g.stroke(); g.restore();
    }
    walls(Math.max(2, cell * 0.16), 'rgba(40,231,255,0.35)', cell * 0.5);
    walls(Math.max(1.2, cell * 0.07), '#bdf8ff', 0);
    // start pad
    var s = cxy(startI); g.save(); g.fillStyle = 'rgba(61,255,162,0.14)'; g.strokeStyle = 'rgba(61,255,162,0.6)'; g.lineWidth = 1.5;
    rr(g, s[0] - cell * 0.38, s[1] - cell * 0.38, cell * 0.76, cell * 0.76, cell * 0.15); g.fill(); g.stroke(); g.restore();
  }
  function rr(g, x, y, w, h, r) { g.beginPath(); g.moveTo(x + r, y); g.arcTo(x + w, y, x + w, y + h, r); g.arcTo(x + w, y + h, x, y + h, r); g.arcTo(x, y + h, x, y, r); g.arcTo(x, y, x + w, y, r); g.closePath(); }
  function bolt(g, x, y, s, color) {
    g.save(); g.translate(x, y); g.scale(s / 24, s / 24); g.fillStyle = color; g.beginPath();
    g.moveTo(3, -12); g.lineTo(-7, 2); g.lineTo(-1, 2); g.lineTo(-3, 12); g.lineTo(7, -2); g.lineTo(1, -2); g.closePath(); g.fill(); g.restore();
  }

  function folder(g, x, y, s, glow) {
    var w = s, hh = s * 0.74, r = s * 0.08;
    g.save(); g.translate(x - w / 2, y - hh / 2);
    if (glow) { g.shadowColor = '#ffd84a'; g.shadowBlur = s * 0.6; }
    g.fillStyle = '#d99a12'; rr(g, 0, 0, w * 0.45, hh * 0.3, r); g.fill();            // tab
    g.fillStyle = '#f2b51c'; rr(g, 0, hh * 0.14, w, hh * 0.86, r); g.fill();          // back
    g.shadowBlur = 0;
    g.fillStyle = '#fff6d6'; g.fillRect(w * 0.12, hh * 0.06, w * 0.7, hh * 0.5);       // paper
    g.fillStyle = 'rgba(90,70,0,0.55)'; for (var l = 0; l < 3; l++) g.fillRect(w * 0.2, hh * (0.14 + l * 0.11), w * 0.5, Math.max(1, hh * 0.04));
    var gr = g.createLinearGradient(0, hh * 0.3, 0, hh); gr.addColorStop(0, '#ffe066'); gr.addColorStop(1, '#ffc928');
    g.fillStyle = gr; g.beginPath(); g.moveTo(w * 0.04, hh * 0.32); g.lineTo(w, hh * 0.32); g.lineTo(w * 0.96, hh); g.lineTo(0, hh); g.closePath(); g.fill();
    g.restore();
  }
  var T0 = performance.now();
  var particles = [];
  function frame(now) {
    requestAnimationFrame(frame);
    if (!grid) return;
    var t = (now - T0) / 1000;
    stepPlayer(now);
    if (!locked && NM) {
      if (!hintOn && notesLeft() > 0 && now - lastProgress > (C.NOTES_HINT_SECONDS || 20) * 1000) {
        hintOn = true; hintFrom = -1; updateHint(true);
        if (hintPath && !hintToastShown) { hintToastShown = true; showToast(esc(C.NOTES_HINT || '')); }
        if (!hintPath) { hintOn = false; lastProgress = now; }
      }
      if (hintOn) updateHint(false);
    }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);
    // visited trail
    ctx.fillStyle = 'rgba(40,231,255,0.10)';
    for (var i = 0; i < visited.length; i++) if (visited[i]) { var v = cxy(i); ctx.beginPath(); ctx.arc(v[0], v[1], cell * 0.1, 0, 6.283); ctx.fill(); }
    ctx.drawImage(layer, 0, 0, W, H);
    // exit: XXX switch
    var e = cxy(exitI), lastOpen = gates.length && gates[gates.length - 1].open && notesLeft() === 0;
    ctx.save(); ctx.shadowColor = '#ff3b5c'; ctx.shadowBlur = cell * (0.4 + 0.3 * Math.sin(t * 4));
    ctx.fillStyle = lastOpen ? 'rgba(255,59,92,0.35)' : 'rgba(255,59,92,0.16)'; ctx.strokeStyle = '#ff3b5c'; ctx.lineWidth = 2;
    rr(ctx, e[0] - cell * 0.4, e[1] - cell * 0.4, cell * 0.8, cell * 0.8, cell * 0.14); ctx.fill(); ctx.stroke(); ctx.restore();
    ctx.fillStyle = '#ffd0d8'; ctx.font = '900 ' + Math.max(7, cell * 0.26) + 'px Orbitron, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('XXX', e[0], e[1] - cell * 0.1); ctx.font = '700 ' + Math.max(6, cell * 0.19) + 'px Orbitron, sans-serif'; ctx.fillText('450V', e[0], e[1] + cell * 0.18);
    // hint: dotted golden trail to the nearest research file
    if (hintOn && hintPath && hintPath.length > 1) {
      ctx.save(); ctx.strokeStyle = 'rgba(255,216,74,0.75)'; ctx.lineWidth = Math.max(2, cell * 0.11); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
      ctx.setLineDash([Math.max(1, cell * 0.02), cell * 0.32]); ctx.lineDashOffset = -t * cell * 1.4; ctx.shadowColor = '#ffd84a'; ctx.shadowBlur = cell * 0.3;
      ctx.beginPath(); for (var hp = 0; hp < hintPath.length; hp++) { var hc = cxy(hintPath[hp]); if (hp) ctx.lineTo(hc[0], hc[1]); else ctx.moveTo(hc[0], hc[1]); }
      ctx.stroke(); ctx.restore();
    }
    // research files (glowing folders, pinging from afar)
    for (var n = 0; n < notes.length; n++) {
      if (notes[n].taken) continue; var p = cxy(notes[n].cell), bob = Math.sin(t * 3 + n) * cell * 0.05;
      var ph = ((t * 0.9 + n * 0.37) % 1);
      ctx.save(); ctx.strokeStyle = 'rgba(255,216,74,' + (0.85 * (1 - ph)) + ')'; ctx.lineWidth = Math.max(1.5, cell * 0.07);
      ctx.beginPath(); ctx.arc(p[0], p[1], cell * (0.35 + ph * 0.75), 0, 6.283); ctx.stroke(); ctx.restore();
      var halo = ctx.createRadialGradient(p[0], p[1], 0, p[0], p[1], cell * 0.75);
      halo.addColorStop(0, 'rgba(255,216,74,' + (0.38 + 0.12 * Math.sin(t * 4 + n)) + ')'); halo.addColorStop(1, 'rgba(255,216,74,0)');
      ctx.fillStyle = halo; ctx.beginPath(); ctx.arc(p[0], p[1], cell * 0.75, 0, 6.283); ctx.fill();
      folder(ctx, p[0], p[1] + bob, cell * (0.66 + 0.04 * Math.sin(t * 4 + n)), true);
    }
    // gates
    for (var k = 0; k < gates.length; k++) {
      var G = gates[k], q = cxy(G.cell), s = cell * 0.5;
      if (G.open) {
        G.anim = Math.min(1, G.anim + 0.04);
        ctx.save(); ctx.globalAlpha = 0.25 + 0.75 * (1 - G.anim); ctx.strokeStyle = '#3dffa2'; ctx.lineWidth = 1.5; ctx.setLineDash([3, 3]);
        ctx.strokeRect(q[0] - s * 0.8, q[1] - s * 0.8, s * 1.6, s * 1.6); ctx.restore();
        if (G.anim < 1) { ctx.save(); ctx.globalAlpha = 1 - G.anim; ctx.strokeStyle = '#ff3df2'; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(q[0], q[1], s * (1 + G.anim * 2.5), 0, 6.283); ctx.stroke(); ctx.restore(); }
      } else {
        var pulse = 0.5 + 0.5 * Math.sin(t * 5 + k);
        ctx.save(); ctx.shadowColor = '#ff3df2'; ctx.shadowBlur = cell * (0.3 + 0.5 * pulse);
        ctx.fillStyle = 'rgba(255,61,242,' + (0.18 + 0.15 * pulse) + ')'; ctx.strokeStyle = '#ff3df2'; ctx.lineWidth = 2;
        rr(ctx, q[0] - s * 0.86, q[1] - s * 0.86, s * 1.72, s * 1.72, s * 0.25); ctx.fill(); ctx.stroke();
        ctx.shadowBlur = 0; ctx.strokeStyle = 'rgba(255,190,250,0.75)'; ctx.lineWidth = Math.max(1, cell * 0.05); ctx.beginPath();
        for (var b = -1; b <= 1; b++) { ctx.moveTo(q[0] + b * s * 0.45, q[1] - s * 0.7); ctx.lineTo(q[0] + b * s * 0.45, q[1] + s * 0.7); }
        ctx.stroke(); ctx.restore();
        var miss = notes.some(function (nn) { return !nn.read && (nn.seg === G.n || G.n === NG - 1); });
        if (miss) { folder(ctx, q[0] + s * 0.78, q[1] - s * 0.78, cell * 0.42, false); }
        var lab = (k === gates.length - 1) ? '450' : String(k + 1);
        ctx.save(); ctx.fillStyle = '#fff'; ctx.font = '900 ' + Math.max(7, cell * (lab.length > 1 ? 0.24 : 0.36)) + 'px Orbitron, sans-serif';
        ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.shadowColor = '#ff3df2'; ctx.shadowBlur = 6; ctx.fillText(lab, q[0], q[1] + 1); ctx.restore();
      }
    }
    // particles
    for (var pi = particles.length - 1; pi >= 0; pi--) {
      var P = particles[pi]; P.life -= 0.025; if (P.life <= 0) { particles.splice(pi, 1); continue; }
      P.x += P.vx; P.y += P.vy; P.vx *= 0.96; P.vy *= 0.96;
      ctx.fillStyle = 'rgba(' + P.c + ',' + P.life + ')'; ctx.beginPath(); ctx.arc(P.x, P.y, P.r * P.life, 0, 6.283); ctx.fill();
    }
    // player
    var px = ox + (pl.x + 0.5) * cell + pl.shx, py = oy + (pl.y + 0.5) * cell + pl.shy;
    var R = cell * 0.3;
    var grd = ctx.createRadialGradient(px, py, 0, px, py, R * 2.4);
    grd.addColorStop(0, 'rgba(255,255,255,0.95)'); grd.addColorStop(0.25, 'rgba(40,231,255,0.85)'); grd.addColorStop(1, 'rgba(40,231,255,0)');
    ctx.fillStyle = grd; ctx.beginPath(); ctx.arc(px, py, R * 2.4, 0, 6.283); ctx.fill();
    ctx.fillStyle = '#fff'; ctx.beginPath(); ctx.arc(px, py, R * 0.62, 0, 6.283); ctx.fill();
    bolt(ctx, px, py, R * 1.05, '#0a7f9a');
    pl.shx *= 0.8; pl.shy *= 0.8;
  }
  function burst(i, color, n) {
    var p = cxy(i);
    for (var k = 0; k < (n || 24); k++) { var a = Math.random() * 6.283, sp = (0.5 + Math.random() * 2.2) * cell / 18; particles.push({ x: p[0], y: p[1], vx: Math.cos(a) * sp, vy: Math.sin(a) * sp, r: cell * (0.06 + Math.random() * 0.08), life: 1, c: color }); }
  }

  /* ---------- player & movement ---------- */
  var pl = { c: 0, x: 0, y: 0, fx: 0, fy: 0, tx: 0, ty: 0, t0: 0, moving: false, dur: 105, shx: 0, shy: 0 };
  var queue = [], runDir = null, held = null, locked = true;
  function placePlayer(i) { pl.c = i; pl.x = pl.tx = i % cols; pl.y = pl.ty = (i / cols) | 0; pl.moving = false; }
  function canStep(i, d) { return !(grid[i] & DIRS[d][2]); }
  function stepTo(n) {
    pl.fx = pl.x; pl.fy = pl.y; pl.tx = n % cols; pl.ty = (n / cols) | 0; pl.t0 = performance.now(); pl.moving = true; pl.target = n;
  }
  function tryDir(d) {
    if (locked || pl.moving) return false;
    if (!canStep(pl.c, d)) { bump(d); return false; }
    var D = DIRS[d], n = pl.c + D[1] * cols + D[0];
    if (closedGate(n)) { runDir = null; queue = []; hitGate(gateAt(n)); return false; }
    if (n === exitI && !exitOpen()) { runDir = null; queue = []; if (gates[gates.length - 1].open) lockedMsg(null); return false; }
    stepTo(n); return true;
  }
  function bump(d) { var D = DIRS[d]; pl.shx = D[0] * cell * 0.12; pl.shy = D[1] * cell * 0.12; SFX.bump(); runDir = null; }
  function stepPlayer(now) {
    if (!pl.moving) return;
    var k = Math.min(1, (now - pl.t0) / pl.dur), e = k < 0.5 ? 2 * k * k : 1 - Math.pow(-2 * k + 2, 2) / 2;
    pl.x = pl.fx + (pl.tx - pl.fx) * e; pl.y = pl.fy + (pl.ty - pl.fy) * e;
    if (k >= 1) { pl.moving = false; arrive(pl.target); }
  }
  function arrive(i) {
    var cameFrom = pl.c; pl.c = i; visited[i] = 1; SFX.step();
    if (i === exitI) { finish(); return; }
    var nt = noteAt(i);
    if (nt) { queue = []; runDir = null; held = null; openNote(nt); return; }
    if (queue.length) {
      var n = queue.shift();
      if (closedGate(n)) { queue = []; hitGate(gateAt(n)); return; }
      if (n === exitI && !exitOpen()) { queue = []; if (gates[gates.length - 1].open) lockedMsg(null); return; }
      stepTo(n); return;
    }
    if (runDir) {
      var opens = neighbors(i, grid);
      if (opens.length === 2 && !nt) {
        var nxt = opens[0] === cameFrom ? opens[1] : opens[0];
        var d = dirTo(i, nxt); runDir = d;
        if (tryDir(d)) return;
      }
      runDir = null;
    }
    if (held) tryDir(held);
  }
  function dirTo(a, b) { var dx = (b % cols) - (a % cols), dy = ((b / cols) | 0) - ((a / cols) | 0); return dx === 1 ? 'E' : dx === -1 ? 'W' : dy === 1 ? 'S' : 'N'; }
  function exitOpen() { return gates[gates.length - 1].open && notesLeft() === 0; }
  function hitGate(G) {
    if (!G) return;
    if (missingFor(G) > 0) { lockedMsg(G); return; }
    openQuiz(G);
  }
  var lockT = 0;
  function lockedMsg(G) {
    var now = performance.now(); if (now - lockT < 900) return; lockT = now;
    var left = notesLeft(), txt;
    if (G && G.n < NG - 1) txt = C.NOTES_GATE_LOCKED || '';
    else txt = (left === 1 ? (C.NOTES_MISSING_ONE || '') : (C.NOTES_MISSING_MANY || '')).replace('{X}', left);
    SFX.wrong(); pl.shx = (Math.random() - 0.5) * cell * 0.2;
    showToast('<span class="lockmsg">' + esc(txt) + '</span><span class="lockcount">📁 ' + (NM - left) + '/' + NM + '</span>', 'lock');
    var chip = $('#notes-chip'); chip.classList.remove('nudge'); void chip.offsetWidth; chip.classList.add('nudge');
    hintOn = true; hintFrom = -1; updateHint(true);
  }
  /* nearest unread file reachable right now (closed gates block) */
  function updateHint(force) {
    if (!hintOn) { hintPath = null; return; }
    if (!force && hintFrom === pl.c) return;
    hintFrom = pl.c;
    var prev = new Int32Array(cols * rows).fill(-1), q = [pl.c], h = 0, hit = -1; prev[pl.c] = pl.c;
    while (h < q.length) {
      var c = q[h++]; var nt = noteAt(c); if (nt && c !== pl.c) { hit = c; break; }
      var nb = neighbors(c, grid);
      for (var j = 0; j < nb.length; j++) { var n = nb[j]; if (prev[n] !== -1 || closedGate(n) || n === exitI) continue; prev[n] = c; q.push(n); }
    }
    if (hit < 0) { hintPath = null; return; }
    var p = [hit]; while (p[p.length - 1] !== pl.c) p.push(prev[p[p.length - 1]]);
    hintPath = p.reverse();
  }
  function progress() { lastProgress = performance.now(); hintOn = false; hintPath = null; hintToastShown = false; }
  function run(d) { if (locked) return; queue = []; runDir = d; if (!pl.moving) { if (!tryDir(d)) runDir = null; } }
  function goTo(target) {
    if (locked || target === pl.c) return;
    var p = bfs(pl.c, target, function (n) { return closedGate(n) || (n === exitI && !exitOpen()); });
    if (!p) { SFX.bump(); return; }
    p.shift(); runDir = null;
    if (!p.length) return;
    queue = p;
    if (!pl.moving) {
      var n = queue.shift();
      if (closedGate(n)) { queue = []; hitGate(gateAt(n)); return; }
      if (n === exitI && !exitOpen()) { queue = []; lockedMsg(null); return; }
      stepTo(n);
    }
  }

  /* input: keyboard */
  var KEYMAP = { ArrowUp: 'N', ArrowDown: 'S', ArrowLeft: 'W', ArrowRight: 'E', w: 'N', s: 'S', a: 'W', d: 'E', W: 'N', S: 'S', A: 'W', D: 'E', 'ו': 'N', 'ד': 'S', 'ש': 'W', 'ג': 'E' };
  var keyCodeMap = { KeyW: 'N', KeyS: 'S', KeyA: 'W', KeyD: 'E' };
  window.addEventListener('keydown', function (ev) {
    var d = KEYMAP[ev.key] || keyCodeMap[ev.code];
    if (!d) { if ((ev.key === 'Enter' || ev.key === ' ') && !$('#intro').classList.contains('hidden') && document.activeElement !== $('#start')) { ev.preventDefault(); startGame(); } return; }
    if (!$('#quiz').classList.contains('hidden')) return;
    if (!$('#note').classList.contains('hidden')) return;
    ev.preventDefault();
    if (ev.repeat) return;
    held = d; queue = []; runDir = null;
    if (!pl.moving) tryDir(d);
  });
  window.addEventListener('keyup', function (ev) { var d = KEYMAP[ev.key] || keyCodeMap[ev.code]; if (d && held === d) held = null; });
  window.addEventListener('blur', function () { held = null; });

  /* input: d-pad (tap = step, hold = repeat) */
  Array.prototype.forEach.call(document.querySelectorAll('.dir'), function (b) {
    var d = b.getAttribute('data-dir');
    b.addEventListener('pointerdown', function (ev) { ev.preventDefault(); ac(); b.classList.add('held'); held = d; queue = []; runDir = null; if (!pl.moving) tryDir(d); try { b.setPointerCapture(ev.pointerId); } catch (e) {} });
    var up = function () { b.classList.remove('held'); if (held === d) held = null; };
    b.addEventListener('pointerup', up); b.addEventListener('pointercancel', up); b.addEventListener('lostpointercapture', up);
    b.addEventListener('contextmenu', function (ev) { ev.preventDefault(); });
  });

  /* input: swipe / tap on the maze */
  var sw = null;
  cv.addEventListener('pointerdown', function (ev) { ev.preventDefault(); ac(); sw = { x: ev.clientX, y: ev.clientY, t: performance.now(), id: ev.pointerId }; try { cv.setPointerCapture(ev.pointerId); } catch (e) {} });
  cv.addEventListener('pointermove', function (ev) {
    if (!sw || sw.id !== ev.pointerId) return;
    var dx = ev.clientX - sw.x, dy = ev.clientY - sw.y;
    if (Math.abs(dx) > 26 || Math.abs(dy) > 26) {
      var d = Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? 'E' : 'W') : (dy > 0 ? 'S' : 'N');
      run(d); sw.x = ev.clientX; sw.y = ev.clientY; sw.swiped = true;
    }
  });
  cv.addEventListener('pointerup', function (ev) {
    if (!sw) return; var s = sw; sw = null;
    if (s.swiped) return;
    var r = cv.getBoundingClientRect(), x = ev.clientX - r.left - ox, y = ev.clientY - r.top - oy;
    var cx = Math.floor(x / cell), cy = Math.floor(y / cell);
    if (cx < 0 || cy < 0 || cx >= cols || cy >= rows) return;
    goTo(cy * cols + cx);
  });
  cv.addEventListener('pointercancel', function () { sw = null; });

  /* ---------- voltage meter (SVG) ---------- */
  var NS = 'http://www.w3.org/2000/svg', svg = $('#gauge'), needle, valArc, CX = 100, CY = 104, RAD = 82;
  function el(n, a) { var e = document.createElementNS(NS, n); for (var k in a) e.setAttribute(k, a[k]); return e; }
  function pol(v, r) { var a = Math.PI * (1 - v / VMAX); return [CX + r * Math.cos(a), CY - r * Math.sin(a)]; }
  function arcD(v0, v1, r) { var a = pol(v0, r), b = pol(v1, r); return 'M' + a[0].toFixed(2) + ' ' + a[1].toFixed(2) + ' A' + r + ' ' + r + ' 0 0 1 ' + b[0].toFixed(2) + ' ' + b[1].toFixed(2); }
  function buildGauge() {
    var defs = el('defs', {});
    var lg = el('linearGradient', { id: 'vg', x1: '0', y1: '0', x2: '1', y2: '0' });
    [['0', '#28e7ff'], ['0.6', '#7b3cff'], ['0.67', '#ff9a3c'], ['0.95', '#ff3b5c'], ['1', '#ff3b5c']].forEach(function (s) { lg.appendChild(el('stop', { offset: s[0], 'stop-color': s[1] })); });
    var fl = el('filter', { id: 'glow', x: '-30%', y: '-30%', width: '160%', height: '160%' });
    fl.appendChild(el('feGaussianBlur', { stdDeviation: '2.4', result: 'b' }));
    var mg = el('feMerge', {}); mg.appendChild(el('feMergeNode', { in: 'b' })); mg.appendChild(el('feMergeNode', { in: 'SourceGraphic' })); fl.appendChild(mg);
    defs.appendChild(lg); defs.appendChild(fl); svg.appendChild(defs);
    svg.appendChild(el('path', { d: arcD(0, VMAX, RAD), stroke: 'rgba(255,255,255,0.09)', 'stroke-width': '12', fill: 'none', 'stroke-linecap': 'round' }));
    svg.appendChild(el('path', { d: arcD(300, 435, RAD + 10), stroke: '#ff9a3c', 'stroke-width': '2.5', fill: 'none', opacity: '0.8' }));
    svg.appendChild(el('path', { d: arcD(435, VMAX, RAD + 10), stroke: '#ff3b5c', 'stroke-width': '3.5', fill: 'none' }));
    valArc = el('path', { d: arcD(0, VMAX, RAD), stroke: 'url(#vg)', 'stroke-width': '12', fill: 'none', 'stroke-linecap': 'round', filter: 'url(#glow)', pathLength: '100', 'stroke-dasharray': '0 100' });
    svg.appendChild(valArc);
    for (var s = 1; s <= 30; s++) {
      var v = s * 15, major = s % 5 === 0, a = pol(v, RAD - 9), b = pol(v, RAD - (major ? 18 : 13));
      svg.appendChild(el('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], stroke: v >= 435 ? '#ff3b5c' : v >= 300 ? '#ff9a3c' : 'rgba(189,248,255,0.75)', 'stroke-width': major ? '2' : '1' }));
    }
    function lbl(v, txt, r, size, color) { var p = pol(v, r); var t = el('text', { x: p[0], y: p[1], fill: color, 'font-size': size, 'text-anchor': 'middle', 'dominant-baseline': 'middle', 'font-family': 'Orbitron, sans-serif', 'font-weight': '700' }); t.textContent = txt; svg.appendChild(t); }
    lbl(15, '15', RAD - 27, 8, '#a6a9d6'); lbl(150, '150', RAD - 27, 8, '#a6a9d6'); lbl(300, '300', RAD - 27, 8, '#ff9a3c'); lbl(450, '450', RAD - 27, 8, '#ff3b5c');
    var tx = el('text', { x: CX + RAD + 4, y: CY + 12, fill: '#ff3b5c', 'font-size': '9', 'text-anchor': 'middle', 'font-family': 'Orbitron, sans-serif', 'font-weight': '900' }); tx.textContent = 'XXX'; svg.appendChild(tx);
    needle = el('g', {});
    needle.appendChild(el('polygon', { points: (CX - RAD + 14) + ',' + CY + ' ' + CX + ',' + (CY - 3.2) + ' ' + (CX + 8) + ',' + CY + ' ' + CX + ',' + (CY + 3.2), fill: '#ffffff', filter: 'url(#glow)' }));
    svg.appendChild(needle);
    svg.appendChild(el('circle', { cx: CX, cy: CY, r: '6', fill: '#ff3df2', filter: 'url(#glow)' }));
    svg.appendChild(el('circle', { cx: CX, cy: CY, r: '2.5', fill: '#fff' }));
    var leds = $('#leds'); for (var i = 0; i < 30; i++) leds.appendChild(document.createElement('i'));
  }
  var volt = 0, voltShown = 0, voltAnim = null;
  function setVolt(v) {
    volt = v; var from = voltShown, t0 = performance.now(), dur = 1100;
    if (voltAnim) cancelAnimationFrame(voltAnim);
    (function tick(now) {
      var k = Math.min(1, (now - t0) / dur), e = 1 - Math.pow(1 - k, 3);
      var cur = from + (v - from) * e + (k < 1 ? Math.sin(k * 30) * 6 * (1 - k) : 0);
      renderVolt(Math.max(0, Math.min(VMAX, cur)), k >= 1 ? v : Math.round(from + (v - from) * e));
      if (k < 1) voltAnim = requestAnimationFrame(tick); else voltShown = v;
    })(t0);
  }
  function renderVolt(cur, num) {
    needle.setAttribute('transform', 'rotate(' + (cur / VMAX * 180).toFixed(2) + ' ' + CX + ' ' + CY + ')');
    valArc.setAttribute('stroke-dasharray', (cur / VMAX * 100).toFixed(2) + ' 100');
    $('#volt').textContent = num;
    var ro = $('.readout'); ro.classList.toggle('hot', num >= 300 && num < 435); ro.classList.toggle('max', num >= 435);
    var leds = $('#leds').children, on = Math.round(num / 15);
    for (var i = 0; i < leds.length; i++) { leds[i].className = i < on ? ('on' + ((i + 1) * 15 >= 435 ? ' max' : (i + 1) * 15 >= 300 ? ' hot' : '')) : ''; }
  }
  function setStatus() {
    var opened = gates.filter(function (g) { return g.open; }).length, L = C.LEARNER || [];
    var idx = Math.min(L.length - 1, Math.round(opened * (L.length - 1) / NG));
    $('#status').textContent = L[idx] || '';
    var dots = $('#gates').children;
    for (var i = 0; i < dots.length; i++) dots[i].classList.toggle('on', !!(gates[i] && gates[i].open));
  }

  /* ---------- quiz ---------- */
  var curGate = null, prodI = 0;
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]; }); }
  function shuffle(a) { a = a.slice(); for (var i = a.length - 1; i > 0; i--) { var j = (Math.random() * (i + 1)) | 0, t = a[i]; a[i] = a[j]; a[j] = t; } return a; }
  function buildQuestion(G) {
    var def = GATES[G.n];
    if (def.type === 'factor') {
      var F = C.FACTORS || [], right = F[(Math.random() * F.length) | 0];
      var others = shuffle(F.filter(function (f) { return f !== right; })).slice(0, 3);
      var opts = [{ t: right.name, ok: true }].concat(others.map(function (f) { return { t: f.name, why: '"' + f.name + '" זה: ' + f.def }; }));
      return { title: def.title, q: def.q, def: right.def, options: shuffle(opts), explain: [right.name + ': ' + right.def] };
    }
    return { title: def.title, q: def.q, options: def.keepOrder ? def.options.slice() : shuffle(def.options), explain: def.explain || [] };
  }
  function openQuiz(G) {
    if (!G) return;
    held = null; queue = []; runDir = null; locked = true; curGate = G;
    var Q = buildQuestion(G); curGate.q = Q;
    $('#q-title').textContent = Q.title;
    $('#q-volt').textContent = Math.round((G.n + 1) * VMAX / NG) + 'V';
    $('#q-text').innerHTML = (Q.def ? '<span class="def">' + esc(Q.def) + '</span>' : '') + esc(Q.q);
    var box = $('#opts'); box.innerHTML = '';
    var short = Q.options.every(function (o) { return o.t.length <= 4; });
    box.className = 'opts' + (short ? ' short' : '');
    Q.options.forEach(function (o, i) {
      var b = document.createElement('button'); b.type = 'button'; b.className = 'opt'; b.textContent = o.t; b.setAttribute('data-i', i);
      b.addEventListener('click', function () { answer(i, b); });
      box.appendChild(b);
    });
    $('#feedback').innerHTML = ''; $('#q-next').classList.add('hidden');
    $('#quiz').classList.remove('hidden');
    $('#quizcard').scrollTop = 0;
    SFX.zap();
  }
  function answer(i, b) {
    var Q = curGate.q, o = Q.options[i];
    if (o.ok) {
      SFX.right();
      Array.prototype.forEach.call(document.querySelectorAll('.opt'), function (x) { x.disabled = true; if (x !== b) x.classList.add('dim'); });
      b.classList.add('good');
      $('#feedback').innerHTML = '<div class="yes">✔ נכון! השער נפתח.</div><blockquote>' + Q.explain.map(function (s) { return '<p>' + esc(s) + '</p>'; }).join('') + '<div class="src">מתוך הסיכום</div></blockquote>';
      var nx = $('#q-next'); nx.textContent = (curGate.n === NG - 1) ? 'למתג האחרון ⚡' : 'פתחו את השער ⚡'; nx.classList.remove('hidden');
      try { nx.focus({ preventScroll: true }); } catch (e) {}
      setTimeout(function () { var c = $('#quizcard'); c.scrollTop = c.scrollHeight; }, 30);
    } else {
      SFX.wrong();
      b.classList.add('bad'); b.disabled = true;
      $('#feedback').innerHTML = '<div class="no">✖ לא בדיוק. ' + esc(o.why || 'נסו שוב.') + '</div><div class="src">נסו תשובה אחרת 🙂</div>';
    }
  }
  function closeQuiz() {
    var G = curGate; if (!G) return;
    $('#quiz').classList.add('hidden');
    G.open = true; G.anim = 0; curGate = null;
    SFX.gate(); burst(G.cell, '255,61,242', 30); burst(G.cell, '40,231,255', 18);
    var opened = gates.filter(function (g) { return g.open; }).length;
    setVolt(Math.round(opened * VMAX / NG)); setStatus();
    progress();
    if (opened < NG) { var P = C.PRODS || []; if (P.length) showProd(P[prodI++ % P.length]); }
    else showProd(notesLeft() ? 'עוד לא. חסרים תיקי מחקר.' : 'המתג האחרון לפניכם. XXX');
    locked = false;
    tryDir(dirTo(pl.c, G.cell));
  }
  var prodT = null, toastT = null;
  function showProd(txt) { var p = $('#prod'); p.innerHTML = '🥼 החוקר: <b>"' + esc(txt) + '"</b>'; p.classList.add('show'); clearTimeout(prodT); prodT = setTimeout(function () { p.classList.remove('show'); }, 2600); }
  function showToast(html, kind) { var t = $('#toast'); t.innerHTML = html; t.className = 'toast show' + (kind ? ' ' + kind : ''); clearTimeout(toastT); toastT = setTimeout(function () { t.classList.remove('show'); }, kind === 'lock' ? 5000 : 6500); }

  /* ---------- research files (notes) ---------- */
  var curNote = null, readyT = null;
  function updateChip(pulse) {
    var c = $('#notes-chip'), done = NM - notesLeft();
    c.innerHTML = '<span class="ic">📁</span> תיקי מחקר <b>' + done + '/' + NM + '</b>' + (done === NM && NM ? ' <span class="ok">✓</span>' : '');
    c.classList.toggle('all', done === NM && NM > 0);
    c.classList.toggle('hidden', !NM);
    if (pulse) { c.classList.remove('pop'); void c.offsetWidth; c.classList.add('pop'); }
  }
  function openNote(nt) {
    locked = true; held = null; queue = []; runDir = null; curNote = nt; nt.taken = true;
    SFX.note(); burst(nt.cell, '255,216,74', 22);
    $('#n-count').textContent = 'תיק מחקר ' + (nt.k + 1) + ' מתוך ' + NM;
    $('#n-src').textContent = nt.src || '';
    $('#n-src').classList.toggle('hidden', !nt.src);
    $('#n-text').textContent = nt.text;
    var b = $('#n-ok'); b.disabled = true; b.classList.add('wait');
    $('#note').classList.remove('hidden');
    clearTimeout(readyT);
    readyT = setTimeout(function () { b.disabled = false; b.classList.remove('wait'); try { b.focus({ preventScroll: true }); } catch (e) {} }, 1300);
  }
  function closeNote() {
    var nt = curNote; if (!nt || $('#n-ok').disabled) return;
    nt.read = true; curNote = null;
    $('#note').classList.add('hidden');
    SFX.right(); burst(nt.cell, '255,216,74', 26);
    updateChip(true); progress();
    var left = notesLeft();
    showToast(left ? ('📁 נאסף! עוד ' + left + ' ' + (left === 1 ? 'תיק' : 'תיקים') + ' במבוך') : '📁 אספתם את כל תיקי המחקר! המתג האחרון יחכה לכם ⚡');
    locked = false;
  }
  function fillSummary() {
    var box = $('#e-notes');
    box.innerHTML = notes.map(function (n) { return '<li><div class="ns">' + esc(n.src) + '</div><p>' + esc(n.text) + '</p></li>'; }).join('');
  }

  /* ---------- start / end ---------- */
  function startGame() {
    ac();
    $('#intro').classList.add('hidden'); $('#end').classList.add('hidden');
    buildMaze(); layout(); placePlayer(startI);
    gates.forEach(function (g) { g.open = false; });
    voltShown = 0; renderVolt(0, 0); setStatus();
    var dots = $('#gates'); dots.innerHTML = '';
    for (var i = 0; i < NG; i++) { var d = document.createElement('span'); d.className = 'gate-dot'; d.textContent = i === NG - 1 ? 'X' : (i + 1); dots.appendChild(d); }
    particles = []; locked = false; prodI = 0;
    updateChip(false); $('#note').classList.add('hidden'); $('#e-notes').classList.add('hidden'); curNote = null;
    showToast(NM ? 'הגיעו אל <b>XXX · 450V</b>. בדרך: אספו את כל <b>תיקי המחקר 📁</b> וענו נכון בכל שער ⚡' : 'הגיעו אל <b>XXX · 450V</b> בפינה. כל שער ורוד נפתח בתשובה נכונה ⚡');
    try { cv.focus(); window.focus(); } catch (e) {}
  }
  function finish() {
    locked = true; held = null; SFX.win(); burst(exitI, '255,59,92', 50); burst(exitI, '255,255,255', 20);
    setVolt(VMAX);
    setTimeout(function () {
      $('#e-hint').classList.add('hidden');
      fillSummary(); $('#e-notes').classList.add('hidden'); $('#e-sum').classList.toggle('hidden', !NM);
      $('#end').classList.remove('hidden');
      try { if (inFrame && window.parent) window.parent.postMessage({ type: 'milgram-maze-complete', code: String(C.FINAL_CODE) }, '*'); } catch (e) {}
    }, 900);
  }
  function backToRoom() {
    var h = $('#e-hint');
    if (!inFrame && C.RETURN_URL) { window.location.href = C.RETURN_URL; return; }
    if (!inFrame) { try { window.close(); } catch (e) {} }
    h.innerHTML = esc(C.RETURN_HINT || '') + (inFrame ? '' : '<br><small>(אפשר לסגור את הלשונית הזו ולחזור ללשונית של חדר הבריחה)</small>');
    h.classList.remove('hidden');
  }

  /* ---------- texts from config ---------- */
  function fillTexts() {
    if (C.TITLE) { $('#t-title').textContent = C.TITLE; $('#i-title').textContent = C.TITLE; }
    if (C.SUBTITLE) $('#t-sub').textContent = C.SUBTITLE;
    var intro = (C.INTRO || []).slice(); if (NM && C.NOTES_INTRO) intro.splice(Math.max(0, intro.length - 1), 0, C.NOTES_INTRO.replace('{N}', NM));
    $('#i-text').innerHTML = intro.map(function (p, i) { return '<p' + (p.indexOf('📁') === 0 ? ' class="notes-intro"' : '') + '>' + esc(p) + '</p>'; }).join('');
    $('#e-title').textContent = C.END_TITLE || '';
    $('#e-note').textContent = C.CODE_NOTE || '';
    $('#e-label').textContent = C.CODE_LABEL || '';
    $('#e-code').textContent = String(C.FINAL_CODE == null ? '' : C.FINAL_CODE);
    $('#e-refl').textContent = C.END_REFLECTION || '';
    $('#back').textContent = C.RETURN_TEXT || 'חזרו לחדר הבריחה';
  }

  /* ---------- boot ---------- */
  fillTexts(); buildGauge(); setMuteIcon();
  $('#mute').addEventListener('click', function () { muted = !muted; pset('muted', muted ? '1' : '0'); setMuteIcon(); if (!muted) { ac(); SFX.right(); } });
  $('#start').addEventListener('click', startGame);
  $('#q-next').addEventListener('click', closeQuiz);
  $('#back').addEventListener('click', backToRoom);
  $('#again').addEventListener('click', startGame);
  $('#n-ok').addEventListener('click', closeNote);
  $('#e-sum').addEventListener('click', function () { var b = $('#e-notes'); b.classList.toggle('hidden'); if (!b.classList.contains('hidden')) setTimeout(function () { b.scrollIntoView({ block: 'nearest', behavior: 'smooth' }); }, 30); });
  // a maze in the background behind the intro
  buildMaze(); layout(); placePlayer(startI); renderVolt(0, 0); setStatus(); updateChip(false);
  (function () { var dots = $('#gates'); for (var i = 0; i < NG; i++) { var d = document.createElement('span'); d.className = 'gate-dot'; d.textContent = i === NG - 1 ? 'X' : (i + 1); dots.appendChild(d); } })();
  var ro = window.ResizeObserver ? new ResizeObserver(function () { layout(); }) : null;
  if (ro) ro.observe($('#mazewrap')); else window.addEventListener('resize', layout);
  requestAnimationFrame(frame);
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(function () { drawLayer(); });

  /* test hook (read-only helpers for automated checks) */
  window.__maze = {
    state: function () { return { cols: cols, rows: rows, player: pl.c, moving: pl.moving, exit: exitI, gates: gates.map(function (g) { return { cell: g.cell, open: g.open }; }), volt: volt, locked: locked, quizOpen: !$('#quiz').classList.contains('hidden'), endOpen: !$('#end').classList.contains('hidden') }; },
    route: function () { var p = bfs(pl.c, exitI); var out = []; for (var i = 1; p && i < p.length; i++) out.push(dirTo(p[i - 1], p[i])); return out; },
    sampleGate: function (n) { return buildQuestion({ n: n }).explain[0].slice(0, 20); },
    correctIndex: function () { if (!curGate) return -1; for (var i = 0; i < curGate.q.options.length; i++) if (curGate.q.options[i].ok) return i; return -1; },
    notes: function () { return notes.map(function (n) { return { cell: n.cell, seg: n.seg, taken: n.taken, read: n.read, src: n.src, text: n.text }; }); },
    noteOpen: function () { return !$('#note').classList.contains('hidden'); },
    hint: function () { return { on: hintOn, path: hintPath ? hintPath.length : 0 }; },
    routeTo: function (target) { var p = bfs(pl.c, target, function (n) { return closedGate(n) || n === exitI; }); var out = []; for (var i = 1; p && i < p.length; i++) out.push(dirTo(p[i - 1], p[i])); return p ? out : null; },
    regen: function () { buildMaze(); layout(); placePlayer(startI); return { L: path.length, deps: notes.map(function (n) { return n.dep; }) }; },
    gateCells: function () { return gates.map(function (g) { return g.cell; }); },
    cellCenter: function (i) { var p = cxy(i), r = cv.getBoundingClientRect(); return [r.left + p[0], r.top + p[1]]; }
  };
})();
