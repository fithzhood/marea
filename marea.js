/* Marea — disequazioni di secondo grado risolte alzando il mare */
(function () {
  'use strict';

  /* ═══════════════ utilità ═══════════════ */
  var $ = function (s) { return document.querySelector(s); };
  var MINUS = '−';

  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function lerp(a, b, t) { return a + (b - a) * t; }
  function easeOut(t) { return 1 - Math.pow(1 - t, 3); }
  function easeInOut(t) { return t < .5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2; }
  function randInt(a, b) { return a + Math.floor(Math.random() * (b - a + 1)); }
  function pick(arr) { return arr[Math.floor(Math.random() * arr.length)]; }
  function buzz(ms) { try { if (navigator.vibrate) navigator.vibrate(ms); } catch (e) {} }

  function hex(c) {
    return [parseInt(c.substr(1, 2), 16), parseInt(c.substr(3, 2), 16), parseInt(c.substr(5, 2), 16)];
  }
  function mixColor(c1, c2, t) {
    var a = hex(c1), b = hex(c2);
    return 'rgb(' + Math.round(lerp(a[0], b[0], t)) + ',' + Math.round(lerp(a[1], b[1], t)) + ',' + Math.round(lerp(a[2], b[2], t)) + ')';
  }

  /* numeri all'italiana: intero, frazione esatta, oppure decimale con virgola */
  function fmtNum(v) {
    if (!isFinite(v)) return v > 0 ? '+∞' : MINUS + '∞';
    if (Math.abs(v - Math.round(v)) < 1e-9) return String(Math.round(v)).replace('-', MINUS);
    for (var d = 2; d <= 16; d++) {
      var n = v * d;
      if (Math.abs(n - Math.round(n)) < 1e-9) {
        n = Math.round(n);
        var sg = n < 0 ? MINUS : '';
        return sg + Math.abs(n) + '/' + d;
      }
    }
    return v.toFixed(2).replace('-', MINUS).replace('.', ',');
  }
  function isExact(v) {
    if (Math.abs(v - Math.round(v)) < 1e-9) return true;
    for (var d = 2; d <= 16; d++) { var n = v * d; if (Math.abs(n - Math.round(n)) < 1e-9) return true; }
    return false;
  }
  function fmtInt(n) { return String(n).replace('-', MINUS); }

  /* per righello e quota: sempre decimale, mai frazione */
  function fmtDec(v) {
    var a = Math.abs(v);
    var s = v.toFixed(a >= 10 ? 0 : a >= 1 ? 1 : a >= .1 ? 2 : a >= .01 ? 3 : 4);
    if (s.indexOf('.') >= 0) s = s.replace(/0+$/, '').replace(/\.$/, '');
    if (s === '-0') s = '0';
    return s.replace('-', MINUS).replace('.', ',');
  }

  var OPS = ['>', '<', '>=', '<='];
  function opSym(op) { return op === '>' ? '>' : op === '<' ? '<' : op === '>=' ? '≥' : '≤'; }

  function eqString(a, b, c, op) {
    var s = '';
    s += (a === 1 ? '' : a === -1 ? MINUS : fmtInt(a)) + 'x²';
    if (b !== 0) s += (b > 0 ? ' + ' : ' ' + MINUS + ' ') + (Math.abs(b) === 1 ? '' : Math.abs(b)) + 'x';
    if (c !== 0) s += (c > 0 ? ' + ' : ' ' + MINUS + ' ') + Math.abs(c);
    return s + ' <span class="op">' + opSym(op) + '</span> 0';
  }
  function polyString(a, b, c) {
    var s = '';
    s += (a === 1 ? '' : a === -1 ? MINUS : fmtInt(a)) + 'x²';
    if (b !== 0) s += (b > 0 ? ' + ' : ' ' + MINUS + ' ') + (Math.abs(b) === 1 ? '' : Math.abs(b)) + 'x';
    if (c !== 0) s += (c > 0 ? ' + ' : ' ' + MINUS + ' ') + Math.abs(c);
    return s;
  }

  /* ═══════════════ stato ═══════════════ */
  var S = {
    phase: 'setup',           // setup | bend | sea | pick | done
    a: 1, b: -2, c: -3, op: '>',
    D: 0, r1: null, r2: null, nr: 0, xv: 0, yv: 0,
    zones: [], okZones: [], attempts: 0, fish: [], fishMax: 0,
    hero: null, heroes: [], heroT: 0, bubbleT: 0,
    bend: { d: 0, morph: 0, wrong: false, dragging: false, touched: false, busy: false },
    sea: { y: 0, min: 0, max: 0, dragging: false, locked: false, revealed: false, dragY0: 0, dragS0: 0 },
    trees: [],
    t: 0
  };
  var V = { x0: -5, x1: 5, y0: -5, y1: 5 };
  var W = 0, H = 0, UI = 1;   /* UI: quanto ingrandire figure e scritte su schermi grandi */

  var stage = $('#stage'), cv = $('#scene'), ctx = cv.getContext('2d');
  var hintEl = $('#hint'), actionsEl = $('#actions'), calcEl = $('#calc');
  var flashEl = $('#flash'), stripEl = $('#axis-strip');
  var zonesEl = $('#axis-zones'), marksEl = $('#axis-marks');

  function f(x) { return (S.a * x + S.b) * x + S.c; }

  /* ═══════════════ vista ═══════════════ */
  /* La parabola sullo schermo ha SEMPRE la stessa curvatura, qualunque sia a: cambia
     solo il verso e dove cade la quota zero. Non è un grafico in scala fissa, è un
     disegno leggibile — la mappatura resta lineare, quindi radici, segni e righello
     restano veri; a decide solo quanto vale un'unità sull'asse y. */
  function computeView() {
    var a = S.a, absA = Math.abs(a);
    S.xv = -S.b / (2 * a);
    S.yv = f(S.xv);

    /* curvatura di riferimento: radici a 55% della larghezza, vertice a 30% dell'altezza */
    var K = (H * .30) / Math.pow(W * .275, 2);
    var scaleX, scaleY;
    if (S.nr === 1) {
      /* vertice esattamente sulla quota zero: lo zoom verticale non ha vincoli */
      scaleX = W * .1375;
      scaleY = K * scaleX * scaleX / absA;
    } else {
      var gap = (S.nr === 2 ? H * .30 : H * .18);   /* px fra vertice e quota zero */
      scaleY = gap / Math.abs(S.yv);
      scaleX = Math.sqrt(absA * scaleY / K);
    }

    /* altezza della quota zero sullo schermo, scelta per lasciare cielo sopra,
       terra sotto e corsa al mare */
    var zeroPx;
    if (S.nr === 2) zeroPx = a > 0 ? H * .40 : H * .60;
    else if (S.nr === 1) zeroPx = a > 0 ? H * .52 : H * .48;
    else zeroPx = a > 0 ? H * .66 : H * .34;

    var spanX = W / scaleX, spanY = H / scaleY;
    V.x0 = S.xv - (W / 2) / scaleX; V.x1 = V.x0 + spanX;
    V.y0 = -spanY * (H - zeroPx) / H; V.y1 = V.y0 + spanY;

    S.sea.min = V.y0 + spanY * .02;
    S.sea.max = V.y1 - spanY * .06;
    /* il mare parte 22% di schermo sotto lo zero: corsa vera per il dito e, quando la
       parabola guarda in su, già dentro la conca */
    S.sea.start = P2Y(zeroPx + H * .22);
    if (S.phase === 'setup' || S.phase === 'bend') S.sea.y = S.sea.start;
  }

  function X2P(x) { return (x - V.x0) / (V.x1 - V.x0) * W; }
  function Y2P(y) { return H - (y - V.y0) / (V.y1 - V.y0) * H; }
  function P2X(p) { return V.x0 + p / W * (V.x1 - V.x0); }
  function P2Y(p) { return V.y0 + (H - p) / H * (V.y1 - V.y0); }

  /* Profilo del terreno in pixel. Durante la piega la barra non e' una curva a se':
     e' gia' la parabola finale, presa a curvatura ridotta. A piega completa le due
     coincidono esattamente, quindi il passaggio a paesaggio non ha nessuno scatto. */
  function ground(px) {
    var par = Y2P(f(P2X(px)));
    if (S.phase === 'bend' || S.bend.morph < 1) {
      var flat = H * .5;
      var meta = S.bend.wrong ? (2 * flat - par) : par;   /* piega al contrario: specchiata */
      return lerp(flat, meta, clamp(S.bend.morph, 0, 1));
    }
    return par;
  }

  /* ═══════════════ tween minimale ═══════════════ */
  var tweens = [], CLOCK = 0;   /* un solo orologio: così le animazioni si possono anche pilotare a mano */
  function tween(get, set, to, ms, done) {
    var from = get(), t0 = CLOCK;
    tweens.push({ step: function () {
      var p = clamp((CLOCK - t0) / ms, 0, 1);
      set(lerp(from, to, easeInOut(p)));
      if (p >= 1) { if (done) done(); return true; }
      return false;
    } });
  }
  function runTweens() {
    for (var i = tweens.length - 1; i >= 0; i--) if (tweens[i].step()) tweens.splice(i, 1);
  }
  function advance(ms) { CLOCK += ms; S.t = CLOCK / 1000; runTweens(); updateFish(ms / 1000); draw(); }

  /* ═══════════════ disegno ═══════════════ */
  var clouds = [
    { x: .10, y: .16, s: 1.0, v: 7 },
    { x: .55, y: .09, s: .72, v: 4.5 },
    { x: .82, y: .26, s: .85, v: 9 }
  ];

  function drawSky() {
    var g = ctx.createLinearGradient(0, 0, 0, H);
    /* cielo chiaro e luminoso: il mare è verde scuro, così le due masse non si confondono */
    g.addColorStop(0, '#3f9ad6'); g.addColorStop(.5, '#8fcdea'); g.addColorStop(1, '#dcf0f7');
    ctx.fillStyle = g; ctx.fillRect(0, 0, W, H);

    var sx = W * .84, sy = H * .15, r = Math.min(W, H) * .062;
    var gg = ctx.createRadialGradient(sx, sy, r * .3, sx, sy, r * 3.2);
    gg.addColorStop(0, 'rgba(255,236,170,.75)'); gg.addColorStop(1, 'rgba(255,236,170,0)');
    ctx.fillStyle = gg; ctx.beginPath(); ctx.arc(sx, sy, r * 3.2, 0, 6.2832); ctx.fill();
    ctx.fillStyle = '#ffe98a';
    ctx.beginPath(); ctx.arc(sx, sy, r, 0, 6.2832); ctx.fill();

    for (var i = 0; i < clouds.length; i++) {
      var c = clouds[i];
      var x = ((c.x * W + S.t * c.v) % (W + 160)) - 80;
      drawCloud(x, c.y * H, Math.min(W, H) * .055 * c.s);
    }
  }
  function drawCloud(x, y, r) {
    ctx.fillStyle = 'rgba(255,255,255,.82)';
    ctx.beginPath();
    ctx.arc(x, y, r, 0, 6.2832);
    ctx.arc(x + r * .95, y + r * .18, r * .78, 0, 6.2832);
    ctx.arc(x - r * .9, y + r * .22, r * .66, 0, 6.2832);
    ctx.arc(x + r * .12, y + r * .45, r * .72, 0, 6.2832);
    ctx.fill();
  }

  function groundPath() {
    ctx.beginPath();
    ctx.moveTo(-4, ground(-4));
    for (var px = 0; px <= W; px += 3) ctx.lineTo(px, ground(px));
    ctx.lineTo(W + 4, ground(W + 4));
  }

  function drawGround() {
    var m = S.bend.morph;
    /* corpo del terreno */
    if (m > 0) {
      ctx.save(); ctx.globalAlpha = m;
      groundPath();
      ctx.lineTo(W + 4, H + 60); ctx.lineTo(-4, H + 60); ctx.closePath();
      var g = ctx.createLinearGradient(0, Y2P(Math.max(S.yv, 0)) - 40, 0, H);
      g.addColorStop(0, '#7d5f3c'); g.addColorStop(.45, '#63492c'); g.addColorStop(1, '#3f2e1c');
      ctx.fillStyle = g; ctx.fill();
      /* strati, perché la terra non sia una macchia piatta */
      ctx.strokeStyle = 'rgba(0,0,0,.07)'; ctx.lineWidth = 7;
      for (var k = 1; k <= 3; k++) {
        ctx.save(); ctx.translate(0, k * 26);
        groundPath(); ctx.stroke();
        ctx.restore();
      }
      ctx.restore();
    }
    /* crosta: la barra che diventa erba */
    ctx.save();
    ctx.lineJoin = 'round'; ctx.lineCap = 'round';
    groundPath();
    ctx.lineWidth = lerp(13, 11, m);
    ctx.strokeStyle = mixColor('#9aa7b2', '#3f6b2c', m);
    ctx.stroke();
    groundPath();
    ctx.lineWidth = lerp(7, 5, m);
    ctx.strokeStyle = mixColor('#cdd7df', '#7cc255', m);
    ctx.stroke();
    ctx.restore();
  }

  function drawTrees() {
    if (S.bend.morph < .55) return;
    ctx.save(); ctx.globalAlpha = (S.bend.morph - .55) / .45;
    for (var i = 0; i < S.trees.length; i++) {
      var tx = X2P(S.trees[i].x), gy = ground(tx);
      if (gy < -30 || gy > H + 30) continue;
      var s = S.trees[i].s * Math.min(W, H) * .036;
      ctx.fillStyle = '#5a3f26';
      ctx.fillRect(tx - s * .11, gy - s * .95, s * .22, s * .95);
      ctx.fillStyle = '#2f6b2a';
      for (var k = 0; k < 3; k++) {
        var yy = gy - s * (.55 + k * .5), ww = s * (.62 - k * .13);
        ctx.beginPath(); ctx.moveTo(tx, yy - s * .75);
        ctx.lineTo(tx + ww, yy); ctx.lineTo(tx - ww, yy); ctx.closePath(); ctx.fill();
      }
    }
    ctx.restore();
  }

  function waveAt(px) {
    return Math.sin(px * .042 + S.t * 2.1) * 2.1 + Math.sin(px * .019 - S.t * 1.35) * 1.5;
  }

  /* profilo dell'acqua: superficie ondulata sopra, terreno (o fondo schermo) sotto */
  var seaTop = [], seaBot = [];
  function seaProfile() {
    seaTop.length = 0; seaBot.length = 0;
    var base = Y2P(S.sea.y), px;
    for (px = -4; px <= W + 4; px += 4) {
      var ty = base + waveAt(px);
      seaTop.push(ty);
      seaBot.push(Math.max(ty, Math.min(ground(px), H + 60)));
    }
  }
  function waterPath() {
    var px, i = 0;
    ctx.beginPath();
    for (px = -4; px <= W + 4; px += 4, i++) { if (i === 0) ctx.moveTo(px, seaTop[i]); else ctx.lineTo(px, seaTop[i]); }
    i--;
    for (px = px - 4; px >= -4; px -= 4, i--) ctx.lineTo(px, seaBot[i]);
    ctx.closePath();
  }

  function drawSea() {
    if (S.phase === 'bend' || S.phase === 'setup') return;
    seaProfile();
    var base = Y2P(S.sea.y);
    waterPath();
    var g = ctx.createLinearGradient(0, base, 0, H);
    g.addColorStop(0, 'rgba(23,150,150,.93)');
    g.addColorStop(.45, 'rgba(11,97,120,.95)');
    g.addColorStop(1, 'rgba(4,38,58,.98)');
    ctx.fillStyle = g; ctx.fill();

    /* i pesci nuotano ritagliati dentro l'acqua: non possono uscirne mai */
    ctx.save(); waterPath(); ctx.clip(); drawFish(); ctx.restore();

    /* superficie: solo nei tratti dove l'acqua esiste davvero, non sopra la terraferma */
    ctx.beginPath();
    var open = false, px, i = 0;
    for (px = -4; px <= W + 4; px += 4, i++) {
      if (seaBot[i] - seaTop[i] > 1.5) {
        if (!open) { ctx.moveTo(px, seaTop[i]); open = true; } else ctx.lineTo(px, seaTop[i]);
      } else open = false;
    }
    ctx.strokeStyle = 'rgba(222,248,255,.95)'; ctx.lineWidth = 2.4; ctx.stroke();
  }

  /* ═══════════════ pesci ═══════════════ */
  var FISH_COLORS = ['#ff9f43', '#ffd166', '#ff7f9c', '#7fe3ff', '#ffbe6b', '#a8f0b6'];
  function spawnFish() {
    S.fish = [];
    for (var i = 0; i < 9; i++) {
      S.fish.push({
        x: 20 + Math.random() * Math.max(60, W - 40),
        depth: .16 + Math.random() * .68,
        v: (Math.random() < .5 ? -1 : 1) * (11 + Math.random() * 17),
        s: (5.5 + Math.random() * 4) * UI,
        ph: Math.random() * 6.283,
        c: FISH_COLORS[i % FISH_COLORS.length],
        y: null, dry: 0
      });
    }
  }
  /* porta il pesce nel tratto d'acqua più profondo, se ce n'è uno che lo contiene */
  function moveToWater(f, ySurf, pad) {
    var best = -1, bestX = null, x, i;
    for (i = 0; i <= 24; i++) {
      x = 6 + (W - 12) * i / 24;
      var sp = Math.min(ground(x), H + 40) - ySurf;
      if (sp > best) { best = sp; bestX = x; }
    }
    if (bestX != null && best > pad * 2 + 8) {
      f.x = clamp(bestX + (Math.random() - .5) * W * .3, 8, W - 8);
      f.depth = .16 + Math.random() * .68;      /* sparpaglia anche in profondità */
    }
  }

  /* quanta acqua c'è, in pixel quadri: una pozza piccola ospita pochi pesci */
  function waterArea() {
    var n = 0;
    for (var i = 0; i < seaBot.length; i++) n += Math.max(0, seaBot[i] - seaTop[i]);
    return n * 4;
  }

  function updateFish(dt) {
    if (S.phase === 'setup' || S.phase === 'bend') return;
    var ySurf = Y2P(S.sea.y);
    S.fishMax = clamp(Math.round(waterArea() / 4500), 0, S.fish.length);
    for (var i = 0; i < S.fish.length; i++) {
      var f = S.fish[i];
      if (i >= S.fishMax) { f.y = null; continue; }
      f.x += f.v * dt;
      if (f.x < 10 && f.v < 0) f.v = -f.v;
      if (f.x > W - 10 && f.v > 0) f.v = -f.v;
      var pad = f.s * 1.4;
      var space = Math.min(ground(f.x), H + 40) - ySurf;
      if (space < pad * 2 + 4) {        /* qui l'acqua è troppo bassa: fa dietrofront */
        f.v = -f.v; f.x += f.v * dt * 1.5; f.y = null;
        f.dry += dt;
        /* se resta all'asciutto torna dove l'acqua è fonda: succede mentre è invisibile */
        if (f.dry > 1.1) { f.dry = 0; moveToWater(f, ySurf, pad); }
      } else {
        f.y = ySurf + pad + (space - pad * 2) * f.depth;
        f.dry = 0;
      }
    }
  }
  function drawFish() {
    for (var i = 0; i < S.fish.length; i++) {
      var f = S.fish[i];
      if (f.y == null) continue;
      var s = f.s, wag = Math.sin(S.t * 7 + f.ph) * s * .32;
      ctx.save();
      ctx.globalAlpha = .96 - f.depth * .28;
      ctx.translate(f.x, f.y + Math.sin(S.t * 2.2 + f.ph) * 2);
      ctx.scale(f.v < 0 ? -1 : 1, 1);
      ctx.fillStyle = f.c;
      ctx.beginPath(); ctx.ellipse(0, 0, s, s * .55, 0, 0, 6.2832); ctx.fill();
      ctx.beginPath();
      ctx.moveTo(-s * .78, 0);
      ctx.lineTo(-s * 1.5, -s * .5 + wag);
      ctx.lineTo(-s * 1.5, s * .5 + wag);
      ctx.closePath(); ctx.fill();
      ctx.fillStyle = 'rgba(255,255,255,.5)';
      ctx.beginPath(); ctx.ellipse(-s * .05, s * .2, s * .48, s * .16, 0, 0, 6.2832); ctx.fill();
      ctx.fillStyle = '#0b2030';
      ctx.beginPath(); ctx.arc(s * .46, -s * .14, s * .13, 0, 6.2832); ctx.fill();
      ctx.restore();
    }
  }

  /* linea della quota corrente + righello */
  function drawLevel() {
    if (S.phase === 'bend' || S.phase === 'setup') return;
    if (S.sea.locked && !S.sea.auto) return;
    var y = Y2P(S.sea.y);
    ctx.save();
    ctx.setLineDash([7, 6]);
    ctx.strokeStyle = 'rgba(255,255,255,.6)';
    ctx.lineWidth = 1.6;
    ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke();
    ctx.restore();
    if (S.sea.locked) return;
    /* maniglia senza numeri: la quota non si legge, si legge dove finiscono le rive */
    ctx.fillStyle = 'rgba(9,32,50,.88)';
    roundRect(9, y - 14, 30, 28, 9); ctx.fill();
    ctx.strokeStyle = 'rgba(255,255,255,.4)'; ctx.lineWidth = 1; ctx.stroke();
    ctx.fillStyle = '#cfeaff'; ctx.font = '700 15px ' + FONT;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('⇕', 24, y + 1);
  }

  /* ascisse dei punti in cui il livello del mare incontra il profilo del terreno */
  function shoreX() {
    var disc = S.b * S.b - 4 * S.a * (S.c - S.sea.y);
    if (disc < 0) return [];
    var s = Math.sqrt(disc), p = (-S.b - s) / (2 * S.a), q = (-S.b + s) / (2 * S.a);
    return p <= q ? [p, q] : [q, p];
  }



  /* rive, divisori e zone selezionabili */
  function drawZones() {
    if (!S.sea.revealed) return;
    var roots = S.nr === 2 ? [S.r1, S.r2] : S.nr === 1 ? [S.r1] : [];
    var i;
    if (S.phase === 'pick' || S.phase === 'done') {
      var yz = Y2P(0), band = Math.min(H * .16, 90);
      for (i = 0; i < S.zones.length; i++) {
        var z = S.zones[i];
        var xa = isFinite(z.lo) ? X2P(z.lo) : -2, xb = isFinite(z.hi) ? X2P(z.hi) : W + 2;
        var rgb = (S.phase === 'done' && S.okZones.indexOf(i) >= 0) ? '78,192,106' : null;
        /* alone sfumato attorno all'asse: segnala la zona senza tingere il cielo */
        if (rgb) {
          var g2 = ctx.createLinearGradient(0, yz - band, 0, yz + band);
          g2.addColorStop(0, 'rgba(' + rgb + ',0)');
          g2.addColorStop(.5, 'rgba(' + rgb + ',.28)');
          g2.addColorStop(1, 'rgba(' + rgb + ',0)');
          ctx.fillStyle = g2;
          ctx.fillRect(xa, yz - band, xb - xa, band * 2);
          /* barra sottile e spostata sotto il pelo dell'acqua: le onde devono restare in vista */
          ctx.fillStyle = 'rgb(' + rgb + ')';
          ctx.fillRect(xa + 1.5, yz + 4, xb - xa - 3, 4);
        }
      }
    }
    ctx.save();
    ctx.setLineDash([5, 5]); ctx.strokeStyle = 'rgba(255,255,255,.75)'; ctx.lineWidth = 1.4;
    for (i = 0; i < roots.length; i++) {
      var rx = X2P(roots[i]);
      ctx.beginPath(); ctx.moveTo(rx, 0); ctx.lineTo(rx, H); ctx.stroke();
    }
    ctx.restore();
    /* pallini sulla riva */
    var full = (S.op === '>=' || S.op === '<=');
    for (i = 0; i < roots.length; i++) {
      var px = X2P(roots[i]), py = Y2P(0);
      ctx.beginPath(); ctx.arc(px, py, 6.5, 0, 6.2832);
      ctx.fillStyle = full ? '#ffca47' : '#0d2233';
      ctx.fill(); ctx.strokeStyle = '#ffca47'; ctx.lineWidth = 2.5; ctx.stroke();
    }
  }

  /* cartelli piantati dove la parabola incontra l'asse: solo il numero */
  /* Cartelli piantati dove il pelo dell'acqua tocca il terreno. Durante la marea si
     spostano e il numero cambia: quando segnano le soluzioni, il livello e' quello giusto. */
  function drawSigns() {
    var xs, esatto;
    if (S.phase === 'sea' && !S.sea.locked) { xs = shoreX(); esatto = false; }
    else if (S.sea.revealed && S.nr === 2) {
      /* con una radice sola il cartello non aggiunge niente: c'e' gia' il pallino */
      xs = [S.r1, S.r2];
      esatto = true;
    } else return;
    if (!xs.length) return;

    var y0 = Y2P(S.sea.y), i, k;
    ctx.font = '700 ' + (14.5 * UI).toFixed(1) + 'px ' + FONT;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    var pxs = [], labs = [];
    for (i = 0; i < xs.length; i++) {
      pxs.push(X2P(xs[i]));
      labs.push(esatto ? fmtNum(xs[i]) : fmtDec(xs[i]));
    }
    for (i = 0; i < xs.length; i++) {
      var px = pxs[i];
      if (px < -24 || px > W + 24) continue;

      var wp = Math.max(30 * UI, ctx.measureText(labs[i]).width + 18 * UI);
      var plateH = 21 * UI, top = y0 - 12 * UI - plateH;   /* asta corta: il cartello sta sulla riva */
      /* due cartelli vicini: il secondo sale di un piano */
      if (xs.length === 2 && Math.abs(pxs[0] - pxs[1]) < wp + 10 && i === 1) top -= plateH + 7;
      var bx = clamp(px, wp / 2 + 3, W - wp / 2 - 3);
      ctx.strokeStyle = '#6b4f33'; ctx.lineWidth = 3.5; ctx.lineCap = 'butt';
      ctx.beginPath(); ctx.moveTo(px, y0); ctx.lineTo(px, top + plateH - 1); ctx.stroke();
      ctx.fillStyle = '#f7f1e0';
      roundRect(bx - wp / 2, top, wp, plateH, 4); ctx.fill();
      ctx.strokeStyle = '#6b4f33'; ctx.lineWidth = 2; ctx.stroke();
      ctx.fillStyle = '#3a2b1c';
      ctx.fillText(labs[i], bx, top + plateH / 2 + 1);
      ctx.beginPath(); ctx.arc(px, y0, 4.5, 0, 6.2832);
      ctx.fillStyle = '#ffca47'; ctx.fill();
    }
  }

  /* maniglia della piega */
  function drawHandle() {
    if (S.phase !== 'bend' || S.bend.busy) return;
    var y = ground(W / 2), pulse = S.bend.touched ? 0 : (Math.sin(S.t * 3) * .5 + .5);
    ctx.save();
    ctx.globalAlpha = .55 + pulse * .45;
    ctx.fillStyle = 'rgba(13,34,51,.9)';
    ctx.beginPath(); ctx.arc(W / 2, y, 21, 0, 6.2832); ctx.fill();
    ctx.strokeStyle = '#ffca47'; ctx.lineWidth = 2.4; ctx.stroke();
    ctx.fillStyle = '#ffca47'; ctx.font = '700 12px ' + FONT;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('▲', W / 2, y - 8);
    ctx.fillText('▼', W / 2, y + 9);
    ctx.restore();
  }

  function roundRect(x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  var FONT = '"Segoe UI",-apple-system,Roboto,sans-serif';

  function draw() {
    ctx.clearRect(0, 0, W, H);
    drawSky();
    drawGround();
    drawTrees();
    drawSea();
    drawZones();
    drawSigns();
    drawHeroes();
    drawLevel();
    drawHandle();
  }

  var last = 0;
  function loop(now) {
    if (!last) last = now;
    advance(Math.min(now - last, 50));
    last = now;
    requestAnimationFrame(loop);
  }

  /* ═══════════════ dimensioni ═══════════════ */
  function resize() {
    var r = stage.getBoundingClientRect();
    W = Math.max(1, r.width); H = Math.max(1, r.height);
    var dpr = Math.min(window.devicePixelRatio || 1, 2.5);
    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    UI = clamp(Math.min(W, H) / 420, 1, 1.7);
    computeView();
    layoutStrip();
    if (S.hero) placeHeroes();   /* le posizioni sono in pixel: vanno rifatte */
  }
  window.addEventListener('resize', resize);
  if (window.ResizeObserver) new ResizeObserver(resize).observe(stage);

  /* ═══════════════ problema ═══════════════ */
  function solve() {
    var a = S.a, b = S.b, c = S.c;
    S.D = b * b - 4 * a * c;
    if (S.D > 1e-9) {
      var s = Math.sqrt(S.D);
      var p = (-b - s) / (2 * a), q = (-b + s) / (2 * a);
      S.r1 = Math.min(p, q); S.r2 = Math.max(p, q); S.nr = 2;
    } else if (S.D > -1e-9) {
      S.D = 0; S.r1 = S.r2 = -b / (2 * a); S.nr = 1;
    } else { S.r1 = S.r2 = null; S.nr = 0; }

    /* zone e zone corrette */
    S.zones = [];
    if (S.nr === 2) {
      S.zones.push({ lo: -Infinity, hi: S.r1, sample: S.r1 - 1 });
      S.zones.push({ lo: S.r1, hi: S.r2, sample: (S.r1 + S.r2) / 2 });
      S.zones.push({ lo: S.r2, hi: Infinity, sample: S.r2 + 1 });
    } else if (S.nr === 1) {
      S.zones.push({ lo: -Infinity, hi: S.r1, sample: S.r1 - 1 });
      S.zones.push({ lo: S.r1, hi: Infinity, sample: S.r1 + 1 });
    } else {
      S.zones.push({ lo: -Infinity, hi: Infinity, sample: S.xv });
    }
    var wantPos = (S.op === '>' || S.op === '>=');
    S.okZones = [];
    for (var i = 0; i < S.zones.length; i++) {
      var v = f(S.zones[i].sample);
      if (wantPos ? v > 0 : v < 0) S.okZones.push(i);
    }
  }

  /* ═══════════════ soluzione in parole ═══════════════ */
  function buildSolution() {
    var inc = (S.op === '>=' || S.op === '<=');
    var roots = S.nr === 2 ? [S.r1, S.r2] : S.nr === 1 ? [S.r1] : [];
    var ok = [], i;
    for (i = 0; i < S.zones.length; i++) ok.push(S.okZones.indexOf(i) >= 0);

    var parts = [];   /* {lo,hi,loInc,hiInc} */
    var cur = null;
    for (i = 0; i < S.zones.length; i++) {
      if (ok[i]) {
        if (cur) { cur.hi = S.zones[i].hi; cur.hiInc = false; }
        else cur = { lo: S.zones[i].lo, hi: S.zones[i].hi, loInc: false, hiInc: false };
        /* il confine destro entra nella soluzione? */
        if (i < S.zones.length - 1 && inc) {
          if (ok[i + 1]) { continue; }          /* fonde con la prossima */
          cur.hiInc = true;
        }
        parts.push(cur); cur = null;
      } else if (inc && i < S.zones.length - 1) {
        /* zona esclusa, ma la riva di destra è inclusa: punto isolato */
        var r = roots[i];
        if (!ok[i + 1]) parts.push({ lo: r, hi: r, loInc: true, hiInc: true, point: true });
      }
    }
    /* la riva sinistra dei tratti che iniziano su una radice inclusa */
    if (inc) {
      for (i = 0; i < parts.length; i++) {
        if (isFinite(parts[i].lo) && !parts[i].point) parts[i].loInc = true;
      }
    }
    return parts;
  }

  function solutionText(parts) {
    if (!parts.length) return '∅  (nessun valore di x)';
    if (parts.length === 1 && !isFinite(parts[0].lo) && !isFinite(parts[0].hi)) return '∀x ∈ ℝ';
    /* tutta la retta tranne un punto: si scrive meglio così */
    if (parts.length === 2 && !isFinite(parts[0].lo) && !isFinite(parts[1].hi) &&
        Math.abs(parts[0].hi - parts[1].lo) < 1e-9 && !parts[0].hiInc && !parts[1].loInc)
      return '∀x ≠ ' + fmtNum(parts[0].hi);
    var out = [];
    for (var i = 0; i < parts.length; i++) {
      var p = parts[i];
      if (p.point) { out.push('x = ' + fmtNum(p.lo)); continue; }
      if (!isFinite(p.lo)) out.push('x ' + (p.hiInc ? '≤' : '<') + ' ' + fmtNum(p.hi));
      else if (!isFinite(p.hi)) out.push('x ' + (p.loInc ? '≥' : '>') + ' ' + fmtNum(p.lo));
      else out.push(fmtNum(p.lo) + ' ' + (p.loInc ? '≤' : '<') + ' x ' + (p.hiInc ? '≤' : '<') + ' ' + fmtNum(p.hi));
    }
    return out.join('  ∨  ');
  }

  function intervalText(parts) {
    if (!parts.length) return '∅';
    var out = [];
    for (var i = 0; i < parts.length; i++) {
      var p = parts[i];
      if (p.point) { out.push('{' + fmtNum(p.lo) + '}'); continue; }
      var l = isFinite(p.lo) ? (p.loInc ? '[' : ']') + fmtNum(p.lo) : ']' + MINUS + '∞';
      var r = isFinite(p.hi) ? fmtNum(p.hi) + (p.hiInc ? ']' : '[') : '+∞[';
      out.push(l + '; ' + r);
    }
    return out.join(' ∪ ');
  }

  /* ═══════════════ striscia dell'asse x ═══════════════ */
  function layoutStrip() {
    if (S.phase !== 'pick' && S.phase !== 'done') return;
    zonesEl.innerHTML = ''; marksEl.innerHTML = '';
    var sw = stripEl.getBoundingClientRect().width;
    for (var i = 0; i < S.zones.length; i++) {
      var z = S.zones[i];
      var xa = isFinite(z.lo) ? X2P(z.lo) / W * sw : 0;
      var xb = isFinite(z.hi) ? X2P(z.hi) / W * sw : sw;
      var d = document.createElement('div');
      d.className = 'zone' + (S.phase === 'done' && S.okZones.indexOf(i) >= 0 ? ' picked' : '');
      d.style.left = (xa + 3) + 'px';
      d.style.width = Math.max(10, xb - xa - 6) + 'px';
      d.dataset.i = i;
      zonesEl.appendChild(d);
    }
    var roots = S.nr === 2 ? [S.r1, S.r2] : S.nr === 1 ? [S.r1] : [];
    var full = (S.op === '>=' || S.op === '<=');
    for (var k = 0; k < roots.length; k++) {
      var m = document.createElement('div');
      m.className = 'mark';
      m.style.left = (X2P(roots[k]) / W * sw) + 'px';
      m.innerHTML = '<div class="dot' + (full ? ' full' : '') + '"></div>' +
        '<div class="lbl">' + fmtNum(roots[k]) + '</div>';
      marksEl.appendChild(m);
    }
  }

  /* ═══════════════ interfaccia per fase ═══════════════ */
  function setActions(list) {
    actionsEl.innerHTML = '';
    list.forEach(function (o) {
      var b = document.createElement('button');
      b.type = 'button';
      b.textContent = o.label;
      if (o.cls) b.className = o.cls;
      b.addEventListener('click', o.fn);
      actionsEl.appendChild(b);
    });
  }
  function setPips() {
    var order = ['bend', 'sea', 'pick', 'done'];
    var idx = order.indexOf(S.phase);
    document.querySelectorAll('.pip').forEach(function (p, i) {
      p.className = 'pip' + (i < idx ? ' done' : i === idx ? ' on' : '');
    });
  }
  function say(html) { hintEl.innerHTML = html; }
  function flash(txt, good) {
    flashEl.textContent = txt;
    flashEl.className = 'show ' + (good ? 'good' : 'bad');
    setTimeout(function () { flashEl.className = ''; }, good ? 1300 : 1900);
  }

  function setPhase(p) {
    S.phase = p;
    setPips();
    calcEl.hidden = (p !== 'sea' && p !== 'pick' && p !== 'done') || !S.sea.revealed;
    stripEl.hidden = (p !== 'pick' && p !== 'done');
    if (!stripEl.hidden) layoutStrip();

    if (p === 'bend') {
      say('Piega la barra: deve diventare il grafico di <b class="m">y = ' + polyString(S.a, S.b, S.c) + '</b>');
      setActions([{ label: 'Cambia disequazione', cls: 'ghost', fn: openSetup }]);
    } else if (p === 'sea') {
      if (S.nr === 0) {
        /* niente radici, quindi niente rive su cui puntare: il mare va da sé */
        say('<b class="m">' + polyString(S.a, S.b, S.c) + ' = 0</b> non ha soluzioni: non c’è nessuna riva da cercare. Il mare sale da solo.');
        setActions([]);
        S.sea.locked = true; S.sea.auto = true;   /* bloccato al dito, ma la linea si vede salire */
        tween(function () { return S.sea.y; }, function (v) { S.sea.y = v; }, 0, 1500, function () {
          S.sea.auto = false; revealRoots();
        });
      } else {
        say('Alza il mare finché le rive arrivano sulle soluzioni di <b class="m">' + polyString(S.a, S.b, S.c) + ' = 0</b>');
        setActions([
          { label: '▼', fn: function () { nudge(-1); } },
          { label: '▲', fn: function () { nudge(1); } }
        ]);
      }
    } else if (p === 'pick') {
      say('Chi mandi a cercare la soluzione di <b class="m">' + polyString(S.a, S.b, S.c) + ' ' + opSym(S.op) + ' 0</b>?');
      setActions([
        { label: '🧗 Alpinista', fn: function () { chooseHero('alp'); } },
        { label: '🤿 Subacqueo', fn: function () { chooseHero('sub'); } }
      ]);
    }
  }

  /* ═══════════════ fase 1 — la piega ═══════════════ */
  function bendRelease() {
    var d = S.bend.d;
    var tornaDritta = function (ms) {
      tween(function () { return S.bend.morph; }, function (v) { S.bend.morph = v; }, 0, ms, function () {
        S.bend.d = 0; S.bend.wrong = false;
      });
    };
    if (Math.abs(d) < 22) { tornaDritta(260); return; }
    var wantDown = S.a > 0;          /* a>0 → il centro scende → valle */
    if ((d > 0) === wantDown) {
      S.bend.busy = true; S.bend.wrong = false;
      flash(wantDown ? 'Valle — concavità verso l’alto' : 'Collina — concavità verso il basso', true);
      buzz(18);
      /* la forma e' gia' quella giusta: resta solo da finire di piegarla */
      tween(function () { return S.bend.morph; }, function (v) { S.bend.morph = v; }, 1,
        Math.round(700 * (1 - S.bend.morph) + 120), function () {
          S.bend.busy = false;
          S.sea.y = S.sea.start;
          setPhase('sea');
        });
    } else {
      flash('Con a = ' + fmtInt(S.a) + ' la piega va dall’altra parte', false);
      buzz([14, 60, 14]);
      tornaDritta(420);
    }
  }

  /* ═══════════════ fase 2 — la marea ═══════════════ */
  function nudge(dir) {
    if (S.sea.locked) return;
    var st = (V.y1 - V.y0) * .035;
    setSea(S.sea.y + dir * st);
  }
  function setSea(y) {
    if (S.sea.locked) return;
    var span = V.y1 - V.y0, prev = S.sea.y;
    y = clamp(y, S.sea.min, S.sea.max);
    /* aggancio alla quota zero: per vicinanza, oppure se un gesto veloce la scavalca */
    if (Math.abs(y) < span * .035 || (prev < 0 && y >= 0) || (prev > 0 && y <= 0)) {
      S.sea.y = 0;
      revealRoots();
    } else S.sea.y = y;
  }

  function revealRoots() {
    if (S.sea.revealed) return;
    S.sea.revealed = true; S.sea.locked = true; S.sea.dragging = false;
    buzz(25);
    var html = '<div class="row"><span>Δ = b² ' + MINUS + ' 4ac = ' + fmtInt(S.b) + '² ' + MINUS + ' 4·' + fmtInt(S.a) + '·' + fmtInt(S.c) + '</span><span>' + fmtInt(S.D) + '</span></div>';
    if (S.nr === 2) {
      html += '<div class="row"><span>rive del mare</span><span>x₁ = ' + rootLabel(S.r1) + ' , x₂ = ' + rootLabel(S.r2) + '</span></div>';
      flash('Quota zero — due rive', true);
    } else if (S.nr === 1) {
      html += '<div class="row"><span>una sola riva</span><span>x₀ = ' + rootLabel(S.r1) + '</span></div>';
      flash('Il mare sfiora la cima: una sola riva', true);
    } else {
      html += '<div class="row"><span>rive</span><span>nessuna</span></div>';
      flash('Il terreno non tocca mai il mare', true);
    }
    calcEl.innerHTML = html; calcEl.hidden = false;
    say('L’acqua è a <b>quota 0</b>: sopra il pelo dell’acqua ' + polyString(S.a, S.b, S.c) + ' è positivo, sotto è negativo.');
    setActions([{ label: 'Avanti', cls: 'primary', fn: function () { setPhase('pick'); } }]);
  }
  function rootLabel(r) {
    return isExact(r) ? fmtNum(r) : '≈ ' + r.toFixed(2).replace('-', MINUS).replace('.', ',');
  }

  /* ═══════════════ fase 3 — la scelta ═══════════════ */
  /* ═══════════════ i due personaggi ═══════════════ */
  function art(v, prima) {
    var intero = Math.abs(v - Math.round(v)) < 1e-9 && v > 0;
    return prima ? (intero ? 'del ' : 'di ') : (intero ? 'il ' : '');
  }
  function zoneText(i) {
    var z = S.zones[i];
    if (!isFinite(z.lo) && !isFinite(z.hi)) return tuttoText();
    if (!isFinite(z.lo)) return 'Io mi trovo prima ' + art(z.hi, true) + fmtNum(z.hi);
    if (!isFinite(z.hi)) return 'Io mi trovo dopo ' + art(z.lo, false) + fmtNum(z.lo);
    return 'Io mi trovo tra ' + fmtNum(z.lo) + ' e ' + fmtNum(z.hi);
  }

  function tuttoText() {
    return S.hero === 'alp' ? 'Evviva: è tutta montagna!' : 'Evviva: è tutto sott’acqua!';
  }

  /* il punto con più acqua sopra la testa */
  function deepSpot() {
    var ySea = Y2P(0), best = W / 2, bestD = -1e9;
    for (var k = 0; k <= 24; k++) {
      var px = 34 + (W - 68) * k / 24;
      var d = Math.min(ground(px), H) - ySea;
      if (d > bestD) { bestD = d; best = px; }
    }
    return { x: best, d: bestD };
  }

  /* il punto di terreno più pianeggiante fra quelli in vista */
  function flatSpot() {
    var best = W / 2, bestScore = -1e9;
    for (var k = 0; k <= 24; k++) {
      var px = 34 + (W - 68) * k / 24, gy = ground(px);
      if (gy < 60 || gy > H - 30) continue;
      var sc = -Math.abs(ground(px + 5) - ground(px - 5));
      if (sc > bestScore) { bestScore = sc; best = px; }
    }
    return best;
  }

  /* cerca nella zona il punto migliore: pianeggiante per l'alpinista, fondo per il sub */
  function spotInZone(xa, xb, z, isAlp, margine, lasco) {
    var lo = isFinite(z.lo) ? xa + margine : xa + 6;
    var hi = isFinite(z.hi) ? xb - margine : xb - 6;
    lo = Math.max(lo, 26); hi = Math.min(hi, W - 26);
    if (hi < lo) { var c = clamp((xa + xb) / 2, 26, W - 26); lo = c; hi = c; }
    var ySea = Y2P(0), best = null, bestScore = -1e9, n = (hi > lo) ? 20 : 0;
    for (var k = 0; k <= n; k++) {
      var px = n ? lo + (hi - lo) * k / n : lo, gy = ground(px), score;
      if (isAlp) {
        if (!lasco && (gy < 52 || gy > H - 26)) continue;
        score = -Math.abs(ground(px + 5) - ground(px - 5));
      } else {
        var d = Math.min(gy, H) - ySea;
        if (!lasco && d < 26) continue;
        score = d;
      }
      if (score > bestScore) { bestScore = score; best = px; }
    }
    return best;
  }

  function placeHeroes() {
    S.heroes = [];
    if (!S.hero) return;
    var isAlp = S.hero === 'alp', ySea = Y2P(0), i, k;

    /* se la soluzione è tutta la retta basta un personaggio solo: con Δ = 0 le zone
       sono due ma il punto in mezzo è incluso, e due fumetti direbbero una mezza verità */
    var parts = buildSolution();
    if (parts.length === 1 && !isFinite(parts[0].lo) && !isFinite(parts[0].hi)) {
      if (isAlp) {
        var fx = flatSpot();
        S.heroes.push({ x: fx, y: ground(fx), s: 1, text: tuttoText() });
      } else {
        var dp = deepSpot();
        S.heroes.push({ x: dp.x, y: ySea + Math.min(dp.d * .5, H * .16),
          s: clamp(dp.d / 95, .62, 1), text: tuttoText() });
      }
      return;
    }
    for (i = 0; i < S.zones.length; i++) {
      if (S.okZones.indexOf(i) < 0) continue;
      var z = S.zones[i];
      var xa = clamp(isFinite(z.lo) ? X2P(z.lo) : 0, 4, W - 4);
      var xb = clamp(isFinite(z.hi) ? X2P(z.hi) : W, 4, W - 4);
      /* si prova a stare larghi dalle rive, dove vanno i cartelli; se in quella fascia
         il terreno esce dall'inquadratura si stringe, e in ultima istanza si accetta
         qualunque punto: una zona della soluzione deve SEMPRE avere il suo personaggio */
      var margini = [44, 26, 12], best = null, usato = 0;
      for (var mi = 0; mi < margini.length && best == null; mi++) {
        best = spotInZone(xa, xb, z, isAlp, margini[mi], false);
        usato = margini[mi];
      }
      if (best == null) { best = spotInZone(xa, xb, z, isAlp, 4, true); usato = 4; }
      if (best == null) continue;
      var stretto = usato < 40;      /* poco spazio: rimpicciolisce per non coprire il cartello */
      var g2 = ground(best), deep = Math.min(g2, H) - ySea;
      S.heroes.push({
        x: best,
        y: isAlp ? g2 : ySea + Math.min(deep * .5, H * .16),
        s: (isAlp ? 1 : clamp(deep / 95, .62, 1)) * (stretto ? .78 : 1),
        text: zoneText(i)
      });
    }
    if (S.heroes.length || S.okZones.length) return;
    /* nessuna zona: il personaggio compare lo stesso e dice come stanno le cose */
    var roots = S.nr === 2 ? [S.r1, S.r2] : S.nr === 1 ? [S.r1] : [];
    var inc = (S.op === '>=' || S.op === '<=');
    if (inc && roots.length === 1) {
      /* il punto è il fondo della conca: sotto c'è terra piena, quindi ci galleggia sopra */
      S.heroes.push({ x: X2P(roots[0]), y: isAlp ? ground(X2P(roots[0])) : Y2P(0) - 13, s: .9,
        text: isAlp ? 'È rimasta solo la punta sul ' + fmtNum(roots[0])
                    : 'C’è soltanto una goccia sul ' + fmtNum(roots[0]) });
    } else {
      /* nessun posto dove stare: resta in piedi sul terreno, scontento */
      var spot = flatSpot(), gy = ground(spot);
      var y = (gy > 40 && gy < H - 20) ? gy : H * .62;
      /* con Δ = 0 la parabola lo zero lo tocca, in un punto solo: dirlo com'è */
      var sfiora = (roots.length === 1);
      S.heroes.push({
        x: spot, y: y, s: 1, standing: true, sad: true,
        underwater: isAlp && y > Y2P(0),        /* l'alpinista senza montagne è sott'acqua */
        text: isAlp ? (sfiora ? 'Non c’è più spazio'
                              : 'Qui non c’è nessuna montagna… blub blub!')
                    : (sfiora ? 'Non c’è acqua'
                              : 'Qui non c’è acqua da nessuna parte')
      });
    }
  }

  function drawClimber(s, sad) {
    var w = s * .34;
    ctx.lineCap = 'round';
    ctx.strokeStyle = '#2b3a55'; ctx.lineWidth = s * .1;
    ctx.beginPath();
    ctx.moveTo(-w * .38, 0); ctx.lineTo(-w * .2, -s * .34);
    ctx.moveTo(w * .38, 0); ctx.lineTo(w * .16, -s * .34);
    ctx.stroke();
    ctx.fillStyle = '#8b5a2b'; roundRect(-w * .78, -s * .74, w * .55, s * .32, s * .05); ctx.fill();
    ctx.fillStyle = '#e04b3a'; roundRect(-w * .44, -s * .76, w * .88, s * .44, s * .07); ctx.fill();
    ctx.strokeStyle = '#e04b3a'; ctx.lineWidth = s * .09;
    if (sad) {                       /* braccio giù e piccozza a terra */
      ctx.beginPath(); ctx.moveTo(w * .4, -s * .68); ctx.lineTo(w * .54, -s * .38); ctx.stroke();
      ctx.strokeStyle = '#cfd6dd'; ctx.lineWidth = s * .045;
      ctx.beginPath(); ctx.moveTo(w * .54, -s * .4); ctx.lineTo(w * .6, -s * .02);
      ctx.moveTo(w * .6, -s * .02); ctx.lineTo(w * .44, -s * .08); ctx.stroke();
    } else {
      ctx.beginPath(); ctx.moveTo(w * .3, -s * .68); ctx.lineTo(w * .64, -s * .88); ctx.stroke();
      ctx.strokeStyle = '#cfd6dd'; ctx.lineWidth = s * .045;
      ctx.beginPath(); ctx.moveTo(w * .52, -s * .74); ctx.lineTo(w * .84, -s * 1.04);
      ctx.moveTo(w * .84, -s * 1.04); ctx.lineTo(w * .6, -s * 1.02); ctx.stroke();
    }
    ctx.fillStyle = '#f0c9a0'; ctx.beginPath(); ctx.arc(0, -s * .88, s * .135, 0, 6.2832); ctx.fill();
    ctx.fillStyle = '#ffca47';
    ctx.beginPath(); ctx.arc(0, -s * .90, s * .16, Math.PI, 0); ctx.fill();
    ctx.fillRect(-s * .17, -s * .91, s * .34, s * .045);
  }

  /* subacqueo a terra: in piedi, pinne larghe, maschera alzata e broncio */
  function drawStandingDiver(s) {
    var w = s * .34;
    ctx.lineCap = 'round';
    /* pinne, con un filo di bordo chiaro o spariscono sul terreno scuro */
    ctx.fillStyle = '#16232f'; ctx.strokeStyle = 'rgba(200,222,236,.8)'; ctx.lineWidth = s * .022;
    ctx.beginPath(); ctx.ellipse(-w * .74, -s * .03, w * .6, s * .075, .14, 0, 6.2832); ctx.fill(); ctx.stroke();
    ctx.beginPath(); ctx.ellipse(w * .74, -s * .03, w * .6, s * .075, -.14, 0, 6.2832); ctx.fill(); ctx.stroke();
    ctx.strokeStyle = '#1b2a3a'; ctx.lineWidth = s * .11;      /* gambe */
    ctx.beginPath();
    ctx.moveTo(-w * .32, -s * .07); ctx.lineTo(-w * .22, -s * .36);
    ctx.moveTo(w * .32, -s * .07); ctx.lineTo(w * .22, -s * .36);
    ctx.stroke();
    ctx.fillStyle = '#9aa7b2';                                  /* bombola di lato */
    roundRect(-w * .95, -s * .76, w * .32, s * .38, s * .06); ctx.fill();
    ctx.strokeStyle = '#c9d3da'; ctx.lineWidth = s * .028;      /* tubo verso la testa */
    ctx.beginPath(); ctx.moveTo(-w * .8, -s * .74); ctx.lineTo(-s * .16, -s * .88); ctx.stroke();
    ctx.fillStyle = '#1b2a3a';                                  /* busto */
    roundRect(-w * .46, -s * .76, w * .92, s * .44, s * .08); ctx.fill();
    ctx.strokeStyle = '#1b2a3a'; ctx.lineWidth = s * .095;      /* braccia giù, spalle basse */
    ctx.beginPath();
    ctx.moveTo(-w * .44, -s * .68); ctx.lineTo(-w * .6, -s * .4);
    ctx.moveTo(w * .44, -s * .68); ctx.lineTo(w * .6, -s * .4);
    ctx.stroke();
    ctx.fillStyle = '#f0c9a0';                                  /* testa */
    ctx.beginPath(); ctx.arc(0, -s * .92, s * .175, 0, 6.2832); ctx.fill();
    ctx.fillStyle = '#8ee6ff';                                  /* maschera alzata sulla fronte */
    roundRect(-s * .18, -s * 1.09, s * .36, s * .12, s * .035); ctx.fill();
    ctx.strokeStyle = '#16232f'; ctx.lineWidth = s * .028;
    ctx.beginPath(); ctx.moveTo(-s * .19, -s * 1.02); ctx.lineTo(s * .19, -s * 1.02); ctx.stroke();
    ctx.fillStyle = '#16232f';                                  /* occhi */
    ctx.beginPath(); ctx.arc(-s * .065, -s * .945, s * .023, 0, 6.2832);
    ctx.arc(s * .065, -s * .945, s * .023, 0, 6.2832); ctx.fill();
    ctx.strokeStyle = '#9c6552'; ctx.lineWidth = s * .028;      /* broncio */
    ctx.beginPath(); ctx.arc(0, -s * .84, s * .075, Math.PI * 1.22, Math.PI * 1.78); ctx.stroke();
  }

  function drawDiver(s) {
    ctx.fillStyle = '#1b2a3a';
    ctx.beginPath(); ctx.ellipse(-s * .02, 0, s * .34, s * .19, -.12, 0, 6.2832); ctx.fill();
    ctx.beginPath();
    ctx.moveTo(-s * .3, -s * .02); ctx.lineTo(-s * .62, -s * .18); ctx.lineTo(-s * .56, s * .12);
    ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#9aa7b2'; roundRect(-s * .16, -s * .28, s * .3, s * .15, s * .05); ctx.fill();
    ctx.fillStyle = '#1b2a3a'; ctx.beginPath(); ctx.arc(s * .32, -s * .07, s * .16, 0, 6.2832); ctx.fill();
    ctx.fillStyle = '#8ee6ff'; roundRect(s * .3, -s * .15, s * .2, s * .13, s * .04); ctx.fill();
    ctx.strokeStyle = '#1b2a3a'; ctx.lineWidth = s * .085; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(s * .08, s * .04); ctx.lineTo(s * .3, s * .2); ctx.stroke();
    ctx.fillStyle = 'rgba(255,255,255,.55)';
    for (var b = 0; b < 3; b++) {
      var ph = (S.t * .5 + b * .34) % 1;
      ctx.beginPath();
      ctx.arc(s * .46 + b * s * .07, -s * .22 - ph * s * .95, s * .055 * (1 - ph * .45), 0, 6.2832);
      ctx.fill();
    }
  }

  function drawBalloon(x, y, text, alpha) {
    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.font = '600 ' + (12.5 * UI).toFixed(1) + 'px ' + FONT;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    /* le frasi lunghe vanno su due righe, spezzate dove le due metà si pareggiano */
    var righe = [text], k;
    if (ctx.measureText(text).width + 20 > W - 26) {
      var par = text.split(' '), tagl = -1, diff = 1e9;
      for (k = 1; k < par.length; k++) {
        var d = Math.abs(ctx.measureText(par.slice(0, k).join(' ')).width -
                         ctx.measureText(par.slice(k).join(' ')).width);
        if (d < diff) { diff = d; tagl = k; }
      }
      if (tagl > 0) righe = [par.slice(0, tagl).join(' '), par.slice(tagl).join(' ')];
    }
    var wp = 0;
    for (k = 0; k < righe.length; k++) wp = Math.max(wp, ctx.measureText(righe[k]).width);
    wp += 20;
    var hp = righe.length > 1 ? 42 : 26;
    var bx = clamp(x, wp / 2 + 5, W - wp / 2 - 5), by = y;
    ctx.fillStyle = 'rgba(255,255,255,.96)';
    roundRect(bx - wp / 2, by - hp / 2, wp, hp, 9); ctx.fill();
    ctx.beginPath();                                   /* codina verso il personaggio */
    ctx.moveTo(clamp(x, bx - wp / 2 + 8, bx + wp / 2 - 8) - 5, by + hp / 2 - 1);
    ctx.lineTo(clamp(x, bx - wp / 2 + 8, bx + wp / 2 - 8) + 5, by + hp / 2 - 1);
    ctx.lineTo(x, by + hp / 2 + 9);
    ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#123049';
    for (k = 0; k < righe.length; k++) {
      ctx.fillText(righe[k], bx, by + 1 + (righe.length > 1 ? (k === 0 ? -9 : 9) : 0));
    }
    ctx.restore();
  }

  function drawHeroes() {
    if (!S.hero || !S.heroes.length || S.heroT <= 0) return;
    var isAlp = S.hero === 'alp', i, used = [];
    for (i = 0; i < S.heroes.length; i++) {
      var h = S.heroes[i];
      var t = easeOut(clamp(S.heroT * 1.35 - i * .18, 0, 1));
      if (t <= 0) continue;
      var s = 46 * h.s * UI;
      var aTerra = isAlp || h.standing;
      var bob = aTerra ? 0 : Math.sin(S.t * 1.5 + i * 2) * 3;
      ctx.save();
      ctx.globalAlpha = t;
      ctx.translate(h.x, h.y + bob - (1 - t) * 30);
      if (isAlp) drawClimber(s, h.sad);
      else if (h.standing) drawStandingDiver(s);
      else drawDiver(s);
      ctx.restore();
      /* chi è finito sott'acqua fa le bollicine */
      if (h.underwater) {
        ctx.save(); ctx.globalAlpha = t * .9;
        ctx.fillStyle = 'rgba(226,250,255,.85)';
        ctx.strokeStyle = 'rgba(255,255,255,.95)'; ctx.lineWidth = 1.4;
        for (var b = 0; b < 4; b++) {
          var ph = (S.t * .42 + b * .26) % 1;
          var r = s * (.11 - b * .012) * (1 - ph * .35);
          ctx.beginPath();
          ctx.arc(h.x + s * .22 + Math.sin(ph * 4 + b) * s * .07, h.y - s * 1.02 - ph * s * 1.1, r, 0, 6.2832);
          ctx.fill(); ctx.stroke();
        }
        ctx.restore();
      }
      /* fumetto sopra la testa, scansato se due si accavallano */
      if (S.bubbleT > 0) {
        var by = h.y + bob - (aTerra ? s * 1.15 : s * .55) - 14;
        for (var k = 0; k < used.length; k++) {
          if (Math.abs(used[k].x - h.x) < 150 && Math.abs(used[k].y - by) < 30) by = used[k].y - 34;
        }
        by = clamp(by, 32, H - 32);
        used.push({ x: h.x, y: by });
        drawBalloon(h.x, by, h.text, S.bubbleT * t);
      }
    }
  }

  /* ═══════════════ fase 3 — chi va a cercare la soluzione ═══════════════ */
  function chooseHero(kind) {
    var wantPos = (S.op === '>' || S.op === '>=');
    if ((kind === 'alp') !== wantPos) {
      S.attempts++;
      buzz([14, 60, 14]);
      flash(kind === 'alp' ? 'L’alpinista cammina all’asciutto' : 'Il subacqueo sta sott’acqua', false);
      say(kind === 'alp'
        ? 'L’alpinista sta dove il terreno è <b>sopra</b> il pelo dell’acqua, cioè dove <b class="m">' + polyString(S.a, S.b, S.c) + '</b> è <b>positivo</b>. È quello che chiede <b class="m">' + polyString(S.a, S.b, S.c) + ' ' + opSym(S.op) + ' 0</b>?'
        : 'Il subacqueo sta dove il terreno è <b>sotto</b> il pelo dell’acqua, cioè dove <b class="m">' + polyString(S.a, S.b, S.c) + '</b> è <b>negativo</b>. È quello che chiede <b class="m">' + polyString(S.a, S.b, S.c) + ' ' + opSym(S.op) + ' 0</b>?');
      return;
    }
    S.hero = kind;
    placeHeroes();
    buzz(30);
    flash('Esatto!', true);
    tween(function () { return S.heroT; }, function (v) { S.heroT = v; }, 1, 650);
    tween(function () { return S.bubbleT; }, function (v) { S.bubbleT = v; }, 1, 900);
    check();
  }

  function check() {
    var parts = buildSolution();
    calcEl.innerHTML =
      '<div class="row"><span>Δ</span><span>' + fmtInt(S.D) + (S.nr === 2 ? ' > 0' : S.nr === 1 ? ' = 0' : ' < 0') + '</span></div>' +
      '<div class="row"><span>concavità</span><span>' + (S.a > 0 ? 'verso l’alto (valle)' : 'verso il basso (collina)') + '</span></div>' +
      (S.nr ? '<div class="row"><span>' + (S.nr === 2 ? 'x₁ , x₂' : 'x₀') + '</span><span>' +
        (S.nr === 2 ? rootLabel(S.r1) + ' , ' + rootLabel(S.r2) : rootLabel(S.r1)) + '</span></div>'
              : '<div class="row"><span>rive</span><span>nessuna: il terreno non tocca il mare</span></div>') +
      '<div class="sol">' + solutionText(parts) + '</div>' +
      '<div class="row" style="justify-content:center;opacity:.8;margin-top:2px"><span>' + intervalText(parts) + '</span></div>';
    calcEl.hidden = false;
    say('Soluzione trovata.');
    setActions([
      { label: 'Nuova', cls: 'primary', fn: function () { randomProblem(); startProblem(); } },
      { label: 'Scrivi tu', cls: 'ghost', fn: openSetup }
    ]);
    setPhase('done');
  }

  /* ═══════════════ tocchi sul canvas ═══════════════ */
  var ptr = { down: false, x0: 0, y0: 0, moved: 0 };
  cv.addEventListener('pointerdown', function (e) {
    try { cv.setPointerCapture(e.pointerId); } catch (_) {}
    var r = cv.getBoundingClientRect();
    ptr.down = true; ptr.x0 = e.clientX - r.left; ptr.y0 = e.clientY - r.top; ptr.moved = 0;
    if (S.phase === 'bend' && !S.bend.busy) {
      S.bend.dragging = true; S.bend.touched = true;
      S.bend.dragY0 = ptr.y0; S.bend.dragD0 = S.bend.d;
    }
    if (S.phase === 'sea' && !S.sea.locked) {
      S.sea.dragging = true; S.sea.dragY0 = ptr.y0; S.sea.dragS0 = S.sea.y;
    }
  });
  cv.addEventListener('pointermove', function (e) {
    if (!ptr.down) return;
    var r = cv.getBoundingClientRect();
    var x = e.clientX - r.left, y = e.clientY - r.top;
    ptr.moved = Math.max(ptr.moved, Math.abs(x - ptr.x0) + Math.abs(y - ptr.y0));
    if (S.bend.dragging) {
      S.bend.d = clamp(S.bend.dragD0 + (y - S.bend.dragY0), -H * .34, H * .34);
      S.bend.wrong = (S.bend.d > 0) !== (S.a > 0);
      S.bend.morph = clamp(Math.abs(S.bend.d) / (H * .30), 0, 1);
    }
    if (S.sea.dragging) {
      var perPx = (V.y1 - V.y0) / H;
      setSea(S.sea.dragS0 + (S.sea.dragY0 - y) * perPx);
    }
  });
  function endPointer() {
    if (!ptr.down) return;
    ptr.down = false;
    if (S.bend.dragging) { S.bend.dragging = false; bendRelease(); }
    if (S.sea.dragging) S.sea.dragging = false;
  }
  cv.addEventListener('pointerup', endPointer);
  cv.addEventListener('pointercancel', endPointer);

  /* ═══════════════ avvio di un problema ═══════════════ */
  function startProblem() {
    solve();
    S.bend = { d: 0, morph: 0, wrong: false, dragging: false, touched: false, busy: false };
    S.sea = { y: 0, min: 0, max: 0, dragging: false, locked: false, revealed: false, dragY0: 0, dragS0: 0 };
    S.attempts = 0;
    S.hero = null; S.heroes = []; S.heroT = 0; S.bubbleT = 0;
    computeView();
    S.sea.y = S.sea.start;
    spawnFish();
    S.trees = [];
    for (var i = 0; i < 11; i++) {
      S.trees.push({ x: V.x0 + (i + .5 + (i % 3) * .18) / 11 * (V.x1 - V.x0), s: .8 + (i % 4) * .12 });
    }
    $('#eq-display').innerHTML = eqString(S.a, S.b, S.c, S.op);
    calcEl.hidden = true;
    $('#setup').classList.add('hide');
    setTimeout(function () { $('#setup').hidden = true; resize(); }, 380);
    setPhase('bend');
  }

  function randomProblem() {
    var a, b, c, r1, r2, kind, guard = 0;
    do {
      kind = pick(['two', 'two', 'two', 'two', 'double', 'none']);
      a = pick([1, 1, 1, 1, -1, -1, -1, 2, -2, 3]);
      if (kind === 'two') {
        do { r1 = randInt(-6, 6); r2 = randInt(-6, 6); } while (r1 === r2);
        if (r1 > r2) { var t = r1; r1 = r2; r2 = t; }
        b = -a * (r1 + r2); c = a * r1 * r2;
      } else if (kind === 'double') {
        r1 = randInt(-4, 4);
        b = -2 * a * r1; c = a * r1 * r1;
      } else {
        b = randInt(-6, 6);
        var lim = b * b / (4 * a);
        c = a > 0 ? Math.ceil(lim) + randInt(1, 4) : Math.floor(lim) - randInt(1, 4);
      }
    } while (++guard < 40 && (Math.abs(b) > 24 || Math.abs(c) > 48));
    S.a = a; S.b = b; S.c = c; S.op = pick(OPS);
  }

  /* ═══════════════ schermata di inserimento ═══════════════ */
  var draft = { a: '1', b: '-2', c: '-3', op: '>' }, editing = null;

  function paintSetup() {
    document.querySelectorAll('.coef').forEach(function (el) {
      var k = el.dataset.k, v = draft[k], n = parseInt(v, 10), show;
      if (isNaN(n)) show = (v === '-' ? MINUS : '') + '?';
      else show = (k === 'a') ? fmtInt(n) : String(Math.abs(n));   /* per b e c il segno sta nel separatore */
      el.textContent = show;
      el.classList.toggle('active', editing === k);
    });
    /* segni fra i termini */
    ['b', 'c'].forEach(function (k) {
      var n = parseInt(draft[k], 10);
      var el = document.querySelector('.sgn[data-for="' + k + '"]');
      el.textContent = (isNaN(n) || n >= 0) ? '+' : MINUS;
    });
    $('#op-chip').textContent = opSym(draft.op);
    var a = parseInt(draft.a, 10);
    var bad = isNaN(a) || a === 0 || isNaN(parseInt(draft.b, 10)) || isNaN(parseInt(draft.c, 10));
    $('#setup-warn').textContent = isNaN(a) || a === 0 ? 'Il coefficiente a non può essere 0: non sarebbe di secondo grado.' : (bad ? 'Completa i coefficienti.' : ' ');
    $('#btn-start').disabled = bad;
    $('#btn-start').style.opacity = bad ? .45 : 1;
  }

  document.querySelectorAll('.coef').forEach(function (el) {
    el.addEventListener('click', function () {
      editing = el.dataset.k;
      $('#pad').hidden = false;
      paintSetup();
    });
  });
  $('#op-chip').addEventListener('click', function () {
    draft.op = OPS[(OPS.indexOf(draft.op) + 1) % 4];
    paintSetup();
  });
  document.querySelectorAll('.key').forEach(function (el) {
    el.addEventListener('click', function () {
      if (!editing) return;
      var k = el.dataset.key, v = draft[editing];
      if (k === 'del') v = v.length ? v.slice(0, -1) : '';
      else if (k === 'neg') v = v.charAt(0) === '-' ? v.slice(1) : '-' + v;
      else if (v.replace('-', '').length < 3) v = (v === '0' ? '' : v) + k;
      draft[editing] = v;
      paintSetup();
    });
  });
  $('#btn-random').addEventListener('click', function () {
    randomProblem();
    draft = { a: String(S.a), b: String(S.b), c: String(S.c), op: S.op };
    editing = null; $('#pad').hidden = true;
    paintSetup();
  });
  $('#btn-start').addEventListener('click', function () {
    var a = parseInt(draft.a, 10), b = parseInt(draft.b, 10), c = parseInt(draft.c, 10);
    if (isNaN(a) || a === 0 || isNaN(b) || isNaN(c)) return;
    S.a = a; S.b = b; S.c = c; S.op = draft.op;
    startProblem();
  });

  function openSetup() {
    draft = { a: String(S.a), b: String(S.b), c: String(S.c), op: S.op };
    editing = null; $('#pad').hidden = true;
    paintSetup();
    $('#setup').hidden = false;
    requestAnimationFrame(function () { $('#setup').classList.remove('hide'); });
    S.phase = 'setup';
    setPips();
    stripEl.hidden = true;
  }
  $('#btn-restart').addEventListener('click', function () {
    if (S.phase === 'setup') return;
    startProblem();
  });

  /* ═══════════════ aiuto ═══════════════ */
  var HELP = {
    setup: ['Come funziona', '<p>Scegli i tre coefficienti e il verso. Poi pieghi una barra fino a farne una parabola, alzi il mare e decidi quali zone tenere.</p>'],
    bend: ['La concavità', '<p>Il coefficiente <span class="m">a</span> decide come si piega la parabola: se <span class="m">a &gt; 0</span> la concavità è verso l’alto (una valle), se <span class="m">a &lt; 0</span> è verso il basso (una collina).</p><p>Qui <span class="m">a = {A}</span>.</p>'],
    sea: ['Dove fermare il mare', '<p>Le <b>rive</b> sono i punti in cui il pelo dell’acqua incontra il terreno, e sotto ognuna trovi la sua <span class="m">x</span>. Il mare è al posto giusto quando quelle due <span class="m">x</span> sono le soluzioni di <span class="m">{EQ} = 0</span>: lì l’acqua è a quota zero, e la disequazione con zero si confronta.</p><p>Se non le hai ancora calcolate: <span class="m">Δ = b² − 4ac = {DELTA}</span>, e <span class="m">x = (−b ± √Δ) / 2a = {ROOTS}</span>.</p>'],
    pick: ['Alpinista o subacqueo', '<p>L’<b>alpinista</b> cammina sulla terra emersa, cioè dove la quota è <span class="m">positiva</span>. Il <b>subacqueo</b> nuota sotto il pelo dell’acqua, dove la quota è <span class="m">negativa</span>.</p><p>Guarda il verso: <span class="m">&gt;</span> o <span class="m">≥</span> chiedono dove il polinomio è positivo, <span class="m">&lt;</span> o <span class="m">≤</span> dove è negativo. Poi il personaggio si sistema da solo e ti dice dove si trova.</p><p>Con <span class="m">≥</span> e <span class="m">≤</span> anche le rive fanno parte della soluzione: i pallini sono pieni.</p>'],
    done: ['Il risultato', '<p>Le zone verdi sono quelle che risolvono la disequazione. Sotto trovi la soluzione scritta come disuguaglianza e come intervalli.</p>']
  };
  $('#btn-help').addEventListener('click', function () {
    var h = HELP[S.phase] || HELP.setup;
    $('#help-title').textContent = h[0];
    $('#help-body').innerHTML = h[1]
      .replace('{A}', fmtInt(S.a))
      .replace('{EQ}', polyString(S.a, S.b, S.c))
      .replace('{DELTA}', fmtInt(S.D))
      .replace('{ROOTS}', S.nr === 2 ? rootLabel(S.r1) + ' e ' + rootLabel(S.r2)
                        : S.nr === 1 ? rootLabel(S.r1) + ' (una sola)' : 'nessuna soluzione');
    $('#helpbox').hidden = false;
  });
  $('#help-close').addEventListener('click', function () { $('#helpbox').hidden = true; });

  /* ═══════════════ via ═══════════════ */
  randomProblem();
  draft = { a: String(S.a), b: String(S.b), c: String(S.c), op: S.op };
  paintSetup();
  solve();
  resize();
  requestAnimationFrame(loop);

  /* ganci per il collaudo automatico */
  window.__marea = {
    S: S, V: V,
    probe: function (a, b, c, op) {
      S.a = a; S.b = b; S.c = c; S.op = op;
      solve();
      var p = buildSolution();
      return { D: S.D, nr: S.nr, r1: S.r1, r2: S.r2, ok: S.okZones.slice(), txt: solutionText(p), iv: intervalText(p) };
    },
    play: function (a, b, c, op) { S.a = a; S.b = b; S.c = c; S.op = op; startProblem(); },
    bend: function (d) { S.bend.d = d; bendRelease(); },
    sea: function (y) { setSea(y); },
    hero: function (kind) { chooseHero(kind); },
    tick: function (ms) { advance(ms || 16); },
    size: function () { return { W: W, H: H }; },
    shot: function () { return cv.toDataURL('image/png'); },
    probeGround: function (px) { return ground(px); }
  };
})();
