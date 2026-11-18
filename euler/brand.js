/* dm3 brand animation: travelling sine wave and hero phase portrait.
   Copied from AXLE/AAlpha_Linkedin/dm3brand.html. */
/* ── TRAVELLING SINE WAVE (the dm³ wake) ───────────────── */
(function () {
  var STEPS = 64, W = 100, CY = 10, AMP = 6.2, FREQ = 1.15, SPEED = 2.2, start = null;
  function buildPath(phase) {
    var pts = [], i, t, env, y;
    for (i = 0; i <= STEPS; i++) {
      t = i / STEPS;
      env = Math.sin(Math.PI * t);            /* taper to zero at both ends */
      y = CY + AMP * env * Math.sin(2 * Math.PI * FREQ * t - phase);
      pts.push([(t * W).toFixed(2), y.toFixed(2)]);
    }
    return 'M' + pts[0].join(',') + pts.slice(1).map(function (p) { return 'L' + p.join(','); }).join('');
  }
  var paths = Array.prototype.map.call(
    document.querySelectorAll('.wave-svg[data-wave]'),
    function (s) { return s.querySelector('.wave-path'); }
  );
  if (!paths.length) return;
  if (window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches) {
    var d0 = buildPath(0); paths.forEach(function (p) { p.setAttribute('d', d0); }); return;
  }
  (function loop(ts) {
    if (!start) start = ts;
    var d = buildPath((ts - start) / 1000 * SPEED);
    paths.forEach(function (p) { p.setAttribute('d', d); });
    requestAnimationFrame(loop);
  })(performance.now());
})();

/* ── HERO FIELD: starfield + phase portrait ────────────────
   The trajectories integrate the polar system

       dr/dt = r(1 - r²)      dθ/dt = ω

   whose unit circle is an attracting limit cycle — the same
   object the transverse Lyapunov exponent μmax = −2 measures.
   Orbits started inside and outside both wind onto it.        */
(function () {
  var cv = document.getElementById('field');
  if (!cv) return;
  var ctx = cv.getContext('2d'), w = 0, h = 0, dpr = 1;
  var reduce = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  var stars = [], orbits = [];

  function seed() {
    stars = [];
    var n = Math.min(170, Math.round(w * h / 9000));
    for (var i = 0; i < n; i++) {
      stars.push({ x: Math.random() * w, y: Math.random() * h,
                   r: Math.random() * 1.05 + 0.2,
                   a: Math.random() * 0.45 + 0.12,
                   tw: Math.random() * 6.28, sp: Math.random() * 0.8 + 0.25 });
    }
    orbits = [];
    for (var k = 0; k < 26; k++) {
      var inside = k % 2 === 0;
      orbits.push({
        r: inside ? 0.06 + Math.random() * 0.34 : 1.35 + Math.random() * 1.25,
        th: Math.random() * 6.28,
        w: 0.34 + Math.random() * 0.30,
        hue: k % 3,
        a: 0.16 + Math.random() * 0.30
      });
    }
  }

  function resize() {
    var rect = cv.getBoundingClientRect();
    dpr = Math.min(window.devicePixelRatio || 1, 2);
    w = rect.width; h = rect.height;
    cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    seed();
    ctx.fillStyle = '#04060d'; ctx.fillRect(0, 0, w, h);
  }

  var COLORS = ['201,168,76', '86,200,216', '139,123,240'];
  var last = 0;

  function frame(ts) {
    var dt = Math.min((ts - last) / 1000, 0.05); last = ts;

    /* motion-blur wash leaves the orbit trails behind */
    ctx.fillStyle = 'rgba(4,6,13,0.13)';
    ctx.fillRect(0, 0, w, h);

    var cx = w * 0.5, cy = h * 0.46;
    var R = Math.min(w, h) * 0.30;

    for (var i = 0; i < stars.length; i++) {
      var s = stars[i];
      s.tw += dt * s.sp;
      var a = s.a * (0.62 + 0.38 * Math.sin(s.tw));
      ctx.fillStyle = 'rgba(236,233,224,' + a.toFixed(3) + ')';
      ctx.fillRect(s.x, s.y, s.r, s.r);
    }

    for (var j = 0; j < orbits.length; j++) {
      var o = orbits[j];
      /* one explicit Euler step of the limit-cycle flow */
      o.r += o.r * (1 - o.r * o.r) * dt * 0.85;
      o.th += o.w * dt;
      var px = cx + Math.cos(o.th) * o.r * R;
      var py = cy + Math.sin(o.th) * o.r * R * 0.52;
      ctx.beginPath();
      ctx.arc(px, py, 1.25, 0, 6.2832);
      ctx.fillStyle = 'rgba(' + COLORS[o.hue] + ',' + o.a.toFixed(3) + ')';
      ctx.fill();
    }

    /* the attractor itself */
    ctx.beginPath();
    ctx.ellipse(cx, cy, R, R * 0.52, 0, 0, 6.2832);
    ctx.strokeStyle = 'rgba(201,168,76,0.13)';
    ctx.lineWidth = 1;
    ctx.stroke();

    requestAnimationFrame(frame);
  }

  resize();
  window.addEventListener('resize', resize);
  if (!reduce) requestAnimationFrame(function (t) { last = t; frame(t); });
})();

