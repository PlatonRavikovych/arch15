(function () {
  "use strict";
  const $ = (s) => document.querySelector(s);
  const S = 10,
    W = 800,
    H = 520,
    CELL = 10,
    COLS = W / CELL,
    ROWS = H / CELL,
    LAT = (50.45 * Math.PI) / 180,
    MINEL = 0.08;
  const cv = $("#cv"),
    ctx = cv.getContext("2d"),
    sh = document.createElement("canvas"),
    sctx = sh.getContext("2d");
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  [cv, sh].forEach((c) => {
    c.width = W * dpr;
    c.height = H * dpr;
  });
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  sctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const css = (n) =>
    getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const DEF = {
    tree: { s: 5, l: 5, h: 8 },
    building: { s: 12, l: 9, h: 15 },
    awning: { s: 8, l: 4, h: 3 },
    sensor: { s: 1, l: 1, h: 0 },
  };
  const NAME = {
    tree: "Дерево",
    building: "Будівля",
    awning: "Навіс",
    sensor: "Лавка-датчик",
  };
  /* ---------- Стан застосунку ---------- */
  let objs = [],
    sel = null,
    tool = "select",
    day = 172,
    time = 13,
    showHeat = false,
    base = null,
    nid = 1;
  let steps = [],
    heat = new Float32Array(COLS * ROWS),
    curve = [],
    pend = false,
    playing = null;

  /* ---------- Астрономія сонця ---------- */
  function sun(d, t) {
    const dec =
      ((23.44 * Math.PI) / 180) * Math.sin((2 * Math.PI * (284 + d)) / 365);
    const hh = ((t - 12) * 15 * Math.PI) / 180;
    const se =
      Math.sin(LAT) * Math.sin(dec) +
      Math.cos(LAT) * Math.cos(dec) * Math.cos(hh);
    const el = Math.asin(se);
    let c =
      (Math.sin(dec) - se * Math.sin(LAT)) / (Math.cos(el) * Math.cos(LAT));
    c = Math.max(-1, Math.min(1, c));
    let az = Math.acos(c);
    if (hh > 0) az = 2 * Math.PI - az;
    return { el, az };
  }
  /* ---------- Геометрія тіней ---------- */
  function hull(p) {
    p = p.slice().sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const cr = (o, a, b) =>
      (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
    const lo = [],
      up = [];
    for (const q of p) {
      while (lo.length > 1 && cr(lo[lo.length - 2], lo[lo.length - 1], q) <= 0)
        lo.pop();
      lo.push(q);
    }
    for (let i = p.length - 1; i >= 0; i--) {
      const q = p[i];
      while (up.length > 1 && cr(up[up.length - 2], up[up.length - 1], q) <= 0)
        up.pop();
      up.push(q);
    }
    lo.pop();
    up.pop();
    return lo.concat(up);
  }
  function corners(o, dx = 0, dy = 0) {
    const w = (o.s * S) / 2,
      l = (o.l * S) / 2;
    return [
      [o.x - w + dx, o.y - l + dy],
      [o.x + w + dx, o.y - l + dy],
      [o.x + w + dx, o.y + l + dy],
      [o.x - w + dx, o.y + l + dy],
    ];
  }
  function poly(o, sx, sy) {
    if (o.t === "tree") {
      const r = (o.s * S) / 2,
        pts = [[o.x, o.y]],
        zl = Math.max(1, o.h - o.s);
      for (const z of [zl, o.h])
        for (let i = 0; i < 14; i++) {
          const a = (i / 14) * Math.PI * 2;
          pts.push([
            o.x + Math.cos(a) * r + sx * z,
            o.y + Math.sin(a) * r + sy * z,
          ]);
        }
      return hull(pts);
    }
    if (o.t === "building")
      return hull(corners(o).concat(corners(o, sx * o.h, sy * o.h)));
    return hull(
      corners(o, sx * o.h, sy * o.h).concat(
        corners(o, sx * (o.h - 0.3), sy * (o.h - 0.3)),
      ),
    );
  }
  function hullsFor(s) {
    const k = 1 / Math.tan(s.el),
      sx = -Math.sin(s.az) * k * S,
      sy = Math.cos(s.az) * k * S;
    return objs
      .filter((o) => o.t !== "sensor")
      .map((o) => {
        const p = poly(o, sx, sy);
        let x0 = 1e9,
          y0 = 1e9,
          x1 = -1e9,
          y1 = -1e9;
        for (const q of p) {
          x0 = Math.min(x0, q[0]);
          y0 = Math.min(y0, q[1]);
          x1 = Math.max(x1, q[0]);
          y1 = Math.max(y1, q[1]);
        }
        return { p, b: [x0, y0, x1, y1] };
      });
  }
  function inHull(h, x, y) {
    let f = 0;
    for (let i = 0; i < h.length; i++) {
      const a = h[i],
        b = h[(i + 1) % h.length];
      const c = (b[0] - a[0]) * (y - a[1]) - (b[1] - a[1]) * (x - a[0]);
      if (c < 0) f |= 1;
      else if (c > 0) f |= 2;
      if (f === 3) return false;
    }
    return true;
  }
  function inAny(hs, x, y) {
    for (const q of hs) {
      const b = q.b;
      if (x >= b[0] && x <= b[2] && y >= b[1] && y <= b[3] && inHull(q.p, x, y))
        return true;
    }
    return false;
  }

  /* ---------- Розрахунок доби ---------- */
  function recompute() {
    steps = [];
    for (let t = 4; t <= 22.01; t += 0.5) {
      const s = sun(day, t);
      if (s.el >= MINEL) steps.push({ t, s, h: hullsFor(s) });
    }
    heat.fill(0);
    curve = [];
    for (const st of steps) {
      let c = 0;
      for (let j = 0; j < ROWS; j++)
        for (let i = 0; i < COLS; i++) {
          if (inAny(st.h, i * CELL + CELL / 2, j * CELL + CELL / 2)) {
            heat[j * COLS + i] += 0.5;
            c++;
          }
        }
      curve.push(c / (COLS * ROWS));
    }
  }
  function metrics() {
    const dh = steps.length * 0.5 || 1;
    let sum = 0,
      comf = 0;
    for (const v of heat) {
      sum += v;
      if (v >= dh * 0.5) comf++;
    }
    let mi = 0;
    curve.forEach((v, i) => {
      if (v < curve[mi]) mi = i;
    });
    return {
      avg: (sum / heat.length / dh) * 100,
      comf: (comf / heat.length) * 100,
      worst: steps[mi] ? steps[mi].t : null,
      dh,
    };
  }
  const fmt = (t) => {
    const h = Math.floor(t),
      m = Math.round((t - h) * 60);
    return String(h).padStart(2, "0") + ":" + String(m).padStart(2, "0");
  };
  function dt(v, u) {
    return (v >= 0 ? "+" : "") + v.toFixed(1) + u;
  }

  /* ---------- Малювання ---------- */
  function draw() {
    const s = sun(day, time),
      active = s.el >= MINEL;
    ctx.clearRect(0, 0, W, H);
    ctx.fillStyle = css("--ground");
    ctx.fillRect(0, 0, W, H);
    ctx.fillStyle = css("--lawn");
    [
      [30, 30, 230, 150],
      [540, 300, 230, 190],
      [300, 400, 180, 90],
    ].forEach((r) => {
      ctx.beginPath();
      ctx.roundRect(r[0], r[1], r[2], r[3], 26);
      ctx.fill();
    });
    ctx.strokeStyle = "rgba(128,120,170,.18)";
    ctx.lineWidth = 1;
    ctx.beginPath();
    for (let x = 0; x <= W; x += 50) {
      ctx.moveTo(x, 0);
      ctx.lineTo(x, H);
    }
    for (let y = 0; y <= H; y += 50) {
      ctx.moveTo(0, y);
      ctx.lineTo(W, y);
    }
    ctx.stroke();
    if (showHeat && steps.length) {
      const dh = steps.length * 0.5,
        hot = css("--hot"),
        cool = css("--cool");
      for (let j = 0; j < ROWS; j++)
        for (let i = 0; i < COLS; i++) {
          const v = heat[j * COLS + i] / dh;
          ctx.globalAlpha = 0.18 + 0.5 * Math.abs(v - 0.5) * 2 * 0.9;
          ctx.fillStyle = v > 0.5 ? cool : hot;
          ctx.fillRect(i * CELL, j * CELL, CELL, CELL);
        }
      ctx.globalAlpha = 1;
    }
    let hs = [];
    if (active) {
      hs = hullsFor(s);
      sctx.clearRect(0, 0, W, H);
      sctx.fillStyle = "#120a2e";
      for (const q of hs) {
        sctx.beginPath();
        q.p.forEach((p, i) =>
          i ? sctx.lineTo(p[0], p[1]) : sctx.moveTo(p[0], p[1]),
        );
        sctx.closePath();
        sctx.fill();
      }
      ctx.globalAlpha = 0.5;
      ctx.drawImage(sh, 0, 0, W, H);
      ctx.globalAlpha = 1;
    }
    objs
      .slice()
      .sort((a, b) => a.h - b.h)
      .forEach((o) => drawObj(o, hs, active));
    if (!active) {
      ctx.fillStyle = "rgba(10,6,40,.5)";
      ctx.fillRect(0, 0, W, H);
    }
    // компас
    const cx = W - 48,
      cy = 48;
    ctx.fillStyle = "rgba(20,14,50,.6)";
    ctx.beginPath();
    ctx.arc(cx, cy, 34, 0, 7);
    ctx.fill();
    ctx.fillStyle = "#fff";
    ctx.font = "700 12px Onest,sans-serif";
    ctx.textAlign = "center";
    ctx.fillText("Пн", cx, cy - 20);
    if (active) {
      ctx.fillStyle = "#ffb347";
      ctx.beginPath();
      ctx.arc(cx + Math.sin(s.az) * 17, cy - Math.cos(s.az) * 17 + 3, 8, 0, 7);
      ctx.fill();
    }
    $("#clock").textContent = fmt(time);
    $("#sunTxt").textContent = active
      ? "Сонце " + Math.round((s.el * 180) / Math.PI) + "° над обрієм"
      : "Сонце за обрієм";
    const di = steps.findIndex((x) => Math.abs(x.t - time) < 0.26);
    $("#nowTxt").textContent =
      active && di >= 0
        ? "Зараз у тіні " + Math.round(curve[di] * 100) + "% території."
        : "Сонце низько або за обрієм, тіні не рахуємо.";
    chart();
    sensors();
  }
  function drawObj(o, hs, active) {
    const x = o.x,
      y = o.y,
      ac = css("--accent");
    if (o.t === "tree") {
      const r = (o.s * S) / 2;
      ctx.fillStyle = css("--leaf");
      ctx.beginPath();
      ctx.arc(x, y, r, 0, 7);
      ctx.fill();
      ctx.fillStyle = "rgba(255,255,255,.18)";
      ctx.beginPath();
      ctx.arc(x - r * 0.28, y - r * 0.28, r * 0.55, 0, 7);
      ctx.fill();
      ctx.fillStyle = "#6b4a34";
      ctx.beginPath();
      ctx.arc(x, y, 3, 0, 7);
      ctx.fill();
    } else if (o.t === "building" || o.t === "awning") {
      const w = o.s * S,
        l = o.l * S;
      if (o.t === "building") {
        ctx.fillStyle = css("--bld");
        ctx.fillRect(x - w / 2, y - l / 2, w, l);
        ctx.fillStyle = css("--bld2");
        ctx.fillRect(x - w / 2 + 5, y - l / 2 + 5, w - 10, l - 10);
      } else {
        ctx.save();
        ctx.beginPath();
        ctx.rect(x - w / 2, y - l / 2, w, l);
        ctx.clip();
        ctx.fillStyle = css("--rose");
        ctx.fillRect(x - w / 2, y - l / 2, w, l);
        ctx.fillStyle = "rgba(255,255,255,.75)";
        for (let i = -l; i < w; i += 14) {
          ctx.beginPath();
          ctx.moveTo(x - w / 2 + i, y - l / 2);
          ctx.lineTo(x - w / 2 + i + 7, y - l / 2);
          ctx.lineTo(x - w / 2 + i + 7 + l, y + l / 2);
          ctx.lineTo(x - w / 2 + i + l, y + l / 2);
          ctx.fill();
        }
        ctx.restore();
      }
      ctx.fillStyle = "#fff";
      ctx.font = "700 12px Onest,sans-serif";
      ctx.textAlign = "center";
      ctx.shadowColor = "rgba(0,0,0,.6)";
      ctx.shadowBlur = 3;
      ctx.fillText(o.h + " м", x, y + 4);
      ctx.shadowBlur = 0;
    } else {
      const sh2 = active && inAny(hs, x, y);
      ctx.fillStyle = sh2 ? css("--cool") : css("--sun");
      ctx.beginPath();
      ctx.arc(x, y, 9, 0, 7);
      ctx.fill();
      ctx.strokeStyle = "#fff";
      ctx.lineWidth = 2;
      ctx.stroke();
      ctx.fillStyle = "#fff";
      ctx.font = "700 11px Onest,sans-serif";
      ctx.textAlign = "center";
      ctx.fillText(sh2 ? "тінь" : "сонце", x, y + 22);
    }
    if (o === sel) {
      ctx.strokeStyle = ac;
      ctx.lineWidth = 2;
      ctx.setLineDash([6, 4]);
      ctx.beginPath();
      if (o.t === "tree" || o.t === "sensor")
        ctx.arc(x, y, (o.t === "tree" ? (o.s * S) / 2 : 9) + 5, 0, 7);
      else
        ctx.rect(
          x - (o.s * S) / 2 - 4,
          y - (o.l * S) / 2 - 4,
          o.s * S + 8,
          o.l * S + 8,
        );
      ctx.stroke();
      ctx.setLineDash([]);
    }
  }
  function sensors() {
    const ul = $("#sensorList");
    ul.innerHTML = "";
    objs
      .filter((o) => o.t === "sensor")
      .forEach((o, i) => {
        let hrs = 0;
        for (const st of steps) if (inAny(st.h, o.x, o.y)) hrs += 0.5;
        const li = document.createElement("li");
        li.innerHTML =
          "<span>Лавка " +
          (i + 1) +
          "</span><b>" +
          hrs.toFixed(1) +
          " з " +
          (steps.length * 0.5).toFixed(1) +
          " год у тіні</b>";
        ul.appendChild(li);
      });
  }
  function chart() {
    const c = $("#chart"),
      g = c.getContext("2d"),
      w = c.width,
      h = c.height,
      px = 26,
      py = 10;
    g.clearRect(0, 0, w, h);
    const X = (t) => px + ((t - 4) / 18) * (w - px - 6),
      Y = (v) => h - 18 - v * (h - 18 - py);
    g.font = "11px Onest,sans-serif";
    g.fillStyle = css("--mut");
    g.strokeStyle = css("--line");
    g.lineWidth = 1;
    g.textAlign = "center";
    for (let t = 4; t <= 22; t += 6) {
      g.fillText(t + ":00", X(t), h - 4);
    }
    [0, 0.5, 1].forEach((v) => {
      g.beginPath();
      g.moveTo(px, Y(v));
      g.lineTo(w - 6, Y(v));
      g.stroke();
      g.textAlign = "right";
      g.fillText(v * 100 + "%", px - 4, Y(v) + 4);
    });
    const line = (ts, vs, col, dash) => {
      if (!ts.length) return;
      g.strokeStyle = col;
      g.lineWidth = 2.5;
      g.setLineDash(dash || []);
      g.beginPath();
      ts.forEach((t, i) =>
        i ? g.lineTo(X(t), Y(vs[i])) : g.moveTo(X(t), Y(vs[i])),
      );
      g.stroke();
      g.setLineDash([]);
    };
    if (base) line(base.ts, base.curve, css("--mut"), [5, 4]);
    line(
      steps.map((s) => s.t),
      curve,
      css("--accent"),
    );
    g.strokeStyle = css("--sun");
    g.lineWidth = 2;
    g.beginPath();
    g.moveTo(X(time), py);
    g.lineTo(X(time), h - 18);
    g.stroke();
  }
  /* ---------- Метрики та статистика ---------- */
  function stats() {
    const m = metrics();
    $("#sAvg").textContent = Math.round(m.avg) + "%";
    $("#sComf").textContent = Math.round(m.comf) + "%";
    $("#sWorst").textContent = m.worst == null ? "–" : fmt(m.worst);
    $("#dAvg").textContent = base ? dt(m.avg - base.m.avg, " в.п.") : "";
    $("#dComf").textContent = base ? dt(m.comf - base.m.comf, " в.п.") : "";
    $("#dAvg").style.color = $("#dComf").style.color = base
      ? "var(--accent)"
      : "";
  }

  /* ---------- Оновлення ---------- */
  function dirty() {
    if (pend) return;
    pend = true;
    requestAnimationFrame(() => {
      pend = false;
      recompute();
      stats();
      draw();
      save();
    });
  }
  function save() {
    try {
      localStorage.setItem("shadelab", JSON.stringify({ objs, day }));
    } catch (e) {}
  }
  function load() {
    try {
      const d = JSON.parse(localStorage.getItem("shadelab") || "null");
      if (d && Array.isArray(d.objs)) {
        objs = d.objs;
        day = d.day || 172;
        nid = objs.reduce((m, o) => Math.max(m, o.id || 0), 0) + 1;
        return true;
      }
    } catch (e) {}
    return false;
  }

  /* ---------- Взаємодія з полотном та інтерфейсом ---------- */
  function pos(e) {
    const r = cv.getBoundingClientRect();
    return [
      ((e.clientX - r.left) * W) / r.width,
      ((e.clientY - r.top) * H) / r.height,
    ];
  }
  function hit(x, y) {
    for (let i = objs.length - 1; i >= 0; i--) {
      const o = objs[i];
      if (o.t === "tree") {
        if (Math.hypot(x - o.x, y - o.y) <= (o.s * S) / 2) return o;
      } else if (o.t === "sensor") {
        if (Math.hypot(x - o.x, y - o.y) <= 14) return o;
      } else if (
        Math.abs(x - o.x) <= (o.s * S) / 2 &&
        Math.abs(y - o.y) <= (o.l * S) / 2
      )
        return o;
    }
    return null;
  }
  let drag = null;
  cv.addEventListener("pointerdown", (e) => {
    const [x, y] = pos(e);
    cv.setPointerCapture(e.pointerId);
    if (tool === "erase") {
      const o = hit(x, y);
      if (o) {
        objs = objs.filter((q) => q !== o);
        if (sel === o) sel = null;
        ins();
        dirty();
      }
      return;
    }
    if (tool === "select") {
      const o = hit(x, y);
      sel = o;
      ins();
      if (o) drag = { dx: o.x - x, dy: o.y - y };
      draw();
      return;
    }
    const o = Object.assign({ id: nid++, t: tool, x, y }, DEF[tool]);
    objs.push(o);
    sel = o;
    drag = { dx: 0, dy: 0 };
    ins();
    dirty();
  });
  cv.addEventListener("pointermove", (e) => {
    if (!drag || !sel) return;
    const [x, y] = pos(e);
    sel.x = Math.max(0, Math.min(W, x + drag.dx));
    sel.y = Math.max(0, Math.min(H, y + drag.dy));
    dirty();
  });
  ["pointerup", "pointercancel"].forEach((n) =>
    cv.addEventListener(n, () => {
      if (drag && tool !== "select") {
        setTool("select");
      }
      drag = null;
    }),
  );
  window.addEventListener("keydown", (e) => {
    if (
      (e.key === "Delete" || e.key === "Backspace") &&
      sel &&
      document.activeElement.tagName !== "INPUT"
    ) {
      delSel();
    }
  });
  function delSel() {
    if (!sel) return;
    objs = objs.filter((q) => q !== sel);
    sel = null;
    ins();
    dirty();
  }
  $("#del").onclick = delSel;
  function setTool(t) {
    tool = t;
    document
      .querySelectorAll("[data-tool]")
      .forEach((b) => b.classList.toggle("on", b.dataset.tool === t));
    cv.style.cursor = t === "select" ? "default" : "crosshair";
  }
  document
    .querySelectorAll("[data-tool]")
    .forEach((b) => (b.onclick = () => setTool(b.dataset.tool)));

  function ins() {
    const box = $("#ins");
    if (!sel || sel.t === "sensor") {
      box.hidden = !sel;
      if (sel) {
        $("#insTitle").textContent = "Лавка-датчик";
        $("#f_h").closest(".row").hidden = true;
        $("#rs").hidden = true;
        $("#rl").hidden = true;
      }
      return;
    }
    box.hidden = false;
    $("#insTitle").textContent = NAME[sel.t];
    const f = $("#f_h");
    f.closest(".row").hidden = false;
    const rng = { tree: [2, 20], building: [3, 40], awning: [2, 6] }[sel.t];
    f.min = rng[0];
    f.max = rng[1];
    f.step = 0.5;
    f.value = sel.h;
    $("#o_h").textContent = sel.h + " м";
    $("#lbl_s").textContent =
      sel.t === "tree" ? "Діаметр крони, м" : "Ширина, м";
    $("#f_s").value = sel.s;
    $("#o_s").textContent = sel.s + " м";
    $("#rs").hidden = false;
    $("#rl").hidden = sel.t === "tree";
    $("#f_l").value = sel.l;
    $("#o_l").textContent = sel.l + " м";
  }
  ["h", "s", "l"].forEach(
    (k) =>
      ($("#f_" + k).oninput = (e) => {
        if (!sel) return;
        sel[k] = +e.target.value;
        if (sel.t === "tree") sel.l = sel.s;
        ins();
        dirty();
      }),
  );

  $("#time").oninput = (e) => {
    time = +e.target.value;
    draw();
  };
  $("#day").oninput = (e) => {
    day = +e.target.value;
    dayLabel();
    dirty();
  };
  document.querySelectorAll("[data-day]").forEach(
    (b) =>
      (b.onclick = () => {
        day = +b.dataset.day;
        $("#day").value = day;
        dayLabel();
        dirty();
      }),
  );
  function dayLabel() {
    $("#dayTxt").textContent = new Date(2026, 0, day).toLocaleDateString(
      "uk-UA",
      { day: "numeric", month: "long" },
    );
  }
  $("#play").onclick = () => {
    if (playing) {
      clearInterval(playing);
      playing = null;
      $("#play").textContent = "▶ Пуск";
      return;
    }
    $("#play").textContent = "❚❚ Стоп";
    playing = setInterval(() => {
      time += 0.1;
      if (time > 22) time = 4;
      $("#time").value = time;
      draw();
    }, 50);
  };
  $("#heatBtn").onclick = (e) => {
    showHeat = !showHeat;
    e.currentTarget.classList.toggle("on", showHeat);
    e.currentTarget.setAttribute("aria-pressed", showHeat);
    draw();
  };
  $("#snap").onclick = () => {
    base = { ts: steps.map((s) => s.t), curve: curve.slice(), m: metrics() };
    stats();
    draw();
  };
  $("#clearBase").onclick = () => {
    base = null;
    stats();
    draw();
  };

  /* ---------- Сценарії та завантаження ---------- */
  const T = (x, y, s, h) => ({ t: "tree", x: x * S, y: y * S, s, l: s, h });
  const B = (x, y, s, l, h) => ({ t: "building", x: x * S, y: y * S, s, l, h });
  const A = (x, y, s, l, h) => ({ t: "awning", x: x * S, y: y * S, s, l, h });
  const P = (x, y) => ({ t: "sensor", x: x * S, y: y * S, s: 1, l: 1, h: 0 });
  const PRESETS = {
    empty: () => [P(40, 26)],
    school: () => [
      B(14, 10, 22, 10, 14),
      B(66, 38, 16, 9, 10),
      T(40, 14, 6, 9),
      T(30, 34, 5, 7),
      T(52, 22, 6, 10),
      T(22, 42, 4, 6),
      A(40, 30, 9, 4, 3),
      P(36, 20),
      P(26, 38),
      P(60, 20),
    ],
    grove: () => {
      const a = [P(40, 26), P(20, 12), P(62, 40)];
      for (let i = 0; i < 14; i++)
        a.push(
          T(8 + ((i * 37) % 66), 6 + ((i * 23) % 42), 4 + (i % 3), 6 + (i % 5)),
        );
      return a;
    },
    block: () => [
      B(12, 12, 14, 12, 24),
      B(34, 12, 12, 12, 32),
      B(56, 12, 14, 12, 18),
      B(12, 38, 14, 12, 12),
      B(40, 40, 18, 10, 22),
      P(23, 26),
      P(46, 26),
      P(66, 28),
    ],
  };
  document.querySelectorAll("[data-preset]").forEach(
    (b) =>
      (b.onclick = () => {
        objs = PRESETS[b.dataset.preset]().map((o) =>
          Object.assign({ id: nid++ }, o),
        );
        sel = null;
        ins();
        dirty();
      }),
  );

  /* ---------- Початкове завантаження ---------- */
  if (!load()) {
    objs = PRESETS.school().map((o) => Object.assign({ id: nid++ }, o));
  }
  $("#day").value = day;
  dayLabel();
  ins();
  recompute();
  stats();
  draw();
  matchMedia("(prefers-color-scheme: dark)").addEventListener("change", draw);
})();
