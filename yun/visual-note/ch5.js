/* =========================================================
   Chapter 5 — Trajectory Generation (Lecture 5)
   ========================================================= */
(function () {
  'use strict';
  const R = String.raw;
  const { I, mul, rx, rz, tr, app, R3, p3, fromRp, add, sub, scl, norm, atan2d, f, D } = M;
  const K = window.KIN;
  const { robot, fr, pt, vec, ln, arc, body, drop } = K;
  const X = [1, 0, 0], Z = [0, 0, 1], O = [0, 0, 0];
  const c = a => Math.cos(a * D), s = a => Math.sin(a * D);
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const sgn = x => (x > 0 ? 1 : x < 0 ? -1 : 0);
  const base = rx(90);
  const wipe = S => { ['frames', 'pts', 'vecs', 'lines', 'arcs', 'bodies'].forEach(k => drop(S, k)); S.watch = null; };
  const row = a => ({ al: 0, a, d: 0, th: 0, type: 'R' });
  const ls = items => `<ul class="ls">${items.map(x => `<li>${x}</li>`).join('')}</ul>`;
  const pick = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
  const n2 = x => f(x, 2), n3 = x => f(x, 3);
  const pm = x => (x < 0 ? '- ' + f(-x, 3) : '+ ' + f(x, 3));

  /* ---------- trajectories: ev(t) → [θ, θ̇, θ̈] ---------- */
  function cubic(th0, thf, tf, v0, vf) {
    v0 = v0 || 0; vf = vf || 0;
    const d = thf - th0, a2 = 3 * d / tf ** 2 - 2 * v0 / tf - vf / tf, a3 = -2 * d / tf ** 3 + (vf + v0) / tf ** 2;
    return { T: tf, a: [th0, v0, a2, a3], ev: t => [th0 + v0 * t + a2 * t * t + a3 * t ** 3, v0 + 2 * a2 * t + 3 * a3 * t * t, 2 * a2 + 6 * a3 * t] };
  }
  const poly = (a, T) => ({ T, a, ev: t => [a.reduce((sm, k, i) => sm + k * t ** i, 0), a.reduce((sm, k, i) => sm + (i ? i * k * t ** (i - 1) : 0), 0), a.reduce((sm, k, i) => sm + (i > 1 ? i * (i - 1) * k * t ** (i - 2) : 0), 0)] });
  const quad = (p0, v0, a, T) => ({ T, ev: t => [p0 + v0 * t + 0.5 * a * t * t, v0 + a * t, a] });
  function pw(segs, extra) {
    let acc = 0; segs.forEach(g => { g.t0 = acc; acc += g.T; });
    return Object.assign({ T: acc, segs, vl: segs.slice(1).map(g => g.t0), ev: t => { const g = segs.find(h => t <= h.t0 + h.T + 1e-9) || segs[segs.length - 1]; return g.ev(t - g.t0); } }, extra || {});
  }
  // chain of quadratic pieces given [duration, acceleration], starting at p0 with zero velocity
  function chainQ(p0, pieces, extra) {
    let p = p0, v = 0; const segs = [];
    pieces.forEach(([T, a]) => { if (T <= 1e-9) return; segs.push(quad(p, v, a, T)); p += v * T + 0.5 * a * T * T; v += a * T; });
    return pw(segs, extra);
  }
  // single LPB
  function lpb(th0, thf, tf, A) {
    const d = thf - th0, sg = sgn(d) || 1, Dm = Math.abs(d), Amin = 4 * Dm / tf ** 2, ok = A >= Amin - 1e-9;
    const a = Math.max(A, Amin), tb = tf / 2 - Math.sqrt(Math.max(0, a * a * tf * tf - 4 * a * Dm)) / (2 * a);
    const tr2 = chainQ(th0, [[tb, sg * a], [tf - 2 * tb, 0], [tb, -sg * a]]);
    return Object.assign(tr2, { tb, Amin, ok, V: sg * a * tb, thb: th0 + 0.5 * sg * a * tb * tb });
  }
  // LPB through via points (Craig): th[n], td[n-1] (durations between points), |θ̈| = A
  function lpbVia(th, td, A) {
    const n = th.length, acc = [], tb = [], vel = [], lin = [];
    acc[0] = (sgn(th[1] - th[0]) || 1) * A;
    tb[0] = td[0] - Math.sqrt(Math.max(0, td[0] ** 2 - 2 * (th[1] - th[0]) / acc[0]));
    vel[0] = (th[1] - th[0]) / (td[0] - 0.5 * tb[0]);
    const m = n - 1;
    acc[m] = (sgn(th[m - 1] - th[m]) || 1) * A;
    tb[m] = td[m - 1] - Math.sqrt(Math.max(0, td[m - 1] ** 2 + 2 * (th[m] - th[m - 1]) / acc[m]));
    vel[m - 1] = (th[m] - th[m - 1]) / (td[m - 1] - 0.5 * tb[m]);
    for (let j = 1; j < m - 1; j++) vel[j] = (th[j + 1] - th[j]) / td[j];
    for (let k = 1; k < m; k++) { acc[k] = (sgn(vel[k] - vel[k - 1]) || 1) * A; tb[k] = (vel[k] - vel[k - 1]) / acc[k]; }
    for (let j = 0; j < m; j++) lin[j] = td[j] - (j === 0 ? tb[0] : 0.5 * tb[j]) - (j === m - 1 ? tb[m] : 0.5 * tb[j + 1]);
    const pieces = [];
    for (let k = 0; k <= m; k++) { pieces.push([tb[k], acc[k]]); if (k < m) pieces.push([Math.max(0, lin[k]), 0]); }
    let tt = 0; const marks = th.map((v, i) => { const r = { t: tt, p: v }; if (i < m) tt += td[i]; return r; });
    const trj = chainQ(th[0], pieces, { marks });
    return Object.assign(trj, { acc, tb, vel, lin, ok: lin.every(x => x >= -1e-6) && tb.every(x => x >= -1e-9 && isFinite(x)) });
  }
  // cubic splines through via points with heuristic via velocities
  function viaCubic(th, td) {
    const n = th.length, v = th.map(() => 0);
    for (let k = 1; k < n - 1; k++) { const a = (th[k] - th[k - 1]) / td[k - 1], b = (th[k + 1] - th[k]) / td[k]; v[k] = sgn(a) === sgn(b) && a !== 0 ? (a + b) / 2 : 0; }
    let tt = 0; const marks = th.map((p, i) => { const r = { t: tt, p }; if (i < n - 1) tt += td[i]; return r; });
    const segs = td.map((T, i) => cubic(th[i], th[i + 1], T, v[i], v[i + 1]));
    return pw(segs, { v, marks, segs2: segs });
  }
  // two cubics with continuous acceleration, each of duration tf (Craig 7.3 / slide 17)
  function twoCubic(t0, tv, tg, tf) {
    const a1 = [t0, 0, (12 * tv - 3 * tg - 9 * t0) / (4 * tf * tf), (-8 * tv + 3 * tg + 5 * t0) / (4 * tf ** 3)];
    const a2 = [tv, (3 * tg - 3 * t0) / (4 * tf), (-12 * tv + 6 * tg + 6 * t0) / (4 * tf * tf), (8 * tv - 5 * tg - 3 * t0) / (4 * tf ** 3)];
    return pw([poly(a1, tf), poly(a2, tf)], { a1, a2, marks: [{ t: 0, p: t0 }, { t: tf, p: tv }, { t: 2 * tf, p: tg }] });
  }
  function quintic(t0, tf, T, v0, vf, ac0, acf) {
    v0 = v0 || 0; vf = vf || 0; ac0 = ac0 || 0; acf = acf || 0;
    const a = [t0, v0, ac0 / 2,
      (20 * tf - 20 * t0 - (8 * vf + 12 * v0) * T - (3 * ac0 - acf) * T * T) / (2 * T ** 3),
      (30 * t0 - 30 * tf + (14 * vf + 16 * v0) * T + (3 * ac0 - 2 * acf) * T * T) / (2 * T ** 4),
      (12 * tf - 12 * t0 - (6 * vf + 6 * v0) * T - (ac0 - acf) * T * T) / (2 * T ** 5)];
    return poly(a, T);
  }

  /* ---------- θ, θ̇, θ̈ plot (SVG, in the viewport card) ---------- */
  function plot(trj, t, o) {
    o = o || {};
    const W = 330, H = 46, G = 17, ML = 38, MR = 6, N = 260, T = trj.T, pre = 0.06 * T;
    const t0 = -pre, t1 = T + pre, Xs = tt => ML + (W - ML - MR) * (tt - t0) / (t1 - t0);
    const end = trj.ev(T), beg = trj.ev(0);
    const ev = tt => (tt < 0 ? [beg[0], 0, 0] : tt > T ? [end[0], 0, 0] : trj.ev(tt));
    const ts = []; for (let i = 0; i <= N; i++) ts.push(t0 + (t1 - t0) * i / N);
    [0, T].concat(trj.vl || []).forEach(x => { ts.push(x - 1e-6, x + 1e-6); });
    ts.sort((a, b) => a - b);
    const vals = ts.map(ev), cur = ev(clamp(t, 0, T));
    const names = ['θ', 'θ̇', 'θ̈'], units = ['°', '°/s', '°/s²'], cols = ['var(--acc)', 'var(--j1)', 'var(--j2)'];
    const HT = 3 * (H + G) + 10;
    let g = `<svg width="${W}" height="${HT}" viewBox="0 0 ${W} ${HT}" style="display:block;max-width:100%;margin-top:2px" font-family="var(--f-mono)">`;
    for (let k = 0; k < 3; k++) {
      const d = vals.map(v => v[k]).concat((o.extra || []).flatMap(e => e.vals ? e.vals.map(v => v[k]) : []));
      let lo = Math.min(...d, 0), hi = Math.max(...d, 0); if (hi - lo < 1e-6) { hi += 1; lo -= 1; }
      const pad = (hi - lo) * 0.1, y0 = k * (H + G) + G - 3, Y = v => y0 + H - (v - (lo - pad)) / (hi - lo + 2 * pad) * H;
      g += `<rect x="${ML}" y="${y0}" width="${W - ML - MR}" height="${H}" fill="none" stroke="var(--line)"/>`;
      if (lo < 0 && hi > 0) g += `<line x1="${ML}" x2="${W - MR}" y1="${Y(0).toFixed(1)}" y2="${Y(0).toFixed(1)}" stroke="var(--grid2)" stroke-dasharray="2 2"/>`;
      [0, T].concat(trj.vl || []).forEach(x => { g += `<line x1="${Xs(x).toFixed(1)}" x2="${Xs(x).toFixed(1)}" y1="${y0}" y2="${y0 + H}" stroke="var(--grid2)" stroke-dasharray="${x === 0 || x === T ? '' : '3 3'}"/>`; });
      (o.extra || []).forEach(e => {
        const pth = e.ts.map((tt, i) => `${i ? 'L' : 'M'}${Xs(tt).toFixed(1)},${Y(e.vals[i][k]).toFixed(1)}`).join('');
        g += `<path d="${pth}" fill="none" stroke="${e.c || 'var(--mute)'}" stroke-width="1.3" stroke-dasharray="4 3"/>`;
      });
      const pth = ts.map((tt, i) => `${i ? 'L' : 'M'}${Xs(tt).toFixed(1)},${Y(vals[i][k]).toFixed(1)}`).join('');
      g += `<path d="${pth}" fill="none" stroke="${cols[k]}" stroke-width="1.9"/>`;
      if (k === 0 && trj.marks) trj.marks.forEach(m => { g += `<circle cx="${Xs(m.t).toFixed(1)}" cy="${Y(m.p).toFixed(1)}" r="3.2" fill="var(--panel2)" stroke="var(--ink)" stroke-width="1.2"/>`; });
      g += `<text x="${ML - 4}" y="${y0 + 8}" text-anchor="end" font-size="9" fill="var(--mute)">${f(hi, 1)}</text><text x="${ML - 4}" y="${y0 + H}" text-anchor="end" font-size="9" fill="var(--mute)">${f(lo, 1)}</text>`;
      g += `<text x="${ML + 2}" y="${y0 - 3}" font-size="10.5" font-weight="600" fill="${cols[k]}">${names[k]} = ${f(cur[k], 2)} ${units[k]}</text>`;
      const xc = Xs(clamp(t, 0, T)).toFixed(1);
      g += `<line x1="${xc}" x2="${xc}" y1="${y0}" y2="${y0 + H}" stroke="var(--ink)" stroke-opacity=".45"/><circle cx="${xc}" cy="${Y(cur[k]).toFixed(1)}" r="3" fill="${cols[k]}"/>`;
    }
    g += `<text x="${W - MR}" y="${HT - 2}" text-anchor="end" font-size="9.5" fill="var(--mute)">t = ${f(clamp(t, 0, T), 2)} / ${f(T, 2)} s</text>`;
    if (o.legend) g += `<text x="${ML}" y="${HT - 2}" font-size="9.5" fill="var(--mute)">${o.legend}</text>`;
    return `<div class="vh">${o.title || '시간에 따른 관절각 · 속도 · 가속도'}</div>${g}</svg>`;
  }
  const sampled = (trj, T) => { const ts = []; for (let i = 0; i <= 200; i++) ts.push(-0.06 * T + 1.12 * T * i / 200); const b = trj.ev(0), e = trj.ev(trj.T); return { ts, vals: ts.map(tt => (tt < 0 ? [b[0], 0, 0] : tt > trj.T ? [e[0], 0, 0] : trj.ev(tt))) }; };

  /* ---------- 1-link scene ---------- */
  const LL = 1.3, rows1 = [row(0)];
  function oneLink(S, th, ghosts, o) {
    wipe(S); o = o || {};
    robot(S, rows1, [th], { base, tool: LL, fs: 0.34, w: 0.08, jr: 0.1, jh: 0.2, noDrag: true, frameOpt: { 0: { size: 0.5 } } });
    (ghosts || []).forEach((gq, i) => {
      robot(S, rows1, [gq.q], { pre: 'g' + i, base, tool: LL, noFrames: true, noLabels: true, op: 0.2, w: 0.08, jr: 0.1, jh: 0.2, noDrag: true });
      pt(S, 'gl' + i, app(base, [(LL + 0.12) * c(gq.q), (LL + 0.12) * s(gq.q), 0]), gq.label, { c: gq.c || 'mute', r: 0.01 });
    });
    if (o.from != null && Math.abs(th - o.from) > 0.5) arc(S, 'sw', { f: 'F0', c: [0, 0, 0.02], n: Z, u: [c(o.from), s(o.from), 0], ang: th - o.from, r: 0.55, col: 'acc', label: 'θ(t)' });
  }
  // play button for live steps (param u in %, real-time playback)
  const player = dur => (el, p, refresh) => {
    const b = document.createElement('button'); b.className = 'btn sm'; b.textContent = '▶ 재생 (실제 시간)'; b.style.marginTop = '4px';
    el.appendChild(b);
    let raf = 0;
    b.onclick = () => {
      if (raf) { cancelAnimationFrame(raf); raf = 0; b.textContent = '▶ 이어서 재생'; return; }
      const T = Math.max(0.5, typeof dur === 'function' ? dur(p) : dur), t0 = performance.now(), u0 = p.u >= 99.9 ? 0 : p.u;
      b.textContent = '■ 멈춤';
      const tick = now => {
        if (!b.isConnected) return;
        p.u = Math.min(100, u0 + (now - t0) / (T * 1000) * 100); refresh();
        if (p.u < 100) raf = requestAnimationFrame(tick); else { raf = 0; b.textContent = '▶ 처음부터 다시'; }
      };
      raf = requestAnimationFrame(tick);
    };
  };
  const uParam = { id: 'u', label: R`\(t\)`, min: 0, max: 100, step: 0.5, val: 0, unit: '%' };

  const sections = [];
  const sec = o => sections.push(o);
  const VIEW1 = { pos: [0.45, -5.8, 1.3], target: [0.45, 0, 0.62] };

  /* ================= 5.1 Path vs trajectory ================= */
  {
    const Lc = [1.0, 0.8], qA = [-10, 70], qB = [100, 40];
    const fk = q => [Lc[0] * c(q[0]) + Lc[1] * c(q[0] + q[1]), Lc[0] * s(q[0]) + Lc[1] * s(q[0] + q[1])];
    const ik = p => { const c2 = clamp((p[0] ** 2 + p[1] ** 2 - Lc[0] ** 2 - Lc[1] ** 2) / (2 * Lc[0] * Lc[1]), -1, 1), s2 = Math.sqrt(1 - c2 * c2); return [atan2d(p[1], p[0]) - atan2d(Lc[1] * s2, Lc[0] + Lc[1] * c2), atan2d(s2, c2)]; };
    const PA = fk(qA), PB = fk(qB), sm = u => 3 * u * u - 2 * u ** 3;
    const qJ = u => [qA[0] + (qB[0] - qA[0]) * sm(u), qA[1] + (qB[1] - qA[1]) * sm(u)];
    const qC = u => ik([PA[0] + (PB[0] - PA[0]) * sm(u), PA[1] + (PB[1] - PA[1]) * sm(u)]);
    const W = p => app(base, [p[0], p[1], 0]);
    const trace = (S, id, qf, col) => { let prev = null; for (let i = 0; i <= 30; i++) { const p = W(fk(qf(i / 30))); if (prev) ln(S, id + i, prev, p, { c: col, dash: false }); prev = p; } };
    const scene = (S, q, lv) => {
      wipe(S);
      robot(S, [row(0), row(Lc[0])], q, { base, tool: Lc[1], fs: 0.3, w: 0.06, jr: 0.08, jh: 0.14, noDrag: true, hide: [1, 2], frameOpt: { 0: { size: 0.45 } } });
      robot(S, [row(0), row(Lc[0])], qA, { pre: 'a', base, tool: Lc[1], noFrames: true, noLabels: true, op: 0.18, w: 0.06, jr: 0.08, jh: 0.14, noDrag: true });
      robot(S, [row(0), row(Lc[0])], qB, { pre: 'b', base, tool: Lc[1], noFrames: true, noLabels: true, op: 0.18, w: 0.06, jr: 0.08, jh: 0.14, noDrag: true });
      pt(S, 'A', W(PA), '시작', { c: 'ink' }); pt(S, 'B', W(PB), '목표', { c: 'ink' });
      if (lv === 1 || lv === 3) trace(S, 'tj', qJ, 'j2');
      if (lv === 2 || lv === 3) trace(S, 'tc', qC, 'acc');
    };
    sec({
      id: 'c5-intro', group: 'lecture', ref: '슬라이드 3–8', title: '5.1 경로와 궤적: 관절 공간 vs 직교 공간',
      view: { pos: [0.3, -5.6, 1.0], target: [0.3, 0, 0.8] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        return {
          init(S) { scene(S, qA, 0); },
          steps: [
            {
              t: '경로(path)와 궤적(trajectory)',
              tex: R`\text{trajectory} = \text{path} + \text{timing}:\qquad \Theta(t),\ \dot\Theta(t),\ \ddot\Theta(t)\quad (0 \le t \le t_f)`,
              html: R`<p>로봇을 시작 자세에서 목표 자세로 옮기는 문제입니다.</p>
              ${ls([R`<b>경로(path)</b>: 거쳐 가는 자세들의 순서 (기하학)`, R`<b>궤적(trajectory)</b>: 경로 + 시간 정보. 각 순간의 위치·속도·가속도`, R`좋은 궤적: 움직임이 부드러움 (속도·가속도가 연속, 급격한 변화 없음)`])}
              <p>사용자는 시작·목표(필요하면 중간 <b>경유점(via point)</b>)와 시간만 정하고, 나머지는 궤적 생성기가 채웁니다.</p>`
            },
            {
              t: '관절 공간 방식 (joint-space scheme)',
              do(S) { scene(S, qA, 1); },
              tex: R`\Theta_A = \text{IK}(P_A),\ \ \Theta_B = \text{IK}(P_B)\ \ \rightarrow\ \ \theta_i(t)\ \text{를 관절마다 부드러운 함수로 보간}`,
              html: R`<p>시작·목표에서만 역기구학을 풀고, 그 사이는 <b>각 관절각</b>을 시간의 부드러운 함수로 잇습니다.</p>
              ${ls([R`계산이 쉬움 (역기구학 두 번)`, R`특이점 문제가 없음`, R`대신 끝점이 지나가는 길(분홍)은 직선이 아니라 곡선`])}`
            },
            {
              t: '직교 공간 방식 (Cartesian-space scheme)',
              do(S) { scene(S, qA, 3); },
              tex: R`P(t) = P_A + (P_B - P_A)\,s(t)\ \ \rightarrow\ \ \Theta(t) = \text{IK}\big(P(t)\big)\ \ \text{매 순간}`,
              html: R`<p>끝점 경로를 직교 좌표에서 직접 정합니다(파란 직선). 매 순간 역기구학을 풀어야 합니다.</p>
              <p>문제가 생길 수 있는 경우:</p>
              ${ls([R`중간 점이 작업공간 밖에 있는 경우 (시작·목표는 닿아도)`, R`경로가 특이점 근처를 지나 관절 속도가 너무 커지는 경우`, R`시작과 목표가 서로 다른 해(자세)로만 닿을 수 있는 경우`])}`
            },
            {
              t: '두 방식 비교 — 재생해 보기',
              live: {
                params: [uParam, { id: 'm', label: '방식', min: 0, max: 1, step: 1, val: 0 }],
                custom: player(3),
                apply(S, p) { const u = p.u / 100, q = p.m ? qC(u) : qJ(u); scene(S, q, 3); },
                vpInfo(p) { const u = p.u / 100, q = p.m ? qC(u) : qJ(u); return `<div class="vh">${p.m ? '직교 공간 (파랑 직선)' : '관절 공간 (분홍 곡선)'}</div><div class="vr">θ₁ = ${n2(q[0])}°, θ₂ = ${n2(q[1])}°</div>`; },
                tex: p => (p.m ? R`\text{직교 공간:}\ \ P(t)\ \text{직선},\ \ \Theta(t) = \text{IK}(P(t))` : R`\text{관절 공간:}\ \ \theta_i(t) = \theta_{i,A} + (\theta_{i,B}-\theta_{i,A})\,s(t)`),
                html: () => R`<p>‘방식’ 슬라이더로 0(관절 공간), 1(직교 공간)을 바꾸고 재생해 보세요. 두 방식 모두 같은 시작·목표 자세에 도달하지만 그 사이의 끝점 경로가 다릅니다.</p>`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 5.2 Cubic polynomial ================= */
  {
    const E = { t0: 15, tf: 75, T: 3 };
    sec({
      id: 'c5-cubic', group: 'lecture', ref: '슬라이드 9–11', title: '5.2 3차 다항식 궤적',
      view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        const cb = cubic(E.t0, E.tf, E.T), a = cb.a;
        const gh = [{ q: E.t0, label: 'θ₀' }, { q: E.tf, label: 'θ_f' }];
        return {
          init(S) { oneLink(S, E.t0, gh); },
          steps: [
            {
              t: '조건 4개 → 계수 4개',
              tex: R`\theta(t) = a_0 + a_1t + a_2t^2 + a_3t^3,\qquad \theta(0) = \theta_0,\ \ \theta(t_f) = \theta_f,\ \ \dot\theta(0) = 0,\ \ \dot\theta(t_f) = 0`,
              html: R`<p>관절 하나가 \(\theta_0\)에서 출발해 \(t_f\)초 뒤 \(\theta_f\)에 정지해야 합니다. 위치 조건 2개 + 속도 조건 2개(정지 → 정지) = 조건 4개입니다.</p>
              <p>미지수가 4개인 <b>3차 다항식(cubic polynomial)</b>이면 딱 맞게 풀립니다.</p>`
            },
            {
              t: '계수 풀기',
              tex: R`\begin{aligned}\theta_0 &= a_0, & 0 &= a_1,\\ \theta_f &= a_0 + a_1t_f + a_2t_f^2 + a_3t_f^3, & 0 &= a_1 + 2a_2t_f + 3a_3t_f^2\end{aligned}\ \Rightarrow\ a_2 = \frac{3}{t_f^2}(\theta_f-\theta_0),\ \ a_3 = -\frac{2}{t_f^3}(\theta_f-\theta_0)`,
              html: R`<p>\(t=0\) 조건에서 \(a_0, a_1\)이 바로 나오고, 나머지 두 식(연립방정식)에서 \(a_2, a_3\)을 구합니다.</p>`
            },
            {
              t: '예제: 15° → 75°, 3초',
              do(S) { oneLink(S, E.tf, gh, { from: E.t0 }); },
              vpInfo: plot(cb, E.T),
              tex: R`\theta(t) = 15 + 20t^2 - 4.44t^3,\qquad \dot\theta(t) = 40t - 13.33t^2,\qquad \ddot\theta(t) = 40 - 26.67t`,
              html: R`<p>\(a_2 = 3\cdot60/9 = 20\), \(a_3 = -2\cdot60/27 = -4.44\).</p>
              ${ls([R`위치: S자 모양`, R`속도: 포물선, 가운데(\(t = t_f/2\))에서 최대 \(1.5(\theta_f-\theta_0)/t_f = 30^\circ/\text{s}\)`, R`가속도: 직선, 시작 \(+40\)에서 끝 \(-40\)\(^\circ/\text{s}^2\). 시작·끝에서 0으로 뚝 끊김(불연속)`])}`
            },
            {
              t: '숫자를 바꿔 재생해 보기',
              live: {
                params: [uParam, { id: 't0', label: R`\(\theta_0\)`, min: -60, max: 150, step: 1, val: E.t0, unit: '°' }, { id: 'tf', label: R`\(\theta_f\)`, min: -60, max: 150, step: 1, val: E.tf, unit: '°' }, { id: 'T', label: R`\(t_f\)`, min: 1, max: 6, step: 0.1, val: E.T, unit: 's' }],
                custom: player(p => p.T),
                apply(S, p) { const cq = cubic(p.t0, p.tf, p.T); oneLink(S, cq.ev(p.u / 100 * p.T)[0], [{ q: p.t0, label: 'θ₀' }, { q: p.tf, label: 'θ_f' }], { from: p.t0 }); },
                vpInfo(p) { return plot(cubic(p.t0, p.tf, p.T), p.u / 100 * p.T); },
                tex(p) { const k = cubic(p.t0, p.tf, p.T).a; return R`\theta(t) = ${n3(k[0])} ${pm(k[2])}t^2 ${pm(k[3])}t^3,\qquad \dot\theta_{max} = \frac{3}{2}\frac{\theta_f-\theta_0}{t_f} = ${n3(1.5 * (p.tf - p.t0) / p.T)}^\circ/\text{s}`; },
                html: () => R`<p>재생 버튼은 실제 시간(\(t_f\)초)으로 움직입니다.</p>
                ${ls([R`\(t_f\)를 줄이면 속도는 \(1/t_f\), 가속도는 \(1/t_f^2\)로 커짐`, R`이동량을 두 배로 하면 속도·가속도도 두 배`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 5.3 Cubic with via points ================= */
  const VP = [10, 35, 25, 10], VT = [2, 1, 3];
  {
    sec({
      id: 'c5-via', group: 'lecture', ref: '슬라이드 12–14', title: '5.3 경유점이 있는 3차 다항식',
      view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        const vc = viaCubic(VP, VT);
        const gh = VP.map((q, i) => ({ q, label: ['θ₀', 'θ_v1', 'θ_v2', 'θ_f'][i] }));
        return {
          init(S) { oneLink(S, VP[0], gh); },
          steps: [
            {
              t: '끝 속도가 0이 아닌 3차식',
              tex: R`a_0 = \theta_0,\quad a_1 = \dot\theta_0,\quad a_2 = \frac{3}{t_f^2}(\theta_f-\theta_0) - \frac{2}{t_f}\dot\theta_0 - \frac{1}{t_f}\dot\theta_f,\quad a_3 = -\frac{2}{t_f^3}(\theta_f-\theta_0) + \frac{1}{t_f^2}(\dot\theta_f+\dot\theta_0)`,
              html: R`<p>경유점에서 멈추지 않고 지나가려면 각 구간의 끝 속도가 0이 아니어야 합니다. 속도 조건을 \(\dot\theta(0) = \dot\theta_0\), \(\dot\theta(t_f) = \dot\theta_f\)로 바꿔 풀면 위 계수가 나옵니다.</p>
              <p>\(\dot\theta_0 = \dot\theta_f = 0\)이면 5.2절의 식으로 돌아갑니다.</p>`
            },
            {
              t: '경유점 속도는 어떻게 정하나',
              do(S) { oneLink(S, VP[3], gh, { from: VP[0] }); },
              vpInfo: plot(vc, vc.T, { title: '경유점 10° → 35° → 25° → 10° (2 s, 1 s, 3 s)' }),
              tex: R`\dot\theta_{12}^{\,lin} = \tfrac{35-10}{2} = 12.5,\quad \dot\theta_{23}^{\,lin} = \tfrac{25-35}{1} = -10,\quad \dot\theta_{34}^{\,lin} = \tfrac{10-25}{3} = -5\ \ \Rightarrow\ \ \dot\theta_{v1} = 0,\quad \dot\theta_{v2} = \tfrac12(-10-5) = -7.5^\circ/\text{s}`,
              html: R`<p>경유점을 직선으로 이었을 때의 기울기로 판단하는 간단한 규칙(heuristic)입니다.</p>
              ${ls([R`양옆 기울기의 부호가 바뀌면: 경유점 속도 = 0`, R`부호가 같으면: 두 기울기의 평균`])}
              ${ls([R`35°: 앞 기울기 \(+12.5\), 뒤 \(-10\) → 부호가 바뀜 → 그 점에서 멈추듯 \(\dot\theta = 0\)`, R`25°: 앞 \(-10\), 뒤 \(-5\) → 같은 부호 → 평균 \(-7.5^\circ/\text{s}\)`])}
              <p>그래프의 동그라미가 경유점입니다. 속도는 이어지지만 가속도는 경유점에서 끊깁니다.</p>`
            },
            {
              t: '경유점을 바꿔 재생해 보기',
              live: {
                params: [uParam].concat(VP.map((v, i) => ({ id: 'p' + i, label: [R`\(\theta_0\)`, R`\(\theta_{v1}\)`, R`\(\theta_{v2}\)`, R`\(\theta_f\)`][i], min: -40, max: 120, step: 1, val: v, unit: '°' }))),
                custom: player(VT.reduce((a, b) => a + b, 0)),
                apply(S, p) { const th = [p.p0, p.p1, p.p2, p.p3], v2 = viaCubic(th, VT); oneLink(S, v2.ev(p.u / 100 * v2.T)[0], th.map((q, i) => ({ q, label: ['θ₀', 'θ_v1', 'θ_v2', 'θ_f'][i] })), { from: p.p0 }); },
                vpInfo(p) { const v2 = viaCubic([p.p0, p.p1, p.p2, p.p3], VT); return plot(v2, p.u / 100 * v2.T); },
                tex(p) { const v2 = viaCubic([p.p0, p.p1, p.p2, p.p3], VT); return R`\dot\theta_{v1} = ${n3(v2.v[1])}^\circ/\text{s},\qquad \dot\theta_{v2} = ${n3(v2.v[2])}^\circ/\text{s}\qquad (t_d = 2,\ 1,\ 3\ \text{s})`; },
                html: () => R`<p>경유점 값을 바꾸면 휴리스틱이 고른 경유점 속도가 바뀝니다. 기울기 부호가 바뀌는 점에서는 그래프의 속도가 0을 지나는지 확인해 보세요.</p>`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 5.4 Continuous acceleration & quintic ================= */
  {
    const E = { t0: 10, tv: 60, tg: 30, T: 2 };
    sec({
      id: 'c5-cont', group: 'lecture', ref: '슬라이드 15–18', title: '5.4 가속도까지 연속: 3차식 두 개 · 5차식',
      view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        const tc = twoCubic(E.t0, E.tv, E.tg, E.T);
        const gh = [{ q: E.t0, label: 'θ₀' }, { q: E.tv, label: 'θ_v' }, { q: E.tg, label: 'θ_g' }];
        return {
          init(S) { oneLink(S, E.t0, gh); },
          steps: [
            {
              t: '조건 8개: 경유점에서 속도·가속도 연속',
              tex: R`\begin{aligned}&\theta_1(0) = \theta_0,\ \ \theta_1(t_{f1}) = \theta_v,\ \ \theta_2(0) = \theta_v,\ \ \theta_2(t_{f2}) = \theta_g,\ \ \dot\theta_1(0) = 0,\ \ \dot\theta_2(t_{f2}) = 0\\ &\dot\theta_1(t_{f1}) = \dot\theta_2(0),\qquad \ddot\theta_1(t_{f1}) = \ddot\theta_2(0)\end{aligned}`,
              html: R`<p>3차식 두 개(계수 8개)로 \(\theta_0 \to \theta_v \to \theta_g\)를 잇되, 경유점에서 <b>속도와 가속도가 모두 연속</b>이 되도록 조건을 줍니다.</p>
              <p>5.3절의 휴리스틱과 달리 경유점 속도를 미리 정하지 않고 조건에서 자동으로 결정됩니다.</p>`
            },
            {
              t: '풀이 (t_f1 = t_f2 = t_f)',
              do(S) { oneLink(S, E.tg, gh, { from: E.t0 }); },
              vpInfo: plot(tc, tc.T, { title: `${E.t0}° → ${E.tv}° → ${E.tg}°, 각 ${E.T} s` }),
              tex: R`\begin{aligned}&a_{10} = \theta_0,\ a_{11} = 0,\ a_{12} = \tfrac{12\theta_v - 3\theta_g - 9\theta_0}{4t_f^2},\ a_{13} = \tfrac{-8\theta_v + 3\theta_g + 5\theta_0}{4t_f^3}\\ &a_{20} = \theta_v,\ a_{21} = \tfrac{3\theta_g - 3\theta_0}{4t_f},\ a_{22} = \tfrac{-12\theta_v + 6\theta_g + 6\theta_0}{4t_f^2},\ a_{23} = \tfrac{8\theta_v - 5\theta_g - 3\theta_0}{4t_f^3}\end{aligned}`,
              html: R`<p>두 구간의 길이가 같을 때의 결과입니다. 경유점 속도는 \(a_{21} = \dfrac{3(\theta_g-\theta_0)}{4t_f}\)로, 경유점 값과 무관합니다.</p>
              <p>그래프: 가속도(아래)가 경유점(점선)에서 끊기지 않고 이어집니다. 시작·끝에서는 여전히 끊깁니다.</p>`
            },
            {
              t: '5차 다항식: 끝 가속도까지 지정',
              do(S) { oneLink(S, E.tv, [gh[0], gh[1]], { from: E.t0 }); },
              vpInfo: (() => { const q5 = quintic(E.t0, E.tv, E.T), c3 = cubic(E.t0, E.tv, E.T), sm = sampled(c3, E.T); return plot(q5, E.T, { title: `5차식 (실선) vs 3차식 (점선): ${E.t0}° → ${E.tv}°, ${E.T} s`, extra: [Object.assign(sm, { c: 'var(--mute)' })] }); })(),
              tex: R`\begin{aligned}&\theta(t) = a_0 + a_1t + a_2t^2 + a_3t^3 + a_4t^4 + a_5t^5,\qquad a_0 = \theta_0,\ \ a_1 = \dot\theta_0,\ \ a_2 = \tfrac12\ddot\theta_0\\ &a_3 = \tfrac{20\Delta - (8\dot\theta_f + 12\dot\theta_0)t_f - (3\ddot\theta_0 - \ddot\theta_f)t_f^2}{2t_f^3},\ \ a_4 = \tfrac{-30\Delta + (14\dot\theta_f + 16\dot\theta_0)t_f + (3\ddot\theta_0 - 2\ddot\theta_f)t_f^2}{2t_f^4},\ \ a_5 = \tfrac{12\Delta - 6(\dot\theta_f + \dot\theta_0)t_f - (\ddot\theta_0 - \ddot\theta_f)t_f^2}{2t_f^5}\end{aligned}`,
              html: R`<p>위치·속도·가속도를 양 끝에서 모두 정하면 조건이 6개 → <b>5차 다항식(quintic)</b>이 필요합니다(\(\Delta = \theta_f - \theta_0\)).</p>
              ${ls([R`정지→정지(\(\ddot\theta_0 = \ddot\theta_f = 0\))면 \(a_3 = 10\Delta/t_f^3,\ a_4 = -15\Delta/t_f^4,\ a_5 = 6\Delta/t_f^5\)`, R`가속도가 0에서 시작해 0으로 끝나 시작·끝의 충격이 없음`, R`대가: 최대 속도·가속도가 3차식보다 큼 (속도 최대 \(1.875\Delta/t_f\))`])}`
            },
            {
              t: '경유점을 움직여 보기',
              live: {
                params: [uParam, { id: 't0', label: R`\(\theta_0\)`, min: -40, max: 120, step: 1, val: E.t0, unit: '°' }, { id: 'tv', label: R`\(\theta_v\)`, min: -40, max: 120, step: 1, val: E.tv, unit: '°' }, { id: 'tg', label: R`\(\theta_g\)`, min: -40, max: 120, step: 1, val: E.tg, unit: '°' }, { id: 'T', label: R`\(t_f\)`, min: 0.8, max: 4, step: 0.1, val: E.T, unit: 's' }],
                custom: player(p => 2 * p.T),
                apply(S, p) { const t2 = twoCubic(p.t0, p.tv, p.tg, p.T); oneLink(S, t2.ev(p.u / 100 * t2.T)[0], [{ q: p.t0, label: 'θ₀' }, { q: p.tv, label: 'θ_v' }, { q: p.tg, label: 'θ_g' }], { from: p.t0 }); },
                vpInfo(p) { const t2 = twoCubic(p.t0, p.tv, p.tg, p.T); return plot(t2, p.u / 100 * t2.T); },
                tex(p) { const t2 = twoCubic(p.t0, p.tv, p.tg, p.T); return R`\theta_1(t) = ${n3(t2.a1[0])} ${pm(t2.a1[2])}t^2 ${pm(t2.a1[3])}t^3,\quad \theta_2(t) = ${n3(t2.a2[0])} ${pm(t2.a2[1])}t ${pm(t2.a2[2])}t^2 ${pm(t2.a2[3])}t^3`; },
                html: () => R`<p>경유점 \(\theta_v\)를 아주 크게 하면 첫 구간에서 목표를 지나쳤다 돌아오는(overshoot) 모양이 생길 수 있습니다.</p>`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 5.5 Linear segment with parabolic blends ================= */
  {
    const E = { t0: 15, tf: 75, T: 3, A: 40 };
    sec({
      id: 'c5-lpb', group: 'lecture', ref: '슬라이드 19–24', title: '5.5 포물선 혼합 직선 궤적 (LPB)',
      view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        const lp = lpb(E.t0, E.tf, E.T, E.A);
        const gh = [{ q: E.t0, label: 'θ₀' }, { q: E.tf, label: 'θ_f' }];
        return {
          init(S) { oneLink(S, E.t0, gh); },
          steps: [
            {
              t: '직선 + 양 끝 포물선',
              do(S) { oneLink(S, E.tf, gh, { from: E.t0 }); },
              vpInfo: plot(lp, lp.T, { title: `LPB: ${E.t0}° → ${E.tf}°, ${E.T} s, θ̈ = ${E.A}°/s²` }),
              tex: R`\theta(t) = \begin{cases}\theta_0 + \tfrac12\ddot\theta t^2 & 0 \le t \le t_b\\ \theta_b + \dot\theta_{lin}(t - t_b) & t_b \le t \le t_f - t_b\\ \theta_f - \tfrac12\ddot\theta(t_f - t)^2 & t_f - t_b \le t \le t_f\end{cases}`,
              html: R`<p>가운데는 일정한 속도의 <b>직선(linear segment)</b>, 양 끝은 일정한 가속도의 <b>포물선 혼합(parabolic blend)</b>입니다.</p>
              ${ls([R`가속도: \(+\ddot\theta\) → 0 → \(-\ddot\theta\) (계단 모양)`, R`속도: 사다리꼴 (trapezoidal velocity profile)`, R`가운데 시점 \(t_h = t_f/2\)에 대해 대칭`])}`
            },
            {
              t: '혼합 시간 t_b 구하기',
              tex: R`\ddot\theta\,t_b = \frac{\theta_h - \theta_b}{t_h - t_b},\ \ \theta_b = \theta_0 + \tfrac12\ddot\theta t_b^2\ \Rightarrow\ \ddot\theta t_b^2 - \ddot\theta t_f t_b + (\theta_f - \theta_0) = 0\ \Rightarrow\ t_b = \frac{t_f}{2} - \frac{\sqrt{\ddot\theta^2t_f^2 - 4\ddot\theta(\theta_f-\theta_0)}}{2\ddot\theta}`,
              html: R`<p>혼합 구간 끝의 속도(\(\ddot\theta t_b\))가 직선의 기울기와 같아야 매끄럽게 이어집니다. 직선은 가운데 점 \((t_h, \theta_h)\), \(\theta_h = (\theta_0+\theta_f)/2\)를 지납니다.</p>
              <p>2차 방정식의 두 근 중 \(t_b \le t_f/2\)인 작은 근을 씁니다.</p>
              <p>예: \(t_b = 1.5 - \sqrt{1600\cdot9 - 4\cdot40\cdot60}/80 = ${n3(lp.tb)}\) s.</p>`
            },
            {
              t: '필요한 최소 가속도',
              assume: [{ t: R`\(\ddot\theta \ge \dfrac{4(\theta_f-\theta_0)}{t_f^2} = ${n3(lp.Amin)}^\circ/\text{s}^2\)`, ok: true }],
              do(S) { oneLink(S, E.tf, gh, { from: E.t0 }); },
              vpInfo: (() => { const l2 = lpb(E.t0, E.tf, E.T, lp.Amin), sm = sampled(lp, E.T); return plot(l2, E.T, { title: '최소 가속도 (실선, 직선 구간 없음) vs θ̈ = 40 (점선)', extra: [Object.assign(sm, { c: 'var(--mute)' })] }); })(),
              tex: R`\ddot\theta^2t_f^2 - 4\ddot\theta(\theta_f-\theta_0) \ge 0\ \Rightarrow\ \ddot\theta \ge \frac{4(\theta_f-\theta_0)}{t_f^2}`,
              html: R`<p>제곱근 안이 음수면 해가 없습니다. 즉 가속도가 너무 작으면 주어진 시간 안에 도착할 수 없습니다.</p>
              ${ls([R`등호일 때: \(t_b = t_f/2\), 직선 구간이 사라지고 가속→감속만 남음 (속도가 삼각형)`, R`가속도가 클수록: \(t_b\)가 짧아지고 직선 구간이 길어짐`, R`가속도 → ∞: 직선 보간과 같아짐 (속도가 순간적으로 바뀜)`])}`
            },
            {
              t: '가속도를 바꿔 재생해 보기',
              live: {
                params: [uParam, { id: 't0', label: R`\(\theta_0\)`, min: -60, max: 150, step: 1, val: E.t0, unit: '°' }, { id: 'tf', label: R`\(\theta_f\)`, min: -60, max: 150, step: 1, val: E.tf, unit: '°' }, { id: 'T', label: R`\(t_f\)`, min: 1, max: 6, step: 0.1, val: E.T, unit: 's' }, { id: 'A', label: R`\(|\ddot\theta|\)`, min: 5, max: 300, step: 1, val: E.A, unit: '°/s²' }],
                custom: player(p => p.T),
                assume: p => { const l2 = lpb(p.t0, p.tf, p.T, p.A); return [{ t: R`\(|\ddot\theta| \ge 4|\theta_f-\theta_0|/t_f^2 = ${n3(l2.Amin)}\)${l2.ok ? '' : ' — 부족하므로 최소값으로 계산'}`, ok: l2.ok }]; },
                apply(S, p) { const l2 = lpb(p.t0, p.tf, p.T, p.A); oneLink(S, l2.ev(p.u / 100 * p.T)[0], [{ q: p.t0, label: 'θ₀' }, { q: p.tf, label: 'θ_f' }], { from: p.t0 }); },
                vpInfo(p) { const l2 = lpb(p.t0, p.tf, p.T, p.A); return plot(l2, p.u / 100 * p.T); },
                tex(p) { const l2 = lpb(p.t0, p.tf, p.T, p.A); return R`t_b = ${n3(l2.tb)}\ \text{s},\qquad \theta_b = ${n3(l2.thb)}^\circ,\qquad \dot\theta_{lin} = \ddot\theta t_b = ${n3(l2.V)}^\circ/\text{s}`; },
                html: () => R`<p>가속도를 최소값 가까이 줄이면 속도 그래프가 삼각형이 되고, 크게 하면 사각형에 가까워집니다.</p>`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 5.6 LPB with via points ================= */
  const lpbTable = r => R`\begin{array}{c|cccc} & \text{점 1} & \text{점 2} & \text{점 3} & \text{점 4}\\ \hline \ddot\theta_k & ${r.acc.map(n2).join(' & ')}\\ t_k & ${r.tb.map(n3).join(' & ')}\\ \hline & 1\text{–}2 & 2\text{–}3 & 3\text{–}4 & \\ \dot\theta_{jk} & ${r.vel.map(n3).join(' & ')} & \\ t_{jk} & ${r.lin.map(n3).join(' & ')} & \end{array}`;
  {
    const A0 = 50;
    sec({
      id: 'c5-lpbvia', group: 'lecture', ref: '슬라이드 25–30', title: '5.6 경유점이 있는 LPB',
      view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        const r = lpbVia(VP, VT, A0);
        const gh = VP.map((q, i) => ({ q, label: `θ${'₁₂₃₄'[i]}` }));
        return {
          init(S) { oneLink(S, VP[0], gh); },
          steps: [
            {
              t: '기호: 점 j, k, l과 구간',
              tex: R`t_{djk}:\ \text{점 } j\to k\ \text{지정 시간},\quad t_{jk}:\ \text{직선 구간 시간},\quad t_k:\ \text{점 } k\ \text{의 혼합 시간},\quad \dot\theta_{jk}:\ \text{직선 속도},\quad \ddot\theta_k:\ \text{혼합 가속도}`,
              html: R`<p>여러 경유점을 LPB로 잇습니다. 각 경유점 근처에 포물선 혼합을 두고, 그 사이를 직선으로 연결합니다.</p>
              ${ls([R`사용자가 정하는 것: 점의 값 \(\theta_k\), 구간 시간 \(t_{djk}\), 가속도 크기 \(|\ddot\theta_k|\)`, R`구하는 것: 직선 속도, 혼합 시간, 직선 구간 시간`])}`
            },
            {
              t: '내부 경유점',
              tex: R`\dot\theta_{jk} = \frac{\theta_k - \theta_j}{t_{djk}},\qquad \ddot\theta_k = \text{sgn}(\dot\theta_{kl} - \dot\theta_{jk})\,|\ddot\theta_k|,\qquad t_k = \frac{\dot\theta_{kl} - \dot\theta_{jk}}{\ddot\theta_k},\qquad t_{jk} = t_{djk} - \tfrac12t_j - \tfrac12t_k`,
              html: R`<p>내부 구간의 직선은 두 점을 그대로 잇습니다.</p>
              ${ls([R`혼합 가속도의 부호: 속도가 커지는 쪽이면 +, 작아지는 쪽이면 −`, R`혼합 시간: 속도 변화량 ÷ 가속도`, R`직선 구간: 지정 시간에서 양쪽 혼합의 절반씩 뺀 것`])}`
            },
            {
              t: '첫 구간과 마지막 구간',
              tex: R`\begin{aligned}&\ddot\theta_1 = \text{sgn}(\theta_2-\theta_1)|\ddot\theta_1|,\ \ t_1 = t_{d12} - \sqrt{t_{d12}^2 - \tfrac{2(\theta_2-\theta_1)}{\ddot\theta_1}},\ \ \dot\theta_{12} = \frac{\theta_2-\theta_1}{t_{d12} - \frac12t_1},\ \ t_{12} = t_{d12} - t_1 - \tfrac12t_2\\ &\ddot\theta_n = \text{sgn}(\theta_{n-1}-\theta_n)|\ddot\theta_n|,\ \ t_n = t_{d(n-1)n} - \sqrt{t_{d(n-1)n}^2 + \tfrac{2(\theta_n-\theta_{n-1})}{\ddot\theta_n}},\ \ \dot\theta_{(n-1)n} = \frac{\theta_n-\theta_{n-1}}{t_{d(n-1)n} - \frac12t_n},\ \ t_{(n-1)n} = t_{d(n-1)n} - t_n - \tfrac12t_{n-1}\end{aligned}`,
              html: R`<p>양 끝은 정지 상태에서 시작·끝나고, 혼합 구간 전체가 구간 <b>안쪽</b>에 들어갑니다(내부 점은 경유 시각을 가운데에 둠).</p>
              <p>첫 구간: 혼합 끝 속도 = 직선 속도이고, 그 직선이 점 2를 지나도록 하는 조건에서 \(t_1\)이 나옵니다. 마지막 구간은 대칭입니다.</p>`
            },
            {
              t: '예제: 10°, 35°, 25°, 10° / 2, 1, 3 s / |θ̈| = 50°/s²',
              do(S) { oneLink(S, VP[3], gh, { from: VP[0] }); },
              vpInfo: plot(r, r.T, { title: 'LPB 경유점 예제 (동그라미 = 지정한 점)' }),
              tex: lpbTable(r),
              html: R`<p>순서대로 계산합니다.</p>
              <ol class="ls"><li>첫 구간: \(t_1 = 2 - \sqrt{4 - 2\cdot25/50} = ${n3(r.tb[0])}\), \(\dot\theta_{12} = 25/(2 - ${n3(r.tb[0] / 2)}) = ${n3(r.vel[0])}\)</li><li>내부 직선: \(\dot\theta_{23} = (25-35)/1 = -10\)</li><li>마지막 구간: \(t_4 = 3 - \sqrt{9 + 2(10-25)/50} = ${n3(r.tb[3])}\), \(\dot\theta_{34} = ${n3(r.vel[2])}\)</li><li>내부 혼합: \(t_2 = ${n3(r.tb[1])}\), \(t_3 = ${n3(r.tb[2])}\), 그다음 직선 구간 시간</li></ol>`
            },
            {
              t: '경유점을 실제로 지나가지 않는다',
              do(S) { oneLink(S, VP[1], gh, { from: VP[0] }); },
              vpInfo: (() => { const hi = lpbVia(VP, VT, 400), sm = sampled(hi, hi.T); return plot(r, r.T, { title: '|θ̈| = 50 (실선) vs 400 (점선): 가속도가 클수록 점에 가까워짐', extra: [Object.assign(sm, { c: 'var(--mute)' })] }); })(),
              tex: R`\theta(t_{v}) \ne \theta_{v}\ \ \text{(내부 경유점)},\qquad |\ddot\theta| \uparrow\ \Rightarrow\ t_k \downarrow\ \Rightarrow\ \text{경유점에 더 가까이}`,
              html: R`<p>내부 경유점에서는 혼합 구간이 모서리를 깎아 지나가므로, 궤적이 경유점 값에 <b>정확히 닿지 않습니다</b> (그래프에서 35° 동그라미 아래로 지나감).</p>
              ${ls([R`가속도를 크게 하면 혼합 시간이 짧아져 더 가까이 지나감`, R`정확히 지나가게 하려면 <b>의사 경유점(pseudo via point)</b>을 경유점 양옆에 하나씩 추가: 실제 경유점이 두 의사 경유점 사이의 직선 위에 놓이게 함`])}`
            },
            {
              t: '점·가속도를 바꿔 재생해 보기',
              live: {
                params: [uParam].concat(VP.map((v, i) => ({ id: 'p' + i, label: R`\(\theta_${i + 1}\)`, min: -40, max: 120, step: 1, val: v, unit: '°' })), [{ id: 'A', label: R`\(|\ddot\theta|\)`, min: 20, max: 400, step: 1, val: A0, unit: '°/s²' }]),
                custom: player(VT.reduce((a, b) => a + b, 0)),
                assume: p => { const r2 = lpbVia([p.p0, p.p1, p.p2, p.p3], VT, p.A); return [{ t: '모든 혼합·직선 시간 ≥ 0 (가속도가 충분)', ok: r2.ok }]; },
                apply(S, p) { const th = [p.p0, p.p1, p.p2, p.p3], r2 = lpbVia(th, VT, p.A); oneLink(S, r2.ev(p.u / 100 * r2.T)[0], th.map((q, i) => ({ q, label: `θ${'₁₂₃₄'[i]}` })), { from: p.p0 }); },
                vpInfo(p) { const r2 = lpbVia([p.p0, p.p1, p.p2, p.p3], VT, p.A); return plot(r2, p.u / 100 * r2.T); },
                tex(p) { return lpbTable(lpbVia([p.p0, p.p1, p.p2, p.p3], VT, p.A)); },
                html: () => R`<p>\(|\ddot\theta|\)를 키우면 곡선이 동그라미(지정한 점)에 가까워집니다. 너무 작으면 혼합 구간이 겹쳐 계산이 깨집니다(조건 ✗).</p>`
              }
            }
          ]
        };
      }
    });
  }

  /* =========================================================
     Practice
     ========================================================= */
  sec({
    id: 'c5-hw-cubic', group: 'practice', ref: '강의 5 · 3차 다항식 연습', title: '정지→정지 3차 궤적의 계수와 값',
    view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
    params: {
      orig: { t0: 20, tf: 80, T: 4, tq: 1 }, origLabel: '기본 문제',
      rand() { const t0 = pick(-6, 6) * 5, d = pick(4, 18) * 5 * (Math.random() < 0.3 ? -1 : 1), T = pick(2, 6); return { t0, tf: t0 + d, T, tq: pick(1, 2 * T - 1) / 2 }; }
    },
    build(P) {
      const cb = cubic(P.t0, P.tf, P.T), a = cb.a, v = cb.ev(P.tq), d = P.tf - P.t0;
      const gh = [{ q: P.t0, label: 'θ₀' }, { q: P.tf, label: 'θ_f' }];
      return {
        answers: [{ label: R`\(a_2\)`, val: a[2], tol: 0.002, dp: 4 }, { label: R`\(a_3\)`, val: a[3], tol: 0.002, dp: 4 }, { label: R`\(\theta(${P.tq})\)`, val: v[0], unit: '°', tol: 0.02, dp: 3 }],
        calcData: { a, v },
        init(S) { oneLink(S, P.t0, gh); },
        steps: [
          {
            t: '문제',
            tex: R`\theta_0 = ${P.t0}^\circ,\quad \theta_f = ${P.tf}^\circ,\quad t_f = ${P.T}\ \text{s},\qquad \dot\theta(0) = \dot\theta(t_f) = 0`,
            html: R`<p>관절 하나가 정지 상태에서 출발해 정지 상태로 끝나는 3차 다항식 궤적을 만듭니다.</p>
            <ol class="ls"><li>계수 \(a_0, a_1, a_2, a_3\)을 구하시오.</li><li>\(t = ${P.tq}\) s에서 \(\theta, \dot\theta, \ddot\theta\)를 구하시오.</li><li>최대 속도와 그때의 시각, 시작 순간의 가속도를 구하시오.</li></ol>`
          },
          {
            t: '① 계수',
            tex: R`a_0 = \theta_0 = ${P.t0},\quad a_1 = 0,\quad a_2 = \frac{3(\theta_f-\theta_0)}{t_f^2} = \frac{3(${d})}{${P.T}^2} = ${f(a[2], 4)},\quad a_3 = -\frac{2(\theta_f-\theta_0)}{t_f^3} = -\frac{2(${d})}{${P.T}^3} = ${f(a[3], 4)}`,
            html: R`<p>\(\theta(t) = ${P.t0} ${pm(a[2])}t^2 ${pm(a[3])}t^3\)</p>`
          },
          {
            t: `② t = ${P.tq} s에서의 값`,
            do(S) { oneLink(S, v[0], gh, { from: P.t0 }); },
            vpInfo: plot(cb, P.tq),
            tex: R`\begin{aligned}\theta(t) &= a_0 + a_2t^2 + a_3t^3 = ${P.t0} + (${f(a[2], 4)})(${P.tq})^2 + (${f(a[3], 4)})(${P.tq})^3 = ${f(v[0], 3)}^\circ\\ \dot\theta(t) &= 2a_2t + 3a_3t^2 = 2(${f(a[2], 4)})(${P.tq}) + 3(${f(a[3], 4)})(${P.tq})^2 = ${f(v[1], 3)}^\circ/\text{s}\\ \ddot\theta(t) &= 2a_2 + 6a_3t = 2(${f(a[2], 4)}) + 6(${f(a[3], 4)})(${P.tq}) = ${f(v[2], 3)}^\circ/\text{s}^2\end{aligned}`,
            html: R`<p>각 식에 \(t = ${P.tq}\)를 대입합니다. 그래프의 세로선이 그 시각입니다.</p>`
          },
          {
            t: '③ 최대 속도와 시작 가속도',
            do(S) { oneLink(S, cb.ev(P.T / 2)[0], gh, { from: P.t0 }); },
            vpInfo: plot(cb, P.T / 2),
            tex: R`\ddot\theta = 0\ \Rightarrow\ t = -\frac{a_2}{3a_3} = \frac{t_f}{2} = ${f(P.T / 2, 3)}\ \text{s},\quad \dot\theta_{max} = \frac{3}{2}\frac{\theta_f-\theta_0}{t_f} = \frac{3}{2}\cdot\frac{${d}}{${P.T}} = ${f(1.5 * d / P.T, 4)}^\circ/\text{s},\quad \ddot\theta(0) = 2a_2 = 2(${f(a[2], 4)}) = ${f(2 * a[2], 4)}^\circ/\text{s}^2`,
            html: R`<p>속도가 최대인 순간은 가속도가 0인 순간이고, 3차 정지-정지 궤적에서는 항상 가운데 시점입니다.</p>`
          }
        ]
      };
    }
  });

  sec({
    id: 'c5-hw-lpb', group: 'practice', ref: '강의 5 · LPB 연습', title: '포물선 혼합 직선 궤적 (LPB) 계산',
    view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
    params: {
      orig: { t0: 10, tf: 70, T: 4, A: 30 }, origLabel: '기본 문제',
      rand() { for (let n = 0; n < 50; n++) { const t0 = pick(-4, 6) * 5, d = pick(4, 16) * 5, T = pick(2, 6), Am = 4 * d / T / T, A = Math.ceil(Am * (1.2 + Math.random())); return { t0, tf: t0 + d, T, A }; } }
    },
    build(P) {
      const lp = lpb(P.t0, P.tf, P.T, P.A), d = P.tf - P.t0, tq = M.round(P.T * 0.35, 2), vq = lp.ev(tq);
      const gh = [{ q: P.t0, label: 'θ₀' }, { q: P.tf, label: 'θ_f' }];
      return {
        answers: [{ label: R`\(t_b\)`, val: lp.tb, unit: 's', tol: 0.002, dp: 4 }, { label: R`\(\dot\theta_{lin}\)`, val: lp.V, unit: '°/s', tol: 0.02, dp: 3 }],
        calcData: { lp, tq, vq },
        init(S) { oneLink(S, P.t0, gh); },
        steps: [
          {
            t: '문제',
            tex: R`\theta_0 = ${P.t0}^\circ,\ \ \theta_f = ${P.tf}^\circ,\ \ t_f = ${P.T}\ \text{s},\ \ |\ddot\theta| = ${P.A}^\circ/\text{s}^2`,
            html: R`<p>포물선 혼합 직선 궤적(LPB)으로 관절을 움직입니다.</p>
            <ol class="ls"><li>이 시간 안에 도달하기 위한 최소 가속도를 구하고, 주어진 가속도가 충분한지 확인하시오.</li><li>혼합 시간 \(t_b\)를 구하시오.</li><li>혼합 끝의 각 \(\theta_b\)와 직선 구간 속도를 구하시오.</li><li>\(t = ${tq}\) s에서 \(\theta\)를 구하시오.</li></ol>`
          },
          {
            t: '① 최소 가속도',
            assume: [{ t: R`\(${P.A} \ge ${n3(lp.Amin)}\)`, ok: lp.ok }],
            tex: R`\ddot\theta_{min} = \frac{4(\theta_f - \theta_0)}{t_f^2} = \frac{4\cdot${d}}{${P.T * P.T}} = ${f(lp.Amin, 4)}^\circ/\text{s}^2\ \le\ ${P.A}`,
            html: R`<p>주어진 가속도가 최소값보다 크므로 직선 구간이 있는 LPB가 가능합니다.</p>`
          },
          {
            t: '② 혼합 시간',
            do(S) { oneLink(S, lp.thb, gh, { from: P.t0 }); },
            vpInfo: plot(lp, lp.tb),
            tex: R`t_b = \frac{t_f}{2} - \frac{\sqrt{\ddot\theta^2t_f^2 - 4\ddot\theta(\theta_f-\theta_0)}}{2\ddot\theta} = ${f(P.T / 2, 3)} - \frac{\sqrt{${P.A * P.A * P.T * P.T} - ${4 * P.A * d}}}{${2 * P.A}} = ${f(lp.tb, 4)}\ \text{s}`,
            html: R`<p>제곱근 안: \(${P.A}^2\cdot${P.T}^2 - 4\cdot${P.A}\cdot${d}\).</p>`
          },
          {
            t: '③ 혼합 끝 각과 직선 속도',
            do(S) { oneLink(S, lp.thb, gh, { from: P.t0 }); },
            vpInfo: plot(lp, lp.tb),
            tex: R`\theta_b = \theta_0 + \tfrac12\ddot\theta t_b^2 = ${P.t0} + \tfrac12(${P.A})(${f(lp.tb, 4)})^2 = ${f(lp.thb, 4)}^\circ,\qquad \dot\theta_{lin} = \ddot\theta\,t_b = (${P.A})(${f(lp.tb, 4)}) = ${f(lp.V, 4)}^\circ/\text{s}`,
            html: R`<p>확인: 직선 \(\theta_b + \dot\theta_{lin}(t - t_b)\)가 \(t = t_f/2\)에서 중간값 \(${f((P.t0 + P.tf) / 2, 3)}^\circ\)를 지나야 합니다.</p>`
          },
          {
            t: `④ t = ${tq} s에서의 각`,
            do(S) { oneLink(S, vq[0], gh, { from: P.t0 }); },
            vpInfo: plot(lp, tq),
            tex: tq <= lp.tb ? R`t \le t_b:\ \ \theta = \theta_0 + \tfrac12\ddot\theta t^2 = ${P.t0} + \tfrac12(${P.A})(${tq})^2 = ${f(vq[0], 4)}^\circ` : R`t_b < t \le t_f - t_b:\ \ \theta = \theta_b + \dot\theta_{lin}(t - t_b) = ${f(lp.thb, 3)} + ${f(lp.V, 3)}(${tq} - ${f(lp.tb, 3)}) = ${f(vq[0], 4)}^\circ`,
            html: R`<p>먼저 그 시각이 어느 구간(혼합/직선)에 있는지 확인한 뒤 해당 식을 씁니다.</p>`
          }
        ]
      };
    }
  });

  sec({
    id: 'c5-hw-via', group: 'practice', ref: '강의 5 · 슬라이드 28 유형 (숫자 변경)', title: '경유점이 있는 LPB 계산',
    view: VIEW1, grid: [3, 0.5], scale: 0.7, fsize: 1,
    params: {
      orig: { th: [10, 35, 25, 10], td: [2, 1, 3], A: 50 }, origLabel: '강의 예제',
      rand() {
        for (let n = 0; n < 200; n++) {
          const th = [pick(0, 4) * 5]; for (let i = 0; i < 3; i++) th.push(th[i] + pick(-6, 6) * 5);
          const td = [pick(1, 3), pick(1, 3), pick(1, 3)], A = pick(4, 12) * 10;
          if (th.some((v, i) => i && v === th[i - 1])) continue;
          const r = lpbVia(th, td, A); if (r.ok && r.lin.every(x => x > 0.05)) return { th, td, A };
        }
        return { th: [10, 35, 25, 10], td: [2, 1, 3], A: 50 };
      }
    },
    build(P) {
      const r = lpbVia(P.th, P.td, P.A), th = P.th, td = P.td;
      const gh = th.map((q, i) => ({ q, label: `θ${'₁₂₃₄'[i]}` }));
      return {
        answers: [{ label: R`\(t_{12}\)`, val: r.lin[0], unit: 's', tol: 0.003, dp: 4 }, { label: R`\(t_{23}\)`, val: r.lin[1], unit: 's', tol: 0.003, dp: 4 }, { label: R`\(t_{34}\)`, val: r.lin[2], unit: 's', tol: 0.003, dp: 4 }],
        calcData: { r },
        init(S) { oneLink(S, th[0], gh); },
        steps: [
          {
            t: '문제',
            tex: R`\theta = (${th.join(',\\ ')})^\circ,\qquad t_d = (${td.join(',\\ ')})\ \text{s},\qquad |\ddot\theta_k| = ${P.A}^\circ/\text{s}^2`,
            html: R`<p>네 점을 지나는 LPB 궤적의 모든 혼합 가속도, 혼합 시간, 직선 속도, 직선 구간 시간을 구하시오.</p>`
          },
          {
            t: '① 첫 구간',
            tex: R`\begin{aligned}\ddot\theta_1 &= \text{sgn}(\theta_2-\theta_1)|\ddot\theta| = ${f(r.acc[0], 0)}\\ t_1 &= t_{d12} - \sqrt{t_{d12}^2 - \tfrac{2(\theta_2-\theta_1)}{\ddot\theta_1}} = ${td[0]} - \sqrt{${td[0]}^2 - \tfrac{2(${th[1] - th[0]})}{${f(r.acc[0], 0)}}} = ${f(r.tb[0], 4)}\\ \dot\theta_{12} &= \frac{\theta_2-\theta_1}{t_{d12} - \frac12t_1} = \frac{${th[1] - th[0]}}{${td[0]} - \frac12(${f(r.tb[0], 4)})} = ${f(r.vel[0], 4)}\end{aligned}`,
            html: R`<p>가속도 부호는 \(\theta_2 - \theta_1\)의 부호를 따릅니다.</p>`
          },
          {
            t: '② 내부 직선',
            tex: R`\dot\theta_{23} = \frac{\theta_3 - \theta_2}{t_{d23}} = \frac{${th[2] - th[1]}}{${td[1]}} = ${f(r.vel[1], 4)}`,
            html: R`<p>양 끝이 아닌 구간은 두 점을 바로 잇는 기울기입니다.</p>`
          },
          {
            t: '③ 마지막 구간',
            tex: R`\begin{aligned}\ddot\theta_4 &= \text{sgn}(\theta_3-\theta_4)|\ddot\theta| = ${f(r.acc[3], 0)}\\ t_4 &= t_{d34} - \sqrt{t_{d34}^2 + \tfrac{2(\theta_4-\theta_3)}{\ddot\theta_4}} = ${td[2]} - \sqrt{${td[2]}^2 + \tfrac{2(${th[3] - th[2]})}{${f(r.acc[3], 0)}}} = ${f(r.tb[3], 4)}\\ \dot\theta_{34} &= \frac{\theta_4-\theta_3}{t_{d34} - \frac12t_4} = \frac{${th[3] - th[2]}}{${td[2]} - \frac12(${f(r.tb[3], 4)})} = ${f(r.vel[2], 4)}\end{aligned}`,
            html: R`<p>가속도 부호는 \(\theta_3 - \theta_4\)의 부호를 따릅니다(마지막에 속도를 0으로 줄이는 방향).</p>`
          },
          {
            t: '④ 내부 혼합',
            tex: R`\begin{aligned}\ddot\theta_k &= \text{sgn}(\dot\theta_{kl}-\dot\theta_{jk})|\ddot\theta|,\qquad t_k = \frac{\dot\theta_{kl}-\dot\theta_{jk}}{\ddot\theta_k}\\ \ddot\theta_2 &= ${f(r.acc[1], 0)},\ \ t_2 = \frac{${f(r.vel[1], 4)} - (${f(r.vel[0], 4)})}{${f(r.acc[1], 0)}} = ${f(r.tb[1], 4)}\\ \ddot\theta_3 &= ${f(r.acc[2], 0)},\ \ t_3 = \frac{${f(r.vel[2], 4)} - (${f(r.vel[1], 4)})}{${f(r.acc[2], 0)}} = ${f(r.tb[2], 4)}\end{aligned}`,
            html: R`<p>부호는 (다음 직선 속도 − 앞 직선 속도)의 부호입니다.</p>`
          },
          {
            t: '⑤ 직선 구간 시간',
            do(S) { oneLink(S, th[3], gh, { from: th[0] }); },
            vpInfo: plot(r, r.T, { title: '계산한 LPB 궤적' }),
            tex: R`\begin{aligned}t_{12} &= t_{d12} - t_1 - \tfrac12t_2 = ${td[0]} - ${f(r.tb[0], 4)} - \tfrac12(${f(r.tb[1], 4)}) = ${f(r.lin[0], 4)}\\ t_{23} &= t_{d23} - \tfrac12t_2 - \tfrac12t_3 = ${td[1]} - \tfrac12(${f(r.tb[1], 4)}) - \tfrac12(${f(r.tb[2], 4)}) = ${f(r.lin[1], 4)}\\ t_{34} &= t_{d34} - t_4 - \tfrac12t_3 = ${td[2]} - ${f(r.tb[3], 4)} - \tfrac12(${f(r.tb[2], 4)}) = ${f(r.lin[2], 4)}\end{aligned}`,
            html: R`<p>모든 직선 구간 시간이 양수이면 주어진 가속도로 충분합니다. 음수가 나오면 가속도를 키워야 합니다.</p>`
          }
        ]
      };
    }
  });

  window.COURSE.chapters.push({ id: 'ch5', title: 'Lecture 5 · Trajectory Generation', short: 'Ch5 궤적 생성', sections });
  window.TRAJ = { cubic, lpb, lpbVia, viaCubic, twoCubic, quintic };
})();
