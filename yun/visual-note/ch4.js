/* =========================================================
   Chapter 4 — Jacobians: Velocities and Static Forces (Lecture 4)
   + Homework 3 solutions
   ========================================================= */
(function () {
  'use strict';
  const R = String.raw;
  const { I, mul, rx, ry, rz, tr, inv, app, R3, p3, fromRp, RT, mv3, col, unit, cross, dot, norm, scl, add, sub, atan2d, f, tm, tv, D } = M;
  const K = window.KIN;
  const { robot, dragSpec, fr, pt, vec, ln, arc, body, drop } = K;
  const X = [1, 0, 0], Yv = [0, 1, 0], Z = [0, 0, 1], O = [0, 0, 0];
  const c = a => Math.cos(a * D), s = a => Math.sin(a * D);
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const base = rx(90);                       // arm plane = world XZ, Z0 toward the viewer
  const Wv = v => [v[0], -(v[2] || 0), v[1]]; // planar {0} components → world
  const wipe = S => { ['frames', 'pts', 'vecs', 'lines', 'arcs', 'bodies'].forEach(k => drop(S, k)); S.watch = null; };
  const row = a => ({ al: 0, a, d: 0, th: 0, type: 'R' });
  const rowsOf = L => L.slice(0, -1).reduce((r, a) => (r.push(row(a)), r), [row(0)]);
  const sub3 = (v, n) => v.slice(0, n);
  const bm = (A, n) => R`\begin{bmatrix}${A.map(r => r.map(x => typeof x === 'number' ? f(x, n == null ? 3 : n) : x).join('&')).join(R`\\`)}\end{bmatrix}`;
  const cv = (v, n) => bm(v.map(x => [x]), n);
  const vcard = (title, rows) => `<div class="vh">${title}</div>` + rows.filter(Boolean).map(r => `<div class="vr${r.on ? ' on' : ''}"><b>${r.s}</b>${r.v != null ? ' = ' + r.v : ''}${r.n ? ` <span class="vn">${r.n}</span>` : ''}</div>`).join('');
  const t3 = (v, n) => `(${v.map(x => f(x, n == null ? 3 : n)).join(', ')})`;
  const ls = items => `<ul class="ls">${items.map(x => `<li>${x}</li>`).join('')}</ul>`;
  // arrow drawn from a frame's origin (or a point given in that frame), components in that frame
  const arw = (S, id, fid, v, k, o, at) => { const a = at || O; if (norm(v) * k < 0.025) return; vec(S, id, { f: fid, p: a }, { f: fid, p: add(a, scl(v, k)) }, o); };
  // torque arc about a frame's Z axis
  const tq = (S, id, fid, tau, k, o) => { const ang = clamp(tau * k, -330, 330); if (Math.abs(ang) < 2) return; arc(S, id, Object.assign({ f: fid, c: [0, 0, 0.02], n: Z, u: X, ang, r: 0.3 }, o)); };

  /* ---------- planar serial chain (all revolute) ----------
     L = [link lengths …, tool length]; frames 1..n at the joints, frame n+1 at the tool point */
  function propP(L, q, qd) {
    const n = q.length, w = [0], v = [[0, 0, 0]];
    let wi = 0, vi = [0, 0];
    for (let i = 0; i <= n; i++) {
      if (i === 0) { wi = qd[0]; vi = [0, 0]; }
      else {
        const inner = [vi[0], vi[1] + wi * L[i - 1]], a = i < n ? q[i] : 0;
        vi = [inner[0] * c(a) + inner[1] * s(a), -inner[0] * s(a) + inner[1] * c(a)];
        if (i < n) wi += qd[i];
      }
      w.push(wi); v.push([vi[0], vi[1], 0]);
    }
    return { w, v }; // index 1..n+1
  }
  function statP(L, q, F, nz) {
    const n = q.length, fs = [], ns = [];
    let f2 = [F[0], F[1]], mz = nz || 0;
    fs[n + 1] = [f2[0], f2[1], 0]; ns[n + 1] = [0, 0, mz];
    for (let k = n; k >= 1; k--) {
      const a = k < n ? q[k] : 0;
      f2 = [f2[0] * c(a) - f2[1] * s(a), f2[0] * s(a) + f2[1] * c(a)];
      mz += L[k - 1] * f2[1];
      fs[k] = [f2[0], f2[1], 0]; ns[k] = [0, 0, mz];
    }
    return { f: fs, n: ns, tau: q.map((_, i) => ns[i + 1][2]) };
  }
  // 2×2 base-frame Jacobian of a planar 2-link (tip = end of link 2)
  const J0two = (l1, l2, q) => { const a = q[0], b = q[0] + q[1]; return [[-l1 * s(a) - l2 * s(b), -l2 * s(b)], [l1 * c(a) + l2 * c(b), l2 * c(b)]]; };
  const inv2 = A => { const d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; return { d, Ai: [[A[1][1] / d, -A[0][1] / d], [-A[1][0] / d, A[0][0] / d]] }; };
  const mv2 = (A, v) => [A[0][0] * v[0] + A[0][1] * v[1], A[1][0] * v[0] + A[1][1] * v[1]];

  // draws a planar arm; returns frames incl. the tool frame 'F{n+1}' (or o.tId)
  function arm(S, L, q, o) {
    o = o || {};
    const n = q.length, rows = rowsOf(L);
    const r = robot(S, rows, q, Object.assign({ base, tool: L[n - 1], fs: 0.3, w: 0.06, jr: 0.08, jh: 0.14, noDrag: !o.drag }, o));
    const Tt = mul(r.Ts[n], tr(L[n - 1], 0, 0));
    fr(S, (o.pre || '') + (o.tId || 'F' + (n + 1)), Tt, Object.assign({ label: o.tLabel || String(n + 1), size: o.fs || 0.3, hidden: !!o.hideTool }, o.tOpt || {}));
    return r.Ts.concat([Tt]);
  }
  // velocity ellipse at the tip: {J θ̇ : |θ̇| = 1}
  function ellipse(S, id, tipW, J, k, col) {
    const N = 40; let prev = null;
    for (let i = 0; i <= N; i++) {
      const a = 2 * Math.PI * i / N, v = mv2(J, [Math.cos(a), Math.sin(a)]);
      const p = add(tipW, scl(Wv([v[0], v[1], 0]), k));
      if (prev) ln(S, id + i, prev, p, { c: col || 'acc', dash: false });
      prev = p;
    }
  }

  const sections = [];
  const sec = o => sections.push(o);

  /* ================= 4.1 Rigid-body velocity ================= */
  {
    const TB = mul(tr(1.5, 0.7, 0.25), rz(35)), QB = [0.95, 0.45, 0.55], VS = 0.9;
    const QW = app(TB, QB), RB = R3(TB);
    const scene = (S, o) => {
      wipe(S); o = o || {};
      fr(S, 'A', I(), { label: 'A', size: 0.9 });
      fr(S, 'B', TB, { label: 'B', size: 0.6, cols: ['j2', 'j2', 'j2'] });
      body(S, 'bd', 'B', 'box', [1.3, 0.9, 0.75], [0.6, 0.3, 0.37], { c: 'body', op: 0.22 });
      pt(S, 'Q', QW, 'Q', { c: 'pt' });
      vec(S, 'pb', O, p3(TB), { c: 'mute', label: 'ᴬP<sub>BORG</sub>', w: 0.6 });
      vec(S, 'bq', { f: 'B', p: O }, { f: 'B', p: QB }, { c: 'pt', label: 'ᴮQ', w: 0.7, lt: 0.45 });
    };
    const omega = (S, w) => { arw(S, 'om', 'B', [0, 0, w], 0.8, { c: 'k', label: 'ᴬΩ<sub>B</sub>', w: 1.1, lt: 0.9, lo: [0.12, 0, 0] }); };
    const velQ = (S, p) => {
      const vb = [p.vx, p.vy, 0], vq = mv3(RB, [p.qv, 0, 0]), w = mv3(RB, [0, 0, p.w]);
      const rot = cross(w, sub(QW, p3(TB))), tot = add(add(vb, vq), rot);
      const at = QW, go = (id, v, o) => { if (norm(v) * VS > 0.025) vec(S, id, at, add(at, scl(v, VS)), o); };
      go('vq1', vb, { c: 'mute', label: 'ᴬV<sub>BORG</sub>', w: 0.8, lt: 1.05 });
      go('vq2', vq, { c: 'j2', label: 'R ᴮV<sub>Q</sub>', w: 0.8, lt: 1.05 });
      go('vq3', rot, { c: 'acc', label: 'Ω × R ᴮQ', w: 0.8, lt: 1.05 });
      go('vqs', tot, { c: 'ink', label: 'ᴬV<sub>Q</sub>', w: 1.3, lt: 1.08 });
      if (norm(vb) * VS > 0.025) vec(S, 'vb', p3(TB), add(p3(TB), scl(vb, VS)), { c: 'mute', w: 0.8 });
      return { vb, vq, rot, tot };
    };
    const circ = S => arc(S, 'cq', { f: 'B', c: [0, 0, QB[2]], n: Z, u: unit([QB[0], QB[1], 0]), ang: 359, r: Math.hypot(QB[0], QB[1]), noHead: true, col: 'mute' });
    sec({
      id: 'c4-rigid', group: 'lecture', ref: '슬라이드 3–9', title: '4.1 강체 위 한 점의 속도',
      view: { pos: [4.6, -3.6, 3.0], target: [1.3, 0.5, 0.5] }, grid: [3, 0.5], scale: 0.75, fsize: 1,
      build() {
        return {
          init(S) { scene(S); },
          steps: [
            {
              t: '위치 벡터의 미분: 어느 좌표계에서 미분했나',
              tex: R`{}^BV_Q = \frac{d}{dt}\,{}^BQ = \lim_{\Delta t\to 0}\frac{{}^BQ(t+\Delta t) - {}^BQ(t)}{\Delta t},\qquad {}^A\!\left({}^BV_Q\right) = {}^A_BR\;{}^BV_Q`,
              html: R`<p>속도 벡터에는 좌표계가 <b>두 개</b> 붙을 수 있습니다.</p>
              ${ls([R`안쪽 위첨자 \(B\): <b>미분한 좌표계</b> (어느 좌표계에서 본 움직임인가)`, R`바깥 위첨자 \(A\): <b>표현한 좌표계</b> (어느 축으로 성분을 적었나)`])}
              <p>표현 좌표계만 바꾸는 것은 회전행렬 곱 하나면 됩니다. 두 위첨자가 같으면 하나만 씁니다.</p>
              <p class="note">\(v_C = {}^UV_{CORG}\): 기준(universe) 좌표계 \(U\)에 대한 {C} 원점의 속도. 각속도도 \(\omega_C = {}^U\Omega_C\)로 씁니다.</p>`
            },
            {
              t: '각속도: 점이 아니라 몸체의 성질',
              do(S) { omega(S, 1.2); circ(S); },
              tex: R`{}^A\Omega_B:\quad \text{방향} = \text{순간 회전축},\quad |{}^A\Omega_B| = \text{회전 속력 (rad/s)}`,
              html: R`<p><b>선속도(linear velocity)</b>는 한 <b>점</b>의 성질이고, <b>각속도(angular velocity)</b>는 <b>몸체(좌표계)</b> 전체의 성질입니다.</p>
              ${ls([R`보라색 화살표 \({}^A\Omega_B\): {A}에 대한 {B}의 회전`, R`화살표 방향 = 회전축 (오른손 법칙)`, R`화살표 길이 = 얼마나 빨리 도는가`])}
              <p>회색 원은 \(B\)가 이 축으로 돌 때 점 \(Q\)가 그리는 경로입니다.</p>`
            },
            {
              t: '평행 이동만 할 때',
              do(S) { velQ(S, { vx: 0.6, vy: 0.2, qv: 0.35, w: 0 }); },
              tex: R`{}^AV_Q = {}^AV_{BORG} + {}^A_BR\;{}^BV_Q\qquad (\,{}^A_BR\ \text{일정}\,)`,
              html: R`<p>{B}가 방향은 그대로 두고 미끄러지듯 움직이는 경우입니다.</p>
              ${ls([R`회색: {B} 원점의 속도 \({}^AV_{BORG}\) (Q에도 그대로 더해짐)`, R`분홍: {B} 안에서 Q가 움직이는 속도를 {A}로 표현한 것`, R`검정: 두 벡터의 합 = \({}^AV_Q\)`])}
              <p>방향이 변하지 않을 때만 성립하는 식입니다.</p>`
            },
            {
              t: '회전만 할 때: Ω × Q 항',
              do(S) { omega(S, 1.2); circ(S); velQ(S, { vx: 0, vy: 0, qv: 0, w: 1.2 }); },
              tex: R`{}^AV_Q = {}^A_BR\;{}^BV_Q + {}^A\Omega_B \times {}^A_BR\;{}^BQ`,
              html: R`<p>두 원점이 겹쳐 있고 {B}가 돌기만 하는 경우입니다. Q가 {B}에 고정되어 있으면 첫 항은 0입니다.</p>
              ${ls([R`Q는 회전축을 중심으로 원(회색)을 그림`, R`짧은 시간 동안 움직인 거리: \(|\Delta Q| = |{}^BQ|\sin\theta\,|\Omega|\,\Delta t\)`, R`방향은 축과 Q 모두에 수직 → 외적 \(\Omega\times Q\)`])}
              <p>파란 화살표가 원의 접선 방향인 것을 확인하세요.</p>`
            },
            {
              t: '둘 다 일어날 때 — 직접 바꿔 보기',
              live: {
                params: [
                  { id: 'vx', label: R`\(V_{x}\)`, min: -1, max: 1, step: 0.05, val: 0.5, unit: 'm/s' },
                  { id: 'vy', label: R`\(V_{y}\)`, min: -1, max: 1, step: 0.05, val: 0, unit: 'm/s' },
                  { id: 'qv', label: R`\({}^BV_Q\)`, min: -1, max: 1, step: 0.05, val: 0.3, unit: 'm/s' },
                  { id: 'w', label: R`\(\Omega\)`, min: -2, max: 2, step: 0.05, val: 1, unit: 'rad/s' }
                ],
                apply(S, p) { scene(S); omega(S, p.w); circ(S); velQ(S, p); },
                tex: () => R`{}^AV_Q = \underbrace{{}^AV_{BORG}}_{\text{회색}} + \underbrace{{}^A_BR\,{}^BV_Q}_{\text{분홍}} + \underbrace{{}^A\Omega_B\times{}^A_BR\,{}^BQ}_{\text{파랑}}`,
                vpInfo(p) {
                  const vb = [p.vx, p.vy, 0], vq = mv3(RB, [p.qv, 0, 0]), w = mv3(RB, [0, 0, p.w]), rot = cross(w, sub(QW, p3(TB))), tot = add(add(vb, vq), rot);
                  return vcard('Q의 속도 성분 ({A} 기준, m/s)', [{ s: 'ᴬV<sub>BORG</sub>', v: t3(vb, 2) }, { s: 'R ᴮV<sub>Q</sub>', v: t3(vq, 2), n: '· {B}의 X축 방향 미끄럼' }, { s: 'Ω × R ᴮQ', v: t3(rot, 2) }, { s: 'ᴬV<sub>Q</sub>', v: t3(tot, 2), on: true }]);
                },
                html: () => R`<p>슬라이더로 세 가지 움직임을 따로 켜고 끄며 합이 어떻게 바뀌는지 보세요.</p>
                ${ls([R`\(V_x, V_y\): {B} 원점의 평행 이동 속도`, R`\({}^BV_Q\): Q가 {B}의 \(\hat X_B\) 방향으로 미끄러지는 속도`, R`\(\Omega\): {B}가 \(\hat Z_B\)축으로 도는 각속도`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 4.2 Angular velocity & skew matrix ================= */
  {
    const P0 = [1.1, 0.35, 0.7];
    const Kof = p => [c(p.el) * c(p.az), c(p.el) * s(p.az), s(p.el)];
    const scene = (S, p, lv) => {
      wipe(S);
      const k = Kof(p), Om = scl(k, p.wd), v = cross(Om, P0);
      fr(S, 'A', I(), { label: 'A', size: 0.8 });
      ln(S, 'ax', scl(k, -1.4), scl(k, 1.9), { c: 'k', label: lv >= 1 ? 'K̂' : '', lt: 0.98 });
      pt(S, 'P', P0, 'P', { c: 'pt' });
      vec(S, 'op', O, P0, { c: 'pt', w: 0.6, label: 'ᴬP', lt: 0.45 });
      const cen = scl(k, dot(P0, k)), rr = sub(P0, cen);
      if (lv >= 1) {
        arc(S, 'cp', { c: cen, n: k, u: unit(rr), ang: 359, r: norm(rr), noHead: true, col: 'mute' });
        if (Math.abs(p.wd) > 0.02) vec(S, 'om', O, scl(Om, 0.7), { c: 'k', label: 'Ω = θ̇K̂', w: 1.2, lt: 1.05 });
        if (norm(v) > 0.02) vec(S, 'pd', P0, add(P0, scl(v, 0.8)), { c: 'acc', label: 'Ṗ = Ω × P', w: 1.1, lt: 1.1 });
        ln(S, 'rr', cen, P0, { c: 'mute' });
      }
      return { k, Om, v };
    };
    const v0 = { az: 20, el: 70, wd: 1.2 };
    const Sm = o => [[0, -o[2], o[1]], [o[2], 0, -o[0]], [-o[1], o[0], 0]];
    sec({
      id: 'c4-omega', group: 'lecture', ref: '슬라이드 10–14', title: '4.2 각속도와 반대칭 행렬',
      view: { pos: [3.6, -3.4, 2.6], target: [0.4, 0.2, 0.5] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        return {
          init(S) { scene(S, v0, 0); },
          steps: [
            {
              t: 'RRᵀ = I를 시간에 대해 미분하면',
              tex: R`R R^T = I_3\ \xrightarrow{\ d/dt\ }\ \dot R R^T + R\dot R^T = 0_3\ \Longrightarrow\ S + S^T = 0_3,\qquad S \equiv \dot R R^T`,
              html: R`<p>회전행렬은 항상 \(RR^T = I\)를 만족합니다. 양변을 미분하면 \(\dot RR^T\)와 그 전치의 합이 0이 됩니다.</p>
              <p>\(S + S^T = 0\)을 만족하는 행렬을 <b>반대칭 행렬(skew-symmetric matrix)</b>이라 합니다.</p>`
            },
            {
              t: '반대칭 행렬 = 숫자 3개 = 각속도 벡터',
              tex: R`S = \begin{bmatrix}0 & -\Omega_z & \Omega_y\\ \Omega_z & 0 & -\Omega_x\\ -\Omega_y & \Omega_x & 0\end{bmatrix},\qquad \Omega = \begin{bmatrix}\Omega_x\\ \Omega_y\\ \Omega_z\end{bmatrix}`,
              html: R`<p>\(S+S^T=0\)이면</p>
              ${ls([R`대각 성분은 모두 0`, R`대칭 위치의 성분은 부호만 반대`])}
              <p>그래서 독립인 숫자는 3개뿐이고, 이 3개를 모은 벡터가 바로 <b>각속도 벡터</b> \(\Omega\)입니다.</p>`
            },
            {
              t: 'Ṗ = S P = Ω × P',
              do(S) { scene(S, v0, 1); },
              tex: R`{}^AP = R\,{}^BP\ \Rightarrow\ {}^A\dot P = \dot R\,{}^BP = \dot R R^{T}\,{}^AP = S\,{}^AP = \Omega \times {}^AP`,
              html: R`<p>{B}에 고정된 점 P를 생각합니다(\({}^BP\) 일정).</p>
              ${ls([R`\({}^BP = R^T\,{}^AP\)를 대입하면 \(\dot RR^T = S\)가 나타남`, R`\(S\,P\)를 직접 곱해 보면 외적 \(\Omega\times P\)와 같음`])}
              <p>즉 반대칭 행렬을 곱하는 것 = 각속도와 외적하는 것입니다. 파란 화살표가 회색 원의 접선 방향입니다.</p>`
            },
            {
              t: 'Ω = θ̇ K̂ — 직접 바꿔 보기',
              live: {
                params: [
                  { id: 'az', label: R`\(K\) 방위`, min: -180, max: 180, step: 1, val: v0.az, unit: '°' },
                  { id: 'el', label: R`\(K\) 고도`, min: -90, max: 90, step: 1, val: v0.el, unit: '°' },
                  { id: 'wd', label: R`\(\dot\theta\)`, min: -2, max: 2, step: 0.05, val: v0.wd, unit: 'rad/s' }
                ],
                apply(S, p) { scene(S, p, 1); },
                tex(p) { const k = Kof(p), Om = scl(k, p.wd); return R`\Omega = \dot\theta\hat K = ${cv(Om, 3)},\quad S = ${bm(Sm(Om), 3)},\quad \dot P = S\,P = ${cv(cross(Om, P0), 3)}`; },
                html: () => R`<p>회전축 \(\hat K\)의 방향과 회전 속력 \(\dot\theta\)를 바꿔 보세요.</p>
                ${ls([R`각속도 벡터는 축 방향 단위벡터 × 속력: \(\Omega = \dot\theta\hat K\)`, R`P가 축에 가까울수록(원이 작을수록) 속도가 작아짐`, R`P가 축 위에 있으면 속도 0`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 4.3 Velocity propagation (2-link) ================= */
  const L2 = [1.0, 0.8], Q2 = [30, 60], QD2 = [0.5, 0.8];
  const KW = 0.45, VS = 0.85;
  const velArrows = (S, pr, upto, on) => {
    for (let i = 1; i <= Math.min(upto, 3); i++) {
      arw(S, 'w' + i, 'F' + i, [0, 0, pr.w[i]], KW, { c: 'k', label: `<sup>${i}</sup>ω<sub>${i}</sub>`, w: 0.9, lt: 1.1, op: on && on !== i ? 0.35 : 1 });
      arw(S, 'v' + i, 'F' + i, pr.v[i], VS, { c: 'pt', label: `<sup>${i}</sup>v<sub>${i}</sub>`, w: 1.1, lt: 1.08, op: on && on !== i ? 0.35 : 1 });
    }
  };
  const propCard = (pr, on, q) => vcard('속도 전파 결과 (각 프레임 기준)', [1, 2, 3].map(i => ({ s: `<sup>${i}</sup>ω<sub>${i}</sub>, <sup>${i}</sup>v<sub>${i}</sub>`, v: `${f(pr.w[i], 3)} · ${t3(sub3(pr.v[i], 2), 3)}`, on: on === i })).concat([q ? { s: '⁰v₃', v: t3(sub3(rotv(pr.v[3], q[0] + q[1]), 2), 3), on: on === 4, n: 'm/s' } : null]));
  // frame at the tip with the base orientation (to read ⁰v components there)
  const tipG = (S, show) => fr(S, 'G3', fromRp(R3(base), p3(S.frames.F3.T)), { label: '', size: 0.32, hidden: !show, sub: '0', cols: ['x', 'y', 'z'], op: 0.7 });
  const rotv = (v, a) => [v[0] * c(a) - v[1] * s(a), v[0] * s(a) + v[1] * c(a), v[2] || 0];
  {
    const scene = (S, q, o) => { wipe(S); arm(S, L2, q, Object.assign({ frameOpt: { 0: { size: 0.45 } } }, o)); };
    sec({
      id: 'c4-prop', group: 'lecture', ref: '슬라이드 15–20', title: '4.3 링크에서 링크로: 속도 전파',
      view: { pos: [1.9, -5.0, 2.6], target: [0.65, 0, 0.75] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        const pr = propP(L2, Q2, QD2);
        return {
          init(S) { scene(S, Q2); },
          steps: [
            {
              t: '전파 공식 (회전 관절 · 직동 관절)',
              tex: R`\begin{aligned}&\textbf{revolute:}\ \ {}^{i+1}\omega_{i+1} = {}^{i+1}_{\ \ i}R\,{}^i\omega_i + \dot\theta_{i+1}\,{}^{i+1}\hat Z_{i+1},\quad {}^{i+1}v_{i+1} = {}^{i+1}_{\ \ i}R\left({}^iv_i + {}^i\omega_i\times{}^iP_{i+1}\right)\\ &\textbf{prismatic:}\ {}^{i+1}\omega_{i+1} = {}^{i+1}_{\ \ i}R\,{}^i\omega_i,\qquad\qquad\quad\ \ {}^{i+1}v_{i+1} = {}^{i+1}_{\ \ i}R\left({}^iv_i + {}^i\omega_i\times{}^iP_{i+1}\right) + \dot d_{i+1}\,{}^{i+1}\hat Z_{i+1}\end{aligned}`,
              html: R`<p>로봇은 링크가 사슬처럼 이어져 있으므로, 베이스에서 시작해 한 링크씩 속도를 넘겨줍니다.</p>
              ${ls([R`각속도: 앞 링크의 각속도를 새 프레임으로 돌려 적고, 회전 관절이면 자기 \(\dot\theta\hat Z\)를 더함`, R`선속도: 앞 원점의 속도 + 앞 링크가 돌아서 생기는 \(\omega\times P\), 직동 관절이면 \(\dot d\hat Z\)를 더함`])}
              <p>화면은 관절 2개짜리 평면 팔입니다 (\(l_1=${L2[0]}\), \(l_2=${L2[1]}\) m). {3}은 팔 끝에 있고 {2}와 방향이 같습니다.</p>`
            },
            {
              t: '{1}: 베이스는 멈춰 있음',
              do(S) { velArrows(S, pr, 1); },
              vpInfo: propCard(pr, 1),
              tex: R`{}^0\omega_0 = 0,\ {}^0v_0 = 0\ \Rightarrow\ {}^1\omega_1 = \begin{bmatrix}0\\0\\ \dot\theta_1\end{bmatrix},\quad {}^1v_1 = \begin{bmatrix}0\\0\\0\end{bmatrix}`,
              html: R`<p>{1}의 원점은 관절 1 위에 있어 움직이지 않습니다. 각속도는 관절 1의 회전 \(\dot\theta_1\)뿐이고 방향은 \(\hat Z_1\) (화면 앞쪽)입니다.</p>
              <p>예시 값: \(\theta = (${Q2[0]}^\circ, ${Q2[1]}^\circ)\), \(\dot\theta = (${QD2[0]}, ${QD2[1]})\) rad/s.</p>`
            },
            {
              t: '{2}: 링크 1이 돌아서 생기는 속도',
              do(S) { velArrows(S, pr, 2, 2); },
              vpInfo: propCard(pr, 2),
              tex: R`{}^2\omega_2 = \begin{bmatrix}0\\0\\ \dot\theta_1+\dot\theta_2\end{bmatrix},\qquad {}^2v_2 = {}^2_1R\left({}^1\omega_1\times{}^1P_2\right) = \begin{bmatrix}c_2 & s_2 & 0\\ -s_2 & c_2 & 0\\ 0&0&1\end{bmatrix}\begin{bmatrix}0\\ l_1\dot\theta_1\\ 0\end{bmatrix} = \begin{bmatrix}l_1s_2\dot\theta_1\\ l_1c_2\dot\theta_1\\ 0\end{bmatrix}`,
              html: R`<p>\({}^1P_2 = (l_1, 0, 0)\)이고 \({}^1\omega_1\times{}^1P_2 = (0,\ l_1\dot\theta_1,\ 0)\): 링크 1에 수직인 방향입니다.</p>
              <p>이것을 {2}의 축으로 다시 적으면(\({}^2_1R = {}^1_2R^T\)) 위 결과가 됩니다. 노란 화살표가 링크 1에 수직인 것을 확인하세요.</p>`
            },
            {
              t: '{3}: 끝점의 속도',
              do(S) { velArrows(S, pr, 3, 3); },
              vpInfo: propCard(pr, 3),
              tex: R`{}^3\omega_3 = {}^2\omega_2,\qquad {}^3v_3 = {}^2v_2 + {}^2\omega_2\times{}^2P_3 = \begin{bmatrix}l_1s_2\dot\theta_1\\ l_1c_2\dot\theta_1 + l_2(\dot\theta_1+\dot\theta_2)\\ 0\end{bmatrix}`,
              html: R`<p>{3}은 {2}와 방향이 같으므로 회전행렬은 \(I\)입니다. 관절이 없으니 각속도도 그대로입니다.</p>
              <p>링크 2 길이만큼 떨어진 끝점에는 \(l_2(\dot\theta_1+\dot\theta_2)\)가 더해집니다.</p>`
            },
            {
              t: '⁰v₃: 베이스 축으로 다시 적기',
              do(S) { velArrows(S, pr, 3, 3); const v0 = rotv(pr.v[3], Q2[0] + Q2[1]); tipG(S, true); arw(S, 'v0x', 'G3', [v0[0], 0, 0], VS, { c: 'x', w: 0.6, label: '⁰v<sub>x</sub>', lt: 1.15 }); arw(S, 'v0y', 'G3', [0, v0[1], 0], VS, { c: 'y', w: 0.6, label: '⁰v<sub>y</sub>', lt: 1.15 }); },
              vpInfo: propCard(pr, 4, Q2),
              tex: R`{}^0v_3 = {}^0_3R\,{}^3v_3 = \begin{bmatrix}-l_1s_1\dot\theta_1 - l_2s_{12}(\dot\theta_1+\dot\theta_2)\\ l_1c_1\dot\theta_1 + l_2c_{12}(\dot\theta_1+\dot\theta_2)\\ 0\end{bmatrix},\qquad {}^0_3R = R_Z(\theta_1+\theta_2)`,
              html: R`<p>같은 화살표(같은 물리적 속도)를 {0}의 축으로 분해한 것입니다. 끝점에 {0}과 같은 방향의 축을 겹쳐 그려 두었습니다.</p>
              <p>끝점 위치 \(x = l_1c_1 + l_2c_{12},\ y = l_1s_1+l_2s_{12}\)를 직접 미분해도 같은 결과가 나옵니다.</p>`
            },
            {
              t: '관절 속도를 바꿔 보기',
              live: {
                params: [
                  { id: 'q1', label: R`\(\theta_1\)`, min: -180, max: 180, step: 1, val: Q2[0], unit: '°' },
                  { id: 'q2', label: R`\(\theta_2\)`, min: -170, max: 170, step: 1, val: Q2[1], unit: '°' },
                  { id: 'd1', label: R`\(\dot\theta_1\)`, min: -1.5, max: 1.5, step: 0.05, val: QD2[0], unit: 'rad/s' },
                  { id: 'd2', label: R`\(\dot\theta_2\)`, min: -1.5, max: 1.5, step: 0.05, val: QD2[1], unit: 'rad/s' }
                ],
                drag: dragSpec(rowsOf(L2)),
                apply(S, p) { const q = [p.q1, p.q2]; scene(S, q, { drag: true }); velArrows(S, propP(L2, q, [p.d1, p.d2]), 3); },
                vpInfo(p) { const q = [p.q1, p.q2]; return propCard(propP(L2, q, [p.d1, p.d2]), 4, q); },
                tex(p) { const pr2 = propP(L2, [p.q1, p.q2], [p.d1, p.d2]); return R`{}^3v_3 = \begin{bmatrix}${f(L2[0])}\cdot s_2\cdot ${f(p.d1, 2)}\\ ${f(L2[0])}\cdot c_2\cdot ${f(p.d1, 2)} + ${f(L2[1])}(${f(p.d1, 2)} + ${f(p.d2, 2)})\end{bmatrix} = ${cv(sub3(pr2.v[3], 2), 3)}\ \text{m/s}`; },
                html: () => R`<p>슬라이더나 3D 화면의 링크를 끌어 자세와 관절 속도를 바꿔 보세요.</p>
                ${ls([R`\(\dot\theta_1\)만 있으면 끝점은 원점을 중심으로 도는 방향으로 움직임`, R`\(\dot\theta_2\)만 있으면 관절 2를 중심으로 도는 방향`, R`둘이 섞이면 두 방향의 합`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 4.4 Jacobian ================= */
  {
    const scene = (S, q, o) => { wipe(S); return arm(S, L2, q, Object.assign({ frameOpt: { 0: { size: 0.45 } } }, o)); };
    const cols = (S, q, qd, lv) => {
      const J = J0two(L2[0], L2[1], q), c1 = scl([J[0][0], J[1][0], 0], qd[0]), c2 = scl([J[0][1], J[1][1], 0], qd[1]);
      tipG(S, false);
      arw(S, 'jc1', 'G3', c1, VS, { c: 'j1', label: 'J<sub>:,1</sub> θ̇₁', w: 0.9, lt: 1.12 });
      if (lv >= 2) arw(S, 'jc2', 'G3', c2, VS, { c: 'j2', label: 'J<sub>:,2</sub> θ̇₂', w: 0.9, lt: 1.12 });
      if (lv >= 2) { const tot = add(c1, c2); arw(S, 'jv', 'G3', tot, VS, { c: 'pt', label: '⁰v = J θ̇', w: 1.3, lt: 1.1 }); if (norm(c1) * VS > 0.03 && norm(c2) * VS > 0.03) { ln(S, 'pg1', { f: 'G3', p: scl(c1, VS) }, { f: 'G3', p: scl(tot, VS) }, { c: 'j2' }); ln(S, 'pg2', { f: 'G3', p: scl(c2, VS) }, { f: 'G3', p: scl(tot, VS) }, { c: 'j1' }); } }
      return J;
    };
    sec({
      id: 'c4-jac', group: 'lecture', ref: '슬라이드 21–23', title: '4.4 자코비안: 관절 속도 → 끝점 속도',
      view: { pos: [1.2, -5.4, 1.6], target: [0.6, 0, 0.75] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        return {
          init(S) { scene(S, Q2); },
          steps: [
            {
              t: '자코비안의 정의',
              tex: R`\mathcal X = F(\Theta)\ \Rightarrow\ \dot{\mathcal X} = \frac{\partial F}{\partial\Theta}\dot\Theta = J(\Theta)\,\dot\Theta,\qquad J_{ij} = \frac{\partial F_i}{\partial\theta_j},\qquad {}^0\nu = \begin{bmatrix}{}^0v\\ {}^0\omega\end{bmatrix} = {}^0J(\Theta)\,\dot\Theta`,
              html: R`<p><b>자코비안(Jacobian)</b>은 여러 변수 함수의 미분을 행렬로 모은 것입니다. 로봇에서는</p>
              ${ls([R`입력: 관절 속도 \(\dot\Theta\) (n×1)`, R`출력: 끝점의 선속도와 각속도 \(\nu\) (6×1)`, R`크기: 6×n, 값은 자세 \(\Theta\)에 따라 달라짐 (시간에 따라 변하는 선형 변환)`])}
              <p>앞에 붙은 위첨자는 결과 속도를 표현하는 좌표계입니다.</p>`
            },
            {
              t: '속도 전파 결과를 행렬로: ³J',
              do(S) { const pr = propP(L2, Q2, QD2); velArrows(S, pr, 3, 3); },
              tex: R`{}^3v_3 = \begin{bmatrix}l_1s_2\dot\theta_1\\ l_1c_2\dot\theta_1 + l_2(\dot\theta_1+\dot\theta_2)\end{bmatrix} = \underbrace{\begin{bmatrix}l_1s_2 & 0\\ l_1c_2+l_2 & l_2\end{bmatrix}}_{{}^3J(\Theta)}\begin{bmatrix}\dot\theta_1\\ \dot\theta_2\end{bmatrix}`,
              html: R`<p>4.3절의 \({}^3v_3\)를 \(\dot\theta_1,\dot\theta_2\)의 계수로 정리하면 자코비안이 바로 읽힙니다.</p>
              <p>평면 팔이라 각속도는 \(\omega_z = \dot\theta_1+\dot\theta_2\) 하나뿐이고, 여기서는 선속도 2줄만 씁니다.</p>`
            },
            {
              t: '기준 좌표계 바꾸기: ⁰J = ⁰₃R ³J',
              do(S) { cols(S, Q2, QD2, 2); },
              tex: R`{}^0J = {}^0_3R\;{}^3J = \begin{bmatrix}-l_1s_1 - l_2s_{12} & -l_2s_{12}\\ l_1c_1 + l_2c_{12} & l_2c_{12}\end{bmatrix},\qquad {}^AJ(\Theta) = \begin{bmatrix}{}^A_BR & 0\\ 0 & {}^A_BR\end{bmatrix}{}^BJ(\Theta)`,
              html: R`<p>자코비안의 기준 좌표계를 바꿀 때는 선속도 부분과 각속도 부분을 각각 회전시키면 됩니다.</p>
              <p>화면의 화살표:</p>
              ${ls([R`청록: 첫째 열 × \(\dot\theta_1\) (관절 1만 움직일 때의 끝점 속도)`, R`분홍: 둘째 열 × \(\dot\theta_2\)`, R`노랑: 두 열의 합 = 끝점 속도`])}`
            },
            {
              t: '열 하나 = 관절 하나의 기여 — 직접 바꿔 보기',
              live: {
                params: [
                  { id: 'q1', label: R`\(\theta_1\)`, min: -180, max: 180, step: 1, val: Q2[0], unit: '°' },
                  { id: 'q2', label: R`\(\theta_2\)`, min: -170, max: 170, step: 1, val: Q2[1], unit: '°' },
                  { id: 'd1', label: R`\(\dot\theta_1\)`, min: -1.5, max: 1.5, step: 0.05, val: QD2[0], unit: 'rad/s' },
                  { id: 'd2', label: R`\(\dot\theta_2\)`, min: -1.5, max: 1.5, step: 0.05, val: QD2[1], unit: 'rad/s' }
                ],
                drag: dragSpec(rowsOf(L2)),
                apply(S, p) { scene(S, [p.q1, p.q2], { drag: true }); cols(S, [p.q1, p.q2], [p.d1, p.d2], 2); },
                tex(p) { const J = J0two(L2[0], L2[1], [p.q1, p.q2]); return R`{}^0v = {}^0J\,\dot\Theta = ${bm(J, 3)}\begin{bmatrix}${f(p.d1, 2)}\\ ${f(p.d2, 2)}\end{bmatrix} = ${cv(mv2(J, [p.d1, p.d2]), 3)}\ \text{m/s}`; },
                html: () => R`<p>링크를 끌거나 슬라이더를 움직여 보세요.</p>
                ${ls([R`\(\dot\theta_2 = 0\)이면 노랑 = 청록`, R`둘째 열(분홍)은 항상 링크 2에 수직`, R`첫째 열(청록)은 항상 원점→끝점 선분에 수직`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 4.5 Singularities ================= */
  {
    const VD = [0.5, 0];
    const scene = (S, q, vd, o, lv) => {
      wipe(S);
      const Ts = arm(S, L2, q, Object.assign({ frameOpt: { 0: { size: 0.45 } } }, o));
      tipG(S, false);
      const J = J0two(L2[0], L2[1], q), tip = p3(Ts[3]);
      ellipse(S, 'el', tip, J, 0.55, 'acc');
      if (lv >= 1 && vd) {
        arw(S, 'vd', 'G3', [vd[0], vd[1], 0], VS, { c: 'pt', label: '원하는 v', w: 1.2, lt: 1.12 });
        const { d, Ai } = inv2(J);
        if (Math.abs(d) > 1e-3) { const qd = mv2(Ai, vd); tq(S, 'r1', 'J1', qd[0], 40, { col: 'j1', label: 'θ̇₁', r: 0.32 }); tq(S, 'r2', 'J2', qd[1], 40, { col: 'j2', label: 'θ̇₂', r: 0.28 }); }
      }
      return J;
    };
    const card = (q, vd) => {
      const J = J0two(L2[0], L2[1], q), { d, Ai } = inv2(J), bad = Math.abs(d) < 1e-3, qd = bad ? null : mv2(Ai, vd), big = qd && Math.max(Math.abs(qd[0]), Math.abs(qd[1])) > 3;
      return vcard('특이점까지 얼마나 가까운가', [{ s: 'det J', v: `l₁l₂s₂ = ${f(d, 4)}`, on: Math.abs(d) < 0.1 }, { s: 'θ̇₁', v: bad ? '∞ (역행렬 없음)' : f(qd[0], 3) + ' rad/s', on: big }, { s: 'θ̇₂', v: bad ? '∞ (역행렬 없음)' : f(qd[1], 3) + ' rad/s', on: big }, { s: '', v: null, n: '파란 타원: |θ̇| = 1일 때 끝점이 낼 수 있는 속도들' }]);
    };
    sec({
      id: 'c4-sing', group: 'lecture', ref: '슬라이드 24–25', title: '4.5 특이점: 자코비안의 역행렬이 없을 때',
      view: { pos: [1.2, -5.4, 1.6], target: [0.6, 0, 0.75] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        return {
          init(S) { scene(S, Q2, VD, {}, 0); },
          steps: [
            {
              t: '끝점 속도를 주고 관절 속도 구하기',
              do(S) { scene(S, Q2, VD, {}, 1); },
              vpInfo: card(Q2, VD),
              tex: R`\dot\Theta = J^{-1}(\Theta)\,\nu,\qquad \det\!\left({}^3J\right) = \det\begin{bmatrix}l_1s_2 & 0\\ l_1c_2+l_2 & l_2\end{bmatrix} = l_1l_2\,s_2`,
              html: R`<p>실제 작업에서는 "끝점을 이 속도로 움직이고 싶다"가 주어지고, 이를 위한 관절 속도를 구해야 합니다. 그러려면 \(J\)의 <b>역행렬</b>이 필요합니다.</p>
              ${ls([R`노란 화살표: 원하는 끝점 속도 (\(+\hat X_0\) 방향 0.5 m/s)`, R`관절의 호: 필요한 \(\dot\theta_1, \dot\theta_2\) (길이 ∝ 크기)`, R`파란 타원: 관절 속도의 크기가 1일 때 끝점이 낼 수 있는 속도들`])}`
            },
            {
              t: '특이점: 한 방향으로 움직일 수 없게 됨',
              do(S) { scene(S, [30, 0], VD, {}, 0); },
              view: { pos: [1.6, -5.2, 1.8], target: [0.8, 0, 0.6] },
              vpInfo: card([30, 0], VD),
              tex: R`\det J = l_1l_2s_2 = 0\ \Longleftrightarrow\ \theta_2 = 0^\circ\ \text{(쭉 편 자세)}\ \text{또는}\ 180^\circ\ \text{(완전히 접은 자세)}`,
              html: R`<p>\(\det J = 0\)이 되는 자세를 <b>특이점(singularity)</b>이라 합니다. 타원이 납작한 선으로 찌그러졌습니다.</p>
              ${ls([R`팔을 쭉 편 상태에서는 팔 방향으로 끝점을 움직일 수 없음 (자유도 하나를 잃음)`, R`그 근처에서 그 방향으로 움직이려면 관절 속도가 무한대로 커짐`])}
              <p>특이점의 두 종류:</p>
              ${ls([R`<b>작업공간 경계 특이점(workspace-boundary)</b>: 팔을 다 펴거나 다 접어 작업공간 경계에 닿을 때`, R`<b>작업공간 내부 특이점(workspace-interior)</b>: 작업공간 안쪽에서 관절축 둘 이상이 한 줄로 정렬될 때 (공간 로봇에서 발생)`])}`
            },
            {
              t: '특이점에 다가가 보기',
              live: {
                params: [
                  { id: 'q1', label: R`\(\theta_1\)`, min: -180, max: 180, step: 1, val: Q2[0], unit: '°' },
                  { id: 'q2', label: R`\(\theta_2\)`, min: -180, max: 180, step: 0.5, val: Q2[1], unit: '°' },
                  { id: 'vx', label: R`\(v_x\)`, min: -1, max: 1, step: 0.05, val: VD[0], unit: 'm/s' },
                  { id: 'vy', label: R`\(v_y\)`, min: -1, max: 1, step: 0.05, val: VD[1], unit: 'm/s' }
                ],
                drag: dragSpec(rowsOf(L2)),
                apply(S, p) { scene(S, [p.q1, p.q2], [p.vx, p.vy], { drag: true }, 1); },
                vpInfo(p) { return card([p.q1, p.q2], [p.vx, p.vy]); },
                assume: p => [{ t: R`\(\theta_2 \ne 0^\circ, \pm180^\circ\) (특이점이 아님)`, ok: Math.abs(s(p.q2)) > 0.02 }],
                tex(p) { const J = J0two(L2[0], L2[1], [p.q1, p.q2]), { d, Ai } = inv2(J); return Math.abs(d) < 1e-3 ? R`\det J = ${f(d, 4)}\ \Rightarrow\ J^{-1}\ \text{없음}` : R`\dot\Theta = {}^0J^{-1}v = \frac{1}{${f(d, 4)}}${bm([[J[1][1], -J[0][1]], [-J[1][0], J[0][0]]], 3)}${cv([p.vx, p.vy], 2)} = ${cv(mv2(Ai, [p.vx, p.vy]), 3)}\ \text{rad/s}`; },
                html: () => R`<p>\(\theta_2\)를 0°에 가깝게 끌어 보세요.</p>
                ${ls([R`타원이 점점 납작해짐`, R`팔 방향의 속도를 요구하면 관절 속도(호)가 급격히 커짐`, R`팔에 수직인 방향의 속도는 여전히 쉽게 만들 수 있음`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 4.6 Static forces ================= */
  const F2 = [6, 8], FS = 0.06, KN = 0.05, KT = 12;
  const statArrows = (S, st, upto, on) => {
    const op = i => (on && on !== i ? 0.35 : 1);
    if (upto >= 3) arw(S, 'f3', 'F3', st.f[3], FS, { c: 'warn', label: '³f₃ = F', w: 1.2, lt: 1.08, op: op(3) });
    for (let i = 2; i >= 1; i--) {
      if (upto < (i === 2 ? 4 : 5)) continue;
      arw(S, 'f' + i, 'F' + i, st.f[i], FS, { c: 'warn', label: `<sup>${i}</sup>f<sub>${i}</sub>`, w: 0.9, lt: 1.08, op: op(i) });
      arw(S, 'n' + i, 'F' + i, st.n[i], KN, { c: 'k', label: `<sup>${i}</sup>n<sub>${i}</sub>`, w: 0.9, lt: 1.1, op: op(i) });
      tq(S, 't' + i, 'J' + i, st.n[i][2], KT, { col: 'j' + i, label: `τ${i === 1 ? '₁' : '₂'}`, r: i === 1 ? 0.34 : 0.28, op: op(i) });
    }
  };
  const statCard = (st, on) => vcard('힘 전파 결과 (각 프레임 기준)', [{ s: '³f₃', v: t3(sub3(st.f[3], 2), 2) + ' N', on: on === 3 }, { s: '²f₂, ²n₂', v: `${t3(sub3(st.f[2], 2), 2)} N · n<sub>z</sub> = ${f(st.n[2][2], 3)} N·m`, on: on === 2 }, { s: '¹f₁, ¹n₁', v: `${t3(sub3(st.f[1], 2), 2)} N · n<sub>z</sub> = ${f(st.n[1][2], 3)} N·m`, on: on === 1 }, { s: 'τ', v: `(${f(st.tau[0], 3)}, ${f(st.tau[1], 3)}) N·m`, on: on === 4 }]);
  {
    const scene = (S, q, o) => { wipe(S); arm(S, L2, q, Object.assign({ frameOpt: { 0: { size: 0.45 } } }, o)); };
    sec({
      id: 'c4-static', group: 'lecture', ref: '슬라이드 26–29', title: '4.6 정역학: 끝점의 힘을 버티는 관절 토크',
      view: { pos: [1.9, -5.0, 2.6], target: [0.65, 0, 0.75] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        const st = statP(L2, Q2, F2, 0);
        return {
          init(S) { scene(S, Q2); },
          steps: [
            {
              t: '링크 하나의 힘·모멘트 평형',
              tex: R`\begin{aligned}&{}^if_i - {}^i_{i+1}R\,{}^{i+1}f_{i+1} = 0, \qquad {}^in_i - {}^i_{i+1}R\,{}^{i+1}n_{i+1} - {}^iP_{i+1}\times{}^if_{i+1} = 0\\ \Rightarrow\ &{}^if_i = {}^i_{i+1}R\,{}^{i+1}f_{i+1},\qquad {}^in_i = {}^i_{i+1}R\,{}^{i+1}n_{i+1} + {}^iP_{i+1}\times{}^if_i\\ &\tau_i = {}^in_i^{\,T}\,{}^i\hat Z_i\ \ \text{(revolute)},\qquad \tau_i = {}^if_i^{\,T}\,{}^i\hat Z_i\ \ \text{(prismatic)}\end{aligned}`,
              html: R`<p>로봇이 정지한 채로 끝점이 환경을 밀고 있을 때, 각 관절이 내야 하는 토크를 구합니다(중력 무시).</p>
              ${ls([R`\(f_i\): 링크 \(i-1\)이 링크 \(i\)에 가하는 힘`, R`\(n_i\): 링크 \(i-1\)이 링크 \(i\)에 가하는 모멘트`, R`각 링크에서 힘의 합 = 0, 모멘트의 합 = 0`])}
              <p>속도는 베이스→끝으로, 힘은 반대로 <b>끝→베이스</b>로 전파합니다. 관절 토크는 모멘트(또는 힘)의 \(\hat Z\) 성분입니다.</p>`
            },
            {
              t: '끝에서 시작: ³f₃ = F, ³n₃ = 0',
              do(S) { statArrows(S, st, 3, 3); },
              vpInfo: statCard(st, 3),
              tex: R`{}^3f_3 = \begin{bmatrix}f_x\\ f_y\\ 0\end{bmatrix} = \begin{bmatrix}${F2[0]}\\ ${F2[1]}\\ 0\end{bmatrix}\ \text{N},\qquad {}^3n_3 = 0`,
              html: R`<p>손끝이 환경에 가하는 힘 \({}^3F\)를 빨간 화살표로 표시했습니다. {3}의 축으로 적은 성분입니다.</p>`
            },
            {
              t: '{2}: 링크 2가 받는 힘과 모멘트',
              do(S) { statArrows(S, st, 4, 2); },
              vpInfo: statCard(st, 2),
              tex: R`{}^2f_2 = \begin{bmatrix}f_x\\ f_y\\ 0\end{bmatrix},\qquad {}^2n_2 = {}^2P_3\times{}^2f_2 = \begin{bmatrix}l_2\\0\\0\end{bmatrix}\times\begin{bmatrix}f_x\\ f_y\\ 0\end{bmatrix} = \begin{bmatrix}0\\0\\ l_2f_y\end{bmatrix}`,
              html: R`<p>{2}와 {3}은 방향이 같아 회전행렬이 \(I\)입니다.</p>
              ${ls([R`힘은 그대로 전달`, R`모멘트는 팔 길이 \(l_2\) × 링크에 수직인 힘 \(f_y\)`, R`\(\tau_2 = l_2f_y\) (분홍 호)`])}`
            },
            {
              t: '{1}: 링크 1까지',
              do(S) { statArrows(S, st, 5, 1); },
              vpInfo: statCard(st, 1),
              tex: R`{}^1f_1 = {}^1_2R\,{}^2f_2 = \begin{bmatrix}c_2f_x - s_2f_y\\ s_2f_x + c_2f_y\\ 0\end{bmatrix},\qquad {}^1n_1 = {}^1_2R\,{}^2n_2 + {}^1P_2\times{}^1f_1 = \begin{bmatrix}0\\0\\ l_1s_2f_x + l_1c_2f_y + l_2f_y\end{bmatrix}`,
              html: R`<p>힘을 {1}의 축으로 돌려 적고, 모멘트에는 링크 1 길이만큼의 팔(\({}^1P_2 = (l_1,0,0)\))이 더해집니다.</p>
              <p>청록 호가 \(\tau_1\)입니다. 모멘트 화살표(보라)는 모두 \(\hat Z\) 방향입니다.</p>`
            },
            {
              t: '정리: τ = (행렬) × F',
              do(S) { statArrows(S, st, 5); },
              vpInfo: statCard(st, 4),
              tex: R`\tau = \begin{bmatrix}\tau_1\\ \tau_2\end{bmatrix} = \begin{bmatrix}l_1s_2 & l_2 + l_1c_2\\ 0 & l_2\end{bmatrix}\begin{bmatrix}f_x\\ f_y\end{bmatrix} = ${cv(st.tau, 3)}\ \text{N·m}`,
              html: R`<p>관절 토크가 끝점 힘에 대해 <b>선형</b>입니다. 이 2×2 행렬을 잘 봐 두세요. 다음 절에서 4.4절의 \({}^3J\)와 비교합니다.</p>`
            },
            {
              t: '힘과 자세를 바꿔 보기',
              live: {
                params: [
                  { id: 'q1', label: R`\(\theta_1\)`, min: -180, max: 180, step: 1, val: Q2[0], unit: '°' },
                  { id: 'q2', label: R`\(\theta_2\)`, min: -170, max: 170, step: 1, val: Q2[1], unit: '°' },
                  { id: 'fx', label: R`\(f_x\)`, min: -10, max: 10, step: 0.5, val: F2[0], unit: 'N' },
                  { id: 'fy', label: R`\(f_y\)`, min: -10, max: 10, step: 0.5, val: F2[1], unit: 'N' }
                ],
                drag: dragSpec(rowsOf(L2)),
                apply(S, p) { const q = [p.q1, p.q2]; scene(S, q, { drag: true }); statArrows(S, statP(L2, q, [p.fx, p.fy], 0), 5); },
                vpInfo(p) { return statCard(statP(L2, [p.q1, p.q2], [p.fx, p.fy], 0), 4); },
                tex(p) { const st2 = statP(L2, [p.q1, p.q2], [p.fx, p.fy], 0); return R`\tau = \begin{bmatrix}${f(L2[0])}s_2 & ${f(L2[1])} + ${f(L2[0])}c_2\\ 0 & ${f(L2[1])}\end{bmatrix}${cv([p.fx, p.fy], 1)} = ${cv(st2.tau, 3)}\ \text{N·m}`; },
                html: () => R`<p>힘은 {3}(끝점 프레임) 기준 성분입니다.</p>
                ${ls([R`\(f_y = 0\)이면(링크 2 방향으로만 밀면) \(\tau_2 = 0\)`, R`\(\theta_2 = 0\)이고 \(f_y = 0\)이면 \(\tau_1\)도 0: 쭉 편 팔이 길이 방향 힘을 토크 없이 버팀`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 4.7 τ = Jᵀ F ================= */
  {
    const scene = (S, q, F0, o) => {
      wipe(S); arm(S, L2, q, Object.assign({ frameOpt: { 0: { size: 0.45 } } }, o)); tipG(S, false);
      arw(S, 'F', 'G3', [F0[0], F0[1], 0], FS, { c: 'warn', label: '⁰F', w: 1.2, lt: 1.1 });
      const J = J0two(L2[0], L2[1], q), tau = [J[0][0] * F0[0] + J[1][0] * F0[1], J[0][1] * F0[0] + J[1][1] * F0[1]];
      tq(S, 't1', 'J1', tau[0], KT, { col: 'j1', label: 'τ₁', r: 0.34 }); tq(S, 't2', 'J2', tau[1], KT, { col: 'j2', label: 'τ₂', r: 0.28 });
      return { J, tau };
    };
    const Fof = p => [p.fm * c(p.fa), p.fm * s(p.fa)];
    const v0 = { q1: 30, q2: 60, fm: 10, fa: 200 };
    sec({
      id: 'c4-jt', group: 'lecture', ref: '슬라이드 30–31', title: '4.7 τ = Jᵀ𝓕와 가상 일의 원리',
      view: { pos: [1.2, -5.4, 1.6], target: [0.6, 0, 0.75] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        return {
          init(S) { scene(S, [v0.q1, v0.q2], Fof(v0)); },
          steps: [
            {
              t: '4.6절의 행렬 = ³J의 전치',
              tex: R`{}^3J = \begin{bmatrix}l_1s_2 & 0\\ l_1c_2+l_2 & l_2\end{bmatrix}\ \Rightarrow\ {}^3J^T = \begin{bmatrix}l_1s_2 & l_1c_2+l_2\\ 0 & l_2\end{bmatrix}\qquad\therefore\ \tau = {}^3J^T\,{}^3\mathcal F`,
              html: R`<p>4.6절에서 힘을 전파해 얻은 행렬이 4.4절 자코비안의 <b>전치(transpose)</b>와 정확히 같습니다. 우연이 아닙니다.</p>
              <p>일반적으로 \(\tau = J^T\mathcal F\)이며, \(\mathcal F\)는 끝점의 힘·모멘트 벡터(6×1)입니다.</p>`
            },
            {
              t: '이유: 가상 일의 원리',
              tex: R`\mathcal F\cdot\delta\mathcal X = \tau\cdot\delta\Theta,\quad \delta\mathcal X = J\,\delta\Theta\ \Rightarrow\ \mathcal F^TJ\,\delta\Theta = \tau^T\delta\Theta\quad(\forall\,\delta\Theta)\ \Rightarrow\ \tau = J^T\mathcal F`,
              html: R`<p><b>가상 일의 원리(principle of virtual work)</b>: 아주 작은 가상의 변위를 줄 때, 한 일은 어느 좌표로 계산해도 같아야 합니다.</p>
              ${ls([R`직교 좌표에서 한 일: 끝점 힘 · 끝점 변위 \(\mathcal F\cdot\delta\mathcal X\)`, R`관절 좌표에서 한 일: 관절 토크 · 관절 변위 \(\tau\cdot\delta\Theta\)`, R`\(\delta\mathcal X = J\delta\Theta\)를 대입하면 모든 \(\delta\Theta\)에 대해 성립해야 하므로 \(\tau = J^T\mathcal F\)`])}`
            },
            {
              t: '좌표계를 맞춰서: τ = ⁰Jᵀ ⁰F',
              do(S) { scene(S, [v0.q1, v0.q2], Fof(v0)); },
              tex: (() => { const F0 = Fof(v0), J = J0two(L2[0], L2[1], [v0.q1, v0.q2]); return R`\tau = {}^0J^T\,{}^0F = ${bm([[J[0][0], J[1][0]], [J[0][1], J[1][1]]], 3)}${cv(F0, 3)} = ${cv([J[0][0] * F0[0] + J[1][0] * F0[1], J[0][1] * F0[0] + J[1][1] * F0[1]], 3)}\ \text{N·m}`; })(),
              html: R`<p>힘이 {0} 기준으로 주어지면 \({}^0J\)를 씁니다. <b>자코비안과 힘은 같은 좌표계</b>여야 합니다.</p>
              <p>예: \(|F| = ${v0.fm}\) N, 방향 \(${v0.fa}^\circ\) (X₀에서 잰 각).</p>`
            },
            {
              t: '특이 자세에서는 토크 없이 버티는 힘이 있다',
              do(S) { const F0 = [10 * c(30), 10 * s(30)]; scene(S, [30, 0], F0); },
              tex: R`\theta_2 = 0^\circ:\quad {}^3J^T = \begin{bmatrix}0 & l_1+l_2\\ 0 & l_2\end{bmatrix}\ \Rightarrow\ {}^3\mathcal F = \begin{bmatrix}f_x\\ 0\end{bmatrix}\ \text{이면}\ \tau = 0`,
              html: R`<p>팔을 쭉 편 자세에서 <b>팔 방향</b>으로 미는 힘은 관절 토크 없이 구조물이 그대로 버팁니다(호가 사라짐).</p>
              ${ls([R`속도: 그 방향으로 움직일 수 없음 (4.5절)`, R`힘: 그 방향의 힘은 토크 없이 버팀`])}
              <p>같은 현상의 두 얼굴입니다. \(J\)가 특이하면 \(J^T\)도 특이합니다.</p>`
            },
            {
              t: '힘의 방향을 돌려 보기',
              live: {
                params: [
                  { id: 'q1', label: R`\(\theta_1\)`, min: -180, max: 180, step: 1, val: v0.q1, unit: '°' },
                  { id: 'q2', label: R`\(\theta_2\)`, min: -170, max: 170, step: 1, val: v0.q2, unit: '°' },
                  { id: 'fm', label: R`\(|F|\)`, min: 0, max: 12, step: 0.5, val: v0.fm, unit: 'N' },
                  { id: 'fa', label: '방향', min: -180, max: 360, step: 1, val: v0.fa, unit: '°' }
                ],
                drag: dragSpec(rowsOf(L2)),
                apply(S, p) { scene(S, [p.q1, p.q2], Fof(p), { drag: true }); },
                vpInfo(p) { const r = (() => { const J = J0two(L2[0], L2[1], [p.q1, p.q2]), F0 = Fof(p); return [J[0][0] * F0[0] + J[1][0] * F0[1], J[0][1] * F0[0] + J[1][1] * F0[1]]; })(); return vcard('관절 토크 (N·m)', [{ s: 'τ₁', v: f(r[0], 3), on: Math.abs(r[0]) < 0.05 }, { s: 'τ₂', v: f(r[1], 3), on: Math.abs(r[1]) < 0.05 }, { s: '', n: '강조된 줄 = 그 관절은 토크 없이 버팀' }]); },
                tex(p) { const J = J0two(L2[0], L2[1], [p.q1, p.q2]), F0 = Fof(p); return R`\tau = {}^0J^T\,{}^0F = ${bm([[J[0][0], J[1][0]], [J[0][1], J[1][1]]], 3)}${cv(F0, 2)} = ${cv([J[0][0] * F0[0] + J[1][0] * F0[1], J[0][1] * F0[0] + J[1][1] * F0[1]], 3)}`; },
                html: () => R`<p>힘의 방향을 바꾸며 토크가 0이 되는 방향을 찾아보세요.</p>
                ${ls([R`\(\tau_2 = 0\): 힘이 링크 2와 나란할 때`, R`\(\tau_1 = 0\): 힘의 작용선이 관절 1을 지날 때`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* ================= 4.8 Cartesian transforms T_υ, T_f (force sensor) ================= */
  const DSs = 4, FSs = 0.05, NSs = 0.25;
  const sensorScene = (S, px, pz) => {
    wipe(S);
    const TS = fromRp(R3(rx(180)), [0, 0, 1.4]), TT = mul(TS, tr(px * DSs, 0, pz * DSs));
    fr(S, 'W', I(), { hidden: true });
    fr(S, 'S', TS, { label: 'S', size: 0.38, cols: ['j5', 'j5', 'j5'] });
    fr(S, 'T', TT, { label: 'T', size: 0.32, cols: ['warn', 'warn', 'warn'] });
    body(S, 'll', 'S', 'box', [0.45, 0.4, 0.7], [0, 0, -0.68], { c: 'body' });
    body(S, 'sn', 'S', 'box', [0.7, 0.5, 0.3], [0, 0, -0.16], { c: 'j5', op: 0.45 });
    body(S, 'tv', 'S', 'box', [0.06, 0.06, pz * DSs], [0, 0, pz * DSs / 2], { c: 'ink' });
    body(S, 'th', 'S', 'box', [px * DSs + 0.03, 0.06, 0.06], [px * DSs / 2, 0, pz * DSs], { c: 'ink' });
    ln(S, 'dz', { f: 'S', p: [-0.32, 0, 0] }, { f: 'S', p: [-0.32, 0, pz * DSs] }, { c: 'mute', label: `${f(pz, 3)} m`, lo: [-0.2, 0, 0] });
    ln(S, 'dx', { f: 'S', p: [0, 0, pz * DSs + 0.22] }, { f: 'S', p: [px * DSs, 0, pz * DSs + 0.22] }, { c: 'mute', label: `${f(px, 3)} m`, lo: [0, 0, -0.12] });
    return { TS, TT };
  };
  const skew = p => [[0, -p[2], p[1]], [p[2], 0, -p[0]], [-p[1], p[0], 0]];
  const Tf6 = (Rm, P) => { const PR = skew(P).map(r => [0, 1, 2].map(j => r[0] * Rm[0][j] + r[1] * Rm[1][j] + r[2] * Rm[2][j])); return [0, 1, 2, 3, 4, 5].map(i => [0, 1, 2, 3, 4, 5].map(j => i < 3 ? (j < 3 ? Rm[i][j] : 0) : (j < 3 ? PR[i - 3][j] : Rm[i - 3][j - 3]))); };
  const sensorForces = (S, sF, sN, tF, tN, lv) => {
    arw(S, 'sF', 'S', sF, FSs, { c: 'warn', label: 'ˢF', w: 1.1, lt: 1.08 });
    arw(S, 'sN', 'S', sN, NSs, { c: 'k', label: 'ˢN', w: 1.1, lt: 1.12 });
    if (lv >= 1) { arw(S, 'tF', 'T', tF, FSs, { c: 'warn', label: 'ᵀF', w: 1.1, lt: 1.08 }); arw(S, 'tN', 'T', tN, NSs, { c: 'k', label: 'ᵀN', w: 1.1, lt: 1.12 }); }
  };
  const tipFT = (px, pz, sF, sN) => { const P = [-px, 0, -pz]; return { P, tF: sF.slice(), tN: add(cross(P, sF), sN) }; };
  {
    const v0 = { fx: 5, fz: -10, ny: 2 }, px = 0.1, pz = 0.2;
    sec({
      id: 'c4-cart', group: 'lecture', ref: '슬라이드 32–35', title: '4.8 속도·힘의 좌표 변환 (T_υ, T_f)',
      view: { pos: [0.9, -4.6, 1.3], target: [0.2, 0, 1.0] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      build() {
        return {
          init(S) { sensorScene(S, px, pz); },
          steps: [
            {
              t: '같은 강체 위 두 프레임의 속도 변환',
              tex: R`\begin{bmatrix}{}^Av_A\\ {}^A\omega_A\end{bmatrix} = \underbrace{\begin{bmatrix}{}^A_BR & -{}^A_BR\;{}^BP_{AORG}\times\\ 0 & {}^A_BR\end{bmatrix}}_{{}^A_BT_\upsilon}\begin{bmatrix}{}^Bv_B\\ {}^B\omega_B\end{bmatrix}`,
              html: R`<p>{A}와 {B}가 같은 강체에 붙어 있으면 각속도는 같고, 선속도는 원점 사이 거리만큼 \(\omega\times P\)가 더해집니다.</p>
              ${ls([R`\({}^Av_A = {}^A_BR\left({}^Bv_B + {}^B\omega_B\times{}^BP_{AORG}\right)\)`, R`\({}^A\omega_A = {}^A_BR\,{}^B\omega_B\)`])}
              <p>이를 6×6 행렬 하나로 묶은 것이 <b>속도 변환 행렬</b> \(T_\upsilon\)입니다. 화면: 힘 센서 {S}와 공구 끝 {T}.</p>`
            },
            {
              t: '힘·모멘트의 변환',
              tex: R`\begin{bmatrix}{}^AF_A\\ {}^AN_A\end{bmatrix} = \underbrace{\begin{bmatrix}{}^A_BR & 0\\ {}^AP_{BORG}\times{}^A_BR & {}^A_BR\end{bmatrix}}_{{}^A_BT_f}\begin{bmatrix}{}^BF_B\\ {}^BN_B\end{bmatrix},\qquad {}^A_BT_f = {}^B_AT_\upsilon^{\,T}`,
              html: R`<p>힘은 그대로 돌려 적고, 모멘트에는 <b>지렛대 효과</b> \(P\times F\)가 더해집니다(4.6절의 \(n_i\) 식과 같은 구조).</p>
              <p>속도 변환과 힘 변환은 서로 전치 관계입니다. 가상 일의 원리에서 나온 \(\tau = J^T\mathcal F\)와 같은 이유입니다.</p>`
            },
            {
              t: '외적을 행렬로: P×',
              tex: R`P\times = \begin{bmatrix}0 & -p_z & p_y\\ p_z & 0 & -p_x\\ -p_y & p_x & 0\end{bmatrix},\qquad (P\times)\,F = P\times F`,
              html: R`<p>6×6 행렬 안의 \(P\times\)는 4.2절의 반대칭 행렬과 같은 모양입니다. 벡터 \(P\)를 "외적하는 연산자"로 바꾼 것입니다.</p>`
            },
            {
              t: '힘 센서 읽기를 공구 끝으로 — 직접 바꿔 보기',
              live: {
                params: [
                  { id: 'fx', label: R`\({}^SF_x\)`, min: -12, max: 12, step: 0.5, val: v0.fx, unit: 'N' },
                  { id: 'fz', label: R`\({}^SF_z\)`, min: -12, max: 12, step: 0.5, val: v0.fz, unit: 'N' },
                  { id: 'ny', label: R`\({}^SN_y\)`, min: -3, max: 3, step: 0.1, val: v0.ny, unit: 'N·m' }
                ],
                apply(S, p) { sensorScene(S, px, pz); const sF = [p.fx, 0, p.fz], sN = [0, p.ny, 0], r = tipFT(px, pz, sF, sN); sensorForces(S, sF, sN, r.tF, r.tN, 1); },
                tex(p) { const sF = [p.fx, 0, p.fz], sN = [0, p.ny, 0], r = tipFT(px, pz, sF, sN); return R`{}^TN = {}^TP_{SORG}\times{}^SF + {}^SN = ${cv(r.P, 2)}\times${cv(sF, 2)} + ${cv(sN, 2)} = ${cv(r.tN, 3)}\ \text{N·m}`; },
                vpInfo(p) { const sF = [p.fx, 0, p.fz], sN = [0, p.ny, 0], r = tipFT(px, pz, sF, sN); return vcard('센서 → 공구 끝', [{ s: 'ˢF', v: t3(sF, 2) + ' N' }, { s: 'ˢN', v: t3(sN, 2) + ' N·m' }, { s: 'ᵀF', v: t3(r.tF, 2) + ' N' }, { s: 'ᵀN', v: t3(r.tN, 3) + ' N·m', on: true }]); },
                html: () => R`<p>{S}와 {T}는 방향이 같으므로 \(R = I\)이고 \({}^TP_{SORG} = (-${px}, 0, -${pz})\) m입니다.</p>
                ${ls([R`힘은 그대로: \({}^TF = {}^SF\)`, R`모멘트는 지렛대 항만큼 달라짐`, R`기본값(과제 3 문제 3)에서는 공구 끝 모멘트가 0`])}`
              }
            }
          ]
        };
      }
    });
  }

  /* =========================================================
     Homework 3
     ========================================================= */
  const pick = (a, b) => a + Math.floor(Math.random() * (b - a + 1));

  /* ---------- HW3 P1: RP manipulator ---------- */
  const R12 = [[0, 0, 1], [1, 0, 0], [0, 1, 0]];
  const DSr = 2.4, VSr = 3;
  function rpScene(S, p, o) {
    o = o || {};
    wipe(S);
    const T0 = base, T1 = mul(base, rz(p.t1)), T2 = mul(mul(T1, tr(p.d2 * DSr, 0, 0)), fromRp(R12, O));
    fr(S, 'F0', T0, { label: '0', size: 0.75 });
    fr(S, 'F1', T1, { label: '1', size: 0.5, cols: ['j1', 'j1', 'j1'] });
    fr(S, 'F2', T2, { label: '2', size: 0.42 });
    const dg = o.drag ? 'q1' : null;
    body(S, 'hub', 'F1', 'cyl', [0.11, 0.2], [0, 0, 0], { c: 'j1', drag: dg });
    body(S, 'slv', 'F1', 'box', [0.62, 0.17, 0.17], [0.31, 0, 0], { c: 'j1', drag: dg });
    body(S, 'rod', 'F1', 'box', [p.d2 * DSr, 0.07, 0.07], [p.d2 * DSr / 2, 0, 0], { c: 'j2', drag: o.drag ? 'd2' : null });
    body(S, 'tip', 'F2', 'sph', [0.08], [0, 0, 0], { c: 'ink', drag: o.drag ? 'd2' : null });
    arc(S, 'a1', { f: 'F0', c: [0, 0, 0], n: Z, u: X, ang: p.t1, r: 0.95, col: 'j1', label: 'θ₁' });
    ln(S, 'dd', { f: 'F1', p: [0, -0.3, 0] }, { f: 'F1', p: [p.d2 * DSr, -0.3, 0] }, { c: 'mute', label: 'd₂', lo: [0, 0, 0.1] });
  }
  const rpVel = (p) => ({ w2: [0, p.td1, 0], v2: [p.d2 * p.td1, 0, p.dd2], v0: [-p.d2 * s(p.t1) * p.td1 + c(p.t1) * p.dd2, p.d2 * c(p.t1) * p.td1 + s(p.t1) * p.dd2] });
  const rpArrows = (S, p, lv) => {
    const r = rpVel(p);
    arw(S, 'w2', 'F2', r.w2, 1.2, { c: 'k', label: '²ω₂', w: 0.9, lt: 1.1 });
    if (lv >= 1) {
      arw(S, 'vx', 'F2', [r.v2[0], 0, 0], VSr, { c: 'x', label: 'd₂θ̇₁ X̂₂', w: 0.8, lt: 1.12, lo: [0, 0, 0.14] });
      arw(S, 'vz', 'F2', [0, 0, r.v2[2]], VSr, { c: 'z', label: 'ḋ₂ Ẑ₂', w: 0.8, lt: 1.15 });
      arw(S, 'vs', 'F2', r.v2, VSr, { c: 'pt', label: '²v₂', w: 1.3, lt: 1.1 });
    }
    return r;
  };
  sec({
    id: 'c4-hw-rp', group: 'practice', ref: '과제 3 · 문제 1', title: 'RP 팔: 속도 전파와 자코비안',
    view: { pos: [1.2, -5.0, 1.4], target: [0.7, 0, 0.55] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
    params: {
      orig: { t1: 30, d2: 0.5, td1: 0.2, dd2: 0.1 }, origLabel: '과제 숫자',
      rand() { return { t1: pick(4, 14) * 5, d2: pick(3, 9) / 10, td1: pick(1, 6) / 10 * (Math.random() < 0.25 ? -1 : 1), dd2: pick(-3, 3) / 20 || 0.05 }; }
    },
    build(P) {
      const p = P, r = rpVel(p), sp = Math.hypot(r.v0[0], r.v0[1]);
      return {
        answers: [
          { label: R`\({}^0v_x\)`, val: r.v0[0], unit: 'm/s', tol: 0.0006, dp: 4 },
          { label: R`\({}^0v_y\)`, val: r.v0[1], unit: 'm/s', tol: 0.0006, dp: 4 },
          { label: R`\(|{}^0v_2|\)`, val: sp, unit: 'm/s', tol: 0.0006, dp: 4 }
        ],
        calcData: { r, sp },
        init(S) { rpScene(S, p); },
        steps: [
          {
            t: '문제',
            tex: R`\begin{bmatrix}{}^0v_x\\ {}^0v_y\end{bmatrix} = {}^0J(\Theta)\begin{bmatrix}\dot\theta_1\\ \dot d_2\end{bmatrix},\qquad \theta_1 = ${p.t1}^\circ,\ d_2 = ${p.d2}\ \text{m},\ \dot\theta_1 = ${p.td1}\ \text{rad/s},\ \dot d_2 = ${p.dd2}\ \text{m/s}`,
            html: R`<p>회전 관절 1(\(\theta_1\))과 직동 관절 2(\(d_2\))를 가진 RP 팔입니다.</p>
            <ol class="ls"><li>속도 전파 공식으로 \({}^2\omega_2\), \({}^2v_2\)를 구하시오.</li><li>공구 속도를 {0}에서 표현한 \({}^0v_2\)와 2×2 자코비안 \({}^0J(\Theta)\)를 쓰시오.</li><li>\({}^0_2T\)에서 얻은 \({}^0P_2\)를 직접 미분해 (2)를 확인하시오.</li><li>위 숫자에서 \({}^0v_2\)와 그 크기를 구하시오.</li></ol>`
          },
          {
            t: '그림에서 프레임 읽기',
            tex: R`{}^1_2R = \begin{bmatrix}\hat X_2 & \hat Y_2 & \hat Z_2\end{bmatrix}_{\{1\}} = \begin{bmatrix}0&0&1\\ 1&0&0\\ 0&1&0\end{bmatrix},\qquad {}^1P_{2} = \begin{bmatrix}d_2\\0\\0\end{bmatrix},\qquad {}^0_1R = R_Z(\theta_1)`,
            html: R`<p>그림에서 각 축이 가리키는 방향을 {1}의 축으로 적습니다({1}의 \(\hat X_1\)은 팔 방향).</p>
            ${ls([R`\(\hat Z_2\): 팔 방향 = \(\hat X_1\) → (1, 0, 0)`, R`\(\hat X_2\): 팔에 수직, 왼쪽 위 = \(\hat Y_1\) → (0, 1, 0)`, R`\(\hat Y_2 = \hat Z_2\times\hat X_2 = \hat Z_1\) (화면 앞쪽) → (0, 0, 1)`])}
            <p>이 세 열을 나란히 놓으면 \({}^1_2R\)입니다. {2}의 원점은 팔을 따라 \(d_2\)만큼 떨어져 있습니다.</p>`
          },
          {
            t: '{1}: 회전 관절 1',
            do(S) { arw(S, 'w1', 'F1', [0, 0, p.td1], 1.2, { c: 'k', label: '¹ω₁', w: 0.9, lt: 1.1 }); },
            tex: R`{}^1\omega_1 = {}^1_0R\,{}^0\omega_0 + \dot\theta_1\,{}^1\hat Z_1 = \begin{bmatrix}0\\0\\ \dot\theta_1\end{bmatrix},\qquad {}^1v_1 = {}^1_0R\left({}^0v_0 + {}^0\omega_0\times{}^0P_1\right) = \begin{bmatrix}0\\0\\0\end{bmatrix}`,
            html: R`<p>베이스는 정지(\(\omega_0 = v_0 = 0\))해 있고 {1}의 원점은 {0}과 같은 점입니다. 따라서 \({}^1v_1 = 0\)이고 각속도는 관절 1의 \(\dot\theta_1\)뿐입니다.</p>`
          },
          {
            t: '{2}: 직동 관절 2',
            do(S) { rpArrows(S, p, 1); },
            tex: R`\begin{aligned}{}^2\omega_2 &= {}^2_1R\,{}^1\omega_1 = {}^1_2R^T\,[0\ \ 0\ \ \dot\theta_1]^T = [0\ \ \dot\theta_1\ \ 0]^T\\ {}^2v_2 &= {}^2_1R\left({}^1v_1 + {}^1\omega_1\times{}^1P_2\right) + \dot d_2\,{}^2\hat Z_2 = {}^2_1R\,[0\ \ d_2\dot\theta_1\ \ 0]^T + [0\ \ 0\ \ \dot d_2]^T = [d_2\dot\theta_1\ \ 0\ \ \dot d_2]^T\end{aligned}`,
            html: R`<p>직동 관절은 각속도를 더하지 않고, 선속도에 \(\dot d_2\hat Z_2\)를 더합니다. \({}^2_1R = {}^1_2R^T\)입니다.</p>
            ${ls([R`\({}^2\omega_2\)가 \(\hat Y_2\) 성분: \(\hat Y_2 = \hat Z_1\)이기 때문`, R`\(d_2\dot\theta_1\): 팔이 돌아서 생기는 속도, 팔에 수직(\(\hat X_2\))`, R`\(\dot d_2\): 팔이 늘어나는 속도, 팔 방향(\(\hat Z_2\))`])}`
          },
          {
            t: '⁰v₂와 ⁰J',
            do(S) { rpArrows(S, p, 1); },
            tex: R`{}^0v_2 = {}^0_2R\,{}^2v_2 = \begin{bmatrix}-s_1 & 0 & c_1\\ c_1 & 0 & s_1\\ 0 & 1 & 0\end{bmatrix}\begin{bmatrix}d_2\dot\theta_1\\0\\ \dot d_2\end{bmatrix} = \begin{bmatrix}-d_2s_1\dot\theta_1 + c_1\dot d_2\\ d_2c_1\dot\theta_1 + s_1\dot d_2\\ 0\end{bmatrix}\ \Rightarrow\ {}^0J(\Theta) = \begin{bmatrix}-d_2s_1 & c_1\\ d_2c_1 & s_1\end{bmatrix}`,
            html: R`<p>\({}^0_2R = {}^0_1R\,{}^1_2R = R_Z(\theta_1)\,{}^1_2R\)입니다. 열은 차례로 {0}에서 본 \(\hat X_2, \hat Y_2, \hat Z_2\)입니다.</p>
            <p>\(\dot\theta_1\)과 \(\dot d_2\)의 계수를 열로 모으면 자코비안입니다.</p>`
          },
          {
            t: '직접 미분으로 확인',
            tex: R`{}^0_2T = {}^0_1T\,{}^1_2T\ \Rightarrow\ {}^0P_2 = R_Z(\theta_1)\begin{bmatrix}d_2\\0\\0\end{bmatrix} = \begin{bmatrix}d_2c_1\\ d_2s_1\end{bmatrix}\ \xrightarrow{\ d/dt\ }\ \begin{bmatrix}\dot d_2c_1 - d_2s_1\dot\theta_1\\ \dot d_2s_1 + d_2c_1\dot\theta_1\end{bmatrix}`,
            html: R`<p>곱의 미분(\(d_2\)와 \(\theta_1\) 모두 시간의 함수)을 쓰면 앞 단계의 \({}^0v_2\)와 똑같습니다.</p>
            <p>\(\dfrac{\partial}{\partial\theta_1}\)과 \(\dfrac{\partial}{\partial d_2}\)로 편미분해 열을 만들어도 \({}^0J\)가 그대로 나옵니다.</p>`
          },
          {
            t: '숫자 대입',
            do(S) { rpArrows(S, p, 1); },
            tex: R`{}^0v_2 = \begin{bmatrix}-(${p.d2})s_{${p.t1}}(${p.td1}) + c_{${p.t1}}(${p.dd2})\\ (${p.d2})c_{${p.t1}}(${p.td1}) + s_{${p.t1}}(${p.dd2})\end{bmatrix} = \begin{bmatrix}${f(r.v0[0], 4)}\\ ${f(r.v0[1], 4)}\end{bmatrix}\ \text{m/s},\qquad |{}^0v_2| = \sqrt{v_x^2+v_y^2} = ${f(sp, 4)}\ \text{m/s}`,
            html: R`<p>크기는 프레임에 무관하므로 \({}^2v_2\)로도 확인할 수 있습니다: \(\sqrt{(d_2\dot\theta_1)^2 + \dot d_2^{\,2}} = \sqrt{${f(p.d2 * p.td1, 4)}^2 + ${f(p.dd2, 4)}^2} = ${f(sp, 4)}\).</p>`
          },
          {
            t: '움직여 보기',
            live: {
              params: [
                { id: 't1', label: R`\(\theta_1\)`, min: -180, max: 180, step: 1, val: p.t1, unit: '°' },
                { id: 'd2', label: R`\(d_2\)`, min: 0.15, max: 1, step: 0.01, val: p.d2, unit: 'm' },
                { id: 'td1', label: R`\(\dot\theta_1\)`, min: -0.6, max: 0.6, step: 0.01, val: p.td1, unit: 'rad/s' },
                { id: 'dd2', label: R`\(\dot d_2\)`, min: -0.3, max: 0.3, step: 0.01, val: p.dd2, unit: 'm/s' }
              ],
              drag: { q1: { frame: 'F1', type: 'rot', get: q => q.t1, set: (q, v) => { q.t1 = v; } }, d2: { frame: 'F2', type: 'lin', sign: 1 / DSr } },
              apply(S, q) { rpScene(S, q, { drag: true }); rpArrows(S, q, 1); },
              tex(q) { const r2 = rpVel(q); return R`{}^0J = ${bm([[-q.d2 * s(q.t1), c(q.t1)], [q.d2 * c(q.t1), s(q.t1)]], 3)},\quad {}^0v_2 = ${cv(r2.v0, 4)},\quad |v| = ${f(Math.hypot(r2.v0[0], r2.v0[1]), 4)}\ \text{m/s}`; },
              html: () => R`<p>팔을 돌리거나 끝을 끌어 늘려 보세요.</p>
              ${ls([R`\(d_2\)가 길수록 같은 \(\dot\theta_1\)에도 수직 속도(빨강)가 커짐`, R`늘어나는 속도(파랑)는 \(d_2\)와 무관`])}`
            }
          }
        ]
      };
    }
  });

  /* ---------- HW3 P2: 3R planar ---------- */
  const L3 = [0.4, 0.3, 0.1], DS3 = 3, L3u = L3.map(x => x * DS3);
  const J3 = q => { const s23 = s(q[1] + q[2]), c23 = c(q[1] + q[2]), s3 = s(q[2]), c3 = c(q[2]), [a, b, e] = L3; return [[a * s23 + b * s3, b * s3, 0], [a * c23 + b * c3 + e, b * c3 + e, e], [1, 1, 1]]; };
  const det3 = A => A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0]) + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]);
  const solve3 = (A, b) => { const d = det3(A); return [0, 1, 2].map(k => det3(A.map((r, i) => r.map((x, j) => (j === k ? b[i] : x)))) / d); };
  const QV3 = [20, 45, -35], QD3 = [0.4, 0.3, 0.5], F3 = [3, 4], NZ3 = 0.3;
  {
    const VS3 = 3.5, FS3 = 0.09, KN3 = 0.6, KT3 = 60;
    const scene = (S, q, o) => { wipe(S); arm(S, L3u, q, Object.assign({ tId: 'FT', tLabel: 'T', fs: 0.26, frameOpt: { 0: { size: 0.4 } } }, o)); };
    const vel = (S, upto, on) => {
      const pr = propP(L3, QV3, QD3), fid = ['', 'F1', 'F2', 'F3', 'FT'], nm = ['', '1', '2', '3', 'T'];
      for (let i = 2; i <= upto; i++) {
        const op = on && on !== i ? 0.35 : 1;
        arw(S, 'w' + i, fid[i], [0, 0, pr.w[i]], 0.5, { c: 'k', label: `<sup>${nm[i]}</sup>ω<sub>${nm[i]}</sub>`, w: 0.8, lt: 1.12, op });
        arw(S, 'v' + i, fid[i], pr.v[i], VS3, { c: 'pt', label: `<sup>${nm[i]}</sup>v<sub>${nm[i]}</sub>`, w: 1.0, lt: 1.1, op });
      }
    };
    const frc = (S, q, from) => {
      const st = statP(L3, q, F3, NZ3), fid = ['', 'F1', 'F2', 'F3', 'FT'];
      arw(S, 'fT', 'FT', st.f[4], FS3, { c: 'warn', label: 'ᵀF', w: 1.1, lt: 1.1 });
      arw(S, 'nT', 'FT', st.n[4], KN3, { c: 'k', label: 'ᵀN', w: 0.9, lt: 1.15 });
      for (let i = 3; i >= from; i--) tq(S, 't' + i, 'J' + i, st.tau[i - 1], KT3, { col: 'j' + i, label: ['', 'τ₁', 'τ₂', 'τ₃'][i], r: [0, 0.3, 0.26, 0.22][i] });
      return st;
    };
    sec({
      id: 'c4-hw-3r', group: 'practice', ref: '과제 3 · 문제 2', title: '평면 3R 팔: 자코비안·토크·특이점',
      view: { pos: [1.5, -5.6, 1.9], target: [1.0, 0, 0.7] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
      params: {
        orig: { v: 0.1, ths: [30, 5, 1] }, origLabel: '과제 숫자',
        rand() { return { v: pick(1, 4) * 0.05, ths: [pick(3, 9) * 5, pick(3, 8), pick(1, 2)] }; }
      },
      build(P) {
        const rates = P.ths.map(t => solve3(J3([0, t, -t]), [P.v, 0, 0]));
        const live0 = P.ths[0];
        return {
          answers: [
            { label: R`\(\dot\theta_1\ (\theta_2 = ${P.ths[2]}^\circ)\)`, val: rates[2][0], unit: 'rad/s', tol: Math.max(0.01, Math.abs(rates[2][0]) * 0.003), dp: 3 },
            { label: R`\(\dot\theta_2\ (\theta_2 = ${P.ths[2]}^\circ)\)`, val: rates[2][1], unit: 'rad/s', tol: Math.max(0.01, Math.abs(rates[2][1]) * 0.003), dp: 3 },
            { label: R`\(\dot\theta_3\ (\theta_2 = ${P.ths[2]}^\circ)\)`, val: rates[2][2], unit: 'rad/s', tol: Math.max(0.01, Math.abs(rates[2][2]) * 0.003), dp: 3 }
          ],
          calcData: { rates },
          init(S) { scene(S, QV3); },
          steps: [
            {
              t: '문제',
              tex: R`L_1 = 0.4,\ L_2 = 0.3,\ L_3 = 0.1\ \text{m},\qquad {}^3P_T = \begin{bmatrix}L_3\\0\\0\end{bmatrix},\ {}^3_TR = I,\qquad {}^T\nu_T = \begin{bmatrix}{}^Tv_x\\ {}^Tv_y\\ {}^T\omega_z\end{bmatrix} = {}^TJ(\Theta)\,\dot\Theta`,
              html: R`<ol class="ls"><li>베이스부터 속도를 전파해 \({}^Tv_T\), \({}^T\omega_T\)를 구하고 \({}^TJ(\Theta)\)를 쓰시오.</li><li>공구가 환경에 \({}^TF = (f_x, f_y, 0)\), \({}^TN = (0,0,n_z)\)를 가할 때 힘을 전파해 \(\tau = A(\Theta)\,{}^T\mathcal F\)를 구하시오.</li><li>\(A = {}^TJ^T\)임을 보이고 가상 일의 원리로 설명하시오.</li><li>특이 자세를 모두 찾아 분류하시오.</li><li>\(\Theta = (0, \theta_2, -\theta_2)\), \(v = (${f(P.v, 3)}, 0, 0)\)일 때 \(\theta_2 = ${P.ths.join('^\\circ, ')}^\circ\)에서 \(\dot\Theta = J^{-1}v\)를 구하시오.</li></ol>
              <p class="note">문제지의 \({}^TF = [f_x\ f_z\ 0]^T\)는 \([f_x\ f_y\ 0]^T\)의 오타로 보고 풉니다.</p>`
            },
            {
              t: '① {1}, {2}로 속도 전파',
              do(S) { vel(S, 2, 2); },
              tex: R`{}^1\omega_1 = \begin{bmatrix}0\\0\\ \dot\theta_1\end{bmatrix},\ {}^1v_1 = 0,\qquad {}^2\omega_2 = \begin{bmatrix}0\\0\\ \dot\theta_1+\dot\theta_2\end{bmatrix},\quad {}^2v_2 = {}^2_1R\begin{bmatrix}0\\ L_1\dot\theta_1\\ 0\end{bmatrix} = \begin{bmatrix}L_1s_2\dot\theta_1\\ L_1c_2\dot\theta_1\\ 0\end{bmatrix}`,
              html: R`<p>4.3절의 2링크 결과와 같습니다. 화살표는 예시 자세 \(\Theta = (${QV3.join('^\\circ, ')}^\circ)\), \(\dot\Theta = (${QD3.join(', ')})\) rad/s에서 그린 것입니다.</p>`
            },
            {
              t: '① {3}',
              do(S) { vel(S, 3, 3); },
              tex: R`{}^3\omega_3 = \begin{bmatrix}0\\0\\ \dot\theta_1+\dot\theta_2+\dot\theta_3\end{bmatrix},\quad {}^3v_3 = {}^3_2R\begin{bmatrix}L_1s_2\dot\theta_1\\ L_1c_2\dot\theta_1 + L_2(\dot\theta_1+\dot\theta_2)\\ 0\end{bmatrix} = \begin{bmatrix}L_1s_{23}\dot\theta_1 + L_2s_3(\dot\theta_1+\dot\theta_2)\\ L_1c_{23}\dot\theta_1 + L_2c_3(\dot\theta_1+\dot\theta_2)\\ 0\end{bmatrix}`,
              html: R`<p>\({}^3_2R = R_Z(\theta_3)^T\)를 곱할 때 합의 공식을 씁니다.</p>
              ${ls([R`\(s_2c_3 + c_2s_3 = s_{23}\)`, R`\(-s_2s_3 + c_2c_3 = c_{23}\)`])}`
            },
            {
              t: '① {T}와 ᵀJ',
              do(S) { vel(S, 4, 4); },
              tex: R`{}^Tv_T = {}^3v_3 + {}^3\omega_3\times{}^3P_T,\qquad {}^T\nu_T = \underbrace{\begin{bmatrix}L_1s_{23}+L_2s_3 & L_2s_3 & 0\\ L_1c_{23}+L_2c_3+L_3 & L_2c_3+L_3 & L_3\\ 1 & 1 & 1\end{bmatrix}}_{{}^TJ(\Theta)}\begin{bmatrix}\dot\theta_1\\ \dot\theta_2\\ \dot\theta_3\end{bmatrix}`,
              html: R`<p>{T}는 {3}과 방향이 같으므로(\({}^T_3R = I\)) 회전 없이 \(L_3(\dot\theta_1+\dot\theta_2+\dot\theta_3)\)만 \(y\) 성분에 더해집니다. 셋째 줄은 \({}^T\omega_z\)입니다.</p>`
            },
            {
              t: '② 힘 전파: {T} → {3}',
              do(S) { frc(S, QV3, 3); },
              tex: R`{}^3f_3 = {}^TF = \begin{bmatrix}f_x\\ f_y\\ 0\end{bmatrix},\qquad {}^3n_3 = {}^TN + {}^3P_T\times{}^3f_3 = \begin{bmatrix}0\\0\\ n_z + L_3f_y\end{bmatrix}\ \Rightarrow\ \tau_3 = L_3f_y + n_z`,
              html: R`<p>끝에서부터 거꾸로 전파합니다. 화살표는 예시 값 \(f_x = ${F3[0]}\), \(f_y = ${F3[1]}\) N, \(n_z = ${NZ3}\) N·m입니다.</p>`
            },
            {
              t: '② {2}',
              do(S) { frc(S, QV3, 2); },
              tex: R`{}^2f_2 = {}^2_3R\,{}^3f_3 = \begin{bmatrix}c_3f_x - s_3f_y\\ s_3f_x + c_3f_y\\ 0\end{bmatrix},\quad {}^2n_2 = {}^2_3R\,{}^3n_3 + {}^2P_3\times{}^2f_2\ \Rightarrow\ \tau_2 = L_2s_3f_x + (L_2c_3+L_3)f_y + n_z`,
              html: R`<p>\({}^2P_3 = (L_2, 0, 0)\)이므로 모멘트에 \(L_2\times\)(\({}^2f_2\)의 y 성분)이 더해집니다.</p>`
            },
            {
              t: '② {1}과 행렬 A',
              do(S) { frc(S, QV3, 1); },
              tex: R`\tau_1 = (L_1s_{23}+L_2s_3)f_x + (L_1c_{23}+L_2c_3+L_3)f_y + n_z\ \Rightarrow\ \tau = \underbrace{\begin{bmatrix}L_1s_{23}+L_2s_3 & L_1c_{23}+L_2c_3+L_3 & 1\\ L_2s_3 & L_2c_3+L_3 & 1\\ 0 & L_3 & 1\end{bmatrix}}_{A(\Theta)}\begin{bmatrix}f_x\\ f_y\\ n_z\end{bmatrix}`,
              html: R`<p>\({}^1f_1 = {}^1_2R\,{}^2f_2\)는 \(\theta_2+\theta_3\)만큼 돌린 힘이 되어 \(s_{23}, c_{23}\)이 나타납니다.</p>`
            },
            {
              t: '③ A = ᵀJᵀ와 가상 일',
              do(S) { frc(S, QV3, 1); },
              tex: R`A(\Theta) = {}^TJ(\Theta)^T,\qquad {}^T\mathcal F^T\,\delta\mathcal X = \tau^T\delta\Theta,\ \ \delta\mathcal X = {}^TJ\,\delta\Theta\ \Rightarrow\ \tau = {}^TJ^T\,{}^T\mathcal F`,
              html: R`<p>②의 \(A\)를 ①의 \({}^TJ\)와 비교하면 행과 열이 바뀐 것뿐입니다.</p>
              ${ls([R`이유: 작은 가상 변위에 대해 끝점이 한 일 \(\mathcal F\cdot\delta\mathcal X\)와 관절이 한 일 \(\tau\cdot\delta\Theta\)가 같아야 함 (마찰·중력 무시, 정지 상태)`, R`\(\delta\mathcal X = J\delta\Theta\)를 대입하면 \((J^T\mathcal F - \tau)^T\delta\Theta = 0\)이 모든 \(\delta\Theta\)에 대해 성립 → \(\tau = J^T\mathcal F\)`, R`\(J\)와 \(\mathcal F\)는 같은 프레임 {T}로 표현해야 함`])}`
            },
            {
              t: '④ 특이 자세',
              do(S) { scene(S, [20, 0, 25]); arm(S, L3u, [20, 180, 25], { tId: 'GT', pre: 'g', noFrames: true, hideTool: true, op: 0.25, noLabels: true }); },
              view: { pos: [1.4, -6.2, 1.6], target: [1.1, 0, 0.5] },
              tex: R`\det{}^TJ = (L_1s_{23}+L_2s_3)(L_2c_3) - L_2s_3(L_1c_{23}+L_2c_3) = L_1L_2(s_{23}c_3 - c_{23}s_3) = L_1L_2\,s_2 = 0\ \Leftrightarrow\ \theta_2 = 0^\circ,\ 180^\circ`,
              html: R`<p>셋째 열 \((0, L_3, 1)\)을 이용해 전개하면(또는 셋째 열 기준 소거) 위처럼 간단해집니다.</p>
              ${ls([R`\(\theta_2 = 0^\circ\): 링크 1·2가 일직선 (진한 팔) → 손목점이 바깥 경계 \(r = L_1+L_2\)`, R`\(\theta_2 = 180^\circ\): 링크 2가 링크 1 위로 완전히 접힘 (흐린 팔) → 안쪽 경계 \(r = L_1-L_2\)`, R`둘 다 <b>작업공간 경계 특이점</b>. 평면 팔은 회전축이 모두 평행해 한 줄로 겹칠 수 없으므로 내부 특이점은 없음`, R`\(\theta_1, \theta_3\)는 det에 나타나지 않음: 어떤 값이어도 특이`])}`
            },
            {
              t: '⑤ 특이점 근처에서 Θ̇ = J⁻¹v',
              do(S) { scene(S, [0, live0, -live0]); tipG2(S); },
              tex: R`{}^TJ\big|_{(0,\theta_2,-\theta_2)} = \begin{bmatrix}-L_2s_{\theta_2} & -L_2s_{\theta_2} & 0\\ L_1+L_2c_{\theta_2}+L_3 & L_2c_{\theta_2}+L_3 & L_3\\ 1&1&1\end{bmatrix},\quad \dot\Theta = J^{-1}\begin{bmatrix}${f(P.v, 3)}\\0\\0\end{bmatrix}:\ ${P.ths.map((t, i) => R`\underset{\theta_2 = ${t}^\circ}{${cv(rates[i], 3)}}`).join(',\ ')}`,
              html: R`<p>\(\theta_1+\theta_2+\theta_3 = 0\)이므로 {T}의 방향이 {0}과 같아 \({}^TJ = {}^0J\)입니다. 공구는 \(+\hat X\) 방향(팔을 펴는 방향)으로 움직여야 합니다.</p>
              ${ls([R`\(\det J = L_1L_2s_{\theta_2}\)가 작아질수록 관절 속도가 \(1/\sin\theta_2\)에 비례해 커짐`, R`\(\theta_2 = 1^\circ\) 근처에서는 같은 끝점 속도에 수십 배의 관절 속도 필요 → 실제 모터 한계를 넘음`, R`그래서 특이점 근처의 직교 좌표 경로는 피해야 함`])}`
            },
            {
              t: '⑤ θ₂를 0°로 가까이',
              live: {
                params: [{ id: 'th', label: R`\(\theta_2\)`, min: -60, max: 60, step: 0.5, val: live0, unit: '°' }],
                apply(S, q) { scene(S, [0, q.th, -q.th]); tipG2(S); const A = J3([0, q.th, -q.th]); if (Math.abs(det3(A)) > 1e-6) { const r2 = solve3(A, [P.v, 0, 0]); r2.forEach((w, i) => tq(S, 'r' + i, 'J' + (i + 1), w, 30, { col: 'j' + (i + 1), label: `θ̇${'₁₂₃'[i]}`, r: [0.3, 0.26, 0.22][i] })); } },
                vpInfo(q) { const A = J3([0, q.th, -q.th]), d = det3(A), ok = Math.abs(d) > 1e-6, r2 = ok ? solve3(A, [P.v, 0, 0]) : null; const bar = w => `<span style="display:inline-block;height:7px;vertical-align:middle;background:var(--acc);width:${Math.min(150, Math.abs(w) * 12)}px"></span>`; return vcard(`Θ̇ = J⁻¹v (rad/s), det J = ${f(d, 5)}`, ok ? r2.map((w, i) => ({ s: `θ̇${'₁₂₃'[i]}`, v: `${f(w, 3)} ${bar(w)}`, on: Math.abs(w) > 5 })) : [{ s: '특이점', v: 'J⁻¹ 없음' }]); },
                tex(q) { const A = J3([0, q.th, -q.th]); return R`{}^TJ = ${bm(A, 4)},\quad \det J = 0.12\,s_{\theta_2} = ${f(det3(A), 5)}`; },
                html: () => R`<p>\(\theta_2\)를 0°에 가깝게 움직이며 관절 속도 막대가 커지는 것을 보세요. 호의 길이도 관절 속도에 비례합니다.</p>`
              }
            }
          ]
        };
      }
    });
    function tipG2(S) { fr(S, 'GT', fromRp(R3(base), p3(S.frames.FT.T)), { hidden: true }); arw(S, 'vd', 'GT', [1, 0, 0], 0.45, { c: 'pt', label: 'v', w: 1.2, lt: 1.15 }); }
  }

  /* ---------- HW3 P3: force sensor ---------- */
  sec({
    id: 'c4-hw-sensor', group: 'practice', ref: '과제 3 · 문제 3', title: '힘 센서 측정값을 공구 끝으로 옮기기',
    view: { pos: [0.9, -4.6, 1.3], target: [0.2, 0, 1.0] }, grid: [3, 0.5], scale: 0.7, fsize: 1,
    params: {
      orig: { px: 0.1, pz: 0.2, F: [5, 0, -10], N: [0, 2, 0] }, origLabel: '과제 숫자',
      rand() {
        const px = pick(1, 3) * 0.05, pz = pick(2, 6) * 0.05, F = [pick(-8, 8), pick(-3, 3), -pick(5, 15)];
        const Pv = [-px, 0, -pz], N = scl(cross(Pv, F), -1).map(v => M.round(v, 3));
        return { px, pz, F, N };
      }
    },
    build(P) {
      const Pv = [-P.px, 0, -P.pz], TSinv = fromRp([[1, 0, 0], [0, 1, 0], [0, 0, 1]], Pv), Tf = Tf6(R3(I()), Pv);
      const tF = P.F.slice(), tN = add(cross(Pv, P.F), P.N);
      const T4 = TSinv.map(r => r.slice());
      return {
        answers: [0, 1, 2].map(i => ({ label: R`\({}^TN_${'xyz'[i]}\)`, val: tN[i], unit: 'N·m', tol: 0.002, dp: 3 })),
        calcData: { Pv, tN, Tf },
        init(S) { sensorScene(S, P.px, P.pz); },
        steps: [
          {
            t: '문제',
            tex: R`{}^S_TT = \begin{bmatrix}1&0&0&${P.px}\\0&1&0&0\\0&0&1&${P.pz}\\0&0&0&1\end{bmatrix}\ (\text{m}),\qquad {}^T\mathcal F = {}^T_ST_f\;{}^S\mathcal F,\quad {}^T_ST_f = \begin{bmatrix}{}^T_SR & 0\\ {}^TP_{SORG}\times{}^T_SR & {}^T_SR\end{bmatrix}`,
            html: R`<p>마지막 링크와 L자 공구 사이에 힘 센서가 있습니다. 센서는 자기 프레임 {S}에서 힘·모멘트 \({}^S\mathcal F = [{}^SF^T\ {}^SN^T]^T\)를 잽니다. {T}는 공구 끝에 있고 {S}와 방향이 같습니다.</p>
            <ol class="ls"><li>\({}^T_ST\)를 구하고 6×6 행렬 \({}^T_ST_f\)를 숫자로 쓰시오.</li><li>\({}^SF = (${P.F.join(', ')})\) N, \({}^SN = (${P.N.map(v => f(v, 3)).join(', ')})\) N·m일 때 \({}^TF\), \({}^TN\)을 구하고, 공구 끝에 모멘트가 없는데도 센서가 모멘트를 재는 이유를 설명하시오.</li></ol>`
          },
          {
            t: '① ᵀ_ST = (ˢ_TT)⁻¹',
            tex: R`{}^T_ST = \begin{bmatrix}R^T & -R^T\,{}^SP_{TORG}\\ 0 & 1\end{bmatrix} = \begin{bmatrix}1&0&0&${f(-P.px, 3)}\\0&1&0&0\\0&0&1&${f(-P.pz, 3)}\\0&0&0&1\end{bmatrix}\ \Rightarrow\ {}^T_SR = I,\ \ {}^TP_{SORG} = ${cv(Pv, 3)}`,
            html: R`<p>회전이 없으므로 역변환은 위치 부호만 바뀝니다. {T}에서 보면 센서 원점은 \(x\) 방향으로 \(-${P.px}\), \(z\) 방향으로 \(-${P.pz}\) m에 있습니다(그림에서 \(\hat Z\)가 아래쪽).</p>`
          },
          {
            t: '① 6×6 힘 변환 행렬',
            tex: R`{}^TP_{SORG}\times = \begin{bmatrix}0 & -p_z & p_y\\ p_z & 0 & -p_x\\ -p_y & p_x & 0\end{bmatrix} = ${bm(skew(Pv), 3)},\qquad {}^T_ST_f = ${bm(Tf, 3)}`,
            html: R`<p>\(R = I\)이므로 왼쪽 아래 블록은 \(P\times\) 그 자체입니다.</p>`
          },
          {
            t: '② ᵀF와 ᵀN',
            do(S) { sensorForces(S, P.F, P.N, tF, tN, 1); },
            tex: R`{}^TF = {}^SF = ${cv(tF, 3)}\ \text{N},\qquad {}^TN = {}^TP_{SORG}\times{}^SF + {}^SN = ${cv(cross(Pv, P.F), 3)} + ${cv(P.N, 3)} = ${cv(tN, 3)}\ \text{N·m}`,
            html: R`<p>6×6 행렬을 곱하는 것은 위 두 식을 한 번에 계산하는 것과 같습니다.</p>
            ${ls([R`위 3줄: 힘은 회전만 (\(R = I\)이라 그대로)`, R`아래 3줄: 지렛대 항 \(P\times F\) + 센서 모멘트`])}`
          },
          {
            t: '② 왜 센서는 모멘트를 재는가',
            do(S) { sensorForces(S, P.F, P.N, tF, tN, 1); ln(S, 'lev', { f: 'S', p: O }, { f: 'T', p: O }, { c: 'acc', label: '지렛대 팔', dash: false }); },
            tex: R`{}^SN = {}^SP_{TORG}\times{}^SF\quad(\text{공구 끝 모멘트가 0일 때}),\qquad {}^SP_{TORG} = ${cv([P.px, 0, P.pz], 3)}\ \text{m}`,
            html: R`<p>공구 끝에서는 힘만 작용(점 접촉)하지만, 그 힘은 센서 중심에서 떨어진 곳에 작용합니다.</p>
            ${ls([R`L자 공구가 \(${P.px}\) m, \(${P.pz}\) m 떨어진 <b>지렛대 팔(moment arm)</b> 역할`, R`힘 × 팔 길이만큼의 모멘트가 센서에 전달됨`, R`그래서 \({}^TN = 0\)이어도 \({}^SN = {}^SP_{TORG}\times{}^SF \ne 0\)`])}`
          }
        ]
      };
    }
  });

  window.COURSE.chapters.push({ id: 'ch4', title: 'Lecture 4 · Jacobians: Velocities and Static Forces', short: 'Ch4 자코비안', sections });
})();
