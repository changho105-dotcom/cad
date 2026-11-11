/* 말로 캐드 — 실제 캐드 명령 확장 (index.html 다음에 읽힘)
   사람이 쓰는 명령(명령줄·메뉴·도구막대)과 AI(apply_drawing의 ops)가 같은 기하 함수를 쓴다.
   단위 mm, 각도 °(X축 +방향 0°, 반시계 +). index.html의 전역(doc, view, CMDS, w2s …)을 그대로 쓴다. */
(() => {
'use strict';

/* ---------- 기본 벡터 ---------- */
const EPS = 1e-7;
const dist = (a, b) => Math.hypot(b[0] - a[0], b[1] - a[1]);
const sub = (a, b) => [a[0] - b[0], a[1] - b[1]], addv = (a, b) => [a[0] + b[0], a[1] + b[1]], mulv = (a, k) => [a[0] * k, a[1] * k];
const dot = (a, b) => a[0] * b[0] + a[1] * b[1], crs = (a, b) => a[0] * b[1] - a[1] * b[0];
const unit = v => { const L = Math.hypot(v[0], v[1]) || 1; return [v[0] / L, v[1] / L]; };
const angOf = (c, p) => Math.atan2(p[1] - c[1], p[0] - c[0]) / D2R;
const onArc = (a, a1, a2) => norm360(a - a1) <= norm360(a2 - a1) + 1e-9;
const polar = (c, r, deg) => [c[0] + r * Math.cos(deg * D2R), c[1] + r * Math.sin(deg * D2R)];
const clone = o => JSON.parse(JSON.stringify(o));
const NUMRE = /^-?\d*\.?\d+$/;
const P2 = v => Array.isArray(v) && v.length >= 2 && Number.isFinite(+v[0]) && Number.isFinite(+v[1]) ? [+v[0], +v[1]] : null;

/* ---------- 새 도형 ----------
   ellipse{cx,cy,rx,ry,rot,a1?,a2?} spline{pts,closed} xline{x,y,ang} ray{x,y,ang} point{x,y} donut{cx,cy,ri,ro}
   hatch{pts,holes?,pat,sc,ang} mtext{x,y,h,text,rot} leader{pts,text,h} dimang{cx,cy,r,a1,a2,text?} insert{name,x,y,sx,sy,rot} */
const EXT = ['ellipse', 'spline', 'xline', 'ray', 'point', 'donut', 'hatch', 'mtext', 'leader', 'dimang', 'insert'];
LAYERS.hatch = LAYERS.hatch || { color:'#7f8c99', dash:[] };
DXF_BASE.hatch = DXF_BASE.hatch || ['50_HATCH', 8, 'CONTINUOUS'];
Object.assign(TYPE_KO, { ellipse:'타원', spline:'스플라인', xline:'무한선', ray:'광선', point:'점', donut:'도넛', hatch:'해치', mtext:'여러 줄 문자', leader:'지시선', dimang:'각도 치수', insert:'블록' });

function ellipsePts(e) {
  const part = e.a1 != null && e.a2 != null, t0 = part ? e.a1 : 0, sw = part ? (norm360(e.a2 - e.a1) || 360) : 360;
  const n = Math.max(12, Math.ceil(sw / 5)), c = Math.cos((e.rot || 0) * D2R), s = Math.sin((e.rot || 0) * D2R), out = [];
  for (let i = 0; i <= (part ? n : n - 1); i++) { const t = (t0 + sw * i / n) * D2R, x = e.rx * Math.cos(t), y = e.ry * Math.sin(t); out.push([e.cx + x * c - y * s, e.cy + x * s + y * c]); }
  return out;
}
function splinePts(P, closed) { // 통과점을 지나는 캣멀-롬 곡선
  if (P.length < 3) return P.slice();
  const n = P.length, get = i => closed ? P[(i + n) % n] : P[Math.max(0, Math.min(n - 1, i))], out = [], segs = closed ? n : n - 1;
  for (let i = 0; i < segs; i++) {
    const p0 = get(i - 1), p1 = get(i), p2 = get(i + 1), p3 = get(i + 2);
    for (let j = 0; j < 12; j++) {
      const t = j / 12, t2 = t * t, t3 = t2 * t;
      out.push([0, 1].map(k => 0.5 * (2 * p1[k] + (-p0[k] + p2[k]) * t + (2 * p0[k] - 5 * p1[k] + 4 * p2[k] - p3[k]) * t2 + (-p0[k] + 3 * p1[k] - 3 * p2[k] + p3[k]) * t3)));
    }
  }
  if (!closed) out.push(P[n - 1].slice());
  return out;
}
const PAT = { ANSI31:[[45, 3.175]], ANSI37:[[45, 3.175], [135, 3.175]], NET:[[0, 3.175], [90, 3.175]] };
function hatchPrims(e) {
  const loops = [e.pts, ...(e.holes || [])];
  if ((e.pat || 'ANSI31') === 'SOLID') return [{ k:'fill', loops, alpha:0.55 }];
  const out = [];
  for (const [base, sp] of PAT[e.pat] || PAT.ANSI31) {
    const th = (base + (e.ang || 0)) * D2R, u = [Math.cos(th), Math.sin(th)], n = [-u[1], u[0]], s = sp * (e.sc || 1);
    const ds = loops.flat().map(q => dot(q, n)), d0 = Math.min(...ds), d1 = Math.max(...ds);
    if ((d1 - d0) / s > 3000) continue; // 너무 촘촘하면 생략(축척을 키우면 보임)
    for (let d = Math.ceil(d0 / s) * s; d <= d1; d += s) {
      const ts = [];
      for (const L of loops) for (let i = 0; i < L.length; i++) {
        const a = L[i], b = L[(i + 1) % L.length], da = dot(a, n) - d, db = dot(b, n) - d;
        if ((da > 0) !== (db > 0)) { const q = addv(a, mulv(sub(b, a), da / (da - db))); ts.push(dot(q, u)); }
      }
      ts.sort((x, y) => x - y);
      for (let i = 0; i + 1 < ts.length; i += 2) out.push({ k:'pl', pts:[addv(mulv(n, d), mulv(u, ts[i])), addv(mulv(n, d), mulv(u, ts[i + 1]))] });
    }
  }
  return out;
}
function mtextPrims(e) {
  const r = (e.rot || 0) * D2R, c = Math.cos(r), s = Math.sin(r);
  return String(e.text || '').split('\n').map((t, i) => { const dy = -e.h - i * e.h * 1.6; return { k:'text', x:e.x - s * dy, y:e.y + c * dy, h:e.h, rot:r, text:t }; });
}
function dimangPrims(e) {
  const T = doc.dimTxt, A = T * 0.8, c = [e.cx, e.cy], sw = norm360(e.a2 - e.a1), out = [{ k:'arc', c, r:e.r, a1:e.a1, a2:e.a2 }];
  for (const [a, sgn] of [[e.a1, -1], [e.a2, 1]]) { const tip = polar(c, e.r, a), tg = [-Math.sin(a * D2R) * sgn, Math.cos(a * D2R) * sgn]; out.push({ k:'fill', loops:[arrow(tip, tg[0], tg[1], A)] }); }
  const m = e.a1 + sw / 2, rot = readable((m - 90) * D2R), q = polar(c, e.r + T * 0.4, m);
  out.push({ k:'text', x:q[0], y:q[1], h:T, rot, text:e.text || fmt(sw) + '°', center:true });
  return out;
}
function insertXf(e, b) {
  const sx = e.sx ?? 1, sy = e.sy ?? sx, rot = e.rot || 0, c = Math.cos(rot * D2R), s = Math.sin(rot * D2R);
  return { sx, sy, rot, mir:sx * sy < 0, f:p => { const x = (p[0] - b.base[0]) * sx, y = (p[1] - b.base[1]) * sy; return [e.x + x * c - y * s, e.y + x * s + y * c]; } };
}
function xfPrim(q, T) {
  const k = Math.abs(T.sx), A = a => { const v = [T.sx * Math.cos(a * D2R), T.sy * Math.sin(a * D2R)]; return Math.atan2(v[1], v[0]) / D2R + T.rot; };
  switch (q.k) {
    case 'pl': return { ...q, pts:q.pts.map(T.f) };
    case 'arc': { if (q.full) return { ...q, c:T.f(q.c), r:q.r * k }; const a1 = A(q.a1), a2 = A(q.a2); return { ...q, c:T.f(q.c), r:q.r * k, a1:T.mir ? a2 : a1, a2:T.mir ? a1 : a2 }; }
    case 'fill': return { ...q, loops:q.loops.map(L => L.map(T.f)) };
    case 'text': { const p = T.f([q.x, q.y]); return { ...q, x:p[0], y:p[1], h:q.h * Math.abs(T.sy), rot:q.rot + T.rot * D2R }; }
    case 'pt': return { ...q, p:T.f(q.p) };
    case 'ring': return { ...q, c:T.f(q.c), ri:q.ri * k, ro:q.ro * k };
  }
  return q;
}
// 모든 도형을 기본 조각(꺾은선·호·채움·글자·점·도넛)으로 — 그리기·고르기·범위·DXF·블록이 함께 씀
function primsAny(e, depth = 0) {
  const P = [], pl = (pts, closed) => P.push({ k:'pl', pts, closed:!!closed });
  switch (e.type) {
    case 'line': pl([[e.x1, e.y1], [e.x2, e.y2]]); break;
    case 'circle': P.push({ k:'arc', c:[e.cx, e.cy], r:e.r, a1:0, a2:360, full:true }); break;
    case 'arc': P.push({ k:'arc', c:[e.cx, e.cy], r:e.r, a1:e.a1, a2:e.a2 }); break;
    case 'rect': pl(rectPts(e), true); break;
    case 'polyline': pl(e.pts, e.closed); break;
    case 'room': case 'bldg': case 'slab': pl(e.pts, true); break;
    case 'text': P.push({ k:'text', x:e.x, y:e.y, h:e.h, rot:(e.rot || 0) * D2R, text:e.text }); break;
    case 'wall': pl(wallQuad(e), true); break;
    case 'column': if (e.r > 0) P.push({ k:'arc', c:[e.cx, e.cy], r:e.r, a1:0, a2:360, full:true }); else pl(columnPts(e), true); break;
    case 'equip': pl(equipPts(e), true); break;
    case 'door': { const g = doorGeom(e); pl([[e.x, e.y], g.open]); pl(g.arc); break; }
    case 'window': windowLines(e).forEach(l => pl([[l[0], l[1]], [l[2], l[3]]])); break;
    case 'ellipse': pl(ellipsePts(e), !(e.a1 != null && e.a2 != null)); break;
    case 'spline': pl(splinePts(e.pts, e.closed), e.closed); break;
    case 'xline': case 'ray': { const u = [Math.cos(e.ang * D2R), Math.sin(e.ang * D2R)], L = 1e7, a = e.type === 'ray' ? [e.x, e.y] : [e.x - u[0] * L, e.y - u[1] * L]; P.push({ k:'pl', pts:[a, [e.x + u[0] * L, e.y + u[1] * L]], nb:true }); break; }
    case 'point': P.push({ k:'pt', p:[e.x, e.y] }); break;
    case 'donut': P.push({ k:'ring', c:[e.cx, e.cy], ri:e.ri || 0, ro:e.ro }); break;
    case 'hatch': P.push(...hatchPrims(e)); break;
    case 'mtext': P.push(...mtextPrims(e)); break;
    case 'leader': {
      pl(e.pts); const h = e.h || doc.dimTxt, a = e.pts[0], u = unit(sub(a, e.pts[1])); P.push({ k:'fill', loops:[arrow(a, u[0], u[1], h * 0.9)] });
      if (e.text) { const l = e.pts[e.pts.length - 1], right = l[0] >= e.pts[e.pts.length - 2][0], w = textW(e.text, h); P.push({ k:'text', x:right ? l[0] + h * 0.4 : l[0] - h * 0.4 - w, y:l[1] - h * 0.4, h, rot:0, text:e.text }); }
      break;
    }
    case 'dimang': P.push(...dimangPrims(e)); break;
    case 'insert': {
      const b = (doc.blocks || {})[e.name];
      if (!b || depth > 6) { P.push({ k:'pt', p:[e.x, e.y] }); break; }
      const T = insertXf(e, b);
      for (const be of b.ents) for (const q of primsAny(be, depth + 1) || []) P.push(xfPrim(q, T));
      break;
    }
    default:
      if (isDim(e)) { const g = dimGeom(e); g.lines.forEach(l => pl([[l[0], l[1]], [l[2], l[3]]])); g.tris.forEach(t => P.push({ k:'fill', loops:[t] })); g.texts.forEach(t => P.push({ k:'text', ...t })); }
      else return null;
  }
  return P;
}
window.extPrims = e => EXT.includes(e.type) ? primsAny(e) : null;
window.drawPrims = (prs, color, dash, width) => {
  ctx.strokeStyle = color; ctx.fillStyle = color; ctx.lineWidth = width || 1.3;
  const path = pts => pts.forEach((q, i) => { const s = w2s(q[0], q[1]); i ? ctx.lineTo(s[0], s[1]) : ctx.moveTo(s[0], s[1]); });
  for (const q of prs) {
    if (q.k === 'pl') { ctx.setLineDash(dash || []); ctx.beginPath(); path(q.pts); if (q.closed) ctx.closePath(); ctx.stroke(); }
    else if (q.k === 'arc') { ctx.setLineDash(dash || []); ctx.beginPath(); const [x, y] = w2s(q.c[0], q.c[1]); if (q.full) { ctx.moveTo(x + q.r * view.s, y); ctx.arc(x, y, q.r * view.s, 0, Math.PI * 2); } else ctx.arc(x, y, q.r * view.s, -q.a1 * D2R, -q.a2 * D2R, true); ctx.stroke(); }
    else if (q.k === 'fill') { ctx.beginPath(); for (const L of q.loops) { path(L); ctx.closePath(); } ctx.save(); ctx.globalAlpha *= q.alpha ?? 1; ctx.fill('evenodd'); ctx.restore(); }
    else if (q.k === 'text') drawText(q, color);
    else if (q.k === 'pt') { const [x, y] = w2s(q.p[0], q.p[1]); ctx.setLineDash([]); ctx.beginPath(); ctx.moveTo(x - 4, y); ctx.lineTo(x + 4, y); ctx.moveTo(x, y - 4); ctx.lineTo(x, y + 4); ctx.stroke(); }
    else if (q.k === 'ring') { const [x, y] = w2s(q.c[0], q.c[1]); ctx.beginPath(); ctx.arc(x, y, q.ro * view.s, 0, Math.PI * 2); if (q.ri > 0) { ctx.moveTo(x + q.ri * view.s, y); ctx.arc(x, y, q.ri * view.s, 0, Math.PI * 2, true); } ctx.fill('evenodd'); }
  }
};
function arcDist(q, p) {
  if (q.full || onArc(angOf(q.c, p), q.a1, q.a2)) return Math.abs(dist(q.c, p) - q.r);
  return Math.min(dist(p, polar(q.c, q.r, q.a1)), dist(p, polar(q.c, q.r, q.a2)));
}
window.primsDist = (prs, p) => {
  let m = Infinity;
  for (const q of prs) {
    if (q.k === 'pl') { const n = q.closed ? q.pts.length : q.pts.length - 1; for (let i = 0; i < n; i++) { const a = q.pts[i], b = q.pts[(i + 1) % q.pts.length]; m = Math.min(m, segDist(p, a[0], a[1], b[0], b[1])); } }
    else if (q.k === 'arc') m = Math.min(m, arcDist(q, p));
    else if (q.k === 'text') {
      const w = textW(q.text, q.h), c = Math.cos(q.rot), s = Math.sin(q.rot), d = sub(p, [q.x, q.y]);
      const lx = d[0] * c + d[1] * s + (q.center ? w / 2 : 0), ly = -d[0] * s + d[1] * c;
      m = Math.min(m, Math.max(lx < 0 ? -lx : lx > w ? lx - w : 0, ly < 0 ? -ly : ly > q.h ? ly - q.h : 0));
    }
    else if (q.k === 'pt') m = Math.min(m, dist(p, q.p));
    else if (q.k === 'ring') m = Math.min(m, Math.max(0, dist(p, q.c) - q.ro));
    else if (q.k === 'fill') for (const L of q.loops) { if (inPoly(p, L)) m = 0; }
  }
  return m;
};
window.primsBounds = (prs, add) => {
  for (const q of prs) {
    if (q.k === 'pl') { if (!q.nb) q.pts.forEach(p => add(p[0], p[1])); } // 무한선·광선은 전체보기 범위에서 뺌
    else if (q.k === 'arc' || q.k === 'ring') { const r = q.r ?? q.ro; add(q.c[0] - r, q.c[1] - r); add(q.c[0] + r, q.c[1] + r); }
    else if (q.k === 'text') { add(q.x, q.y); add(q.x + textW(q.text, q.h), q.y + q.h); }
    else if (q.k === 'pt') add(q.p[0], q.p[1]);
    else if (q.k === 'fill') q.loops.forEach(L => L.forEach(p => add(p[0], p[1])));
  }
};
window.dxfPrims = (prs, w, l) => {
  const { g, head, line, text, poly } = w;
  for (const q of prs) {
    if (q.k === 'pl') { if (q.pts.length === 2 && !q.closed) line(q.pts[0][0], q.pts[0][1], q.pts[1][0], q.pts[1][1], l); else poly(q.pts, q.closed, l); }
    else if (q.k === 'arc') { if (q.full) { head('CIRCLE', l); g(10, q.c[0]); g(20, q.c[1]); g(30, 0); g(40, q.r); } else { head('ARC', l); g(10, q.c[0]); g(20, q.c[1]); g(30, 0); g(40, q.r); g(50, norm360(q.a1)); g(51, norm360(q.a2)); } }
    else if (q.k === 'text') text(q.x, q.y, q.h, q.text, q.rot / D2R, l, !!q.center);
    else if (q.k === 'pt') { head('POINT', l); g(10, q.p[0]); g(20, q.p[1]); g(30, 0); }
    else if (q.k === 'fill') for (const L of q.loops) {
      if (L.length === 3 || L.length === 4) { const v = L.length === 3 ? [L[0], L[1], L[2], L[2]] : [L[0], L[1], L[3], L[2]]; head('SOLID', l); v.forEach((p, i) => { g(10 + i, p[0]); g(20 + i, p[1]); g(30 + i, 0); }); }
      else poly(L, true, l);
    }
    else if (q.k === 'ring') { // 폭 있는 폴리선 두 반원(R12)
      const t = q.ro - q.ri, rm = (q.ro + q.ri) / 2;
      head('POLYLINE', l); g(66, 1); g(10, 0); g(20, 0); g(30, 0); g(70, 1); g(40, t); g(41, t);
      for (const sx of [-1, 1]) { head('VERTEX', l); g(10, q.c[0] + sx * rm); g(20, q.c[1]); g(30, 0); g(42, 1); }
      head('SEQEND', l);
    }
  }
};
window.extSnaps = e => {
  switch (e.type) {
    case 'ellipse': {
      if (e.a1 != null) { const p = ellipsePts(e); return [[e.cx, e.cy, '중심'], [...p[0], '끝점'], [...p[p.length - 1], '끝점']]; }
      const c = Math.cos((e.rot || 0) * D2R), s = Math.sin((e.rot || 0) * D2R);
      return [[e.cx, e.cy, '중심'], ...[[e.rx, 0], [0, e.ry], [-e.rx, 0], [0, -e.ry]].map(([x, y]) => [e.cx + x * c - y * s, e.cy + x * s + y * c, '사분점'])];
    }
    case 'spline': return e.pts.map(p => [p[0], p[1], '끝점']);
    case 'xline': case 'ray': return [[e.x, e.y, '끝점']];
    case 'point': return [[e.x, e.y, '절점']];
    case 'donut': return [[e.cx, e.cy, '중심']];
    case 'mtext': case 'insert': return [[e.x, e.y, '삽입점']];
    case 'leader': return e.pts.map(p => [p[0], p[1], '끝점']);
    case 'text': return [[e.x, e.y, '삽입점']];
  }
  return [];
};
window.extXform = (e, f, o) => {
  const k = o.k || 1, mir = o.mirror != null, A = a => mir ? 2 * o.mirror - a : a + (o.rot || 0);
  switch (e.type) {
    case 'ellipse': e.rot = A(e.rot || 0); e.rx *= k; e.ry *= k; if (mir && e.a1 != null) { const a1 = -e.a2, a2 = -e.a1; e.a1 = a1; e.a2 = a2; } break;
    case 'xline': case 'ray': e.ang = A(e.ang || 0); break;
    case 'insert': { const sx = e.sx ?? 1, sy = e.sy ?? sx; e.sx = sx * k; e.sy = (mir ? -sy : sy) * k; e.rot = mir ? 2 * o.mirror - (e.rot || 0) : (e.rot || 0) + (o.rot || 0); break; }
    case 'hatch': e.ang = A(e.ang || 0); e.sc = (e.sc || 1) * k; if (e.holes) e.holes = e.holes.map(L => L.map(f)); break;
    case 'donut': e.ri = (e.ri || 0) * k; e.ro *= k; break;
    case 'mtext': if (!mir) e.rot = (e.rot || 0) + (o.rot || 0); e.h *= k; break;
    case 'leader': if (e.h) e.h *= k; break;
    case 'dimang': if (mir) { const a1 = A(e.a2), a2 = A(e.a1); e.a1 = a1; e.a2 = a2; } else { e.a1 += o.rot || 0; e.a2 += o.rot || 0; } break;
  }
};
const moveEnt0 = moveEnt;
moveEnt = (e, dx, dy) => { moveEnt0(e, dx, dy); if (e.holes) e.holes = e.holes.map(L => L.map(q => [q[0] + dx, q[1] + dy])); };

const EXT_NUM = ['x', 'y', 'cx', 'cy', 'r', 'rx', 'ry', 'rot', 'a1', 'a2', 'ang', 'ri', 'ro', 'h', 'w', 'sc', 'sx', 'sy'];
const ptsOf = v => (Array.isArray(v) ? v : []).map(P2).filter(Boolean);
window.extSanitize = a => {
  if (!EXT.includes(a.type)) return undefined;
  const e = { type:a.type, layer:LAYERS[a.layer] ? a.layer : '0' };
  for (const k of EXT_NUM) if (a[k] != null && Number.isFinite(+a[k])) e[k] = +a[k];
  if (a.floor != null && lvOf(String(a.floor))) e.floor = String(a.floor);
  if (a.tag && typeof a.tag === 'string') e.tag = a.tag;
  const has = (...ks) => ks.every(k => Number.isFinite(e[k]));
  switch (e.type) {
    case 'ellipse': if (!has('cx', 'cy') || !(e.rx > 0) || !(e.ry > 0)) return null; break;
    case 'spline': e.pts = ptsOf(a.pts); e.closed = !!a.closed; if (e.pts.length < 2) return null; break;
    case 'xline': case 'ray': if (!has('x', 'y')) return null; e.ang = e.ang || 0; break;
    case 'point': if (!has('x', 'y')) return null; break;
    case 'donut': if (!has('cx', 'cy') || !(e.ro > 0)) return null; e.ri = Math.max(0, Math.min(e.ri || 0, e.ro)); break;
    case 'hatch':
      e.pts = ptsOf(a.pts); if (e.pts.length < 3) return null;
      if (Array.isArray(a.holes)) e.holes = a.holes.map(ptsOf).filter(L => L.length >= 3);
      e.pat = ['SOLID', 'ANSI31', 'ANSI37', 'NET'].includes(a.pat) ? a.pat : 'ANSI31';
      if (!(e.sc > 0)) e.sc = autoHatchScale(e.pts);
      if (!LAYERS[a.layer]) e.layer = 'hatch'; break;
    case 'mtext': if (!has('x', 'y') || !a.text) return null; e.text = String(a.text); if (!(e.h > 0)) e.h = doc.dimTxt; break;
    case 'leader': e.pts = ptsOf(a.pts); if (e.pts.length < 2) return null; if (a.text) e.text = String(a.text); if (!(e.h > 0)) e.h = doc.dimTxt; e.layer = 'dim'; break;
    case 'dimang': if (!has('cx', 'cy', 'a1', 'a2') || !(e.r > 0)) return null; if (typeof a.text === 'string' && a.text) e.text = a.text; e.layer = 'dim'; break;
    case 'insert': e.name = String(a.name || ''); if (!(doc.blocks || {})[e.name] || !has('x', 'y')) return null; break;
  }
  return e;
};
function autoHatchScale(pts) { const xs = pts.map(p => p[0]), ys = pts.map(p => p[1]), sz = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)); return Math.max(1, Math.round(sz / 300)); }

/* ---------- 곡선 계산 (자르기·연장·끊기·등분이 씀) ---------- */
// 엔티티의 모서리를 선분{k:'seg',a,b}·호{k:'arc',c,r,a1,a2,full}로 — 글자·채움·치수는 뺌
function geomPrims(e) {
  if (isDim(e) || ['text', 'mtext', 'hatch', 'dimang', 'point'].includes(e.type)) return [];
  const out = [];
  for (const q of primsAny(e) || []) {
    if (q.k === 'pl') { const n = q.closed ? q.pts.length : q.pts.length - 1; for (let i = 0; i < n; i++) out.push({ k:'seg', a:q.pts[i], b:q.pts[(i + 1) % q.pts.length] }); }
    else if (q.k === 'arc') out.push(q);
    else if (q.k === 'ring') { out.push({ k:'arc', c:q.c, r:q.ro, a1:0, a2:360, full:true }); if (q.ri > 0) out.push({ k:'arc', c:q.c, r:q.ri, a1:0, a2:360, full:true }); }
  }
  return out;
}
function interLineCircle(a, b, c, r, clampSeg) {
  const d = sub(b, a), f = sub(a, c), A = dot(d, d), B = 2 * dot(f, d), C = dot(f, f) - r * r, D = B * B - 4 * A * C;
  if (A < EPS || D < 0) return [];
  const sq = Math.sqrt(D), ts = D < 1e-12 ? [-B / (2 * A)] : [(-B - sq) / (2 * A), (-B + sq) / (2 * A)];
  return ts.filter(t => !clampSeg || (t >= -1e-9 && t <= 1 + 1e-9)).map(t => addv(a, mulv(d, t)));
}
function interPrims(p, q) {
  if (p.k === 'seg' && q.k === 'seg') {
    const r = sub(p.b, p.a), s = sub(q.b, q.a), den = crs(r, s); if (Math.abs(den) < 1e-12) return [];
    const t = crs(sub(q.a, p.a), s) / den, u = crs(sub(q.a, p.a), r) / den;
    return t >= -1e-9 && t <= 1 + 1e-9 && u >= -1e-9 && u <= 1 + 1e-9 ? [addv(p.a, mulv(r, t))] : [];
  }
  const inA = (x, pt) => x.full || onArc(angOf(x.c, pt), x.a1, x.a2);
  if (p.k === 'seg' || q.k === 'seg') { const s = p.k === 'seg' ? p : q, ar = p.k === 'seg' ? q : p; return interLineCircle(s.a, s.b, ar.c, ar.r, true).filter(pt => inA(ar, pt)); }
  const d = dist(p.c, q.c); if (d < EPS || d > p.r + q.r + 1e-9 || d < Math.abs(p.r - q.r) - 1e-9) return [];
  const a = (p.r * p.r - q.r * q.r + d * d) / (2 * d), h = Math.sqrt(Math.max(0, p.r * p.r - a * a)), u = unit(sub(q.c, p.c)), m = addv(p.c, mulv(u, a));
  const pts = h < 1e-9 ? [m] : [addv(m, [-u[1] * h, u[0] * h]), addv(m, [u[1] * h, -u[0] * h])];
  return pts.filter(pt => inA(p, pt) && inA(q, pt));
}
const primLen = q => q.k === 'seg' ? dist(q.a, q.b) : q.r * (q.full ? 360 : norm360(q.a2 - q.a1)) * D2R;
const primAt = (q, s) => q.k === 'seg' ? addv(q.a, mulv(sub(q.b, q.a), s / (dist(q.a, q.b) || 1))) : polar(q.c, q.r, q.a1 + s / q.r / D2R);
function primParam(q, p) {
  if (q.k === 'seg') { const L = dist(q.a, q.b) || 1, t = Math.max(0, Math.min(L, dot(sub(p, q.a), sub(q.b, q.a)) / L)); return [t, dist(p, primAt(q, t))]; }
  const sw = q.full ? 360 : norm360(q.a2 - q.a1); let a = norm360(angOf(q.c, p) - q.a1);
  if (a > sw) a = (a - sw < 360 - a) ? sw : 0;
  const s = a * D2R * q.r; return [s, dist(p, primAt(q, s))];
}
// 경로로 다룰 수 있는 도형 → {prims, closed, L, cum, at(t), param(p)}
function curveOf(e) {
  let prims, closed;
  if (['line', 'wall', 'window'].includes(e.type)) { prims = [{ k:'seg', a:[e.x1, e.y1], b:[e.x2, e.y2] }]; closed = false; }
  else if (e.type === 'arc') { prims = [{ k:'arc', c:[e.cx, e.cy], r:e.r, a1:e.a1, a2:e.a2 }]; closed = false; }
  else if (e.type === 'circle') { prims = [{ k:'arc', c:[e.cx, e.cy], r:e.r, a1:0, a2:360, full:true }]; closed = true; }
  else if (['polyline', 'rect', 'room', 'bldg', 'slab', 'ellipse', 'spline'].includes(e.type)) {
    const q = primsAny(e)[0]; closed = !!q.closed; const n = closed ? q.pts.length : q.pts.length - 1; prims = [];
    for (let i = 0; i < n; i++) { const a = q.pts[i], b = q.pts[(i + 1) % q.pts.length]; if (dist(a, b) > EPS) prims.push({ k:'seg', a, b }); }
  } else return null;
  const cum = [0]; prims.forEach(q => cum.push(cum[cum.length - 1] + primLen(q)));
  const L = cum[cum.length - 1];
  const at = t => { if (closed) t = ((t % L) + L) % L; t = Math.max(0, Math.min(L, t)); let i = 0; while (i < prims.length - 1 && t > cum[i + 1]) i++; return primAt(prims[i], t - cum[i]); };
  const param = p => { let best = [0, Infinity]; prims.forEach((q, i) => { const [s, d] = primParam(q, p); if (d < best[1]) best = [cum[i] + s, d]; }); return best[0]; };
  return { prims, closed, L, cum, at, param };
}
const GEOM_KEYS = ['x1', 'y1', 'x2', 'y2', 'cx', 'cy', 'r', 'a1', 'a2', 'x', 'y', 'w', 'h', 'pts', 'closed', 'rx', 'ry', 'rot', 'name', 'kind'];
function baseOf(e) { const b = clone(e); delete b.id; for (const k of GEOM_KEYS) delete b[k]; if (!['line', 'wall', 'window'].includes(e.type) && b.layer && ['room', 'area', 'slab'].includes(b.layer)) b.layer = '0'; return b; }
// 경로의 t0~t1 구간을 새 도형으로 (닫힌 경로는 t1 > L 허용 = 한 바퀴 넘김)
function pieceOf(e, C, t0, t1) {
  const b = baseOf(e);
  if (C.prims.length === 1 && C.prims[0].k === 'arc') {
    const q = C.prims[0], a1 = q.a1 + t0 / q.r / D2R, a2 = q.a1 + t1 / q.r / D2R;
    return Object.assign(b, { type:'arc', cx:q.c[0], cy:q.c[1], r:q.r, a1:norm360(a1), a2:norm360(a2) });
  }
  const br = []; C.cum.forEach(c => { br.push(c); if (C.closed) br.push(c + C.L); });
  const pts = [C.at(t0)]; br.filter(v => v > t0 + 1e-9 && v < t1 - 1e-9).sort((x, y) => x - y).forEach(v => pts.push(C.at(v))); pts.push(C.at(t1));
  if (pts.length === 2) {
    const type = ['line', 'wall', 'window'].includes(e.type) ? e.type : 'line';
    return Object.assign(b, { type, x1:pts[0][0], y1:pts[0][1], x2:pts[1][0], y2:pts[1][1] });
  }
  return Object.assign(b, { type:'polyline', pts, closed:false });
}
function replaceEnt(e, outs) {
  const i = doc.ents.indexOf(e); if (i < 0) return [];
  doc.ents.splice(i, 1); sel.delete(e.id);
  return outs.filter(Boolean).map(n => { const before = doc.ents.length; addEnt(n); const added = doc.ents.pop(); doc.ents.splice(Math.min(i, before), 0, added); return added; });
}
const live = () => doc.ents.filter(e => (!e.floor || e.floor === doc.cur) && !layerOff(e)); // 경계로 쓰는 객체(잠긴 레이어 포함)

/* ---------- 편집 기하 (사람·AI 공용) ---------- */
const G = {
  trim(e, cutters, pick) {
    const C = curveOf(e); if (!C) throw new Error(`${TYPE_KO[e.type] || e.type}은(는) 자를 수 없습니다`);
    const tol = 1e-6 * Math.max(1, C.L), ts = [];
    for (const k of cutters) { if (k === e) continue; const gp = geomPrims(k); for (const p of C.prims) for (const q of gp) for (const x of interPrims(p, q)) ts.push(C.param(x)); }
    const tp = C.param(pick);
    if (!C.closed) {
      let lo = 0, hi = C.L;
      for (const t of ts) { if (t <= tol || t >= C.L - tol) continue; if (t < tp && t > lo) lo = t; if (t > tp && t < hi) hi = t; }
      if (lo === 0 && hi === C.L) throw new Error('자를 경계와 만나지 않습니다');
      return replaceEnt(e, [lo > tol ? pieceOf(e, C, 0, lo) : null, hi < C.L - tol ? pieceOf(e, C, hi, C.L) : null]);
    }
    const u = [...new Set(ts.map(t => Math.round(t / tol) * tol))].sort((a, b) => a - b);
    if (u.length < 2) throw new Error('닫힌 도형은 경계와 두 번 이상 만나야 자를 수 있습니다');
    let lo = u.filter(t => t < tp).pop(), hi = u.find(t => t > tp);
    if (lo == null) lo = u[u.length - 1] - C.L; if (hi == null) hi = u[0] + C.L;
    let a = hi, b = lo + C.L; if (a >= C.L) { a -= C.L; b -= C.L; }
    return replaceEnt(e, [pieceOf(e, C, a, b)]);
  },
  extend(e, bounds, pick) {
    const B = bounds.filter(k => k !== e).flatMap(geomPrims);
    if (e.type === 'arc') {
      const c = [e.cx, e.cy], full = { k:'arc', c, r:e.r, a1:0, a2:360, full:true }, angs = B.flatMap(q => interPrims(full, q)).map(p => angOf(c, p));
      const endA2 = dist(pick, polar(c, e.r, e.a2)) < dist(pick, polar(c, e.r, e.a1));
      const cand = angs.map(a => endA2 ? norm360(a - e.a2) : norm360(e.a1 - a)).filter(d => d > 1e-6 && d < 360 - norm360(e.a2 - e.a1));
      if (!cand.length) throw new Error('연장할 경계를 찾지 못했습니다');
      const d = Math.min(...cand); if (endA2) e.a2 = norm360(e.a2 + d); else e.a1 = norm360(e.a1 - d); return [e];
    }
    let a, b, set;
    if (['line', 'wall', 'window'].includes(e.type)) {
      const p1 = [e.x1, e.y1], p2 = [e.x2, e.y2], endIs2 = dist(pick, p2) < dist(pick, p1);
      a = endIs2 ? p1 : p2; b = endIs2 ? p2 : p1; set = q => { if (endIs2) { e.x2 = q[0]; e.y2 = q[1]; } else { e.x1 = q[0]; e.y1 = q[1]; } };
    } else if (e.type === 'polyline' && !e.closed) {
      const n = e.pts.length, endLast = dist(pick, e.pts[n - 1]) < dist(pick, e.pts[0]);
      a = endLast ? e.pts[n - 2] : e.pts[1]; b = endLast ? e.pts[n - 1] : e.pts[0]; set = q => { e.pts[endLast ? n - 1 : 0] = q; };
    } else throw new Error(`${TYPE_KO[e.type] || e.type}은(는) 연장할 수 없습니다`);
    const u = unit(sub(b, a)), ray = { k:'seg', a:b, b:addv(b, mulv(u, 1e7)) };
    const hits = B.flatMap(q => interPrims(ray, q)).map(p => [dot(sub(p, b), u), p]).filter(([d]) => d > 1e-6).sort((x, y) => x[0] - y[0]);
    if (!hits.length) throw new Error('연장할 경계를 찾지 못했습니다');
    set(hits[0][1]); return [e];
  },
  // 두 선(또는 벽)의 모서리: r>0 모깎기, chamfer=[d1,d2] 모따기, 둘 다 0이면 모서리 맞춤
  corner(e1, e2, r, pick1, pick2, chamfer) {
    const LT = ['line', 'wall', 'window'];
    if (!LT.includes(e1.type) || !LT.includes(e2.type)) throw new Error('모깎기·모따기는 선이나 벽 두 개에 씁니다 (폴리선은 P 옵션)');
    const A1 = [e1.x1, e1.y1], B1 = [e1.x2, e1.y2], A2 = [e2.x1, e2.y1], B2 = [e2.x2, e2.y2], P = lineX(A1, B1, A2, B2);
    if (!P) throw new Error('평행한 두 선은 모서리를 만들 수 없습니다');
    const far = (A, B, pk) => { const fa = dist(A, P), fb = dist(B, P); if (pk) { const d = unit(sub(B, A)), s = Math.sign(dot(sub(pk, P), d)) || 1; return dot(sub(B, P), d) * s >= dot(sub(A, P), d) * s ? B : A; } return fa > fb ? A : B; };
    const F1 = far(A1, B1, pick1), F2 = far(A2, B2, pick2), u1 = unit(sub(F1, P)), u2 = unit(sub(F2, P));
    const set = (e, F, Q) => { const firstIsF = dist([e.x1, e.y1], F) < 1e-9; if (firstIsF) { e.x2 = Q[0]; e.y2 = Q[1]; } else { e.x1 = Q[0]; e.y1 = Q[1]; } };
    const outs = [];
    if (chamfer && (chamfer[0] > 0 || chamfer[1] > 0)) {
      const C1 = addv(P, mulv(u1, chamfer[0])), C2 = addv(P, mulv(u2, chamfer[1]));
      if (chamfer[0] > dist(P, F1) || chamfer[1] > dist(P, F2)) throw new Error('모따기 거리가 선보다 깁니다');
      set(e1, F1, C1); set(e2, F2, C2); outs.push({ ...baseOf(e1), type:'line', x1:C1[0], y1:C1[1], x2:C2[0], y2:C2[1] });
    } else if (r > 0) {
      const th = Math.acos(Math.max(-1, Math.min(1, dot(u1, u2)))); if (th < 1e-6 || Math.PI - th < 1e-6) throw new Error('두 선이 일직선입니다');
      const t = r / Math.tan(th / 2); if (t > dist(P, F1) + 1e-6 || t > dist(P, F2) + 1e-6) throw new Error('반지름이 너무 큽니다');
      const T1 = addv(P, mulv(u1, t)), T2 = addv(P, mulv(u2, t)), c = addv(P, mulv(unit(addv(u1, u2)), r / Math.sin(th / 2)));
      set(e1, F1, T1); set(e2, F2, T2);
      let a1 = angOf(c, T1), a2 = angOf(c, T2); if (norm360(a2 - a1) > 180) [a1, a2] = [a2, a1];
      outs.push({ ...baseOf(e1), type:'arc', cx:c[0], cy:c[1], r, a1:norm360(a1), a2:norm360(a2), layer:e1.type === 'line' ? e1.layer : '0' });
    } else { set(e1, F1, P); set(e2, F2, P); }
    outs.forEach(addEnt); return outs;
  },
  filletPoly(e, r, chamfer) { // 폴리선의 모든 꼭짓점
    if (!e.pts && e.type !== 'rect') throw new Error('폴리선이 아닙니다');
    if (e.type === 'rect') { const q = rectPts(e); delete e.x; delete e.y; delete e.w; delete e.h; e.type = 'polyline'; e.pts = q; e.closed = true; }
    const P = e.pts, n = P.length, closed = e.type !== 'polyline' || e.closed, out = [];
    for (let i = 0; i < n; i++) {
      if (!closed && (i === 0 || i === n - 1)) { out.push(P[i]); continue; }
      const p = P[i], a = P[(i - 1 + n) % n], b = P[(i + 1) % n], u1 = unit(sub(a, p)), u2 = unit(sub(b, p)), th = Math.acos(Math.max(-1, Math.min(1, dot(u1, u2))));
      if (th < 1e-6 || Math.PI - th < 1e-6) { out.push(p); continue; }
      if (chamfer) { out.push(addv(p, mulv(u1, chamfer)), addv(p, mulv(u2, chamfer))); continue; }
      const t = Math.min(r / Math.tan(th / 2), dist(p, a) / 2, dist(p, b) / 2), rr = t * Math.tan(th / 2), c = addv(p, mulv(unit(addv(u1, u2)), rr / Math.sin(th / 2)));
      const T1 = addv(p, mulv(u1, t)), T2 = addv(p, mulv(u2, t)); let a1 = angOf(c, T1), sw = norm360(angOf(c, T2) - a1); if (sw > 180) sw -= 360;
      for (let j = 0; j <= 8; j++) out.push(polar(c, rr, a1 + sw * j / 8));
    }
    e.pts = out; return [e];
  },
  breakAt(e, p1, p2) {
    const C = curveOf(e); if (!C) throw new Error(`${TYPE_KO[e.type] || e.type}은(는) 끊을 수 없습니다`);
    let t1 = C.param(p1), t2 = p2 ? C.param(p2) : t1;
    if (!C.closed) { if (t1 > t2) [t1, t2] = [t2, t1]; return replaceEnt(e, [t1 > EPS ? pieceOf(e, C, 0, t1) : null, t2 < C.L - EPS ? pieceOf(e, C, t2, C.L) : null]); }
    if (!p2) throw new Error('닫힌 도형은 두 점으로 끊어야 합니다');
    return replaceEnt(e, [pieceOf(e, C, t2, t1 < t2 ? t1 + C.L : t1)]);
  },
  join(list) {
    const chainOf = e => {
      if (e.type === 'line') return [[e.x1, e.y1], [e.x2, e.y2]];
      if (e.type === 'polyline' && !e.closed) return e.pts.map(p => p.slice());
      if (e.type === 'arc') { const sw = norm360(e.a2 - e.a1), n = Math.max(4, Math.ceil(sw / 10)); return Array.from({ length:n + 1 }, (_, i) => polar([e.cx, e.cy], e.r, e.a1 + sw * i / n)); }
      return null;
    };
    const items = list.map(e => [e, chainOf(e)]).filter(x => x[1]);
    if (items.length < 2) throw new Error('결합할 선·열린 폴리선·호가 두 개 이상 필요합니다');
    const tol = 0.5, near = (a, b) => dist(a, b) <= tol;
    let [first, cur] = items.shift(); const used = [first];
    for (let found = true; found;) {
      found = false;
      for (let i = 0; i < items.length; i++) {
        const c = items[i][1], L = cur.length - 1, M = c.length - 1;
        if (near(cur[L], c[0])) cur = cur.concat(c.slice(1));
        else if (near(cur[L], c[M])) cur = cur.concat(c.slice().reverse().slice(1));
        else if (near(cur[0], c[M])) cur = c.concat(cur.slice(1));
        else if (near(cur[0], c[0])) cur = c.slice().reverse().concat(cur.slice(1));
        else continue;
        used.push(items[i][0]); items.splice(i, 1); found = true; break;
      }
    }
    const closed = cur.length > 3 && near(cur[0], cur[cur.length - 1]); if (closed) cur.pop();
    const res = { ...baseOf(first), type:'polyline', pts:cur, closed };
    doc.ents = doc.ents.filter(x => !used.includes(x)); used.forEach(x => sel.delete(x.id));
    addEnt(res); return { ent:res, joined:used.length, left:items.length };
  },
  explode(e) {
    const b = baseOf(e), L = (a, c) => ({ ...b, type:'line', x1:a[0], y1:a[1], x2:c[0], y2:c[1] }), outs = [];
    const segsOf = (pts, closed) => { const n = closed ? pts.length : pts.length - 1; for (let i = 0; i < n; i++) outs.push(L(pts[i], pts[(i + 1) % pts.length])); };
    const texts = prs => prs.filter(q => q.k === 'text').forEach(q => outs.push({ ...b, type:'text', x:q.x, y:q.y, h:q.h, rot:q.rot / D2R, text:q.text }));
    switch (e.type) {
      case 'rect': segsOf(rectPts(e), true); break;
      case 'polyline': segsOf(e.pts, e.closed); break;
      case 'room': case 'bldg': case 'slab': segsOf(e.pts, true); break;
      case 'wall': segsOf(wallQuad(e), true); break;
      case 'equip': segsOf(equipPts(e), true); break;
      case 'ellipse': case 'spline': { const q = primsAny(e)[0]; outs.push({ ...b, type:'polyline', pts:q.pts, closed:q.closed }); break; }
      case 'donut': outs.push({ ...b, type:'circle', cx:e.cx, cy:e.cy, r:e.ro }); if (e.ri > 0) outs.push({ ...b, type:'circle', cx:e.cx, cy:e.cy, r:e.ri }); break;
      case 'mtext': case 'leader': case 'dimang': case 'hatch': case 'dim': case 'dimdia': case 'dimrad': {
        const prs = primsAny(e);
        prs.forEach(q => { if (q.k === 'pl') q.pts.length === 2 ? outs.push(L(q.pts[0], q.pts[1])) : outs.push({ ...b, type:'polyline', pts:q.pts, closed:q.closed }); else if (q.k === 'arc') outs.push({ ...b, type:'arc', cx:q.c[0], cy:q.c[1], r:q.r, a1:q.a1, a2:q.a2 }); });
        texts(prs); if (e.type === 'hatch' && e.pat === 'SOLID') return null; break;
      }
      case 'insert': {
        const blk = (doc.blocks || {})[e.name]; if (!blk) return null;
        const T = insertXf(e, blk), o = T.mir ? { mirror:T.rot / 2, k:Math.abs(T.sx) } : { rot:T.rot, k:Math.abs(T.sx) };
        for (const be of blk.ents) { const n = clone(be); delete n.id; xformEnt(n, T.f, o); if (!n.layer || n.layer === '0') n.layer = e.layer; outs.push(n); }
        break;
      }
      default: return null;
    }
    return replaceEnt(e, outs);
  },
  stretch(win, dx, dy) {
    const [x0, y0, x1, y1] = [Math.min(win[0], win[2]), Math.min(win[1], win[3]), Math.max(win[0], win[2]), Math.max(win[1], win[3])];
    const inW = p => p[0] >= x0 && p[0] <= x1 && p[1] >= y0 && p[1] <= y1, mv = p => [p[0] + dx, p[1] + dy];
    let n = 0;
    for (const e of doc.ents.filter(visible)) {
      const bb = bounds([e]); if (!bb || bb[2] < x0 || bb[0] > x1 || bb[3] < y0 || bb[1] > y1) continue;
      if (bb[0] >= x0 && bb[2] <= x1 && bb[1] >= y0 && bb[3] <= y1) { moveEnt(e, dx, dy); n++; continue; }
      if (e.type === 'rect') { const q = rectPts(e); delete e.x; delete e.y; delete e.w; delete e.h; e.type = 'polyline'; e.pts = q; e.closed = true; }
      let hit = false;
      for (const [a, c] of [['x1', 'y1'], ['x2', 'y2']]) if (a in e && inW([e[a], e[c]])) { [e[a], e[c]] = mv([e[a], e[c]]); hit = true; }
      if (e.pts) e.pts = e.pts.map(p => inW(p) ? (hit = true, mv(p)) : p);
      for (const [a, c] of [['cx', 'cy'], ['x', 'y']]) if (a in e && !e.pts && !('x1' in e) && inW([e[a], e[c]])) { moveEnt(e, dx, dy); hit = true; break; }
      if (hit) n++;
    }
    return n;
  },
  lengthen(e, pick, { delta, total }) {
    if (['line', 'wall', 'window'].includes(e.type)) {
      const p1 = [e.x1, e.y1], p2 = [e.x2, e.y2], L = dist(p1, p2), nl = total != null ? total : L + delta; if (!(nl > 0)) throw new Error('길이가 0 이하가 됩니다');
      if (dist(pick, p2) <= dist(pick, p1)) { const q = addv(p1, mulv(unit(sub(p2, p1)), nl)); e.x2 = q[0]; e.y2 = q[1]; } else { const q = addv(p2, mulv(unit(sub(p1, p2)), nl)); e.x1 = q[0]; e.y1 = q[1]; }
      return [e];
    }
    if (e.type === 'arc') {
      const c = [e.cx, e.cy], sw = norm360(e.a2 - e.a1), nsw = (total != null ? total : sw * D2R * e.r + delta) / e.r / D2R; if (!(nsw > 0) || nsw >= 360) throw new Error('호 길이가 맞지 않습니다');
      if (dist(pick, polar(c, e.r, e.a2)) <= dist(pick, polar(c, e.r, e.a1))) e.a2 = norm360(e.a1 + nsw); else e.a1 = norm360(e.a2 - nsw);
      return [e];
    }
    throw new Error('선이나 호만 길이를 바꿀 수 있습니다');
  },
  arrayRect(list, rows, cols, dx, dy) { const out = []; for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) { if (!r && !c) continue; for (const e of list) { const n = clone(e); delete n.id; moveEnt(n, c * dx, r * dy); addEnt(n); out.push(n); } } return out; },
  arrayPolar(list, ctr, count, angle = 360, rot = true) {
    const step = Math.abs(angle) >= 360 ? angle / count : angle / Math.max(1, count - 1), out = [];
    for (let i = 1; i < count; i++) for (const e of list) {
      const n = clone(e); delete n.id; const a = step * i;
      if (rot) xformEnt(n, rotF(ctr, a), { rot:a }); else { const b = bounds([e]), c0 = [(b[0] + b[2]) / 2, (b[1] + b[3]) / 2], c1 = rotF(ctr, a)(c0); moveEnt(n, c1[0] - c0[0], c1[1] - c0[1]); }
      addEnt(n); out.push(n);
    }
    return out;
  },
  divide(e, n, d) {
    const C = curveOf(e); if (!C) throw new Error('나눌 수 없는 객체입니다');
    const ts = []; if (n) for (let i = 1; i < n; i++) ts.push(C.L * i / n); else for (let t = d; t < C.L - 1e-9; t += d) ts.push(t);
    return ts.map(t => { const p = C.at(t), q = { type:'point', layer:e.layer, x:p[0], y:p[1] }; addEnt(q); return q; });
  },
  hatchAt(p, pat, sc, ang) { // 클릭한 점을 감싸는 가장 작은 닫힌 도형을 경계로(안쪽 닫힌 도형은 구멍)
    const loops = live().map(e => [e, closedLoop(e)]).filter(x => x[1] && x[1].length >= 3);
    const hits = loops.filter(([, L]) => inPoly(p, L)).sort((a, b) => polyAreaM2(a[1]) - polyAreaM2(b[1]));
    if (!hits.length) throw new Error('클릭한 곳을 감싸는 닫힌 도형이 없습니다');
    const outer = hits[0][1], holes = loops.filter(([e, L]) => e !== hits[0][0] && !inPoly(p, L) && L.every(q => inPoly(q, outer))).map(x => x[1]);
    const h = { type:'hatch', layer:'hatch', pts:outer.map(q => q.slice()), holes, pat:pat || 'ANSI31', sc:sc || autoHatchScale(outer), ang:ang || 0 };
    if (!holes.length) delete h.holes; addEnt(h); return h;
  },
  makeBlock(name, base, list) {
    if (!name) throw new Error('블록 이름이 필요합니다'); if (!list.length) throw new Error('블록에 넣을 객체가 없습니다');
    doc.blocks = doc.blocks || {};
    doc.blocks[name] = { base:base.slice(), ents:list.map(e => { const n = clone(e); delete n.id; delete n.floor; return n; }) };
    doc.ents = doc.ents.filter(e => !list.includes(e)); list.forEach(e => sel.delete(e.id));
    const ins = { type:'insert', layer:'0', name, x:base[0], y:base[1], sx:1, sy:1, rot:0 }; addEnt(ins); return ins;
  },
  matchProp(src, list) { for (const e of list) { e.layer = src.layer; if (src.h && (e.type === src.type) && e.h) e.h = src.h; if (src.type === 'hatch' && e.type === 'hatch') { e.pat = src.pat; e.sc = src.sc; e.ang = src.ang; } if (src.type === 'wall' && e.type === 'wall') { e.t = src.t; e.wk = src.wk; } } return list; }
};
function closedLoop(e) {
  if (['rect', 'room', 'bldg', 'slab'].includes(e.type) || (e.type === 'polyline' && e.closed) || (e.type === 'ellipse' && e.a1 == null) || (e.type === 'spline' && e.closed)) return primsAny(e)[0].pts;
  if (e.type === 'circle') return Array.from({ length:72 }, (_, i) => polar([e.cx, e.cy], e.r, i * 5));
  if (e.type === 'hatch') return e.pts;
  return null;
}
window.CAD_GEOM = G; // 시험·디버그용

/* ---------- 고르기·스냅·극좌표 ---------- */
pick = p => { // 꺼지거나 잠긴 레이어는 고르지 않음
  const tol = 8 / view.s; let best = null, bd = tol;
  for (const e of doc.ents) { if (layerBlocked(e)) continue; const d = hitDist(e, p); if (d < bd) { bd = d; best = e; } }
  return best;
};
const SNAP_KO = { '끝점':'end', '경첩':'end', '중간점':'mid', '중심':'cen', '사분점':'quad', '절점':'node', '삽입점':'ins' };
const SNAP_DEFAULT = { end:true, mid:true, cen:true, quad:true, int:true, perp:true, near:false, node:true, ins:true };
settings.snap = Object.assign({}, SNAP_DEFAULT, settings.snap || {});
let polarOn = false; settings.polarInc = settings.polarInc || 15;
findSnap = p => {
  if (!snapOn) return null;
  const tol = 10 / view.s, M = settings.snap; let best = null, bd = tol;
  const near = [];
  for (const e of doc.ents) {
    if (layerOff(e)) continue;
    const bb = bounds([e]); if (bb && (p[0] < bb[0] - tol || p[0] > bb[2] + tol || p[1] < bb[1] - tol || p[1] > bb[3] + tol) && e.type !== 'xline' && e.type !== 'ray') continue;
    near.push(e);
    for (const s of snapPts(e)) { if (!M[SNAP_KO[s[2]] || 'end']) continue; const d = Math.hypot(s[0] - p[0], s[1] - p[1]); if (d < bd) { bd = d; best = s; } }
  }
  if (best) return best;
  const prims = near.slice(0, 300).map(e => geomPrims(e));
  if (M.int) for (let i = 0; i < prims.length; i++) for (let j = i + 1; j < prims.length; j++) for (const a of prims[i]) for (const b of prims[j]) for (const x of interPrims(a, b)) { const d = dist(x, p); if (d < bd) { bd = d; best = [x[0], x[1], '교차점']; } }
  if (best) return best;
  const ref = cmd && refPoint(cmd);
  if (M.perp && ref) for (const gp of prims) for (const q of gp) if (q.k === 'seg') {
    const d = unit(sub(q.b, q.a)), t = dot(sub(ref, q.a), d), L = dist(q.a, q.b); if (t < 0 || t > L) continue;
    const f = addv(q.a, mulv(d, t)), dd = dist(f, p); if (dd < bd) { bd = dd; best = [f[0], f[1], '수직']; }
  }
  if (best) return best;
  if (M.near) for (const gp of prims) for (const q of gp) { const [s] = primParam(q, p), f = primAt(q, s), dd = dist(f, p); if (dd < bd) { bd = dd; best = [f[0], f[1], '근처점']; } }
  return best;
};
const applyOrtho0 = applyOrtho;
applyOrtho = (p, ref) => {
  if (orthoOn || !polarOn || !ref) return applyOrtho0(p, ref);
  const a = angOf(ref, p), inc = settings.polarInc, s = Math.round(a / inc) * inc;
  if (Math.abs(a - s) > 3) return p;
  return polar(ref, dist(ref, p), s);
};

/* ---------- 레이어(켜기·잠금·색·새 레이어) ---------- */
function layerProp(k) { return (doc.layerProps || {})[k] || {}; }
window.layerOff = e => !!layerProp(e.layer).off;
window.layerBlocked = e => { const p = layerProp(e.layer); return !!(p.off || p.lock); };
const layerLabel = k => { const o = [...$('#layerSel').options].find(x => x.value === k); return o ? o.textContent : k; };
function ensureLayer(key, name, color, dash) {
  if (!LAYERS[key]) LAYERS[key] = { color, dash:dash || [] };
  // DXF R12는 한글 레이어 이름을 못 담아서 영문이 아니면 L번호로 내보냄
  if (!DXF_BASE[key]) DXF_BASE[key] = [/^[\x21-\x7e]+$/.test(name) ? name.toUpperCase().slice(0, 31) : 'L' + Object.keys(DXF_BASE).length, 7, dash && dash.length ? 'HIDDEN' : 'CONTINUOUS'];
  if (![...$('#layerSel').options].some(o => o.value === key)) { const o = document.createElement('option'); o.value = key; o.textContent = name; $('#layerSel').appendChild(o); }
}
function ensureUserLayers() {
  for (const [k, v] of Object.entries(doc.userLayers || {})) ensureLayer(k, v.name, v.color, v.dash);
  for (const [k, v] of Object.entries(doc.layerProps || {})) if (v.color && LAYERS[k]) LAYERS[k].color = v.color;
}
const draw0 = draw;
draw = () => { ensureUserLayers(); draw0(); drawGrips(); };
function openLayers() {
  let dlg = $('#dlgLayer');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgLayer';
    dlg.innerHTML = '<h2>레이어</h2><div class="hint">● 현재 레이어 · 끄면 안 보이고, 잠그면 보이지만 고를 수 없습니다.</div>' +
      '<div style="max-height:52vh;overflow:auto;margin-top:8px"><table class="help" id="layTab"></table></div>' +
      '<div style="display:flex;gap:6px;margin-top:10px"><input type="text" id="layNew" placeholder="새 레이어 이름 (예: 가구, 조경)" style="flex:1"><input type="color" id="layNewC" value="#9fd3ff"><button id="layAdd">추가</button></div>' +
      '<div class="btns"><button id="layClose" class="primary">닫기</button></div>';
    document.body.appendChild(dlg);
    $('#layClose').onclick = () => dlg.close();
    $('#layAdd').onclick = () => {
      const name = $('#layNew').value.trim(); if (!name) return;
      const key = 'u_' + Date.now().toString(36); doc.userLayers = doc.userLayers || {}; doc.userLayers[key] = { name, color:$('#layNewC').value, dash:[] };
      ensureLayer(key, name, $('#layNewC').value); $('#layNew').value = ''; save(); renderLay();
    };
  }
  const renderLay = () => {
    const cnt = {}; doc.ents.forEach(e => { cnt[e.layer] = (cnt[e.layer] || 0) + 1; });
    const tb = $('#layTab'); tb.innerHTML = '<tr><td>현재</td><td>이름</td><td>색</td><td>켜기</td><td>잠금</td><td>개수</td></tr>';
    for (const k of Object.keys(LAYERS)) {
      const p = layerProp(k), tr = document.createElement('tr');
      tr.innerHTML = `<td><input type="radio" name="layCur" ${curLayer === k ? 'checked' : ''}></td><td></td><td><input type="color"></td><td><input type="checkbox" ${p.off ? '' : 'checked'}></td><td><input type="checkbox" ${p.lock ? 'checked' : ''}></td><td>${cnt[k] || 0}</td>`;
      tr.children[1].textContent = layerLabel(k);
      const [rCur, , cIn, cOn, cLock] = tr.querySelectorAll('input'), setP = (key, v) => { doc.layerProps = doc.layerProps || {}; doc.layerProps[k] = Object.assign({}, doc.layerProps[k], { [key]:v }); save(); draw(); };
      const hex = /^#[0-9a-f]{6}$/i.test(LAYERS[k].color) ? LAYERS[k].color : '#e8e8e8'; tr.querySelector('input[type=color]').value = hex;
      rCur.onchange = () => { curLayer = k; $('#layerSel').value = k; status(`현재 레이어: ${layerLabel(k)}`); };
      tr.querySelector('input[type=color]').onchange = ev => { LAYERS[k].color = ev.target.value; setP('color', ev.target.value); };
      tr.querySelectorAll('input[type=checkbox]')[0].onchange = ev => setP('off', !ev.target.checked);
      tr.querySelectorAll('input[type=checkbox]')[1].onchange = ev => setP('lock', ev.target.checked);
      tb.appendChild(tr);
    }
  };
  renderLay(); dlg.showModal();
}
function openOsnap() {
  let dlg = $('#dlgOsnap');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgOsnap';
    const items = [['end', '끝점'], ['mid', '중간점'], ['cen', '중심'], ['quad', '사분점'], ['int', '교차점'], ['perp', '수직'], ['near', '근처점'], ['node', '절점'], ['ins', '삽입점']];
    dlg.innerHTML = '<h2>객체 스냅·극좌표 설정</h2>' + items.map(([k, t]) => `<label><input type="checkbox" data-snap="${k}"> ${t}</label>`).join('') +
      '<label for="polInc">극좌표 각도 간격 (F10)</label><select id="polInc"><option>5</option><option>10</option><option>15</option><option>30</option><option>45</option><option>90</option></select>' +
      '<div class="btns"><button id="osClose" class="primary">닫기</button></div>';
    document.body.appendChild(dlg);
    dlg.querySelectorAll('[data-snap]').forEach(cb => { cb.onchange = () => { settings.snap[cb.dataset.snap] = cb.checked; store.set('vc.settings', settings); }; });
    $('#polInc').onchange = ev => { settings.polarInc = +ev.target.value; store.set('vc.settings', settings); };
    $('#osClose').onclick = () => dlg.close();
  }
  dlg.querySelectorAll('[data-snap]').forEach(cb => { cb.checked = !!settings.snap[cb.dataset.snap]; });
  $('#polInc').value = String(settings.polarInc); dlg.showModal();
}

/* ---------- 그립(선택한 객체의 파란 점을 눌러 바로 고치기) ---------- */
function gripsOf(e) {
  switch (e.type) {
    case 'line': case 'wall': case 'window': return [[e.x1, e.y1, 'p1'], [e.x2, e.y2, 'p2'], [(e.x1 + e.x2) / 2, (e.y1 + e.y2) / 2, 'move']];
    case 'dim': return [[e.x1, e.y1, 'p1'], [e.x2, e.y2, 'p2']];
    case 'polyline': case 'room': case 'bldg': case 'slab': case 'hatch': case 'spline': case 'leader': return e.pts.map((p, i) => [p[0], p[1], 'v', i]);
    case 'circle': return [[e.cx, e.cy, 'move'], [e.cx + e.r, e.cy, 'rad'], [e.cx, e.cy + e.r, 'rad'], [e.cx - e.r, e.cy, 'rad'], [e.cx, e.cy - e.r, 'rad']];
    case 'arc': { const c = [e.cx, e.cy]; return [[e.cx, e.cy, 'move'], [...polar(c, e.r, e.a1), 'a1'], [...polar(c, e.r, e.a2), 'a2'], [...polar(c, e.r, e.a1 + norm360(e.a2 - e.a1) / 2), 'rad']]; }
    case 'rect': return rectPts(e).map((p, i) => [p[0], p[1], 'rc', i]);
    case 'ellipse': case 'donut': case 'column': case 'equip': case 'dimdia': case 'dimrad': case 'dimang': return [[e.cx, e.cy, 'move']];
    case 'text': case 'mtext': case 'insert': case 'point': case 'door': case 'xline': case 'ray': return [[e.x, e.y, 'move']];
  }
  return [];
}
function applyGrip(e, g, p) {
  const k = g[2];
  if (k === 'p1') { e.x1 = p[0]; e.y1 = p[1]; }
  else if (k === 'p2') { e.x2 = p[0]; e.y2 = p[1]; }
  else if (k === 'move') moveEnt(e, p[0] - g[0], p[1] - g[1]);
  else if (k === 'v') e.pts[g[3]] = p.slice();
  else if (k === 'rad') e.r = dist([e.cx, e.cy], p);
  else if (k === 'a1') e.a1 = norm360(angOf([e.cx, e.cy], p));
  else if (k === 'a2') e.a2 = norm360(angOf([e.cx, e.cy], p));
  else if (k === 'rc') { const o = rectPts(e)[(g[3] + 2) % 4]; Object.assign(e, { x:Math.min(o[0], p[0]), y:Math.min(o[1], p[1]), w:Math.abs(p[0] - o[0]), h:Math.abs(p[1] - o[1]) }); }
}
function drawGrips() {
  if (sel.size > 30) return;
  ctx.setLineDash([]); ctx.lineWidth = 1;
  for (const id of sel) { const e = findEnt(id); if (!e) continue; for (const g of gripsOf(e)) { const [x, y] = w2s(g[0], g[1]); ctx.fillStyle = '#2f7fd1'; ctx.fillRect(x - 4, y - 4, 8, 8); ctx.strokeStyle = '#dfe9f5'; ctx.strokeRect(x - 4, y - 4, 8, 8); } }
}
const clickAt0 = clickAt;
clickAt = (sx, sy) => {
  if (!cmd && sel.size && sel.size <= 30) {
    for (const id of sel) {
      const e = findEnt(id); if (!e) continue;
      for (const g of gripsOf(e)) { const [x, y] = w2s(g[0], g[1]); if (Math.abs(x - sx) <= 6 && Math.abs(y - sy) <= 6) { startGrip(e, g); return; } }
    }
  }
  clickAt0(sx, sy);
};
function startGrip(e, g) {
  startCmd('GRIP'); cmd.ent = e; cmd.grip = g; cmd.ref = [g[0], g[1]]; cmd.prompt = '그립: 새 위치 지정 (Esc=취소):'; setPrompt(); draw();
}
CMDS.GRIP = () => ({
  start() {},
  point(c, p) { snapshot(); applyGrip(c.ent, c.grip, p); save(); endCmd(); },
  preview(c, cur) { if (!c.ent) return []; const n = clone(c.ent); applyGrip(n, c.grip, cur); n.ghost = true; return [n, { ...lineE(c.ref, cur), ghost:true }]; }
});

/* ---------- 대화형 명령 ---------- */
const N = t => NUMRE.test(t) ? +t : null;
const withSel = () => [...sel].map(findEnt).filter(Boolean);
function tryRun(fn) { try { return fn(); } catch (err) { status(err.message); return null; } }

Object.assign(CMDS, {
  // 그리기 ---------------------------------------------------------------
  XLINE: () => ({
    start(c) { c.prompt = '무한선 — 점 지정 (H=수평, V=수직, A=각도):'; },
    text(c, t) { const u = t.toUpperCase(); if (u === 'H' || u === 'V') { c.fixed = u === 'H' ? 0 : 90; c.prompt = `${u === 'H' ? '수평' : '수직'} 무한선이 지날 점 (Enter=끝):`; return true; } if (u === 'A') { c.askA = true; c.prompt = '각도 입력:'; return true; } if (c.askA && N(t) != null) { c.fixed = N(t); c.askA = false; c.prompt = '무한선이 지날 점 (Enter=끝):'; return true; } },
    point(c, p) {
      if (c.fixed != null) { commit({ type:'xline', layer:curLayer, x:p[0], y:p[1], ang:c.fixed }); return; }
      if (!c.base) { c.base = p; c.ref = p; c.prompt = '지날 점 (Enter=끝):'; return; }
      commit({ type:'xline', layer:curLayer, x:c.base[0], y:c.base[1], ang:angOf(c.base, p) });
    },
    preview(c, cur) { if (c.fixed != null) return [{ type:'xline', layer:curLayer, x:cur[0], y:cur[1], ang:c.fixed }]; return c.base ? [{ type:'xline', layer:curLayer, x:c.base[0], y:c.base[1], ang:angOf(c.base, cur) }] : []; }
  }),
  RAY: () => ({
    start(c) { c.prompt = '광선 — 시작점:'; },
    point(c, p) { if (!c.base) { c.base = p; c.ref = p; c.prompt = '지날 점 (Enter=끝):'; return; } commit({ type:'ray', layer:curLayer, x:c.base[0], y:c.base[1], ang:angOf(c.base, p) }); },
    preview(c, cur) { return c.base ? [{ type:'ray', layer:curLayer, x:c.base[0], y:c.base[1], ang:angOf(c.base, cur) }] : []; }
  }),
  POLYGON: () => ({
    start(c) { c.n = 4; c.prompt = '다각형 — 변의 수 <4>:'; c.stage = 'n'; },
    enter(c) { if (c.stage === 'n') { c.stage = 'c'; c.prompt = '중심점:'; } else if (c.stage === 'ic') { c.stage = 'r'; c.prompt = '반지름 (숫자 또는 클릭):'; } else endCmd(); },
    text(c, t) {
      if (c.stage === 'n' && N(t) >= 3) { c.n = Math.round(N(t)); c.stage = 'c'; c.prompt = '중심점:'; return true; }
      if (c.stage === 'ic' && /^[ic]$/i.test(t)) { c.circ = /c/i.test(t); c.stage = 'r'; c.prompt = '반지름 (숫자 또는 클릭):'; return true; }
      if (c.stage === 'r' && N(t) > 0) { this.make(c, N(t), -90 + 180 / c.n + (c.n % 2 ? 0 : 0)); return true; }
    },
    pts(c, r, a0) { const R = c.circ ? r / Math.cos(Math.PI / c.n) : r; return Array.from({ length:c.n }, (_, i) => polar(c.ctr, R, a0 + 360 * i / c.n)); },
    make(c, r, a0) { commit({ type:'polyline', layer:curLayer, pts:this.pts(c, r, a0), closed:true }); endCmd(); },
    point(c, p) {
      if (c.stage === 'n') { c.stage = 'c'; }
      if (c.stage === 'c') { c.ctr = p; c.ref = p; c.stage = 'ic'; c.prompt = '내접(I) / 외접(C) <I>:'; return; }
      if (c.stage === 'ic') c.stage = 'r';
      if (c.stage === 'r') { const a = angOf(c.ctr, p); this.make(c, dist(c.ctr, p), c.circ ? a - 180 / c.n : a); }
    },
    preview(c, cur) { if (c.stage !== 'r' && c.stage !== 'ic' || !c.ctr) return []; const a = angOf(c.ctr, cur); return [{ type:'polyline', layer:curLayer, pts:this.pts(c, dist(c.ctr, cur), c.circ ? a - 180 / c.n : a), closed:true }]; }
  }),
  ELLIPSE: () => ({
    start(c) { c.prompt = '타원 — 축의 끝점 (C=중심):'; },
    text(c, t) {
      if (!c.pts.length && /^c$/i.test(t)) { c.center = true; c.prompt = '중심점:'; return true; }
      if (c.pts.length === 2 && N(t) > 0) { this.make(c, N(t)); return true; }
    },
    geo(c) { const [a, b] = c.pts; return c.center ? { ctr:a, rx:dist(a, b), rot:angOf(a, b) } : { ctr:mulv(addv(a, b), 0.5), rx:dist(a, b) / 2, rot:angOf(a, b) }; },
    make(c, ry) { const g = this.geo(c); commit({ type:'ellipse', layer:curLayer, cx:g.ctr[0], cy:g.ctr[1], rx:g.rx, ry, rot:g.rot }); endCmd(); },
    point(c, p) {
      if (c.pts.length < 2) { c.pts.push(p); c.prompt = c.pts.length === 1 ? (c.center ? '축의 끝점:' : '축의 다른 끝점:') : '다른 축의 반지름 (클릭 또는 숫자):'; if (c.pts.length === 2) c.ref = this.geo(c).ctr; return; }
      const g = this.geo(c), u = [Math.cos(g.rot * D2R), Math.sin(g.rot * D2R)]; this.make(c, Math.abs(crs(u, sub(p, g.ctr))));
    },
    preview(c, cur) {
      if (c.pts.length === 1) return [{ ...lineE(c.pts[0], cur), ghost:true }];
      if (c.pts.length === 2) { const g = this.geo(c), u = [Math.cos(g.rot * D2R), Math.sin(g.rot * D2R)], ry = Math.abs(crs(u, sub(cur, g.ctr))); return ry > 0 ? [{ type:'ellipse', layer:curLayer, cx:g.ctr[0], cy:g.ctr[1], rx:g.rx, ry, rot:g.rot }] : []; }
      return [];
    }
  }),
  SPLINE: () => ({
    start(c) { c.prompt = '스플라인 — 첫 점:'; },
    point(c, p) { c.pts.push(p); c.prompt = '다음 점 (C=닫기, Enter=끝):'; },
    finish(c, closed) { if (c.pts.length >= 2) commit({ type:'spline', layer:curLayer, pts:c.pts.slice(), closed }); endCmd(); },
    enter(c) { this.finish(c, false); },
    text(c, t) { if (/^c$/i.test(t) && c.pts.length > 2) { this.finish(c, true); return true; } },
    preview(c, cur) { return c.pts.length ? [{ type:'spline', layer:curLayer, pts:[...c.pts, cur] }] : []; }
  }),
  POINT: () => ({ start(c) { c.prompt = '점 위치 (Enter=끝):'; }, point(c, p) { commit({ type:'point', layer:curLayer, x:p[0], y:p[1] }); } }),
  DONUT: () => ({
    start(c) { c.ri = 50; c.ro = 100; c.stage = 'ri'; c.prompt = '도넛 — 안쪽 지름 <100>:'; },
    enter(c) { if (c.stage === 'ri') { c.stage = 'ro'; c.prompt = '바깥 지름 <200>:'; } else if (c.stage === 'ro') { c.stage = 'c'; c.prompt = '중심점 (Enter=끝):'; } else endCmd(); },
    text(c, t) { const v = N(t); if (v == null || v < 0) return; if (c.stage === 'ri') { c.ri = v / 2; c.stage = 'ro'; c.prompt = `바깥 지름 <${fmt(Math.max(c.ri * 4, 1))}>:`; c.ro = Math.max(c.ri * 2, 0.5); return true; } if (c.stage === 'ro' && v > 0) { c.ro = v / 2; c.stage = 'c'; c.prompt = '중심점 (Enter=끝):'; return true; } },
    point(c, p) { if (c.stage !== 'c') { c.stage = 'c'; } commit({ type:'donut', layer:curLayer, cx:p[0], cy:p[1], ri:Math.min(c.ri, c.ro), ro:c.ro }); },
    preview(c, cur) { return c.stage === 'c' ? [{ type:'donut', layer:curLayer, cx:cur[0], cy:cur[1], ri:Math.min(c.ri, c.ro), ro:c.ro }] : []; }
  }),
  HATCH: () => ({
    start(c) { c.pat = 'ANSI31'; c.stage = 'pat'; c.prompt = '해치 — 패턴 [SOLID/ANSI31/ANSI37/NET] <ANSI31>:'; },
    enter(c) { if (c.stage === 'pat') { c.stage = 'sc'; c.prompt = '패턴 간격 배율 <자동>:'; } else if (c.stage === 'sc') { c.stage = 'pick'; c.prompt = '해치할 영역 안쪽을 클릭 (Enter=끝):'; } else endCmd(); },
    text(c, t) {
      const u = t.toUpperCase();
      if (c.stage === 'pat' && ['SOLID', 'ANSI31', 'ANSI37', 'NET'].includes(u)) { c.pat = u; c.stage = 'sc'; c.prompt = '패턴 간격 배율 <자동>:'; return true; }
      if (c.stage === 'sc' && N(t) > 0) { c.sc = N(t); c.stage = 'pick'; c.prompt = '해치할 영역 안쪽을 클릭 (Enter=끝):'; return true; }
    },
    point(c, p, raw) { if (c.stage !== 'pick') { c.stage = 'pick'; } snapshot(); if (tryRun(() => G.hatchAt(raw, c.pat, c.sc, 0))) save(); else undoStack.pop(); }
  }),
  REVCLOUD: () => ({
    start(c) { c.prompt = '구름형 수정기호 — 첫 모서리 (O=닫힌 객체 선택):'; },
    text(c, t) { if (/^o$/i.test(t)) { c.obj = true; c.prompt = '닫힌 객체 클릭:'; return true; } },
    cloud(L) { // 경계를 따라 바깥으로 부푼 작은 호를 이어 붙임
      const per = perim(L, true), arcL = Math.max(per / 40, 1), out = []; let a = 0; for (let i = 0; i < L.length; i++) a += L[i][0] * L[(i + 1) % L.length][1] - L[(i + 1) % L.length][0] * L[i][1];
      const sgn = a > 0 ? -1 : 1, C = curveOf({ type:'polyline', pts:L, closed:true }), n = Math.max(8, Math.round(per / arcL));
      for (let i = 0; i < n; i++) { const p = C.at(per * i / n), q = C.at(per * (i + 1) / n), d = unit(sub(q, p)), h = dist(p, q) * 0.35; for (let j = 0; j < 6; j++) { const t = j / 6, bump = Math.sin(Math.PI * t) * h; out.push(addv(addv(p, mulv(sub(q, p), t)), mulv([-d[1] * sgn, d[0] * sgn], bump))); } }
      return out;
    },
    point(c, p, raw) {
      if (c.obj) { const e = pick(raw), L = e && closedLoop(e); if (!L) return status('닫힌 객체를 클릭하세요'); commit({ type:'polyline', layer:curLayer, pts:this.cloud(L), closed:true }); endCmd(); return; }
      if (!c.pts.length) { c.pts.push(p); c.prompt = '반대쪽 모서리:'; return; }
      const a = c.pts[0]; commit({ type:'polyline', layer:curLayer, pts:this.cloud([[a[0], a[1]], [p[0], a[1]], [p[0], p[1]], [a[0], p[1]]]), closed:true }); endCmd();
    },
    preview(c, cur) { if (!c.pts.length) return []; const a = c.pts[0]; return [{ type:'rect', layer:curLayer, x:Math.min(a[0], cur[0]), y:Math.min(a[1], cur[1]), w:Math.abs(cur[0] - a[0]), h:Math.abs(cur[1] - a[1]) }]; }
  }),
  MTEXT: () => ({
    start(c) { c.prompt = '여러 줄 문자 — 왼쪽 위 지점:'; },
    point(c, p) { endCmd(); openMtext(p); }
  }),
  BLOCK: () => ({
    start(c) { c.rawText = true; c.prompt = `블록 이름 입력${Object.keys(doc.blocks || {}).length ? ` (있는 블록: ${Object.keys(doc.blocks).join(', ')})` : ''}:`; },
    text(c, t) {
      if (c.bn) return;
      c.bn = t.trim(); c.rawText = false; c.prompt = '기준점 지정:'; return true;
    },
    point(c, p) {
      if (!c.bn) return;
      c.base = p; c.def.point = null;
      selectStep(c, cc => { snapshot(); const ins = tryRun(() => G.makeBlock(cc.bn, cc.base, withSel())); if (ins) { save(); status(`블록 "${cc.bn}" 만들었습니다`); } else undoStack.pop(); endCmd(); }, '블록으로 만들');
    }
  }),
  INSERT: () => ({
    start(c) {
      const names = Object.keys(doc.blocks || {}); if (!names.length) { endCmd(); status('만든 블록이 없습니다. 먼저 BLOCK(B)으로 만드세요'); return; }
      c.rawText = true; c.prompt = `삽입할 블록 이름 (${names.join(', ')}):`;
    },
    text(c, t) {
      if (!c.bn) { if (!(doc.blocks || {})[t.trim()]) { status('없는 블록입니다: ' + t); return true; } c.bn = t.trim(); c.rawText = false; c.prompt = '삽입점:'; return true; }
      if (c.at && c.sc == null && N(t) > 0) { c.sc = N(t); c.prompt = '회전 각도 <0>:'; return true; }
      if (c.at && c.sc != null && N(t) != null) { this.make(c, N(t)); return true; }
    },
    enter(c) { if (!c.at) return endCmd(); if (c.sc == null) { c.sc = 1; c.prompt = '회전 각도 <0>:'; return; } this.make(c, 0); },
    make(c, rot) { commit({ type:'insert', layer:curLayer, name:c.bn, x:c.at[0], y:c.at[1], sx:c.sc, sy:c.sc, rot }); endCmd(); },
    point(c, p) { if (c.bn && !c.at) { c.at = p; c.prompt = '축척 <1>:'; } },
    preview(c, cur) { return c.bn && !c.at ? [{ type:'insert', layer:curLayer, name:c.bn, x:cur[0], y:cur[1], sx:1, sy:1, rot:0, ghost:true }] : []; }
  }),
  // 수정 ---------------------------------------------------------------
  TRIM: () => ({
    start(c) { c.prompt = '자르기 — 지울 부분을 클릭 (모든 객체가 경계, Enter=끝):'; },
    point(c, p, raw) {
      const e = pick(raw); if (!e) return status('객체를 클릭하세요');
      snapshot(); if (tryRun(() => G.trim(e, live(), raw))) save(); else undoStack.pop();
    }
  }),
  EXTEND: () => ({
    start(c) { c.prompt = '연장 — 늘릴 쪽 끝 가까이를 클릭 (모든 객체가 경계, Enter=끝):'; },
    point(c, p, raw) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); snapshot(); if (tryRun(() => G.extend(e, live(), raw))) save(); else undoStack.pop(); }
  }),
  FILLET: () => ({
    start(c) { c.r = doc.filletR ?? 0; c.prompt = `모깎기 — 첫 객체 (R=반지름 ${fmt(c.r)}, P=폴리선 전체):`; },
    text(c, t) {
      if (/^r$/i.test(t)) { c.askR = true; c.prompt = '모깎기 반지름:'; return true; }
      if (c.askR && N(t) >= 0) { c.r = doc.filletR = N(t); c.askR = false; c.prompt = `첫 객체 (반지름 ${fmt(c.r)}, P=폴리선 전체):`; return true; }
      if (/^p$/i.test(t)) { c.poly = true; c.prompt = '폴리선 클릭:'; return true; }
    },
    point(c, p, raw) {
      const e = pick(raw); if (!e) return status('객체를 클릭하세요');
      if (c.poly) { snapshot(); if (tryRun(() => G.filletPoly(e, c.r))) save(); else undoStack.pop(); endCmd(); return; }
      if (!c.e1) { c.e1 = e; c.p1 = raw; c.prompt = '두번째 객체:'; return; }
      snapshot(); if (tryRun(() => G.corner(c.e1, e, c.r, c.p1, raw))) save(); else undoStack.pop(); endCmd();
    }
  }),
  CHAMFER: () => ({
    start(c) { c.d = doc.chamferD || [0, 0]; c.prompt = `모따기 — 첫 선 (D=거리 ${fmt(c.d[0])},${fmt(c.d[1])}, P=폴리선 전체):`; },
    text(c, t) {
      if (/^d$/i.test(t)) { c.ask = 1; c.prompt = '첫 번째 모따기 거리:'; return true; }
      if (c.ask === 1 && N(t) >= 0) { c.d = [N(t), N(t)]; c.ask = 2; c.prompt = `두 번째 모따기 거리 <${fmt(N(t))}>:`; return true; }
      if (c.ask === 2 && N(t) >= 0) { c.d[1] = N(t); c.ask = 0; doc.chamferD = c.d; c.prompt = '첫 선:'; return true; }
      if (/^p$/i.test(t)) { c.poly = true; c.prompt = '폴리선 클릭:'; return true; }
    },
    enter(c) { if (c.ask === 2) { c.ask = 0; doc.chamferD = c.d; c.prompt = '첫 선:'; } else endCmd(); },
    point(c, p, raw) {
      const e = pick(raw); if (!e) return status('객체를 클릭하세요');
      if (c.poly) { snapshot(); if (tryRun(() => G.filletPoly(e, 0, c.d[0]))) save(); else undoStack.pop(); endCmd(); return; }
      if (!c.e1) { c.e1 = e; c.p1 = raw; c.prompt = '두번째 선:'; return; }
      snapshot(); if (tryRun(() => G.corner(c.e1, e, 0, c.p1, raw, c.d))) save(); else undoStack.pop(); endCmd();
    }
  }),
  BREAK: () => ({
    start(c) { c.prompt = '끊기 — 객체 클릭 (클릭한 곳이 첫 끊는 점):'; },
    text(c, t) { if (c.e && /^f$/i.test(t)) { c.p1 = null; c.prompt = '첫 끊는 점:'; return true; } },
    point(c, p, raw) {
      if (!c.e) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); c.e = e; c.p1 = p; c.prompt = '두번째 끊는 점 (F=첫 점 다시):'; return; }
      if (!c.p1) { c.p1 = p; c.prompt = '두번째 끊는 점:'; return; }
      snapshot(); if (tryRun(() => G.breakAt(c.e, c.p1, p))) save(); else undoStack.pop(); endCmd();
    }
  }),
  BREAKATPOINT: () => ({
    start(c) { c.prompt = '점에서 끊기 — 객체 클릭:'; },
    point(c, p, raw) {
      if (!c.e) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); c.e = e; c.prompt = '끊을 점:'; return; }
      snapshot(); if (tryRun(() => G.breakAt(c.e, p))) save(); else undoStack.pop(); endCmd();
    }
  }),
  JOIN: () => ({ start(c) { selectStep(c, () => { snapshot(); const r = tryRun(() => G.join(withSel())); if (r) { save(); status(`${r.joined}개를 한 폴리선으로 결합${r.left ? ` (이어지지 않은 ${r.left}개 남음)` : ''}`); } else undoStack.pop(); endCmd(); }, '결합'); } }),
  EXPLODE: () => ({ start(c) { selectStep(c, () => { snapshot(); let n = 0; for (const e of withSel()) { const r = G.explode(e); if (r) n++; } if (n) { save(); status(`${n}개 분해`); } else { undoStack.pop(); status('분해할 수 있는 객체가 없습니다'); } sel.clear(); endCmd(); }, '분해'); } }),
  ARRAY: () => ({
    start(c) { selectStep(c, cc => { cc.prompt = '배열 — 직사각형(R) / 원형(P) <R>:'; cc.stage = 'kind'; cc.def.enter = k => { if (k.stage === 'kind') arrayRectStart(k); else endCmd(); }; cc.def.text = arrayText; }, '배열'); }
  }),
  STRETCH: () => ({
    start(c) { c.prompt = '신축 — 늘릴 부분을 걸치는 창의 첫 구석:'; },
    point(c, p) {
      if (!c.w1) { c.w1 = p; c.prompt = '반대쪽 구석:'; return; }
      if (!c.w2) { c.w2 = p; c.prompt = '기준점:'; return; }
      if (!c.base) { c.base = p; c.ref = p; c.prompt = '두번째 점:'; return; }
      snapshot(); const n = G.stretch([...c.w1, ...c.w2], p[0] - c.base[0], p[1] - c.base[1]); save(); endCmd(); status(`${n}개 신축`);
    },
    preview(c, cur) { if (c.w1 && !c.w2) return [{ type:'rect', layer:'0', x:Math.min(c.w1[0], cur[0]), y:Math.min(c.w1[1], cur[1]), w:Math.abs(cur[0] - c.w1[0]), h:Math.abs(cur[1] - c.w1[1]), ghost:true }]; return c.base ? [{ ...lineE(c.base, cur), ghost:true }] : []; }
  }),
  LENGTHEN: () => ({
    start(c) { c.prompt = '길이 조정 — 증분(DE) / 전체 길이(T):'; },
    text(c, t) {
      if (/^de$/i.test(t)) { c.mode = 'delta'; c.prompt = '늘릴 길이 (줄이려면 -):'; return true; }
      if (/^t$/i.test(t)) { c.mode = 'total'; c.prompt = '전체 길이:'; return true; }
      if (c.mode && c.val == null && N(t) != null) { c.val = N(t); c.prompt = '바꿀 쪽 끝 가까이를 클릭 (Enter=끝):'; return true; }
    },
    point(c, p, raw) { if (c.val == null) return; const e = pick(raw); if (!e) return status('객체를 클릭하세요'); snapshot(); if (tryRun(() => G.lengthen(e, raw, c.mode === 'total' ? { total:c.val } : { delta:c.val }))) save(); else undoStack.pop(); }
  }),
  ALIGN: () => ({
    start(c) { selectStep(c, cc => { cc.prompt = '정렬 — 첫 원본 점:'; cc.ap = []; cc.def.point = (k, p) => {
      k.ap.push(p); const L = ['첫 대상 점:', '두번째 원본 점:', '두번째 대상 점:']; if (k.ap.length < 4) { k.prompt = L[k.ap.length - 1]; k.ref = p; return; }
      k.prompt = '크기도 맞출까요? (Y/N) <N>:'; k.ready = true;
    }; cc.def.text = (k, t) => { if (k.ready && /^[yn]$/i.test(t)) { alignDo(k, /y/i.test(t)); return true; } }; cc.def.enter = k => { if (k.ready) alignDo(k, false); else endCmd(); }; }, '정렬'); }
  }),
  MATCHPROP: () => ({
    start(c) { c.prompt = '특성 일치 — 원본 객체:'; },
    point(c, p, raw) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); if (!c.src) { c.src = e; c.prompt = `대상 객체 클릭 (원본 레이어: ${layerLabel(e.layer)}, Enter=끝):`; return; } snapshot(); G.matchProp(c.src, [e]); save(); }
  }),
  PEDIT: () => ({
    start(c) { c.prompt = '폴리선 편집 — 폴리선(또는 선) 클릭:'; },
    point(c, p, raw) {
      const e = pick(raw); if (!e) return status('객체를 클릭하세요');
      if (e.type === 'line') { snapshot(); Object.assign(e, { type:'polyline', pts:[[e.x1, e.y1], [e.x2, e.y2]], closed:false }); ['x1', 'y1', 'x2', 'y2'].forEach(k => delete e[k]); save(); }
      if (e.type !== 'polyline') return status('폴리선이 아닙니다');
      c.e = e; c.prompt = '닫기(C) / 열기(O) / 결합(J) / 끝(X):'; c.def.point = null;
    },
    text(c, t) {
      const u = t.toUpperCase(); if (!c.e) return;
      if (u === 'C' || u === 'O') { snapshot(); c.e.closed = u === 'C'; save(); draw(); return true; }
      if (u === 'J') { sel.clear(); sel.add(c.e.id); c.prompt = '이어 붙일 객체를 클릭해 선택한 뒤 Enter:'; c.selecting = true; c.def.enter = () => { snapshot(); const r = tryRun(() => G.join(withSel())); if (r) save(); else undoStack.pop(); endCmd(); }; return true; }
      if (u === 'X') { endCmd(); return true; }
    }
  }),
  DIVIDE: () => ({
    start(c) { c.prompt = '등분 — 객체 클릭:'; },
    point(c, p, raw) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); c.e = e; c.prompt = '몇 등분?:'; },
    text(c, t) { if (c.e && N(t) >= 2) { snapshot(); if (tryRun(() => G.divide(c.e, Math.round(N(t))))) save(); else undoStack.pop(); endCmd(); return true; } }
  }),
  MEASURE: () => ({
    start(c) { c.prompt = '길이 분할 — 객체 클릭:'; },
    point(c, p, raw) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); c.e = e; c.prompt = '간격 길이:'; },
    text(c, t) { if (c.e && N(t) > 0) { snapshot(); if (tryRun(() => G.divide(c.e, 0, N(t)))) save(); else undoStack.pop(); endCmd(); return true; } }
  }),
  // 치수 ---------------------------------------------------------------
  DIMANGULAR: () => ({
    start(c) { c.prompt = '각도 치수 — 첫 선 (Enter=꼭짓점 지정):'; },
    enter(c) { if (!c.l1 && !c.vtx) { c.vmode = true; c.prompt = '각의 꼭짓점:'; } else endCmd(); },
    point(c, p, raw) {
      if (c.vmode) {
        if (!c.vtx) { c.vtx = p; c.ref = p; c.prompt = '첫 변의 점:'; return; }
        if (!c.q1) { c.q1 = p; c.prompt = '두번째 변의 점:'; return; }
        if (!c.q2) { c.q2 = p; c.prompt = '치수 호 위치:'; return; }
        this.make(c, c.vtx, [angOf(c.vtx, c.q1)], [angOf(c.vtx, c.q2)], p); return;
      }
      const e = pick(raw);
      if (!c.l1) { if (!e || !['line', 'wall', 'window'].includes(e.type)) return status('선을 클릭하세요'); c.l1 = e; c.prompt = '두번째 선:'; return; }
      if (!c.l2) { if (!e || !['line', 'wall', 'window'].includes(e.type)) return status('선을 클릭하세요'); const v = lineX([c.l1.x1, c.l1.y1], [c.l1.x2, c.l1.y2], [e.x1, e.y1], [e.x2, e.y2]); if (!v) return status('평행한 선입니다'); c.l2 = e; c.vtx = v; c.prompt = '치수 호 위치:'; return; }
      const a1 = angOf([c.l1.x1, c.l1.y1], [c.l1.x2, c.l1.y2]), a2 = angOf([c.l2.x1, c.l2.y1], [c.l2.x2, c.l2.y2]);
      this.make(c, c.vtx, [a1, a1 + 180], [a2, a2 + 180], p);
    },
    pickAng(v, A1, A2, p) { const ph = angOf(v, p); let best = null; for (const x of A1) for (const y of A2) for (const [s, t] of [[x, y], [y, x]]) { const sw = norm360(t - s); if (sw > 1e-6 && onArc(ph, s, t) && (!best || sw < best[2])) best = [s, t, sw]; } return best; },
    make(c, v, A1, A2, p) { const b = this.pickAng(v, A1, A2, p); if (!b) return status('각을 정하지 못했습니다'); commit({ type:'dimang', layer:'dim', cx:v[0], cy:v[1], r:dist(v, p), a1:norm360(b[0]), a2:norm360(b[1]) }); endCmd(); },
    preview(c, cur) {
      if (c.vmode && c.q2) { const b = this.pickAng(c.vtx, [angOf(c.vtx, c.q1)], [angOf(c.vtx, c.q2)], cur); return b ? [{ type:'dimang', layer:'dim', cx:c.vtx[0], cy:c.vtx[1], r:dist(c.vtx, cur), a1:b[0], a2:b[1] }] : []; }
      if (c.l2) { const a1 = angOf([c.l1.x1, c.l1.y1], [c.l1.x2, c.l1.y2]), a2 = angOf([c.l2.x1, c.l2.y1], [c.l2.x2, c.l2.y2]), b = this.pickAng(c.vtx, [a1, a1 + 180], [a2, a2 + 180], cur); return b ? [{ type:'dimang', layer:'dim', cx:c.vtx[0], cy:c.vtx[1], r:dist(c.vtx, cur), a1:b[0], a2:b[1] }] : []; }
      return [];
    }
  }),
  DIMCONTINUE: () => dimChain(false),
  DIMBASELINE: () => dimChain(true),
  QLEADER: () => ({
    start(c) { c.prompt = '지시선 — 화살표 끝점:'; },
    point(c, p) { c.pts.push(p); c.prompt = '다음 점 (Enter=글자 입력):'; },
    enter(c) { if (c.pts.length < 2) return endCmd(); c.rawText = true; c.prompt = '지시선 글자 (Enter=글자 없이):'; c.def.enter = k => { commit({ type:'leader', layer:'dim', pts:k.pts.slice(), h:doc.dimTxt }); endCmd(); }; },
    text(c, t) { if (!c.rawText) return; commit({ type:'leader', layer:'dim', pts:c.pts.slice(), text:t, h:doc.dimTxt }); endCmd(); return true; },
    preview(c, cur) { return c.pts.length && !c.rawText ? [{ type:'leader', layer:'dim', pts:[...c.pts, cur], h:doc.dimTxt }] : []; }
  }),
  // 형식·보기·도구 ---------------------------------------------------------
  LAYER: () => ({ start() { endCmd(); openLayers(); } }),
  OSNAP: () => ({ start() { endCmd(); openOsnap(); } }),
  PURGE: () => ({ start() { endCmd(); const used = new Set(); const walk = list => list.forEach(e => { if (e.type === 'insert' && !used.has(e.name)) { used.add(e.name); walk(((doc.blocks || {})[e.name] || {}).ents || []); } }); walk(doc.ents); const rm = Object.keys(doc.blocks || {}).filter(n => !used.has(n)); rm.forEach(n => delete doc.blocks[n]); save(); status(rm.length ? `쓰지 않는 블록 ${rm.length}개 정리: ${rm.join(', ')}` : '정리할 블록이 없습니다'); } }),
  ZOOM: () => ({
    start(c) { c.prompt = '줌 — 전체(E) / 창(W) / 이전(P) <E>:'; },
    enter() { pushView(); endCmd(); zoomExtents(); },
    text(c, t) { const u = t.toUpperCase(); if (u === 'E') { pushView(); endCmd(); zoomExtents(); return true; } if (u === 'P') { endCmd(); popView(); return true; } if (u === 'W') { c.win = true; c.prompt = '창의 첫 구석:'; return true; } },
    point(c, p) {
      if (!c.win) { c.win = true; }
      if (!c.w1) { c.w1 = p; c.prompt = '반대쪽 구석:'; return; }
      pushView(); const r = cv.getBoundingClientRect(), w = Math.abs(p[0] - c.w1[0]) || 1, h = Math.abs(p[1] - c.w1[1]) || 1;
      view.s = Math.min(r.width / w, r.height / h) * 0.95; view.ox = r.width / 2 - (p[0] + c.w1[0]) / 2 * view.s; view.oy = r.height / 2 + (p[1] + c.w1[1]) / 2 * view.s; endCmd();
    },
    preview(c, cur) { return c.w1 ? [{ type:'rect', layer:'0', x:Math.min(c.w1[0], cur[0]), y:Math.min(c.w1[1], cur[1]), w:Math.abs(cur[0] - c.w1[0]), h:Math.abs(cur[1] - c.w1[1]), ghost:true }] : []; }
  }),
  PASTECLIP: () => ({
    start(c) { if (!clip) { endCmd(); status('복사한 것이 없습니다 (Ctrl+C)'); return; } c.prompt = '붙여넣을 위치 (복사한 객체들의 왼쪽 아래 기준):'; },
    point(c, p) { snapshot(); for (const e of clip.ents) { const n = clone(e); moveEnt(n, p[0] - clip.base[0], p[1] - clip.base[1]); delete n.floor; addEnt(n); } save(); endCmd(); status(`${clip.ents.length}개 붙여넣음`); },
    preview(c, cur) { return clip ? clip.ents.slice(0, 200).map(e => { const n = clone(e); moveEnt(n, cur[0] - clip.base[0], cur[1] - clip.base[1]); n.ghost = true; return n; }) : []; }
  }),
  DXFIN: () => ({ start() { endCmd(); openDxfIn(); } })
});
// ARRAY의 하위 단계(직사각형·원형)
function arrayText(k, t) {
  const u = t.toUpperCase();
  if (k.stage === 'kind') {
    if (u === 'P') {
      k.stage = 'pc'; k.prompt = '원형 배열 — 중심점:';
      k.def.point = (kk, p) => { kk.ctr = p; kk.stage = 'pn'; kk.prompt = '전체 개수 (원본 포함):'; kk.def.point = null; };
      k.def.enter = kk => { if (kk.stage === 'pa') polarDo(kk, 360); else endCmd(); };
      return true;
    }
    if (u === 'R') { arrayRectStart(k); return true; }
    return;
  }
  if (k.stage === 'rr' && N(t) >= 1) { k.rows = Math.round(N(t)); k.stage = 'rc'; k.prompt = '열 수 <1>:'; return true; }
  if (k.stage === 'rc' && N(t) >= 1) { k.cols = Math.round(N(t)); k.stage = 'rdy'; k.prompt = '행 간격 (위로 +):'; return true; }
  if (k.stage === 'rdy' && N(t) != null) { k.dy = N(t); k.stage = 'rdx'; k.prompt = '열 간격 (오른쪽으로 +):'; return true; }
  if (k.stage === 'rdx' && N(t) != null) { k.dx = N(t); snapshot(); const out = G.arrayRect(withSel(), k.rows || 1, k.cols || 1, k.dx, k.dy || 0); save(); endCmd(); status(`${out.length}개 배열`); return true; }
  if (k.stage === 'pn' && N(t) >= 2) { k.cnt = Math.round(N(t)); k.stage = 'pa'; k.prompt = '채울 각도 <360>:'; return true; }
  if (k.stage === 'pa' && N(t) != null) { polarDo(k, N(t)); return true; }
}
function arrayRectStart(k) {
  k.stage = 'rr'; k.prompt = '행 수 <1>:';
  k.def.enter = kk => {
    const def = { rr:['rows', 1, 'rc', '열 수 <1>:'], rc:['cols', 1, 'rdy', '행 간격 (위로 +):'] }[kk.stage];
    if (def) { kk[def[0]] = def[1]; kk.stage = def[2]; kk.prompt = def[3]; return; }
    endCmd();
  };
}
function polarDo(k, ang) { snapshot(); const out = G.arrayPolar(withSel(), k.ctr, k.cnt, ang, true); save(); endCmd(); status(`${out.length}개 원형 배열`); }
function alignDo(k, scaleIt) {
  const [s1, d1, s2, d2] = k.ap, th = angOf(d1, d2) - angOf(s1, s2), sc = scaleIt ? dist(d1, d2) / (dist(s1, s2) || 1) : 1;
  const f = p => { const v = mulv(sub(p, s1), sc), c = Math.cos(th * D2R), s = Math.sin(th * D2R); return [d1[0] + v[0] * c - v[1] * s, d1[1] + v[0] * s + v[1] * c]; };
  snapshot(); for (const e of withSel()) xformEnt(e, f, { rot:th, k:sc }); save(); endCmd(); status('정렬했습니다');
}
function dimChain(baseline) {
  return {
    start(c) {
      c.last = [...doc.ents].reverse().find(e => e.type === 'dim' && visible(e));
      if (!c.last) { endCmd(); status('이어 그릴 선형 치수가 없습니다. 먼저 DLI로 하나 그리세요'); return; }
      c.n = 0; c.prompt = `${baseline ? '기준선' : '연속'} 치수 — 다음 점 (Enter=끝):`;
    },
    point(c, p) {
      const L = c.last, sp = doc.dimTxt * 3, sgn = Math.sign(L.off || 1);
      const from = baseline ? [L.x1, L.y1] : [L.x2, L.y2];
      const d = { type:'dim', layer:'dim', dir:L.dir || 'a', x1:from[0], y1:from[1], x2:p[0], y2:p[1] };
      if (d.dir === 'h') { const yl = L.y1 + L.off + (baseline ? sgn * sp * (c.n + 1) : 0); d.off = yl - d.y1; }
      else if (d.dir === 'v') { const xl = L.x1 + L.off + (baseline ? sgn * sp * (c.n + 1) : 0); d.off = xl - d.x1; }
      else d.off = (L.off || 0) + (baseline ? sgn * sp * (c.n + 1) : 0);
      commit(d); c.n++; if (!baseline) c.last = d;
    },
    preview(c, cur) { return []; }
  };
}
let views = [];
function pushView() { views.push({ ...view }); if (views.length > 20) views.shift(); }
function popView() { const v = views.pop(); if (!v) return status('이전 화면이 없습니다'); Object.assign(view, v); draw(); }

// 여러 줄 문자 입력 창
function openMtext(at) {
  let dlg = $('#dlgMtext');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgMtext';
    dlg.innerHTML = '<h2>여러 줄 문자</h2><textarea id="mtBody" style="height:120px" placeholder="여러 줄로 입력하세요"></textarea><label for="mtH">글자 높이</label><input type="text" id="mtH"><div class="btns"><button id="mtCancel">취소</button><button id="mtOk" class="primary">넣기</button></div>';
    document.body.appendChild(dlg); $('#mtCancel').onclick = () => dlg.close();
  }
  $('#mtBody').value = ''; $('#mtH').value = fmt(doc.dimTxt);
  $('#mtOk').onclick = () => { const t = $('#mtBody').value.replace(/\s+$/, ''); if (t) commit({ type:'mtext', layer:curLayer, x:at[0], y:at[1], h:parseFloat($('#mtH').value) || doc.dimTxt, text:t }); dlg.close(); draw(); };
  dlg.showModal(); setTimeout(() => $('#mtBody').focus(), 0);
}

/* ---------- 클립보드 (Ctrl+C / Ctrl+X / Ctrl+V) ---------- */
let clip = store.get('vc.clip', null);
document.addEventListener('keydown', ev => {
  if (document.querySelector('dialog[open]') || typing() || !(ev.ctrlKey || ev.metaKey)) return;
  const k = ev.key.toLowerCase();
  if ((k === 'c' || k === 'x') && sel.size) {
    ev.preventDefault();
    const ents = withSel().map(e => { const n = clone(e); delete n.id; return n; }), b = bounds(ents);
    clip = { base:[b[0], b[1]], ents }; store.set('vc.clip', clip);
    if (k === 'x') { snapshot(); doc.ents = doc.ents.filter(e => !sel.has(e.id)); sel.clear(); save(); draw(); }
    status(`${ents.length}개 ${k === 'x' ? '잘라냄' : '복사함'}`);
  } else if (k === 'v') { ev.preventDefault(); startCmd('PASTECLIP'); }
});

/* ---------- DXF 열기 ---------- */
const ACI_RGB = { 1:'#ff0000', 2:'#ffff00', 3:'#00ff00', 4:'#00ffff', 5:'#0000ff', 6:'#ff00ff', 7:'#e8e8e8', 8:'#808080', 9:'#c0c0c0' };
function aciHex(i) {
  i = Math.abs(i | 0); if (ACI_RGB[i]) return ACI_RGB[i]; if (i < 10 || i > 249) return '#e8e8e8';
  const h = Math.floor((i - 10) / 10) * 15, v = (i % 10), l = [50, 75, 40, 65, 30, 55, 20, 45, 15, 35][v] / 100, s = v % 2 ? 0.5 : 1;
  const f = n => { const k = (n + h / 30) % 12, a = s * Math.min(l, 1 - l); return Math.round(255 * (l - a * Math.max(-1, Math.min(k - 3, 9 - k, 1)))).toString(16).padStart(2, '0'); };
  return '#' + f(0) + f(8) + f(4);
}
function decodeDxfText(s) {
  return String(s).replace(/%%[cC]/g, 'Ø').replace(/%%[dD]/g, '°').replace(/%%[pP]/g, '±').replace(/\\U\+([0-9A-Fa-f]{4})/g, (m, h) => String.fromCharCode(parseInt(h, 16)));
}
function mtextPlain(s) {
  return decodeDxfText(s).replace(/\\P/g, '\n').replace(/\\[ACFHQTWfhqtw][^;]*;/g, '').replace(/\\[LlOoKk]/g, '').replace(/\\~/g, ' ').replace(/[{}]/g, '').replace(/\\\\/g, '\\');
}
function bulgePts(a, b, bulge) {
  if (!bulge) return [b];
  const th = 4 * Math.atan(bulge), d = dist(a, b), r = d / (2 * Math.sin(th / 2)), m = mulv(addv(a, b), 0.5), u = unit(sub(b, a)), h = r * Math.cos(th / 2);
  const c = addv(m, mulv([-u[1], u[0]], h)), a0 = angOf(c, a), sw = th / D2R, n = Math.max(2, Math.ceil(Math.abs(sw) / 10)), out = [];
  for (let i = 1; i <= n; i++) out.push(polar(c, Math.abs(r), a0 + sw * i / n));
  return out;
}
function parseDxf(text) {
  const L = text.split(/\r\n|\r|\n/), pairs = [];
  for (let i = 0; i + 1 < L.length; i += 2) pairs.push([parseInt(L[i].trim(), 10), L[i + 1]]);
  const res = { header:{}, layers:{}, blocks:{}, ents:[], skipped:{} };
  let i = 0;
  const readEnt = () => { const type = pairs[i][1].trim(), d = []; i++; while (i < pairs.length && pairs[i][0] !== 0) { d.push(pairs[i]); i++; } return { type, d }; };
  const collect = (until, out) => {
    while (i < pairs.length) {
      if (pairs[i][0] !== 0) { i++; continue; }
      const t = pairs[i][1].trim(); if (until.includes(t)) return t;
      const e = readEnt();
      if (e.type === 'POLYLINE') { e.verts = []; while (i < pairs.length && pairs[i][0] === 0 && pairs[i][1].trim() === 'VERTEX') e.verts.push(readEnt()); if (i < pairs.length && pairs[i][1].trim() === 'SEQEND') readEnt(); }
      out.push(e);
    }
    return null;
  };
  while (i < pairs.length) {
    if (pairs[i][0] === 0 && pairs[i][1].trim() === 'SECTION') {
      const name = (pairs[i + 1] || [])[1] && pairs[i + 1][1].trim(); i += 2;
      if (name === 'HEADER') { let v = null; while (i < pairs.length && !(pairs[i][0] === 0 && pairs[i][1].trim() === 'ENDSEC')) { if (pairs[i][0] === 9) v = pairs[i][1].trim(); else if (v && res.header[v] == null) res.header[v] = pairs[i][1].trim(); i++; } }
      else if (name === 'TABLES') {
        while (i < pairs.length && !(pairs[i][0] === 0 && pairs[i][1].trim() === 'ENDSEC')) {
          if (pairs[i][0] === 0 && pairs[i][1].trim() === 'LAYER') { const e = readEnt(), g = c => (e.d.find(x => x[0] === c) || [])[1]; const nm = (g(2) || '').trim(); if (nm) res.layers[nm] = { color:parseInt(g(62) || '7', 10), lt:(g(6) || '').trim() }; }
          else i++;
        }
      }
      else if (name === 'BLOCKS') {
        while (i < pairs.length && !(pairs[i][0] === 0 && pairs[i][1].trim() === 'ENDSEC')) {
          if (pairs[i][0] === 0 && pairs[i][1].trim() === 'BLOCK') { const b = readEnt(), g = c => (b.d.find(x => x[0] === c) || [])[1]; const ents = []; collect(['ENDBLK'], ents); if (i < pairs.length) readEnt(); res.blocks[(g(2) || '').trim()] = { base:[+g(10) || 0, +g(20) || 0], raw:ents }; }
          else i++;
        }
      }
      else if (name === 'ENTITIES') { collect(['ENDSEC'], res.ents); }
      continue;
    }
    i++;
  }
  return res;
}
function convDxfEnt(r, k, layerKey, skipped) {
  const d = r.d, g = c => { const x = d.find(p => p[0] === c); return x ? x[1] : undefined; }, n = c => parseFloat(g(c)) || 0, P = (cx, cy) => [n(cx) * k, n(cy) * k];
  const lay = layerKey((g(8) || '0').trim()), base = { layer:lay };
  switch (r.type) {
    case 'LINE': return { ...base, type:'line', x1:n(10) * k, y1:n(20) * k, x2:n(11) * k, y2:n(21) * k };
    case 'CIRCLE': return { ...base, type:'circle', cx:n(10) * k, cy:n(20) * k, r:n(40) * k };
    case 'ARC': return { ...base, type:'arc', cx:n(10) * k, cy:n(20) * k, r:n(40) * k, a1:n(50), a2:n(51) };
    case 'POINT': return { ...base, type:'point', x:n(10) * k, y:n(20) * k };
    case 'LWPOLYLINE': {
      const vs = []; let cur = null;
      for (const [c, v] of d) { if (c === 10) { cur = { p:[parseFloat(v) * k, 0], b:0 }; vs.push(cur); } else if (c === 20 && cur) cur.p[1] = parseFloat(v) * k; else if (c === 42 && cur) cur.b = parseFloat(v) || 0; }
      const closed = (parseInt(g(70) || '0', 10) & 1) === 1; if (vs.length < 2) return null;
      const pts = [vs[0].p]; for (let j = 0; j < vs.length - 1 + (closed ? 1 : 0); j++) pts.push(...bulgePts(vs[j].p, vs[(j + 1) % vs.length].p, vs[j].b));
      if (closed) pts.pop();
      return { ...base, type:'polyline', pts, closed };
    }
    case 'POLYLINE': {
      const fl = parseInt(g(70) || '0', 10); if (fl & (16 | 64)) { skipped['3D 메시'] = (skipped['3D 메시'] || 0) + 1; return null; }
      const vs = (r.verts || []).map(v => { const gv = c => parseFloat((v.d.find(p => p[0] === c) || [])[1]) || 0; return { p:[gv(10) * k, gv(20) * k], b:gv(42) }; });
      if (vs.length < 2) return null; const closed = (fl & 1) === 1;
      const pts = [vs[0].p]; for (let j = 0; j < vs.length - 1 + (closed ? 1 : 0); j++) pts.push(...bulgePts(vs[j].p, vs[(j + 1) % vs.length].p, vs[j].b));
      if (closed) pts.pop();
      return { ...base, type:'polyline', pts, closed };
    }
    case 'TEXT': case 'ATTRIB': {
      const al = parseInt(g(72) || '0', 10) || parseInt(g(73) || '0', 10), p = al && g(11) != null ? P(11, 21) : P(10, 20), t = decodeDxfText(g(1) || ''); if (!t.trim()) return null;
      const h = n(40) * k || doc.dimTxt; return { ...base, type:'text', x:p[0] - (al && (parseInt(g(72) || '0', 10) === 1 || parseInt(g(72) || '0', 10) === 4) ? textW(t, h) / 2 : 0), y:p[1], h, rot:n(50), text:t };
    }
    case 'MTEXT': {
      const t = mtextPlain(d.filter(p => p[0] === 3).map(p => p[1]).join('') + (g(1) || '')); if (!t.trim()) return null;
      const rot = g(50) != null ? n(50) : (g(11) != null ? Math.atan2(n(21), n(11)) / D2R : 0);
      return { ...base, type:'mtext', x:n(10) * k, y:n(20) * k, h:n(40) * k || doc.dimTxt, rot, text:t };
    }
    case 'ELLIPSE': {
      const c = P(10, 20), mx = n(11) * k, my = n(21) * k, rx = Math.hypot(mx, my), ry = rx * (n(40) || 1), p1 = n(41), p2 = g(42) != null ? n(42) : Math.PI * 2;
      const e = { ...base, type:'ellipse', cx:c[0], cy:c[1], rx, ry, rot:Math.atan2(my, mx) / D2R };
      if (Math.abs(p2 - p1 - Math.PI * 2) > 1e-6 && Math.abs(p2 - p1) > 1e-6) { e.a1 = p1 / D2R; e.a2 = p2 / D2R; } return e;
    }
    case 'SPLINE': {
      const fit = [], ctl = []; let cur = null;
      for (const [c, v] of d) { if (c === 11) { cur = [parseFloat(v) * k, 0]; fit.push(cur); } else if (c === 21 && cur) cur[1] = parseFloat(v) * k; }
      cur = null; for (const [c, v] of d) { if (c === 10) { cur = [parseFloat(v) * k, 0]; ctl.push(cur); } else if (c === 20 && cur) cur[1] = parseFloat(v) * k; }
      const pts = fit.length >= 2 ? fit : ctl; if (pts.length < 2) return null;
      return { ...base, type:'spline', pts, closed:(parseInt(g(70) || '0', 10) & 1) === 1 };
    }
    case 'INSERT': case 'DIMENSION': {
      const name = (g(2) || '').trim(); if (!name) return null;
      if (r.type === 'DIMENSION') return { ...base, type:'insert', name, x:0, y:0, sx:1, sy:1, rot:0 };
      const sx = g(41) != null ? n(41) : 1, sy = g(42) != null ? n(42) : sx; const p = P(10, 20);
      return { ...base, type:'insert', name, x:p[0], y:p[1], sx, sy, rot:n(50) };
    }
    case 'SOLID': case 'TRACE': { const q = [P(10, 20), P(11, 21), P(13, 23), P(12, 22)]; return { ...base, type:'hatch', pts:dist(q[2], q[3]) < 1e-9 ? q.slice(0, 3) : q, pat:'SOLID', sc:1 }; }
    case 'HATCH': {
      const loops = []; let j = d.findIndex(p => p[0] === 91); const nLoops = j >= 0 ? parseInt(d[j][1], 10) : 0; j++;
      for (let li = 0; li < nLoops && j < d.length; li++) {
        while (j < d.length && d[j][0] !== 92) j++; if (j >= d.length) break;
        const flag = parseInt(d[j][1], 10); j++; const pts = [];
        if (flag & 2) { // 폴리선 경계
          let hasB = 0, nv = 0; while (j < d.length && d[j][0] !== 93) { if (d[j][0] === 72) hasB = parseInt(d[j][1], 10); j++; } nv = parseInt(d[j][1], 10); j++;
          const vs = []; for (let v = 0; v < nv && j < d.length; v++) { const x = parseFloat(d[j][1]) * k; const y = parseFloat(d[j + 1][1]) * k; j += 2; let b = 0; if (hasB && d[j] && d[j][0] === 42) { b = parseFloat(d[j][1]) || 0; j++; } vs.push({ p:[x, y], b }); }
          if (vs.length) { pts.push(vs[0].p); for (let v = 0; v < vs.length; v++) pts.push(...bulgePts(vs[v].p, vs[(v + 1) % vs.length].p, vs[v].b)); pts.pop(); }
        } else { // 모서리 경계(선·호)
          while (j < d.length && d[j][0] !== 93) j++; const ne = parseInt(d[j][1], 10); j++;
          for (let ei = 0; ei < ne && j < d.length; ei++) {
            const et = parseInt(d[j][1], 10); j++; const val = c => { while (j < d.length && d[j][0] !== c) j++; const v = parseFloat(d[j][1]); j++; return v; };
            if (et === 1) { const a = [val(10) * k, val(20) * k], b = [val(11) * k, val(21) * k]; if (!pts.length) pts.push(a); pts.push(b); }
            else if (et === 2) { const c = [val(10) * k, val(20) * k], rr = val(40) * k, a1 = val(50), a2 = val(51), ccw = val(73); const sw = ccw ? norm360(a2 - a1) : -norm360(a1 - a2), s0 = ccw ? a1 : -a1; for (let q = 0; q <= 12; q++) pts.push(polar(c, rr, (ccw ? s0 : a1) + sw * q / 12 * (ccw ? 1 : 1))); }
            else { skipped['해치 곡선 경계'] = (skipped['해치 곡선 경계'] || 0) + 1; }
          }
        }
        if (pts.length >= 3) loops.push(pts);
      }
      if (!loops.length) { skipped['해치'] = (skipped['해치'] || 0) + 1; return null; }
      const pn = (g(2) || '').trim().toUpperCase(), solid = parseInt(g(70) || '0', 10) === 1 || pn === 'SOLID';
      const e = { ...base, type:'hatch', pts:loops[0], pat:solid ? 'SOLID' : (PAT[pn] ? pn : 'ANSI31'), sc:(n(41) || 1) * k, ang:n(52) };
      if (loops.length > 1) e.holes = loops.slice(1); return e;
    }
    case 'LEADER': { const pts = []; let cur = null; for (const [c, v] of d) { if (c === 10) { cur = [parseFloat(v) * k, 0]; pts.push(cur); } else if (c === 20 && cur) cur[1] = parseFloat(v) * k; } return pts.length >= 2 ? { ...base, type:'leader', pts, h:doc.dimTxt } : null; }
    case 'ATTDEF': case 'VIEWPORT': case 'SEQEND': return null;
  }
  skipped[r.type] = (skipped[r.type] || 0) + 1; return null;
}
const UNIT_MM = { 0:1, 1:25.4, 2:304.8, 4:1, 5:10, 6:1000 };
function importDxf(text, mode) {
  const R = parseDxf(text), k = UNIT_MM[parseInt(R.header.$INSUNITS || '4', 10)] || 1;
  const layerKey = name => {
    if (name === '0' || !name) return '0';
    const key = 'dx_' + name.replace(/[^\w가-힣-]/g, '_').slice(0, 40);
    if (!LAYERS[key]) {
      const L = R.layers[name] || { color:7, lt:'' }, dash = /HIDDEN|DASH|CENTER|PHANTOM|DOT/i.test(L.lt) ? [10, 5] : [];
      doc.userLayers = doc.userLayers || {}; doc.userLayers[key] = { name, color:aciHex(L.color), dash };
      ensureLayer(key, name, aciHex(L.color), dash); DXF_BASE[key][1] = Math.abs(L.color) || 7;
      if (L.color < 0) { doc.layerProps = doc.layerProps || {}; doc.layerProps[key] = { off:true }; }
    }
    return key;
  };
  if (mode === 'new') { doc.ents = []; doc.blocks = {}; sel.clear(); }
  doc.blocks = doc.blocks || {};
  const skipped = {};
  for (const [name, b] of Object.entries(R.blocks)) {
    if (/^\*(MODEL|PAPER)_SPACE/i.test(name)) continue;
    doc.blocks[name] = { base:[b.base[0] * k, b.base[1] * k], ents:b.raw.map(r => convDxfEnt(r, k, layerKey, skipped)).filter(Boolean) };
  }
  let n = 0; const before = doc.ents.length;
  for (const r of R.ents) { const e = convDxfEnt(r, k, layerKey, skipped); if (e) { addEnt(e); n++; } }
  if (mode === 'add' && before) { const old = bounds(doc.ents.slice(0, before)), nb = bounds(doc.ents.slice(before)); if (old && nb && nb[0] < old[2] && nb[2] > old[0] && nb[1] < old[3] && nb[3] > old[1]) doc.ents.slice(before).forEach(e => moveEnt(e, old[2] + (old[2] - old[0]) * 0.1 - nb[0], 0)); }
  return { n, blocks:Object.keys(R.blocks).length, layers:Object.keys(R.layers).length, skipped, ver:R.header.$ACADVER || '?', unit:k };
}
function openDxfIn() {
  let dlg = $('#dlgDxf');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgDxf';
    dlg.innerHTML = '<h2>DXF 열기</h2><div class="hint">오토캐드 등에서 DXF로 저장한 도면을 엽니다. 선·폴리선·원·호·글자·여러 줄 문자·타원·스플라인·블록·치수(모양 그대로)·해치·레이어 색을 가져옵니다. DWG는 오토캐드에서 「다른 이름으로 저장 → DXF」로 바꿔 주세요.</div>' +
      '<label for="dxfFile">DXF 파일</label><input type="file" id="dxfFile" accept=".dxf"><div class="err" id="dxfErr"></div>' +
      '<div class="btns"><button id="dxfCancel">닫기</button><button id="dxfAdd">지금 도면에 추가</button><button id="dxfNew" class="primary">새 도면으로 열기</button></div>';
    document.body.appendChild(dlg); $('#dxfCancel').onclick = () => dlg.close();
    const go = async mode => {
      const f = $('#dxfFile').files[0]; if (!f) { $('#dxfErr').textContent = 'DXF 파일을 고르세요'; return; }
      const buf = new Uint8Array(await f.arrayBuffer()), head = new TextDecoder('latin1').decode(buf.slice(0, 4000));
      const ver = (head.match(/\$ACADVER\s*\r?\n\s*1\s*\r?\n\s*AC(\d+)/) || [])[1];
      let text; try { text = new TextDecoder(ver && +ver >= 1021 ? 'utf-8' : 'euc-kr').decode(buf); } catch { text = new TextDecoder('utf-8').decode(buf); }
      snapshot();
      try {
        const r = importDxf(text, mode); save(); dlg.close(); zoomExtents();
        const sk = Object.entries(r.skipped).map(([t, c]) => `${t} ${c}`).join(', ');
        info(`DXF 열기: ${f.name} · 요소 ${r.n}개 · 블록 ${r.blocks} · 레이어 ${r.layers}${r.unit !== 1 ? ` · 단위 ×${r.unit}→mm` : ''}${sk ? `\n가져오지 못한 것: ${sk}` : ''}`);
      } catch (err) { undoStack.pop(); $('#dxfErr').textContent = 'DXF를 읽지 못했습니다: ' + err.message; }
    };
    $('#dxfNew').onclick = () => go('new'); $('#dxfAdd').onclick = () => go('add');
  }
  $('#dxfErr').textContent = ''; dlg.showModal();
}
window.importDxfText = importDxf; // 시험용

/* ---------- AI가 쓰는 명령 실행 (apply_drawing.ops) ---------- */
window.runOps = (ops, refs, opts = {}) => {
  const R = { done:0, skipped:0, errors:[] }, fresh = new Set(Object.values(refs));
  const idOf = v => refs[String(v)] || String(v);
  const E = v => (Array.isArray(v) ? v : v == null ? [] : [v]).map(idOf).map(findEnt).filter(Boolean);
  const one = v => { const e = E(v)[0]; if (!e) throw new Error(`없는 객체: ${v}`); return e; };
  const pt = (v, name) => { const p = P2(v); if (!p) throw new Error(`${name} 좌표가 필요합니다`); return p; };
  for (const op of ops || []) {
    const name = String(op && op.op || '').toUpperCase();
    try {
      const touched = [...E(op.ids), ...E(op.id), ...E(op.id1), ...E(op.id2), ...E(op.src)];
      if (opts.addOnly && touched.some(e => !fresh.has(e.id))) { R.skipped++; continue; }
      switch (name) {
        case 'ERASE': { const s = new Set(E(op.ids).map(e => e.id)); doc.ents = doc.ents.filter(e => !s.has(e.id)); break; }
        case 'MOVE': E(op.ids).forEach(e => moveEnt(e, +op.dx || 0, +op.dy || 0)); break;
        case 'COPY': { const n = Math.max(1, Math.round(+op.n || 1)); for (let i = 1; i <= n; i++) for (const e of E(op.ids)) { const c = clone(e); delete c.id; moveEnt(c, (+op.dx || 0) * i, (+op.dy || 0) * i); addEnt(c); } break; }
        case 'ROTATE': { const b = pt(op.base, 'base'), a = +op.ang || 0; for (const e of E(op.ids)) { const t = op.copy ? clone(e) : e; if (op.copy) delete t.id; xformEnt(t, rotF(b, a), { rot:a }); if (op.copy) addEnt(t); } break; }
        case 'MIRROR': { const p1 = pt(op.p1, 'p1'), p2 = pt(op.p2, 'p2'), a = angOf(p1, p2), keep = op.keep !== false; for (const e of E(op.ids)) { const t = keep ? clone(e) : e; if (keep) delete t.id; xformEnt(t, mirF(p1, a), { mirror:a }); if (keep) addEnt(t); } break; }
        case 'SCALE': { const b = pt(op.base, 'base'), k = +op.k; if (!(k > 0)) throw new Error('배율 k가 필요합니다'); E(op.ids).forEach(e => xformEnt(e, sclF(b, k), { k })); break; }
        case 'OFFSET': { const d = +op.d; if (!(d > 0)) throw new Error('거리 d가 필요합니다'); for (const e of E(op.ids || op.id)) { const n = offsetEnt(e, d, pt(op.side, 'side')); if (!n) throw new Error(`${TYPE_KO[e.type] || e.type} 간격띄우기 불가`); addEnt(n); } break; }
        case 'TRIM': G.trim(one(op.id), op.cutters ? E(op.cutters) : live(), pt(op.pick, 'pick')); break;
        case 'EXTEND': G.extend(one(op.id), op.bounds ? E(op.bounds) : live(), pt(op.pick, 'pick')); break;
        case 'FILLET': if (op.id && !op.id1) G.filletPoly(one(op.id), +op.r || 0); else G.corner(one(op.id1), one(op.id2), +op.r || 0, P2(op.pick1), P2(op.pick2)); break;
        case 'CHAMFER': if (op.id && !op.id1) G.filletPoly(one(op.id), 0, +op.d1 || 0); else G.corner(one(op.id1), one(op.id2), 0, P2(op.pick1), P2(op.pick2), [+op.d1 || 0, op.d2 != null ? +op.d2 : +op.d1 || 0]); break;
        case 'BREAK': G.breakAt(one(op.id), pt(op.p1, 'p1'), P2(op.p2)); break;
        case 'JOIN': G.join(E(op.ids)); break;
        case 'EXPLODE': E(op.ids).forEach(e => G.explode(e)); break;
        case 'ARRAYRECT': G.arrayRect(E(op.ids), Math.max(1, Math.round(+op.rows || 1)), Math.max(1, Math.round(+op.cols || 1)), +op.dx || 0, +op.dy || 0); break;
        case 'ARRAYPOLAR': G.arrayPolar(E(op.ids), pt(op.center, 'center'), Math.max(2, Math.round(+op.count || 2)), op.angle != null ? +op.angle : 360, op.rotate !== false); break;
        case 'STRETCH': { const w = op.window; if (!Array.isArray(w) || w.length < 4) throw new Error('window [x0,y0,x1,y1]가 필요합니다'); G.stretch(w.map(Number), +op.dx || 0, +op.dy || 0); break; }
        case 'LENGTHEN': { const e = one(op.id), C = curveOf(e), endPt = C ? C.at(op.end === 'start' ? 0 : C.L) : [e.x2, e.y2]; G.lengthen(e, endPt, op.total != null ? { total:+op.total } : { delta:+op.delta || 0 }); break; }
        case 'HATCH': {
          let pts = op.id ? closedLoop(one(op.id)) : (op.pts || []).map(P2).filter(Boolean);
          if (!pts || pts.length < 3) throw new Error('닫힌 경계가 필요합니다');
          addEnt({ type:'hatch', layer:'hatch', pts:pts.map(q => q.slice()), pat:['SOLID', 'ANSI31', 'ANSI37', 'NET'].includes(String(op.pattern || '').toUpperCase()) ? String(op.pattern).toUpperCase() : 'ANSI31', sc:+op.scale > 0 ? +op.scale : autoHatchScale(pts), ang:+op.ang || 0 });
          break;
        }
        case 'BLOCK': { const ins = G.makeBlock(String(op.name || ''), pt(op.base, 'base'), E(op.ids)); if (op.ref) refs[String(op.ref)] = ins.id; break; }
        case 'INSERT': { const b = (doc.blocks || {})[String(op.name)]; if (!b) throw new Error(`없는 블록: ${op.name}`); const ins = { type:'insert', layer:'0', name:String(op.name), x:+op.x || 0, y:+op.y || 0, sx:+op.sx || +op.sc || 1, sy:+op.sy || +op.sx || +op.sc || 1, rot:+op.rot || 0 }; addEnt(ins); if (op.ref) refs[String(op.ref)] = ins.id; break; }
        case 'DIVIDE': G.divide(one(op.id), Math.max(2, Math.round(+op.n || 2))); break;
        case 'MEASURE': { if (!(+op.d > 0)) throw new Error('간격 d가 필요합니다'); G.divide(one(op.id), 0, +op.d); break; }
        case 'MATCHPROP': G.matchProp(one(op.src), E(op.ids)); break;
        default: throw new Error('모르는 명령');
      }
      R.done++;
    } catch (err) { R.errors.push(`${name}: ${err.message}`); }
  }
  return R;
};
const OPS = ['ERASE', 'MOVE', 'COPY', 'ROTATE', 'MIRROR', 'SCALE', 'OFFSET', 'TRIM', 'EXTEND', 'FILLET', 'CHAMFER', 'BREAK', 'JOIN', 'EXPLODE', 'ARRAYRECT', 'ARRAYPOLAR', 'STRETCH', 'LENGTHEN', 'HATCH', 'BLOCK', 'INSERT', 'DIVIDE', 'MEASURE', 'MATCHPROP'];
(() => { // AI 도구 정의에 새 도형·명령 추가
  const AP = TOOL.input_schema.properties, IT = AP.add.items.properties, num = { type:'number' };
  EXT.forEach(t => { if (!IT.type.enum.includes(t)) IT.type.enum.push(t); });
  for (const k of ['rx', 'ry', 'ri', 'ro', 'sc', 'sx', 'sy']) IT[k] = num;
  IT.holes = { type:'array', items:{ type:'array', items:{ type:'array', items:num } } };
  IT.pat = { type:'string', enum:['SOLID', 'ANSI31', 'ANSI37', 'NET'] };
  IT.ref = { type:'string', description:'이 요소를 같은 응답의 ops에서 가리킬 이름' };
  AP.ops = { type:'array', description:'실제 캐드 명령을 순서대로 실행(add 다음에 실행)', items:{ type:'object', properties:{ op:{ type:'string', enum:OPS }, id:{ type:'string' }, ids:{ type:'array', items:{ type:'string' } } }, required:['op'] } };
})();
window.SYS_EXTRA = `

[추가 도형 — add에 쓸 수 있음]
- ellipse: cx,cy,rx(장축 반지름),ry(단축 반지름),rot(°) / 부분 타원은 a1,a2(매개변수 각도°)
- spline: pts(지나는 점들), closed
- xline: x,y,ang(°) 무한 보조선 / ray: x,y,ang 광선
- point: x,y
- donut: cx,cy,ri(안쪽 반지름),ro(바깥 반지름)
- hatch: pts(닫힌 경계), holes(구멍 경계 배열), pat("SOLID"|"ANSI31"|"ANSI37"|"NET"), sc(패턴 간격 배율, 생략하면 자동), ang(°)
- mtext: x,y(왼쪽 위),h,text(줄바꿈은 \\n),rot
- leader: pts(첫 점이 화살표 끝), text, h
- dimang: cx,cy(각의 꼭짓점), r(치수 호 반지름), a1,a2(반시계로 a1→a2를 재는 각도 치수)
- insert: name(blocks에 있는 블록 이름), x,y, sx,sy(축척), rot
add 항목에 "ref":"이름"을 붙이면 같은 응답의 ops에서 그 이름으로 가리킬 수 있습니다.

[ops — 실제 캐드 명령을 순서대로 실행] id 자리에는 기존 id 또는 ref 이름을 씁니다.
- ERASE{ids} MOVE{ids,dx,dy} COPY{ids,dx,dy,n} ROTATE{ids,base:[x,y],ang,copy} MIRROR{ids,p1,p2,keep(기본 true=원본 남김)} SCALE{ids,base,k}
- OFFSET{id,d,side:[x,y](띄울 쪽의 점)} TRIM{id,pick:[x,y](지울 부분 위의 점),cutters?} EXTEND{id,pick(늘릴 끝 근처),bounds?}
- FILLET{id1,id2,r} 두 선 모깎기(r=0이면 모서리 맞춤) / FILLET{id(폴리선),r} 모든 꼭짓점 / CHAMFER{id1,id2,d1,d2}
- BREAK{id,p1,p2?} JOIN{ids} EXPLODE{ids} ARRAYRECT{ids,rows,cols,dx,dy} ARRAYPOLAR{ids,center,count,angle(기본 360),rotate}
- STRETCH{window:[x0,y0,x1,y1],dx,dy} LENGTHEN{id,total 또는 delta,end:"start"|"end"} HATCH{id 또는 pts,pattern,scale,ang}
- BLOCK{name,ids,base,ref?} INSERT{name,x,y,sx,rot,ref?} DIVIDE{id,n} MEASURE{id,d} MATCHPROP{src,ids}
같은 모양이 반복되거나 대칭인 도면(볼트 구멍, 같은 창 여러 개, 기둥 열, 좌우 대칭 평면 등)은 하나만 add로 그리고 ARRAYRECT·ARRAYPOLAR·MIRROR·COPY로 만드는 것을 우선합니다. 모서리 라운드·모따기는 FILLET·CHAMFER, 교차하는 선의 정리는 TRIM·EXTEND를 씁니다.`;

/* ---------- 메뉴·도구막대·단축키 ---------- */
const NEW_ALIASES = { XL:'XLINE', POL:'POLYGON', EL:'ELLIPSE', SPL:'SPLINE', PO:'POINT', DO:'DONUT', H:'HATCH', BH:'HATCH', MT:'MTEXT', B:'BLOCK', I:'INSERT', AR:'ARRAY',
  TR:'TRIM', EX:'EXTEND', F:'FILLET', CHA:'CHAMFER', BR:'BREAK', J:'JOIN', X:'EXPLODE', S:'STRETCH', LEN:'LENGTHEN', AL:'ALIGN', MA:'MATCHPROP', PE:'PEDIT',
  DIV:'DIVIDE', ME:'MEASURE', DAN:'DIMANGULAR', DCO:'DIMCONTINUE', DBA:'DIMBASELINE', LE:'QLEADER', LEAD:'QLEADER', LA:'LAYER', OS:'OSNAP', D:'DIMTXT', PU:'PURGE', DXFIN:'DXFIN' };
Object.assign(DEFAULT_ALIASES, NEW_ALIASES);
for (const [k, v] of Object.entries(NEW_ALIASES)) if (!(k in settings.aliases)) settings.aliases[k] = v;
Object.assign(CMD_DESC, {
  XLINE:'무한선 (H/V/A)', RAY:'광선', POLYGON:'다각형 (변 수→중심→I/C→반지름)', ELLIPSE:'타원 (C=중심)', SPLINE:'스플라인', POINT:'점', DONUT:'도넛', HATCH:'해치 (패턴→배율→안쪽 클릭)', REVCLOUD:'구름형 수정기호',
  MTEXT:'여러 줄 문자', BLOCK:'블록 만들기', INSERT:'블록 삽입', TRIM:'자르기', EXTEND:'연장', FILLET:'모깎기 (R=반지름, P=폴리선)', CHAMFER:'모따기 (D=거리, P=폴리선)', BREAK:'끊기', BREAKATPOINT:'점에서 끊기',
  JOIN:'결합', EXPLODE:'분해', ARRAY:'배열 (R=직사각형, P=원형)', STRETCH:'신축', LENGTHEN:'길이 조정 (DE/T)', ALIGN:'정렬', MATCHPROP:'특성 일치', PEDIT:'폴리선 편집 (C/O/J)', DIVIDE:'등분', MEASURE:'길이 분할',
  DIMANGULAR:'각도 치수', DIMCONTINUE:'연속 치수', DIMBASELINE:'기준선 치수', QLEADER:'지시선', LAYER:'레이어 관리', OSNAP:'객체 스냅·극좌표 설정', PURGE:'쓰지 않는 블록 정리', DXFIN:'DXF 열기', PASTECLIP:'붙여넣기 (Ctrl+V)', ZOOM:'줌 (E/W/P)'
});
const M = t => MENUS.find(m => m[0] === t)[1];
const C = (cmd, label, key) => ({ cmd, label, key });
M('파일').splice(1, 0, ['DXF 열기…', 'DXFIN', () => startCmd('DXFIN')]);
M('편집').splice(3, 0, ['잘라내기', 'Ctrl+X', () => document.dispatchEvent(new KeyboardEvent('keydown', { key:'x', ctrlKey:true }))], ['복사', 'Ctrl+C', () => document.dispatchEvent(new KeyboardEvent('keydown', { key:'c', ctrlKey:true }))], C('PASTECLIP', '붙여넣기', 'Ctrl+V'), '-');
M('보기').splice(1, 0, ['줌 창', 'Z → W', () => { startCmd('ZOOM'); submitInput('W'); }], ['이전 화면', 'Z → P', () => popView()]);
M('보기').push({ label:'극좌표 추적', key:'F10', chk:() => polarOn, run:() => setPolar(!polarOn) });
const draw_ = M('그리기'); draw_.length = 0;
draw_.push(C('LINE', '선'), C('XLINE', '무한선'), C('RAY', '광선'), C('PLINE', '폴리선'), C('POLYGON', '다각형'), C('RECTANG', '사각형'), C('ARC', '호'), C('CIRCLE', '원'), C('DONUT', '도넛'), C('SPLINE', '스플라인'), C('ELLIPSE', '타원'), '-',
  C('POINT', '점'), C('DIVIDE', '등분'), C('MEASURE', '길이 분할'), '-', C('HATCH', '해치'), C('REVCLOUD', '구름형 수정기호'), '-', C('BLOCK', '블록 만들기'), C('INSERT', '블록 삽입'), '-', C('TEXT', '문자'), C('MTEXT', '여러 줄 문자'));
const dim_ = M('치수'); dim_.length = 0;
dim_.push(C('DIMLINEAR', '선형 치수'), C('DIMALIGNED', '정렬 치수'), C('DIMANGULAR', '각도 치수'), C('DIMRADIUS', '반지름 치수'), C('DIMDIAMETER', '지름 치수'), '-', C('DIMCONTINUE', '연속 치수'), C('DIMBASELINE', '기준선 치수'), C('QLEADER', '지시선'), '-', C('DIMTXT', '치수 글자 높이…'));
const mod_ = M('수정'); mod_.length = 0;
mod_.push(C('PROPERTIES', '속성 (값 직접 고치기)…', 'Ctrl+1'), C('MATCHPROP', '특성 일치'), '-', C('ERASE', '지우기'), C('COPY', '복사'), C('MIRROR', '대칭'), C('OFFSET', '간격띄우기'), C('ARRAY', '배열'), '-',
  C('MOVE', '이동'), C('ROTATE', '회전'), C('SCALE', '축척'), C('STRETCH', '신축'), C('LENGTHEN', '길이 조정'), '-', C('TRIM', '자르기'), C('EXTEND', '연장'), C('BREAKATPOINT', '점에서 끊기'), C('BREAK', '끊기'), C('JOIN', '결합'),
  C('CHAMFER', '모따기'), C('FILLET', '모깎기'), C('EXPLODE', '분해'), '-', C('PEDIT', '폴리선 편집'), C('ALIGN', '정렬'));
MENUS.splice(MENUS.findIndex(m => m[0] === '조회'), 0, ['형식', [C('LAYER', '레이어…'), C('OSNAP', '객체 스냅·극좌표 설정…'), C('DIMTXT', '치수 글자 높이…'), '-', C('PURGE', '쓰지 않는 블록 정리')]]);
Object.assign(ICONS, {
  xline:'<path d="M2 18 22 6"/><circle cx="12" cy="12" r="1.6"/>', polygon:'<path d="m12 3 8 6-3 10H7L4 9z"/>', ellipse:'<ellipse cx="12" cy="12" rx="9" ry="5.5"/>', spline:'<path d="M3 17c4-12 7 6 11-4s5-2 7-4"/>',
  hatch:'<rect x="4" y="4" width="16" height="16"/><path d="m4 12 8-8M4 20 20 4M12 20l8-8"/>', block:'<rect x="4" y="4" width="7" height="7"/><rect x="13" y="13" width="7" height="7"/><path d="M11 7.5h4.5V13"/>',
  mtext:'<path d="M4 6h16M4 10h12M4 14h16M4 18h9"/>', dimang:'<path d="M4 20h16M4 20 16 6"/><path d="M12 20a8 8 0 0 0-2.3-5.6"/>', leader:'<path d="m4 20 8-8h8"/><path d="m4 20 1-4 3 3z" fill="currentColor"/>',
  array:'<rect x="3" y="3" width="5" height="5"/><rect x="10" y="3" width="5" height="5"/><rect x="3" y="10" width="5" height="5"/><rect x="10" y="10" width="5" height="5"/><path d="M17 17h4M19 15v4"/>',
  stretch:'<path d="M3 8h8v8H3z"/><path d="M11 12h9m-3-3 3 3-3 3"/>', trim:'<path d="M4 4l16 16M20 4 4 20"/><path d="M14 14l6 6" stroke-dasharray="2 2"/>', extend:'<path d="M20 3v18M3 12h11"/><path d="M14 12h6" stroke-dasharray="2 2"/>',
  break_:'<path d="M3 12h6M15 12h6"/><path d="M9 9v6M15 9v6"/>', join:'<path d="M3 15h7M14 9h7M10 15l4-6"/>', chamfer:'<path d="M4 20V10l6-6h10"/>', fillet:'<path d="M4 20V12a8 8 0 0 1 8-8h8"/>', explode:'<path d="M12 3v5M12 16v5M3 12h5M16 12h5M6 6l3 3M15 15l3 3M18 6l-3 3M6 18l3-3"/>',
  layer:'<path d="m12 3 9 5-9 5-9-5z"/><path d="m3 13 9 5 9-5"/>'
});
TB_DRAW.splice(1, 0, ['XLINE', '무한선', 'xline']);
TB_DRAW.splice(TB_DRAW.findIndex(x => x[0] === 'RECTANG') + 1, 0, ['POLYGON', '다각형', 'polygon']);
TB_DRAW.splice(TB_DRAW.findIndex(x => x[0] === 'ARC') + 1, 0, ['ELLIPSE', '타원', 'ellipse'], ['SPLINE', '스플라인', 'spline'], ['HATCH', '해치', 'hatch'], ['INSERT', '블록 삽입', 'block']);
TB_DRAW.splice(TB_DRAW.findIndex(x => x[0] === 'TEXT') + 1, 0, ['MTEXT', '여러 줄 문자', 'mtext']);
TB_DRAW.push(['DIMANGULAR', '각도 치수', 'dimang'], ['QLEADER', '지시선', 'leader']);
TB_MODIFY.splice(TB_MODIFY.findIndex(x => x[0] === 'OFFSET') + 1, 0, ['ARRAY', '배열', 'array']);
TB_MODIFY.splice(TB_MODIFY.findIndex(x => x[0] === 'SCALE') + 1, 0, ['STRETCH', '신축', 'stretch'], ['TRIM', '자르기', 'trim'], ['EXTEND', '연장', 'extend'], ['BREAK', '끊기', 'break_'], ['JOIN', '결합', 'join'], ['CHAMFER', '모따기', 'chamfer'], ['FILLET', '모깎기', 'fillet'], ['EXPLODE', '분해', 'explode']);
TB_MODIFY.push(['LAYER', '레이어', 'layer']);
function setPolar(v) { polarOn = v; const b = $('#tPolar'); if (b) b.classList.toggle('on', v); status(v ? `극좌표 켜짐 (${settings.polarInc}°)` : '극좌표 꺼짐'); }
(() => { // 상태막대: 극좌표 버튼, 객체스냅 오른쪽 클릭 = 설정
  const b = document.createElement('button'); b.id = 'tPolar'; b.title = '극좌표 추적 (F10) — 오른쪽 클릭: 각도 설정'; b.textContent = '극좌표';
  $('#tOrtho').after(b); b.onclick = () => setPolar(!polarOn); b.oncontextmenu = ev => { ev.preventDefault(); openOsnap(); };
  $('#tSnap').title = '객체 스냅 (F3) — 오른쪽 클릭: 스냅 종류 설정'; $('#tSnap').oncontextmenu = ev => { ev.preventDefault(); openOsnap(); };
  document.addEventListener('keydown', ev => { if (ev.key === 'F10' && !document.querySelector('dialog[open]')) { ev.preventDefault(); setPolar(!polarOn); } });
})();
// 호·원 옵션 (AutoCAD식: 호 C=중심부터, 원 2P/3P)
CMDS.ARC = () => ({
  start(c) { c.prompt = '호의 시작점 (C=중심부터):'; },
  text(c, t) { if (!c.pts.length && /^c$/i.test(t)) { c.cen = true; c.prompt = '호의 중심:'; return true; } },
  point(c, p) {
    c.pts.push(p);
    if (c.cen) {
      if (c.pts.length === 1) { c.ref = p; c.prompt = '호의 시작점:'; return; }
      if (c.pts.length === 2) { c.prompt = '호의 끝점(반시계):'; return; }
      const [ctr, s, e] = c.pts; commit({ type:'arc', layer:curLayer, cx:ctr[0], cy:ctr[1], r:dist(ctr, s), a1:norm360(angOf(ctr, s)), a2:norm360(angOf(ctr, e)) }); endCmd(); return;
    }
    if (c.pts.length === 1) c.prompt = '호의 두번째 점:'; else if (c.pts.length === 2) c.prompt = '호의 끝점:';
    else { const a = circ3(...c.pts); if (a) commit({ ...a, layer:curLayer }); endCmd(); }
  },
  preview(c, cur) {
    if (c.cen) { if (c.pts.length === 1) return [{ ...lineE(c.pts[0], cur), ghost:true }]; if (c.pts.length === 2) { const [ctr, s] = c.pts; return [{ type:'arc', layer:curLayer, cx:ctr[0], cy:ctr[1], r:dist(ctr, s), a1:angOf(ctr, s), a2:angOf(ctr, cur) }]; } return []; }
    if (c.pts.length === 1) return [lineE(c.pts[0], cur)];
    if (c.pts.length === 2) { const a = circ3(c.pts[0], c.pts[1], cur); return a ? [{ ...a, layer:curLayer }] : []; }
    return [];
  }
});
const CIRCLE0 = CMDS.CIRCLE;
CMDS.CIRCLE = () => {
  const d = CIRCLE0(), t0 = d.text, p0 = d.point, pv0 = d.preview;
  return Object.assign(d, {
    start(c) { c.prompt = '원의 중심점 (2P / 3P):'; },
    text(c, t) {
      if (!c.pts.length && /^[23]p$/i.test(t)) { c.mode = t[0] === '2' ? 2 : 3; c.prompt = '원 위의 첫 점:'; return true; }
      return t0.call(this, c, t);
    },
    point(c, p, raw) {
      if (c.mode) { c.pts.push(p); if (c.pts.length < c.mode) { c.prompt = '원 위의 다음 점:'; return; }
        if (c.mode === 2) { const m = mulv(addv(c.pts[0], c.pts[1]), 0.5); commit({ type:'circle', layer:curLayer, cx:m[0], cy:m[1], r:dist(c.pts[0], c.pts[1]) / 2 }); }
        else { const a = circ3(...c.pts); if (a) commit({ type:'circle', layer:curLayer, cx:a.cx, cy:a.cy, r:a.r }); }
        endCmd(); return; }
      return p0.call(this, c, p, raw);
    },
    preview(c, cur) {
      if (c.mode === 2 && c.pts.length === 1) { const m = mulv(addv(c.pts[0], cur), 0.5); return [{ type:'circle', layer:curLayer, cx:m[0], cy:m[1], r:dist(c.pts[0], cur) / 2 }]; }
      if (c.mode === 3 && c.pts.length === 2) { const a = circ3(c.pts[0], c.pts[1], cur); return a ? [{ type:'circle', layer:curLayer, cx:a.cx, cy:a.cy, r:a.r }] : []; }
      if (c.mode) return [];
      return pv0.call(this, c, cur);
    }
  });
};
buildToolbars(); buildMenus(); buildHelp();
ensureUserLayers();
draw();
})();
