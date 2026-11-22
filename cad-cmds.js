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
const EXT = ['ellipse', 'spline', 'xline', 'ray', 'point', 'donut', 'hatch', 'mtext', 'leader', 'dimang', 'insert', 'dimord'];
let blockVer = 0; // 블록 정의가 바뀌면 올림(블록·해치 그림 조각 캐시 무효화)
const primCache = new WeakMap();
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
  const T = doc.dimTxt, A = T * dimSt().arrow, c = [e.cx, e.cy], sw = norm360(e.a2 - e.a1), out = [{ k:'arc', c, r:e.r, a1:e.a1, a2:e.a2 }];
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
    case 'hatch': { // 해치 무늬는 계산이 많아 경계·패턴이 같으면 다시 쓰기
      const sig = `${e.pts.length}|${e.pts[0]}|${e.pts[e.pts.length - 1]}|${(e.holes || []).length}|${e.pat}|${e.sc}|${e.ang}`, ca = primCache.get(e);
      if (ca && ca.sig === sig) P.push(...ca.p); else { const hp = hatchPrims(e); primCache.set(e, { sig, p:hp }); P.push(...hp); }
      break;
    }
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
      const sig = `${e.name}|${e.x}|${e.y}|${e.sx}|${e.sy}|${e.rot}|${blockVer}`, ca = primCache.get(e);
      if (ca && ca.sig === sig) { P.push(...ca.p); break; }
      const T = insertXf(e, b), bp = [];
      for (const be of b.ents) for (const q of primsAny(be, depth + 1) || []) bp.push(xfPrim(q, T));
      primCache.set(e, { sig, p:bp }); P.push(...bp);
      break;
    }
    case 'dimord': P.push(...dimordPrims(e)); break;
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
moveEnt = (e, dx, dy) => { moveEnt0(e, dx, dy); if (e.holes) e.holes = e.holes.map(L => L.map(q => [q[0] + dx, q[1] + dy])); if ('lx' in e) { e.lx += dx; e.ly += dy; } };

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
    doc.blocks[name] = { base:base.slice(), ents:list.map(e => { const n = clone(e); delete n.id; delete n.floor; return n; }) }; blockVer++;
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
const SNAP_DEFAULT = { end:true, mid:true, cen:true, quad:true, int:true, tan:true, perp:true, near:false, node:true, ins:true };
settings.snap = Object.assign({}, SNAP_DEFAULT, settings.snap || {}); if (settings.snap.tan == null) settings.snap.tan = true;
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
  if (M.tan && ref) for (const gp of prims) for (const q of gp) if (q.k === 'arc') { // 접선: 기준점에서 원·호에 닿는 점
    const d = dist(ref, q.c); if (d <= q.r) continue;
    const base = angOf(q.c, ref), al = Math.acos(q.r / d) / D2R;
    for (const a of [base + al, base - al]) { if (!q.full && !onArc(a, q.a1, q.a2)) continue; const f = polar(q.c, q.r, a), dd = dist(f, p); if (dd < bd) { bd = dd; best = [f[0], f[1], '접선']; } }
  }
  if (best) return best;
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
const LAYER_KO = { dim:'치수', struct:'구조벽(10)', wall:'칸막이벽(13)', col:'기둥(11)', open:'창호(20)', area:'면적선(04)', room:'실', slab:'슬라브(30)', equip:'설비(40)', sheet:'도곽(70)', elev:'입면(60)', sec:'단면', hatch:'해치(50)', xref:'외부 참조' };
const layerLabel = k => { const o = [...$('#layerSel').options].find(x => x.value === k); return o ? o.textContent : LAYER_KO[k] || k; };
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
    const items = [['end', '끝점'], ['mid', '중간점'], ['cen', '중심'], ['quad', '사분점'], ['int', '교차점'], ['tan', '접선'], ['perp', '수직'], ['near', '근처점'], ['node', '절점'], ['ins', '삽입점']];
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
    start(c) { c.prompt = '줌 — 전체(E·A·Enter) / 창(W) / 이전(P) <전체>:'; },
    enter() { pushView(); endCmd(); zoomExtents(); },
    text(c, t) { const u = t.toUpperCase(); if (['E', 'A', 'Z', 'ALL', '전체'].includes(u)) { pushView(); endCmd(); zoomExtents(); return true; } if (u === 'P') { endCmd(); popView(); return true; } if (u === 'W') { c.win = true; c.prompt = '창의 첫 구석:'; return true; } },
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
    if (!LAYERS[key] || !(doc.userLayers || {})[key]) { // 도면에도 레이어 정의를 남김(다시 열 때 색 유지)
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
  if (mode === 'collect') { blockVer++; return { list:R.ents.map(r => convDxfEnt(r, k, layerKey, skipped)).filter(Boolean), skipped, unit:k }; } // 외부 참조용
  for (const r of R.ents) { const e = convDxfEnt(r, k, layerKey, skipped); if (e) { addEnt(e); n++; } }
  blockVer++;
  if (mode === 'add' && before) { const old = bounds(doc.ents.slice(0, before)), nb = bounds(doc.ents.slice(before)); if (old && nb && nb[0] < old[2] && nb[2] > old[0] && nb[1] < old[3] && nb[3] > old[1]) doc.ents.slice(before).forEach(e => moveEnt(e, old[2] + (old[2] - old[0]) * 0.1 - nb[0], 0)); }
  return { n, blocks:Object.keys(R.blocks).length, layers:Object.keys(R.layers).length, skipped, ver:R.header.$ACADVER || '?', unit:k };
}
function openDxfIn() {
  let dlg = $('#dlgDxf');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgDxf';
    dlg.innerHTML = '<h2>도면 열기 (DXF · DWG)</h2><div class="hint">오토캐드 도면(DWG)이나 DXF를 엽니다. 선·폴리선·원·호·글자·여러 줄 문자·타원·스플라인·블록·치수(모양 그대로)·해치·레이어 색을 가져옵니다. DWG는 이 브라우저 안에서만 읽고 서버로 보내지 않습니다.</div>' +
      '<label for="dxfFile">DWG 또는 DXF 파일</label><input type="file" id="dxfFile" accept=".dxf,.dwg"><div class="err" id="dxfErr"></div>' +
      '<div class="btns"><button id="dxfCancel">닫기</button><button id="dxfAdd">지금 도면에 추가</button><button id="dxfNew" class="primary">새 도면으로 열기</button></div>';
    document.body.appendChild(dlg); $('#dxfCancel').onclick = () => dlg.close();
    const go = async mode => {
      const f = $('#dxfFile').files[0]; if (!f) { $('#dxfErr').textContent = 'DWG나 DXF 파일을 고르세요'; return; }
      if (/\.dwg$/i.test(f.name)) { // DWG는 acad-ts로 읽음
        $('#dxfErr').textContent = 'DWG를 읽는 중…'; snapshot();
        try { const r = await importDwg(await f.arrayBuffer(), mode); save(); dlg.close(); zoomExtents(); $('#dxfErr').textContent = '';
          const sk = Object.entries(r.skipped).map(([t, c]) => `${t} ${c}`).join(', ');
          info(`DWG 열기: ${f.name} · 요소 ${r.n}개 · 블록 ${r.blocks} · 레이어 ${r.layers}${r.unit !== 1 ? ` · 단위 ×${r.unit}→mm` : ''}${sk ? `
가져오지 못한 것: ${sk}` : ''}`);
        } catch (err) { undoStack.pop(); $('#dxfErr').textContent = 'DWG를 읽지 못했습니다: ' + err.message; }
        return;
      }
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
/* =====================================================================
   2차 확장: 치수 스타일·좌표 치수·폴리선 호·원 TTR·그룹·DWG 열기/저장·외부 참조·출력(PDF)·3D 보기
   ===================================================================== */
/* ---------- 치수 스타일 ---------- */
function dimSt() { return Object.assign({ arrow:0.8, gap:0.4, prec:null }, doc.dimStyle || {}); }
function dimFmt(v) { const p = dimSt().prec; return p == null || p === '' ? fmt(v) : (+v).toFixed(+p); }
dimGeom = e => { // 기본 치수 모양에 치수 스타일(화살표 크기·보조선 띄움·소수 자리)을 반영
  const st = dimSt(), T = doc.dimTxt, A = T * st.arrow, gap = T * st.gap, lines = [], tris = [], texts = [];
  if (e.type === 'dim') {
    const dir = e.dir || 'a', off = Number.isFinite(e.off) ? e.off : T * 3; let d1, d2;
    if (dir === 'h') { const y = e.y1 + off; d1 = [e.x1, y]; d2 = [e.x2, y]; }
    else if (dir === 'v') { const x = e.x1 + off; d1 = [x, e.y1]; d2 = [x, e.y2]; }
    else { const L = Math.hypot(e.x2 - e.x1, e.y2 - e.y1) || 1, nx = -(e.y2 - e.y1) / L, ny = (e.x2 - e.x1) / L; d1 = [e.x1 + nx * off, e.y1 + ny * off]; d2 = [e.x2 + nx * off, e.y2 + ny * off]; }
    for (const [p, d] of [[[e.x1, e.y1], d1], [[e.x2, e.y2], d2]]) { const vx = d[0] - p[0], vy = d[1] - p[1], L = Math.hypot(vx, vy); if (L > gap) { const ux = vx / L, uy = vy / L; lines.push([p[0] + ux * gap, p[1] + uy * gap, d[0] + ux * gap * 1.5, d[1] + uy * gap * 1.5]); } }
    lines.push([d1[0], d1[1], d2[0], d2[1]]);
    const len = Math.hypot(d2[0] - d1[0], d2[1] - d1[1]);
    if (len > 0) { const ux = (d2[0] - d1[0]) / len, uy = (d2[1] - d1[1]) / len; tris.push(arrow(d1, -ux, -uy, A), arrow(d2, ux, uy, A)); }
    const ang = readable(Math.atan2(d2[1] - d1[1], d2[0] - d1[0])), mx = (d1[0] + d2[0]) / 2, my = (d1[1] + d2[1]) / 2;
    texts.push({ x:mx - Math.sin(ang) * gap, y:my + Math.cos(ang) * gap, h:T, rot:ang, text:e.text || dimFmt(len), center:true });
  } else {
    const a = (Number.isFinite(e.ang) ? e.ang : 45) * D2R, ux = Math.cos(a), uy = Math.sin(a);
    const txt = e.text || (e.type === 'dimdia' ? 'Ø' + dimFmt(e.r * 2) : 'R' + dimFmt(e.r)), tw = textW(txt, T);
    const pEnd = [e.cx + ux * e.r, e.cy + uy * e.r], pStart = e.type === 'dimdia' ? [e.cx - ux * e.r, e.cy - uy * e.r] : [e.cx, e.cy], ext = [pEnd[0] + ux * (tw + gap * 2), pEnd[1] + uy * (tw + gap * 2)];
    lines.push([pStart[0], pStart[1], ext[0], ext[1]]); tris.push(arrow(pEnd, ux, uy, A)); if (e.type === 'dimdia') tris.push(arrow(pStart, -ux, -uy, A));
    const ang = readable(a), mx = (pEnd[0] + ext[0]) / 2, my = (pEnd[1] + ext[1]) / 2;
    texts.push({ x:mx - Math.sin(ang) * gap, y:my + Math.cos(ang) * gap, h:T, rot:ang, text:txt, center:true });
  }
  return { lines, tris, texts };
};
function openDimStyle() {
  let dlg = $('#dlgDim');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgDim';
    dlg.innerHTML = '<h2>치수 스타일</h2><div class="hint">도면의 모든 치수에 적용됩니다.</div>' +
      '<label for="dsH">문자 높이 (mm, 실제 크기)</label><input type="text" id="dsH">' +
      '<label for="dsA">화살표 크기 (문자 높이의 배수)</label><input type="text" id="dsA">' +
      '<label for="dsG">치수 보조선 띄움 (문자 높이의 배수)</label><input type="text" id="dsG">' +
      '<label for="dsP">소수 자리 (비우면 자동, 건축은 보통 0)</label><input type="text" id="dsP">' +
      '<label for="dsO">좌표 치수 원점 X,Y</label><input type="text" id="dsO">' +
      '<div class="btns"><button id="dsCancel">닫기</button><button id="dsOk" class="primary">적용</button></div>';
    document.body.appendChild(dlg); $('#dsCancel').onclick = () => dlg.close();
    $('#dsOk').onclick = () => {
      const h = parseFloat($('#dsH').value), a = parseFloat($('#dsA').value), g = parseFloat($('#dsG').value), pr = $('#dsP').value.trim(), o = $('#dsO').value.split(',').map(Number);
      if (h > 0) doc.dimTxt = h;
      doc.dimStyle = { arrow:a > 0 ? a : 0.8, gap:g >= 0 ? g : 0.4, prec:/^\d$/.test(pr) ? +pr : null };
      if (o.length === 2 && o.every(Number.isFinite)) doc.ordOrigin = o;
      save(); draw(); dlg.close(); status('치수 스타일을 적용했습니다');
    };
  }
  const st = dimSt(); $('#dsH').value = fmt(doc.dimTxt); $('#dsA').value = st.arrow; $('#dsG').value = st.gap; $('#dsP').value = st.prec ?? ''; $('#dsO').value = (doc.ordOrigin || [0, 0]).join(',');
  dlg.showModal();
}

/* ---------- 좌표 치수 dimord{x,y(대상 점),lx,ly(지시선 끝),axis:'x'|'y'} ---------- */
function dimordPrims(e) {
  const T = doc.dimTxt, o = doc.ordOrigin || [0, 0], v = e.axis === 'x' ? e.x - o[0] : e.y - o[1], txt = e.text || dimFmt(v), gap = T * dimSt().gap, w = textW(txt, T);
  if (e.axis === 'x') {
    const s = Math.sign(e.ly - e.y) || 1;
    return [{ k:'pl', pts:[[e.x, e.y + s * gap], [e.x, e.ly]] }, { k:'text', x:e.x + T * 0.5, y:s > 0 ? e.ly + T * 0.3 : e.ly - T * 0.3 - w, h:T, rot:Math.PI / 2, text:txt }];
  }
  const s = Math.sign(e.lx - e.x) || 1;
  return [{ k:'pl', pts:[[e.x + s * gap, e.y], [e.lx, e.y]] }, { k:'text', x:s > 0 ? e.lx + T * 0.3 : e.lx - T * 0.3 - w, y:e.y - T * 0.5, h:T, rot:0, text:txt }];
}
{
  const san0 = window.extSanitize, xf0 = window.extXform, sn0 = window.extSnaps;
  window.extSanitize = a => {
    if (a && a.type === 'dimord') {
      const n = k => Number.isFinite(+a[k]) && a[k] !== null && a[k] !== '' ? +a[k] : null; if ([n('x'), n('y'), n('lx'), n('ly')].some(v => v == null)) return null;
      const e = { type:'dimord', layer:'dim', x:n('x'), y:n('y'), lx:n('lx'), ly:n('ly'), axis:a.axis === 'y' ? 'y' : 'x' };
      if (typeof a.text === 'string' && a.text) e.text = a.text; if (a.floor != null && lvOf(String(a.floor))) e.floor = String(a.floor); return e;
    }
    return san0(a);
  };
  window.extXform = (e, f, o) => { if (e.type === 'dimord') { const q = f([e.lx, e.ly]); e.lx = q[0]; e.ly = q[1]; return; } xf0(e, f, o); };
  window.extSnaps = e => e.type === 'dimord' ? [[e.x, e.y, '끝점']] : sn0(e);
  TYPE_KO.dimord = '좌표 치수';
}

/* ---------- 폴리선 호 구간 (PLINE의 A/L) ---------- */
function plArc(S, t, E) { // S에서 접선 방향 t로 출발해 E에서 끝나는 호(점 목록)와 끝 접선
  const n = [-t[1], t[0]], ch = sub(E, S), dn = dot(ch, n);
  if (Math.abs(dn) < 1e-9 * Math.max(1, dot(ch, ch))) return { pts:[E], endDir:unit(ch) };
  const R = dot(ch, ch) / (2 * dn), c = addv(S, mulv(n, R)), a1 = angOf(c, S), a2 = angOf(c, E);
  let sw = norm360(a2 - a1); if (R < 0) sw -= 360;
  const NN = Math.max(4, Math.ceil(Math.abs(sw) / 6)), pts = [];
  for (let i = 1; i <= NN; i++) pts.push(polar(c, Math.abs(R), a1 + sw * i / NN));
  pts[pts.length - 1] = E.slice();
  return { pts, endDir:unit(R > 0 ? [-(E[1] - c[1]), E[0] - c[0]] : [E[1] - c[1], -(E[0] - c[0])]) };
}
CMDS.PLINE = () => ({
  start(c) { c.prompt = '폴리선 — 첫 점:'; c.arc = false; },
  pr(c) { c.prompt = c.arc ? '호의 끝점 (L=직선, C=닫기, Enter=끝):' : '다음 점 (A=호, C=닫기, Enter=끝):'; },
  point(c, p) {
    if (!c.pts.length) { c.pts.push(p); this.pr(c); return; }
    const s = c.pts[c.pts.length - 1];
    if (c.arc) { const r = plArc(s, c.dir || unit(sub(p, s)), p); c.pts.push(...r.pts); c.dir = r.endDir; }
    else { c.pts.push(p); c.dir = unit(sub(p, s)); }
    this.pr(c);
  },
  finish(c, closed) { if (c.pts.length >= 2) commit({ type:'polyline', layer:curLayer, pts:c.pts.slice(), closed }); endCmd(); },
  enter(c) { this.finish(c, false); },
  text(c, t) {
    if (/^a$/i.test(t) && c.pts.length) { c.arc = true; this.pr(c); return true; }
    if (/^l$/i.test(t)) { c.arc = false; this.pr(c); return true; }
    if (/^c$/i.test(t) && c.pts.length > 2) { this.finish(c, true); return true; }
  },
  preview(c, cur) {
    if (!c.pts.length) return [];
    const s = c.pts[c.pts.length - 1], tail = c.arc && dist(s, cur) > 1e-9 ? plArc(s, c.dir || unit(sub(cur, s)), cur).pts : [cur];
    return [{ type:'polyline', layer:curLayer, pts:[...c.pts, ...tail] }];
  }
});

/* ---------- 원 TTR (두 객체에 접하고 반지름을 아는 원) ---------- */
function offsetsOf(e, r) {
  if (['line', 'wall', 'window'].includes(e.type)) { const a = [e.x1, e.y1], b = [e.x2, e.y2], u = unit(sub(b, a)), n = [-u[1], u[0]]; return [1, -1].map(s => ({ k:'line', a:addv(a, mulv(n, r * s)), b:addv(b, mulv(n, r * s)) })); }
  if (e.type === 'circle' || e.type === 'arc') return [e.r + r, e.r - r].filter(x => x > 1e-9).map(R => ({ k:'circ', c:[e.cx, e.cy], r:R }));
  return [];
}
function interOff(A, B) {
  if (A.k === 'line' && B.k === 'line') { const x = lineX(A.a, A.b, B.a, B.b); return x ? [x] : []; }
  if (A.k === 'line' || B.k === 'line') { const L = A.k === 'line' ? A : B, Cc = A.k === 'line' ? B : A; return interLineCircle(L.a, L.b, Cc.c, Cc.r, false); }
  return interPrims({ k:'arc', c:A.c, r:A.r, a1:0, a2:360, full:true }, { k:'arc', c:B.c, r:B.r, a1:0, a2:360, full:true });
}
function ttrCenter(o1, o2, r, k1, k2) {
  const cand = []; for (const A of offsetsOf(o1, r)) for (const B of offsetsOf(o2, r)) cand.push(...interOff(A, B));
  if (!cand.length) return null;
  const m = mulv(addv(k1, k2), 0.5); cand.sort((x, y) => dist(x, m) - dist(y, m)); return cand[0];
}
{
  const CIRCLE1 = CMDS.CIRCLE;
  CMDS.CIRCLE = () => {
    const d = CIRCLE1(), t1 = d.text, p1 = d.point, pv1 = d.preview;
    return Object.assign(d, {
      start(c) { c.prompt = '원의 중심점 (2P / 3P / T=접선·접선·반지름):'; },
      text(c, t) {
        if (!c.pts.length && !c.mode && /^t(tr)?$/i.test(t)) { c.mode = 'T'; c.prompt = '원이 닿을 첫 객체(선·원·호) 클릭:'; return true; }
        if (c.mode === 'T') { if (c.o2 && N(t) > 0) { const ctr = ttrCenter(c.o1, c.o2, N(t), c.k1, c.k2); if (!ctr) status('그 반지름으로는 두 객체에 닿는 원이 없습니다'); else commit({ type:'circle', layer:curLayer, cx:ctr[0], cy:ctr[1], r:N(t) }); endCmd(); } return true; }
        return t1.call(this, c, t);
      },
      point(c, p, raw) {
        if (c.mode === 'T') {
          const e = pick(raw); if (!e || !offsetsOf(e, 1).length) return status('선·원·호를 클릭하세요');
          if (!c.o1) { c.o1 = e; c.k1 = raw; c.prompt = '두번째 객체 클릭:'; } else if (!c.o2) { c.o2 = e; c.k2 = raw; c.prompt = '반지름:'; }
          return;
        }
        return p1.call(this, c, p, raw);
      },
      preview(c, cur) { return c.mode === 'T' ? [] : pv1.call(this, c, cur); }
    });
  };
}

/* ---------- 좌표 치수 명령 ---------- */
CMDS.DIMORDINATE = () => ({
  start(c) { c.prompt = '좌표 치수 — 대상 점:'; },
  point(c, p) {
    if (!c.f) { c.f = p; c.ref = p; c.prompt = '지시선 끝 (위아래로 끌면 X값, 좌우로 끌면 Y값):'; return; }
    commit(this.mk(c, p)); endCmd();
  },
  mk(c, p) { const ax = Math.abs(p[1] - c.f[1]) >= Math.abs(p[0] - c.f[0]) ? 'x' : 'y'; return { type:'dimord', layer:'dim', x:c.f[0], y:c.f[1], lx:p[0], ly:p[1], axis:ax }; },
  preview(c, cur) { return c.f ? [this.mk(c, cur)] : []; }
});

/* ---------- 그룹 ---------- */
function liveGroups() {
  const g = doc.groups || (doc.groups = {});
  for (const [n, ids] of Object.entries(g)) { g[n] = ids.filter(id => findEnt(id)); if (!g[n].length) delete g[n]; }
  return g;
}
CMDS.GROUP = () => ({
  start(c) { c.rawText = true; c.prompt = '그룹 이름 (Enter=자동 이름):'; },
  enter(c) { this.text(c, '그룹' + (Object.keys(liveGroups()).length + 1)); },
  text(c, t) {
    if (c.gn) return; c.gn = t.trim() || '그룹' + (Object.keys(liveGroups()).length + 1); c.rawText = false;
    selectStep(c, () => { const g = liveGroups(); g[c.gn] = [...sel]; save(); status(`그룹 "${c.gn}" 만듦 (${sel.size}개)`); endCmd(); }, '그룹으로 묶을');
    return true;
  }
});
CMDS.UNGROUP = () => ({ start(c) { selectStep(c, () => { const g = liveGroups(); let n = 0; for (const [k, ids] of Object.entries(g)) if (ids.some(id => sel.has(id))) { delete g[k]; n++; } save(); status(n ? `그룹 ${n}개 풀었습니다` : '선택한 것에 그룹이 없습니다'); endCmd(); }, '그룹을 풀'); } });
{
  const clickAt1 = clickAt;
  clickAt = (sx, sy) => { // 그룹 안의 하나를 고르면 그룹 전체가 함께 골라짐
    const before = new Set(sel); clickAt1(sx, sy);
    if (cmd && !cmd.selecting) return;
    let changed = false;
    for (const ids of Object.values(liveGroups())) {
      const added = ids.some(id => sel.has(id) && !before.has(id)), removed = ids.some(id => !sel.has(id) && before.has(id));
      if (added) { ids.forEach(id => sel.add(id)); changed = true; } else if (removed) { ids.forEach(id => sel.delete(id)); changed = true; }
    }
    if (changed) { setPrompt(); draw(); }
  };
}

/* ---------- DWG 열기·저장 (acad-ts 3.6.0, MIT — vendor/acad-ts-LICENSE.txt) ---------- */
let acadP = null;
const acad = () => acadP || (acadP = import('./vendor/acad-ts-3.6.0.min.js').catch(err => { acadP = null; throw new Error('DWG 도구를 불러오지 못했습니다: ' + err.message); }));
function acadLayerKeyer(ad) {
  const tbl = {}; try { for (const L of ad.layers) tbl[L.name] = { color:L.color ? L.color.index : 7, on:L.isOn !== false, lt:L.lineType ? L.lineType.name : '' }; } catch {}
  return name => {
    if (!name || name === '0') return '0';
    const key = 'dx_' + name.replace(/[^\w가-힣-]/g, '_').slice(0, 40);
    if (!LAYERS[key] || !(doc.userLayers || {})[key]) { // 도면에도 레이어 정의를 남김(다시 열 때 색 유지)
      const L = tbl[name] || { color:7, on:true, lt:'' }, dash = /HIDDEN|DASH|CENTER|PHANTOM|DOT/i.test(L.lt) ? [10, 5] : [], col = aciHex(L.color);
      doc.userLayers = doc.userLayers || {}; doc.userLayers[key] = { name, color:col, dash };
      ensureLayer(key, name, col, dash); DXF_BASE[key][1] = Math.abs(L.color) || 7;
      if (!L.on || L.color < 0) { doc.layerProps = doc.layerProps || {}; doc.layerProps[key] = { off:true }; }
    }
    return key;
  };
}
function acadConvert(ad, k, skipped) {
  const layerKey = acadLayerKeyer(ad), done = new Set(), V = v => [v.x * k, v.y * k];
  const lay = e => layerKey(e.layer ? e.layer.name : '0');
  const ensureBlock = br => {
    if (!br) return null; const name = br.name; if (done.has(name)) return name; done.add(name);
    const bp = (br.blockEntity && br.blockEntity.basePoint) || { x:0, y:0 };
    doc.blocks[name] = { base:[bp.x * k, bp.y * k], ents:[] };
    const ents = []; for (const be of br.entities) { const r = conv(be); if (r) ents.push(...r); }
    doc.blocks[name].ents = ents; return name;
  };
  const textOf = (e, L) => {
    const al = (e.horizontalAlignment || 0) || (e.verticalAlignment || 0), p = al && e.alignmentPoint ? V(e.alignmentPoint) : V(e.insertPoint), t = String(e.value ?? '');
    if (!t.trim()) return null; const h = (e.height || 1) * k;
    return { layer:L, type:'text', x:p[0] - ([1, 4].includes(e.horizontalAlignment) ? textW(t, h) / 2 : 0), y:p[1], h, rot:(e.rotation || 0) / D2R, text:decodeDxfText(t) };
  };
  const conv = e => {
    const L = lay(e), on = e.objectName;
    try {
      switch (on) {
        case 'LINE': return [{ layer:L, type:'line', x1:e.startPoint.x * k, y1:e.startPoint.y * k, x2:e.endPoint.x * k, y2:e.endPoint.y * k }];
        case 'CIRCLE': return [{ layer:L, type:'circle', cx:e.center.x * k, cy:e.center.y * k, r:e.radius * k }];
        case 'ARC': { const flip = e.normal && e.normal.z < 0; let a1 = e.startAngle / D2R, a2 = e.endAngle / D2R, cx = e.center.x * k; if (flip) { cx = -cx; [a1, a2] = [180 - a2, 180 - a1]; } return [{ layer:L, type:'arc', cx, cy:e.center.y * k, r:e.radius * k, a1:norm360(a1), a2:norm360(a2) }]; }
        case 'LWPOLYLINE': case 'POLYLINE': {
          const vs = [...(e.vertices || [])].map(v => { const q = v.location || v; return { p:[q.x * k, q.y * k], b:v.bulge || 0 }; }); if (vs.length < 2) return null;
          const closed = !!e.isClosed, pts = [vs[0].p]; for (let j = 0; j < vs.length - 1 + (closed ? 1 : 0); j++) pts.push(...bulgePts(vs[j].p, vs[(j + 1) % vs.length].p, vs[j].b));
          if (closed) pts.pop(); return [{ layer:L, type:'polyline', pts, closed }];
        }
        case 'TEXT': case 'ATTRIB': { const t = textOf(e, L); return t ? [t] : null; }
        case 'MTEXT': {
          const t = decodeDxfText(typeof e.getPlainTextLines === 'function' ? e.getPlainTextLines().join('\n') : (e.plainText ?? e.value ?? '')); if (!t.trim()) return null;
          const h = (e.height || 1) * k, p = V(e.insertPoint), lines = t.split('\n'), w = Math.max(...lines.map(s => textW(s, h))), tot = h + (lines.length - 1) * h * 1.6;
          const ap = (e.attachmentPoint || 1) - 1, col = ap % 3, row = Math.floor(ap / 3);
          return [{ layer:L, type:'mtext', x:p[0] - col * w / 2, y:p[1] + row * tot / 2, h, rot:(e.rotation || 0) / D2R, text:t }];
        }
        case 'POINT': { const q = e.location || e.position; return q ? [{ layer:L, type:'point', x:q.x * k, y:q.y * k }] : null; }
        case 'ELLIPSE': {
          const m = e.majorAxisEndPoint || e.endPoint, rx = Math.hypot(m.x, m.y) * k, r = { layer:L, type:'ellipse', cx:e.center.x * k, cy:e.center.y * k, rx, ry:rx * (e.radiusRatio || 1), rot:Math.atan2(m.y, m.x) / D2R };
          const p1 = e.startParameter || 0, p2 = e.endParameter ?? Math.PI * 2; if (Math.abs(p2 - p1 - Math.PI * 2) > 1e-6 && Math.abs(p2 - p1) > 1e-6) { r.a1 = p1 / D2R; r.a2 = p2 / D2R; } return [r];
        }
        case 'SPLINE': { const src = (e.fitPoints && e.fitPoints.length >= 2) ? e.fitPoints : (e.controlPoints || []); const pts = [...src].map(V); return pts.length >= 2 ? [{ layer:L, type:'spline', pts, closed:!!e.isClosed }] : null; }
        case 'INSERT': {
          const name = ensureBlock(e.block); if (!name) return null; const p = V(e.insertPoint);
          const out = [{ layer:L, type:'insert', name, x:p[0], y:p[1], sx:e.xScale ?? 1, sy:e.yScale ?? e.xScale ?? 1, rot:(e.rotation || 0) / D2R }];
          for (const at of e.attributes || []) { const t = textOf(at, lay(at)); if (t) out.push(t); }
          return out;
        }
        case 'DIMENSION': { const name = ensureBlock(e.block); return name ? [{ layer:L, type:'insert', name, x:0, y:0, sx:1, sy:1, rot:0 }] : null; }
        case 'SOLID': case 'TRACE': { const q = [V(e.firstCorner), V(e.secondCorner), V(e.fourthCorner), V(e.thirdCorner)]; return [{ layer:L, type:'hatch', pts:dist(q[2], q[3]) < 1e-9 ? q.slice(0, 3) : q, pat:'SOLID', sc:1 }]; }
        case 'HATCH': {
          const loops = [];
          for (const path of e.paths || []) {
            const pts = [];
            for (const ed of path.edges || []) {
              if (ed.vertices) { const vs = [...ed.vertices].map(v => ({ p:[v.x * k, v.y * k], b:v.z || 0 })); if (!vs.length) continue; pts.push(vs[0].p); for (let j = 0; j < vs.length - 1 + (ed.isClosed ? 1 : 0); j++) pts.push(...bulgePts(vs[j].p, vs[(j + 1) % vs.length].p, vs[j].b)); }
              else if (ed.start && ed.end) { if (!pts.length) pts.push(V(ed.start)); pts.push(V(ed.end)); }
              else if (ed.center && ed.radius != null && ed.startAngle != null) { const c = V(ed.center), r = ed.radius * k, a1 = ed.startAngle / D2R, a2 = ed.endAngle / D2R, ccw = ed.counterClockWise !== false, sw = norm360(a2 - a1) || 360; for (let q = 0; q <= 12; q++) pts.push(polar(c, r, ccw ? a1 + sw * q / 12 : -a1 - sw * q / 12)); }
              else skipped['해치 곡선 경계'] = (skipped['해치 곡선 경계'] || 0) + 1;
            }
            if (pts.length >= 3) loops.push(pts);
          }
          if (!loops.length) { skipped['해치'] = (skipped['해치'] || 0) + 1; return null; }
          const pn = String(e.pattern && e.pattern.name || '').toUpperCase();
          const h = { layer:L, type:'hatch', pts:loops[0], pat:e.isSolid || pn === 'SOLID' ? 'SOLID' : (PAT[pn] ? pn : 'ANSI31'), sc:(e.patternScale || 1) * k, ang:(e.patternAngle || 0) / D2R };
          if (loops.length > 1) h.holes = loops.slice(1); return [h];
        }
        case 'LEADER': { const pts = [...(e.vertices || [])].map(V); return pts.length >= 2 ? [{ layer:L, type:'leader', pts, h:doc.dimTxt }] : null; }
        case 'VIEWPORT': case 'ATTDEF': return null;
      }
    } catch (err) { skipped[on + ' 오류'] = (skipped[on + ' 오류'] || 0) + 1; return null; }
    skipped[on] = (skipped[on] || 0) + 1; return null;
  };
  return { conv };
}
async function importDwg(ab, mode) {
  const A = await acad();
  const ad = A.DwgReader.readFromStream(ab, () => {});
  const k = UNIT_MM[ad.header.insUnits] || 1, skipped = {};
  if (mode === 'new') { doc.ents = []; doc.blocks = {}; sel.clear(); }
  doc.blocks = doc.blocks || {};
  const { conv } = acadConvert(ad, k, skipped), list = [];
  for (const e of ad.modelSpace.entities) { const r = conv(e); if (r) list.push(...r); }
  blockVer++;
  if (mode === 'collect') return { list, skipped, unit:k };
  const before = doc.ents.length; list.forEach(e => addEnt(e));
  if (mode === 'add' && before) { const old = bounds(doc.ents.slice(0, before)), nb = bounds(doc.ents.slice(before)); if (old && nb && nb[0] < old[2] && nb[2] > old[0] && nb[1] < old[3] && nb[3] > old[1]) doc.ents.slice(before).forEach(e => moveEnt(e, old[2] + (old[2] - old[0]) * 0.1 - nb[0], 0)); }
  return { n:list.length, blocks:Object.keys(doc.blocks).length, layers:[...ad.layers].length, skipped, unit:k };
}
window.importDwgBuffer = importDwg; // 시험용
async function buildDwg() {
  const A = await acad(), ad = new A.CadDocument(); ad.header.version = A.ACadVersion.AC1032;
  const layers = new Map(), XYZ = (x, y) => new A.XYZ(x, y, 0);
  const layerFor = e => {
    const Lr = dxfLayerOf(e); if (Lr.name === '0') return null;
    if (!layers.has(Lr.name)) { const ly = new A.Layer(Lr.name); try { ly.color = new A.Color(Lr.color); } catch {} ad.layers.add(ly); layers.set(Lr.name, ly); }
    return layers.get(Lr.name);
  };
  const add = (ent, e) => { const ly = layerFor(e); if (ly) ent.layer = ly; if (e.color) { try { ent.color = new A.Color(hexToAci(e.color)); } catch {} } ad.modelSpace.entities.add(ent); };
  const poly = (pts, closed, e) => {
    if (pts.length === 2 && !closed) { const l = new A.Line(); l.startPoint = XYZ(...pts[0]); l.endPoint = XYZ(...pts[1]); add(l, e); return; }
    const p = new A.LwPolyline(); for (const q of pts) { const v = new A.LwPolylineVertex(); v.location = new A.XY(q[0], q[1]); p.vertices.push(v); } p.isClosed = !!closed; add(p, e);
  };
  const text = (t, e) => {
    const x = new A.TextEntity(), h = t.h, r = t.rot || 0, half = t.center ? textW(t.text, h) / 2 : 0;
    x.value = String(t.text); x.height = h; x.rotation = r; x.insertPoint = XYZ(t.x - half * Math.cos(r), t.y - half * Math.sin(r)); add(x, e);
  };
  let n = 0;
  for (const e of doc.ents) {
    if (layerOff(e)) continue;
    if (e.type === 'line') { const l = new A.Line(); l.startPoint = XYZ(e.x1, e.y1); l.endPoint = XYZ(e.x2, e.y2); add(l, e); n++; continue; }
    if (e.type === 'text') { text({ x:e.x, y:e.y, h:e.h, rot:(e.rot || 0) * D2R, text:e.text }, e); n++; continue; }
    let prs = primsAny(e); if (!prs) continue;
    if (e.type === 'room') { const c = polyCentroid(e.pts); prs = prs.concat([{ k:'text', x:c[0], y:c[1], h:Math.max(doc.dimTxt * 1.2, 1), rot:0, text:`${e.name || ''} ${polyAreaM2(e.pts).toFixed(2)}㎡`, center:true }]); }
    for (const q of prs) {
      if (q.k === 'pl') { if (!q.nb) poly(q.pts, q.closed, e); }
      else if (q.k === 'arc') { if (q.full) { const c = new A.Circle(); c.center = XYZ(...q.c); c.radius = q.r; add(c, e); } else { const a = new A.Arc(); a.center = XYZ(...q.c); a.radius = q.r; a.startAngle = norm360(q.a1) * D2R; a.endAngle = norm360(q.a2) * D2R; add(a, e); } }
      else if (q.k === 'text') text(q, e);
      else if (q.k === 'fill') for (const Lp of q.loops) { if (Lp.length === 3 || Lp.length === 4) { const s = new A.Solid(), v = Lp.length === 3 ? [Lp[0], Lp[1], Lp[2], Lp[2]] : [Lp[0], Lp[1], Lp[3], Lp[2]]; s.firstCorner = XYZ(...v[0]); s.secondCorner = XYZ(...v[1]); s.thirdCorner = XYZ(...v[2]); s.fourthCorner = XYZ(...v[3]); add(s, e); } else poly(Lp, true, e); }
      else if (q.k === 'pt') { const p = new A.Point(); p.location = XYZ(...q.p); add(p, e); }
      else if (q.k === 'ring') for (const r of [q.ro, q.ri]) if (r > 0) { const c = new A.Circle(); c.center = XYZ(...q.c); c.radius = r; add(c, e); }
    }
    n++;
  }
  return { bytes:A.DwgWriter.writeToBuffer(ad), n };
}
window.buildDwgBytes = buildDwg; // 시험용
async function exportDWG() {
  if (!doc.ents.length) return status('그린 것이 없습니다');
  status('DWG를 만드는 중…');
  try {
    const r = await buildDwg();
    download(new Blob([r.bytes], { type:'application/acad' }), `drawing_${stamp()}.dwg`);
    info(`DWG 저장: 요소 ${r.n}개 (오토캐드 2018 형식). 블록·해치·치수는 선과 글자로 풀어서 저장됩니다.`);
  } catch (err) { status('DWG 저장 실패'); addMsg('err', 'DWG로 저장하지 못했습니다: ' + err.message); }
}

/* ---------- 외부 참조 붙이기 (다른 DWG·DXF를 블록 하나로) ---------- */
async function xattachFile(f) {
  let r;
  if (/\.dwg$/i.test(f.name)) r = await importDwg(await f.arrayBuffer(), 'collect');
  else { const buf = new Uint8Array(await f.arrayBuffer()), head = new TextDecoder('latin1').decode(buf.slice(0, 4000)), ver = (head.match(/\$ACADVER\s*\r?\n\s*1\s*\r?\n\s*AC(\d+)/) || [])[1]; r = importDxf(new TextDecoder(ver && +ver >= 1021 ? 'utf-8' : 'euc-kr').decode(buf), 'collect'); }
  if (!r.list.length) throw new Error('가져올 객체가 없습니다');
  const name = '참조_' + f.name.replace(/\.(dxf|dwg)$/i, '');
  doc.blocks = doc.blocks || {}; doc.blocks[name] = { base:[0, 0], ents:r.list, xref:f.name }; blockVer++;
  if (!LAYERS.xref) { doc.userLayers = doc.userLayers || {}; doc.userLayers.xref = { name:'외부 참조', color:'#9aa7b4', dash:[] }; ensureLayer('xref', '외부 참조', '#9aa7b4'); }
  const ins = { type:'insert', layer:'xref', name, x:0, y:0, sx:1, sy:1, rot:0 }; addEnt(ins);
  return { ins, n:r.list.length };
}
window.xattachFile = xattachFile; // 시험용
function xattach() {
  const inp = document.createElement('input'); inp.type = 'file'; inp.accept = '.dxf,.dwg';
  inp.onchange = async () => {
    const f = inp.files[0]; if (!f) return;
    status(`${f.name} 읽는 중…`); snapshot();
    try {
      const r = await xattachFile(f); save(); zoomExtents();
      info(`외부 참조 붙임: ${f.name} (객체 ${r.n}개, 원래 좌표 그대로)\n한 덩어리 블록이라 이동(M)·회전으로 맞추고, 레이어 「외부 참조」를 잠그면 실수로 고치지 않습니다. 원본 파일이 바뀌면 다시 붙여야 합니다.`);
    } catch (err) { undoStack.pop(); addMsg('err', '외부 참조를 붙이지 못했습니다: ' + err.message); status('외부 참조 실패'); }
  };
  inp.click();
}

/* ---------- 출력 (PDF·인쇄) — 축척·용지·선 굵기 ---------- */
const PAPER_MM = { A4:[297, 210], A3:[420, 297], A2:[594, 420], A1:[841, 594], A0:[1189, 841] };
const LW_DEFAULT = { '0':0.25, struct:0.5, area:0.5, wall:0.35, col:0.5, open:0.25, room:0.13, slab:0.25, equip:0.25, dim:0.18, center:0.18, hidden:0.25, site:0.35, setback:0.25, ann:0.25, sheet:0.35, elev:0.35, sec:0.5, hatch:0.13, xref:0.18 };
const lwOf = k => (doc.plotLW || {})[k] ?? LW_DEFAULT[k] ?? 0.25;
const plotKey = e => isDim(e) || ['dimang', 'dimord', 'leader'].includes(e.type) ? 'dim' : e.type === 'wall' ? (e.wk === 'struct' ? 'struct' : 'wall') : e.layer;
function plotSVG(o) {
  const [pw0, ph0] = PAPER_MM[o.paper] || PAPER_MM.A3, [W, H] = o.portrait ? [ph0, pw0] : [pw0, ph0], MG = 10;
  const ents = doc.ents.filter(e => !layerOff(e) && (!e.floor || e.floor === doc.cur));
  let box;
  if (o.area === 'view') { const r = cv.getBoundingClientRect(), a = s2w(0, r.height), b = s2w(r.width, 0); box = [a[0], a[1], b[0], b[1]]; }
  else if (o.area === 'sheet') box = bounds(ents.filter(e => e.tag === 'sheet')) || bounds(ents);
  else box = bounds(ents);
  if (!box) throw new Error('출력할 도면이 없습니다');
  const bw = Math.max(box[2] - box[0], 1), bh = Math.max(box[3] - box[1], 1);
  const s = o.scale ? 1 / o.scale : Math.min((W - 2 * MG) / bw, (H - 2 * MG) / bh);
  const tx = W / 2 - (box[0] + box[2]) / 2 * s, ty = H / 2 + (box[1] + box[3]) / 2 * s, X = x => (x * s + tx).toFixed(3), Y = y => (-y * s + ty).toFixed(3), S = v => (v * s).toFixed(3);
  const esc = t => String(t).replace(/[&<>"]/g, c => ({ '&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;' }[c]));
  const DASH = { center:'6 1.2 1 1.2', hidden:'2.5 1.2', site:'8 1.5 1.5 1.5 1.5 1.5', setback:'5 2' };
  const colOf = k => { if (o.mono) return '#000'; const c = (LAYERS[k] || LAYERS['0']).color, m = /^#([0-9a-f]{6})$/i.exec(c); if (!m) return '#000'; const v = parseInt(m[1], 16), lum = (0.299 * (v >> 16) + 0.587 * ((v >> 8) & 255) + 0.114 * (v & 255)) / 255; return lum > 0.75 ? '#000' : c; };
  const out = [];
  for (const e of ents) {
    let prs = e.type === 'text' ? [{ k:'text', x:e.x, y:e.y, h:e.h, rot:(e.rot || 0) * D2R, text:e.text }] : primsAny(e);
    if (!prs) continue;
    if (e.type === 'room') { const c = polyCentroid(e.pts); prs = prs.concat([{ k:'text', x:c[0], y:c[1], h:Math.max(doc.dimTxt * 1.2, 1), rot:0, text:`${e.name || ''} ${polyAreaM2(e.pts).toFixed(2)}㎡`, center:true }]); }
    const lk = plotKey(e), col = e.color && !o.mono ? e.color : colOf(lk), lw = lwOf(lk), dashed = (e.lt && LT_PLOT[e.lt]) || DASH[lk] || (((LAYERS[e.layer] || {}).dash || []).length ? '2.5 1.2' : '');
    const st = `fill="none" stroke="${col}" stroke-width="${lw}"${dashed ? ` stroke-dasharray="${dashed}"` : ''}`;
    for (const q of prs) {
      if (q.k === 'pl') { if (q.nb) continue; out.push(`<${q.closed ? 'polygon' : 'polyline'} points="${q.pts.map(p => X(p[0]) + ',' + Y(p[1])).join(' ')}" ${st}/>`); }
      else if (q.k === 'arc') { if (q.full) out.push(`<circle cx="${X(q.c[0])}" cy="${Y(q.c[1])}" r="${S(q.r)}" ${st}/>`); else { const a = polar(q.c, q.r, q.a1), b = polar(q.c, q.r, q.a2), sw = norm360(q.a2 - q.a1); out.push(`<path d="M${X(a[0])} ${Y(a[1])} A${S(q.r)} ${S(q.r)} 0 ${sw > 180 ? 1 : 0} 0 ${X(b[0])} ${Y(b[1])}" ${st}/>`); } }
      else if (q.k === 'fill') out.push(`<path d="${q.loops.map(Lp => 'M' + Lp.map(p => X(p[0]) + ' ' + Y(p[1])).join('L') + 'Z').join(' ')}" fill="${col}" fill-opacity="${q.alpha ?? 1}" fill-rule="evenodd" stroke="none"/>`);
      else if (q.k === 'text') { const fs = q.h * s; if (fs < 0.5) continue; out.push(`<text x="${X(q.x)}" y="${Y(q.y)}" font-size="${fs.toFixed(3)}" fill="${col}" font-family="Malgun Gothic, Apple SD Gothic Neo, sans-serif"${q.center ? ' text-anchor="middle"' : ''} transform="rotate(${(-(q.rot || 0) / D2R).toFixed(3)} ${X(q.x)} ${Y(q.y)})">${esc(q.text)}</text>`); }
      else if (q.k === 'pt') out.push(`<path d="M${(+X(q.p[0]) - 0.8).toFixed(3)} ${Y(q.p[1])}h1.6M${X(q.p[0])} ${(+Y(q.p[1]) - 0.8).toFixed(3)}v1.6" stroke="${col}" stroke-width="${lw}"/>`);
      else if (q.k === 'ring') { const ring = r => `M${X(q.c[0] + r)} ${Y(q.c[1])}a${S(r)} ${S(r)} 0 1 0 ${S(-2 * r)} 0a${S(r)} ${S(r)} 0 1 0 ${S(2 * r)} 0`; out.push(`<path d="${ring(q.ro)}${q.ri > 0 ? ring(q.ri) : ''}" fill="${col}" fill-rule="evenodd"/>`); }
    }
  }
  const fits = !o.scale || (bw * s <= W - 2 * MG + 0.01 && bh * s <= H - 2 * MG + 0.01);
  return { svg:`<svg xmlns="http://www.w3.org/2000/svg" width="${W}mm" height="${H}mm" viewBox="0 0 ${W} ${H}" stroke-linecap="round" stroke-linejoin="round"><rect width="${W}" height="${H}" fill="#fff"/>${out.join('')}</svg>`, W, H, scaleText:o.scale ? `1:${o.scale}` : `맞춤(약 1:${Math.round(1 / s)})`, fits, count:out.length };
}
window.plotSVG = plotSVG; // 시험용
function openPlot() {
  let dlg = $('#dlgPlot');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgPlot';
    dlg.innerHTML = '<h2>출력 (PDF · 인쇄)</h2><div class="hint">「인쇄 / PDF」를 누르면 인쇄 창이 뜹니다. 프린터에서 <b>PDF로 저장</b>을 고르면 축척이 맞는 벡터 PDF가 됩니다. 인쇄 설정의 배율은 <b>100%(실제 크기)</b>, 여백은 <b>없음</b>으로 두세요.</div>' +
      '<div style="display:grid;grid-template-columns:1fr 1fr;gap:0 12px">' +
      '<div><label for="plP">용지</label><select id="plP"><option>A4</option><option selected>A3</option><option>A2</option><option>A1</option><option>A0</option></select></div>' +
      '<div><label for="plO">방향</label><select id="plO"><option value="l">가로</option><option value="p">세로</option></select></div>' +
      '<div><label for="plS">축척</label><select id="plS"><option value="0">용지에 맞춤</option><option>1</option><option>10</option><option>20</option><option>30</option><option>50</option><option selected>100</option><option>150</option><option>200</option><option>300</option><option>500</option><option>1000</option></select></div>' +
      '<div><label for="plA">출력 범위</label><select id="plA"><option value="all">도면 전체(현재 층)</option><option value="view">지금 화면</option><option value="sheet">도곽</option></select></div></div>' +
      '<label><input type="checkbox" id="plM" checked> 흑백으로 출력</label>' +
      '<details style="margin-top:8px"><summary>레이어별 선 굵기 (mm)</summary><div id="plLW" style="display:grid;grid-template-columns:auto 80px;gap:4px 10px;margin-top:6px"></div></details>' +
      '<div class="err" id="plErr"></div><div class="btns"><button id="plClose">닫기</button><button id="plSvg">SVG로 저장</button><button id="plGo" class="primary">인쇄 / PDF</button></div>';
    document.body.appendChild(dlg); $('#plClose').onclick = () => dlg.close();
    const opts = () => ({ paper:$('#plP').value, portrait:$('#plO').value === 'p', scale:+$('#plS').value || 0, area:$('#plA').value, mono:$('#plM').checked });
    const make = () => { const r = plotSVG(opts()); $('#plErr').textContent = r.fits ? '' : `도면이 ${$('#plP').value} 용지(축척 ${r.scaleText})를 넘습니다. 더 큰 용지나 작은 축척을 고르세요. 넘치는 부분은 잘립니다.`; return r; };
    $('#plSvg').onclick = () => { try { const r = make(); download(new Blob([r.svg], { type:'image/svg+xml' }), `plot_${stamp()}.svg`); } catch (err) { $('#plErr').textContent = err.message; } };
    $('#plGo').onclick = () => {
      try {
        const r = make(), w = window.open('', '_blank');
        if (!w) { $('#plErr').textContent = '팝업이 막혀 있습니다. 주소창 오른쪽에서 팝업을 허용하거나 「SVG로 저장」을 쓰세요.'; return; }
        w.document.write(`<!doctype html><html><head><meta charset="utf-8"><title>말로 캐드 출력 ${r.scaleText}</title><style>@page{size:${r.W}mm ${r.H}mm;margin:0}html,body{margin:0;padding:0;background:#fff}svg{display:block;width:${r.W}mm;height:${r.H}mm}</style></head><body>${r.svg}<script>window.onload=()=>setTimeout(()=>window.print(),200)<\/script></body></html>`);
        w.document.close();
      } catch (err) { $('#plErr').textContent = err.message; }
    };
  }
  const box = $('#plLW'); box.innerHTML = '';
  for (const k of [...new Set(doc.ents.map(plotKey))]) {
    const l = document.createElement('span'); l.textContent = layerLabel(k); const i = document.createElement('input'); i.type = 'text'; i.value = lwOf(k);
    i.onchange = () => { const v = parseFloat(i.value); if (v > 0) { doc.plotLW = Object.assign({}, doc.plotLW, { [k]:v }); save(); } }; box.append(l, i);
  }
  $('#plErr').textContent = ''; dlg.showModal();
}

/* ---------- 3D 보기 (벽·기둥·슬라브·창·문·설비를 층고대로 세워 봄) ---------- */
function build3D() {
  const faces = [], lines = [], lvl = id => { const l = doc.levels.find(x => x.id === id) || doc.levels.find(x => x.id === doc.cur) || { el:0, h:3 }; return [l.el * 1000, (l.el + l.h) * 1000]; };
  const TILE = 1000; // 큰 면은 1m 조각으로 나눠 앞뒤 순서를 정확히(화가 알고리즘)
  const quad = (q, col, alpha, out) => { // q: 사각형 네 꼭짓점(바깥 방향 정렬됨), 조각으로 나눠 넣음
    const nu = Math.max(1, Math.min(40, Math.ceil(Math.hypot(...[0, 1, 2].map(i => q[1][i] - q[0][i])) / TILE))), nv = Math.max(1, Math.min(40, Math.ceil(Math.hypot(...[0, 1, 2].map(i => q[3][i] - q[0][i])) / TILE)));
    const at = (u, v) => [0, 1, 2].map(i => q[0][i] * (1 - u) * (1 - v) + q[1][i] * u * (1 - v) + q[2][i] * u * v + q[3][i] * (1 - u) * v);
    for (let i = 0; i < nu; i++) for (let j = 0; j < nv; j++) faces.push({ v:[at(i / nu, j / nv), at((i + 1) / nu, j / nv), at((i + 1) / nu, (j + 1) / nv), at(i / nu, (j + 1) / nv)], col, alpha, cull:out, bias:quad.bias || 0 });
  };
  const prism = (pts, z0, z1, col, alpha = 1) => {
    if (pts.length < 3 || z1 <= z0) return; const n = pts.length;
    let ar = 0; for (let i = 0; i < n; i++) ar += pts[i][0] * pts[(i + 1) % n][1] - pts[(i + 1) % n][0] * pts[i][1];
    const P = ar >= 0 ? pts : pts.slice().reverse(); // 반시계로 맞춰 면의 바깥 방향을 일정하게
    faces.push({ v:P.map(p => [p[0], p[1], z1]), col, alpha, cull:true }, { v:P.map(p => [p[0], p[1], z0]).reverse(), col, alpha, cull:true });
    for (let i = 0; i < n; i++) { const a = P[i], b = P[(i + 1) % n]; quad([[a[0], a[1], z0], [b[0], b[1], z0], [b[0], b[1], z1], [a[0], a[1], z1]], col, alpha, true); }
  };
  const panel = (a, b, z0, z1, col, alpha) => { // 창·문: 벽 양쪽 바깥면에서 살짝 띄운 판(각 판의 앞면이 벽 밖을 봄)
    const u = unit(sub(b, a)), nrm = [-u[1], u[0]];
    quad.bias = 400; // 벽면 바로 앞에 붙은 판이라 같은 깊이면 판을 나중에(앞에) 그림
    for (const s of [1, -1]) {
      const o = mulv(nrm, s * 115), A = addv(a, o), B = addv(b, o);
      quad(s < 0 ? [[A[0], A[1], z0], [B[0], B[1], z0], [B[0], B[1], z1], [A[0], A[1], z1]] : [[B[0], B[1], z0], [A[0], A[1], z0], [A[0], A[1], z1], [B[0], B[1], z1]], col, alpha, true);
    }
    quad.bias = 0;
  };
  for (const e of doc.ents) {
    if (layerOff(e)) continue; const [z0, z1] = lvl(e.floor);
    switch (e.type) {
      case 'wall': prism(wallQuad(e), z0, z1, [214, 208, 196]); break;
      case 'column': prism(e.r > 0 ? Array.from({ length:16 }, (_, i) => polar([e.cx, e.cy], e.r, i * 22.5)) : columnPts(e), z0, z1, [190, 186, 178]); break;
      case 'slab': { const top = Number.isFinite(e.top) ? e.top * 1000 : z1; prism(e.pts, top - (e.t || 150), top, [170, 176, 186]); break; }
      case 'equip': prism(equipPts(e), z0, z0 + (e.h || 1500), [222, 160, 90]); break;
      case 'window': panel([e.x1, e.y1], [e.x2, e.y2], z0 + (e.sill ?? 900), z0 + (e.sill ?? 900) + (e.wh || 1500), [90, 170, 230], 0.55); break;
      case 'door': { const g = doorGeom(e); panel([e.x, e.y], g.closed, z0, z0 + (e.dh || 2100), [150, 105, 70], 0.9); break; }
      case 'bldg': case 'room': lines.push({ pts:e.pts.map(p => [p[0], p[1], z0]), closed:true, col:e.type === 'bldg' ? '#ff7a7a' : '#7d8794' }); break;
      case 'line': lines.push({ pts:[[e.x1, e.y1, z0], [e.x2, e.y2, z0]], col:'#55606c' }); break;
      case 'polyline': case 'rect': { const q = primsAny(e)[0]; lines.push({ pts:q.pts.map(p => [p[0], p[1], z0]), closed:q.closed, col:'#55606c' }); break; }
    }
  }
  return { faces, lines };
}
window.build3D = build3D; // 시험용
function open3D() {
  const M3 = build3D();
  if (!M3.faces.length && !M3.lines.length) return status('3D로 세울 벽·기둥·슬라브가 없습니다');
  let dlg = $('#dlg3d');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlg3d'; dlg.style.width = 'min(1100px, calc(100vw - 32px))';
    dlg.innerHTML = '<h2>3D 보기</h2><div class="hint">끌기: 돌리기 · Shift+끌기: 이동 · 휠: 확대/축소 · 벽은 층고, 창·문은 창대·높이 값으로 세웁니다.</div><canvas id="c3d" style="width:100%;height:62vh;display:block;background:#11161b;border-radius:6px;margin-top:8px;touch-action:none"></canvas><div class="btns"><button id="c3dTop">위에서</button><button id="c3dIso">비스듬히</button><button id="c3dClose" class="primary">닫기</button></div>';
    document.body.appendChild(dlg); $('#c3dClose').onclick = () => dlg.close();
  }
  const c = $('#c3d'), g = c.getContext('2d'), all = [...M3.faces.flatMap(f => f.v), ...M3.lines.flatMap(l => l.pts)];
  const mn = [0, 1, 2].map(i => Math.min(...all.map(p => p[i]))), mx = [0, 1, 2].map(i => Math.max(...all.map(p => p[i])));
  const cam = { yaw:-35, pitch:30, dist:Math.max(mx[0] - mn[0], mx[1] - mn[1], mx[2] - mn[2], 1000) * 1.8, tgt:[(mn[0] + mx[0]) / 2, (mn[1] + mx[1]) / 2, (mn[2] + mx[2]) / 2] };
  const u3 = v => { const l = Math.hypot(...v) || 1; return v.map(x => x / l); }, s3 = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]], LD = u3([0.4, -0.6, 0.7]);
  const norms = M3.faces.map(fc => { const a = s3(fc.v[1], fc.v[0]), b = s3(fc.v[2], fc.v[0]); return u3([a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]); });
  const cents = M3.faces.map(fc => [0, 1, 2].map(i => fc.v.reduce((s, p) => s + p[i], 0) / fc.v.length));
  const render = () => {
    const dpr = window.devicePixelRatio || 1, W = c.clientWidth || 800, H = c.clientHeight || 500; c.width = W * dpr; c.height = H * dpr; g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, W, H);
    const cy = Math.cos(cam.yaw * D2R), sy = Math.sin(cam.yaw * D2R), cp = Math.cos(cam.pitch * D2R), sp = Math.sin(cam.pitch * D2R), f = Math.min(W, H) * 1.2;
    const P = p => { const x = p[0] - cam.tgt[0], y = p[1] - cam.tgt[1], z = p[2] - cam.tgt[2], x1 = x * cy - y * sy, y1 = x * sy + y * cy, y2 = y1 * cp - z * sp, z2 = y1 * sp + z * cp, d = Math.max(cam.dist + y2, 1); return [W / 2 + f * x1 / d, H / 2 - f * z2 / d, d]; };
    for (const l of M3.lines) { g.strokeStyle = l.col; g.lineWidth = 1; g.beginPath(); l.pts.forEach((p, i) => { const q = P(p); i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1]); }); if (l.closed) g.closePath(); g.stroke(); }
    const fw = [cp * sy, cp * cy, -sp], eye = [cam.tgt[0] - fw[0] * cam.dist, cam.tgt[1] - fw[1] * cam.dist, cam.tgt[2] - fw[2] * cam.dist]; // 카메라 위치
    const fs = [];
    M3.faces.forEach((fc, i) => {
      const n = norms[i], c0 = cents[i];
      if (fc.cull && n[0] * (eye[0] - c0[0]) + n[1] * (eye[1] - c0[1]) + n[2] * (eye[2] - c0[2]) <= 0) return; // 뒤돌아선 면은 안 그림
      const q = fc.v.map(P); fs.push({ fc, q, n, depth:q.reduce((s, x) => s + x[2], 0) / q.length - (fc.bias || 0) });
    });
    fs.sort((a, b) => b.depth - a.depth);
    for (const { fc, q, n } of fs) {
      const sh = 0.45 + 0.55 * Math.abs(n[0] * LD[0] + n[1] * LD[1] + n[2] * LD[2]);
      const fill = `rgba(${fc.col.map(v => Math.round(v * sh)).join(',')},${fc.alpha})`; g.fillStyle = fill; // 조각 이음매가 안 보이게 같은 색으로 테두리
      g.strokeStyle = fc.alpha < 1 ? 'rgba(40,60,80,0.6)' : fill; g.lineWidth = fc.alpha < 1 ? 0.8 : 0.5;
      g.beginPath(); q.forEach((p, i) => i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1])); g.closePath(); g.fill(); g.stroke();
    }
  };
  let drag = null;
  c.onpointerdown = ev => { c.setPointerCapture(ev.pointerId); drag = { x:ev.clientX, y:ev.clientY, yaw:cam.yaw, pitch:cam.pitch, tgt:cam.tgt.slice(), pan:ev.shiftKey || ev.button === 1 }; };
  c.onpointermove = ev => {
    if (!drag) return; const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y;
    if (drag.pan) { const k = cam.dist / (Math.min(c.clientWidth, c.clientHeight) * 1.2), cy = Math.cos(cam.yaw * D2R), sy = Math.sin(cam.yaw * D2R); cam.tgt = [drag.tgt[0] - dx * cy * k, drag.tgt[1] + dx * sy * k, drag.tgt[2] + dy * k]; }
    else { cam.yaw = drag.yaw - dx * 0.4; cam.pitch = Math.max(-89, Math.min(89, drag.pitch + dy * 0.4)); }
    render();
  };
  c.onpointerup = () => { drag = null; };
  c.onwheel = ev => { ev.preventDefault(); cam.dist *= ev.deltaY < 0 ? 0.88 : 1 / 0.88; render(); };
  $('#c3dTop').onclick = () => { cam.yaw = 0; cam.pitch = 89; render(); };
  $('#c3dIso').onclick = () => { cam.yaw = -35; cam.pitch = 30; render(); };
  dlg.showModal(); requestAnimationFrame(render);
  window.CAD_3D = { cam, render, model:M3 };
}

/* ---------- 명령 등록·메뉴 ---------- */
Object.assign(CMDS, {
  DIMSTYLE: () => ({ start() { endCmd(); openDimStyle(); } }),
  DWGOUT: () => ({ start() { endCmd(); exportDWG(); } }),
  XATTACH: () => ({ start() { endCmd(); xattach(); } }),
  PLOT: () => ({ start() { endCmd(); openPlot(); } }),
  VIEW3D: () => ({ start() { endCmd(); open3D(); } }),
  OPEN: () => ({ start() { endCmd(); openDxfIn(); } })
});
Object.assign(CMD_DESC, { DIMSTYLE:'치수 스타일 (글자·화살표·소수 자리)', DIMORDINATE:'좌표 치수', GROUP:'그룹 만들기', UNGROUP:'그룹 풀기', DWGOUT:'DWG로 저장', XATTACH:'외부 참조 붙이기 (DWG·DXF)', PLOT:'출력 (PDF·인쇄, Ctrl+P)', VIEW3D:'3D 보기', OPEN:'도면 열기 (DWG·DXF)', PLINE:'폴리선 (A=호 구간, L=직선, C=닫기)', CIRCLE:'원 (중심→반지름, D=지름, 2P, 3P, T=접선·접선·반지름)' });
{
  const MORE = { D:'DIMSTYLE', DST:'DIMSTYLE', DOR:'DIMORDINATE', G:'GROUP', XA:'XATTACH', PRINT:'PLOT', '3DO':'VIEW3D', '3D':'VIEW3D', OP:'OPEN' };
  Object.assign(DEFAULT_ALIASES, MORE);
  for (const [k, v] of Object.entries(MORE)) if (settings.aliases[k] == null || (k === 'D' && settings.aliases.D === 'DIMTXT')) settings.aliases[k] = v;
  const f = M('파일'), i = f.findIndex(x => Array.isArray(x) && x[1] === 'DXFIN');
  if (i >= 0) f[i] = C('OPEN', '도면 열기 (DWG·DXF)…');
  f.splice(f.findIndex(x => Array.isArray(x) && x[0] === 'DXF로 내보내기') + 1, 0, C('DWGOUT', 'DWG로 저장'), C('PLOT', '출력 (PDF·인쇄)…', 'Ctrl+P'), '-', C('XATTACH', '외부 참조 붙이기…'));
  M('편집').push('-', C('GROUP', '그룹 만들기'), C('UNGROUP', '그룹 풀기'));
  M('보기').push('-', C('VIEW3D', '3D 보기'));
  const dm = M('치수'); dm.splice(dm.findIndex(x => x && x.cmd === 'DIMDIAMETER') + 1, 0, C('DIMORDINATE', '좌표 치수'));
  const di = dm.findIndex(x => x && x.cmd === 'DIMTXT'); if (di >= 0) dm[di] = C('DIMSTYLE', '치수 스타일…');
  const fm = M('형식'), fi = fm.findIndex(x => x && x.cmd === 'DIMTXT'); if (fi >= 0) fm[fi] = C('DIMSTYLE', '치수 스타일…');
  const tb = (txt, title, run) => { const b = document.createElement('button'); b.className = 'ib txt'; b.title = title; b.textContent = txt; b.onclick = () => { b.blur(); run(); }; return b; };
  $('#bDxf').before(tb('열기', '도면 열기 — DWG·DXF', () => startCmd('OPEN')));
  $('#bDxf').after(tb('DWG', 'DWG로 저장 (오토캐드 2018 형식)', () => startCmd('DWGOUT')));
  $('#bPng').after(tb('출력', '출력 — PDF·인쇄 (Ctrl+P)', () => startCmd('PLOT')));
  $('#b3d').after(tb('3D', '3D 보기', () => startCmd('VIEW3D')));
  ICONS.dimord = '<path d="M5 20V8M5 8h14M9 8V4"/><path d="M14 4h6" stroke-dasharray="2 2"/>';
  TB_DRAW.push(['DIMORDINATE', '좌표 치수', 'dimord']);
  document.addEventListener('keydown', ev => { if ((ev.ctrlKey || ev.metaKey) && ev.key.toLowerCase() === 'p' && !document.querySelector('dialog[open]')) { ev.preventDefault(); startCmd('PLOT'); } });
  const IT = TOOL.input_schema.properties.add.items.properties; IT.lx = { type:'number' }; IT.ly = { type:'number' }; IT.axis = { type:'string', enum:['x', 'y'] };
  window.SYS_EXTRA += `
- dimord: 좌표 치수. x,y(재는 점), lx,ly(지시선 끝), axis("x"=X좌표 표기, "y"=Y좌표 표기). 원점은 치수 스타일의 좌표 원점(기본 0,0).`;
}

/* ---------- 파일 넣기: 버튼 · 화면에 끌어다 놓기 · 그림 붙여넣기(Ctrl+V) ----------
   그림(사진·손그림·캡처) → AI 따라 그리기 / PDF → PDF 가져오기 / DWG·DXF → 도면 열기 */
const IMG_RE = /^image\/(png|jpeg|webp|gif|bmp)$/;
const DRAW_ASK = '첨부한 그림을 도면으로 따라 그려줘. 적힌 치수를 그대로 쓰고 치수선도 넣어줘. 적혀 있지 않은 치수는 비율로 추정해서 알려줘.';
async function imageToAttach(f) { // 큰 사진은 긴 변 2000px로 줄여 JPEG로(투명 부분은 흰 바탕)
  const url = URL.createObjectURL(f), img = new Image();
  try { await new Promise((res, rej) => { img.onload = res; img.onerror = () => rej(new Error('그림을 읽지 못했습니다')); img.src = url; }); }
  finally { setTimeout(() => URL.revokeObjectURL(url), 1000); }
  const sc = Math.min(1, 2000 / Math.max(img.naturalWidth, img.naturalHeight)), c = document.createElement('canvas');
  c.width = Math.max(1, Math.round(img.naturalWidth * sc)); c.height = Math.max(1, Math.round(img.naturalHeight * sc));
  const g = c.getContext('2d'); g.fillStyle = '#fff'; g.fillRect(0, 0, c.width, c.height); g.drawImage(img, 0, 0, c.width, c.height);
  return { name:f.name || '붙여넣은 그림', kind:'image', mime:'image/jpeg', data:c.toDataURL('image/jpeg', 0.9).split(',')[1], trace:true, w:c.width, h:c.height };
}
const setInputFile = (inp, f) => { const dt = new DataTransfer(); dt.items.add(f); inp.files = dt.files; };
async function takeFile(f) {
  const n = (f.name || '').toLowerCase();
  try {
    if (/\.(dwg|dxf)$/.test(n)) { openDxfIn(); setInputFile($('#dxfFile'), f); $('#dxfErr').textContent = `${f.name} — 「새 도면으로 열기」 또는 「지금 도면에 추가」를 누르세요`; return; }
    if (n.endsWith('.pdf') || f.type === 'application/pdf') { openPdfImport(); setInputFile($('#pdfFile'), f); $('#pdfFile').dispatchEvent(new Event('change')); return; }
    if (IMG_RE.test(f.type) || /\.(png|jpe?g|webp|gif|bmp)$/.test(n)) {
      attachment = await imageToAttach(f);
      $('#attachName').textContent = '📎 ' + attachment.name; setAI(true);
      if (!qEl.value.trim()) qEl.value = DRAW_ASK;
      qEl.focus(); qEl.setSelectionRange(qEl.value.length, qEl.value.length);
      addMsg('sys', `그림을 붙였습니다: ${attachment.name} (${attachment.w}×${attachment.h})\n요청 문장을 확인·보충하고 「보내기」를 누르면 AI가 따라 그립니다. 기존 도면은 지우지 않고 옆에 추가합니다.`);
      status('그림을 붙였습니다 — 「보내기」를 누르세요');
      return;
    }
    status('넣을 수 없는 파일입니다: ' + (f.name || f.type) + ' (그림·PDF·DWG·DXF만)');
  } catch (err) { addMsg('err', '파일을 넣지 못했습니다: ' + err.message); }
}
window.takeFile = takeFile; // 시험용
(() => {
  // 도구막대 맨 앞 「파일 넣기」 버튼
  const inp = document.createElement('input'); inp.type = 'file'; inp.hidden = true; inp.accept = 'image/*,.pdf,.dwg,.dxf';
  inp.onchange = () => { const f = inp.files[0]; inp.value = ''; if (f) takeFile(f); };
  const b = document.createElement('button'); b.type = 'button'; b.id = 'bPutFile'; b.className = 'ib txt primary';
  b.textContent = '📂 파일 넣기'; b.title = '그림·사진·손그림 → AI가 따라 그림 / PDF → 선 그대로 가져오기 / DWG·DXF → 도면 열기 (화면에 끌어다 놓거나 Ctrl+V로 붙여도 됩니다)';
  b.onclick = () => { b.blur(); inp.click(); };
  $('#toolbar').prepend(b, inp);
  // 화면 어디든 끌어다 놓기
  const ov = document.createElement('div'); ov.id = 'dropOverlay';
  ov.style.cssText = 'position:fixed;inset:0;z-index:50;display:none;align-items:center;justify-content:center;background:#0b1a2acc;border:3px dashed var(--accent);color:#e6f0fb;font-size:20px;text-align:center;line-height:1.7;pointer-events:none';
  ov.innerHTML = '<div><b>여기에 놓으세요</b><br><span style="font-size:15px">그림·사진·손그림 → AI가 따라 그림 · PDF → 선 그대로 가져오기 · DWG·DXF → 도면 열기</span></div>';
  document.body.appendChild(ov);
  let depth = 0; const hasFiles = ev => [...(ev.dataTransfer && ev.dataTransfer.types || [])].includes('Files');
  window.addEventListener('dragenter', ev => { if (!hasFiles(ev)) return; ev.preventDefault(); depth++; ov.style.display = 'flex'; });
  window.addEventListener('dragover', ev => { if (hasFiles(ev)) ev.preventDefault(); });
  window.addEventListener('dragleave', ev => { if (!hasFiles(ev)) return; if (--depth <= 0) { depth = 0; ov.style.display = 'none'; } });
  window.addEventListener('drop', ev => { if (!hasFiles(ev)) return; ev.preventDefault(); depth = 0; ov.style.display = 'none'; const f = ev.dataTransfer.files[0]; if (f) takeFile(f); });
  // 캡처한 그림을 Ctrl+V로 붙여넣기 (그림이 아니면 기존 도면 붙여넣기 그대로)
  document.addEventListener('paste', ev => {
    if (document.querySelector('dialog[open]')) return;
    const it = [...(ev.clipboardData && ev.clipboardData.items || [])].find(x => x.kind === 'file' && IMG_RE.test(x.type));
    if (!it) return;
    ev.preventDefault(); if (cmd && cmd.name === 'PASTECLIP') endCmd();
    const blob = it.getAsFile(); takeFile(new File([blob], '붙여넣은 그림.png', { type:blob.type }));
  });
})();
{ // AI 창 📎: 그림은 줄여서 붙이고(큰 사진은 AI가 안 받음), DWG·DXF도 고를 수 있게. PDF는 예전처럼 AI 첨부
  const fileIn = $('#file'), change0 = fileIn.onchange;
  fileIn.accept = 'image/*,.pdf,.dwg,.dxf'; $('#bAttach').title = '그림·PDF·DWG·DXF 첨부 (그림은 AI가 따라 그림)';
  fileIn.onchange = ev => {
    const f = ev.target.files[0];
    if (f && !(f.type === 'application/pdf' || /\.pdf$/i.test(f.name))) { ev.target.value = ''; takeFile(f); return; }
    change0(ev);
  };
}
CMDS.PUTFILE = () => ({ start() { endCmd(); $('#bPutFile').click(); } });
CMD_DESC.PUTFILE = '파일 넣기 (그림·PDF·DWG·DXF)';
M('파일').splice(1, 0, ['파일 넣기 (그림·PDF·DWG·DXF)…', '끌어다 놓기', () => $('#bPutFile').click()]);

/* ---------- 화면 색 (배경·그림·글자) — 이 브라우저에 저장 ---------- */
settings.view = Object.assign({ bg:'#ffffff', ink:'#000000', text:'', keepDim:true }, settings.view || {}); // 기본: 흰 바탕·그림 검정·치수 그대로(2026-11-23 요청)
const VIEW_PRESETS = {
  paper:{ bg:'#ffffff', ink:'#000000', text:'', keepDim:true, label:'흰 바탕 · 그림 검정 · 치수 그대로' },
  dark:{ bg:'#0f1215', ink:'', text:'', keepDim:true, label:'어두운 바탕 · 레이어 색' },
  gray:{ bg:'#2b3036', ink:'', text:'', keepDim:true, label:'회색 바탕' }
};
const hexLum = h => { const m = /^#([0-9a-f]{6})$/i.exec(h || ''); if (!m) return 0.5; const v = parseInt(m[1], 16); return (0.299 * (v >> 16) + 0.587 * ((v >> 8) & 255) + 0.114 * (v & 255)) / 255; };
const bgLight = () => hexLum(settings.view.bg) > 0.55;
const fitBg = c => { const L = hexLum(c); if (bgLight() && L > 0.75) return '#111111'; if (!bgLight() && L < 0.12) return '#e8e8e8'; return c; }; // 바탕과 비슷해 안 보이는 색만 뒤집음
const isDimLike = e => isDim(e) || ['dimang', 'dimord', 'leader'].includes(e.type) || e.layer === 'dim';
function viewColor(e) {
  const V = settings.view, base = (LAYERS[e.layer] || LAYERS['0']).color;
  if (e.color) return fitBg(e.color); // 객체에 직접 정한 색이 먼저(오토캐드와 같음)
  if (isDimLike(e) && V.keepDim) return fitBg(base);
  if ((e.type === 'text' || e.type === 'mtext') && V.text) return V.text;
  return V.ink || fitBg(base);
}
{
  const drawEnt0 = drawEnt;
  drawEnt = (e, color, dash, width) => drawEnt0(e, color || viewColor(e), dash || (e.lt && LT_DASH[e.lt]) || undefined, width); // 선택·미리보기처럼 색을 정해 부르는 경우는 그대로
  drawGrid = (W, H) => {
    const light = bgLight(), target = 40 / view.s, p = Math.pow(10, Math.floor(Math.log10(target)));
    let step = p * 10; for (const m of [1, 2, 5, 10]) if (p * m >= target) { step = p * m; break; }
    const [x0, y1] = s2w(0, 0), [x1, y0] = s2w(W, H);
    ctx.setLineDash([]); ctx.lineWidth = 1; ctx.strokeStyle = light ? '#e8ebee' : '#1b2127'; ctx.beginPath();
    for (let x = Math.ceil(x0 / step) * step; x <= x1; x += step) { const sx = Math.round(w2s(x, 0)[0]) + .5; ctx.moveTo(sx, 0); ctx.lineTo(sx, H); }
    for (let y = Math.ceil(y0 / step) * step; y <= y1; y += step) { const sy = Math.round(w2s(0, y)[1]) + .5; ctx.moveTo(0, sy); ctx.lineTo(W, sy); }
    ctx.stroke();
    const [ax, ay] = w2s(0, 0); ctx.strokeStyle = light ? '#cfd5da' : '#27333e'; ctx.beginPath(); ctx.moveTo(ax, 0); ctx.lineTo(ax, H); ctx.moveTo(0, ay); ctx.lineTo(W, ay); ctx.stroke();
  };
  drawCrosshair = (W, H) => {
    if (!ptrScreen || ptrType !== 'mouse') return;
    const [x, y] = ptrScreen.map(v => Math.round(v) + .5);
    ctx.setLineDash([]); ctx.lineWidth = 1; ctx.strokeStyle = bgLight() ? '#1c2228cc' : '#e8edf2cc';
    ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.moveTo(x, 0); ctx.lineTo(x, H); ctx.stroke();
    if (!cmd || cmd.selecting) ctx.strokeRect(x - 5, y - 5, 10, 10);
  };
}
function applyView() { cv.style.background = settings.view.bg; store.set('vc.settings', settings); draw(); }
function setView(v) { Object.assign(settings.view, v); applyView(); }
window.setView = setView; // 시험용
function openViewColors() {
  let dlg = $('#dlgView');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgView';
    dlg.innerHTML = '<h2>화면 색</h2><div class="hint">이 브라우저의 화면에만 적용됩니다. 도면 파일·출력(PDF)·DWG 색은 바뀌지 않습니다.</div>' +
      '<div id="vwPre" style="display:flex;flex-direction:column;gap:6px;margin-top:10px"></div>' +
      '<div style="display:grid;grid-template-columns:auto 1fr;gap:8px 12px;align-items:center;margin-top:12px">' +
      '<label for="vwBg" style="margin:0">배경색</label><input type="color" id="vwBg">' +
      '<label for="vwInkSel" style="margin:0">그림 색</label><div style="display:flex;gap:6px"><select id="vwInkSel" style="flex:1"><option value="">레이어 색 그대로</option><option value="#000000">검정</option><option value="#ffffff">흰색</option><option value="custom">직접 고르기</option></select><input type="color" id="vwInk"></div>' +
      '<label for="vwTxtSel" style="margin:0">글자 색</label><div style="display:flex;gap:6px"><select id="vwTxtSel" style="flex:1"><option value="">그림 색과 같게</option><option value="#000000">검정</option><option value="#ffffff">흰색</option><option value="#0050c8">파랑</option><option value="#c80000">빨강</option><option value="custom">직접 고르기</option></select><input type="color" id="vwTxt"></div></div>' +
      '<label><input type="checkbox" id="vwDim"> 치수선·치수 글자는 원래 색 그대로</label>' +
      '<div class="btns"><button id="vwClose" class="primary">닫기</button></div>';
    document.body.appendChild(dlg);
    for (const [k, p] of Object.entries(VIEW_PRESETS)) {
      const b = document.createElement('button'); b.type = 'button'; b.style.cssText = 'display:flex;align-items:center;gap:10px;text-align:left';
      b.innerHTML = `<span style="width:28px;height:18px;border:1px solid #555;border-radius:3px;background:${p.bg};display:inline-flex;align-items:center;justify-content:center;font-size:11px;color:${p.ink || '#e8e8e8'}">가</span><span></span>`;
      b.lastChild.textContent = p.label; b.onclick = () => { const { label, ...v } = p; setView(v); fill(); }; $('#vwPre').appendChild(b);
    }
    const pickSel = (sel, inp, key) => { sel.onchange = () => { if (sel.value === 'custom') { inp.click(); return; } setView({ [key]:sel.value }); fill(); }; inp.oninput = () => { setView({ [key]:inp.value }); sel.value = 'custom'; }; };
    pickSel($('#vwInkSel'), $('#vwInk'), 'ink'); pickSel($('#vwTxtSel'), $('#vwTxt'), 'text');
    $('#vwBg').oninput = ev => setView({ bg:ev.target.value });
    $('#vwDim').onchange = ev => setView({ keepDim:ev.target.checked });
    $('#vwClose').onclick = () => dlg.close();
  }
  const fill = () => {
    const V = settings.view; $('#vwBg').value = V.bg;
    const setSel = (sel, inp, v) => { const has = [...sel.options].some(o => o.value === v); sel.value = has ? v : 'custom'; inp.value = /^#[0-9a-f]{6}$/i.test(v) ? v : '#000000'; };
    setSel($('#vwInkSel'), $('#vwInk'), V.ink); setSel($('#vwTxtSel'), $('#vwTxt'), V.text); $('#vwDim').checked = !!V.keepDim;
  };
  fill(); dlg.showModal();
}
window.applyScreenFromAI = sc => { // AI가 보낸 화면 색(배경·그림·글자) — 이 브라우저 화면에만
  const hex = v => typeof v === 'string' && /^#[0-9a-f]{6}$/i.test(v) ? v.toLowerCase() : null, v = {};
  if (hex(sc.bg)) v.bg = hex(sc.bg);
  if (sc.ink === '' || hex(sc.ink)) v.ink = sc.ink === '' ? '' : hex(sc.ink);
  if (sc.text === '' || hex(sc.text)) v.text = sc.text === '' ? '' : hex(sc.text);
  if (typeof sc.keepDim === 'boolean') v.keepDim = sc.keepDim;
  if (v.bg && v.ink == null && hexLum(v.bg) < 0.45 && hexLum(settings.view.ink || '#e8e8e8') < 0.3) v.ink = ''; // 어두운 바탕인데 그림이 검정이면 안 보이므로 레이어 색으로
  if (v.bg && v.ink == null && hexLum(v.bg) > 0.55 && settings.view.ink && hexLum(settings.view.ink) > 0.7) v.ink = '#000000';
  if (Object.keys(v).length) setView(v);
};
{
  const AP = TOOL.input_schema.properties, col = { type:'string', description:'#rrggbb, 빈 문자열이면 레이어 색 그대로' };
  AP.screen = { type:'object', description:'화면 색 바꾸기(이 브라우저 화면만, 도면 데이터는 그대로). 배경색·바탕색·바닥색·화면 색·선 색·글자 색을 바꿔 달라는 요청은 이것만 쓰고 해치나 도형을 만들지 않는다.', properties:{ bg:col, ink:col, text:col, keepDim:{ type:'boolean', description:'치수는 원래 색 유지' } } };
  window.SYS_EXTRA += `
[화면 색] "배경색(바탕색·바닥색·화면 색)을 검정/흰색으로", "선을 흰색으로", "글자를 빨갛게"처럼 화면 표시 색을 바꾸라는 요청은 screen{bg,ink,text,keepDim}만 보냅니다(#rrggbb). 이때 해치·사각형 등 도형을 추가하지 않습니다. 실제 바닥 마감·재료를 칠해 달라고 분명히 말할 때만 HATCH를 씁니다.`;
}
CMDS.SCREENCOLOR = () => ({ start() { endCmd(); openViewColors(); } });
CMD_DESC.SCREENCOLOR = '화면 색 (배경·그림·글자)';
DEFAULT_ALIASES.BG = 'SCREENCOLOR'; if (settings.aliases.BG == null) settings.aliases.BG = 'SCREENCOLOR';
M('형식').unshift(C('SCREENCOLOR', '화면 색 (배경·그림·글자)…'));
M('보기').push(C('SCREENCOLOR', '화면 색 (배경·그림·글자)…'));
cv.style.background = settings.view.bg;

/* =====================================================================
   3차: 손으로 빨리 고치는 명령 — 더블클릭 편집, 객체별 색·선 종류, 선택 도구, 찾기/바꾸기, 레이어 도구,
        그리기 순서, 중복 제거, 빠른 치수, 호 길이 치수, 중심 표시, 벽·문·창·실 직접 그리기 등
   ===================================================================== */
/* ---------- 객체별 색·선 종류 (도구막대에서 고름, 없으면 레이어를 따름) ---------- */
const LT_DASH = { center:[16, 4, 3, 4], hidden:[8, 5], dashed:[12, 6], phantom:[18, 4, 4, 4, 4, 4] };
const LT_PLOT = { center:'6 1.2 1 1.2', hidden:'2.5 1.2', dashed:'4 2', phantom:'8 1.5 1.5 1.5 1.5 1.5' };
const LT_DXF = { center:'CENTER', hidden:'HIDDEN', dashed:'HIDDEN', phantom:'PHANTOM' };
const COLOR_LIST = [['', '레이어 색'], ['#ff0000', '빨강'], ['#ffff00', '노랑'], ['#00c000', '초록'], ['#00c0ff', '하늘'], ['#0040ff', '파랑'], ['#ff00ff', '자홍'], ['#000000', '검정'], ['#ffffff', '흰색'], ['#808080', '회색']];
function hexToAci(hex) {
  const m = /^#([0-9a-f]{6})$/i.exec(hex || ''); if (!m) return 7;
  const v = parseInt(m[1], 16), r = v >> 16, g = (v >> 8) & 255, b = v & 255;
  return ACI.reduce((best, c) => { const d = (c[1] - r) ** 2 + (c[2] - g) ** 2 + (c[3] - b) ** 2; return d < best[1] ? [c[0], d] : best; }, [7, Infinity])[0];
}
window.dxfEntLayer = e => { const l = Object.assign({}, dxfLayerOf(e)); if (e.color) l.c62 = hexToAci(e.color); if (e.lt && LT_DXF[e.lt]) l.lt6 = LT_DXF[e.lt]; return l; };
let curColor = '', curLt = ''; // 새로 그리는 객체의 색·선 종류('' = 레이어를 따름)
{
  const commit0 = commit;
  commit = (...ents) => { for (const e of ents) { if (curColor && e.color == null && !isDimLike(e)) e.color = curColor; if (curLt && e.lt == null && !isDimLike(e)) e.lt = curLt; } commit0(...ents); };
  const mkSel = (id, title, items, onPick) => {
    const s = document.createElement('select'); s.id = id; s.className = 'tb'; s.title = title;
    for (const [v, t] of items) { const o = document.createElement('option'); o.value = v; o.textContent = t; s.appendChild(o); }
    s.onchange = () => { onPick(s.value); s.blur(); }; return s;
  };
  // 고른 객체가 있으면 그 객체를 바꾸고, 없으면 앞으로 그릴 객체의 색·선 종류로
  const colorSel = mkSel('colorSel', '색 — 고른 객체가 있으면 바꾸고, 없으면 앞으로 그릴 색', [...COLOR_LIST, ['custom', '직접 고르기…']], v => {
    if (v === 'custom') { const i = document.createElement('input'); i.type = 'color'; i.oninput = () => setColor(i.value); i.click(); return; }
    setColor(v);
  });
  const ltSel = mkSel('ltSel', '선 종류 — 고른 객체가 있으면 바꾸고, 없으면 앞으로 그릴 선', [['', '레이어 선'], ['solid', '실선'], ['center', '중심선 ─ ·'], ['hidden', '숨은선 - -'], ['dashed', '파선 ─ ─'], ['phantom', '가상선 ─ · ·']], v => setLt(v));
  $('#layerSel').after(colorSel, ltSel);
  window.setColor = v => {
    if (sel.size) { snapshot(); for (const e of withSel()) { if (v) e.color = v; else delete e.color; } save(); draw(); status(`${sel.size}개 색 → ${v || '레이어 색'}`); colorSel.value = ''; }
    else { curColor = v; status(`앞으로 그릴 색: ${v || '레이어 색'}`); if (![...colorSel.options].some(o => o.value === v)) colorSel.value = 'custom'; }
  };
  window.setLt = v => {
    const val = v === 'solid' ? 'solid' : v;
    if (sel.size) { snapshot(); for (const e of withSel()) { if (val) e.lt = val; else delete e.lt; } save(); draw(); status(`${sel.size}개 선 종류 변경`); ltSel.value = ''; }
    else { curLt = val; status(`앞으로 그릴 선 종류: ${ltSel.options[ltSel.selectedIndex].textContent}`); }
  };
  LT_DASH.solid = []; LT_PLOT.solid = ''; // 레이어가 점선이어도 이 객체는 실선
}

/* ---------- 더블클릭: 글자는 바로 고치고, 나머지는 속성 창 ---------- */
function editTextOf(e) {
  let dlg = $('#dlgEd');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgEd';
    dlg.innerHTML = '<h2 id="edTitle">문자 고치기</h2><div class="hint" id="edHint"></div><textarea id="edBody" style="height:110px;margin-top:8px"></textarea><div class="btns"><button id="edCancel">취소</button><button id="edOk" class="primary">적용</button></div>';
    document.body.appendChild(dlg); $('#edCancel').onclick = () => dlg.close();
    $('#edBody').addEventListener('keydown', ev => { if (ev.key === 'Enter' && (ev.ctrlKey || !$('#edBody').dataset.multi)) { ev.preventDefault(); $('#edOk').click(); } });
  }
  const multi = e.type === 'mtext', key = (e.type === 'room' || e.type === 'slab' || e.type === 'equip') ? 'name' : 'text';
  $('#edTitle').textContent = isDim(e) || e.type === 'dimang' || e.type === 'dimord' ? '치수 글자 고치기' : key === 'name' ? '이름 고치기' : '문자 고치기';
  $('#edHint').textContent = isDim(e) || e.type === 'dimang' || e.type === 'dimord' ? '비우면 실제 치수값이 자동으로 들어갑니다.' : multi ? '여러 줄로 쓸 수 있습니다 (Ctrl+Enter = 적용).' : 'Enter = 적용';
  $('#edBody').dataset.multi = multi ? '1' : ''; $('#edBody').value = e[key] || '';
  $('#edOk').onclick = () => {
    const v = multi ? $('#edBody').value.replace(/\s+$/, '') : $('#edBody').value.replace(/\n/g, ' ').trim();
    snapshot(); if (v) e[key] = v; else if (isDim(e) || e.type === 'dimang' || e.type === 'dimord' || key === 'name') delete e[key]; save(); draw(); dlg.close();
  };
  dlg.showModal(); setTimeout(() => { $('#edBody').focus(); $('#edBody').select(); }, 0);
}
cv.addEventListener('dblclick', ev => {
  if (cmd) return;
  const r = cv.getBoundingClientRect(), e = pick(s2w(ev.clientX - r.left, ev.clientY - r.top)); if (!e) return;
  sel.clear(); sel.add(e.id); setPrompt(); draw();
  if (['text', 'mtext', 'leader', 'dim', 'dimdia', 'dimrad', 'dimang', 'dimord', 'room', 'slab', 'equip'].includes(e.type)) editTextOf(e); else openProps(e, 1);
});
// 속성 창에도 색·선 종류
{
  const op0 = openProps;
  openProps = (e, count) => {
    op0(e, count);
    const f = $('#propForm'), row = (lbl, el) => { const l = document.createElement('label'); l.textContent = lbl; f.append(l, el); };
    const cs = document.createElement('select'); cs.dataset.ext = 'color';
    for (const [v, t] of COLOR_LIST) { const o = document.createElement('option'); o.value = v; o.textContent = t; cs.appendChild(o); }
    if (e.color && !COLOR_LIST.some(c => c[0] === e.color)) { const o = document.createElement('option'); o.value = e.color; o.textContent = e.color; cs.appendChild(o); }
    cs.value = e.color || ''; row('색', cs);
    const ls = document.createElement('select'); ls.dataset.ext = 'lt';
    for (const [v, t] of [['', '레이어 선'], ['solid', '실선'], ['center', '중심선'], ['hidden', '숨은선'], ['dashed', '파선'], ['phantom', '가상선']]) { const o = document.createElement('option'); o.value = v; o.textContent = t; ls.appendChild(o); }
    ls.value = e.lt || ''; row('선 종류', ls);
  };
  $('#propOk').addEventListener('click', () => { // 본체의 적용 다음에 색·선 종류 반영
    const e = propEnt && findEnt(propEnt.id); if (!e) return;
    const c = $('#propForm [data-ext=color]'), l = $('#propForm [data-ext=lt]');
    if (c) { if (c.value) e.color = c.value; else delete e.color; }
    if (l) { if (l.value) e.lt = l.value; else delete e.lt; }
    save(); draw();
  });
}

/* ---------- 선택 도구 · 찾기/바꾸기 · 그리기 순서 · 중복 제거 · 방향 뒤집기 ---------- */
const typeKo = t => TYPE_KO[t] || t;
function openQselect() {
  let dlg = $('#dlgQs');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgQs';
    dlg.innerHTML = '<h2>조건으로 선택</h2><label for="qsType">종류</label><select id="qsType"></select><label for="qsLay">레이어</label><select id="qsLay"></select><label for="qsCol">색</label><select id="qsCol"></select><div class="hint" id="qsCnt"></div><div class="btns"><button id="qsCancel">닫기</button><button id="qsOk" class="primary">선택</button></div>';
    document.body.appendChild(dlg); $('#qsCancel').onclick = () => dlg.close();
  }
  const ents = doc.ents.filter(visible), opt = (s, list) => { s.innerHTML = ''; for (const [v, t] of [['*', '모두'], ...list]) { const o = document.createElement('option'); o.value = v; o.textContent = t; s.appendChild(o); } };
  opt($('#qsType'), [...new Set(ents.map(e => e.type))].map(t => [t, typeKo(t)]));
  opt($('#qsLay'), [...new Set(ents.map(e => e.layer))].map(l => [l, layerLabel(l)]));
  opt($('#qsCol'), [['', '레이어 색(지정 안 함)'], ...[...new Set(ents.map(e => e.color).filter(Boolean))].map(c => [c, c])]);
  const match = () => ents.filter(e => ($('#qsType').value === '*' || e.type === $('#qsType').value) && ($('#qsLay').value === '*' || e.layer === $('#qsLay').value) && ($('#qsCol').value === '*' || (e.color || '') === $('#qsCol').value));
  const upd = () => { $('#qsCnt').textContent = `해당 ${match().length}개`; };
  ['#qsType', '#qsLay', '#qsCol'].forEach(s => { $(s).onchange = upd; }); upd();
  $('#qsOk').onclick = () => { sel.clear(); match().forEach(e => sel.add(e.id)); setPrompt(); draw(); dlg.close(); status(`${sel.size}개 선택`); };
  dlg.showModal();
}
function openFind() {
  let dlg = $('#dlgFind');
  if (!dlg) {
    dlg = document.createElement('dialog'); dlg.id = 'dlgFind';
    dlg.innerHTML = '<h2>찾기 · 바꾸기</h2><div class="hint">문자·여러 줄 문자·지시선·치수 글자·실 이름에서 찾습니다.</div><label for="fdA">찾을 말</label><input type="text" id="fdA"><label for="fdB">바꿀 말</label><input type="text" id="fdB"><div class="hint" id="fdCnt"></div><div class="btns"><button id="fdClose">닫기</button><button id="fdSel">찾아서 선택</button><button id="fdRep" class="primary">모두 바꾸기</button></div>';
    document.body.appendChild(dlg); $('#fdClose').onclick = () => dlg.close();
  }
  const keyOf = e => ['room', 'slab', 'equip'].includes(e.type) ? 'name' : 'text';
  const hits = () => { const a = $('#fdA').value; return a ? doc.ents.filter(e => typeof e[keyOf(e)] === 'string' && e[keyOf(e)].includes(a)) : []; };
  $('#fdA').oninput = () => { $('#fdCnt').textContent = $('#fdA').value ? `${hits().length}개 있음` : ''; };
  $('#fdSel').onclick = () => { sel.clear(); hits().forEach(e => sel.add(e.id)); setPrompt(); zoomSel(); dlg.close(); status(`${sel.size}개 찾음`); };
  $('#fdRep').onclick = () => { const a = $('#fdA').value, b = $('#fdB').value, hs = hits(); if (!a || !hs.length) return; snapshot(); hs.forEach(e => { const k = keyOf(e); e[k] = e[k].split(a).join(b); }); save(); draw(); $('#fdCnt').textContent = `${hs.length}개 바꿨습니다`; };
  $('#fdCnt').textContent = ''; dlg.showModal(); setTimeout(() => $('#fdA').focus(), 0);
}
function zoomSel() { const b = bounds(withSel()); if (!b) return draw(); const r = cv.getBoundingClientRect(), w = Math.max(b[2] - b[0], 1), h = Math.max(b[3] - b[1], 1); view.s = Math.min(r.width / w, r.height / h) * 0.6; view.ox = r.width / 2 - (b[0] + b[2]) / 2 * view.s; view.oy = r.height / 2 + (b[1] + b[3]) / 2 * view.s; draw(); }
const geomKey = e => { const n = JSON.parse(JSON.stringify(e)); delete n.id; return JSON.stringify(n, (k, v) => typeof v === 'number' ? Math.round(v * 100) / 100 : v); };
function overkill(list) { // 똑같은 객체 중복·길이 0인 선 지우기
  const seen = new Set(), rm = new Set();
  for (const e of list) {
    if (e.type === 'line' && Math.hypot(e.x2 - e.x1, e.y2 - e.y1) < 1e-6) { rm.add(e.id); continue; }
    let k = geomKey(e); if (e.type === 'line') { const r = { ...e, x1:e.x2, y1:e.y2, x2:e.x1, y2:e.y1 }; const k2 = geomKey(r); if (k2 < k) k = k2; } // 방향만 다른 선도 같은 선
    if (seen.has(k)) rm.add(e.id); else seen.add(k);
  }
  doc.ents = doc.ents.filter(e => !rm.has(e.id)); rm.forEach(id => sel.delete(id)); return rm.size;
}
window.overkillList = overkill; // 시험용
function qdim(list, loc) { // 고른 객체의 끝점들 사이에 연속 치수(수평 또는 수직)
  const b = bounds(list); if (!b) return 0;
  const horiz = loc[1] > b[3] || loc[1] < b[1] || !(loc[0] > b[2] || loc[0] < b[0]);
  const pts = list.flatMap(e => snapPts(e).filter(s => ['끝점', '중심', '사분점'].includes(s[2]) && (s[2] !== '사분점' || true)).map(s => [s[0], s[1]]));
  const key = p => Math.round((horiz ? p[0] : p[1]) * 10) / 10, by = new Map();
  for (const p of pts) { const k = key(p), cur = by.get(k), dl = horiz ? Math.abs(p[1] - loc[1]) : Math.abs(p[0] - loc[0]); if (!cur || dl < cur[1]) by.set(k, [p, dl]); } // 같은 좌표면 치수선에 가까운 점
  const sorted = [...by.entries()].sort((a, c) => a[0] - c[0]).map(x => x[1][0]);
  let n = 0;
  for (let i = 0; i + 1 < sorted.length; i++) {
    const p = sorted[i], q = sorted[i + 1];
    addEnt(horiz ? { type:'dim', layer:'dim', dir:'h', x1:p[0], y1:p[1], x2:q[0], y2:q[1], off:loc[1] - p[1] } : { type:'dim', layer:'dim', dir:'v', x1:p[0], y1:p[1], x2:q[0], y2:q[1], off:loc[0] - p[0] }); n++;
  }
  return n;
}
window.qdimList = qdim; // 시험용

Object.assign(CMDS, {
  TEXTEDIT: () => ({ start(c) { c.prompt = '고칠 문자·치수를 클릭:'; }, point(c, p, raw) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); endCmd(); if (['text', 'mtext', 'leader', 'dim', 'dimdia', 'dimrad', 'dimang', 'dimord', 'room', 'slab', 'equip'].includes(e.type)) editTextOf(e); else openProps(e, 1); } }),
  COLOR: () => ({ start(c) { c.prompt = '색 — 1빨강 2노랑 3초록 4하늘 5파랑 6자홍 7검정/흰색 8회색, #rrggbb, 또는 L(레이어 색):'; c.rawText = true; },
    text(c, t) { const u = t.trim().toUpperCase(), map = { 1:'#ff0000', 2:'#ffff00', 3:'#00c000', 4:'#00c0ff', 5:'#0040ff', 6:'#ff00ff', 7:bgLight() ? '#000000' : '#ffffff', 8:'#808080' };
      const v = u === 'L' || u === 'BYLAYER' ? '' : map[u] || (/^#[0-9A-F]{6}$/.test(u) ? u.toLowerCase() : null); if (v == null) { status('색을 이해하지 못했습니다: ' + t); return true; } endCmd(); setColor(v); return true; } }),
  LINETYPE: () => ({ start(c) { c.prompt = '선 종류 — S(실선) C(중심선) H(숨은선) D(파선) P(가상선) L(레이어 선):'; },
    text(c, t) { const v = { S:'solid', C:'center', H:'hidden', D:'dashed', P:'phantom', L:'' }[t.trim().toUpperCase()]; if (v == null) return; endCmd(); setLt(v); return true; } }),
  SELECTSIMILAR: () => ({ start(c) { selectStep(c, () => { const ref = withSel(), keys = new Set(ref.map(e => e.type + '|' + e.layer + '|' + (e.color || ''))); doc.ents.filter(visible).forEach(e => { if (keys.has(e.type + '|' + e.layer + '|' + (e.color || ''))) sel.add(e.id); }); endCmd(); status(`비슷한 것 ${sel.size}개 선택`); }, '기준으로 삼을'); } }),
  QSELECT: () => ({ start() { endCmd(); openQselect(); } }),
  FIND: () => ({ start() { endCmd(); openFind(); } }),
  DRAWORDER: () => ({ start(c) { selectStep(c, cc => { cc.prompt = '앞으로(F) / 뒤로(B) <F>:'; cc.def.enter = k => this.go(k, true); cc.def.text = (k, t) => { if (/^[fb]$/i.test(t)) { this.go(k, /f/i.test(t)); return true; } }; }, '순서를 바꿀'); },
    go(k, front) { const s = new Set(sel); snapshot(); const a = doc.ents.filter(e => s.has(e.id)), b = doc.ents.filter(e => !s.has(e.id)); doc.ents = front ? [...b, ...a] : [...a, ...b]; save(); endCmd(); status(front ? '맨 앞으로 보냈습니다' : '맨 뒤로 보냈습니다'); } }),
  OVERKILL: () => ({ start(c) { selectStep(c, () => { snapshot(); const n = overkill(withSel()); save(); endCmd(); status(n ? `중복·길이 0인 객체 ${n}개 지움` : '지울 중복이 없습니다'); }, '중복을 정리할 (Ctrl+A로 전체)'); } }),
  REVERSE: () => ({ start(c) { selectStep(c, () => { snapshot(); let n = 0; for (const e of withSel()) { if (e.pts) { e.pts.reverse(); n++; } else if (e.type === 'line') { [e.x1, e.y1, e.x2, e.y2] = [e.x2, e.y2, e.x1, e.y1]; n++; } } save(); endCmd(); status(`${n}개 방향 뒤집음`); }, '방향을 뒤집을'); } }),
  PASTEORIG: () => ({ start() { endCmd(); if (!clip) return status('복사한 것이 없습니다 (Ctrl+C)'); snapshot(); for (const e of clip.ents) { const n = clone(e); delete n.floor; addEnt(n); } save(); draw(); status(`원래 위치에 ${clip.ents.length}개 붙여넣음`); } }),
  REGEN: () => ({ start() { endCmd(); blockVer++; draw(); status('다시 그렸습니다'); } }),
  // 레이어 도구
  LAYMCUR: () => ({ start(c) { c.prompt = '이 객체의 레이어를 현재 레이어로 — 객체 클릭:'; }, point(c, p, raw) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); curLayer = e.layer; if ([...$('#layerSel').options].some(o => o.value === e.layer)) $('#layerSel').value = e.layer; endCmd(); status(`현재 레이어: ${layerLabel(e.layer)}`); } }),
  LAYOFF: () => ({ start(c) { c.prompt = '끌 레이어의 객체를 클릭 (Enter=끝):'; }, point(c, p, raw) { const e = pick(raw); if (!e) return status('객체를 클릭하세요'); doc.layerProps = doc.layerProps || {}; doc.layerProps[e.layer] = Object.assign({}, doc.layerProps[e.layer], { off:true }); save(); draw(); status(`레이어 끔: ${layerLabel(e.layer)}`); } }),
  LAYON: () => ({ start() { endCmd(); for (const v of Object.values(doc.layerProps || {})) delete v.off; save(); draw(); status('모든 레이어를 켰습니다'); } }),
  LAYISO: () => ({ start(c) { selectStep(c, () => { const keep = new Set(withSel().map(e => e.layer)); doc.layIso = JSON.parse(JSON.stringify(doc.layerProps || {})); doc.layerProps = doc.layerProps || {}; for (const k of Object.keys(LAYERS)) if (!keep.has(k)) doc.layerProps[k] = Object.assign({}, doc.layerProps[k], { off:true }); save(); endCmd(); draw(); status(`레이어 ${keep.size}개만 남김 — LAYUNISO로 되돌림`); }, '남길 레이어의'); } }),
  LAYUNISO: () => ({ start() { endCmd(); if (!doc.layIso) return status('LAYISO로 숨긴 것이 없습니다'); doc.layerProps = doc.layIso; delete doc.layIso; save(); draw(); status('레이어를 되돌렸습니다'); } }),
  // 치수
  QDIM: () => ({ start(c) { selectStep(c, cc => { cc.prompt = '치수선 위치 (위·아래로 두면 가로, 좌·우로 두면 세로):'; cc.def.point = (k, p) => { snapshot(); const n = qdim(withSel(), p); save(); endCmd(); status(`치수 ${n}개 넣음`); }; }, '치수를 넣을'); } }),
  DIMARC: () => ({ start(c) { c.prompt = '호 길이 치수 — 호 클릭:'; },
    point(c, p, raw) { if (!c.e) { const e = pick(raw); if (!e || e.type !== 'arc') return status('호를 클릭하세요'); c.e = e; c.prompt = '치수 위치:'; return; } commit(this.mk(c, p)); endCmd(); },
    mk(c, p) { const e = c.e, len = e.r * norm360(e.a2 - e.a1) * D2R; return { type:'dimang', layer:'dim', cx:e.cx, cy:e.cy, r:Math.max(dist([e.cx, e.cy], p), 1), a1:e.a1, a2:e.a2, text:'⌒' + dimFmt(len) }; },
    preview(c, cur) { return c.e ? [this.mk(c, cur)] : []; } }),
  CENTERMARK: () => ({ start(c) { c.prompt = '중심 표시 — 원·호 클릭 (Enter=끝):'; }, point(c, p, raw) { const e = pick(raw); if (!e || !(e.type === 'circle' || e.type === 'arc' || (e.type === 'column' && e.r))) return status('원이나 호를 클릭하세요'); const L = e.r * 1.25; commit({ type:'line', layer:'center', x1:e.cx - L, y1:e.cy, x2:e.cx + L, y2:e.cy }, { type:'line', layer:'center', x1:e.cx, y1:e.cy - L, x2:e.cx, y2:e.cy + L }); } }),
  // 건축 요소 직접 그리기
  WALL: () => ({
    start(c) { c.t = doc.wallT || 200; c.prompt = `벽 — 두께 ${c.t} (숫자=두께 바꾸기), 첫 점:`; },
    text(c, t) { if (!c.pts.length && NUMRE.test(t) && +t > 0 && +t < 2000) { c.t = doc.wallT = +t; c.prompt = `벽 두께 ${c.t} — 첫 점:`; return true; } if (/^c$/i.test(t) && c.pts.length > 2) { this.seg(c, c.pts[0]); endCmd(); return true; } },
    seg(c, p) { const a = c.pts[c.pts.length - 1], wk = c.t >= 200 ? 'struct' : 'partition'; commit({ type:'wall', layer:wk === 'struct' ? 'struct' : 'wall', wk, x1:a[0], y1:a[1], x2:p[0], y2:p[1], t:c.t }); },
    point(c, p) { if (c.pts.length) this.seg(c, p); c.pts.push(p); c.prompt = `다음 점 (C=닫기, Enter=끝) · 두께 ${c.t}:`; },
    preview(c, cur) { if (!c.pts.length) return []; const a = c.pts[c.pts.length - 1]; return [{ type:'wall', layer:'struct', x1:a[0], y1:a[1], x2:cur[0], y2:cur[1], t:c.t }]; }
  }),
  DOOR: () => ({
    start(c) { c.w = 900; c.prompt = '문 — 경첩 위치 (벽선 위를 클릭):'; },
    point(c, p) {
      if (!c.h) { c.h = p; c.ref = p; c.prompt = '닫힌 문짝 끝 방향(폭은 숫자로도 입력):'; return; }
      if (c.ang == null) { c.ang = angOf(c.h, p); const d = dist(c.h, p); if (d > 100) c.w = d; c.prompt = '열리는 쪽을 클릭:'; return; }
      const u = [Math.cos(c.ang * D2R), Math.sin(c.ang * D2R)], s = crs(u, sub(p, c.h)) >= 0 ? 1 : -1;
      commit({ type:'door', layer:'open', x:c.h[0], y:c.h[1], w:c.w, ang:norm360(c.ang), swing:s }); endCmd();
    },
    text(c, t) { if (c.h && c.ang == null && NUMRE.test(t) && +t > 0) { c.w = +t; c.prompt = `폭 ${t} — 닫힌 문짝 방향을 클릭:`; return true; } },
    preview(c, cur) { if (!c.h) return []; if (c.ang == null) return [{ type:'door', layer:'open', x:c.h[0], y:c.h[1], w:Math.max(dist(c.h, cur), 100), ang:angOf(c.h, cur), swing:1 }]; const u = [Math.cos(c.ang * D2R), Math.sin(c.ang * D2R)]; return [{ type:'door', layer:'open', x:c.h[0], y:c.h[1], w:c.w, ang:c.ang, swing:crs(u, sub(cur, c.h)) >= 0 ? 1 : -1 }]; }
  }),
  WINDOW: () => ({
    start(c) { c.prompt = '창 — 첫 점 (벽선 위):'; },
    point(c, p) { if (!c.pts.length) { c.pts.push(p); c.prompt = '두번째 점 (또는 길이 입력):'; return; } const a = c.pts[0]; commit({ type:'window', layer:'open', x1:a[0], y1:a[1], x2:p[0], y2:p[1], sill:900, wh:1500 }); endCmd(); },
    preview(c, cur) { return c.pts.length ? [{ type:'window', layer:'open', x1:c.pts[0][0], y1:c.pts[0][1], x2:cur[0], y2:cur[1] }] : []; }
  }),
  ROOM: () => ({
    start(c) { c.prompt = '실 — 모서리를 차례로 클릭 (Enter=이름 입력):'; },
    point(c, p) { if (!c.rawText) { c.pts.push(p); c.prompt = `모서리 ${c.pts.length}개 (Enter=이름 입력):`; } },
    enter(c) { if (c.rawText) { this.fin(c, ''); return; } if (c.pts.length < 3) { endCmd(); return status('모서리가 3개 이상 필요합니다'); } c.rawText = true; c.prompt = '실 이름 (예: 사무실, Enter=이름 없이):'; },
    text(c, t) { if (!c.rawText) return; this.fin(c, t.trim()); return true; },
    fin(c, name) { commit({ type:'room', layer:'room', pts:c.pts.slice(), name }); endCmd(); },
    preview(c, cur) { return c.pts.length && !c.rawText ? [{ type:'polyline', layer:'room', pts:[...c.pts, cur], closed:true }] : []; }
  })
});
Object.assign(CMD_DESC, { TEXTEDIT:'문자·치수 글자 고치기 (더블클릭)', COLOR:'객체 색', LINETYPE:'객체 선 종류', SELECTSIMILAR:'비슷한 것 모두 선택', QSELECT:'조건으로 선택', FIND:'찾기·바꾸기',
  DRAWORDER:'그리기 순서 (앞으로/뒤로)', OVERKILL:'중복 객체 정리', REVERSE:'방향 뒤집기', PASTEORIG:'원래 위치에 붙여넣기', REGEN:'다시 그리기', LAYMCUR:'객체 레이어를 현재로', LAYOFF:'클릭한 객체의 레이어 끄기',
  LAYON:'모든 레이어 켜기', LAYISO:'고른 레이어만 남기기', LAYUNISO:'레이어 되돌리기', QDIM:'빠른 치수 (연속)', DIMARC:'호 길이 치수', CENTERMARK:'중심 표시', WALL:'벽 (두께 → 점 연속)', DOOR:'문 (경첩→방향→여는 쪽)', WINDOW:'창 (두 점)', ROOM:'실 (모서리 → 이름)' });
{
  const A = { ED:'TEXTEDIT', DDEDIT:'TEXTEDIT', COL:'COLOR', LT:'LINETYPE', DR:'DRAWORDER', QS:'QSELECT', SS:'SELECTSIMILAR', OK:'OVERKILL', RE:'REGEN', LAYM:'LAYMCUR', DAR:'DIMARC', QD:'QDIM', CM:'CENTERMARK', WA:'WALL', DO:'DOOR', WIN:'WINDOW', RM:'ROOM', PO2:'PASTEORIG' };
  delete A.DO; // DO는 오토캐드에서 도넛 — 문은 DOOR로
  Object.assign(DEFAULT_ALIASES, A); for (const [k, v] of Object.entries(A)) if (settings.aliases[k] == null) settings.aliases[k] = v;
  M('편집').push('-', C('SELECTSIMILAR', '비슷한 것 모두 선택'), C('QSELECT', '조건으로 선택…'), C('FIND', '찾기·바꾸기…'), C('PASTEORIG', '원래 위치에 붙여넣기'));
  M('보기').push(C('REGEN', '다시 그리기'));
  M('그리기').push('-', C('WALL', '벽'), C('DOOR', '문'), C('WINDOW', '창'), C('ROOM', '실'));
  const dm = M('치수'); dm.splice(dm.findIndex(x => x && x.cmd === 'DIMRADIUS'), 0, C('DIMARC', '호 길이 치수')); dm.splice(dm.findIndex(x => x && x.cmd === 'DIMCONTINUE'), 0, C('QDIM', '빠른 치수'), C('CENTERMARK', '중심 표시'));
  M('수정').push('-', C('TEXTEDIT', '문자 고치기', '더블클릭'), C('DRAWORDER', '그리기 순서'), C('OVERKILL', '중복 정리'), C('REVERSE', '방향 뒤집기'));
  M('형식').splice(2, 0, C('COLOR', '색…'), C('LINETYPE', '선 종류…'), '-', C('LAYMCUR', '객체 레이어를 현재로'), C('LAYOFF', '레이어 끄기 (클릭)'), C('LAYISO', '레이어 하나만 남기기'), C('LAYUNISO', '레이어 되돌리기'), C('LAYON', '모든 레이어 켜기'), '-');
  Object.assign(ICONS, { wall:'<path d="M3 9h18M3 15h18"/><path d="M3 9v6M21 9v6"/>', door:'<path d="M5 20V6"/><path d="M5 6a14 14 0 0 1 14 14H5"/>', win:'<path d="M3 9h18M3 15h18M3 12h18M3 9v6M21 9v6"/>', room:'<rect x="4" y="5" width="16" height="14" stroke-dasharray="3 2"/><path d="M9 12h6"/>', qdim:'<path d="M3 7v10M9 7v10M15 7v10M21 7v10M3 12h18"/>' });
  TB_DRAW.unshift(['WALL', '벽', 'wall'], ['DOOR', '문', 'door'], ['WINDOW', '창', 'win'], ['ROOM', '실', 'room'], '-');
  TB_DRAW.splice(TB_DRAW.findIndex(x => x[0] === 'DIMLINEAR') + 1, 0, ['QDIM', '빠른 치수', 'qdim']);
}

{ // 전체보기를 했는데 보일 것이 없으면 이유를 알려줌(빈 화면만 보여 당황하지 않게)
  const zx0 = zoomExtents;
  zoomExtents = () => {
    zx0();
    const all = doc.ents.filter(e => !layerOff(e)), here = all.filter(e => !e.floor || e.floor === doc.cur);
    if (!doc.ents.length) status('이 브라우저에 저장된 도면이 비어 있습니다 — 다른 PC에서 그렸다면 「서버 도면」에서 불러오세요');
    else if (!all.length) status('모든 레이어가 꺼져 있습니다 — 형식 → 레이어에서 켜세요');
    else if (!here.length) status(`이 층에는 그린 것이 없습니다 — 위쪽 층 탭에서 다른 층을 고르세요`);
  };
}
buildToolbars(); buildMenus(); buildHelp();
ensureUserLayers();
/* ---------- 리본 화면 배치 (CAD식: 빠른 실행 · 리본 탭/패널 · 도면 탭 · 방위 표시 · 떠 있는 명령줄 · 모형/층 탭) ----------
   배치 관례만 따르고 아이콘·디자인은 직접 그림. 예전 도구막대(#toolbar·#tbDraw·#tbModify)는 숨겨 두고 그대로 둠(버튼 동작 재사용). */
(() => {
  Object.assign(ICONS, {
    point:'<circle cx="12" cy="12" r="2.2" fill="currentColor"/><path d="M12 4v4M12 16v4M4 12h4M16 12h4"/>',
    donut:'<circle cx="12" cy="12" r="8"/><circle cx="12" cy="12" r="4"/>',
    revcloud:'<path d="M6 16a3 3 0 0 1 0-6 4 4 0 0 1 7-3 3.5 3.5 0 0 1 5 3 3 3 0 0 1 0 6z"/>',
    ray:'<path d="M4 18 20 6"/><circle cx="4" cy="18" r="1.6" fill="currentColor"/>',
    brush:'<path d="M14 4l6 6-7 7-6-6z"/><path d="M7 11l-3 3c-1 1-1 4-1 6 2 0 5 0 6-1l3-3"/>',
    paste:'<rect x="5" y="5" width="14" height="16" rx="1"/><path d="M9 5V3h6v2M8 11h8M8 15h6"/>',
    cut:'<circle cx="7" cy="17" r="3"/><circle cx="17" cy="17" r="3"/><path d="M9 15 18 3M15 15 6 3"/>',
    group:'<rect x="3" y="3" width="18" height="18" stroke-dasharray="3 2"/><rect x="6" y="6" width="5" height="5"/><circle cx="15.5" cy="15.5" r="3"/>',
    ungroup:'<rect x="5" y="5" width="6" height="6"/><circle cx="16" cy="16" r="3.5"/><path d="M3 21 21 3" stroke-dasharray="2 2"/>',
    xref:'<path d="M6 3h8l4 4v14H6z"/><path d="M9 13h6M12 10l3 3-3 3"/>',
    purge:'<path d="M5 7h14M10 7V4h4v3M7 7l1 13h8l1-13"/>',
    layoff:'<path d="m12 3 9 5-9 5-9-5z"/><path d="M4 20 20 4"/>',
    layon:'<path d="m12 3 9 5-9 5-9-5z"/><path d="m3 13 9 5 9-5"/><path d="m3 17.5 9 5 9-5"/>',
    layiso:'<path d="m12 3 9 5-9 5-9-5z" fill="currentColor" fill-opacity=".35"/><path d="m3 13 9 5 9-5" stroke-dasharray="2 2"/>',
    laycur:'<path d="m12 3 9 5-9 5-9-5z"/><path d="m8 16 3 3 6-6"/>',
    find:'<circle cx="10" cy="10" r="6"/><path d="m15 15 6 6M7.5 10h5"/>',
    qsel:'<path d="M4 4l7 16 2-7 7-2z"/>',
    sim:'<rect x="3" y="6" width="8" height="8"/><rect x="13" y="10" width="8" height="8"/><path d="M11 10h2"/>',
    order:'<rect x="3" y="3" width="11" height="11"/><rect x="10" y="10" width="11" height="11" fill="currentColor" fill-opacity=".25"/>',
    overkill:'<path d="M3 9h18M3 13h18"/><path d="m8 4 8 14" />',
    reverse:'<path d="M4 9h14l-3-3M20 15H6l3 3"/>',
    regen:'<path d="M20 12a8 8 0 1 1-2.3-5.7"/><path d="M20 4v4h-4"/><circle cx="12" cy="12" r="2"/>',
    plot:'<path d="M7 9V3h10v6"/><rect x="3" y="9" width="18" height="8" rx="1"/><path d="M7 14h10v7H7z"/>',
    dwg:'<path d="M6 3h8l4 4v14H6z"/><text x="12" y="17" font-size="6" text-anchor="middle" style="fill:currentColor;stroke:none;font-weight:700">DWG</text>',
    dxf:'<path d="M6 3h8l4 4v14H6z"/><text x="12" y="17" font-size="6" text-anchor="middle" style="fill:currentColor;stroke:none;font-weight:700">DXF</text>',
    png:'<path d="M6 3h8l4 4v14H6z"/><text x="12" y="17" font-size="6" text-anchor="middle" style="fill:currentColor;stroke:none;font-weight:700">PNG</text>',
    pdfin:'<path d="M6 3h8l4 4v14H6z"/><text x="12" y="17" font-size="6" text-anchor="middle" style="fill:currentColor;stroke:none;font-weight:700">PDF</text>',
    putfile:'<path d="M3 7h6l2 2h10v10H3z"/><path d="M12 17v-6M9.5 13.5 12 11l2.5 2.5"/>',
    floor:'<path d="M3 20h18M5 20v-5h14v5M7 15v-5h10v5M9 10V5h6v5"/>',
    color:'<circle cx="12" cy="12" r="9"/><path d="M12 3a9 9 0 0 1 0 18z" fill="currentColor" fill-opacity=".5"/>',
    grid:'<path d="M4 4h16v16H4zM4 9.3h16M4 14.6h16M9.3 4v16M14.6 4v16"/>',
    ai:'<path d="M12 3v3M12 18v3M5 12H3M21 12h-2"/><rect x="7" y="7" width="10" height="10" rx="2"/><path d="M10 11h.01M14 11h.01M10 14h4"/>',
    menu:'<path d="M4 6h16M4 12h16M4 18h16"/>',
    tedit:'<path d="M5 20 11 4l6 16M7.5 14h7"/><path d="m16 8 4-4" />',
    cmark:'<circle cx="12" cy="12" r="7"/><path d="M12 2v20M2 12h20" stroke-dasharray="3 2"/>',
    dimarc:'<path d="M4 18a9 9 0 0 1 16 0"/><path d="M3 12a10 10 0 0 1 18 0" stroke-dasharray="2 2"/>',
    dimcont:'<path d="M3 7v10M10 7v10M17 7v10M3 12h14"/>',
    dimbase:'<path d="M3 5v14M12 9v10M20 13v6M3 10h9M3 15h17"/>',
    dimstyle:'<path d="M4 6v12M20 6v12M4 12h16"/><circle cx="12" cy="7" r="2.5"/>',
    lengthen:'<path d="M3 12h12M19 8v8M15 9l3 3-3 3"/>',
    align:'<path d="M4 20 10 8M14 20l6-12" /><path d="M4 20h16" stroke-dasharray="2 2"/>',
    divide:'<path d="M3 12h18M7.5 9v6M12 9v6M16.5 9v6"/>',
    pedit:'<path d="M3 19 8 8l6 7 7-11"/><circle cx="8" cy="8" r="1.6" fill="currentColor"/>',
    osnap:'<rect x="8" y="8" width="8" height="8"/><path d="M12 3v5M12 16v5M3 12h5M16 12h5"/>',
    breakpt:'<path d="M3 12h8M13 12h8"/><circle cx="12" cy="12" r="1.6" fill="currentColor"/>'
  });
  const st = document.createElement('style');
  st.textContent = `
#toolbar,#tbDraw,#tbModify{display:none!important}
body.oldbars #toolbar{display:flex!important} body.oldbars #tbDraw,body.oldbars #tbModify{display:flex!important}
body.nomenu #menubar{display:none}
#titlebar{height:30px;gap:4px;padding:0 6px;background:#0d1013}
#titlebar .qa{width:26px;height:24px}
#titlebar .qa svg{width:16px;height:16px}
#titlebar .ttl{flex:1;text-align:center;color:var(--text);overflow:hidden;text-overflow:ellipsis}
#titlebar .ttl small{color:var(--muted);font-weight:400}
#titlebar .hint2{display:none}
#ribbon{background:#22272e;border-bottom:1px solid var(--line);user-select:none;flex:none}
#rbTabs{display:flex;align-items:flex-end;gap:1px;padding:2px 6px 0;background:#1a1e23;border-bottom:1px solid #39414b}
#rbTabs .rt{background:none;border:1px solid transparent;border-bottom:0;border-radius:4px 4px 0 0;padding:4px 14px;font-size:13px;color:#c7ced6}
#rbTabs .rt:hover{background:#2a3038}
#rbTabs .rt.on{background:#22272e;border-color:#39414b;color:#fff;margin-bottom:-1px;padding-bottom:5px;box-shadow:inset 0 2px 0 var(--accent)}
#rbTabs .rmin{margin-left:auto;background:none;border:0;padding:2px 8px;font-size:12px;color:var(--muted)}
#rbBody{display:flex;align-items:stretch;overflow-x:auto;overflow-y:hidden;scrollbar-width:thin;scrollbar-color:#46505c #1d2126;min-height:96px}
#ribbon.min #rbBody{display:none}
.rp{display:flex;flex-direction:column;border-right:1px solid #343b44;flex:none;position:relative}
.rp-b{flex:1;display:flex;align-items:flex-start;gap:2px;padding:3px 5px 0}
.rp-t{height:19px;display:flex;align-items:center;justify-content:center;gap:4px;font-size:11.5px;color:#9aa5b1;background:#1d2126;border-top:1px solid #2c323a;cursor:default;white-space:nowrap;padding:0 6px}
.rp-t.more{cursor:pointer}
.rp-t.more:hover{background:#2a3038;color:#fff}
.rbig{display:flex;flex-direction:column;align-items:center;justify-content:flex-start;gap:2px;width:auto;min-width:46px;height:70px;padding:4px 3px 0;background:none;border:1px solid transparent;border-radius:4px;font-size:12px;line-height:1.15;color:#dfe5eb;text-align:center;white-space:nowrap}
.rbig svg{width:30px;height:30px}
.rcol{display:flex;flex-direction:column;gap:1px}
.rsm{display:flex;align-items:center;gap:5px;height:22px;padding:0 6px 0 3px;background:none;border:1px solid transparent;border-radius:3px;font-size:12px;color:#dfe5eb;white-space:nowrap;text-align:left}
.rsm svg{width:16px;height:16px;flex:none}
.rsm.ic{padding:0 3px}
.rbig:hover,.rsm:hover{background:#2f3742;border-color:#46505c}
.rbig svg,.rsm svg{fill:none;stroke:currentColor;stroke-width:1.6;stroke-linecap:round;stroke-linejoin:round}
.rbig.on,.rsm.on{background:#264a6e;border-color:var(--accent)}
.rrow{display:flex;gap:1px;align-items:center}
.rp select{height:22px;padding:0 4px;font-size:12px;background:#15181c;color:var(--text);border:1px solid #39414b;border-radius:3px;max-width:150px}
.rp-fly{position:absolute;top:100%;left:0;z-index:30;min-width:190px;background:#22272e;border:1px solid #39414b;border-radius:0 0 6px 6px;box-shadow:0 8px 24px #0009;padding:4px;display:none;flex-direction:column;gap:1px}
.rp.open .rp-fly{display:flex}
.rp-fly .rsm{width:100%}
#docTabs{display:flex;align-items:flex-end;gap:2px;padding:3px 6px 0;background:#15181c;border-bottom:1px solid var(--line);flex:none}
#docTabs .dt{display:flex;align-items:center;gap:8px;padding:4px 10px;font-size:12.5px;background:#1d2126;border:1px solid var(--line);border-bottom:0;border-radius:4px 4px 0 0;color:var(--muted)}
#docTabs .dt.on{background:#262c33;color:var(--text);box-shadow:inset 0 2px 0 var(--accent)}
#docTabs .dt.add{cursor:pointer;padding:4px 9px}
#docTabs .dt.add:hover{color:#fff}
#vpLabel{position:absolute;top:6px;left:8px;z-index:5;display:flex;gap:2px;font-size:12px;font-family:system-ui,"Malgun Gothic",sans-serif}
#vpLabel button{background:#1d2126cc;border:1px solid #39414b;border-radius:3px;padding:1px 6px;font-size:12px;color:#cfe3ff}
#vpLabel button:hover{background:#2f3742}
#compass{position:absolute;top:8px;right:12px;z-index:5;width:96px;height:96px;cursor:pointer}
#compass text{font-size:11px;font-family:system-ui,"Malgun Gothic",sans-serif;text-anchor:middle;dominant-baseline:central}
#lawbox{top:112px}
#stage #cmdwin{position:absolute;left:50%;bottom:10px;transform:translateX(-50%);width:min(820px,calc(100% - 24px));z-index:6;background:none;border:0;pointer-events:none}
#stage #cmdhist{height:auto;max-height:62px;margin-bottom:2px;padding:2px 8px;background:#14171bcc;border-radius:4px 4px 0 0;color:#b9c3cd;pointer-events:auto}
#stage #cmdhist:empty{display:none}
#stage #cmdbar{border:1px solid #46505c;border-radius:4px;background:#1b1f24f2;box-shadow:0 4px 14px #0007;pointer-events:auto;flex-wrap:nowrap}
#stage #cmdbar::before{content:"⌨";color:var(--muted);font-size:13px;padding:0 2px}
#statusbar{padding:2px 6px;gap:3px;background:#1a1e23;flex-wrap:nowrap;overflow-x:auto;scrollbar-width:thin}
#statusbar button{padding:2px 8px;font-size:12px;border-radius:3px;background:none;border-color:transparent;white-space:nowrap;flex:none}
#statusbar button:hover{background:#2a3038;border-color:#39414b}
#statusbar button.on{background:#264a6e;border-color:#3a6c9c;color:#fff}
#statusbar .lt{border:1px solid #39414b;border-bottom:0;background:#22272e;border-radius:3px 3px 0 0}
#statusbar .lt.on{background:#2f3742;box-shadow:inset 0 2px 0 var(--accent)}
#statusbar #floorbar{padding:0 4px;border:0;background:none;flex-wrap:nowrap;border-left:1px solid #39414b;margin-left:4px}
#statusbar #floorbar .lv{padding:2px 9px}
#statusbar #floorbar .meta{white-space:nowrap}
#statusbar #coords{min-width:140px;text-align:right}
#statusbar .ssep{width:1px;height:18px;background:#39414b;flex:none;margin:0 3px}
@media (max-width:820px){ #compass{width:70px;height:70px} #rbBody{height:92px} #statusbar{flex-wrap:wrap} }
`;
  document.head.appendChild(st);

  const ic = k => `<svg viewBox="0 0 24 24" aria-hidden="true">${ICONS[k] || ICONS.list}</svg>`;
  const aliasOf = name => Object.keys(settings.aliases).find(k => settings.aliases[k] === name);
  const clickEl = sel => () => { const el = $(sel); if (el) el.click(); };
  const ctrlKey = k => () => document.dispatchEvent(new KeyboardEvent('keydown', { key:k, ctrlKey:true, bubbles:true }));
  /* 항목: [라벨, 아이콘, 명령 이름 또는 함수, 켜짐 확인 함수(선택)] */
  const C = (cmdName, label, icn) => ({ label, icn, run:() => startCmd(cmdName), cmd:cmdName });
  const F = (fn, label, icn, chk) => ({ label, icn, run:fn, chk });
  const T = {
    '홈':[
      { t:'그리기', cols:[C('LINE', '선', 'line'), C('PLINE', '폴리선', 'pline'), C('CIRCLE', '원', 'circle'), C('ARC', '호', 'arc'),
        [C('RECTANG', '사각형', 'rect'), C('POLYGON', '다각형', 'polygon'), C('ELLIPSE', '타원', 'ellipse')],
        [C('HATCH', '해치', 'hatch'), C('SPLINE', '스플라인', 'spline'), C('XLINE', '무한선', 'xline')]],
        more:[C('RAY', '광선', 'ray'), C('POINT', '점', 'point'), C('DONUT', '도넛', 'donut'), C('REVCLOUD', '구름형 수정 기호', 'revcloud'), C('DIVIDE', '등분할', 'divide'), C('MEASURE', '길이 분할', 'divide')] },
      { t:'수정', cols:[
        [C('MOVE', '이동', 'move'), C('COPY', '복사', 'copy'), C('STRETCH', '신축', 'stretch')],
        [C('ROTATE', '회전', 'rotate'), C('MIRROR', '대칭', 'mirror'), C('SCALE', '축척', 'scale')],
        [C('TRIM', '자르기', 'trim'), C('FILLET', '모깎기', 'fillet'), C('ARRAY', '배열', 'array')],
        [C('ERASE', '지우기', 'erase'), C('OFFSET', '간격띄우기', 'offset'), C('EXPLODE', '분해', 'explode')]],
        more:[C('EXTEND', '연장', 'extend'), C('CHAMFER', '모따기', 'chamfer'), C('BREAK', '끊기', 'break_'), C('BREAKATPOINT', '점에서 끊기', 'breakpt'), C('JOIN', '결합', 'join'), C('LENGTHEN', '길이 조정', 'lengthen'), C('ALIGN', '정렬', 'align'), C('PEDIT', '폴리선 편집', 'pedit'), C('REVERSE', '방향 뒤집기', 'reverse'), C('OVERKILL', '중복 정리', 'overkill'), C('DRAWORDER', '그리기 순서', 'order')] },
      { t:'주석', cols:[C('TEXT', '문자', 'text'), C('DIMLINEAR', '치수', 'dimlin'),
        [C('QLEADER', '지시선', 'leader'), C('QDIM', '빠른 치수', 'qdim'), C('DIMSTYLE', '치수 스타일', 'dimstyle')]],
        more:[C('MTEXT', '여러 줄 문자', 'mtext'), C('TEXTEDIT', '문자 고치기', 'tedit'), C('DIMALIGNED', '정렬 치수', 'dimali'), C('DIMANGULAR', '각도 치수', 'dimang'), C('DIMRADIUS', '반지름 치수', 'dimrad'), C('DIMDIAMETER', '지름 치수', 'dimdia'), C('DIMARC', '호 길이 치수', 'dimarc'), C('DIMORDINATE', '좌표 치수', 'dimord'), C('DIMCONTINUE', '연속 치수', 'dimcont'), C('DIMBASELINE', '기준선 치수', 'dimbase'), C('CENTERMARK', '중심 표시', 'cmark')] },
      { t:'도면층', cols:[C('LAYER', '도면층\n특성', 'layer'), { el:'layer' }] },
      { t:'블록', cols:[C('INSERT', '삽입', 'block'), [C('BLOCK', '작성', 'block'), C('XATTACH', '외부 참조', 'xref'), C('PURGE', '정리', 'purge')]] },
      { t:'특성', cols:[C('MATCHPROP', '특성\n일치', 'brush'), { el:'props' }] },
      { t:'그룹', cols:[C('GROUP', '그룹', 'group'), [C('UNGROUP', '그룹 해제', 'ungroup')]] },
      { t:'유틸리티', cols:[C('DIST', '측정', 'dist'), [C('AREA', '면적', 'area'), C('LIST', '정보', 'list'), C('ID', '좌표', 'point')], [C('SELECTALL', '모두 선택', 'all'), C('QSELECT', '빠른 선택', 'qsel'), C('FIND', '찾기', 'find')]] },
      { t:'클립보드', cols:[C('PASTECLIP', '붙여넣기', 'paste'), [F(ctrlKey('c'), '복사', 'copy'), F(ctrlKey('x'), '잘라내기', 'cut'), C('PASTEORIG', '원위치 붙여넣기', 'paste')]] }
    ],
    '삽입':[
      { t:'파일', cols:[F(clickEl('#bPutFile'), '파일\n넣기', 'putfile'), F(() => openPdfImport(), 'PDF→\nCAD', 'pdfin'), C('OPEN', '도면 열기\nDWG·DXF', 'open'), [C('XATTACH', '외부 참조', 'xref')]] },
      { t:'블록', cols:[C('INSERT', '삽입', 'block'), [C('BLOCK', '블록 작성', 'block'), C('PURGE', '정리', 'purge'), C('EXPLODE', '분해', 'explode')]] },
      { t:'참조', cols:[[C('PDFSCALE', 'PDF 축척 맞추기', 'dimlin'), F(clickEl('#bSrvOpen'), '서버 도면 열기', 'open')]] }
    ],
    '주석':[
      { t:'문자', cols:[C('MTEXT', '여러 줄\n문자', 'mtext'), [C('TEXT', '한 줄 문자', 'text'), C('TEXTEDIT', '문자 고치기', 'tedit'), C('FIND', '찾기·바꾸기', 'find')], [C('DIMTXT', '치수 글자 크기', 'dimstyle')]] },
      { t:'치수', cols:[C('DIMLINEAR', '선형', 'dimlin'), C('QDIM', '빠른\n치수', 'qdim'),
        [C('DIMALIGNED', '정렬', 'dimali'), C('DIMANGULAR', '각도', 'dimang'), C('DIMARC', '호 길이', 'dimarc')],
        [C('DIMRADIUS', '반지름', 'dimrad'), C('DIMDIAMETER', '지름', 'dimdia'), C('DIMORDINATE', '좌표', 'dimord')],
        [C('DIMCONTINUE', '연속', 'dimcont'), C('DIMBASELINE', '기준선', 'dimbase'), C('DIMSTYLE', '치수 스타일', 'dimstyle')]] },
      { t:'지시선', cols:[C('QLEADER', '지시선', 'leader')] },
      { t:'표시', cols:[C('CENTERMARK', '중심\n표시', 'cmark'), [C('REVCLOUD', '구름형 수정 기호', 'revcloud'), C('HATCH', '해치', 'hatch')]] }
    ],
    '건축':[
      { t:'요소', cols:[C('WALL', '벽', 'wall'), C('DOOR', '문', 'door'), C('WINDOW', '창', 'win'), C('ROOM', '실', 'room')] },
      { t:'층', cols:[F(() => editLevel(null), '층\n추가', 'floor'), [F(() => { const l = lvOf(doc.cur); if (l) editLevel(l); }, '지금 층 수정·삭제', 'floor')]] },
      { t:'도면', cols:[F(clickEl('#bSheet'), '도곽·\n표제란', 'sheet'), F(clickEl('#bViews'), '입면·\n단면', 'views'), C('VIEW3D', '3D\n보기', 'cube'), [F(clickEl('#b3d'), '3D용 내보내기', 'cube')]] }
    ],
    '뷰':[
      { t:'탐색', cols:[F(clickEl('#bZoom'), '전체\n보기', 'zext'), [F(clickEl('#bZin'), '확대', 'zin'), F(clickEl('#bZout'), '축소', 'zout'), C('REGEN', '다시 그리기', 'regen')]] },
      { t:'화면', cols:[C('SCREENCOLOR', '화면 색', 'color'), [F(clickEl('#tGrid'), '그리드 (F7)', 'grid', () => gridOn), F(clickEl('#tOrtho'), '직교 (F8)', 'rect', () => $('#tOrtho').classList.contains('on')), F(clickEl('#tSnap'), '객체 스냅 (F3)', 'osnap', () => $('#tSnap').classList.contains('on'))]] },
      { t:'창', cols:[F(clickEl('#tAI'), 'AI\n도우미', 'ai', () => !$('#aiPanel').classList.contains('hide')), [F(() => setBars('nomenu'), '메뉴 막대', 'menu', () => !document.body.classList.contains('nomenu')), F(() => setBars('oldbars'), '예전 도구막대', 'props', () => document.body.classList.contains('oldbars')), F(() => setRibbonMin(!rb.classList.contains('min')), '리본 접기', 'zout', () => rb.classList.contains('min'))]] },
      { t:'3D', cols:[C('VIEW3D', '3D 보기', 'cube')] }
    ],
    '관리':[
      { t:'설정', cols:[F(clickEl('#bSet'), '설정', 'gear'), F(clickEl('#bHelp'), '명령어\n목록', 'help'), [C('OSNAP', '스냅·극좌표 설정', 'osnap'), C('DIMSTYLE', '치수 스타일', 'dimstyle'), C('SCREENCOLOR', '화면 색', 'color')]] },
      { t:'정리', cols:[C('OVERKILL', '중복\n정리', 'overkill'), [C('PURGE', '안 쓰는 블록 정리', 'purge'), C('DRAWORDER', '그리기 순서', 'order'), C('REVERSE', '방향 뒤집기', 'reverse')]] },
      { t:'선택', cols:[[C('QSELECT', '조건으로 선택', 'qsel'), C('SELECTSIMILAR', '비슷한 것 선택', 'sim'), C('FIND', '찾기·바꾸기', 'find')]] }
    ],
    '출력':[
      { t:'출력', cols:[C('PLOT', '출력\n(PDF)', 'plot'), F(clickEl('#bPng'), 'PNG\n그림', 'png')] },
      { t:'내보내기', cols:[F(clickEl('#bDxf'), 'DXF', 'dxf'), C('DWGOUT', 'DWG', 'dwg'), F(clickEl('#b3d'), '3D용\nJSON', 'cube')] },
      { t:'서버', cols:[F(clickEl('#bSrvSave'), '서버\n저장', 'save'), F(clickEl('#bSrvOpen'), '서버\n열기', 'open'), [F(clickEl('#bNew'), '새 도면', 'new')]] }
    ]
  };

  const chkers = [];
  function mkBtn(it, cls) {
    const b = document.createElement('button'); b.type = 'button'; b.className = cls;
    const al = it.cmd ? aliasOf(it.cmd) : null, plain = it.label.replace(/\n/g, ' ');
    b.innerHTML = ic(it.icn) + '<span></span>'; b.lastChild.textContent = cls === 'rbig' ? it.label : plain;
    if (cls === 'rbig') b.lastChild.style.whiteSpace = 'pre';
    b.title = plain + (al ? ` (${al})` : it.cmd ? ` (${it.cmd})` : '');
    b.onclick = () => { b.blur(); rb.querySelectorAll('.rp.open').forEach(p => p.classList.remove('open')); it.run(); setTimeout(() => { refreshChk(); if (it.cmd && !document.querySelector('dialog[open]')) $('#cmd').focus(); }, 30); };
    if (it.chk) chkers.push([b, it.chk]);
    return b;
  }
  function refreshChk() { for (const [b, f] of chkers) { try { b.classList.toggle('on', !!f()); } catch (e) {} } }
  window.ribbonRefresh = refreshChk;

  const rb = document.createElement('div'); rb.id = 'ribbon';
  rb.innerHTML = '<div id="rbTabs" role="tablist"></div><div id="rbBody"></div>';
  $('#toolbar').before(rb);
  const tabsEl = rb.firstChild, body = rb.lastChild, panes = {};
  /* 도면층·특성 패널의 고르기 상자는 예전 도구막대에서 옮겨 옴(동작 그대로) */
  function elBlock(kind) {
    const box = document.createElement('div'); box.className = 'rcol'; box.style.paddingTop = '2px';
    if (kind === 'layer') {
      const sel = $('#layerSel'); if (sel) { sel.className = ''; sel.title = '현재 도면층'; box.appendChild(sel); }
      const row = document.createElement('div'); row.className = 'rrow';
      for (const it of [C('LAYOFF', '선택한 것의 도면층 끄기', 'layoff'), C('LAYISO', '선택한 도면층만 보기', 'layiso'), C('LAYUNISO', '분리 해제', 'layon'), C('LAYON', '모두 켜기', 'layon'), C('LAYMCUR', '선택한 것의 도면층을 현재로', 'laycur')]) {
        const b = mkBtn(it, 'rsm ic'); b.lastChild.remove(); row.appendChild(b);
      }
      box.appendChild(row);
    } else {
      for (const id of ['#colorSel', '#ltSel']) { const s = $(id); if (s) { s.className = ''; box.appendChild(s); } }
      box.appendChild(mkBtn(C('PROPERTIES', '속성 (Ctrl+1)', 'props'), 'rsm'));
    }
    return box;
  }
  for (const [name, panels] of Object.entries(T)) {
    const tb = document.createElement('button'); tb.type = 'button'; tb.className = 'rt'; tb.textContent = name; tb.setAttribute('role', 'tab');
    tb.onclick = () => showTab(name); tb.ondblclick = () => setRibbonMin(!rb.classList.contains('min'));
    tabsEl.appendChild(tb);
    const pane = document.createElement('div'); pane.style.display = 'contents'; panes[name] = [tb, pane];
    for (const p of panels) {
      const pd = document.createElement('div'); pd.className = 'rp';
      const pb = document.createElement('div'); pb.className = 'rp-b';
      for (const col of p.cols) {
        if (col.el) { pb.appendChild(elBlock(col.el)); continue; }
        if (Array.isArray(col)) { const c = document.createElement('div'); c.className = 'rcol'; for (const it of col) c.appendChild(mkBtn(it, 'rsm')); pb.appendChild(c); continue; }
        pb.appendChild(mkBtn(col, 'rbig'));
      }
      const pt = document.createElement('div'); pt.className = 'rp-t'; pt.textContent = p.t;
      pd.append(pb, pt);
      if (p.more) {
        pt.classList.add('more'); pt.textContent = p.t + ' ▾'; pt.title = '더 보기';
        const fly = document.createElement('div'); fly.className = 'rp-fly';
        for (const it of p.more) fly.appendChild(mkBtn(it, 'rsm'));
        pd.appendChild(fly);
        pt.onclick = ev => { ev.stopPropagation(); const o = pd.classList.contains('open'); rb.querySelectorAll('.rp.open').forEach(x => x.classList.remove('open')); if (!o) { pd.classList.add('open'); const r = pd.getBoundingClientRect(); fly.style.position = 'fixed'; fly.style.left = Math.min(r.left, innerWidth - 200) + 'px'; fly.style.top = r.bottom + 'px'; } };
      }
      pane.appendChild(pd);
    }
    body.appendChild(pane);
  }
  document.addEventListener('pointerdown', ev => { if (!ev.target.closest('.rp')) rb.querySelectorAll('.rp.open').forEach(x => x.classList.remove('open')); });
  body.addEventListener('scroll', () => rb.querySelectorAll('.rp.open').forEach(x => x.classList.remove('open')));
  function showTab(name) {
    if (!panes[name]) name = '홈';
    for (const [n, [tb, pane]] of Object.entries(panes)) { tb.classList.toggle('on', n === name); pane.style.display = n === name ? 'contents' : 'none'; }
    if (rb.classList.contains('min')) setRibbonMin(false);
    store.set('vc.rbTab', name); refreshChk();
  }
  function setRibbonMin(v) { rb.classList.toggle('min', v); store.set('vc.rbMin', v); resize(); refreshChk(); }
  const mn = document.createElement('button'); mn.type = 'button'; mn.className = 'rmin'; mn.textContent = '▲ 리본 접기';
  mn.onclick = () => setRibbonMin(!rb.classList.contains('min'));
  tabsEl.appendChild(mn);
  new MutationObserver(() => { mn.textContent = rb.classList.contains('min') ? '▼ 리본 펼치기' : '▲ 리본 접기'; }).observe(rb, { attributes:true, attributeFilter:['class'] });
  function setBars(cls) { document.body.classList.toggle(cls); store.set('vc.' + cls, document.body.classList.contains(cls)); resize(); refreshChk(); }
  if (store.get('vc.nomenu', false)) document.body.classList.add('nomenu');
  if (store.get('vc.oldbars', false)) document.body.classList.add('oldbars');
  rb.classList.toggle('min', !!store.get('vc.rbMin', false));
  showTab(store.get('vc.rbTab', '홈'));

  /* 제목줄: 빠른 실행 아이콘 + 가운데 제목 */
  const tbar = $('#titlebar'), app = tbar.querySelector('.app');
  const qa = document.createElement('span'); qa.style.cssText = 'display:flex;gap:1px;margin-left:4px';
  for (const [sel, icn, tt] of [['#bNew', 'new', '새 도면'], ['#bSrvOpen', 'open', '서버 도면 열기'], ['#bSrvSave', 'save', '서버 저장 (Ctrl+S)'], ['#bPutFile', 'putfile', '파일 넣기'], [null, 'plot', '출력 (Ctrl+P)'], ['#bUndo', 'undo', '실행취소 (Ctrl+Z)'], ['#bRedo', 'redo', '다시실행 (Ctrl+Y)']]) {
    const b = document.createElement('button'); b.type = 'button'; b.className = 'ib qa'; b.innerHTML = ic(icn); b.title = tt;
    b.onclick = () => { b.blur(); if (sel) $(sel).click(); else startCmd('PLOT'); }; qa.appendChild(b);
  }
  const mb = document.createElement('button'); mb.type = 'button'; mb.className = 'ib qa'; mb.innerHTML = ic('menu'); mb.title = '메뉴 막대 보이기/숨기기';
  mb.onclick = () => { mb.blur(); setBars('nomenu'); }; qa.appendChild(mb);
  app.after(qa);
  const ttl = document.createElement('span'); ttl.className = 'ttl'; qa.after(ttl);
  const srvT = $('#srvTitle'); srvT.style.display = 'none';
  /* 도면 탭 */
  const dtabs = document.createElement('div'); dtabs.id = 'docTabs';
  dtabs.innerHTML = '<span class="dt on"><span></span></span><span class="dt add" title="새 도면">＋</span>';
  dtabs.lastChild.onclick = clickEl('#bNew');
  $('#work').before(dtabs);
  const docName = () => (srvT.textContent || '').trim() || '도면1';
  function updTitle() { const n = docName(); ttl.innerHTML = '말로 캐드 <small></small>'; ttl.lastChild.textContent = '— ' + n; dtabs.querySelector('.dt.on span').textContent = n; document.title = n + ' — 말로 캐드'; }
  new MutationObserver(updTitle).observe(srvT, { childList:true, characterData:true, subtree:true });
  updTitle();

  /* 도면 위: 왼쪽 위 「[-][층][평면도][2D]」, 오른쪽 위 방위 표시, 아래 떠 있는 명령줄 */
  const stage = $('#stage');
  const vp = document.createElement('div'); vp.id = 'vpLabel';
  const vb = (txt, tt, fn) => { const b = document.createElement('button'); b.type = 'button'; b.textContent = txt; b.title = tt; b.onclick = () => { b.blur(); fn(); }; vp.appendChild(b); return b; };
  vb('[-]', '리본 접기/펼치기', () => setRibbonMin(!rb.classList.contains('min')));
  const vFloor = vb('[1층]', '층 바꾸기 — 아래 층 탭에서 골라도 됩니다', () => {
    const i = doc.levels.findIndex(l => l.id === doc.cur), n = doc.levels[(i + 1) % doc.levels.length];
    if (n) { doc.cur = n.id; save(); renderFloors(); draw(); }
  });
  vb('[평면도]', '전체 보기 (Z → A)', clickEl('#bZoom'));
  vb('[2D 선]', '3D로 보기', () => startCmd('VIEW3D'));
  stage.appendChild(vp);
  const NS = 'http://www.w3.org/2000/svg', cp = document.createElementNS(NS, 'svg');
  cp.id = 'compass'; cp.setAttribute('viewBox', '0 0 100 100');
  cp.innerHTML = '<title>방위 (위쪽 = 북) — 누르면 전체 보기</title>' +
    '<circle cx="50" cy="50" r="34" fill="none" stroke-width="7" class="ring"/>' +
    '<rect x="37" y="37" width="26" height="26" rx="2" class="cube"/>' +
    '<text x="50" y="50" class="cubet">위</text>' +
    '<text x="50" y="9" class="dir">북</text><text x="92" y="50" class="dir">동</text><text x="50" y="92" class="dir">남</text><text x="8" y="50" class="dir">서</text>' +
    '<path d="M50 13 46 21h8z" class="arrow"/>';
  cp.onclick = clickEl('#bZoom');
  stage.appendChild(cp);
  function paintCompass() {
    const light = typeof bgLight === 'function' && bgLight();
    const ring = light ? '#c9d0d7' : '#3a434d', fg = light ? '#3a4450' : '#c7ced6', cube = light ? '#f3f5f7' : '#262c33';
    cp.querySelector('.ring').setAttribute('stroke', ring);
    cp.querySelector('.cube').setAttribute('fill', cube); cp.querySelector('.cube').setAttribute('stroke', ring);
    cp.querySelectorAll('text').forEach(t => t.setAttribute('fill', fg));
    cp.querySelector('.arrow').setAttribute('fill', '#d9534f');
    vp.querySelectorAll('button').forEach(b => { b.style.background = light ? '#ffffffd9' : ''; b.style.color = light ? '#1f4f86' : ''; b.style.borderColor = light ? '#c9d0d7' : ''; });
  }
  paintCompass();
  if (typeof applyView === 'function') { const av0 = applyView; applyView = () => { av0(); paintCompass(); }; }
  const cw = $('#cmdwin'); stage.appendChild(cw);
  /* 명령 기록은 최근 3줄만 보이게(위로 스크롤하면 전부) */
  /* 아래: 모형·배치 탭, 층 탭, 상태 아이콘 */
  const sb = $('#statusbar'), coords = $('#coords');
  const lt1 = document.createElement('button'); lt1.type = 'button'; lt1.className = 'lt on'; lt1.textContent = '모형'; lt1.title = '그리는 화면';
  const lt2 = document.createElement('button'); lt2.type = 'button'; lt2.className = 'lt'; lt2.textContent = '배치(출력)'; lt2.title = '종이에 맞춰 출력 (PDF)';
  lt2.onclick = () => { lt2.blur(); startCmd('PLOT'); };
  sb.prepend(lt1, lt2, $('#floorbar'));
  const sp = sb.querySelector('.spacer'); if (sp) sb.insertBefore(sp, coords);
  const sep = () => { const s = document.createElement('span'); s.className = 'ssep'; return s; };
  coords.after(sep());
  $('#tAI').before(sep());
  const lvName = () => { const l = lvOf(doc.cur); return l ? l.name : '1층'; };
  const rf0 = renderFloors;
  renderFloors = () => { rf0(); vFloor.textContent = `[${lvName()}]`; };
  vFloor.textContent = `[${lvName()}]`;
  for (const id of ['#tGrid', '#tOrtho', '#tSnap', '#tPolar', '#tAI']) { const b = $(id); if (b) b.addEventListener('click', () => setTimeout(refreshChk, 30)); }
  document.addEventListener('keydown', ev => { if (/^F\d+$/.test(ev.key)) setTimeout(refreshChk, 30); });
  resize();
})();

draw();
})();
