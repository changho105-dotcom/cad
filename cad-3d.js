/* 말로 캐드 — 3D 모델링 (1단계)
   · 도면 화면을 그대로 3D로 바꿔 보기(돌려보기·이동·확대, 평면/정면/측면/등각, 2D 선·와이어·음영·음영+모서리·X-레이)
   · 입체(type:'solid'): 상자·원기둥·원뿔·구·밀어올리기·누르고 당기기 — 2D 도면에서는 바닥 윤곽으로 보임
   · 3D 화면에서도 명령을 그대로 씀: 클릭한 곳은 작업 평면(층 바닥 + 작업 높이) 또는 입체 윗면 위의 점
   단위 mm, Z = 위. three.js(MIT)는 3D 화면을 처음 열 때 불러옴. 다음 단계 계획은 docs/3D_계획.md */
(() => {
const { primsAny, closedLoop, M } = window.CADX;
const S3 = settings.s3 = Object.assign({ style:'edge', elev:0, persp:false, lastH:3000 }, settings.s3 || {});
const saveSet = () => store.set('vc.settings', settings);
const lvZ = id => { const l = id ? lvOf(id) : null; return l ? l.el * 1000 : 0; };
const lvTop = id => { const l = (id && lvOf(id)) || lvOf(doc.cur) || { el:0, h:3 }; return (l.el + l.h) * 1000; };
const curZ = () => lvZ(doc.cur);
const isNum = t => /^-?\d*\.?\d+$/.test(String(t).trim());
const toV = (x, y, z) => [x, y, z];
const polar = (c, r, deg) => [c[0] + r * Math.cos(deg * D2R), c[1] + r * Math.sin(deg * D2R)];

/* ---------- 입체 → 삼각형 ---------- */
function cleanLoop(pts) {
  const out = [];
  for (const p of pts) { const q = out[out.length - 1]; if (!q || Math.hypot(p[0] - q[0], p[1] - q[1]) > 1e-6) out.push([p[0], p[1]]); }
  if (out.length > 2 && Math.hypot(out[0][0] - out[out.length - 1][0], out[0][1] - out[out.length - 1][1]) < 1e-6) out.pop();
  const res = [];
  for (let i = 0; i < out.length; i++) {
    const a = out[(i + out.length - 1) % out.length], b = out[i], c = out[(i + 1) % out.length];
    if (Math.abs((b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])) > 1e-6 * Math.max(1, Math.hypot(c[0] - a[0], c[1] - a[1]))) res.push(b);
  }
  return res.length >= 3 ? res : out;
}
const area2 = P => { let a = 0; for (let i = 0; i < P.length; i++) { const p = P[i], q = P[(i + 1) % P.length]; a += p[0] * q[1] - q[0] * p[1]; } return a; };
const ccw = P => area2(P) >= 0 ? P : P.slice().reverse();
function triangulate(P) {
  const n = P.length, idx = [...Array(n).keys()], out = [];
  const cr = (a, b, c) => (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]);
  const inside = (p, a, b, c) => cr(a, b, p) >= 0 && cr(b, c, p) >= 0 && cr(c, a, p) >= 0;
  let guard = 0;
  while (idx.length > 3 && guard++ < 20000) {
    let cut = false;
    for (let i = 0; i < idx.length; i++) {
      const i0 = idx[(i + idx.length - 1) % idx.length], i1 = idx[i], i2 = idx[(i + 1) % idx.length], a = P[i0], b = P[i1], c = P[i2];
      if (cr(a, b, c) <= 0) continue;
      let ok = true;
      for (const j of idx) { if (j === i0 || j === i1 || j === i2) continue; if (inside(P[j], a, b, c)) { ok = false; break; } }
      if (!ok) continue;
      out.push([i0, i1, i2]); idx.splice(i, 1); cut = true; break;
    }
    if (!cut) { for (let i = 1; i < idx.length - 1; i++) out.push([idx[0], idx[i], idx[i + 1]]); return out; }
  }
  if (idx.length === 3) out.push(idx);
  return out;
}
function prismTris(pts, z0, z1, T) {
  if (z1 < z0) [z0, z1] = [z1, z0];
  const P = ccw(cleanLoop(pts)); if (P.length < 3 || z1 - z0 < 1e-6) return T;
  for (const [a, b, c] of triangulate(P)) { T.push([toV(...P[a], z1), toV(...P[b], z1), toV(...P[c], z1)], [toV(...P[c], z0), toV(...P[b], z0), toV(...P[a], z0)]); }
  for (let i = 0; i < P.length; i++) {
    const a = P[i], b = P[(i + 1) % P.length];
    T.push([toV(...a, z0), toV(...b, z0), toV(...b, z1)], [toV(...a, z0), toV(...b, z1), toV(...a, z1)]);
  }
  return T;
}
const SEG = 48;
function frustumTris(cx, cy, r1, r2, z0, z1, T) {
  if (z1 < z0) { [z0, z1] = [z1, z0]; [r1, r2] = [r2, r1]; }
  const ring = (r, z) => Array.from({ length:SEG }, (_, i) => [cx + r * Math.cos(i / SEG * 2 * Math.PI), cy + r * Math.sin(i / SEG * 2 * Math.PI), z]);
  const A = ring(r1, z0), B = ring(r2, z1);
  for (let i = 0; i < SEG; i++) {
    const j = (i + 1) % SEG;
    if (r1 > 0) T.push([[cx, cy, z0], A[j], A[i]]);
    if (r2 > 0) T.push([[cx, cy, z1], B[i], B[j]]);
    if (r1 > 0) T.push([A[i], A[j], B[j]]);
    if (r2 > 0) T.push([A[i], B[j], B[i]]);
  }
  return T;
}
function sphereTris(cx, cy, cz, r, T) {
  const NU = 32, NV = 16, P = (u, v) => { const th = u / NU * 2 * Math.PI, ph = v / NV * Math.PI - Math.PI / 2; return [cx + r * Math.cos(ph) * Math.cos(th), cy + r * Math.cos(ph) * Math.sin(th), cz + r * Math.sin(ph)]; };
  for (let u = 0; u < NU; u++) for (let v = 0; v < NV; v++) {
    const a = P(u, v), b = P(u + 1, v), c = P(u + 1, v + 1), d = P(u, v + 1);
    if (v > 0) T.push([a, b, c]);
    if (v < NV - 1) T.push([a, c, d]);
  }
  return T;
}
function solidZ(e) { const z0 = lvZ(e.floor) + (e.z || 0), h = Number.isFinite(e.h) ? e.h : S3.lastH; return [z0, z0 + h]; }
function solidTris(e) {
  const T = [];
  if (e.kind === 'sph') return sphereTris(e.cx, e.cy, lvZ(e.floor) + (e.z || 0), e.r, T);
  const [z0, z1] = solidZ(e);
  if (e.kind === 'cyl') return frustumTris(e.cx, e.cy, e.r, e.r2 ?? e.r, z0, z1, T);
  return prismTris(e.pts || [], z0, z1, T);
}
/* 건축 요소도 같은 방식으로 세움(벽·기둥·슬라브·설비·창·문) — 벽의 창·문 구멍 뚫기는 2단계(합치기·빼기)에서 */
function archTris(e) {
  const z0 = lvZ(e.floor), z1 = lvTop(e.floor), T = [];
  const panel = (a, b, za, zb, off, th) => { const L = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1, nx = -(b[1] - a[1]) / L, ny = (b[0] - a[0]) / L;
    const q = (o1, o2) => [[a[0] + nx * o1, a[1] + ny * o1], [b[0] + nx * o1, b[1] + ny * o1], [b[0] + nx * o2, b[1] + ny * o2], [a[0] + nx * o2, a[1] + ny * o2]];
    for (const s of off) prismTris(q(s, s + th), za, zb, T); };
  switch (e.type) {
    case 'wall': return { T:prismTris(wallQuad(e), z0, z1, T), col:'#d6d0c4' };
    case 'column': return { T:e.r > 0 ? frustumTris(e.cx, e.cy, e.r, e.r, z0, z1, T) : prismTris(columnPts(e), z0, z1, T), col:'#bebab2' };
    case 'slab': { const top = Number.isFinite(e.top) ? e.top * 1000 : z1; return { T:prismTris(e.pts, top - (e.t || 150), top, T), col:'#aab0ba' }; }
    case 'equip': return { T:prismTris(equipPts(e), z0, z0 + (e.h || 1500), T), col:'#dea05a' };
    case 'window': { const s = e.sill ?? 900; panel([e.x1, e.y1], [e.x2, e.y2], z0 + s, z0 + s + (e.wh || 1500), [115, -135], 20); return { T, col:'#5aaae6', alpha:0.55 }; }
    case 'door': { const g = doorGeom(e); panel([e.x, e.y], g.closed, z0, z0 + (e.dh || 2100), [115, -155], 40); return { T, col:'#966946' }; }
  }
  return null;
}
window.CAD3D_TRIS = e => e.type === 'solid' ? solidTris(e) : ((archTris(e) || {}).T || []); // 시험·내보내기용

/* ---------- 2D 도면에서의 입체: 바닥 윤곽 · 스냅 · 변형 · AI · DXF ---------- */
TYPE_KO.solid = '입체';
Object.assign(PROP_KO, { z:'바닥 높이 (층 바닥 기준)', r2:'윗면 반지름' });
for (const k of ['z', 'r2']) if (!NUM_KEYS.includes(k)) NUM_KEYS.push(k);
const ep0 = window.extPrims;
window.extPrims = e => {
  if (e.type !== 'solid') return ep0(e);
  const P = [];
  if (e.kind === 'cyl' || e.kind === 'sph') {
    P.push({ k:'arc', c:[e.cx, e.cy], r:e.r, a1:0, a2:360, full:true });
    if (e.kind === 'cyl' && e.r2 > 0 && e.r2 !== e.r) P.push({ k:'arc', c:[e.cx, e.cy], r:e.r2, a1:0, a2:360, full:true });
    if (e.kind === 'cyl' && e.r2 === 0) P.push({ k:'pt', p:[e.cx, e.cy] });
  } else if (e.pts && e.pts.length > 2) P.push({ k:'pl', pts:e.pts, closed:true });
  P.push({ k:'solid3', e });
  return P;
};
const sn0 = window.extSnaps;
window.extSnaps = e => {
  if (e.type !== 'solid') return sn0(e);
  if (e.kind === 'cyl' || e.kind === 'sph') return [[e.cx, e.cy, '중심'], [e.cx + e.r, e.cy, '사분점'], [e.cx - e.r, e.cy, '사분점'], [e.cx, e.cy + e.r, '사분점'], [e.cx, e.cy - e.r, '사분점']];
  const P = e.pts || [];
  return [...P.map(p => [p[0], p[1], '끝점']), ...P.map((p, i) => { const q = P[(i + 1) % P.length]; return [(p[0] + q[0]) / 2, (p[1] + q[1]) / 2, '중간점']; })];
};
const xf0 = window.extXform;
window.extXform = (e, f, o) => {
  if (e.type !== 'solid') return xf0(e, f, o);
  const k = o.k || 1;
  if (k !== 1) { if (Number.isFinite(e.h)) e.h *= k; if (Number.isFinite(e.r2)) e.r2 *= k; if (Number.isFinite(e.z)) e.z *= k; }
};
const dx0 = window.dxfPrims;
window.dxfPrims = (prs, w, l) => {
  const s = prs.find(q => q.k === 'solid3');
  if (!s) return dx0(prs, w, l);
  const { g, head } = w;
  for (const t of solidTris(s.e)) { head('3DFACE', l); [t[0], t[1], t[2], t[2]].forEach((p, i) => { g(10 + i, p[0]); g(20 + i, p[1]); g(30 + i, p[2]); }); }
};
const san0 = window.extSanitize;
window.extSanitize = a => {
  if (!a || a.type !== 'solid') return san0(a);
  const n = k => (a[k] != null && a[k] !== '' && Number.isFinite(+a[k])) ? +a[k] : null;
  let kind = ['box', 'ext', 'cyl', 'sph'].includes(a.kind) ? a.kind : (Array.isArray(a.pts) ? 'ext' : 'cyl');
  const e = { type:'solid', kind, layer:LAYERS[a.layer] ? a.layer : '0' };
  if (n('z') != null) e.z = n('z');
  if (a.floor != null && lvOf(String(a.floor))) e.floor = String(a.floor);
  if (a.tag && typeof a.tag === 'string') e.tag = a.tag;
  if (typeof a.color === 'string' && /^#[0-9a-f]{6}$/i.test(a.color)) e.color = a.color;
  if (kind === 'box' || kind === 'ext') {
    let pts = (Array.isArray(a.pts) ? a.pts : []).map(p => Array.isArray(p) && Number.isFinite(+p[0]) && Number.isFinite(+p[1]) ? [+p[0], +p[1]] : null).filter(Boolean);
    if (pts.length < 3 && [n('x'), n('y'), n('w'), n('d')].every(v => v != null)) pts = [[n('x'), n('y')], [n('x') + n('w'), n('y')], [n('x') + n('w'), n('y') + n('d')], [n('x'), n('y') + n('d')]];
    if (pts.length < 3) return null; e.pts = pts;
  } else {
    if (n('cx') == null || n('cy') == null || !(n('r') > 0)) return null;
    e.cx = n('cx'); e.cy = n('cy'); e.r = n('r'); if (kind === 'cyl' && n('r2') != null && n('r2') >= 0) e.r2 = n('r2');
  }
  if (kind !== 'sph') { const h = n('h'); e.h = h != null && h !== 0 ? h : lvTop(e.floor) - lvZ(e.floor || doc.cur); if (e.h < 0) { e.z = (e.z || 0) + e.h; e.h = -e.h; if (kind === 'cyl' && e.r2 != null) [e.r, e.r2] = [e.r2, e.r]; } }
  return e;
};
{
  const IT = TOOL.input_schema.properties.add.items.properties;
  if (!IT.type.enum.includes('solid')) IT.type.enum.push('solid');
  for (const k of ['ext', 'cyl', 'sph']) if (!IT.kind.enum.includes(k)) IT.kind.enum.push(k);
  IT.z = { type:'number' }; IT.r2 = { type:'number' }; IT.color = { type:'string' };
  window.SYS_EXTRA += `
[3D 입체] type:'solid' — 2D 도면에는 바닥 윤곽으로, 3D 화면에는 입체로 보인다. 단위 mm, z=층 바닥에서 입체 밑면까지 높이(기본 0), h=높이.
- kind:'box' 또는 'ext': pts=바닥 윤곽(닫힌 다각형 꼭짓점, 방향 무관) 또는 box는 x,y,w,d(가로·세로)로도 가능
- kind:'cyl': cx,cy,r(밑면 반지름), r2=윗면 반지름(생략=r, 0이면 원뿔)
- kind:'sph': cx,cy,r, z=중심 높이
- "이 사각형/도형을 3m 올려(밀어올려)" → 그 도형의 꼭짓점으로 solid ext h:3000을 add하고 원래 도형은 remove. 원은 cyl.
- "입체를 더 높게/낮게" → modify로 h를 바꾼다. 입체를 다른 입체 위에 올리려면 z=아래 입체의 z+h.
- 이미 있는 닫힌 도형(사각형·닫힌 폴리선·원·실·슬라브)을 입체로: ops {"op":"EXTRUDE","ids":[...],"h":3000,"z":0} (원래 선 도형은 입체로 바뀜)
- 화면을 3D로: ops {"op":"VIEW3D","view":"swiso"|"seiso"|"neiso"|"nwiso"|"top"|"front"|"back"|"left"|"right","style":"edge"|"shade"|"wire"|"xray"} / 평면 도면으로: {"op":"PLAN"}`;
}

/* ---------- 3D 화면 ---------- */
let THREE = null, V = null, is3D = false, loading = null;
const host = document.createElement('div'); host.id = 'v3';
host.style.cssText = 'position:absolute;inset:0;display:none;z-index:2;touch-action:none;cursor:crosshair;outline:none';
$('#stage').appendChild(host);
const cam3 = { tgt:[0, 0, 0], az:-135, el:35.264, size:20000 };
let curView = 'swiso';
const VIEWS = {
  top:['3D 평면', -90, 89.9], front:['정면 (남)', -90, 0], back:['배면 (북)', 90, 0], left:['좌측면 (서)', 180, 0], right:['우측면 (동)', 0, 0],
  swiso:['남서 등각', -135, 35.264], seiso:['남동 등각', -45, 35.264], neiso:['북동 등각', 45, 35.264], nwiso:['북서 등각', 135, 35.264]
};
const STYLES = { wire:'3D 와이어프레임', shade:'음영', edge:'음영+모서리', xray:'X-레이' };
async function loadThree() {
  if (THREE) return THREE;
  if (!loading) loading = import('https://cdn.jsdelivr.net/npm/three@0.170.0/build/three.module.min.js');
  THREE = await loading; return THREE;
}
function initV() {
  const T = THREE, renderer = new T.WebGLRenderer({ antialias:true, alpha:false });
  renderer.setPixelRatio(window.devicePixelRatio || 1); host.appendChild(renderer.domElement);
  renderer.domElement.style.cssText = 'width:100%;height:100%;display:block';
  const scene = new T.Scene();
  const ortho = new T.OrthographicCamera(-1, 1, 1, -1, 1, 1e7), persp = new T.PerspectiveCamera(40, 1, 10, 1e8);
  for (const c of [ortho, persp]) c.up.set(0, 0, 1);
  scene.add(new T.HemisphereLight(0xffffff, 0x8a8a8a, 1.6));
  const sun = new T.DirectionalLight(0xffffff, 1.6); sun.position.set(0.45, -0.7, 1); scene.add(sun);
  const root = new T.Group(), helpers = new T.Group(), live = new T.Group(); scene.add(root, helpers, live);
  V = { renderer, scene, ortho, persp, root, helpers, live, cache:new Map(), queued:false };
  new ResizeObserver(() => req()).observe(host);
}
const camera = () => S3.persp ? V.persp : V.ortho;
function camDir() { const a = cam3.az * D2R, e = cam3.el * D2R; return [Math.cos(e) * Math.cos(a), Math.cos(e) * Math.sin(a), Math.sin(e)]; }
function placeCam() {
  const W = host.clientWidth || 1, H = host.clientHeight || 1, asp = W / H, d = camDir(), R = V.sceneR || 50000;
  const o = V.ortho; o.left = -cam3.size * asp / 2; o.right = cam3.size * asp / 2; o.top = cam3.size / 2; o.bottom = -cam3.size / 2;
  const D = R * 4 + cam3.size * 4; o.position.set(cam3.tgt[0] + d[0] * D, cam3.tgt[1] + d[1] * D, cam3.tgt[2] + d[2] * D); o.near = 1; o.far = D * 2 + R * 4;
  o.lookAt(cam3.tgt[0], cam3.tgt[1], cam3.tgt[2]); o.updateProjectionMatrix();
  const p = V.persp, pd = cam3.size / 2 / Math.tan(20 * D2R); p.aspect = asp;
  p.position.set(cam3.tgt[0] + d[0] * pd, cam3.tgt[1] + d[1] * pd, cam3.tgt[2] + d[2] * pd); p.near = Math.max(1, pd / 1000); p.far = pd + R * 8;
  p.lookAt(cam3.tgt[0], cam3.tgt[1], cam3.tgt[2]); p.updateProjectionMatrix();
  V.renderer.setSize(W, H, false);
  paintCompass3();
}
function req() { if (!V || V.queued) return; V.queued = true; requestAnimationFrame(() => { V.queued = false; if (!is3D) return; rebuild(); placeCam(); V.renderer.render(V.scene, camera()); }); }
const reqLive = () => { if (!V || V.liveQ) return; V.liveQ = true; requestAnimationFrame(() => { V.liveQ = false; if (is3D) { placeCam(); V.renderer.render(V.scene, camera()); } }); };

const bgCol = () => settings.view && settings.view.bg || '#ffffff';
const lum = h => { const m = /^#([0-9a-f]{6})$/i.exec(h || ''); if (!m) return 0.5; const v = parseInt(m[1], 16); return (0.299 * (v >> 16) + 0.587 * ((v >> 8) & 255) + 0.114 * (v & 255)) / 255; };
const light = () => lum(bgCol()) > 0.55;
function lineCol(e) {
  let c = e.color || (settings.view && settings.view.ink) || (LAYERS[e.layer] || LAYERS['0']).color;
  if (light() && lum(c) > 0.75) c = '#1a1a1a'; else if (!light() && lum(c) < 0.15) c = '#e8e8e8';
  return c;
}
function solidCol(e) { const c = e.color || (LAYERS[e.layer] || LAYERS['0']).color; return (lum(c) > 0.85 || lum(c) < 0.1) ? '#b9c6d3' : c; }
const edgeCol = () => light() ? '#1f2328' : '#dfe5eb';

function meshFrom(T, col, alpha) {
  const TH = THREE, pos = new Float32Array(T.length * 9); let i = 0;
  for (const t of T) for (const p of t) { pos[i++] = p[0]; pos[i++] = p[1]; pos[i++] = p[2]; }
  const g = new TH.BufferGeometry(); g.setAttribute('position', new TH.BufferAttribute(pos, 3)); g.computeVertexNormals();
  const m = new TH.MeshLambertMaterial({ color:col, side:TH.DoubleSide, transparent:alpha < 1, opacity:alpha, polygonOffset:true, polygonOffsetFactor:1, polygonOffsetUnits:1 });
  const mesh = new TH.Mesh(g, m); mesh.userData.kind = 'face'; mesh.userData.alpha = alpha;
  const eg = new TH.LineSegments(new TH.EdgesGeometry(g, 25), new TH.LineBasicMaterial({ color:edgeCol() })); eg.userData.kind = 'edge';
  const grp = new TH.Group(); grp.add(mesh, eg); return grp;
}
function linesFrom(prs, z, col) {
  const TH = THREE, seg = [];
  const pl = (pts, closed) => { for (let i = 0; i < pts.length - 1 + (closed ? 1 : 0); i++) { const a = pts[i], b = pts[(i + 1) % pts.length]; seg.push(a[0], a[1], z, b[0], b[1], z); } };
  for (const q of prs) {
    if (q.k === 'pl' && !q.nb) pl(q.pts, q.closed);
    else if (q.k === 'arc') { const sw = q.full ? 360 : ((q.a2 - q.a1) % 360 + 360) % 360 || 360, n = Math.max(8, Math.ceil(sw / 7.5)); pl(Array.from({ length:n + 1 }, (_, i) => polar(q.c, q.r, q.a1 + sw * i / n)), false); }
    else if (q.k === 'ring') { for (const r of [q.ro, q.ri]) if (r > 0) pl(Array.from({ length:49 }, (_, i) => polar(q.c, r, i * 7.5)), false); }
    else if (q.k === 'pt') { const s = 60; seg.push(q.p[0] - s, q.p[1], z, q.p[0] + s, q.p[1], z, q.p[0], q.p[1] - s, z, q.p[0], q.p[1] + s, z); }
  }
  if (!seg.length) return null;
  const g = new TH.BufferGeometry(); g.setAttribute('position', new TH.Float32BufferAttribute(seg, 3));
  const ls = new TH.LineSegments(g, new TH.LineBasicMaterial({ color:col })); ls.userData.kind = 'line';
  return ls;
}
const SKIP2D = ['text', 'mtext', 'dim', 'dimdia', 'dimrad', 'dimang', 'dimord', 'leader', 'hatch', 'xline', 'ray', 'image'];
function makeObj(e) {
  if (e.type === 'solid') { const T = solidTris(e); return T.length ? meshFrom(T, solidCol(e), 1) : null; }
  const A = archTris(e); if (A) return A.T.length ? meshFrom(A.T, A.col, A.alpha ?? 1) : null;
  if (SKIP2D.includes(e.type)) return null;
  let prs = null; try { prs = primsAny(e); } catch (err) { prs = null; }
  return prs ? linesFrom(prs, lvZ(e.floor), lineCol(e)) : null;
}
function disposeObj(o) { o.traverse(x => { if (x.geometry) x.geometry.dispose(); if (x.material) x.material.dispose(); }); }
function rebuild() {
  const keep = new Set(), sigX = `${S3.style}|${bgCol()}|${settings.view && settings.view.ink}|${JSON.stringify(doc.levels)}`;
  for (const e of doc.ents) {
    if (layerOff(e)) continue;
    let rec = V.cache.get(e); const sig = JSON.stringify(e) + sigX;
    if (!rec || rec.sig !== sig) { if (rec && rec.obj) { V.root.remove(rec.obj); disposeObj(rec.obj); } const obj = makeObj(e); if (obj) obj.userData.id = e.id; rec = { sig, obj }; V.cache.set(e, rec); }
    if (rec.obj) { keep.add(rec.obj); if (rec.obj.parent !== V.root) V.root.add(rec.obj); }
  }
  for (const [e, rec] of V.cache) if (!rec.obj || !keep.has(rec.obj)) { if (rec.obj) { V.root.remove(rec.obj); disposeObj(rec.obj); } V.cache.delete(e); }
  const st = S3.style, acc = new THREE.Color('#2f7fd1');
  V.root.traverse(o => {
    const id = (o.userData.id ? o : o.parent || {}).userData?.id, on = id && sel.has(id);
    if (o.userData.kind === 'face') { o.visible = st !== 'wire'; const a = st === 'xray' ? Math.min(0.35, o.userData.alpha) : o.userData.alpha; o.material.opacity = a; o.material.transparent = a < 1; o.material.depthWrite = a >= 1; o.material.emissive.set(on ? '#1d4f8a' : '#000000'); }
    else if (o.userData.kind === 'edge') { o.visible = st !== 'shade' || on; o.material.color.set(on ? acc : edgeCol()); }
    else if (o.userData.kind === 'line') { if (!o.userData.col) o.userData.col = o.material.color.getHex(); o.material.color.set(on ? acc : o.userData.col); }
  });
  V.scene.background = new THREE.Color(bgCol());
  const b = new THREE.Box3().setFromObject(V.root);
  V.bounds = b.isEmpty() ? null : b; V.sceneR = b.isEmpty() ? 20000 : b.getSize(new THREE.Vector3()).length() / 2 + 1000;
  buildHelpers();
}
function buildHelpers() {
  const T = THREE, h = V.helpers; h.children.slice().forEach(c => { h.remove(c); disposeObj(c); });
  const z = curZ() + (S3.elev || 0);
  if (gridOn) {
    const tgt = 40 / Math.max(1, host.clientHeight) * cam3.size, p = Math.pow(10, Math.floor(Math.log10(tgt)));
    let step = p * 10; for (const m of [1, 2, 5, 10]) if (p * m >= tgt) { step = p * m; break; }
    const n = 60, half = step * n / 2, cx = Math.round(cam3.tgt[0] / step) * step, cy = Math.round(cam3.tgt[1] / step) * step, seg = [];
    for (let i = 0; i <= n; i++) { const o = -half + i * step; seg.push(cx + o, cy - half, z, cx + o, cy + half, z, cx - half, cy + o, z, cx + half, cy + o, z); }
    const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(seg, 3));
    h.add(new T.LineSegments(g, new T.LineBasicMaterial({ color:light() ? '#e3e7eb' : '#222a32', depthWrite:false })));
  }
  const L = cam3.size * 0.06, ax = [['#e04848', [L, 0, 0]], ['#3aa64c', [0, L, 0]], ['#3c7be0', [0, 0, L]]];
  for (const [c, d] of ax) { const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute([0, 0, z, d[0], d[1], z + d[2]], 3)); h.add(new T.Line(g, new T.LineBasicMaterial({ color:c }))); }
}
function zoomExt3() {
  if (!V) return; rebuild();
  const b = V.bounds; if (!b) { cam3.tgt = [0, 0, curZ()]; cam3.size = 20000; req(); return; }
  const c = b.getCenter(new THREE.Vector3()), s = b.getSize(new THREE.Vector3());
  cam3.tgt = [c.x, c.y, c.z];
  const d = camDir(), W = host.clientWidth || 1, H = host.clientHeight || 1;
  const right = [-d[1], d[0], 0], rl = Math.hypot(...right) || 1, R = right.map(v => v / rl), U = [d[1] * R[2] - d[2] * R[1], d[2] * R[0] - d[0] * R[2], d[0] * R[1] - d[1] * R[0]];
  let wx = 0, wy = 0;
  for (const x of [b.min.x, b.max.x]) for (const y of [b.min.y, b.max.y]) for (const z of [b.min.z, b.max.z]) { const v = [x - c.x, y - c.y, z - c.z]; wx = Math.max(wx, Math.abs(v[0] * R[0] + v[1] * R[1] + v[2] * R[2])); wy = Math.max(wy, Math.abs(v[0] * U[0] + v[1] * U[1] + v[2] * U[2])); }
  cam3.size = Math.max(wy * 2, wx * 2 * H / W, 500) * 1.15; if (!s.length()) cam3.size = 5000;
  req();
}

/* 화면 좌표 → 작업 평면 위 점, 입체 맞춤 */
function ndc(ev) { const r = host.getBoundingClientRect(); return new THREE.Vector2((ev.clientX - r.left) / r.width * 2 - 1, -((ev.clientY - r.top) / r.height) * 2 + 1); }
function ray(ev) { const rc = new THREE.Raycaster(); rc.setFromCamera(ndc(ev), camera()); rc.params.Line.threshold = cam3.size / (host.clientHeight || 1) * 6; return rc; }
function planePt(rc, z) {
  const o = rc.ray.origin, d = rc.ray.direction;
  if (Math.abs(d.z) > 1e-4) { const t = (z - o.z) / d.z; if (t > 0 || !S3.persp) return [o.x + d.x * t, o.y + d.y * t, z]; }
  const n = camDir(), tg = cam3.tgt, den = d.x * n[0] + d.y * n[1] + d.z * n[2], t = ((tg[0] - o.x) * n[0] + (tg[1] - o.y) * n[1] + (tg[2] - o.z) * n[2]) / (den || 1e-9);
  return [o.x + d.x * t, o.y + d.y * t, o.z + d.z * t];
}
function hitAt(ev) {
  const rc = ray(ev), hits = rc.intersectObjects(V.root.children, true).filter(h => h.object.visible);
  for (const h of hits) {
    let o = h.object; while (o && !o.userData.id) o = o.parent;
    if (!o) continue;
    const e = findEnt(o.userData.id); if (!e) continue;
    const n = h.face ? h.face.normal.clone().transformDirection(h.object.matrixWorld) : null;
    return { e, p:[h.point.x, h.point.y, h.point.z], nz:n ? n.z : 0, face:h.object.userData.kind === 'face' };
  }
  return null;
}
function snap3(ev) {
  if (!snapOn || !cmd || cmd.selecting) return null;
  const r = host.getBoundingClientRect(), mx = ev.clientX - r.left, my = ev.clientY - r.top, cam = camera(), v = new THREE.Vector3();
  let best = null, bd = 12;
  const test = (x, y, z, kind) => { v.set(x, y, z).project(cam); const sx = (v.x + 1) / 2 * r.width, sy = (1 - v.y) / 2 * r.height, d = Math.hypot(sx - mx, sy - my); if (d < bd) { bd = d; best = [x, y, z, kind]; } };
  for (const e of doc.ents) {
    if (layerOff(e) || SKIP2D.includes(e.type)) continue;
    const pts = snapPts(e); if (!pts.length) continue;
    if (e.type === 'solid') { if (e.kind === 'sph') { const z = lvZ(e.floor) + (e.z || 0); test(e.cx, e.cy, z, '중심'); continue; } const [z0, z1] = solidZ(e); for (const s of pts) { test(s[0], s[1], z0, s[2]); test(s[0], s[1], z1, s[2]); } }
    else { const z = lvZ(e.floor); for (const s of pts) test(s[0], s[1], z, s[2]); if (['wall', 'column', 'equip'].includes(e.type)) { const z1 = e.type === 'equip' ? z + (e.h || 1500) : lvTop(e.floor); for (const s of pts) test(s[0], s[1], z1, s[2]); } }
  }
  return best;
}
let last3 = null, cur3 = null;
cv.addEventListener('pointerdown', () => { last3 = null; });
function pointer3(ev) {
  const s = snap3(ev);
  if (s) return { p:[s[0], s[1]], z:s[2], snap:s };
  const H = hitAt(ev);
  if (H && H.face && H.nz > 0.9) return { p:[H.p[0], H.p[1]], z:H.p[2], hit:H };
  const q = planePt(ray(ev), curZ() + (S3.elev || 0));
  let p = [q[0], q[1]];
  if (cmd && !cmd.selecting) { const ref = refPoint(cmd); if (ref) p = applyOrtho(p, ref); }
  return { p, z:curZ() + (S3.elev || 0), hit:H };
}
function heightFromRay(ev, base) {
  const rc = ray(ev), o = rc.ray.origin, d = rc.ray.direction;
  const w0 = [o.x - base[0], o.y - base[1], o.z - base[2]], b = d.z, dd = 1, e = w0[0] * d.x + w0[1] * d.y + w0[2] * d.z, c = w0[2];
  const den = 1 - b * b; if (Math.abs(den) < 1e-6) return null;
  return (c - b * e) / den;
}
function drawLive(ev) {
  const T = THREE, L = V.live; L.children.slice().forEach(c => { L.remove(c); disposeObj(c); });
  if (!cur3) return;
  const [x, y] = cur3.p, z = cur3.z, s = cam3.size * 0.035, seg = (a, b, c) => { const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute([...a, ...b], 3)); L.add(new T.Line(g, new T.LineBasicMaterial({ color:c, depthTest:false }))); };
  seg([x - s, y, z], [x + s, y, z], '#e04848'); seg([x, y - s, z], [x, y + s, z], '#3aa64c'); seg([x, y, z], [x, y, z + s], '#3c7be0');
  if (cur3.snap) { const k = s * 0.3; const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute([x - k, y - k, z, x + k, y - k, z, x + k, y - k, z, x + k, y + k, z, x + k, y + k, z, x - k, y + k, z, x - k, y + k, z, x - k, y - k, z], 3)); L.add(new T.LineSegments(g, new T.LineBasicMaterial({ color:'#ff9f1a', depthTest:false }))); }
  if (cmd && !cmd.selecting) {
    const ref = refPoint(cmd); if (ref && !cmd.hBase) seg([ref[0], ref[1], cmd.refZ ?? z], [x, y, z], '#2f7fd1');
    if (cmd.def.preview) {
      let gh = []; try { gh = cmd.def.preview(cmd, cur3.p) || []; } catch (err) { gh = []; }
      for (const e of gh) {
        if (e.type === 'solid') { const T3 = solidTris(e); if (T3.length) { const m = meshFrom(T3, '#2f7fd1', 0.35); L.add(m); } continue; }
        let prs = null; try { prs = primsAny(e); } catch (err) { prs = null; }
        if (prs) { const ls = linesFrom(prs, cmd.refZ ?? z, '#2f7fd1'); if (ls) L.add(ls); }
      }
    }
  }
}

/* 마우스: 왼쪽 끌기 = 돌려보기, 가운데·Shift+왼쪽·오른쪽 끌기 = 이동, 휠 = 확대/축소, 클릭 = 점·선택, 오른쪽 클릭 = Enter */
let drag3 = null;
host.addEventListener('pointerdown', ev => {
  host.setPointerCapture(ev.pointerId); host.focus({ preventScroll:true });
  drag3 = { x:ev.clientX, y:ev.clientY, b:ev.button, pan:ev.button === 1 || ev.button === 2 || ev.shiftKey, az:cam3.az, el:cam3.el, tgt:cam3.tgt.slice(), moved:false };
  if (ev.button === 1) ev.preventDefault();
});
host.addEventListener('pointermove', ev => {
  if (!V) return;
  if (drag3) {
    const dx = ev.clientX - drag3.x, dy = ev.clientY - drag3.y;
    if (drag3.moved || Math.hypot(dx, dy) > 4) {
      drag3.moved = true;
      if (drag3.pan) {
        const k = cam3.size / (host.clientHeight || 1), d = camDir(), R = [-d[1], d[0], 0], rl = Math.hypot(R[0], R[1]) || 1, Rn = [R[0] / rl, R[1] / rl, 0];
        const U = [d[1] * Rn[2] - d[2] * Rn[1], d[2] * Rn[0] - d[0] * Rn[2], d[0] * Rn[1] - d[1] * Rn[0]];
        cam3.tgt = drag3.tgt.map((v, i) => v - Rn[i] * dx * k + U[i] * dy * k);
      } else { cam3.az = drag3.az - dx * 0.4; cam3.el = Math.max(-89.9, Math.min(89.9, drag3.el + dy * 0.4)); curView = ''; updLabels(); }
      buildHelpers(); reqLive(); return;
    }
  }
  cur3 = pointer3(ev);
  if (cmd && cmd.hBase) { const h = heightFromRay(ev, cmd.hBase); if (h != null) { cmd.dragH = Math.round(h / 10) * 10; cur3 = { p:[cmd.hBase[0], cmd.hBase[1]], z:cmd.hBase[2] + cmd.dragH }; } }
  cursor = cur3.p; snapHit = cur3.snap ? [cur3.snap[0], cur3.snap[1], cur3.snap[3]] : null;
  $('#coords').textContent = cmd && cmd.hBase && cmd.dragH != null ? `높이 ${fmt(cmd.dragH)}` : `${fmt(cur3.p[0])}, ${fmt(cur3.p[1])}, ${fmt(cur3.z)}`;
  drawLive(ev); reqLive();
});
const end3 = ev => {
  const d = drag3; drag3 = null;
  if (!d || d.moved || ev.type !== 'pointerup' || d.b !== 0) return;
  click3(ev);
};
host.addEventListener('pointerup', end3);
host.addEventListener('pointercancel', end3);
host.addEventListener('contextmenu', ev => { ev.preventDefault(); if (drag3 && drag3.moved) return; submitInput(''); });
host.addEventListener('auxclick', ev => { if (ev.button === 1 && ev.detail === 2) zoomExt3(); });
host.addEventListener('wheel', ev => {
  ev.preventDefault(); if (!V) return;
  const f = ev.deltaY < 0 ? 1 / 1.15 : 1.15, n = ndc(ev), W = host.clientWidth || 1, H = host.clientHeight || 1;
  const d = camDir(), R = [-d[1], d[0], 0], rl = Math.hypot(R[0], R[1]) || 1, Rn = [R[0] / rl, R[1] / rl, 0], U = [d[1] * Rn[2] - d[2] * Rn[1], d[2] * Rn[0] - d[0] * Rn[2], d[0] * Rn[1] - d[1] * Rn[0]];
  const ox = n.x * cam3.size * W / H / 2, oy = n.y * cam3.size / 2;
  cam3.tgt = cam3.tgt.map((v, i) => v + (Rn[i] * ox + U[i] * oy) * (1 - f)); cam3.size *= f;
  buildHelpers(); reqLive();
}, { passive:false });
function click3(ev) {
  const pt = pointer3(ev);
  last3 = { z:pt.z, hit:pt.hit || hitAt(ev) };
  if (cmd && cmd.hBase && cmd.def.height) { const h = heightFromRay(ev, cmd.hBase); if (h != null) { cmd.def.height(cmd, Math.round(h / 10) * 10); setPrompt(); draw(); return; } }
  if (cmd && !cmd.selecting && cmd.def.point) { cmd.def.point(cmd, pt.p, pt.p); setPrompt(); draw(); return; }
  const H = last3.hit;
  if (H && H.e) { sel.has(H.e.id) ? sel.delete(H.e.id) : sel.add(H.e.id); }
  else if (!cmd) sel.clear();
  setPrompt(); draw();
}

/* draw() 가로채기: 3D일 때는 3D 화면을 다시 그림 */
const draw0 = draw;
draw = (...a) => { if (is3D) { req(); if (cur3) drawLive(); return; } return draw0(...a); };

async function set3D(on, view, style) {
  if (!on) {
    is3D = false; host.style.display = 'none'; cur3 = null;
    if (V) V.live.children.slice().forEach(c => { V.live.remove(c); disposeObj(c); });
    updLabels(); paintCompass3(); draw0(); return;
  }
  if (!THREE) { status('3D 화면을 불러오는 중…'); try { await loadThree(); } catch (err) { status('3D 화면을 불러오지 못했습니다 — 인터넷 연결을 확인하세요'); addMsg('err', '3D 프로그램(three.js)을 불러오지 못했습니다: ' + err.message); return; } }
  if (!V) initV();
  const first = !is3D;
  is3D = true; host.style.display = 'block';
  if (style && STYLES[style]) { S3.style = style; saveSet(); }
  if (view && VIEWS[view]) { curView = view; cam3.az = VIEWS[view][1]; cam3.el = VIEWS[view][2]; }
  updLabels();
  if (first || view) { rebuild(); zoomExt3(); } else req();
  if (first) status('3D 화면 — 왼쪽 끌기: 돌려보기 · 가운데/오른쪽 끌기: 이동 · 휠: 확대 · 오른쪽 클릭: Enter');
}
const ro0 = window.runOps;
window.runOps = (ops, refs, opts = {}) => {
  const MINE = ['EXTRUDE', 'VIEW3D', 'PLAN'], mine = [], rest = [];
  for (const op of ops || []) (MINE.includes(String(op && op.op || '').toUpperCase()) ? mine : rest).push(op);
  const R = ro0(rest, refs, opts), fresh = new Set(Object.values(refs || {}));
  for (const op of mine) {
    const name = String(op.op).toUpperCase();
    try {
      if (name === 'VIEW3D') { set3D(true, VIEWS[op.view] ? op.view : (is3D ? null : 'swiso'), STYLES[op.style] ? op.style : null); R.done++; continue; }
      if (name === 'PLAN') { set3D(false); R.done++; continue; }
      const src = (Array.isArray(op.ids) ? op.ids : [op.ids]).map(v => (refs && refs[String(v)]) || String(v)).map(findEnt).filter(Boolean);
      if (opts.addOnly && src.some(e => !fresh.has(e.id))) { R.skipped++; continue; }
      const h = +op.h || S3.lastH, z = Number.isFinite(+op.z) ? +op.z : 0, del = ['rect', 'polyline', 'circle', 'ellipse', 'spline'];
      let n = 0;
      for (const e of src) {
        const base = { type:'solid', layer:e.layer, floor:e.floor || doc.cur, z, h };
        if (e.type === 'circle') addEnt(normH({ ...base, kind:'cyl', cx:e.cx, cy:e.cy, r:e.r }));
        else { const L = closedLoop(e); if (!L) continue; addEnt(normH({ ...base, kind:'ext', pts:L.map(p => [p[0], p[1]]) })); }
        n++; if (del.includes(e.type)) doc.ents = doc.ents.filter(x => x !== e);
      }
      if (!n) throw new Error('밀어올릴 닫힌 도형이 없습니다');
      R.done++;
    } catch (err) { R.skipped++; R.errors.push(`${name}: ${err.message}`); }
  }
  return R;
};
window.CAD3D = { set3D, get on() { return is3D; }, cam3, S3, zoomExt3, solidTris, req, get V() { return V; } };

/* ---------- 보기 이름표 · 방위 표시 ---------- */
const vp = $('#vpLabel'), vbtn = vp ? [...vp.querySelectorAll('button')] : [], bView = vbtn[2], bStyle = vbtn[3];
function popMenu(anchor, items) {
  document.querySelectorAll('.pop3').forEach(x => x.remove());
  const m = document.createElement('div'); m.className = 'pop3';
  m.style.cssText = 'position:fixed;z-index:60;background:#22272e;border:1px solid #39414b;border-radius:6px;padding:4px;box-shadow:0 8px 24px #0009;display:flex;flex-direction:column;min-width:170px';
  for (const it of items) {
    if (it === '-') { const s = document.createElement('div'); s.style.cssText = 'height:1px;background:#39414b;margin:3px 0'; m.appendChild(s); continue; }
    const b = document.createElement('button'); b.type = 'button'; b.textContent = (it.on ? '✓ ' : '　') + it.label;
    b.style.cssText = 'background:none;border:0;text-align:left;padding:5px 10px;font-size:12.5px;border-radius:4px;white-space:nowrap';
    b.onmouseenter = () => { b.style.background = '#2f7fd1'; }; b.onmouseleave = () => { b.style.background = 'none'; };
    b.onclick = () => { m.remove(); it.run(); }; m.appendChild(b);
  }
  document.body.appendChild(m);
  const r = anchor.getBoundingClientRect(); m.style.left = r.left + 'px'; m.style.top = r.bottom + 2 + 'px';
  setTimeout(() => document.addEventListener('pointerdown', function off(ev) { if (!m.contains(ev.target)) { m.remove(); document.removeEventListener('pointerdown', off); } }), 0);
}
const viewItems = () => [{ label:'평면 (2D 도면)', on:!is3D, run:() => set3D(false) }, '-',
  ...Object.entries(VIEWS).map(([k, v]) => ({ label:v[0], on:is3D && curView === k, run:() => set3D(true, k) })), '-',
  { label:'원근 보기', on:!!S3.persp, run:() => { S3.persp = !S3.persp; saveSet(); if (is3D) req(); else set3D(true); } }];
const styleItems = () => [{ label:'2D 선 (도면)', on:!is3D, run:() => set3D(false) }, '-',
  ...Object.entries(STYLES).map(([k, v]) => ({ label:v, on:is3D && S3.style === k, run:() => set3D(true, is3D ? null : 'swiso', k) }))];
if (bView) { bView.onclick = () => { bView.blur(); popMenu(bView, viewItems()); }; bView.title = '보기 방향 (평면·정면·측면·등각)'; }
if (bStyle) { bStyle.onclick = () => { bStyle.blur(); popMenu(bStyle, styleItems()); }; bStyle.title = '보기 방식 (2D 선·와이어·음영·모서리·X-레이)'; }
function updLabels() {
  if (bView) bView.textContent = `[${is3D ? (VIEWS[curView] ? VIEWS[curView][0] : '사용자 보기') : '평면도'}${is3D && S3.persp ? ' · 원근' : ''}]`;
  if (bStyle) bStyle.textContent = `[${is3D ? STYLES[S3.style] : '2D 선'}]`;
  if (window.ribbonRefresh) window.ribbonRefresh();
}
const cp = $('#compass');
function paintCompass3() {
  if (!cp) return;
  const rot = is3D ? cam3.az + 90 : 0;
  let g = cp.querySelector('g.rot');
  if (!g) {
    g = document.createElementNS('http://www.w3.org/2000/svg', 'g'); g.setAttribute('class', 'rot');
    for (const el of [...cp.querySelectorAll('.ring,.dir,.arrow')]) g.appendChild(el);
    cp.insertBefore(g, cp.querySelector('.cube'));
  }
  g.setAttribute('transform', `rotate(${rot} 50 50)`);
  const t = cp.querySelector('.cubet'); if (t) t.textContent = is3D ? (Math.abs(cam3.el) > 80 ? '위' : '3D') : '위';
}
if (cp) {
  cp.onclick = null;
  const DIRV = { 북:'back', 남:'front', 동:'right', 서:'left' };
  cp.querySelectorAll('.dir').forEach(t => { t.style.cursor = 'pointer'; t.addEventListener('click', ev => { ev.stopPropagation(); set3D(true, DIRV[t.textContent]); }); });
  const top = ev => { ev.stopPropagation(); if (is3D) set3D(true, 'top'); else zoomExtents(); };
  cp.querySelector('.cube').addEventListener('click', top); cp.querySelector('.cubet').addEventListener('click', top);
  cp.addEventListener('dblclick', ev => { ev.stopPropagation(); set3D(true, 'swiso'); });
  cp.querySelector('title').textContent = '방위 — 북·동·남·서를 누르면 그 방향에서 본 3D 입면, 가운데: 평면/전체 보기, 두 번 누르기: 남서 등각';
  paintCompass3();
}
const bZoom = $('#bZoom'); if (bZoom) bZoom.addEventListener('click', ev => { if (is3D) { ev.stopImmediatePropagation(); zoomExt3(); } }, true);

/* ---------- 명령 ---------- */
const pickZrel = () => { const z = last3 ? last3.z : null; last3 = null; return z != null ? Math.round(z - curZ()) : (S3.elev || 0); };
const hPrompt = (c, what) => { c.prompt = `${what}높이 <${fmt(S3.lastH)}> (숫자 입력 · 3D 화면에서는 마우스로 올려 클릭 · 아래로는 -):`; };
function heightStep(c, base2, zrel, apply) {
  c.hBase = [base2[0], base2[1], curZ() + zrel]; c.dragH = null;
  c.def.height = (cc, h) => { if (!h) return status('높이가 0입니다'); S3.lastH = Math.abs(h); saveSet(); apply(cc, h); };
  c.def.text = (cc, t) => { if (isNum(t)) { c.def.height(cc, +t); return true; } };
  c.def.enter = cc => c.def.height(cc, S3.lastH);
}
const normH = e => { if (e.h < 0) { e.z = (e.z || 0) + e.h; e.h = -e.h; if (e.kind === 'cyl' && e.r2 != null) [e.r, e.r2] = [e.r2, e.r]; } return e; };
function addSolid(e, msg) { snapshot(); const n = addEnt(normH({ type:'solid', layer:$('#layerSel') ? $('#layerSel').value : '0', ...e })); save(); endCmd(); status(msg || `${TYPE_KO.solid} 만들었습니다`); return n; }
const ghostH = c => (c.dragH != null ? c.dragH : S3.lastH);
Object.assign(CMDS, {
  '3DORBIT': () => ({ start() { endCmd(); set3D(true, is3D ? null : 'swiso'); } }),
  VIEW3D: () => ({ start() { endCmd(); set3D(true, is3D ? null : 'swiso'); } }),
  PLAN: () => ({ start() { endCmd(); set3D(false); } }),
  VIEW: () => ({
    start(c) { c.prompt = '보기 방향 [T=평면 3D / P=평면 도면 / F=정면 / BK=배면 / L=좌측 / R=우측 / SW·SE·NE·NW=등각]:'; },
    text(c, t) { const k = { T:'top', F:'front', BK:'back', L:'left', R:'right', SW:'swiso', SE:'seiso', NE:'neiso', NW:'nwiso' }[t.trim().toUpperCase()];
      if (t.trim().toUpperCase() === 'P') { endCmd(); set3D(false); return true; } if (!k) { status('T·P·F·BK·L·R·SW·SE·NE·NW 중에서 입력하세요'); return true; } endCmd(); set3D(true, k); return true; }
  }),
  VSCURRENT: () => ({
    start(c) { c.prompt = '보기 방식 [2=2D 선 / W=와이어 / S=음영 / E=음영+모서리 / X=X-레이]:'; },
    text(c, t) { const u = t.trim().toUpperCase(); if (u === '2') { endCmd(); set3D(false); return true; } const k = { W:'wire', S:'shade', E:'edge', X:'xray' }[u]; if (!k) { status('2·W·S·E·X 중에서 입력하세요'); return true; } endCmd(); set3D(true, is3D ? null : 'swiso', k); return true; }
  }),
  ELEV: () => ({
    start(c) { c.prompt = `작업 높이 — 새 입체·3D 클릭 바닥 (층 바닥 기준 mm) <${fmt(S3.elev || 0)}>:`; },
    text(c, t) { if (!isNum(t)) return false; S3.elev = +t; saveSet(); endCmd(); status(`작업 높이 ${fmt(S3.elev)} mm`); if (is3D) req(); return true; },
    enter() { endCmd(); }
  }),
  BOX: () => ({
    start(c) { c.prompt = '상자 첫 구석 (3D에서 입체 윗면을 찍으면 그 위에):'; },
    point(c, p) {
      if (!c.p1) { c.p1 = p; c.ref = p; c.z = pickZrel(); c.refZ = curZ() + c.z; c.prompt = '반대 구석 (@가로,세로):'; return; }
      if (!c.p2) {
        if (Math.abs(p[0] - c.p1[0]) < 1e-6 || Math.abs(p[1] - c.p1[1]) < 1e-6) return status('가로·세로가 0입니다');
        c.p2 = p; hPrompt(c, '상자 ');
        heightStep(c, p, c.z, (cc, h) => addSolid({ kind:'box', pts:rectPts({ x:Math.min(c.p1[0], c.p2[0]), y:Math.min(c.p1[1], c.p2[1]), w:Math.abs(c.p2[0] - c.p1[0]), h:Math.abs(c.p2[1] - c.p1[1]) }), z:c.z, h }, `상자 ${fmt(Math.abs(c.p2[0] - c.p1[0]))}×${fmt(Math.abs(c.p2[1] - c.p1[1]))}×${fmt(Math.abs(h))}`));
        return;
      }
      c.def.height(c, Math.round(Math.hypot(p[0] - c.p2[0], p[1] - c.p2[1])));
    },
    preview(c, cur) {
      if (!c.p1) return [];
      const q = c.p2 || cur, pts = rectPts({ x:Math.min(c.p1[0], q[0]), y:Math.min(c.p1[1], q[1]), w:Math.abs(q[0] - c.p1[0]), h:Math.abs(q[1] - c.p1[1]) });
      if (!c.p2) return [{ type:'polyline', pts, closed:true, ghost:true }];
      return [normH({ type:'solid', kind:'box', pts, z:c.z, h:ghostH(c), floor:doc.cur, ghost:true }), { type:'polyline', pts, closed:true, ghost:true }];
    }
  }),
  CYLINDER: () => cylCmd(false),
  CONE: () => cylCmd(true),
  SPHERE: () => ({
    start(c) { c.prompt = '구 중심:'; },
    point(c, p) {
      if (!c.cen) { c.cen = p; c.ref = p; c.z = pickZrel(); c.refZ = curZ() + c.z; c.prompt = '반지름 (숫자 또는 클릭):'; return; }
      const r = Math.hypot(p[0] - c.cen[0], p[1] - c.cen[1]); if (r > 0) addSolid({ kind:'sph', cx:c.cen[0], cy:c.cen[1], r, z:c.z }, `구 반지름 ${fmt(r)}`);
    },
    text(c, t) { if (c.cen && isNum(t) && +t > 0) { addSolid({ kind:'sph', cx:c.cen[0], cy:c.cen[1], r:+t, z:c.z }, `구 반지름 ${fmt(+t)}`); return true; } },
    preview(c, cur) { if (!c.cen) return []; const r = Math.hypot(cur[0] - c.cen[0], cur[1] - c.cen[1]); return r > 0 ? [{ type:'solid', kind:'sph', cx:c.cen[0], cy:c.cen[1], r, z:c.z, floor:doc.cur, ghost:true }, { type:'circle', cx:c.cen[0], cy:c.cen[1], r, ghost:true }] : []; }
  }),
  EXTRUDE: () => ({
    start(c) {
      selectStep(c, cc => {
        const src = [...sel].map(findEnt).filter(e => e && (e.type === 'circle' || closedLoop(e)) && e.type !== 'solid');
        if (!src.length) { endCmd(); return status('밀어올릴 닫힌 도형이 없습니다 (사각형·닫힌 폴리선·원·타원·실·슬라브)'); }
        cc.src = src; const b = bounds(src); hPrompt(cc, `${src.length}개 밀어올릴 `);
        heightStep(cc, [(b[0] + b[2]) / 2, (b[1] + b[3]) / 2], S3.elev || 0, (k, h) => {
          snapshot(); const del = ['rect', 'polyline', 'circle', 'ellipse', 'spline'];
          for (const e of k.src) {
            const base = { type:'solid', layer:e.layer, floor:e.floor || doc.cur, z:S3.elev || 0, h };
            if (e.color) base.color = e.color;
            addEnt(normH(e.type === 'circle' ? { ...base, kind:'cyl', cx:e.cx, cy:e.cy, r:e.r } : { ...base, kind:'ext', pts:closedLoop(e).map(p => [p[0], p[1]]) }));
          }
          doc.ents = doc.ents.filter(e => !(k.src.includes(e) && del.includes(e.type)));
          sel.clear(); save(); endCmd(); status(`${k.src.length}개를 ${fmt(Math.abs(h))} 밀어올렸습니다`);
        });
      }, '밀어올릴');
    },
    preview(c) {
      if (!c.src) return [];
      return c.src.map(e => normH(e.type === 'circle' ? { type:'solid', kind:'cyl', cx:e.cx, cy:e.cy, r:e.r, z:S3.elev || 0, h:ghostH(c), floor:e.floor || doc.cur } : { type:'solid', kind:'ext', pts:closedLoop(e), z:S3.elev || 0, h:ghostH(c), floor:e.floor || doc.cur }));
    }
  }),
  PRESSPULL: () => ({
    start(c) { c.prompt = '누르고 당길 곳 — 닫힌 도형 안 또는 입체 윗면·밑면을 클릭:'; },
    point(c, p) {
      if (c.tgt) { c.def.height(c, Math.round(Math.hypot(p[0] - c.hBase[0], p[1] - c.hBase[1]))); return; }
      const H = last3 && last3.hit; last3 = null;
      let tg = null;
      if (H && H.e && H.e.type === 'solid' && H.e.kind !== 'sph' && Math.abs(H.nz) > 0.9) tg = { solid:H.e, top:H.nz > 0 };
      if (!tg) {
        const cands = doc.ents.filter(e => !layerOff(e) && (!e.floor || e.floor === doc.cur));
        const sol = cands.filter(e => e.type === 'solid' && e.kind !== 'sph' && (e.kind === 'cyl' ? Math.hypot(p[0] - e.cx, p[1] - e.cy) <= e.r : inPoly(p, e.pts)));
        if (sol.length) tg = { solid:sol.sort((a, b) => solidZ(b)[1] - solidZ(a)[1])[0], top:true };
        else {
          const loops = cands.filter(e => e.type !== 'solid').map(e => ({ e, L:e.type === 'circle' ? null : closedLoop(e) })).filter(o => o.e.type === 'circle' ? Math.hypot(p[0] - o.e.cx, p[1] - o.e.cy) <= o.e.r : (o.L && inPoly(p, o.L)));
          if (loops.length) { const ar = o => o.e.type === 'circle' ? Math.PI * o.e.r * o.e.r : Math.abs(area2(o.L)); tg = { prof:loops.sort((a, b) => ar(a) - ar(b))[0] }; }
        }
      }
      if (!tg) return status('닫힌 도형 안이나 입체 윗면을 클릭하세요');
      c.tgt = tg;
      if (tg.solid) {
        const e = tg.solid, [z0, z1] = solidZ(e);
        const b = bounds([e]), cen = e.kind === 'cyl' ? [e.cx, e.cy] : [(b[0] + b[2]) / 2, (b[1] + b[3]) / 2];
        c.hBase = [cen[0], cen[1], tg.top ? z1 : z0]; c.prompt = `${tg.top ? '윗면' : '밑면'}을 얼마나 (+ 바깥으로 / - 안으로) <${fmt(S3.lastH)}>:`;
        heightStep(c, cen, (tg.top ? z1 : z0) - curZ(), (cc, d) => {
          snapshot(); const x = findEnt(e.id) || e;
          if (tg.top) x.h = (x.h || 0) + d; else { x.z = (x.z || 0) - d; x.h = (x.h || 0) + d; }
          if (x.h <= 0) { doc.ents = doc.ents.filter(q => q !== x); status('입체가 없어졌습니다 (높이 0 이하)'); } else { normH(x); status(`높이 ${fmt(x.h)}`); }
          save(); endCmd();
        });
      } else {
        const o = tg.prof.e, b = bounds([o]), cen = [(b[0] + b[2]) / 2, (b[1] + b[3]) / 2];
        c.prompt = `밀어올릴 높이 (+ 위 / - 아래) <${fmt(S3.lastH)}>:`;
        heightStep(c, cen, S3.elev || 0, (cc, h) => addSolid(o.type === 'circle' ? { kind:'cyl', cx:o.cx, cy:o.cy, r:o.r, z:S3.elev || 0, h, floor:o.floor || doc.cur, layer:o.layer } : { kind:'ext', pts:tg.prof.L.map(q => [q[0], q[1]]), z:S3.elev || 0, h, floor:o.floor || doc.cur, layer:o.layer }, `${fmt(Math.abs(h))} 밀어올렸습니다`));
      }
    },
    preview(c) {
      if (!c.tgt) return [];
      const dh = c.dragH; if (dh == null) return [];
      if (c.tgt.solid) { const e = JSON.parse(JSON.stringify(c.tgt.solid)); if (c.tgt.top) e.h = (e.h || 0) + dh; else { e.z = (e.z || 0) - dh; e.h = (e.h || 0) + dh; } return e.h > 0 ? [normH(e)] : []; }
      const o = c.tgt.prof.e;
      return [normH(o.type === 'circle' ? { type:'solid', kind:'cyl', cx:o.cx, cy:o.cy, r:o.r, z:S3.elev || 0, h:dh, floor:o.floor || doc.cur } : { type:'solid', kind:'ext', pts:c.tgt.prof.L, z:S3.elev || 0, h:dh, floor:o.floor || doc.cur })];
    }
  }),
  OBJOUT: () => ({ start() { endCmd(); export3D('obj'); } }),
  STLOUT: () => ({ start() { endCmd(); export3D('stl'); } })
});
function cylCmd(cone) {
  const nm = cone ? '원뿔' : '원기둥';
  return {
    start(c) { c.prompt = `${nm} 밑면 중심 (3D에서 입체 윗면을 찍으면 그 위에):`; },
    point(c, p) {
      if (!c.cen) { c.cen = p; c.ref = p; c.z = pickZrel(); c.refZ = curZ() + c.z; c.prompt = '밑면 반지름 (숫자 또는 클릭):'; return; }
      if (!c.r) { const r = Math.hypot(p[0] - c.cen[0], p[1] - c.cen[1]); if (r > 0) setR(c, r); return; }
      c.def.height(c, Math.round(Math.hypot(p[0] - c.cen[0], p[1] - c.cen[1])));
    },
    text(c, t) { if (c.cen && !c.r && isNum(t) && +t > 0) { setR(c, +t); return true; } },
    preview(c, cur) {
      if (!c.cen) return [];
      const r = c.r || Math.hypot(cur[0] - c.cen[0], cur[1] - c.cen[1]); if (!(r > 0)) return [];
      const out = [{ type:'circle', cx:c.cen[0], cy:c.cen[1], r, ghost:true }];
      if (c.r) out.unshift(normH({ type:'solid', kind:'cyl', cx:c.cen[0], cy:c.cen[1], r, r2:cone ? 0 : r, z:c.z, h:ghostH(c), floor:doc.cur }));
      return out;
    }
  };
  function setR(c, r) {
    c.r = r; hPrompt(c, `${nm} `);
    heightStep(c, c.cen, c.z, (cc, h) => addSolid({ kind:'cyl', cx:c.cen[0], cy:c.cen[1], r, ...(cone ? { r2:0 } : {}), z:c.z, h }, `${nm} 반지름 ${fmt(r)} 높이 ${fmt(Math.abs(h))}`));
  }
}
function export3D(fmtK) {
  const tris = [];
  for (const e of doc.ents) { if (layerOff(e)) continue; const T = window.CAD3D_TRIS(e); if (T.length) tris.push({ e, T }); }
  if (!tris.length) return status('내보낼 입체·벽이 없습니다');
  if (fmtK === 'obj') {
    const L = ['# 말로 캐드 OBJ — 단위 mm, Z가 위쪽'], push = (s) => L.push(s); let vi = 1;
    for (const { e, T } of tris) {
      push(`o ${TYPE_KO[e.type] || e.type}_${e.id}`);
      for (const t of T) { for (const p of t) push(`v ${p[0].toFixed(2)} ${p[1].toFixed(2)} ${p[2].toFixed(2)}`); push(`f ${vi} ${vi + 1} ${vi + 2}`); vi += 3; }
    }
    download(new Blob([L.join('\n')], { type:'text/plain' }), `model_${stamp()}.obj`);
  } else {
    const n = tris.reduce((s, x) => s + x.T.length, 0), buf = new ArrayBuffer(84 + n * 50), dv = new DataView(buf); dv.setUint32(80, n, true); let o = 84;
    for (const { T } of tris) for (const t of T) {
      const a = t[0], b = t[1], c = t[2], u = [b[0] - a[0], b[1] - a[1], b[2] - a[2]], v = [c[0] - a[0], c[1] - a[1], c[2] - a[2]];
      const nn = [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]], l = Math.hypot(...nn) || 1;
      for (const x of nn) { dv.setFloat32(o, x / l, true); o += 4; }
      for (const p of t) for (const x of p) { dv.setFloat32(o, x, true); o += 4; }
      o += 2;
    }
    download(new Blob([buf], { type:'application/octet-stream' }), `model_${stamp()}.stl`);
  }
  status(`${fmtK.toUpperCase()}로 내보냈습니다 (단위 mm, Z가 위쪽)`);
}
Object.assign(CMD_DESC, {
  '3DORBIT':'3D 보기 (돌려보기)', PLAN:'평면 도면(2D)으로', VIEW:'보기 방향 (평면·정면·측면·등각)', VSCURRENT:'보기 방식 (2D 선·와이어·음영·모서리·X-레이)', ELEV:'작업 높이 (새 입체 바닥)',
  BOX:'상자', CYLINDER:'원기둥', CONE:'원뿔', SPHERE:'구', EXTRUDE:'밀어올리기 (닫힌 도형 → 입체)', PRESSPULL:'누르고 당기기 (도형 안·입체 면 클릭)', OBJOUT:'OBJ로 내보내기 (3D)', STLOUT:'STL로 내보내기 (3D 프린터)', VIEW3D:'3D 보기'
});
{
  const AL = { '3DO':'3DORBIT', '3D':'3DORBIT', ORBIT:'3DORBIT', VS:'VSCURRENT', CYL:'CYLINDER', EXT:'EXTRUDE', PRESS:'PRESSPULL', PP:'PRESSPULL', '-V':'VIEW' };
  Object.assign(DEFAULT_ALIASES, AL);
  for (const [k, v] of Object.entries(AL)) if (settings.aliases[k] == null || ['VIEW3D'].includes(settings.aliases[k])) settings.aliases[k] = v;
  const C = (cmd, label, key) => ({ cmd, label, key });
  const dr = M('그리기'); dr.push('-', C('BOX', '상자', 'BOX'), C('CYLINDER', '원기둥', 'CYL'), C('CONE', '원뿔', 'CONE'), C('SPHERE', '구', 'SPHERE'), C('EXTRUDE', '밀어올리기', 'EXT'), C('PRESSPULL', '누르고 당기기', 'PRESS'));
  const bo = M('보기'); const i3 = bo.findIndex(x => x && x.cmd === 'VIEW3D'); if (i3 >= 0) bo.splice(i3, 1);
  bo.push('-', C('3DORBIT', '3D 보기 (돌려보기)', '3DO'), C('PLAN', '평면 도면 (2D)', 'PLAN'), C('VIEW', '보기 방향…', 'VIEW'), C('VSCURRENT', '보기 방식…', 'VS'), C('ELEV', '작업 높이…', 'ELEV'));
  const fi = M('파일'); const j = fi.findIndex(x => Array.isArray(x) ? false : x && x.cmd === 'DWGOUT'); fi.splice(j >= 0 ? j + 1 : fi.length, 0, C('OBJOUT', 'OBJ로 내보내기 (3D)'), C('STLOUT', 'STL로 내보내기 (3D)'));
  buildMenus(); if (typeof buildHelp === 'function') buildHelp();
}
Object.assign(ICONS, {
  box3:'<path d="m12 3 8 4.5v9L12 21l-8-4.5v-9z"/><path d="m4 7.5 8 4.5 8-4.5M12 12v9"/>',
  cyl3:'<ellipse cx="12" cy="6" rx="7" ry="2.6"/><path d="M5 6v12c0 1.4 3.1 2.6 7 2.6s7-1.2 7-2.6V6"/>',
  cone3:'<path d="M12 3 5 18M12 3l7 15"/><ellipse cx="12" cy="18" rx="7" ry="2.6"/>',
  sph3:'<circle cx="12" cy="12" r="8"/><ellipse cx="12" cy="12" rx="8" ry="3"/>',
  ext3:'<path d="M4 17h11l5-4H9z"/><path d="M4 17V9M15 17V9M20 13V5M9 13V5" stroke-dasharray="2 2"/><path d="M12 11V3M9.5 5.5 12 3l2.5 2.5"/>',
  pp3:'<rect x="5" y="12" width="14" height="8"/><path d="M12 10V3M9.5 5.5 12 3l2.5 2.5"/>',
  orbit:'<circle cx="12" cy="12" r="3"/><ellipse cx="12" cy="12" rx="9" ry="4"/><path d="m19 8 2 .5-1 2"/>',
  plan2:'<rect x="4" y="4" width="16" height="16"/><path d="M4 12h9V4"/>',
  iso:'<path d="m12 3 8 4.5v9L12 21l-8-4.5v-9z"/><path d="m4 7.5 8 4.5 8-4.5M12 12v9"/><circle cx="4.5" cy="16.5" r="1.6" fill="currentColor"/>',
  front:'<rect x="4" y="7" width="16" height="12"/><path d="M4 7l3-3h16l-3 3"/>',
  wire3:'<path d="m12 3 8 4.5v9L12 21l-8-4.5v-9z"/><path d="m4 7.5 8 4.5 8-4.5M12 12v9M12 3v9M4 16.5l8-4.5 8 4.5" stroke-dasharray="2 2"/>',
  shade3:'<path d="m12 3 8 4.5v9L12 21l-8-4.5v-9z" fill="currentColor" fill-opacity=".35"/><path d="m4 7.5 8 4.5 8-4.5M12 12v9"/>',
  xray3:'<path d="m12 3 8 4.5v9L12 21l-8-4.5v-9z" fill="currentColor" fill-opacity=".12"/><path d="m4 7.5 8 4.5 8-4.5M12 12v9M12 3v9" />',
  persp:'<path d="M3 20 9 4h6l6 16z"/><path d="M6 13h12"/>',
  elev3:'<path d="M3 18h18"/><path d="M6 14h12" stroke-dasharray="3 2"/><path d="M12 13V4M9.5 6.5 12 4l2.5 2.5"/>',
  obj3:'<path d="M6 3h8l4 4v14H6z"/><text x="12" y="17" font-size="6" text-anchor="middle" style="fill:currentColor;stroke:none;font-weight:700">OBJ</text>',
  stl3:'<path d="M6 3h8l4 4v14H6z"/><text x="12" y="17" font-size="6" text-anchor="middle" style="fill:currentColor;stroke:none;font-weight:700">STL</text>'
});
if (window.CAD_RIBBON) {
  const { addTab, C, F } = window.CAD_RIBBON;
  const V3 = k => F(() => set3D(true, k), VIEWS[k][0], k === 'top' ? 'plan2' : k === 'front' || k === 'back' || k === 'left' || k === 'right' ? 'front' : 'iso', () => is3D && curView === k);
  const ST = (k, icn) => F(() => set3D(true, is3D ? null : 'swiso', k), STYLES[k], icn, () => is3D && S3.style === k);
  addTab('3D', [
    { t:'모델링', cols:[C('BOX', '상자', 'box3'), C('CYLINDER', '원기둥', 'cyl3'), [C('CONE', '원뿔', 'cone3'), C('SPHERE', '구', 'sph3'), C('ELEV', '작업 높이', 'elev3')], C('EXTRUDE', '밀어\n올리기', 'ext3'), C('PRESSPULL', '누르고\n당기기', 'pp3')] },
    { t:'보기', cols:[F(() => set3D(true, is3D ? null : 'swiso'), '3D\n보기', 'orbit', () => is3D), F(() => set3D(false), '평면\n도면', 'plan2', () => !is3D), [V3('swiso'), V3('seiso'), V3('top')], [V3('front'), V3('right'), V3('left')], [V3('back'), V3('neiso'), V3('nwiso')]] },
    { t:'보기 방식', cols:[[F(() => set3D(false), '2D 선 (도면)', 'plan2', () => !is3D), ST('wire', 'wire3'), ST('shade', 'shade3')], [ST('edge', 'box3'), ST('xray', 'xray3'), F(() => { S3.persp = !S3.persp; saveSet(); if (is3D) req(); else set3D(true, 'swiso'); updLabels(); }, '원근 보기', 'persp', () => !!S3.persp)]] },
    { t:'내보내기', cols:[C('OBJOUT', 'OBJ', 'obj3'), C('STLOUT', 'STL', 'stl3'), F(() => $('#bDxf').click(), 'DXF\n(3D면)', 'dxf')] }
  ], '삽입');
}
updLabels();
})();
