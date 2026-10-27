# -*- coding: utf-8 -*-
# 말로 캐드가 내보낸 건축 요소 JSON(elements_*.json)만 읽어서 3D를 세우는 생성기 (Blender 헤드리스)
#   blender --background --python gen3d.py -- <elements.json> <출력접두어>
# 입력은 mm(평면 좌표, Y+=북), 레벨은 m. 도면에 없는 값은 만들지 않고, 가정한 값은 아래 ASSUME에 모아 화면(로그)에 밝힌다.
import bpy, bmesh, json, math, os, sys

argv = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else []
SRC = argv[0] if argv else "elements.json"
OUT = argv[1] if len(argv) > 1 else os.path.splitext(SRC)[0] + "_3d"
D = json.load(open(SRC, encoding="utf-8"))

ASSUME = {"slab_t_m": 0.15, "door_h_m": 2.1, "glass_t_m": 0.03}   # 도면에 없을 때만 쓰는 가정값
used_assume = set()

bpy.ops.wm.read_factory_settings(use_empty=True)
scene = bpy.context.scene

def mat(name, col, rough=0.5, metal=0.0, alpha=1.0):
    m = bpy.data.materials.new(name); m.use_nodes = True
    b = m.node_tree.nodes["Principled BSDF"]
    b.inputs["Base Color"].default_value = (*col, 1)
    b.inputs["Roughness"].default_value = rough
    b.inputs["Metallic"].default_value = metal
    if alpha < 1:
        b.inputs["Alpha"].default_value = alpha
        try: m.blend_method = 'BLEND'
        except Exception: pass
    return m

M_WALL = mat("wall", (0.9, 0.9, 0.9), 0.6)
M_PART = mat("partition", (0.82, 0.82, 0.8), 0.7)
M_SLAB = mat("slab", (0.62, 0.62, 0.64), 0.7)
M_CANOPY = mat("canopy", (0.86, 0.87, 0.88), 0.35, 0.3)
M_GLASS = mat("glass", (0.5, 0.7, 0.8), 0.05, 0.0, 0.45)
M_COL = mat("column", (0.8, 0.8, 0.82), 0.3, 0.5)
M_GROUND = mat("ground", (0.6, 0.58, 0.54), 0.9)
M_SITE = mat("site", (0.1, 0.1, 0.11), 0.8)
M_LINE = mat("boundary", (1, 0.05, 0.05), 0.4)
M_DOOR = mat("door", (0.35, 0.25, 0.18), 0.5)

# 좌표 원점: 대지 경계(없으면 건물) 중심
pts_all = [p for r in D.get("siteBoundary", []) for p in r] or [p for b in D.get("buildings", []) for p in b["pts"]] or [[0, 0]]
CX = (min(p[0] for p in pts_all) + max(p[0] for p in pts_all)) / 2.0
CY = (min(p[1] for p in pts_all) + max(p[1] for p in pts_all)) / 2.0
def P(x, y): return ((x - CX) / 1000.0, (y - CY) / 1000.0)

def new(name, material):
    me = bpy.data.meshes.new(name); ob = bpy.data.objects.new(name, me)
    scene.collection.objects.link(ob); me.materials.append(material); return ob, me

def prism(name, pts_m, z0, z1, material):
    if len(pts_m) < 3 or z1 - z0 <= 1e-4: return None
    ob, me = new(name, material); bm = bmesh.new()
    vs = [bm.verts.new((x, y, z0)) for x, y in pts_m]
    try:
        f = bm.faces.new(vs)
    except ValueError:
        bm.free(); return None
    r = bmesh.ops.extrude_face_region(bm, geom=[f])
    ev = [v for v in r["geom"] if isinstance(v, bmesh.types.BMVert)]
    bmesh.ops.translate(bm, vec=(0, 0, z1 - z0), verts=ev)
    bmesh.ops.triangulate(bm, faces=bm.faces[:])
    bmesh.ops.recalc_face_normals(bm, faces=bm.faces[:])
    bm.to_mesh(me); bm.free(); return ob

def cyl(name, x, y, r, z0, z1, material):
    ob, me = new(name, material); bm = bmesh.new()
    bmesh.ops.create_cone(bm, cap_ends=True, segments=32, radius1=r, radius2=r, depth=z1 - z0)
    bmesh.ops.translate(bm, vec=(x, y, (z0 + z1) / 2), verts=bm.verts)
    bm.to_mesh(me); bm.free(); return ob

def seg_prism(name, a, b, s0, s1, t, z0, z1, material):
    # 벽 중심선 a->b 위의 [s0,s1](m) 구간을 두께 t(m)로 z0~z1 세움
    L = math.hypot(b[0] - a[0], b[1] - a[1]); ux, uy = (b[0] - a[0]) / L, (b[1] - a[1]) / L; nx, ny = -uy * t / 2, ux * t / 2
    p0 = (a[0] + ux * s0, a[1] + uy * s0); p1 = (a[0] + ux * s1, a[1] + uy * s1)
    return prism(name, [(p0[0] + nx, p0[1] + ny), (p1[0] + nx, p1[1] + ny), (p1[0] - nx, p1[1] - ny), (p0[0] - nx, p0[1] - ny)], z0, z1, material)

# ---------- 대지·바닥 ----------
prism("ground", [(-150, -150), (150, -150), (150, 150), (-150, 150)], -0.08, -0.03, M_GROUND)
for i, ring in enumerate(D.get("siteBoundary", [])):
    rp = [P(*p) for p in ring]
    prism(f"site{i}", rp, -0.03, 0.0, M_SITE)
    for k in range(len(rp)):
        a, b = rp[k], rp[(k + 1) % len(rp)]; L = math.hypot(b[0] - a[0], b[1] - a[1]) or 1
        nx, ny = -(b[1] - a[1]) / L * 0.09, (b[0] - a[0]) / L * 0.09
        prism(f"bnd{i}_{k}", [(a[0] + nx, a[1] + ny), (b[0] + nx, b[1] + ny), (b[0] - nx, b[1] - ny), (a[0] - nx, a[1] - ny)], 0.0, 0.05, M_LINE)
for i, s in enumerate(D.get("setbackLines", [])):
    a, b = P(s[0], s[1]), P(s[2], s[3]); L = math.hypot(b[0] - a[0], b[1] - a[1]) or 1
    nx, ny = -(b[1] - a[1]) / L * 0.06, (b[0] - a[0]) / L * 0.06
    prism(f"setback{i}", [(a[0] + nx, a[1] + ny), (b[0] + nx, b[1] + ny), (b[0] - nx, b[1] - ny), (a[0] - nx, a[1] - ny)], 0.0, 0.04, M_LINE)

# ---------- 벽 (창·문 개구부를 뚫어서) ----------
openings = []
for w in D.get("windows", []):
    openings.append(dict(kind="win", floor=w.get("floor"), a=(w["x1"], w["y1"]), b=(w["x2"], w["y2"]), z0=(w["el0"] or 0) + (w.get("sill") if w.get("sill") is not None else 900) / 1000.0,
                         z1=(w["el0"] or 0) + ((w.get("sill") if w.get("sill") is not None else 900) + (w.get("h") or 1500)) / 1000.0))
for d in D.get("doors", []):
    ang = math.radians(d.get("ang") or 0); w_ = d.get("w") or 900
    dh = d.get("h");
    if dh is None: used_assume.add("door_h_m")
    openings.append(dict(kind="door", floor=d.get("floor"), a=(d["x"], d["y"]), b=(d["x"] + math.cos(ang) * w_, d["y"] + math.sin(ang) * w_), z0=d.get("el0") or 0,
                         z1=(d.get("el0") or 0) + ((dh / 1000.0) if dh is not None else ASSUME["door_h_m"])))

def on_wall(op, wall):
    ax, ay, bx, by = wall["x1"], wall["y1"], wall["x2"], wall["y2"]; L = math.hypot(bx - ax, by - ay)
    if L < 1: return None
    ux, uy = (bx - ax) / L, (by - ay) / L; t = wall.get("t") or 200
    ss = []
    for (px, py) in (op["a"], op["b"]):
        s = (px - ax) * ux + (py - ay) * uy; dist = abs(-(px - ax) * uy + (py - ay) * ux)
        if dist > t / 2 + 80: return None
        ss.append(s)
    s0, s1 = max(0.0, min(ss)), min(L, max(ss))
    return (s0 / 1000.0, s1 / 1000.0) if s1 - s0 > 50 else None

wall_n = 0
for wi, w in enumerate(D.get("walls", [])):
    f = w.get("floor"); z0 = w.get("el0"); z1 = w.get("el1")
    if z0 is None or z1 is None: continue
    a, b = P(w["x1"], w["y1"]), P(w["x2"], w["y2"]); L = math.hypot(b[0] - a[0], b[1] - a[1]); t = (w.get("t") or 200) / 1000.0
    mt = M_WALL if w.get("kind") == "struct" else M_PART
    ops = []
    for op in openings:
        if op["floor"] != f: continue
        rng = on_wall(op, w)
        if rng: ops.append((rng[0], rng[1], op))
    ops.sort(key=lambda o: o[0])
    cur = 0.0
    for k, (s0, s1, op) in enumerate(ops):
        if s0 > cur + 1e-3: seg_prism(f"w{wi}_g{k}", a, b, cur, s0, t, z0, z1, mt)
        if op["z0"] > z0 + 1e-3: seg_prism(f"w{wi}_lo{k}", a, b, s0, s1, t, z0, op["z0"], mt)
        if op["z1"] < z1 - 1e-3: seg_prism(f"w{wi}_hi{k}", a, b, s0, s1, t, op["z1"], z1, mt)
        gt = ASSUME["glass_t_m"]
        if op["kind"] == "win": seg_prism(f"w{wi}_glass{k}", a, b, s0, s1, gt, op["z0"], op["z1"], M_GLASS)
        else: seg_prism(f"w{wi}_door{k}", a, b, s0, s1, 0.04, op["z0"], op["z1"], M_DOOR)
        cur = max(cur, s1)
    if L - cur > 1e-3: seg_prism(f"w{wi}_end", a, b, cur, L, t, z0, z1, mt)
    wall_n += 1

# ---------- 층 슬라브(건물 외곽 기준): 각 층 천장 슬라브 + 최하층 바닥 슬라브 ----------
st = ASSUME["slab_t_m"]; used_assume.add("slab_t_m")
lowest = {}
for b in D.get("buildings", []):
    if b.get("kind") == "excl" or b.get("el0") is None: continue
    rp = [P(*p) for p in b["pts"]]
    prism(f"slab_top_{b['floor']}", rp, b["el1"] - st, b["el1"], M_SLAB)
    if b["floor"] not in lowest or b["el0"] < lowest[b["floor"]]["el0"]: lowest[b["floor"]] = b
if lowest:
    b = min(lowest.values(), key=lambda x: x["el0"])
    prism("slab_ground", [P(*p) for p in b["pts"]], b["el0"] - st, b["el0"], M_SLAB)

# ---------- 슬라브(캐노피·지붕) · 기둥 ----------
for i, s in enumerate(D.get("slabs", [])):
    prism(f"slab_{i}_{s.get('name','')}", [P(*p) for p in s["pts"]], s["top_el_m"] - s["thickness_mm"] / 1000.0, s["top_el_m"], M_CANOPY)
for i, c in enumerate(D.get("columns", [])):
    z0, z1 = c.get("el0"), c.get("el1")
    if z0 is None or z1 is None: continue
    x, y = P(c["cx"], c["cy"])
    if c.get("r"): cyl(f"col{i}", x, y, c["r"] / 1000.0, z0, z1, M_COL)
    else:
        w, d = (c.get("w") or 200) / 1000.0, (c.get("d") or c.get("w") or 200) / 1000.0
        prism(f"col{i}", [(x - w / 2, y - d / 2), (x + w / 2, y - d / 2), (x + w / 2, y + d / 2), (x - w / 2, y + d / 2)], z0, z1, M_COL)

# ---------- 설비(주유기): 완공 사진 기준 형상 ----------
# 사진(확대)에서 읽은 구조: 아일랜드 1개에 주유기 1대. 빨간 캐비닛 1개(긴변 2면 = 앞/뒤), 윗부분에 흰 계량 패널(디스플레이),
# 긴변 한쪽 끝(편심)에 흰 기둥 + 그 위에서 캐비닛 쪽으로 뻗은 흰 덮개(ㄱ자), 덮개에서 호스가 늘어져 캐비닛 노즐 거치대로 연결.
# 6복식 = 노즐 6개 = 한 면(긴변)에 3개씩 × 2면. 아일랜드 양 끝 주황 U자 볼라드(바닥 기준 400mm).
# 높이·기둥 위치(동쪽 끝)·아일랜드 여유 등은 사진 눈대중(도면에 없음) → ASSUME에 밝힘. 평면 크기(w×d)와 위치는 도면 값.
M_DISP_RED = mat("disp_red", (0.72, 0.06, 0.07), 0.35)
M_DISP_WHITE = mat("disp_white", (0.92, 0.92, 0.92), 0.4)
M_DISP_DARK = mat("disp_dark", (0.12, 0.12, 0.13), 0.5)
M_ISLAND = mat("island", (0.74, 0.73, 0.7), 0.85)
M_BOLLARD = mat("bollard", (0.95, 0.45, 0.05), 0.4)
M_HOSE = [mat("hose_k", (0.03, 0.03, 0.04), 0.6), mat("hose_y", (0.95, 0.8, 0.05), 0.5), mat("hose_b", (0.1, 0.2, 0.7), 0.5)]
ASSUME.update({"dispenser_h_m": 2.3, "island_h_m": 0.15, "island_margin_m": 0.25, "bollard_top_from_ground_m": 0.4,
               "disp_cabinet_h_m": 1.0, "disp_head_h_m": 1.4, "disp_post_end": "+x(동쪽 끝)"})

def rbox(name, cx, cy, ang, x0, x1, y0, y1, z0, z1, material):
    # 장비 로컬좌표(x0..x1, y0..y1, m)의 상자를 중심 (cx,cy), 각도 ang(rad)로 돌려 세움
    c, s = math.cos(ang), math.sin(ang)
    pts = [(cx + x * c - y * s, cy + x * s + y * c) for x, y in ((x0, y0), (x1, y0), (x1, y1), (x0, y1))]
    return prism(name, pts, z0, z1, material)

def tube(name, p0, p1, r, material):
    # 3D 점 p0->p1 사이 원통(호스)
    from mathutils import Vector
    v0, v1 = Vector(p0), Vector(p1); d = v1 - v0
    if d.length < 1e-4: return None
    ob, me = new(name, material); bm = bmesh.new()
    bmesh.ops.create_cone(bm, cap_ends=True, segments=8, radius1=r, radius2=r, depth=d.length)
    bm.to_mesh(me); bm.free()
    ob.rotation_euler = d.to_track_quat('Z', 'Y').to_euler(); ob.location = (v0 + v1) / 2
    return ob

for i, e in enumerate(D.get("equipment", [])):
    cx, cy = P(e["cx"], e["cy"]); w, d = (e.get("w") or 1200) / 1000.0, (e.get("d") or 500) / 1000.0
    ang = math.radians(e.get("ang") or 0); z0 = e.get("el0") or 0.0
    c_, s_ = math.cos(ang), math.sin(ang)
    def loc3(x, y, z): return (cx + x * c_ - y * s_, cy + x * s_ + y * c_, z)
    if e.get("kind") == "dispenser":
        for k in ("dispenser_h_m", "island_h_m", "island_margin_m", "bollard_top_from_ground_m", "disp_cabinet_h_m", "disp_head_h_m", "disp_post_end"): used_assume.add(k)
        H = (e["h"] / 1000.0) if e.get("h") else ASSUME["dispenser_h_m"]
        ih, im = ASSUME["island_h_m"], ASSUME["island_margin_m"]
        ch, hh = ASSUME["disp_cabinet_h_m"], ASSUME["disp_head_h_m"]
        top = z0 + ih
        rbox(f"eq{i}_island", cx, cy, ang, -w / 2 - im, w / 2 + im, -d / 2 - im, d / 2 + im, z0, top, M_ISLAND)
        # 캐비닛 1개(앞·뒤 2면): 어두운 하부 받침 + 빨간 본체 + 흰 계량 패널(서쪽 끝 쪽, 디스플레이는 양면)
        rbox(f"eq{i}_skirt", cx, cy, ang, -w / 2 + 0.02, w / 2 - 0.02, -d / 2 + 0.02, d / 2 - 0.02, top, top + 0.15, M_DISP_DARK)
        rbox(f"eq{i}_cab", cx, cy, ang, -w / 2, w / 2, -d / 2, d / 2, top + 0.14, top + ch, M_DISP_RED)
        px0, px1 = -w / 2, -w / 2 + w * 0.42                      # 계량 패널: 서쪽 끝 쪽 42%
        rbox(f"eq{i}_head", cx, cy, ang, px0, px1, -d / 2, d / 2, top + ch - 0.01, top + hh, M_DISP_WHITE)
        for sgn in (-1, 1):
            rbox(f"eq{i}_scr{sgn}", cx, cy, ang, px0 + 0.08, px1 - 0.08, sgn * (d / 2 - 0.01), sgn * (d / 2 + 0.012), top + ch + 0.12, top + hh - 0.08, M_DISP_DARK)
        # 편심 기둥(동쪽 끝) + ㄱ자 덮개(기둥 위에서 서쪽 방향으로 캐비닛 위를 덮음)
        pw = 0.16
        rbox(f"eq{i}_post", cx, cy, ang, w / 2 - pw, w / 2, -d / 2 * 0.7, d / 2 * 0.7, top + 0.02, top + H, M_DISP_WHITE)
        rbox(f"eq{i}_cap", cx, cy, ang, -w / 2 + 0.1, w / 2, -d / 2 - 0.03, d / 2 + 0.03, top + H - 0.1, top + H, M_DISP_WHITE)
        # 호스: 한 면(긴변)당 3개 × 2면 = 6. 덮개 아래 기둥 옆에서 늘어져 노즐 거치대(캐비닛 상부 동쪽 쪽)로
        for sgn in (-1, 1):
            yf = sgn * (d / 2)
            rbox(f"eq{i}_holster{sgn}", cx, cy, ang, w / 2 - 0.55, w / 2 - 0.12, yf - sgn * 0.02, yf + sgn * 0.05, top + ch - 0.28, top + ch - 0.04, M_DISP_DARK)
            for k in range(3):
                xh = w / 2 - pw - 0.05 - k * 0.09                  # 호스 3개: 기둥 옆에서 서쪽으로 0.09m 간격
                xn = w / 2 - 0.2 - k * 0.12                        # 노즐(거치대) 위치
                yt = sgn * (d / 2 * 0.55); yn = sgn * (d / 2 + 0.04)
                mt = M_HOSE[k]
                pts = [loc3(xh, yt, top + H - 0.1), loc3(xh - 0.02, sgn * (d / 2 + 0.05), top + ch + 0.55),
                       loc3(xn, yn, top + ch - 0.12), loc3(xn - 0.05, yn + sgn * 0.05, top + 0.55),
                       loc3(xn + 0.1, yn + sgn * 0.04, top + 0.45)]
                for j in range(len(pts) - 1): tube(f"eq{i}_hose{sgn}_{k}_{j}", pts[j], pts[j + 1], 0.013, mt)
                rbox(f"eq{i}_noz{sgn}_{k}", cx, cy, ang, xn - 0.025, xn + 0.025, yn - 0.03, yn + 0.03, top + ch - 0.22, top + ch - 0.08, M_DISP_DARK)
        # 주황 U자 볼라드: 아일랜드 양 끝(장변 방향) 바닥 기준 400mm
        bh = ASSUME["bollard_top_from_ground_m"] - ih
        for sgn in (-1, 1):
            xe = sgn * (w / 2 + im * 0.6); r = 0.03
            for yy in (-d / 2 - im * 0.3, d / 2 + im * 0.3):
                px, py, _ = loc3(xe, yy, 0)
                cyl(f"eq{i}_bol{sgn}_{yy:+.2f}", px, py, r, top, top + bh, M_BOLLARD)
            rbox(f"eq{i}_bolbar{sgn}", cx, cy, ang, xe - 0.03, xe + 0.03, -d / 2 - im * 0.3, d / 2 + im * 0.3, top + bh - 0.06, top + bh, M_BOLLARD)
    else:
        h = (e["h"] / 1000.0) if e.get("h") else None
        if h is None: used_assume.add("equip_box_h_m"); h = 1.0; ASSUME["equip_box_h_m"] = 1.0
        rbox(f"eq{i}_box", cx, cy, ang, -w / 2, w / 2, -d / 2, d / 2, z0, z0 + h, M_COL)

# ---------- 조명·카메라·렌더 ----------
w = bpy.data.worlds.new("W"); scene.world = w; w.use_nodes = True
bg = w.node_tree.nodes["Background"]; bg.inputs["Color"].default_value = (0.75, 0.82, 0.92, 1); bg.inputs["Strength"].default_value = 0.9
sun = bpy.data.objects.new("sun", bpy.data.lights.new("sun", 'SUN')); scene.collection.objects.link(sun)
sun.data.energy = 3.5; sun.rotation_euler = (math.radians(50), 0, math.radians(35))
scene.render.engine = 'CYCLES'; scene.cycles.samples = 24; scene.cycles.device = 'CPU'
scene.render.resolution_x, scene.render.resolution_y = 1100, 700
scene.view_settings.view_transform = 'Standard'

span = max(max(p[0] for p in pts_all) - min(p[0] for p in pts_all), max(p[1] for p in pts_all) - min(p[1] for p in pts_all)) / 1000.0
tz = max([b.get("el1") or 0 for b in D.get("buildings", [])] + [s["top_el_m"] for s in D.get("slabs", [])] + [4.0])
def shot(name, loc, tgt, lens=28):
    cd = bpy.data.cameras.new(name); cd.lens = lens
    co = bpy.data.objects.new(name, cd); scene.collection.objects.link(co); co.location = loc
    from mathutils import Vector
    co.rotation_euler = (Vector(tgt) - Vector(loc)).to_track_quat('-Z', 'Y').to_euler()
    scene.camera = co; scene.render.filepath = f"{OUT}_{name}.png"; bpy.ops.render.render(write_still=True)

shot("aerial", (span * 0.8, -span * 1.1, span * 0.7), (0, 0, tz * 0.4))
shot("south", (0, -span * 1.4, tz * 0.7), (0, 0, tz * 0.5), lens=35)
shot("north", (0, span * 1.4, tz * 0.7), (0, 0, tz * 0.5), lens=35)
eqs = D.get("equipment", [])
if eqs:
    ex = sum(P(e["cx"], e["cy"])[0] for e in eqs) / len(eqs); ey = sum(P(e["cx"], e["cy"])[1] for e in eqs) / len(eqs)
    shot("equip", (ex + 9, ey - 9, 2.2), (ex, ey, 1.2), lens=30)
bpy.ops.wm.save_as_mainfile(filepath=f"{OUT}.blend")
print("GEN3D DONE walls=%d openings=%d slabs=%d columns=%d equipment=%d" % (wall_n, len(openings), len(D.get("slabs", [])), len(D.get("columns", [])), len(eqs)))
print("GEN3D ASSUMED:", sorted(used_assume), ASSUME)
