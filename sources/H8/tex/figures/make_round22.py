#!/usr/bin/env python3
"""
make_round22.py

One plate for the results of round twenty-two.

  fig_simplextype  thm:simplextype and cor:delsarteall, on the Klein quartic
                   x^3 y + y^3 z + z^3 x.  Left: the Newton triangle in the
                   chart z = 1, with vertices (1, 0), (3, 1), (0, 3) for the
                   monomials z^3 x, x^3 y, y^3 z; its normalised area is
                   7 = [M : M'] and it has three interior lattice points, the
                   genus.  Right: the rays of a smooth fan adapted to it,
                   computed here as in item (LXVII): the three rays of P^2,
                   the three inner normals of the triangle, and the six rays
                   inserted to make every cone unimodular.  The pale sectors
                   are the normal cones of the three vertices, shaded in the
                   colour of the vertex; every cone of the fan lies in one of
                   them.  The curve meets only the divisors of the three
                   inner normals, in one point each.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and the plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round22.py [name ...]     (from the figures directory)
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402

make_round19.GEN = "make_round22.py"


# ========================================================= the Klein quartic
VERTS = [(1, 0), (3, 1), (0, 3)]
MONO = [r"$z^{3}x$", r"$x^{3}y$", r"$y^{3}z$"]
VCOL = ["PTeal", "PClay", "POchre"]
VPALE = ["WTeal", "WClay", "WOchre"]


def det2(v, w):
    return v[0] * w[1] - v[1] * w[0]


def angle(v):
    return math.atan2(v[1], v[0]) % (2 * math.pi)


def primitive(v):
    g = math.gcd(abs(v[0]), abs(v[1]))
    return (v[0] // g, v[1] // g)


def inner_normals():
    """the inner normal of the edge opposite each vertex, keyed by edge."""
    out = {}
    for i in range(3):
        a, b, c = VERTS[i], VERTS[(i + 1) % 3], VERTS[(i + 2) % 3]
        d = (b[0] - a[0], b[1] - a[1])
        n = primitive((-d[1], d[0]))
        if n[0] * (c[0] - a[0]) + n[1] * (c[1] - a[1]) < 0:
            n = (-n[0], -n[1])
        out[(i, (i + 1) % 3)] = n
    return out


def smooth_rays(rays):
    rays = sorted(set(rays), key=angle)
    while True:
        bad = [(rays[i], rays[(i + 1) % len(rays)])
               for i in range(len(rays))
               if det2(rays[i], rays[(i + 1) % len(rays)]) > 1]
        if not bad:
            return rays
        v, w = bad[0]
        best = None
        for a in range(-9, 10):
            for b in range(-9, 10):
                if math.gcd(a, b) != 1:
                    continue
                u = (a, b)
                if det2(v, u) == 1 and det2(u, w) > 0:
                    if best is None or a * a + b * b < best[0] ** 2 + \
                            best[1] ** 2:
                        best = u
        rays = sorted(set(rays + [best]), key=angle)


def vertex_of(v):
    vals = [u[0] * v[0] + u[1] * v[1] for u in VERTS]
    return [i for i, x in enumerate(vals) if x == min(vals)]


def fig_simplextype():
    normals = inner_normals()
    p2 = [(1, 0), (0, 1), (-1, -1)]
    rays = smooth_rays(p2 + list(normals.values()))
    assert len(rays) == 12
    cones = [(rays[i], rays[(i + 1) % 12]) for i in range(12)]
    assert all(det2(v, w) == 1 for v, w in cones)
    assert all(set(vertex_of(v)) & set(vertex_of(w)) for v, w in cones)
    F = Plate("fig_simplextype",
              "The Klein quartic x^3y + y^3z + z^3x (thm:simplextype): its "
              "Newton triangle, of normalised area 7 with three interior "
              "points, and a smooth fan adapted to it.")

    # ---------------------------------------------------------- the triangle
    s = 1.05
    ox, oy = 0.0, 0.0

    def P(x, y):
        return ox + x * s, oy + y * s

    F.poly([P(*u) for u in VERTS], fill="WBlue", draw="PBlue", lw=0.9,
           bg=True)
    F.seg([P(-0.35, 0), P(3.7, 0)], "PSlate,line width=0.45pt," + TIP)
    F.seg([P(0, -0.35), P(0, 3.7)], "PSlate,line width=0.45pt," + TIP)
    F.text(P(3.7, 0)[0] + 0.08, P(3.7, 0)[1], r"exponent of $x$",
           anchor="west", font=SN, color="PSlate")
    F.text(P(0, 3.7)[0], P(0, 3.7)[1] + 0.08, r"exponent of $y$",
           anchor="south", font=SN, color="PSlate")
    for a in range(0, 4):
        for b in range(0, 4):
            if (a, b) in VERTS:
                continue
            inside = (a - 2 * b < 1) and (2 * a + 3 * b < 9) and \
                (3 * a + b > 3)
            if inside:
                F.disc(*P(a, b), 2.2, "PBlue", ring="white", lw=0.5)
            else:
                F.disc(*P(a, b), 1.1, "PSlate!70", ring="white", lw=0.3)
    for u, lab, col in zip(VERTS, MONO, VCOL):
        F.disc(*P(*u), 3.0, col, ring="white", lw=0.6)
    F.text(P(1, 0)[0] + 0.10, P(1, 0)[1] - 0.12, MONO[0], anchor="north west",
           font=FN, color=VCOL[0] + "!85!black")
    F.text(P(3, 1)[0] + 0.14, P(3, 1)[1], MONO[1], anchor="west",
           font=FN, color=VCOL[1] + "!85!black")
    F.text(P(0, 3)[0] + 0.14, P(0, 3)[1] + 0.02, MONO[2], anchor="west",
           font=FN, color=VCOL[2] + "!85!black")
    F.text(P(1.5, -0.55)[0], P(1.5, -0.55)[1] - 0.05,
           r"normalised area $7=[M:M']$,\\three interior points: genus $3$",
           anchor="north", font=SN, extra="align=center")

    # --------------------------------------------------------------- the fan
    cx, cy = 8.4, 1.55
    r = 0.72
    R = 2.65

    def Q(v, t=1.0):
        n = math.hypot(v[0], v[1])
        ln = max(r * n, 1.0)
        return cx + t * ln * v[0] / n, cy + t * ln * v[1] / n

    # the normal cones of the vertices, shaded in the colour of the vertex
    edge_n = {k: v for k, v in normals.items()}
    for i in range(3):
        a = edge_n[((i + 2) % 3, i)]          # edge ending at vertex i
        b = edge_n[(i, (i + 1) % 3)]          # edge starting at vertex i
        # the cone of vertex i runs counterclockwise from one normal to the
        # other; take the order in which the vertex minimises in between
        t0, t1 = angle(b), angle(a)
        mid = (t0 + ((t1 - t0) % (2 * math.pi)) / 2)
        m = (math.cos(mid), math.sin(mid))
        if vertex_of((round(100 * m[0]), round(100 * m[1]))) != [i]:
            t0, t1 = t1, t0
        span = (t1 - t0) % (2 * math.pi)
        pts = [(cx, cy)]
        steps = 40
        for k in range(steps + 1):
            t = t0 + span * k / steps
            pts.append((cx + R * math.cos(t), cy + R * math.sin(t)))
        F.poly(pts, fill=VPALE[i], draw=None, bg=True)
    nset = set(normals.values())
    for v in rays:
        if v in nset:
            style = "PBlue,line width=1.0pt," + TIP
        elif v in p2:
            style = "PInk,line width=0.7pt," + TIP
        else:
            style = "PSlate,line width=0.55pt," + TIP
        F.seg([(cx, cy), Q(v)], style)
    F.disc(cx, cy, 1.6, "PInk", ring="white", lw=0.4)
    # coordinates at the tips of the rays of P^2 and of the inner normals
    for v in rays:
        if v not in nset and v not in p2:
            continue
        ang = angle(v)
        px, py = Q(v)
        dx, dy = math.cos(ang), math.sin(ang)
        c = "PBlue!85!black" if v in nset else "PInk"
        if abs(dx) >= abs(dy) - 1e-9:
            anchor = "west" if dx > 0 else "east"
        else:
            anchor = "south" if dy > 0 else "north"
        F.text(px + 0.10 * dx, py + 0.10 * dy, r"$(%d,%d)$" % v,
               anchor=anchor, font=SN, color=c)

    # legend
    lx, ly = 12.0, 3.05
    F.seg([(lx, ly), (lx + 0.45, ly)], "PInk,line width=0.7pt," + TIP)
    F.text(lx + 0.55, ly, r"a ray of $\PP^{2}$", anchor="west", font=SN)
    F.seg([(lx, ly - 0.62), (lx + 0.45, ly - 0.62)],
          "PBlue,line width=1.0pt," + TIP)
    F.text(lx + 0.55, ly - 0.62,
           r"an inner normal: the curve\\meets its divisor in one point",
           anchor="west", font=SN, extra="align=left")
    F.seg([(lx, ly - 1.36), (lx + 0.45, ly - 1.36)],
          "PSlate,line width=0.55pt," + TIP)
    F.text(lx + 0.55, ly - 1.36,
           r"inserted to make every\\cone unimodular", anchor="west",
           font=SN, extra="align=left")
    for k in range(3):
        yk = ly - 2.1 - 0.46 * k
        F.rect(lx + 0.02, yk - 0.1, lx + 0.40, yk + 0.1, fill=VPALE[k],
               draw=VCOL[k], lw=0.4)
        F.text(lx + 0.55, yk, r"normal cone of %s" % MONO[k],
               anchor="west", font=SN, color=VCOL[k] + "!85!black")
    F.write()
    return F.name


# ================================================================== main
ALL = ["simplextype"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
