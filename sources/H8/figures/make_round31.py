#!/usr/bin/env python3
"""
make_round31.py

The figure of the section that carries the main theorem to every family.

  fig_cmseed       thm:f2propagation.  A polarised abelian scheme
                   f: A -> S over a curved sheet S, the component of the
                   Hodge locus of a flat class xi through a given Hodge class
                   (prop:cmfamily).  On the sheet the points of CM type, which
                   are dense (lem:cmdense), and strata of the algebraic locus
                   Sigma(xi) (lem:algstrata) through some of them.  Above three
                   points, drawn as tori, the fibres: a member of CM type at
                   which xi is algebraic (the seed), a member on the stratum
                   through it, where xi is algebraic as well, and a very
                   general member, where the algebraicity of xi is what (F2)
                   asks for.  The loop on each torus stands for the class xi,
                   carried from fibre to fibre by parallel transport.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and the plate is audited against its own raster before it
is written (make_core.Fig): no label meets ink or another label, and no
leader crosses ink, a label or another leader.

Run:  python3 -B make_round31.py     (from the figures directory)
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
from make_core import Fig, orbit_cam, fit                  # noqa: E402
from make_round19 import FN, SN                            # noqa: E402
from make_round28 import halton                            # noqa: E402
from render3d import unit, sub, dot                        # noqa: E402

GEN = "make_round31.py"

# ----------------------------------------------------------------- the base
X0, X1, Y0, Y1 = -3.2, 3.2, -1.75, 1.75


def height(x, y):
    """A gently rolling sheet: small slopes, so that nothing on it is hidden
    by a fold when it is seen from above."""
    return (0.36 * math.sin(1.05 * x + 0.4) * math.cos(0.9 * y)
            + 0.07 * y)


def lift(x, y, eps=0.012):
    return (x, y, height(x, y) + eps)


def sheet_normal(x, y):
    h = 1e-4
    hx = (height(x + h, y) - height(x - h, y)) / (2 * h)
    hy = (height(x, y + h) - height(x, y - h)) / (2 * h)
    return unit((-hx, -hy, 1.0))


def draw_sheet(F, nx=32, ny=18):
    for i in range(nx):
        for j in range(ny):
            xa = X0 + (X1 - X0) * i / nx
            xb = X0 + (X1 - X0) * (i + 1) / nx
            ya = Y0 + (Y1 - Y0) * j / ny
            yb = Y0 + (Y1 - Y0) * (j + 1) / ny
            P = [(xa, ya, height(xa, ya)), (xb, ya, height(xb, ya)),
                 (xb, yb, height(xb, yb)), (xa, yb, height(xa, yb))]
            c = ((xa + xb) / 2, (ya + yb) / 2)
            F.poly3(P, fill=F.tone(sheet_normal(*c), "PBlue", lo=16, hi=58),
                    draw=None, prio=-5,
                    depth=2e6 + F.D((c[0], c[1], height(*c))))
    rim = ([(X0 + (X1 - X0) * k / 80, Y0) for k in range(81)]
           + [(X1, Y0 + (Y1 - Y0) * k / 40) for k in range(1, 41)]
           + [(X1 - (X1 - X0) * k / 80, Y1) for k in range(1, 81)]
           + [(X0, Y1 - (Y1 - Y0) * k / 40) for k in range(1, 41)])
    F.curve3([lift(x, y, 0.0) for x, y in rim], "PBlue!70,line width=0.55pt",
             prio=-4, chunk=20, depth=1e6 + 1)


def path_on_sheet(pts, n=90):
    """A smooth curve of the sheet through the given points of the plane
    (Catmull-Rom), lifted to the sheet."""
    P = [pts[0]] + list(pts) + [pts[-1]]
    out = []
    for k in range(1, len(P) - 2):
        p0, p1, p2, p3 = P[k - 1], P[k], P[k + 1], P[k + 2]
        m = max(2, n // (len(pts) - 1))
        for i in range(m):
            t = i / m
            t2, t3 = t * t, t * t * t
            xy = [0.5 * ((2 * p1[a]) + (-p0[a] + p2[a]) * t
                         + (2 * p0[a] - 5 * p1[a] + 4 * p2[a] - p3[a]) * t2
                         + (-p0[a] + 3 * p1[a] - 3 * p2[a] + p3[a]) * t3)
                  for a in range(2)]
            out.append(lift(*xy))
    out.append(lift(*pts[-1]))
    return out


# ---------------------------------------------------------------- the fibres
RMAJ, RMIN, LIFT = 0.50, 0.17, 1.62


def torus_pt(c, u, v, eps=0.0):
    r = RMIN + eps
    return (c[0] + (RMAJ + r * math.cos(v)) * math.cos(u),
            c[1] + (RMAJ + r * math.cos(v)) * math.sin(u),
            c[2] + r * math.sin(v))


def torus_normal(u, v):
    return (math.cos(v) * math.cos(u), math.cos(v) * math.sin(u),
            math.sin(v))


def draw_torus(F, c, base, nu=40, nv=20, lo=22, hi=82):
    """The visible facets of a torus with vertical axis, each at its own
    depth, so that the painter lets the near side of the tube cover the
    far side."""
    for i in range(nu):
        for j in range(nv):
            ua, ub = 2 * math.pi * i / nu, 2 * math.pi * (i + 1) / nu
            va, vb = 2 * math.pi * j / nv, 2 * math.pi * (j + 1) / nv
            um, vm = (ua + ub) / 2, (va + vb) / 2
            n = torus_normal(um, vm)
            q = torus_pt(c, um, vm)
            if dot(n, sub(F.cam.eye, q)) <= 0:
                continue
            P = [torus_pt(c, ua, va), torus_pt(c, ub, va),
                 torus_pt(c, ub, vb), torus_pt(c, ua, vb)]
            F.poly3(P, fill=F.tone(n, base, lo=lo, hi=hi),
                    draw="%s!%d!white" % (base, max(8, lo - 4)), lw=0.05,
                    prio=0, depth=F.D(q))


def draw_loop(F, c, style, n=120):
    """The top circle of the torus, the loop that stands for the class xi on
    the fibre; each short run carries the depth of the facet below it, less
    a little, so that it lies on the tube and is hidden where the tube is."""
    pts = [torus_pt(c, 2 * math.pi * k / n, math.pi / 2, eps=0.006)
           for k in range(n + 1)]
    for k in range(n):
        a, b = pts[k], pts[k + 1]
        u = 2 * math.pi * (k + 0.5) / n
        q = torus_pt(c, u, math.pi / 2)
        if dot(torus_normal(u, math.pi / 2), sub(F.cam.eye, q)) <= 0:
            continue
        F.line3([a, b], style, prio=1, depth=F.D(q) - 0.02)


def fibre_line(F, xy, c):
    base = lift(*xy, eps=0.0)
    top = (c[0], c[1], c[2] - RMIN - 0.04)
    pts = [(base[0], base[1], base[2] + (top[2] - base[2]) * k / 20)
           for k in range(21)]
    F.line3(pts, "PSlate!80,line width=0.5pt,dash pattern=on 1.8pt off 1.4pt",
            prio=1, depth=1e6 - 10)


def fig_cmseed():
    cam = orbit_cam((0.0, 0.0, 0.75), 14.0, 30.0, R=32.0)
    F = Fig("fig_cmseed",
            "An abelian scheme over the component S of the Hodge locus of a "
            "flat class xi: the dense points of CM type, strata of the "
            "algebraic locus, a CM member at which xi is algebraic, and a "
            "very general member, where (F2) asks for the same.", cam,
            gen=GEN)

    s0 = (-2.05, -0.55)          # the seed, of CM type
    s1 = (-0.15, 0.62)           # on the stratum through s0
    sg = (1.95, -0.30)           # very general
    tops = {}
    for key, xy in (("s0", s0), ("s1", s1), ("sg", sg)):
        tops[key] = (xy[0], xy[1], height(*xy) + LIFT)
    corners = [(X0, Y0, height(X0, Y0)), (X1, Y0, height(X1, Y0)),
               (X1, Y1, height(X1, Y1)), (X0, Y1, height(X0, Y1))]
    rims = [torus_pt(tops[k], 2 * math.pi * i / 24, 0.0)
            for k in tops for i in range(24)]
    fit(cam, corners + rims, 9.2)

    draw_sheet(F)

    # strata of the algebraic locus: the one through s0 and s1, and two more
    strata = [[(-3.0, -1.25), s0, (-1.1, 0.25), s1, (1.0, 1.3), (1.6, 1.62)],
              [(0.35, -1.62), (0.9, -0.85), (0.55, -0.1), (1.05, 0.55)],
              [(2.3, 1.55), (2.55, 0.85), (3.05, 0.45)]]
    for S in strata:
        F.curve3(path_on_sheet(S), "PGrass,line width=1.0pt", prio=2,
                 chunk=8, depth=1e6 - 3)

    # the points of CM type, standing for a dense set
    cm = []
    i = 5
    while len(cm) < 95:
        x = X0 + 0.15 + (X1 - X0 - 0.3) * halton(i, 2)
        y = Y0 + 0.12 + (Y1 - Y0 - 0.24) * halton(i, 3)
        i += 1
        if min(math.hypot(x - p[0], y - p[1]) for p in (s0, s1, sg)) < 0.22:
            continue
        cm.append((x, y))
    for q in cm:
        F.dot3(lift(*q), "PIndigo", r=0.9, ring="white", prio=3,
               depth=1e6 - 4)

    # the three base points and their fibres
    F.dot3(lift(*s0), "PMag", r=2.3, ring="white", prio=5, depth=1e6 - 6)
    F.dot3(lift(*s1), "PGrass", r=2.0, ring="white", prio=5, depth=1e6 - 6)
    F.dot3(lift(*sg), "POchre", r=2.1, ring="white", prio=5, depth=1e6 - 6)
    for key, xy in (("s0", s0), ("s1", s1), ("sg", sg)):
        fibre_line(F, xy, tops[key])
    draw_torus(F, tops["s0"], "PMag")
    draw_torus(F, tops["s1"], "PGrass")
    draw_torus(F, tops["sg"], "POchre")
    draw_loop(F, tops["s0"], "white,line width=1.1pt")
    draw_loop(F, tops["s1"], "white,line width=1.1pt")
    draw_loop(F, tops["sg"], "white,line width=1.1pt,dash pattern=on 2.2pt "
              "off 1.6pt")

    # labels
    F.alabel(F.P(torus_pt(tops["s0"], math.pi, 0.0)),
             r"$\cA_{c}$ of CM type: $\xi_{c}$ algebraic", color="PMag",
             font=SN, prefer=150, spread=70, rmin=0.2, rmax=3.0, lead=0.3,
             free=0.4)
    F.alabel(F.P(torus_pt(tops["s1"], math.pi / 2, math.pi / 2)),
             r"$\xi_{t}$ algebraic along the stratum", color="PGrass!85!black",
             font=SN, prefer=95, spread=60, rmin=0.2, rmax=3.0, lead=0.3,
             free=0.4)
    F.alabel(F.P(torus_pt(tops["sg"], 0.0, 0.0)),
             r"$\cA_{s}$, $s$ very general: is $\xi_{s}$ algebraic?",
             color="POchre!80!black", font=SN, prefer=30, spread=70,
             rmin=0.2, rmax=3.0, lead=0.3, free=0.4)
    F.alabel(F.P(lift(*s0)), r"$c$", color="PMag", font=SN, prefer=190,
             spread=40, rmin=0.12, rmax=2.4, lead=0.3, free=1.6)
    F.alabel(F.P(lift(*sg)), r"$s$", color="POchre!80!black", font=SN,
             prefer=-15, spread=40, rmin=0.12, rmax=2.6, lead=0.3, free=1.8)
    mid = path_on_sheet(strata[1])[40]
    F.alabel(F.P(mid), r"strata of $\Sigma(\xi)$", color="PGrass!85!black",
             font=SN, prefer=-80, spread=40, rmin=0.2, rmax=3.4, lead=0.3,
             free=1.6)
    F.alabel(F.P(lift(*cm[7])), r"points of CM type, dense",
             color="PIndigo", font=SN, prefer=-110, spread=60, rmin=0.2,
             rmax=3.2, lead=0.3, free=1.0)
    F.alabel(F.P(lift(X1, Y0, 0.0)), r"$S$", color="PBlue", font=FN,
             prefer=-20, spread=60, rmin=0.1, rmax=1.0, lead=0.3, free=0.2)
    fl = (sg[0], sg[1], height(*sg) + 0.55 * LIFT)
    F.alabel(F.P(fl), r"fibres of $\pi\colon\cA\to S$", color="PSlate",
             font=SN, prefer=-25, spread=40, rmin=0.2, rmax=3.6, lead=0.3,
             free=1.8)
    F.write()


ALL = ["cmseed"]

if __name__ == "__main__":
    names = sys.argv[1:] or ALL
    for n in names:
        globals()["fig_" + n]()
