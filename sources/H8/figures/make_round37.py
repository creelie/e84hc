#!/usr/bin/env python3
"""
make_round37.py

The figure of the subsection on the special locus (ssec:speciallocus).

  fig_speciallocus  prop:speciallocus and thm:escape.  The quotient S_F as a
                    pale region; in it five of the countably many proper
                    special subvarieties Y_1, ..., Y_5, each a closed curve
                    segment, and the CM points, which are dense and of which
                    each lies on some Y_j (prop:speciallocus (ii), (iii)).
                    The image of the base point s_0 sits where Y_1 and Y_2
                    meet.  Six points y_1, ..., y_6 of an escaping sequence,
                    chosen as in the proof of thm:escape(i): y_k lies on no
                    Y_j with j <= k, so y_1 may lie on Y_3, y_2 on Y_4 and
                    y_3 on Y_5, while y_4, y_5, y_6 lie on none of the five.
                    A point p(s) with Hg(A_s) = G_F lies on no Y_j.  Beside
                    the region, the legend and the two statements the figure
                    illustrates.  The incidences drawn are checked below.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and the plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round37.py     (from the figures directory)
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, FN, SN       # noqa: E402
from make_round28 import halton                     # noqa: E402

make_round19.GEN = "make_round37.py"

# ------------------------------------------------------------ the region
CX, CY, RA, RB, EX = 4.55, 2.75, 4.45, 2.62, 2.7


def inside(x, y, margin=0.0):
    """Inside the superellipse |u|^EX + |v|^EX < 1, shrunk by margin cm."""
    u = abs(x - CX) / (RA - margin)
    v = abs(y - CY) / (RB - margin)
    return u ** EX + v ** EX < 1.0


def rim(k=160):
    pts = []
    for i in range(k):
        t = 2 * math.pi * i / k
        c, s = math.cos(t), math.sin(t)
        pts.append((CX + RA * math.copysign(abs(c) ** (2 / EX), c),
                    CY + RB * math.copysign(abs(s) ** (2 / EX), s)))
    return pts


def bez_pt(a, c1, c2, b, t):
    u = 1 - t
    return (u ** 3 * a[0] + 3 * u * u * t * c1[0] + 3 * u * t * t * c2[0]
            + t ** 3 * b[0],
            u ** 3 * a[1] + 3 * u * u * t * c1[1] + 3 * u * t * t * c2[1]
            + t ** 3 * b[1])


# the proper special subvarieties Y_1, ..., Y_5, as cubic Bezier arcs
CURVES = [
    ((0.55, 3.55), (2.6, 4.95), (5.6, 4.55), (8.55, 3.35)),     # Y_1
    ((1.15, 0.95), (1.9, 2.4), (2.6, 3.9), (3.55, 5.05)),      # Y_2
    ((3.05, 0.42), (4.6, 1.15), (6.6, 1.25), (8.75, 2.15)),     # Y_3
    ((6.15, 0.45), (6.75, 1.9), (6.0, 3.3), (6.85, 5.0)),      # Y_4
    ((0.45, 2.35), (1.6, 1.85), (3.4, 2.75), (4.95, 2.05)),     # Y_5
]
# where each name sits: (curve, parameter, dx, dy, anchor)
NAMES = [(0, 1.0, -0.10, -0.12, "north"),
         (1, 1.0, 0.13, -0.05, "west"),
         (2, 1.0, -0.02, 0.15, "south east"),
         (3, 1.0, 0.13, -0.05, "west"),
         (4, 0.0, 0.08, 0.17, "south west")]
# where the name of each y_k sits: (dx, dy, anchor)
OFFS = [(0.12, -0.13, "north west"), (0.14, 0.02, "west"),
        (0.02, 0.15, "south"), (0.13, 0.0, "west"),
        (0.13, 0.0, "west"), (0.13, 0.0, "west")]


def on(j, t):
    return bez_pt(*CURVES[j], t)


def dist_to_curve(p, j, n=400):
    return min(math.hypot(p[0] - q[0], p[1] - q[1])
               for q in (on(j, i / n) for i in range(n + 1)))


def intersection(i, j):
    """The meeting point of Y_i and Y_j, by a grid search and refinement."""
    best = (9.0, None)
    n = 200
    A = [on(i, k / n) for k in range(n + 1)]
    B = [on(j, k / n) for k in range(n + 1)]
    for a in A:
        for b in B:
            d = math.hypot(a[0] - b[0], a[1] - b[1])
            if d < best[0]:
                best = (d, ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2))
    assert best[0] < 0.03, best
    return best[1]


def fig_speciallocus():
    F = Plate("fig_speciallocus",
              "The special locus (prop:speciallocus) and an escaping sequence "
              "of CM points (thm:escape).")
    for c in CURVES:
        for k in range(41):
            assert inside(*bez_pt(*c, k / 40), margin=0.10), c
    # the region
    F.poly(rim(), fill="WBlue", draw="PBlue!70", lw=0.6, bg=True)
    F.text(CX + 0.35, CY - RB - 0.12, r"$\mathcal{S}_{F}=\Gamma\backslash"
           r"\cD_{F}$", anchor="north", color="PBlue")
    # the special subvarieties
    clay = "PClay,line width=0.9pt"
    for c in CURVES:
        F.bez(*c, clay)
    for j, t, dx, dy, an in NAMES:
        x, y = on(j, t)
        F.text(x + dx, y + dy, r"$Y_{%d}$" % (j + 1), anchor=an,
               color="PClay!85!black", font=SN, onbg=True)

    # the escaping sequence: y_k on no Y_j with j <= k
    seq = [on(2, 0.43), on(3, 0.30), on(4, 0.22),
           (4.95, 3.40), (2.30, 1.45), (7.75, 2.75)]
    hosts = [3, 4, 5, None, None, None]
    for k, p in enumerate(seq):
        for j in range(5):
            d = dist_to_curve(p, j)
            if hosts[k] == j + 1:
                assert d < 0.02, (k, j, d)
            else:
                assert d > 0.18, (k, j, d)
            if d < 0.02:
                assert k + 1 < j + 1, (k, j)      # y_k on Y_j forces k < j
    # the very general point, off every Y_j
    gen = (3.85, 1.85)
    assert all(dist_to_curve(gen, j) > 0.25 for j in range(5))
    s0 = intersection(0, 1)

    # CM points: quasi-random points of the region, a few on each curve,
    # kept clear of the marked points and of the boxes of the labels
    keep_out = [p for p in seq] + [gen, s0]
    boxes = []

    def box(x, y, w, h, an):
        fx = {"west": 0.0, "east": -1.0}.get(an.split()[-1], -0.5)
        fy = {"south": 0.0, "north": -1.0}.get(an.split()[0], -0.5)
        boxes.append((x + fx * w, y + fy * h, w, h))
    for j, t, dx, dy, an in NAMES:
        x, y = on(j, t)
        box(x + dx, y + dy, 0.38, 0.30, an)
    for p, (dx, dy, an) in zip(seq, OFFS):
        box(p[0] + dx, p[1] + dy, 0.38, 0.30, an)
    box(gen[0] + 0.15, gen[1] - 0.02, 0.62, 0.32, "west")
    box(s0[0] + 0.14, s0[1] - 0.10, 0.80, 0.34, "north west")
    dots = []
    i = 7
    while len(dots) < 46 and i < 4000:
        p = (CX - RA + 2 * RA * halton(i, 2), CY - RB + 2 * RB * halton(i, 3))
        i += 1
        if not inside(*p, margin=0.30):
            continue
        if any(dist_to_curve(p, j, n=120) < 0.13 for j in range(5)):
            continue
        if any(math.hypot(p[0] - q[0], p[1] - q[1]) < 0.36 for q in keep_out):
            continue
        if any(math.hypot(p[0] - q[0], p[1] - q[1]) < 0.30 for q in dots):
            continue
        if any(bx - 0.12 < p[0] < bx + w + 0.12 and by - 0.12 < p[1] < by + h + 0.12
               for bx, by, w, h in boxes):
            continue
        dots.append(p)
    on_curve = [on(j, t) for j, ts in enumerate(
        [(0.22, 0.62, 0.86), (0.18, 0.47), (0.12, 0.70, 0.92), (0.58, 0.82),
         (0.55, 0.85)]) for t in ts]
    for p in dots + on_curve:
        F.disc(p[0], p[1], 1.25, "PBlue", ring="white", lw=0.3)

    # s_0, the escaping sequence and the very general point
    F.disc(s0[0], s0[1], 2.6, "PInk", ring="white", lw=0.5)
    F.text(s0[0] + 0.14, s0[1] - 0.10, r"$p(s_{0})$", anchor="north west",
           font=SN, onbg=True)
    for k, (p, (dx, dy, an)) in enumerate(zip(seq, OFFS)):
        F.disc(p[0], p[1], 2.4, "POchre", ring="white", lw=0.5)
        F.text(p[0] + dx, p[1] + dy, r"$y_{%d}$" % (k + 1), anchor=an,
               color="POchre!80!black", font=SN, onbg=True)
    F.disc(gen[0], gen[1], 2.6, "PGrass", ring="white", lw=0.5)
    F.text(gen[0] + 0.15, gen[1] - 0.02, r"$p(s)$", anchor="west",
           color="PGrass", font=SN, onbg=True)

    # legend and reading
    lx, ly, dy = 9.60, 4.95, 0.62
    F.seg([(lx - 0.18, ly), (lx + 0.18, ly)], clay)
    F.disc(lx, ly - dy, 1.25, "PBlue", ring="white", lw=0.3)
    F.disc(lx, ly - 2 * dy, 2.4, "POchre", ring="white", lw=0.5)
    F.disc(lx, ly - 3 * dy, 2.6, "PGrass", ring="white", lw=0.5)
    F.disc(lx, ly - 4 * dy, 2.6, "PInk", ring="white", lw=0.5)
    rows = [
        r"proper special subvarieties $Y_{j}$",
        r"CM points, each on some $Y_{j}$",
        r"$y_{k}\notin Y_{1}\cup\dots\cup Y_{k}$",
        r"$p(s)$ with $\mathrm{Hg}(A_{s})=G_{F}$",
        r"$p(s_{0})$, the CM base point",
    ]
    for k, s in enumerate(rows):
        F.text(lx + 0.32, ly - k * dy, s, anchor="west", font=FN)
    ry = ly - 4 * dy - 0.62
    reading = [
        r"$\Sigma^{\mathrm{sp}}_{F}=p^{-1}\bigl(\bigcup_{j}Y_{j}\bigr)$ is "
        r"dense,",
        r"$G_{F}(\QQ)$-stable and meagre;",
        r"the $y_{k}$ are Zariski dense in $\mathcal{S}_{F}$",
        r"by Andr\'e--Oort",
    ]
    for k, s in enumerate(reading):
        F.text(lx - 0.20, ry - 0.52 * k, s, anchor="north west", font=FN)
    F.write()
    return F.name


# ================================================================== main
ALL = ["speciallocus"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
