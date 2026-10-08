#!/usr/bin/env python3
"""
make_secant.py

Two plates for the existence theorem of the third ingredient.

  fig_moment     (a) the secant plane P_t at n = 2, d = 2, in the
                 coordinates (ch_0, ch_1, ch_2) of the basis 1, t, t^2/2, the
                 third axis at two fifths scale; the moment curve
                 j -> ch O(jt) = (1, j, j^2) in the plane ch_0 = 1; the
                 integral points of P_t sorted into those the line bundles
                 reach and those they miss; the point p = u_t + v_t and its
                 double 2p, reached by -3[O] + 8[O(t)] - 3[O(2t)].
                 (b) the same plane in its own coordinates (a, b), for the
                 point a u_t + b v_t, with the lattice Z^2, the sublattice
                 b = 0 mod 2 of the points reached, the half plane a > 0 of
                 positive rank, and the ray through p.

  fig_multiple   the least multiple M of the theorem over the seventy two
                 cases d in {1,2,3,5,7,11}, a in {1,2,3}, b in {-2,-1,1,2}
                 for each 1 <= n <= 10, on a logarithmic scale, against n!,
                 which every M divides.

Nothing is drawn by eye.  A class in Q[t]/(t^{n+1}) is written in the basis
t^k/k! as (c_0, ..., c_n); the line bundle O(jt) sits at (1, j, ..., j^n);
the point a u_t + b v_t has c_k = a(-d)^{k/2} for k even and
b(-d)^{(k-1)/2} for k odd; and M is the least common multiple of the
denominators of the solution of the Vandermonde system, computed here
exactly with fractions, as in code/secant_exists.py.  At n = 2, d = 2 the
lattice spanned by the moment points is {(x, y, z) : z = y mod 2}.
"""
import math
import os
import sys
from collections import Counter
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from render3d import Camera, Scene                                # noqa: E402
from make_diagrams import (Plate, compile_plate, proj, TIP, orbit_eye,  # noqa
                           Axes2D, soften)

GEN = "make_secant.py"
ZS = 0.40                      # drawing scale on the third coordinate


def pt(c0, c1, c2):
    """A class (c_0, c_1, c_2) placed in the drawing frame."""
    return (c0, c1, ZS * c2)


# ------------------------------------------------------------ exact algebra
def target(n, a, b, d):
    return [a * (-d) ** (k // 2) if k % 2 == 0 else b * (-d) ** ((k - 1) // 2)
            for k in range(n + 1)]


def vandermonde_solve(n, c):
    rows = [[Fraction(j ** k if (j or k) else 1) for j in range(n + 1)]
            + [Fraction(c[k])] for k in range(n + 1)]
    m = n + 1
    for i in range(m):
        piv = next(r for r in range(i, m) if rows[r][i] != 0)
        rows[i], rows[piv] = rows[piv], rows[i]
        inv = 1 / rows[i][i]
        rows[i] = [v * inv for v in rows[i]]
        for r in range(m):
            if r != i and rows[r][i] != 0:
                f = rows[r][i]
                rows[r] = [x - f * y for x, y in zip(rows[r], rows[i])]
    return [rows[i][m] for i in range(m)]


def least_multiple(n, a, b, d):
    x = vandermonde_solve(n, target(n, a, b, d))
    M = 1
    for v in x:
        M = M * v.denominator // math.gcd(M, v.denominator)
    return M, [int(v * M) for v in x]


# ------------------------------------------------------------------ moment
def fig_moment():
    d, a, b = 2, 1, 1
    M, wit = least_multiple(2, a, b, d)
    assert (M, wit) == (2, [-3, 8, -3])
    tgt = (0.75, 0.35, -0.35)
    cam = Camera(eye=orbit_eye(tgt, 30.0, -62.0, 20.0), target=tgt,
                 focal=30.0, scale=1.62)
    sc = Scene(cam)
    pl = Plate("fig_moment", GEN,
               "The secant plane, the moment curve of line bundle Chern "
               "characters, and the multiple that lands a rational point of "
               "the plane on the lattice they span.", thresh=236)

    # the secant plane P_t = span(u, v), u = (1,0,-d), v = (0,1,0)
    S0, S1, R0, R1 = -0.40, 2.40, -1.40, 2.40
    sc.surface(lambda s, r: pt(s, r, -d * s), (S0, S1), (R0, R1), 16, 18,
               base="PIndigo", opacity=0.10, ambient=0.60, diffuse=0.30)
    for s in (S0, S1):
        sc.polyline([pt(s, R0, -d * s), pt(s, R1, -d * s)],
                    "soft,PIndigo!70,line width=0.45pt", priority=1)
    for r in (R0, R1):
        sc.polyline([pt(S0, r, -d * S0), pt(S1, r, -d * S1)],
                    "soft,PIndigo!70,line width=0.45pt", priority=1)
    # the coordinate axes
    for e, lo, hi in (((1, 0, 0), -0.4, 2.9), ((0, 1, 0), -1.7, 2.9),
                      ((0, 0, 1), -4.6, 5.2)):
        sc.polyline([pt(lo * e[0], lo * e[1], lo * e[2]),
                     pt(hi * e[0], hi * e[1], hi * e[2])],
                    "PSlate,line width=0.5pt," + TIP, priority=2)
    # the moment curve j -> (1, j, j^2), in the plane ch_0 = 1
    sc.curve(lambda j: pt(1.0, j, j * j), (-1.20, 2.25), 120,
             "PTeal,line width=1.25pt", priority=3, chunk=2)
    for j in (-1, 0, 1, 2):
        sc.dot3(pt(1.0, j, j * j), "circle,fill=PTeal,draw=white,"
                "line width=0.55pt,inner sep=2.0pt", priority=6)
    # the witness: -3 (1,0,0) + 8 (1,1,1) - 3 (1,2,4) = 2p
    P2 = pt(2 * a, 2 * b, -2 * d * a)
    for j in (0, 1, 2):
        sc.polyline([pt(1.0, j, j * j), P2],
                    "PAmber,line width=0.6pt,dash pattern=on 1.6pt off 1.4pt",
                    priority=2)
    # the integral points of the plane: reached iff b is even
    for x in (0, 1, 2):
        for y in (-1, 0, 1, 2):
            if (x, y) in ((1, 1), (2, 2)):
                continue
            if y % 2 == 0:
                st = ("circle,fill=PGrass,draw=white,line width=0.5pt,"
                      "inner sep=1.7pt")
            else:
                st = ("circle,draw=PMag,line width=0.8pt,fill=white,"
                      "inner sep=1.5pt")
            sc.dot3(pt(x, y, -d * x), st, priority=5)
    # the basis u_t = (1, 0, -d), v_t = (0, 1, 0) of the plane
    sc.polyline([pt(0, 0, 0), pt(1, 0, -d)], "PIndigo,line width=1.1pt," + TIP,
                priority=4)
    sc.polyline([pt(0, 0, 0), pt(0, 1, 0)], "PIndigo,line width=1.1pt," + TIP,
                priority=4)
    # p and 2p
    sc.polyline([pt(0, 0, 0), P2], "PMag,line width=1.0pt," + TIP, priority=4)
    sc.dot3(pt(a, b, -d * a), "circle,draw=PMag,line width=1.1pt,fill=white,"
            "inner sep=2.2pt", priority=7)
    sc.dot3(P2, "circle,fill=PMag,draw=white,line width=0.6pt,"
            "inner sep=2.4pt", priority=7)
    pl.add(soften(sc.emit()))

    pl.label(proj(cam, pt(2.9, 0, 0)), r"$\ch_{0}$", color="PSlate",
             dirs=[0, -30], rmax=0.5)
    pl.label(proj(cam, pt(0, 2.9, 0)), r"$\ch_{1}$", color="PSlate",
             dirs=[30, 0, 60], rmax=0.5)
    pl.label(proj(cam, pt(0, 0, 5.2)), r"$\ch_{2}$", color="PSlate",
             dirs=[90, 180], rmax=0.5)
    pl.label(proj(cam, pt(1.0, 2.25, 2.25 ** 2)), r"$(1,j,j^{2})$",
             color="PTeal", dirs=[0, 30, -30], rmax=0.8)
    for j, w in ((0, -3), (1, 8), (2, -3)):
        pl.label(proj(cam, pt(1.0, j, j * j)), r"$%d$" % w, color="PAmber!80!black",
                 font=r"\footnotesize", dirs=[180, 150, 210, 120], rmax=0.7,
                 skip=0.1)
    pl.label(proj(cam, pt(a, b, -d * a)), r"$p$", color="PMag",
             dirs=[-90, -60, -120, 180], rmax=0.8, skip=0.1)
    pl.label(proj(cam, P2), r"$2p$", color="PMag", dirs=[0, -30, 30],
             rmax=0.8, skip=0.1)
    pl.label(proj(cam, pt(1, 0, -d)), r"$u_{t}$", color="PIndigo",
             dirs=[-90, -120, 180], rmax=0.8, skip=0.1)
    pl.label(proj(cam, pt(0, 1, 0)), r"$v_{t}$", color="PIndigo",
             dirs=[90, 120, 60], rmax=0.8, skip=0.1)
    pl.label(proj(cam, pt(S1, R0, -d * S1)), r"$P_{t}$", color="PIndigo",
             dirs=[-60, -90, -30, 0], rmax=0.8)
    x0, y0, x1, y1 = [None] * 4

    # (b): the plane in its own coordinates a u_t + b v_t
    body = "".join(pl.parts)
    import make_diagrams as md
    bx0, by0, bx1, by1 = md.ink_bbox(body)
    ax = Axes2D(pl, bx1 + 1.05, by0 + 0.35, 3.84, 4.48, (-1.5, 3.3),
                (-1.5, 4.1))
    pl.add("  \\path[fill=PIndigo!5] (%.3f,%.3f) rectangle (%.3f,%.3f);\n"
           % (ax.X(0), ax.Y(-1.5), ax.X(3.3), ax.Y(4.1)))
    for g in range(-1, 4):
        pl.add("  \\draw[PIndigo!30,line width=0.3pt] (%.3f,%.3f) -- "
               "(%.3f,%.3f);\n" % (ax.X(g), ax.Y(-1.5), ax.X(g), ax.Y(4.1)))
    for g in range(-1, 5):
        pl.add("  \\draw[PIndigo!30,line width=0.3pt] (%.3f,%.3f) -- "
               "(%.3f,%.3f);\n" % (ax.X(-1.5), ax.Y(g), ax.X(3.3), ax.Y(g)))
    pl.add("  \\draw[PSlate,line width=0.5pt,%s] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (TIP, ax.X(-1.5), ax.Y(0), ax.X(3.3), ax.Y(0)))
    pl.add("  \\draw[PSlate,line width=0.5pt,%s] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (TIP, ax.X(0), ax.Y(-1.5), ax.X(0), ax.Y(4.1)))
    # a fundamental domain of the reached sublattice
    pl.add("  \\draw[PGrass,line width=0.7pt,dash pattern=on 2pt off 1.5pt] "
           "(%.3f,%.3f) rectangle (%.3f,%.3f);\n"
           % (ax.X(1), ax.Y(0), ax.X(2), ax.Y(2)))
    pl.add("  \\draw[PMag,line width=1.0pt,%s] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (TIP, ax.X(0), ax.Y(0), ax.X(1.94), ax.Y(1.94)))
    for x in range(-1, 4):
        for y in range(-1, 5):
            if (x, y) in ((1, 1), (2, 2), (0, 0)):
                continue
            if y % 2 == 0:
                st = ("circle,fill=PGrass,draw=white,line width=0.5pt,"
                      "inner sep=1.7pt")
            else:
                st = ("circle,draw=PMag,line width=0.8pt,fill=white,"
                      "inner sep=1.5pt")
            pl.add("  \\node[%s] at (%.3f,%.3f) {};\n" % (st, ax.X(x), ax.Y(y)))
    pl.add("  \\node[circle,fill=PInk,inner sep=1.4pt] at (%.3f,%.3f) {};\n"
           % ax.P(0, 0))
    pl.add("  \\node[circle,draw=PMag,line width=1.1pt,fill=white,"
           "inner sep=2.2pt] at (%.3f,%.3f) {};\n" % ax.P(1, 1))
    pl.add("  \\node[circle,fill=PMag,draw=white,line width=0.6pt,"
           "inner sep=2.4pt] at (%.3f,%.3f) {};\n" % ax.P(2, 2))
    for g in range(-1, 4):
        pl.put(ax.X(g), ax.Y(-1.5) - 0.24, r"$%d$" % g, color="PSlate",
               font=r"\footnotesize")
    for g in range(-1, 5):
        pl.put(ax.X(-1.5) - 0.26, ax.Y(g), r"$%d$" % g, color="PSlate",
               font=r"\footnotesize")
    pl.label(ax.P(3.3, 0), r"$a$", color="PSlate", dirs=[0], rmax=0.3)
    pl.label(ax.P(0, 4.1), r"$b$", color="PSlate", dirs=[90], rmax=0.3)
    pl.label(ax.P(1, 1), r"$p$", color="PMag", dirs=[0, -30, -60], rmax=0.6)
    pl.label(ax.P(2, 2), r"$2p$", color="PMag", dirs=[0, 30, -30], rmax=0.6)
    pl.put(ax.X(0.9), ax.Y(4.1) + 0.62,
           r"(b)\ \ $a\,u_{t}+b\,v_{t}\in P_{t}$", color="PInk")
    pl.put(bx0 - 0.2, ax.Y(4.1) + 0.62, r"(a)", color="PInk", anchor="w")
    pl.build()
    compile_plate("fig_moment")


# ---------------------------------------------------------------- multiple
def fig_multiple():
    ds, as_, bs = (1, 2, 3, 5, 7, 11), (1, 2, 3), (-2, -1, 1, 2)
    data = {}
    for n in range(1, 11):
        Ms = []
        for d in ds:
            for a in as_:
                for b in bs:
                    M, nj = least_multiple(n, a, b, d)
                    # the witness reproduces M c_k, and has rank M a
                    c = target(n, a, b, d)
                    assert all(sum(nj[j] * (j ** k if (j or k) else 1)
                                   for j in range(n + 1)) == M * c[k]
                               for k in range(n + 1))
                    assert sum(nj) == M * a
                    assert math.factorial(n) % M == 0
                    Ms.append(M)
        data[n] = Counter(Ms)
    assert max(data[8]) == 2016 and min(data[7]) > 1
    assert least_multiple(4, 1, 1, 3)[0] == 6
    pl = Plate("fig_multiple", GEN,
               "The least multiple M of the secant existence theorem, over "
               "seventy two cases for each n up to ten, against n!.")
    ax = Axes2D(pl, 0.0, 0.0, 10.4, 5.6, (0.4, 10.6), (-0.3, 7.0), ylog=False)
    ax.frame(range(1, 11), range(0, 8),
             yfmt=lambda v: "$1$" if v == 0 else ("$10$" if v == 1 else
                                                 "$10^{%d}$" % v))
    # n!, which every M divides
    pts = " -- ".join("(%.3f,%.3f)" % ax.P(n, math.log10(math.factorial(n)))
                      for n in range(1, 11))
    pl.add("  \\draw[PClay,line width=0.8pt,dash pattern=on 3pt off 2pt] %s;\n"
           % pts)
    for n in range(1, 11):
        pl.add("  \\node[circle,fill=PClay,inner sep=1.1pt] at (%.3f,%.3f) {};\n"
               % ax.P(n, math.log10(math.factorial(n))))
    # the largest M for each n
    pts = " -- ".join("(%.3f,%.3f)" % ax.P(n, math.log10(max(data[n])))
                      for n in range(1, 11))
    pl.add("  \\draw[PIndigo!70,line width=0.6pt] %s;\n" % pts)
    # every value of M, the area of the disc proportional to its count
    for n in range(1, 11):
        for M, cnt in sorted(data[n].items()):
            r = 0.025 * math.sqrt(cnt)
            x, y = ax.P(n, math.log10(M))
            pl.add("  \\path[fill=PIndigo,fill opacity=0.55,draw=PIndigo!80!black,"
                   "line width=0.3pt] (%.3f,%.3f) circle (%.3f);\n" % (x, y, r))
    pl.label(ax.P(8, math.log10(2016)), r"$2016$", color="PIndigo",
             font=r"\footnotesize", dirs=[-90, -60, -120], rmax=1.2)
    pl.label(ax.P(10, math.log10(max(data[10]))), r"$36288$",
             color="PIndigo", font=r"\footnotesize", dirs=[0, -30, -90],
             rmax=1.2)
    pl.label(ax.P(4, math.log10(6)), r"$6$", color="PIndigo",
             font=r"\footnotesize", dirs=[180, 150, 210], rmax=0.8)
    pl.label(ax.P(10, math.log10(math.factorial(10))), r"$n!$",
             color="PClay", dirs=[0, 30, -30], rmax=0.8)
    pl.label(ax.P(9, math.log10(max(data[9]))), r"$\max M$",
             color="PIndigo", dirs=[120, 90, 150], rmax=1.2)
    pl.put(ax.X(5.5), -0.85, r"$n$", color="PSlate")
    pl.put(-1.25, ax.Y(3.5), r"$M$", color="PSlate")
    pl.build()
    compile_plate("fig_multiple")


if __name__ == "__main__":
    which = sys.argv[1:] or ["moment", "multiple"]
    if "moment" in which:
        fig_moment()
    if "multiple" in which:
        fig_multiple()
