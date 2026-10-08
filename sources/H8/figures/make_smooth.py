#!/usr/bin/env python3
"""
make_smooth.py

One plate for the smooth support theorem.

  fig_bmywindow  (a) the defect 3e(S) - K_S^2 = 24(b^4 - d^2) of the
                 Bogomolov-Miyaoka-Yau inequality for the surface that the
                 theorem on the invariants of a smooth support attaches to
                 the pair (b, d), as a surface over the window
                 1.5 <= b <= 4.5, 0 <= d <= 20, at its true height (the
                 scale on the vertical edge is in the units of the defect).
                 The translucent plane is the height zero; the surface
                 crosses it along the wall d = b^2, drawn in that plane.  The
                 part of the surface above the plane (defect positive) and
                 the part below it (defect negative) are labelled by the
                 sign.  On the surface: the weaker wall d = 5b^2/3 where
                 e(S) = 0, the line b = 3, the four admissible
                 discriminants d = 1, 3, 5, 7 above the wall, the equality
                 case d = 9 on it and d = 11, 13, 15 below.  The d axis runs
                 from left to right, as in (b).
                 (b) the section b = 3: K_S^2 = 3(9+d)(63-d) and
                 3e(S) = 27(9+d)(15-d) against d, meeting at d = 9 in 2916,
                 with the values K_S^2 of the table of invariants at
                 d = 1, 3, 5, 7 and, as drop lines, the defect 3e(S) - K_S^2
                 at those four points; the band d > 9 is where the
                 inequality fails.

Nothing is drawn by eye.  The heights are the exact values of the formulas
of the theorem, and the tick labels are the true values at the drawn
heights.

The surface z = D(b, d) increases in b and decreases in d, and the eye is
in front (small b) and to the right (large d) and above, so every normal of
the surface faces the eye: nothing of the surface hides another part of it.
The parts are drawn in their true occlusion order for an eye above the
plane of height zero: the box, the part of the surface below zero with the
curves on it, the plane, the part above zero with the curves on it, and the
wall, which lies in the plane.
"""
import math
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from render3d import Camera, Scene                                # noqa: E402
from make_diagrams import (Plate, compile_plate, proj, orbit_eye,  # noqa
                           Axes2D, soften, ink_bbox)

GEN = "make_smooth.py"
BLO, BHI = 1.5, 4.5                 # range of b
DLO, DHI = 0.0, 20.0                # range of d
SX, SY, SZ = 0.272, 1.00, 0.225     # drawing scales on d, b and the height
ZF, ZT = -12.0, 12.0                # floor and ceiling, in thousands


def defect(b, d):
    return 24.0 * (b ** 4 - d * d)


def P(b, d, h=None):
    """The point over (b, d) at height h in thousands (default: the
    surface).  d runs along x, b along y (away from the eye)."""
    if h is None:
        h = defect(b, d) / 1000.0
    return ((d - 10.0) * SX, (b - 3.0) * SY, h * SZ)


def invariants(b, d):
    K2 = 3 * (b * b + d) * (7 * b * b - d)
    e = 3 * (b * b + d) * (5 * b * b - 3 * d)
    chi = (b * b + d) * (3 * b * b - d)
    return K2, e, chi


def fig_bmywindow():
    # the table of the paper, recomputed
    table = {1: (260, 1860, 1260), 3: (288, 2160, 1296), 5: (308, 2436, 1260),
             7: (320, 2688, 1152)}
    for d, (chi, K2, e) in table.items():
        assert invariants(3, d) == (K2, e, chi)
        assert 3 * e - K2 == defect(3, d)
    assert invariants(3, 9)[0] == 3 * invariants(3, 9)[1] == 2916
    assert max(abs(defect(b, d)) for b in (BLO, BHI) for d in (DLO, DHI)) \
        < 1000 * ZT

    tgt = P(3.0, 10.0, 0.0)
    eye = orbit_eye(tgt, 40.0, -64.0, 26.0)
    cam = Camera(eye=eye, target=tgt, focal=40.0, scale=1.0)
    pl = Plate("fig_bmywindow", GEN,
               "The Bogomolov-Miyaoka-Yau defect of a smooth support over "
               "the quarter plane of (b,d), and its section at b = 3.",
               thresh=238)

    def poly(pts, style):
        return "  \\draw[%s] %s;\n" % (style, " -- ".join(
            "(%.4f,%.4f)" % proj(cam, p) for p in pts))

    def curve(g, t0, t1, n, style):
        return poly([g(t0 + (t1 - t0) * k / n) for k in range(n + 1)], style)

    def dot(p, style):
        return "  \\node[%s] at (%.4f,%.4f) {};\n" % ((style,) + proj(cam, p))

    # ---------------------------------------------------------------- box
    bg = Scene(cam)
    bg.surface(lambda b, d: P(b, d, ZF), (BLO, BHI), (DLO, DHI), 1, 1,
               base="PSlate", opacity=0.07, ambient=0.8, diffuse=0.1)
    bg.surface(lambda d, h: P(BHI, d, h), (DLO, DHI), (ZF, ZT), 1, 1,
               base="PSlate", opacity=0.05, ambient=0.8, diffuse=0.1)
    bg.surface(lambda b, h: P(b, DLO, h), (BLO, BHI), (ZF, ZT), 1, 1,
               base="PSlate", opacity=0.05, ambient=0.8, diffuse=0.1)
    box = []
    levels = [-8.0, -4.0, 0.0, 4.0, 8.0]
    grid = "soft,PRule!75,line width=0.25pt"
    for h in levels:
        box.append(poly([P(BLO, DLO, h), P(BHI, DLO, h), P(BHI, DHI, h)],
                        grid))
    for d in (5, 10, 15):
        box.append(poly([P(BLO, d, ZF), P(BHI, d, ZF), P(BHI, d, ZT)], grid))
    for b in (2, 3, 4):
        box.append(poly([P(b, DHI, ZF), P(b, DLO, ZF), P(b, DLO, ZT)], grid))
    edge = "PSlate!85,line width=0.45pt"
    soft_edge = "soft,PSlate!55,line width=0.4pt"
    box.append(poly([P(BLO, DLO, ZT), P(BLO, DLO, ZF), P(BLO, DHI, ZF),
                     P(BHI, DHI, ZF)], edge))
    box.append(poly([P(BLO, DLO, ZT), P(BHI, DLO, ZT), P(BHI, DHI, ZT),
                     P(BHI, DHI, ZF)], soft_edge))
    box.append(poly([P(BHI, DLO, ZF), P(BHI, DLO, ZT)], soft_edge))
    box.append(poly([P(BLO, DLO, ZF), P(BHI, DLO, ZF), P(BHI, DHI, ZF)],
                    soft_edge))
    # ticks on the three edges that carry a scale
    tk = "PSlate,line width=0.45pt"
    for h in levels:
        box.append(poly([P(BLO, DLO, h), P(BLO, DLO - 0.55, h)], tk))
    for d in (0, 5, 10, 15, 20):
        box.append(poly([P(BLO, d, ZF), P(BLO - 0.16, d, ZF)], tk))
    for b in (2, 3, 4):
        box.append(poly([P(b, DHI, ZF), P(b, DHI + 0.55, ZF)], tk))

    # ------------------------------------------------------------ surface
    bw = math.sqrt(DHI)

    def dwall(b):
        return min(b * b, DHI)

    neg = Scene(cam)          # below zero: d >= b^2
    neg.surface(lambda b, s: P(b, b * b + s * (DHI - b * b)), (BLO, bw),
                (0.0, 1.0), 26, 18, base="PClay", ambient=0.36, diffuse=0.40)
    pos = Scene(cam)          # above zero: d <= b^2
    pos.surface(lambda b, s: P(b, s * dwall(b)), (BLO, BHI), (0.0, 1.0),
                30, 26, base="PIndigo", ambient=0.36, diffuse=0.40)
    zero = Scene(cam)
    zero.surface(lambda b, d: P(b, d, 0.0), (BLO, BHI), (DLO, DHI), 1, 1,
                 base="PSlate", opacity=0.34, ambient=0.85, diffuse=0.05)

    mesh = "soft,white!62!PInk,line width=0.25pt"
    top_neg, top_pos = [], []
    # the mesh b = const and d = const, split at the wall
    for b in [BLO + 0.5 * i for i in range(7)]:
        w = dwall(b)
        top_pos.append(curve(lambda d, b=b: P(b, d), DLO, w, 40, mesh))
        if w < DHI:
            top_neg.append(curve(lambda d, b=b: P(b, d), w, DHI, 40, mesh))
    for d in [DLO + 2.5 * i for i in range(9)]:
        bd = math.sqrt(d)
        if bd > BLO:
            top_neg.append(curve(lambda b, d=d: P(b, d), BLO, bd, 30, mesh))
        top_pos.append(curve(lambda b, d=d: P(b, d), max(BLO, bd), BHI, 30,
                             mesh))
    # the weaker wall d = 5b^2/3, where e(S) = 0, below zero
    b5 = math.sqrt(3 * DHI / 5)
    top_neg.append(curve(lambda b: P(b, 5 * b * b / 3.0), BLO, b5, 60,
                         "PGrass,line width=1.0pt,dash pattern=on 2.4pt "
                         "off 1.6pt"))
    # the line b = 3 and the discriminants on it
    top_pos.append(curve(lambda d: P(3.0, d), DLO, 9.0, 40,
                         "PInk!85,line width=0.6pt"))
    top_neg.append(curve(lambda d: P(3.0, d), 9.0, DHI, 50,
                         "PInk!85,line width=0.6pt"))
    for d in (1, 3, 5, 7):
        top_pos.append(dot(P(3.0, d), "circle,fill=PAmber,draw=white,"
                           "line width=0.5pt,inner sep=1.9pt"))
    for d in (11, 13, 15):
        top_neg.append(dot(P(3.0, d), "circle,draw=PClay,line width=0.8pt,"
                           "fill=white,inner sep=1.6pt"))
    # the wall d = b^2, in the plane of height zero, and d = 9 on it
    wall = [curve(lambda b: P(b, b * b), BLO, bw, 60,
                  "PMag,line width=1.3pt"),
            dot(P(3.0, 9.0), "circle,fill=PMag,draw=white,line width=0.5pt,"
                "inner sep=2.1pt")]

    body = (bg.emit() + "".join(box) + neg.emit() + "".join(top_neg)
            + zero.emit() + pos.emit() + "".join(top_pos) + "".join(wall))
    body = soften(body)
    # close the hairline seams between the facets of the opaque surface
    body = re.sub(r"\\path\[draw=none,fill=(P(?:Indigo|Clay)![0-9]+!white)\]",
                  r"\\path[draw=\1,line width=0.15pt,fill=\1]", body)
    pl.add(body)

    # ------------------------------------------------------ labels of (a)
    for h in levels:
        x, y = proj(cam, P(BLO, DLO - 0.55, h))
        t = r"$%d$" % int(1000 * h) if h >= 0 else r"$-%d$" % int(-1000 * h)
        pl.put(x - 0.08, y, t, color="PSlate", font=r"\footnotesize",
               anchor="e")
    for d in (0, 5, 10, 15, 20):
        x, y = proj(cam, P(BLO - 0.16, d, ZF))
        pl.put(x, y - 0.08, r"$%d$" % d, color="PSlate",
               font=r"\footnotesize", anchor="n")
    for b in (2, 3, 4):
        x, y = proj(cam, P(b, DHI + 0.55, ZF))
        pl.put(x + 0.10, y, r"$%d$" % b, color="PSlate", font=r"\footnotesize",
               anchor="w")
    x, y = proj(cam, P(BLO - 0.16, 10.0, ZF))
    pl.put(x, y - 0.52, r"$d$", color="PSlate", anchor="n")
    x, y = proj(cam, P(2.5, DHI + 0.55, ZF))
    pl.put(x + 0.72, y - 0.16, r"$b$", color="PSlate", anchor="w")
    xz, yz = proj(cam, P(BLO, DLO, ZT))
    pl.put(xz - 0.10, yz + 0.32, r"$3e(S)-K_{S}^{2}$", color="PSlate",
           anchor="e")

    pl.label(proj(cam, P(bw, DHI)), r"$d=b^{2}$", color="PMag",
             dirs=[0, 30, -30], rmax=1.5, skip=0.1)
    pl.label(proj(cam, P(b5, DHI)), r"$d=\tfrac53b^{2}$", color="PGrass",
             dirs=[0, -20, 20], rmax=2.0, skip=0.1)
    pl.label(proj(cam, P(3.0, DHI)), r"$b=3$", color="PInk",
             dirs=[0, -15, 15], rmax=1.5, skip=0.1)
    pl.label(proj(cam, P(4.45, 12.0)), r"$3e(S)>K_{S}^{2}$", color="PIndigo",
             dirs=[60, 45, 75, 90], rmin=0.3, rmax=3.0, skip=0.1)
    pl.label(proj(cam, P(3.9, 19.2)), r"$3e(S)<K_{S}^{2}$", color="PClay",
             dirs=[0, -15, 15, -30], rmin=0.2, rmax=3.0, skip=0.1)

    # --------------------------------------------------- (b): b = 3
    bx0, by0, bx1, by1 = ink_bbox("".join(pl.parts))
    ax = Axes2D(pl, bx1 + 2.80, by0 + 1.05, 4.5, by1 - by0 - 1.55,
                (0.0, 16.4), (0.0, 4300.0))
    pl.add("  \\path[fill=PClay!8] (%.3f,%.3f) rectangle (%.3f,%.3f);\n"
           % (ax.X(9), ax.Y(0), ax.X(16.4), ax.Y(4300)))
    ax.frame(range(0, 17, 2), range(0, 4001, 1000),
             yfmt=lambda v: "$%d$" % v if v else None)
    K2 = [(d / 10.0, 3 * (9 + d / 10.0) * (63 - d / 10.0))
          for d in range(0, 165)]
    E3 = [(d / 10.0, 27 * (9 + d / 10.0) * (15 - d / 10.0))
          for d in range(0, 151)]
    pl.add("  \\draw[PIndigo,line width=1.1pt] %s;\n"
           % " -- ".join("(%.3f,%.3f)" % ax.P(x, y) for x, y in E3))
    pl.add("  \\draw[PClay,line width=1.1pt] %s;\n"
           % " -- ".join("(%.3f,%.3f)" % ax.P(x, y) for x, y in K2))
    pl.add("  \\draw[PMag,line width=0.5pt,dash pattern=on 1.5pt off 1.5pt] "
           "(%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (ax.X(9), ax.Y(0), ax.X(9), ax.Y(2916)))
    for d in (1, 3, 5, 7):
        k2, e, _ = invariants(3, d)
        pl.add("  \\draw[PAmber!85!black,line width=0.5pt,dash pattern=on 1pt "
               "off 1pt] (%.3f,%.3f) -- (%.3f,%.3f);\n"
               % (ax.X(d), ax.Y(k2), ax.X(d), ax.Y(3 * e)))
        for v in (k2, 3 * e):
            pl.add("  \\node[circle,fill=PAmber,draw=white,line width=0.5pt,"
                   "inner sep=1.7pt] at (%.3f,%.3f) {};\n" % ax.P(d, v))
    for d in (11, 13, 15):
        k2, e, _ = invariants(3, d)
        for v in (k2, 3 * e):
            pl.add("  \\node[circle,draw=PClay,line width=0.8pt,fill=white,"
                   "inner sep=1.4pt] at (%.3f,%.3f) {};\n" % ax.P(d, v))
    pl.add("  \\node[circle,fill=PMag,draw=white,line width=0.5pt,"
           "inner sep=2.0pt] at (%.3f,%.3f) {};\n" % ax.P(9, 2916))
    pl.label(ax.P(9, 2916), r"$2916$", color="PMag", font=r"\footnotesize",
             dirs=[-20, -40, 0], rmax=0.9, skip=0.1)
    pl.label(ax.P(3, 3888), r"$3e(S)$", color="PIndigo", dirs=[90, 60, 120],
             rmax=0.8)
    pl.label(ax.P(15.5, 3 * (9 + 15.5) * (63 - 15.5)), r"$K_{S}^{2}$",
             color="PClay", dirs=[90, 60, 120], rmax=0.8)
    pl.label(ax.P(1, 1860), r"$1860$", color="PAmber!80!black",
             font=r"\footnotesize", dirs=[-60, -90, -30], rmin=0.08,
             rmax=0.9, skip=0.1)
    pl.label(ax.P(12.7, 4150), r"$d>b^{2}$", color="PClay",
             font=r"\footnotesize", dirs=[180, 0], rmin=0.0, rmax=0.6)
    pl.put(ax.X(8.2), ax.Y(0) - 0.62, r"$d$", color="PSlate", anchor="n")
    # the panel labels, on one line
    ytop = max(by1 + 0.25, ax.Y(4300) + 0.45)
    pl.put(ax.x0 - 1.25, ytop, r"(b)\ \ $b=3$", color="PInk", anchor="w")
    pl.put(bx0 - 1.2, ytop, r"(a)", color="PInk", anchor="w")
    pl.build()
    compile_plate("fig_bmywindow")


if __name__ == "__main__":
    fig_bmywindow()
