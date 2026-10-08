#!/usr/bin/env python3
"""
make_round28.py

The figures added when the paper was organised around its main theorem.

  fig_mainlocus   thm:main.  Left, in perspective: a real slice of the period
                  domain D_F as a shaded dome.  On it the explicit CM base
                  point s_0 of part (i), the Hecke orbit G_F(Q).s_0, which is
                  dense (part (ii)), three strata Sigma_{P,q} of the algebraic
                  locus through points of the orbit (part (iii)), the Hodge
                  loci Z_t off which the Hodge group is all of G_F
                  (lem:cmgeneric), and a very general point s.  Right: the two
                  cases of the dichotomy of part (iii), one stratum equal to
                  the whole domain, or a countable union of proper closed
                  strata; part (iv) says that the Hodge conjecture for the
                  very general member is the first case.
  fig_twohalves   thm:final.  Two stacked sheets in perspective: the smooth
                  projective varieties X above, the abelian varieties B below,
                  with the Weil families as a raised plate on the lower sheet.
                  A Hodge class gamma on X is the image Gamma_* beta of a
                  Hodge class beta on B under an algebraic correspondence
                  (the conjecture modulo abelian varieties, F3'), and beta is
                  algebraic (the conjecture for abelian varieties, F2); the
                  plate is where thm:main places the Weil classes.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig): no label meets ink or another label, and no
leader crosses ink, a label or another leader.

Run:  python3 -B make_round28.py     (from the figures directory)
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
from make_core import Fig, f4, orbit_cam, fit              # noqa: E402
from make_round19 import FN, SN                            # noqa: E402
from render3d import Camera, unit, cross, sub, dot         # noqa: E402

GEN = "make_round28.py"


class ShiftCam(Camera):
    """A camera whose screen image is translated by (dx, dy), so that several
    panels, each seen from the same direction, share one plate."""

    def __init__(self, base, dx, dy, scale):
        Camera.__init__(self, base.eye, (0, 0, 0), (0, 0, 1), base.focal,
                        scale)
        self.eye, self.u, self.v, self.w = base.eye, base.u, base.v, base.w
        self.dx, self.dy = dx, dy

    def project(self, p):
        (x, y), d = Camera.project(self, p)
        return (x + self.dx, y + self.dy), d


# ------------------------------------------------------------------ the dome
RAD = 2.0


def height(x, y):
    """A gentle dome over the disc of radius RAD, tilted by a saddle term so
    that the curves drawn on it read as curves on a surface."""
    r2 = (x * x + y * y) / (RAD * RAD)
    return 0.95 * (1.0 - r2) + 0.18 * (x * x - y * y) / (RAD * RAD)


def lift(x, y, eps=0.012):
    return (x, y, height(x, y) + eps)


def dome(u, v):
    r = RAD * u
    return (r * math.cos(v), r * math.sin(v), height(r * math.cos(v),
                                                     r * math.sin(v)))


def dome_normal(p):
    h = 1e-4
    x, y = p[0], p[1]
    hx = (height(x + h, y) - height(x - h, y)) / (2 * h)
    hy = (height(x, y + h) - height(x, y - h)) / (2 * h)
    return unit((-hx, -hy, 1.0))


def seen(F, p):
    """A point of the dome is visible exactly when the dome faces the camera
    there, since the dome is the graph of a concave function."""
    return dot(dome_normal(p), sub(F.cam.eye, p)) > 0


def vis_curve(F, pts, style, prio=1, chunk=10, depth=1e6 - 2):
    """Draw the visible runs of a curve lying on the dome."""
    run = []
    for q in pts + [None]:
        if q is not None and seen(F, q):
            run.append(q)
            continue
        if len(run) > 1:
            F.curve3(run, style, prio=prio, chunk=chunk, depth=depth)
        run = []


def draw_dome(F, base="PBlue", nu=14, nv=40, lo=18, hi=62, rim="PBlue!70"):
    """The dome, shaded facet by facet, and its rim."""
    for i in range(nu):
        for j in range(nv):
            ua, ub = i / nu, (i + 1) / nu
            va = 2 * math.pi * j / nv
            vb = 2 * math.pi * (j + 1) / nv
            P = [dome(ua, va), dome(ub, va), dome(ub, vb), dome(ua, vb)]
            c = tuple(sum(q[k] for q in P) / 4 for k in range(3))
            n = dome_normal(c)
            F.poly3(P, fill=F.tone(n, base, lo=lo, hi=hi), draw=None, prio=-5,
                    depth=2e6 + F.D(c))
    rimpts = [dome(1.0, 2 * math.pi * k / 160) for k in range(161)]
    vis_curve(F, rimpts, "%s,line width=0.55pt" % rim, prio=-4, chunk=20,
              depth=1e6 + 1)


def chord(a, b, n=60):
    """The lift to the dome of the segment ab of the disc."""
    return [lift(a[0] + (b[0] - a[0]) * k / n, a[1] + (b[1] - a[1]) * k / n)
            for k in range(n + 1)]


def clip_chord(p, ang, n=60):
    """The chord of the disc through p in the direction ang."""
    ux, uy = math.cos(ang), math.sin(ang)
    # solve |p + t u| = RAD * 0.985
    R = RAD * 0.985
    b = p[0] * ux + p[1] * uy
    c = p[0] ** 2 + p[1] ** 2 - R * R
    s = math.sqrt(b * b - c)
    t0, t1 = -b - s, -b + s
    return chord((p[0] + t0 * ux, p[1] + t0 * uy),
                 (p[0] + t1 * ux, p[1] + t1 * uy), n)


def arc(centre, rad, a0, a1, n=80):
    """The lift of an arc of a circle of the plane, cut to the disc."""
    pts = []
    for k in range(n + 1):
        t = a0 + (a1 - a0) * k / n
        x, y = centre[0] + rad * math.cos(t), centre[1] + rad * math.sin(t)
        if x * x + y * y < (RAD * 0.985) ** 2:
            pts.append(lift(x, y))
        elif len(pts) > 1:
            break
    return pts


def halton(i, b):
    f, r = 1.0, 0.0
    while i > 0:
        f /= b
        r += f * (i % b)
        i //= b
    return r


def orbit_points(count, skip=3):
    """Quasi-random points of the disc, standing for the dense Hecke orbit."""
    out = []
    i = skip
    while len(out) < count:
        u, v = halton(i, 2), halton(i, 3)
        r = RAD * 0.93 * math.sqrt(u)
        out.append((r * math.cos(2 * math.pi * v), r * math.sin(2 * math.pi * v)))
        i += 1
    return out


def fig_mainlocus():
    cam = orbit_cam((0.0, 0.0, 0.2), 24.0, 34.0, R=30.0)
    F = Fig("fig_mainlocus",
            "The algebraic locus of thm:main over a real slice of the period "
            "domain: the CM base point, the dense Hecke orbit, the closed "
            "strata, the Hodge loci and a very general point; right, the two "
            "cases of the dichotomy.", cam, gen=GEN)
    rim = [dome(1.0, 2 * math.pi * k / 64) for k in range(64)]
    bx0, by0, bx1, by1 = fit(cam, rim + [(0, 0, 0.95)], 7.4)
    base_scale = cam.scale

    draw_dome(F)
    s0 = (-0.55, -0.35)
    # Hodge loci Z_t: chords of the disc, one of them through s_0, drawn thin
    Z = [((-0.55, -0.35), 0.35), ((0.9, 0.55), 1.95), ((-1.2, 0.8), 2.6),
         ((0.3, -1.25), 0.05), ((1.3, -0.4), 1.25), ((-0.2, 1.3), -0.2)]
    for k, (p, ang) in enumerate(Z):
        pts = clip_chord(p, ang)
        style = ("PClay,line width=0.55pt,dash pattern=on 2.4pt off 1.4pt"
                 if k else "PClay,line width=0.95pt")
        vis_curve(F, pts, style, prio=1, chunk=10, depth=1e6 - 2)
    # strata Sigma_{P,q}: arcs through points of the orbit
    strata = [((0.25, -0.1), 1.05, 2.2, 5.3),
              ((-0.9, 0.6), 0.85, -1.4, 1.9),
              ((0.95, 0.95), 0.7, 2.6, 5.6)]
    for c, r, a0, a1 in strata:
        vis_curve(F, arc(c, r, a0, a1), "PGrass,line width=1.05pt", prio=2,
                  chunk=10, depth=1e6 - 3)
    # the dense orbit
    orb = orbit_points(78)
    orb = [q for q in orb if seen(F, lift(*q))]
    for q in orb:
        F.dot3(lift(*q), "PIndigo", r=0.95, ring="white", prio=3,
               depth=1e6 - 4)
    # the base point and a very general point
    F.dot3(lift(*s0), "PInk", r=2.3, ring="white", prio=5, depth=1e6 - 6)
    sg = (1.28, 0.02)
    F.dot3(lift(*sg), "POchre", r=2.1, ring="white", prio=5, depth=1e6 - 6)

    # labels of the dome, placed around it with leaders
    F.alabel(F.P(lift(*s0)), r"$s_{0}$, the CM base point (i)", color="PInk",
             font=SN, prefer=235, spread=90, rmin=0.2, rmax=3.2, lead=0.3,
             free=1.9)
    F.alabel(F.P(lift(*sg)), r"$s$ very general: $\mathrm{Hg}(A_{s})=G_{F}$",
             color="POchre!80!black", font=SN, prefer=-20, spread=80,
             rmin=0.2, rmax=3.2, lead=0.3, free=1.7)
    c, r, a0, a1 = strata[2]
    tgt = arc(c, r, a0, a1)[len(arc(c, r, a0, a1)) // 2]
    F.alabel(F.P(tgt), r"strata $\Sigma_{\underline{P},\underline{q}}$ (iii)",
             color="PGrass!85!black", font=SN, prefer=60, spread=80, rmin=0.2,
             rmax=3.0, lead=0.3, free=1.4)
    zp = clip_chord(*Z[3])[2]
    F.alabel(F.P(zp), r"Hodge loci $Z_{t}$", color="PClay", font=SN,
             prefer=-120, spread=90, rmin=0.2, rmax=3.0, lead=0.3, free=0.6)
    F.alabel(F.P(lift(*orb[5])), r"$G_{F}(\QQ)\cdot s_{0}$, dense (ii)",
             color="PIndigo", font=SN, prefer=110, spread=70, rmin=0.2,
             rmax=3.4, lead=0.3, free=1.6)
    F.alabel(F.P(dome(1.0, -1.35)), r"$\cD_{F}$", color="PBlue", font=FN,
             prefer=-80, spread=60, rmin=0.12, rmax=1.4, lead=0.3, free=0.2)

    # ---- the dichotomy, two small domes on the right
    small = 0.39
    xr = bx1 + 2.75
    tops = [(xr, by1 - 0.95), (xr, by0 + 0.55)]
    heads = [r"$\Sigma_{F}=\cD_{F}$: one stratum is everything",
             r"$\Sigma_{F}$ meagre: proper closed strata"]
    for panel, ((cx, cy), head) in enumerate(zip(tops, heads)):
        sc = ShiftCam(cam, 0.0, 0.0, base_scale * small)
        c0 = sc.project((0, 0, 0.3))[0]
        sc.dx, sc.dy = cx - c0[0], cy - c0[1]
        F.cam = sc
        base = "PGrass" if panel == 0 else "PBlue"
        draw_dome(F, base=base, nu=10, nv=32, lo=20 if panel == 0 else 18,
                  hi=58, rim="%s!70" % base)
        if panel == 1:
            for p, ang in [((0.2, -0.3), 0.6), ((-0.6, 0.5), 2.1),
                           ((0.8, 0.6), 1.3), ((-0.3, -1.1), 2.9)]:
                vis_curve(F, clip_chord(p, ang, 30),
                          "PGrass,line width=0.8pt", prio=2, chunk=10,
                          depth=1e6 - 3)
        rimp = [sc.project(dome(a / 8.0, 2 * math.pi * k / 48))[0]
                for k in range(48) for a in range(9)]
        top = max(q[1] for q in rimp)
        F.label(cx, top + 0.32, head, anchor="south",
                color="PGrass!85!black" if panel == 0 else "PBlue",
                font=SN)
        F.cam = cam
    ybot = min(sc.project(dome(1.0, 2 * math.pi * k / 48))[0][1]
               for k in range(48))
    F.label(xr, ybot - 0.22,
            r"(iv) the Hodge conjecture holds for the very", anchor="north",
            color="PInk", font=SN)
    F.label(xr, ybot - 0.62, r"general member exactly in the upper case",
            anchor="north", color="PInk", font=SN)
    F.write()


# ------------------------------------------------------------ the two halves
def sheet(z, x0, x1, y0, y1):
    return [(x0, y0, z), (x1, y0, z), (x1, y1, z), (x0, y1, z)]


def fig_twohalves():
    cam = orbit_cam((0.0, 0.0, 1.0), 28.0, 22.0, R=30.0)
    F = Fig("fig_twohalves",
            "The two halves of the conjecture in thm:final: a Hodge class on "
            "X is carried by an algebraic correspondence from a Hodge class "
            "on an abelian variety (F3'), which is algebraic (F2); the Weil "
            "families are the plate where thm:main applies.", cam, gen=GEN)
    top = sheet(2.25, -2.6, 2.6, -1.4, 1.4)
    bot = sheet(0.0, -2.6, 2.6, -1.4, 1.4)
    plate = [(0.35, -0.95, 0.10), (2.15, -0.95, 0.10), (2.15, 0.95, 0.10),
             (0.35, 0.95, 0.10)]
    fit(cam, top + bot, 8.2)
    F.poly3(bot, fill="WTeal", draw="PTeal!80", lw=0.6, prio=-4, depth=1e6)
    # the plate of the Weil families, raised, with its side faces
    F.prism((0.35, -0.95, 0.0), (2.15, 0.95, 0.10), "PGrass", prio=-3,
            lw=0.4)
    F.poly3(top, fill="WSlate", draw="PSlate!80", lw=0.6, opacity=0.72,
            prio=4, depth=-1e6)
    # classes and correspondence
    beta = (-1.15, 0.05, 0.0)
    gamma = (-0.35, 0.25, 2.25)
    w = (1.25, 0.0, 0.10)
    F.dot3(beta, "PTeal", r=2.2, prio=2)
    F.dot3(w, "PGrass", r=2.2, prio=2)
    F.dot3(gamma, "PInk", r=2.3, prio=6, depth=-1e6 - 3)
    # Gamma: an arc from beta up to gamma, dashed where it is behind the top
    arcpts = []
    for k in range(41):
        t = k / 40
        x = beta[0] + (gamma[0] - beta[0]) * t
        y = beta[1] + (gamma[1] - beta[1]) * t - 0.55 * math.sin(math.pi * t)
        z = beta[2] + (gamma[2] - beta[2]) * t
        arcpts.append((x, y, z))
    F.line3(arcpts[:-1], "PIndigo,line width=0.9pt,dash pattern=on 2.6pt "
            "off 1.4pt", prio=3, depth=1e6 - 5)
    F.line3(arcpts[-4:], "PIndigo,line width=0.9pt,-{Stealth[length=4.4pt,"
            "width=3.4pt]}", prio=7, depth=-1e6 - 4)
    # a second correspondence from the plate, to a class on X
    gamma2 = (1.55, -0.35, 2.25)
    F.dot3(gamma2, "PInk", r=2.3, prio=6, depth=-1e6 - 3)
    arc2 = [(w[0] + (gamma2[0] - w[0]) * t, w[1] + (gamma2[1] - w[1]) * t
             + 0.45 * math.sin(math.pi * t), w[2] + (gamma2[2] - w[2]) * t)
            for t in [k / 40 for k in range(41)]]
    F.line3(arc2[:-1], "PIndigo,line width=0.9pt,dash pattern=on 2.6pt "
            "off 1.4pt", prio=3, depth=1e6 - 5)
    F.line3(arc2[-4:], "PIndigo,line width=0.9pt,-{Stealth[length=4.4pt,"
            "width=3.4pt]}", prio=7, depth=-1e6 - 4)

    # labels
    F.alabel(F.P((2.6, 1.4, 2.25)),
             r"smooth projective varieties $X$", color="PSlate", font=FN,
             prefer=10, spread=60, rmin=0.12, rmax=1.6, lead=0.3, free=0.2)
    F.alabel(F.P((2.6, 1.4, 0.0)), r"abelian varieties $B$",
             color="PTeal!80!black", font=FN, prefer=10, spread=60,
             rmin=0.12, rmax=1.6, lead=0.3, free=0.2)
    F.alabel(F.P(gamma), r"$\gamma\in\Hdg^{p}(X)$", color="PInk", font=SN,
             prefer=150, spread=70, rmin=0.2, rmax=3.2, lead=0.3, free=1.9)
    F.alabel(F.P(gamma2), r"$\gamma'=\Gamma'_{*}\omega$", color="PInk",
             font=SN, prefer=30, spread=70, rmin=0.2, rmax=3.2, lead=0.3,
             free=1.5)
    F.alabel(F.P(beta), r"$\beta\in\Hdg(B)$, algebraic by (F2)",
             color="PTeal!80!black", font=SN, prefer=200, spread=60,
             rmin=0.2, rmax=3.4, lead=0.3, free=1.4)
    F.alabel(F.P((0.35, -0.95, 0.10)),
             r"Weil families: $\Sigma_{F}$ dense (\textup{Theorem 1.1})",
             color="PGrass!85!black", font=SN, prefer=-100, spread=70,
             rmin=0.2, rmax=3.0, lead=0.3, free=0.5)
    F.alabel(F.P(w), r"Weil class $\omega$", color="PGrass!85!black",
             font=SN, prefer=-30, spread=70, rmin=0.2, rmax=3.0, lead=0.3,
             free=1.1)
    F.alabel(F.P(arcpts[14]),
             r"$\gamma=\Gamma_{*}\beta$, $\Gamma$ algebraic on $B\times X$: (F3$'$)",
             color="PIndigo", font=SN, prefer=190, spread=60, rmin=0.2,
             rmax=3.4, lead=0.3, free=1.1)
    cx, cy = F.P((2.6, -1.4, 0.0))
    F.label(cx + 0.35, cy - 0.05,
            r"Hodge conjecture $\Longleftrightarrow$ (F2) and (F3$'$)",
            anchor="west", color="PInk", font=FN)
    F.write()


ALL = ["mainlocus", "twohalves"]

if __name__ == "__main__":
    names = sys.argv[1:] or ALL
    for n in names:
        globals()["fig_" + n]()
