#!/usr/bin/env python3
"""
make_round42.py

The figure of round 42.

  fig_cyclicmerge   the proof of prop:cyclicmonodromy.  Left: two branch
                    points lambda_1, lambda_2 collide inside a disc
                    (lem:cabling); the cycles outside the disc form the
                    hyperplane Y = E_{a'}, the cycle I of the disc spans
                    the complementary line, and the full twist gamma of the
                    second and third points moves both.  Middle: the
                    decomposition of sl(E_a) under sl(Y) into the adjoint
                    representation, Y, Y^* and the trivial one, used by
                    lem:hyperplanes.  Right: the induction on n = p + q,
                    each merge of two branch points lowering p or q by one
                    (lem:merge, lem:mergefive), down to n = 2, where the
                    full twist of two points with opposite exponents is a
                    transvection; on the axes p q = 0 the monodromy is
                    finite.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round42.py     (from the figures directory)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402

make_round19.GEN = "make_round42.py"


# ------------------------------------------------------------ fig_cyclicmerge
def fig_cyclicmerge():
    F = Plate("fig_cyclicmerge",
              "Collision of two branch points, two copies of SL(Y), and the "
              "induction on n (prop:cyclicmonodromy).")
    arrow = "PInk,line width=0.6pt," + TIP
    ytop, ybot = 4.62, -0.50

    # ------------------------------------------------ panel A: the collision
    F.rect(0.05, ybot, 4.95, ytop, fill="WTeal", bg=True, rc=3)
    F.text(0.25, 4.32, r"\textbf{two branch points collide}", anchor="west",
           onbg=True)
    yl = 2.45
    xs = [0.70, 1.45, 2.55, 3.40, 4.25]
    F.seg([(0.25, yl), (4.70, yl)], "PSlate,line width=0.6pt")
    # the cycle I of the disc around lambda_1, lambda_2
    F.ink(r"  \draw[PMag,line width=0.9pt] (1.0750,%.4f) ellipse "
          r"(0.6200cm and 0.4000cm);" % yl)
    # cycles outside the disc
    for k, (cx, col) in enumerate(((2.975, "PTeal"), (3.825, "PBlue"))):
        F.ink(r"  \draw[%s,line width=0.8pt] (%.4f,%.4f) ellipse "
              r"(0.5500cm and 0.3000cm);" % (col, cx, yl))
    for k, x in enumerate(xs):
        F.disc(x, yl, 1.7, "PClay", ring="white", lw=0.4)
        F.text(x, yl - 0.47 if k < 2 else yl - 0.37,
               r"$\lambda_{%d}$" % (k + 1), anchor="north",
               color="PClay!85!black", font=SN, onbg=True)
    F.text(0.45, yl + 0.22, r"$I$", anchor="south east", color="PMag",
           onbg=True)
    F.text(3.40, yl + 0.36, r"$Y$", anchor="south", color="PTeal",
           onbg=True)
    # the full twist gamma of lambda_2 and lambda_3
    F.bez((1.50, yl + 0.13), (1.66, yl + 0.62), (2.38, yl + 0.62),
          (2.52, yl + 0.15), "PIndigo,line width=0.7pt," + TIP)
    F.bez((2.60, yl + 0.18), (2.50, yl + 1.02), (1.55, yl + 1.02),
          (1.42, yl + 0.20), "PIndigo,line width=0.7pt," + TIP)
    F.text(2.02, yl + 0.96, r"$\gamma=A_{23}$", anchor="south",
           color="PIndigo", font=SN, onbg=True)
    rows = [r"$E_{a}=Y\oplus KI$ with $Y\cong E_{a'}$;",
            r"doubled braids: $E_{a'}$ on $Y$, $\zeta^{j}$ on $I$",
            r"$\gamma(I)=I+(1-t_{1})t_{2}I_{23}$, so",
            r"$\gamma KI\ne KI$ and $\gamma Y\ne Y$"]
    for k, s in enumerate(rows):
        F.text(0.25, 1.15 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel B: two copies
    F.rect(5.30, ybot, 9.95, ytop, fill="WBlue", bg=True, rc=3)
    F.text(5.50, 4.32, r"\textbf{two copies of $\mathrm{SL}(Y)$}",
           anchor="west", onbg=True)
    bx, by, sy, sl = 5.75, 3.50, 1.40, 0.46
    g = 0.05
    blocks = [(bx, by - sy, bx + sy, by, "PTeal!28!white",
               r"$\mathfrak{sl}(Y)$"),
              (bx + sy + g, by - sy, bx + sy + g + sl, by, "PBlue!28!white",
               r"$Y$"),
              (bx, by - sy - g - sl, bx + sy, by - sy - g, "POchre!32!white",
               r"$Y^{*}$"),
              (bx + sy + g, by - sy - g - sl, bx + sy + g + sl, by - sy - g,
               "PGrass!32!white", r"$z$")]
    for x0, y0, x1, y1, fill, lab in blocks:
        F.rect(x0, y0, x1, y1, fill=fill, bg=True)
        F.text((x0 + x1) / 2, (y0 + y1) / 2, lab, anchor="center", font=SN,
               onbg=True)
    F.text(bx + sy / 2, by + 0.06, r"$Y$", anchor="south", color="PSlate",
           font=SN, onbg=True)
    F.text(bx + sy + g + sl / 2, by + 0.06, r"$KI$", anchor="south",
           color="PSlate", font=SN, onbg=True)
    side = [r"$S=\mathrm{SL}(Y)\times1$",
            r"and $\gamma S\gamma^{-1}$",
            r"generate",
            r"$\mathrm{SL}(E_{a})$"]
    for k, s in enumerate(side):
        F.text(8.00, 3.30 - 0.45 * k, s, anchor="west", font=SN, onbg=True,
               color="PIndigo" if k == 3 else "PInk")
    rows = [r"four distinct $\mathfrak{sl}(Y)$-modules,",
            r"as $\dim Y\ge3$; no common invariant",
            r"subspace, so $\mathfrak{t}\supseteq Y,Y^{*}$, and",
            r"$[Y,Y^{*}]\ni z$ gives $\mathfrak{t}=\mathfrak{sl}(E_{a})$"]
    for k, s in enumerate(rows):
        F.text(5.50, 1.15 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel C: induction
    F.rect(10.30, ybot, 15.70, ytop, fill="WOchre", bg=True, rc=3)
    F.text(10.50, 4.32, r"\textbf{induction on $n=p+q$}", anchor="west",
           onbg=True)
    ox, oy, sp, M = 10.95, 1.55, 0.42, 5

    def P(p, q):
        return ox + p * sp, oy + q * sp

    for i in range(M + 1):
        F.seg([P(i, 0), P(i, M)], "PRule,line width=0.3pt")
        F.seg([P(0, i), P(M, i)], "PRule,line width=0.3pt")
    for p in range(M + 1):
        for q in range(M + 1):
            n = p + q
            if n < 2:
                continue
            x, y = P(p, q)
            if p == 0 or q == 0:
                F.disc(x, y, 1.5, "PSlate!55", ring="white", lw=0.3)
            elif n == 2:
                F.disc(x, y, 2.3, "POchre", ring="white", lw=0.4)
            else:
                F.disc(x, y, 2.3, "PGrass", ring="white", lw=0.4)
    chain = [(4, 4), (4, 3), (3, 3), (3, 2), (2, 2), (2, 1), (1, 1)]
    for (p0, q0), (p1, q1) in zip(chain, chain[1:]):
        (x0, y0), (x1, y1) = P(p0, q0), P(p1, q1)
        dx, dy = x1 - x0, y1 - y0
        L = (dx * dx + dy * dy) ** 0.5
        e = 0.10 / L
        F.seg([(x0 + e * dx, y0 + e * dy), (x1 - e * dx, y1 - e * dy)],
              "PMag,line width=0.7pt," + TIP)
    for i in range(M + 1):
        x, y = P(i, 0)
        F.text(x, y - 0.10, "$%d$" % i, anchor="north", font=SN, onbg=True)
        if i:
            x, y = P(0, i)
            F.text(x - 0.10, y, "$%d$" % i, anchor="east", font=SN,
                   onbg=True)
    F.text(ox + M * sp + 0.32, oy - 0.22, r"$p$", anchor="west", font=SN,
           onbg=True)
    F.text(ox - 0.48, oy + M * sp, r"$q$", anchor="east", font=SN,
           onbg=True)
    right = [r"each arrow merges",
             r"two branch points;",
             r"the order $m$ and",
             r"$p,q\ge1$ are kept"]
    for k, s in enumerate(right):
        F.text(13.30, 3.55 - 0.45 * k, s, anchor="west", font=SN, onbg=True,
               color="PMag" if k < 2 else "PInk")
    keys = [("POchre", 2.3, r"$n=2$: a transvection"),
            ("PGrass", 2.3, r"$n\ge3$: two hyperplanes, by induction"),
            ("PSlate!55", 1.5, r"$p=0$ or $q=0$: finite monodromy")]
    for k, (col, rad, s) in enumerate(keys):
        yk = 0.62 - 0.42 * k
        F.disc(10.60, yk, rad, col, ring="white", lw=0.4)
        F.text(10.78, yk, s, anchor="west", font=SN, onbg=True)

    # arrows between the panels
    F.seg([(4.98, 2.45), (5.27, 2.45)], arrow)
    F.seg([(9.98, 2.45), (10.27, 2.45)], arrow)
    F.write()
    return F.name


# ================================================================== main
ALL = ["cyclicmerge"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
