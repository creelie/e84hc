#!/usr/bin/env python3
"""
make_round40.py

The figures of round 40.

  fig_vandermonde   thm:vandermonde and cor:twodiagonal.  Left: the
                    generalised Fermat curve C over P^1, drawn as five
                    sheets that meet over the branch points lambda_0, ...,
                    lambda_5 (the cover has degree d^N; the sheets stand for
                    it).  Top row: the curve, the complete intersection
                    X = C^r/G with the map Phi and its degree |G|, and the
                    decomposition of H^r(X) into the line of eta and the
                    pieces W_[a].  Bottom row: where the Hodge conjecture for
                    X stands, according to the abelian varieties B_[a]: known
                    when they have dimension at most five, open when they are
                    larger or carry Weil classes of Q(zeta_e) with
                    phi(e) >= 4.  The numbers printed are checked below
                    against the formulas of the theorem.

                    A strip at the foot records
                    thm:vgvandermonde: the very general member, every N.

  fig_efourshifts   lem:efourshifts and thm:efourtwolevels.  The value phi
                    of a piece on the horizontal axis (p below t_1 < t_2 <
                    t_3, one of the four placements), the shift on the
                    vertical axis.  The pieces L_zeta sit at the shifts s and
                    s - 1; the run L -> M_1 -> M_2 -> M_3 -> L' up three
                    times and down once ends four shifts lower, the least
                    drop of lem:efourshifts (iii); a top piece W and one of
                    its 28 partners V one shift lower carry the block
                    H^3(W, V).  Beside it the statement of the theorem.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round40.py     (from the figures directory)
"""
import math
import os
import sys
from fractions import Fraction
from itertools import product
from math import factorial, gcd

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402

make_round19.GEN = "make_round40.py"


# ------------------------------------------------------------ the numbers
def genus(d, N):
    return 1 + Fraction(d ** (N - 1) * ((N - 1) * (d - 1) - 2), 2)


def weil_orbits(d):
    """Balanced characters with six nonzero coordinates in P^6, of order at
    least three, up to (Z/d)^x."""
    units = [u for u in range(1, d) if gcd(u, d) == 1]
    orbs = set()
    for a in product(range(d), repeat=7):
        if sum(a) % d or sum(1 for x in a if x) != 6:
            continue
        if d // gcd(d, *a) < 3 or sum(a) != 3 * d:
            continue
        orbs.add(min(tuple(u * x % d for x in a) for u in units))
    return len(orbs)


assert genus(2, 4) == 5 and genus(3, 2) == 1 and genus(4, 2) == 3
assert [factorial(2) * 2 ** 3, factorial(3) * 2 ** 8] == [16, 1536]
ORBITS = {3: 70, 4: 490, 6: 6125}
assert all(weil_orbits(d) == k for d, k in ORBITS.items())


# ------------------------------------------------------------ fig_vandermonde
def fig_vandermonde():
    F = Plate("fig_vandermonde",
              "Diagonal complete intersections of Vandermonde type "
              "(thm:vandermonde, cor:twodiagonal).")
    arrow = "PInk,line width=0.6pt," + TIP

    # the curve over the line
    x0, x1, yl = 0.25, 3.55, 0.75
    lam = [0.55 + 0.56 * k for k in range(6)]
    F.seg([(x0, yl), (x1, yl)], "PSlate,line width=0.6pt")
    for k, x in enumerate(lam):
        F.disc(x, yl, 1.7, "PClay", ring="white", lw=0.4)
        F.text(x, yl - 0.13, r"$\lambda_{%d}$" % k, anchor="north",
               color="PClay!85!black", font=SN)
    F.text(x1 + 0.08, yl, r"$\PP^{1}$", anchor="west", color="PSlate",
           font=SN)
    yc = 2.05
    for k in (-2, -1, 0, 1, 2):
        pts = []
        n = 120
        for i in range(n + 1):
            x = lam[0] + (lam[-1] - lam[0]) * i / n
            ph = (x - lam[0]) / (lam[1] - lam[0]) * math.pi
            pts.append((x, yc + 0.17 * k * abs(math.sin(ph))))
        F.seg(pts, "PTeal,line width=%.2fpt" % (0.75 if k == 0 else 0.45))
    F.text(lam[0] - 0.12, yc, r"$C$", anchor="east", color="PTeal")
    F.seg([(2.05, yc - 0.48), (2.05, yl + 0.18)], arrow)
    F.text(2.24, (yc - 0.48 + yl + 0.18) / 2, r"$C/H$", anchor="west",
           color="PInk", font=SN)

    # the top row of boxes
    top0, top1, step = 2.95, 6.30, 0.52
    boxes = [(0.05, 4.50, "WTeal"), (4.90, 9.20, "WBlue"),
             (9.90, 15.65, "WBlue")]
    for bx0, bx1, col in boxes:
        F.rect(bx0, top0, bx1, top1, fill=col, bg=True, rc=3)
    rows_a = [r"\textbf{generalised Fermat curve}",
              r"$C=X_{d,1}(\lambda)\subset\PP^{N}$",
              r"$C\to\PP^{1}$ Galois, with group",
              r"$H=\mu_{d}^{N+1}/\mu_{d}$, of genus",
              r"$1+\frac12d^{N-1}\bigl((N-1)(d-1)-2\bigr)$"]
    rows_b = [r"\textbf{the complete intersection}",
              r"$X\cong X_{d,r}(\lambda)$",
              r"$c=N-r$ diagonal equations",
              r"$\Phi(u)_{i}=\prod_{j}u^{(j)}_{i}$, $X\cong C^{r}/G$",
              r"$\deg\Phi=|G|=r!\,d^{N(r-1)}$",
              r"$X\in\cA$: (F3$'$) in every degree"]
    rows_c = [r"\textbf{the Hodge classes of degree $r$}",
              r"$H^{r}(X)=\CC\eta\oplus\bigoplus_{[a]}W_{[a]}$",
              r"$W_{[a]}=\bigoplus_{a'\in[a]}\bigwedge^{r}V_{a'}$",
              r"$\dim V_{a}=\#\{i:a_{i}\ne0\}-2$",
              r"$W_{[a]}$ is the image of $H^{r}(B_{[a]})$",
              r"under an algebraic correspondence"]
    for (bx0, bx1, _), rows in zip(boxes, (rows_a, rows_b, rows_c)):
        for k, s in enumerate(rows):
            F.text(bx0 + 0.16, top1 - 0.28 - step * k, s, anchor="west",
                   font=SN if k else FN, onbg=True)
    ym = (top0 + top1) / 2
    F.seg([(4.57, ym), (4.83, ym)], arrow)
    F.seg([(9.27, ym), (9.83, ym)], arrow)
    F.text(9.55, ym + 0.17, r"$\Phi^{*}$", anchor="south", font=SN)

    # the bottom row: where the conjecture stands
    bot0, bot1 = 0.05, 2.45
    lows = [(4.90, 9.20, "WTeal", "PGrass",
             [r"\textbf{known: $\dim B_{[a]}\le5$}",
              r"Markman, Moonen--Zarhin",
              r"$d\in\{3,4,6\}$ and $N\le6$,",
              r"or $d=2$ and $N\le12$;",
              r"$70$, $490$, $6125$ Weil orbits in $\PP^{6}$"]),
            (9.45, 12.55, "WClay", "PClay",
             [r"\textbf{open: $\dim B_{[a]}>5$}",
              r"$N\ge7$ and $d\in\{3,4,6\}$,",
              r"or $N\ge13$ and $d=2$",
              r"a case of (F2)"]),
            (12.75, 15.65, "WClay", "PClay",
             [r"\textbf{open: $\varphi(e)\ge4$}",
              r"$d=5$ or $d\ge7$",
              r"Weil classes of $\QQ(\zeta_{e})$",
              r"$\mathrm{P2}_{\mathrm{split}}$ of the paper"])]
    for bx0, bx1, fill, ink, rows in lows:
        F.rect(bx0, bot0, bx1, bot1, fill=fill, bg=True, rc=3)
        for k, s in enumerate(rows):
            F.text(bx0 + 0.16, bot1 - 0.30 - 0.44 * k, s, anchor="west",
                   color=ink if k == 0 else "PInk", font=SN if k else FN,
                   onbg=True)
    F.seg([(11.10, top0 - 0.06), (7.60, bot1 + 0.08)], arrow)
    F.seg([(11.50, top0 - 0.06), (11.00, bot1 + 0.08)], arrow)
    F.seg([(11.90, top0 - 0.06), (14.20, bot1 + 0.08)], arrow)

    # the very general member (thm:vgvandermonde)
    F.rect(0.05, -1.16, 15.65, -0.16, fill="PGrass!20!white", bg=True, rc=3)
    F.text(0.21, -0.43,
           r"\textbf{very general $\lambda$, every $N$:} the Hodge "
           r"conjecture holds for $d=2$ in every dimension, for $d=3,4$ "
           r"up to dimension $7$", anchor="west", font=SN, onbg=True)
    F.text(0.21, -0.88,
           r"and for $d=6$ up to dimension $5$, through the monodromy of the "
           r"cyclic covers of degree $3$, $4$ and $6$ of $\PP^{1}$",
           anchor="west", font=SN, onbg=True)
    F.write()
    return F.name


# ------------------------------------------------------------ fig_efourshifts
def fig_efourshifts():
    F = Plate("fig_efourshifts",
              "Shifts along chains at n = 4 and the two-shift theorem "
              "(lem:efourshifts, thm:efourtwolevels).")
    arrow = "PInk,line width=0.6pt," + TIP
    X = {"p": 1.95, "t1": 4.15, "t2": 5.75, "t3": 7.35}

    def Y(k):
        return 2.95 + 0.62 * k

    # axes
    F.seg([(0.95, Y(-4.7)), (0.95, Y(3.7))], "PSlate,line width=0.5pt," + TIP)
    F.seg([(0.95, Y(-4.7)), (8.2, Y(-4.7))], "PSlate,line width=0.5pt," + TIP)
    F.text(0.95, Y(3.7) + 0.08, r"shift", anchor="south", color="PSlate",
           font=SN)
    F.text(8.28, Y(-4.7), r"$\phi$", anchor="west", color="PSlate", font=SN)
    for k in range(-4, 4):
        lab = "s" if k == 0 else "s%+d" % k
        F.seg([(0.88, Y(k)), (0.95, Y(k))], "PSlate,line width=0.5pt")
        F.text(0.82, Y(k), r"$%s$" % lab, anchor="east", color="PSlate",
               font=SN)
    for key, lab in (("p", "p"), ("t1", "t_{1}"), ("t2", "t_{2}"),
                     ("t3", "t_{3}")):
        F.seg([(X[key], Y(-4.7)), (X[key], Y(-4.7) - 0.07)],
              "PSlate,line width=0.5pt")
        F.text(X[key], Y(-4.7) - 0.16, r"$%s$" % lab, anchor="north",
               color="PSlate", font=SN)
    for key in ("t1", "t2", "t3"):
        F.seg([(X[key], Y(-4.4)), (X[key], Y(3.5))],
              "PRule,line width=0.35pt,dash pattern=on 1.6pt off 1.6pt")

    # the pieces at the shifts s and s - 1
    for k, col in ((0, "PBlue"), (-1, "PTeal")):
        for j in range(5):
            F.disc(X["p"] - 0.36 + 0.18 * j, Y(k), 1.6, col, ring="white",
                   lw=0.35)
    F.text(X["p"] - 0.48, Y(0), r"$W$", anchor="east", color="PBlue",
           font=SN)
    F.text(X["p"] - 0.48, Y(-1), r"$V$", anchor="east", color="PTeal",
           font=SN)

    # the block H^3(W, V)
    F.bez((X["p"] + 0.42, Y(0) - 0.08), (X["p"] + 0.70, Y(-0.2)),
          (X["p"] + 0.70, Y(-0.8)), (X["p"] + 0.42, Y(-1) + 0.08),
          "PMag,line width=0.8pt," + TIP)
    F.text(X["p"] + 0.80, Y(-0.5), r"$\mathcal{H}^{3}(W,V)$", anchor="west",
           color="PMag", font=SN)

    # the run: up three times, down once
    run = [("p", 0), ("t1", 1), ("t2", 2), ("t3", 3), ("p", -4)]
    pts = [(X[a], Y(k)) for a, k in run]
    for (xa, ya), (xb, yb) in zip(pts, pts[1:]):
        L = math.hypot(xb - xa, yb - ya)
        ux, uy = (xb - xa) / L, (yb - ya) / L
        F.seg([(xa + 0.12 * ux, ya + 0.12 * uy),
               (xb - 0.12 * ux, yb - 0.12 * uy)], arrow)
    for (a, k), name in zip(run[1:4], ("M_{1}", "M_{2}", "M_{3}")):
        F.disc(X[a], Y(k), 2.2, "POchre", ring="white", lw=0.45)
        if name == "M_{2}":
            F.text(X[a] - 0.12, Y(k) + 0.10, r"$%s$" % name,
                   anchor="south east", color="POchre!80!black", font=SN)
        else:
            F.text(X[a] + 0.12, Y(k) - 0.10, r"$%s$" % name,
                   anchor="north west", color="POchre!80!black", font=SN)
    F.disc(X["p"], Y(-4), 2.0, "PBlue", ring="white", lw=0.45)
    F.text(X["p"] - 0.14, Y(-4), r"$L_{\zeta'}$", anchor="east",
           color="PBlue", font=SN)
    for (xa, ya), (xb, yb) in zip(pts[:3], pts[1:4]):
        F.text((xa + xb) / 2 - 0.10, (ya + yb) / 2 + 0.13, r"$+1$",
               anchor="south east", font=SN)
    xa, ya = pts[3]
    xb, yb = pts[4]
    F.text(xa + (xb - xa) * 0.42 + 0.06, ya + (yb - ya) * 0.42 - 0.08,
           r"$-7$", anchor="north west", font=SN)

    # the statement
    sx, sy, dy = 9.1, Y(3.3), 0.47
    rows = [r"\textbf{Two shifts on $E_{0}^{8}$}",
            r"$W$: the $64$ pieces with $\prod\zeta=\epsilon$, at shift $s$;",
            r"$V$: the other $64$, at shift $s-1$;",
            r"a step up in $\phi$ has $\Ext$ degree $0$: shift $+1$;",
            r"a step down has $\Ext$ degree $8$: shift $-7$;",
            r"a run through the multiples drops $\ge4$,",
            r"so no product reaches $\mathcal{H}^{3}(W,V)$,",
            r"and no term of $d_{E}$ leaves it;",
            r"each top piece has $28$ partners $V$, with",
            r"$D=16$ or $64$, $640$ classes in all:",
            r"$\dim\Ext^{2}(E,E)\ge64\cdot640=40960$,",
            r"against $104$ for the polarised criterion;",
            r"three consecutive: $\ge22528$; more stay open"]
    for k, s in enumerate(rows):
        F.text(sx, sy - dy * k, s, anchor="west",
               font=FN if k == 0 else SN,
               color="PClay" if k == len(rows) - 1 else "PInk")
    F.write()
    return F.name


# ================================================================== main
ALL = ["vandermonde", "efourshifts"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
