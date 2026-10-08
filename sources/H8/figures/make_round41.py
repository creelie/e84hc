#!/usr/bin/env python3
"""
make_round41.py

The figures of round 41.

  fig_vgmonodromy   the proof of thm:vgvandermonde.  Left: the curve D_a of
                    a character of order two, a hyperelliptic curve over
                    the 2g + 2 points of the support of a, with the chain
                    of vanishing cycles c_1, ..., c_{2g+1} and the full
                    twist of two neighbouring points, which acts by the
                    square of a Picard-Lefschetz transvection.  Middle: the
                    chain as a graph and the induction in Sym^2 V_a that
                    makes the logarithms N_k generate sp(V_a).  Right: what
                    the monodromy leaves of the Hodge classes, for
                    characters of order two (powers of the polarisation)
                    and of order three, four and six (Weil classes of
                    Q(sqrt(-3)) and Q(i), prop:cyclicmonodromy).

  fig_vgscope       the very general X_{d,r}(lambda), for every N, by the
                    degree d of the equations and the dimension r: proved,
                    proved except for the Weil classes of abelian sixfolds
                    of non-split Weil type for Q(sqrt(-3)) (d = 6, r = 6),
                    open (Weil classes of abelian r-folds over an imaginary
                    quadratic field, r >= 8), open (Weil classes of a CM
                    field of degree at least four), and the odd
                    dimensions, where there is nothing to prove.

  fig_vgcounts      the dimension of the space of Hodge classes of the very
                    general member, from thm:vgvandermonde(iii), against
                    the Hodge number h^{r/2,r/2}, on a logarithmic scale,
                    for fourteen complete intersections of degree 2, 3, 4
                    and 6.  The numbers are
                    computed here from the formulas of the theorem and from
                    the Hodge numbers of code/diagonal_ci.py.

  fig_roadmap       the five parts of the paper, what each proves, and how
                    they lead to the main theorem and to the closure
                    theorem.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round41.py     (from the figures directory)
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.join(os.path.dirname(HERE), "code")
for p in (HERE, CODE):
    if p not in sys.path:
        sys.path.insert(0, p)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402
from diagonal_ci import hodge_middle_ci             # noqa: E402
from cyclic_monodromy import vg_count_formula       # noqa: E402

make_round19.GEN = "make_round41.py"


# ------------------------------------------------------------ the numbers
def vg_count(d, N, r):
    """thm:vgvandermonde(iii)"""
    return vg_count_formula(d, N, r)


def hmid(d, N, r):
    return hodge_middle_ci(d, N, N - r)[r // 2]


COUNTS = [  # (d, N, r, name)
    (2, 4, 2, r"two quadrics in $\PP^{4}$"),
    (2, 6, 4, r"two quadrics in $\PP^{6}$"),
    (2, 8, 4, r"four quadrics in $\PP^{8}$"),
    (2, 9, 6, r"three quadrics in $\PP^{9}$"),
    (3, 5, 4, r"the Fermat cubic in $\PP^{5}$"),
    (3, 7, 6, r"the Fermat cubic in $\PP^{7}$"),
    (3, 6, 4, r"two cubics in $\PP^{6}$"),
    (3, 7, 4, r"three cubics in $\PP^{7}$"),
    (4, 5, 4, r"the Fermat quartic in $\PP^{5}$"),
    (4, 7, 6, r"the Fermat quartic in $\PP^{7}$"),
    (4, 6, 4, r"two quartics in $\PP^{6}$"),
    (4, 7, 4, r"three quartics in $\PP^{7}$"),
    (6, 5, 4, r"the Fermat sextic in $\PP^{5}$"),
    (6, 6, 4, r"two sextics in $\PP^{6}$"),
]
EXPECT = {(2, 4, 2): (6, 6), (2, 6, 4): (8, 8), (2, 8, 4): (94, 166),
          (2, 9, 6): (47, 62), (3, 5, 4): (21, 21), (3, 7, 6): (71, 71),
          (3, 6, 4): (141, 267), (3, 7, 4): (561, 2295),
          (4, 5, 4): (142, 142), (4, 7, 6): (1108, 1108),
          (4, 6, 4): (988, 2584), (4, 7, 4): (3950, 29872),
          (6, 5, 4): (1752, 1752), (6, 6, 4): (12258, 48588)}
for d, N, r, _ in COUNTS:
    assert (vg_count(d, N, r), hmid(d, N, r)) == EXPECT[(d, N, r)], (d, N, r)
# the Lie algebra of the chain has the dimension of sp: g(2g+1)
assert [g * (2 * g + 1) for g in range(1, 5)] == [3, 10, 21, 36]


# ------------------------------------------------------------ fig_vgmonodromy
def fig_vgmonodromy():
    F = Plate("fig_vgmonodromy",
              "Monodromy of the curves D_a and the Hodge classes of the very "
              "general member (lem:vgmonodromy, thm:vgvandermonde).")
    arrow = "PInk,line width=0.6pt," + TIP
    ytop, ybot = 4.62, -0.50

    # ---------------------------------------------------- panel A: the curve
    F.rect(0.05, ybot, 5.05, ytop, fill="WTeal", bg=True, rc=3)
    F.text(0.25, 4.32, r"\textbf{the curve $D_{a}$, $a$ of order two}",
           anchor="west", onbg=True)
    F.text(0.25, 3.86, r"$y^{2}=\prod_{i\in S}(t-\lambda_{i})$, "
           r"$|S|=2g+2=6$", anchor="west", font=SN, onbg=True)
    yl = 2.30
    xs = [0.62 + 0.75 * k for k in range(6)]
    F.seg([(0.30, yl), (4.80, yl)], "PSlate,line width=0.6pt")
    for k in range(5):
        cx, hw, hh = (xs[k] + xs[k + 1]) / 2, 0.43, 0.24
        col = "PTeal" if k % 2 == 0 else "PBlue"
        F.ink(r"  \draw[%s,line width=0.8pt] (%.4f,%.4f) ellipse "
              r"(%.4fcm and %.4fcm);" % (col, cx, yl, hw, hh))
        F.text(cx, yl + hh + 0.07, r"$c_{%d}$" % (k + 1), anchor="south",
               color=col, font=SN, onbg=True)
    for k, x in enumerate(xs):
        F.disc(x, yl, 1.7, "PClay", ring="white", lw=0.4)
        F.text(x, yl - 0.31, r"$\lambda_{s_{%d}}$" % (k + 1),
               anchor="north", color="PClay!85!black", font=SN, onbg=True)
    # the full twist of lambda_{s_3}, lambda_{s_4}: sigma^2 as a braid
    xa, xb = xs[2], xs[3]
    y0, y1, y2 = 1.54, 1.22, 0.90

    def strand(p, q, over, col):
        c1 = (p[0], (p[1] + q[1]) / 2)
        c2 = (q[0], (p[1] + q[1]) / 2)
        if over:
            F.bez(p, c1, c2, q, "white,line width=2.6pt")
        F.bez(p, c1, c2, q, "%s,line width=0.85pt" % col)

    strand((xb, y0), (xa, y1), False, "PClay")
    strand((xa, y0), (xb, y1), True, "PIndigo")
    strand((xb, y1), (xa, y2), False, "PIndigo")
    strand((xa, y1), (xb, y2), True, "PClay")
    F.text(xb + 0.22, y1, r"full twist: $T_{3}^{2}$", anchor="west",
           color="PMag", font=SN, onbg=True)
    F.text(0.25, 0.30, r"$T_{k}(z)=z+\langle z,c_{k}\rangle c_{k}$",
           anchor="west", font=SN, onbg=True)
    F.text(0.25, -0.12, r"$\langle c_{k},c_{k\pm1}\rangle=\pm1$, "
           r"the others $0$", anchor="west", font=SN, onbg=True)

    # ---------------------------------------------------- panel B: the chain
    F.rect(5.45, ybot, 10.30, ytop, fill="WBlue", bg=True, rc=3)
    F.text(5.65, 4.32, r"\textbf{the chain generates $\mathfrak{sp}(V_{a})$}",
           anchor="west", onbg=True)
    yc = 3.45
    cx = [5.95 + 0.98 * k for k in range(5)]
    for k in range(4):
        F.seg([(cx[k] + 0.09, yc), (cx[k + 1] - 0.09, yc)],
              "PSlate,line width=0.7pt")
        F.text((cx[k] + cx[k + 1]) / 2, yc + 0.08, r"$\pm1$", anchor="south",
               color="PSlate", font=SN, onbg=True)
    for k, x in enumerate(cx):
        col = "PTeal" if k % 2 == 0 else "PBlue"
        F.disc(x, yc, 2.6, col, ring="white", lw=0.5)
        F.text(x, yc - 0.13, r"$c_{%d}$" % (k + 1), anchor="north",
               color=col, font=SN, onbg=True)
    rows = [r"$N_{k}=\langle\cdot,c_{k}\rangle c_{k}=\tfrac12c_{k}^{2}$ "
            r"in $\mathrm{Sym}^{2}V_{a}$",
            r"$[c_{k}^{2},c_{k+1}^{2}]=\pm4\,c_{k}c_{k+1}$",
            r"$c_{i}c_{k+1}=\pm\tfrac12[c_{i}c_{k},c_{k+1}^{2}]$ for $i<k$",
            r"so the $c_{i}c_{j}$ span $\mathrm{Sym}^{2}V_{a}=\mathfrak{sp}"
            r"(V_{a})$,",
            r"of dimension $g(2g+1)$;",
            r"a power of each $T_{k}^{2}$ lies in $\Pi'$, so",
            r"$\overline{\Pi'}\supset\mathrm{Sp}(V_{a})$ (Zariski closure)"]
    for k, s in enumerate(rows):
        F.text(5.65, 2.62 - 0.48 * k, s, anchor="west", font=SN, onbg=True,
               color="PIndigo" if k >= len(rows) - 2 else "PInk")

    # ---------------------------------------------------- panel C: classes
    F.rect(10.70, 2.60, 15.70, ytop, fill="WTeal", bg=True, rc=3)
    rows2 = [r"\textbf{order two}",
             r"$\mathrm{Sp}(V_{a})$-invariants of $\bigwedge^{r}V_{a}$:",
             r"the multiples of $\omega_{a}^{r/2}$, the image",
             r"of $\theta_{a}^{r/2}$; so $x_{[a]}$ is algebraic"]
    for k, s in enumerate(rows2):
        F.text(10.90, 4.32 - 0.47 * k, s, anchor="west",
               font=FN if k == 0 else SN, onbg=True,
               color="PTeal" if k == 0 else "PInk")
    F.rect(10.70, ybot, 15.70, 2.40, fill="WOchre", bg=True, rc=3)
    rows3 = [r"\textbf{order $m=3,4,6$}",
             r"$G_{a}^{0}\supseteq\mathrm{SL}(V_{a})$ by collisions;",
             r"a class only if $r=\dim V_{a}$, $p_{a}=r/2$:",
             r"Weil type for $\QQ(\zeta_{m})$; if $\delta$ is trivial",
             r"($m=6$: $c_{3}$ even), Markman for $r\le6$"]
    for k, s in enumerate(rows3):
        F.text(10.90, 2.10 - 0.47 * k, s, anchor="west",
               font=FN if k == 0 else SN, onbg=True,
               color="POchre!85!black" if k == 0 else "PInk")
    F.text(10.90, ybot + 0.24, r"HC: $d=2$; $d\le4$, $r\le6$; $d=6$, "
           r"$r\le4$", anchor="west", color="PGrass", font=SN, onbg=True)

    # arrows between the panels
    F.seg([(5.10, 2.45), (5.40, 2.45)], arrow)
    F.seg([(10.35, 3.60), (10.65, 3.60)], arrow)
    F.seg([(10.35, 1.40), (10.65, 1.40)], arrow)
    F.write()
    return F.name


# ------------------------------------------------------------ fig_vgscope
def vg_status(d, r):
    if r % 2:
        return "odd"
    if r == 2 or d == 2 or (d in (3, 4) and r <= 6) or (d == 6 and r <= 4):
        return "P"
    if d == 6 and r == 6:
        return "A"
    if d in (3, 4, 6):
        return "W"
    return "Z"


def fig_vgscope():
    F = Plate("fig_vgscope",
              "The Hodge conjecture for the very general complete "
              "intersection X_{d,r}(lambda), every N (thm:vgvandermonde, "
              "rem:vandermonde).")
    ds = list(range(2, 9))
    rs = list(range(2, 11))
    CW, CH, GAP = 0.86, 0.46, 0.05
    x0, y0 = 1.10, 0.0

    def box(d, r):
        X = x0 + (d - 2) * CW
        Y = y0 + (r - 2) * CH
        return X, Y, X + CW - GAP, Y + CH - GAP

    fills = {"P": "PGrass!38!white", "A": "WTeal", "W": "WClay",
             "Z": "WClay", "odd": "WSlate"}
    for d in ds:
        for r in rs:
            k = vg_status(d, r)
            a, b, c, e = box(d, r)
            F.rect(a, b, c, e, fill=fills[k], bg=True)
            if k == "A":
                F.hatch(a, b, c, e, "PTeal!70", step=0.10, lw=0.45)
            if k == "Z":
                F.hatch(a, b, c, e, "PClay!55", step=0.10, lw=0.45)
    # axes
    F.seg([(x0 - 0.10, y0 - 0.10), (x0 + 7 * CW, y0 - 0.10)],
          "PInk,line width=0.5pt")
    F.seg([(x0 - 0.10, y0 - 0.10), (x0 - 0.10, y0 + 9 * CH)],
          "PInk,line width=0.5pt")
    for d in ds:
        a, b, c, e = box(d, 2)
        F.text((a + c) / 2, y0 - 0.18, "$%d$" % d, anchor="north", font=SN)
    for r in rs:
        a, b, c, e = box(2, r)
        F.text(x0 - 0.18, (b + e) / 2, "$%d$" % r, anchor="east", font=SN)
    F.text(x0 + 3.5 * CW, y0 - 0.62, r"$d$, the degree of the equations",
           anchor="north")
    F.text(x0 - 0.78, y0 + 4.5 * CH, r"$r=\dim X$", anchor="south",
           extra="rotate=90")
    # legend
    lx, ly, s = x0 + 7 * CW + 0.55, y0 + 9 * CH - 0.25, 0.26
    entries = [
        ("P", r"proved for every $N$: the theorem of Lefschetz for $r=2$,"
              r"\\ and the very general theorem for $d=2$, for $d=3,4$"
              r"\\ with $r\le6$ and for $d=6$ with $r\le4$"),
        ("A", r"proved except for the Weil classes of abelian sixfolds"
              r"\\ of non-split Weil type for $\QQ(\sqrt{-3})$"),
        ("W", r"open: Weil classes of abelian $r$-folds over $\QQ(i)$ or"
              r"\\ $\QQ(\sqrt{-3})$, from dimension $8$ on"),
        ("Z", r"open for $N$ large: Weil classes of $\QQ(\zeta_{e})$, "
              r"$\varphi(e)\ge4$,\\ the case $\mathrm{P2}_{\mathrm{split}}$ "
              r"of the paper"),
        ("odd", r"$r$ odd: no Hodge classes of degree $r$, nothing to "
                r"prove"),
    ]
    for k, t in entries:
        F.rect(lx, ly - s / 2, lx + s, ly + s / 2, fill=fills[k],
               draw="PSlate!70", lw=0.35)
        if k == "A":
            F.hatch(lx, ly - s / 2, lx + s, ly + s / 2, "PTeal!70",
                    step=0.08, lw=0.4, bg=False)
        if k == "Z":
            F.hatch(lx, ly - s / 2, lx + s, ly + s / 2, "PClay!55",
                    step=0.08, lw=0.4, bg=False)
        F.text(lx + s + 0.14, ly, t, anchor="west", font=SN,
               extra="align=left")
        ly -= 0.86
    F.write()
    return F.name


# ------------------------------------------------------------ fig_vgcounts
CCOL = {2: "PTeal", 3: "PBlue", 4: "POchre", 6: "PMag"}


def fig_vgcounts():
    F = Plate("fig_vgcounts",
              "Hodge classes of degree r on the very general member against "
              "h^{r/2,r/2} (thm:vgvandermonde(iii)).")
    xa, W, RH, E = 5.60, 8.00, 0.46, 5
    n = len(COUNTS)

    def X(v):
        return xa + W * math.log10(v) / E

    def Y(i):
        return (n - 1 - i) * RH

    # grid and axis
    for e in range(E + 1):
        F.seg([(X(10 ** e), -0.35), (X(10 ** e), Y(0) + 0.30)],
              "PRule,line width=0.35pt,dash pattern=on 1.4pt off 1.6pt")
        F.text(X(10 ** e), -0.42, r"$10^{%d}$" % e, anchor="north", font=SN)
    F.seg([(xa, -0.35), (X(10 ** E) + 0.10, -0.35)], "PInk,line width=0.5pt")
    for i, (d, N, r, name) in enumerate(COUNTS):
        c, h = vg_count(d, N, r), hmid(d, N, r)
        y = Y(i)
        F.rect(xa, y - 0.14, X(h), y + 0.14, fill="PRule!55!white")
        F.rect(xa, y - 0.08, X(c), y + 0.08, fill=CCOL[d])
        F.text(xa - 0.12, y, r"%s, $r=%d$" % (name, r), anchor="east",
               font=SN)
        tag = (r"$%d=h^{%d,%d}$" % (c, r // 2, r // 2) if c == h
               else r"$%d$ of $%d$" % (c, h))
        F.text(X(10 ** E) + 0.25, y, tag, anchor="west", font=SN,
               color="PGrass" if c == h else "PInk")
    # key
    ky = -1.20
    for k, d in enumerate((2, 3, 4, 6)):
        kx = xa + 1.55 * k
        F.rect(kx, ky - 0.08, kx + 0.40, ky + 0.08, fill=CCOL[d])
        F.text(kx + 0.50, ky, r"$d=%d$" % d, anchor="west", font=SN)
    F.text(xa - 0.12, ky, r"Hodge classes of the very general member:",
           anchor="east", font=SN)
    F.rect(xa, ky - 0.62, xa + 0.40, ky - 0.34, fill="PRule!55!white")
    F.text(xa + 0.50, ky - 0.48, r"$h^{r/2,r/2}(X)$, the classes of type "
           r"$(r/2,r/2)$", anchor="west", font=SN)
    F.write()
    return F.name


# ------------------------------------------------------------ fig_roadmap
def fig_roadmap():
    F = Plate("fig_roadmap",
              "The five parts of the paper and the two theorems they lead to.")
    arrow = "PInk,line width=0.6pt," + TIP
    parts = [
        ("I", "Weil classes and the obstructions", "WSlate", "PSlate",
         r"Weil classes in coordinates; classical constructions miss them"),
        ("II", "Base points and the algebraic locus", "WTeal", "PTeal",
         r"base points in every family, a dense orbit, closed strata"),
        ("III", "Semiregularity and secant objects", "WBlue", "PBlue",
         r"the pure criterion fails; the polarised one is one number"),
        ("IV", "Weil classes of CM fields", "WOchre", "POchre",
         r"CM base points, the main theorem, the quartic criterion"),
        ("V", "Beyond the Weil classes", "WClay", "PClay",
         r"(F3$'$) on new classes, the Mumford square, every family"),
    ]
    BH, PITCH, xl, xr = 0.60, 0.74, 0.40, 15.60
    ytop = 1.55 + 5 * PITCH
    for k, (num, title, fill, ink, line) in enumerate(parts):
        yc = ytop - (k + 0.5) * PITCH
        F.rect(xl, yc - BH / 2, xr, yc + BH / 2, fill=fill, bg=True, rc=3)
        F.text(xl + 0.14, yc, r"\textbf{%s}" % num, anchor="west",
               color=ink, onbg=True)
        F.text(xl + 0.72, yc, title, anchor="west", font=SN, color=ink,
               onbg=True)
        F.text(6.85, yc, line, anchor="west", font=SN, onbg=True)
    # the two theorems
    mx0, mx1 = 0.0, 7.55
    F.rect(mx0, 0.05, mx1, 1.05, fill="PGrass!22!white", draw="PGrass",
           lw=0.6, rc=3, bg=True)
    F.text(mx0 + 0.55, 0.78, r"\textbf{Main theorem}", anchor="west",
           color="PGrass", onbg=True)
    F.text(mx0 + 0.55, 0.33, r"dense, with an explicit CM point; all or "
           r"meagre", anchor="west", font=SN, onbg=True)
    cx0, cx1 = 8.05, 15.60
    F.rect(cx0, 0.05, cx1, 1.05, fill="WSlate", draw="PSlate", lw=0.6, rc=3,
           bg=True)
    F.text(cx0 + 0.15, 0.78, r"\textbf{Closure theorem}", anchor="west",
           color="PSlate", onbg=True)
    F.text(cx0 + 0.15, 0.33, r"$\mathrm{HC}\iff$ (F2) and (F3$'$); both "
           r"are open", anchor="west", font=SN, onbg=True)
    # parts I to IV lead to the main theorem, all five to the closure
    yI = ytop - 0.5 * PITCH
    yIV = ytop - 3.5 * PITCH
    F.seg([(0.20, yI), (0.20, 1.11)], arrow)
    for k in range(4):
        yc = ytop - (k + 0.5) * PITCH
        F.seg([(0.20, yc), (xl - 0.03, yc)], "PInk,line width=0.6pt")
    yV = ytop - 4.5 * PITCH
    F.seg([(11.80, yV - BH / 2 - 0.04), (11.80, 1.11)], arrow)
    del yIV
    F.write()
    return F.name


# ================================================================== main
ALL = ["vgmonodromy", "vgscope", "vgcounts", "roadmap"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
