#!/usr/bin/env python3
"""
make_round44.py

The figure of round 44.

  fig_efourspread   lem:efourspread, lem:cayleycut, thm:efourspreadtwo,
                    thm:efourspreadthree, prop:efourgap, cor:efourfive,
                    prop:efourcupkernel.  Left: one parity at two values
                    two apart; a piece is joined to the thirteen pieces
                    whose ratio moves every coordinate, one of them by -1
                    (weights 256 once and 64 twelve times), and the groups
                    H^4 of the edges crossing between the values survive,
                    at least 1024 by the stabiliser bound.  Middle: the
                    four kinds of arrangement within five consecutive
                    values and their bounds (40960, 1024, 67584, 640).
                    Right: the diagonal at n = 4, 3668 classes, cup rank at
                    most 3184, a kernel of at least 484 against the 104
                    that the criterion allows.  The numbers are recomputed
                    here from code/efour_blocks.py.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round44.py     (from the figures directory)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.join(os.path.dirname(HERE), "code")
for p in (HERE, CODE):
    if p not in sys.path:
        sys.path.insert(0, p)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402
from efour_blocks import R4, Dr, h_dim, NZ, flip    # noqa: E402

make_round19.GEN = "make_round44.py"


# ------------------------------------------------------------ the numbers
WEIGHTS = sorted((Dr(r) for r in R4), reverse=True)
STAR = sum(WEIGHTS)
SPREAD3 = sum(h_dim(r, 5) for r in NZ if flip(r) == 1)
assert WEIGHTS == [256] + [64] * 12 and STAR == 1024 and SPREAD3 == 1072
BOUNDS = [64 * 640, STAR, 64 * SPREAD3 - 128 * 8, 640]
assert BOUNDS == [40960, 1024, 67584, 640]
DIAG, CUP = 131 * 28, 3584 - 400
KER = DIAG - CUP
assert DIAG == 3668 and KER == 484 and KER - 104 == 380


# ------------------------------------------------------------ fig_efourspread
def fig_efourspread():
    F = Plate("fig_efourspread",
              "Shift arrangements on E_0^8 within five values, the groups "
              "of spread two and the diagonal at n = 4 (cor:efourfive).")
    arrow = "PInk,line width=0.6pt," + TIP
    ytop, ybot = 4.62, -1.30

    # ------------------------------------------------ panel A: spread two
    F.rect(0.05, ybot, 4.95, ytop, fill="WTeal", bg=True, rc=3)
    F.text(0.25, 4.32, r"\textbf{one parity at two values}", anchor="west",
           onbg=True)
    yt, yb = 3.30, 1.20
    F.text(0.90, yt, r"$s$", anchor="east", color="PSlate", font=SN,
           onbg=True)
    F.text(0.90, yb, r"$s-2$", anchor="east", color="PSlate", font=SN,
           onbg=True)
    xs_top = [1.15 + 0.30 * j for j in range(13)]
    xs_bot = [1.15 + 0.30 * j for j in range(13)]
    c = (xs_top[6], yt)
    # the thirteen edges of c, the heavy one in magenta
    for j, x in enumerate(xs_bot):
        heavy = j == 6
        col = "PMag" if heavy else "PIndigo"
        lw = 1.1 if heavy else 0.45
        F.seg([(c[0], c[1] - 0.09), (x, yb + 0.09)],
              "%s,line width=%.2fpt" % (col, lw))
    for x in xs_top:
        F.disc(x, yt, 1.7, "PBlue" if x != c[0] else "PMag", ring="white",
               lw=0.35)
    for x in xs_bot:
        F.disc(x, yb, 1.7, "PBlue", ring="white", lw=0.35)
    F.text(c[0], yt + 0.13, r"$c$", anchor="south", font=SN, onbg=True)
    rows = [r"thirteen ratios move all",
            r"four coordinates, one by $-1$:",
            r"weight $256$ (magenta) or $64$;",
            r"a cut weighs $\ge1024$"]
    for k, s in enumerate(rows):
        F.text(0.25, 0.55 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel B: five values
    F.rect(5.30, ybot, 9.95, ytop, fill="WBlue", bg=True, rc=3)
    F.text(5.50, 4.32, r"\textbf{within five values}", anchor="west",
           onbg=True)
    lev = {k: 3.40 - 0.40 * k for k in range(5)}
    for k, y in lev.items():
        F.text(5.50, y, r"$s$" if k == 0 else r"$s-%d$" % k, anchor="west",
               color="PSlate", font=SN, onbg=True)
    cols = [6.60, 7.45, 8.30, 9.15]
    kinds = [((0,), (1,)), ((0, 2), (1,)), ((0,), (3,)), ((0, 4), (1,))]
    for x, (A, B) in zip(cols, kinds):
        F.seg([(x, lev[0] + 0.12), (x, lev[4] - 0.12)],
              "PSlate!45!white,line width=0.4pt")
        for k in A:
            for dx in (-0.18, 0.0, 0.18):
                F.disc(x + dx, lev[k], 1.6, "PBlue", ring="white", lw=0.3)
        for k in B:
            for dx in (-0.18, 0.0, 0.18):
                F.disc(x + dx, lev[k], 1.6, "PTeal", ring="white", lw=0.3)
    for x, tag in zip(cols, ["(a)", "(b)", "(c)", "(d)"]):
        F.text(x, 3.64, tag, anchor="south", font=SN, onbg=True)
    for x, b in zip(cols, BOUNDS):
        F.text(x, 1.40, r"$%d$" % b, anchor="north", color="PGrass",
               font=SN, onbg=True)
    rows = [r"(a) adjacent shifts,",
            r"(b) one parity at two,",
            r"(c) three apart, (d) a gap;",
            r"green: $\dim\Ext^{2}\ge$"]
    for k, s in enumerate(rows):
        F.text(5.50, 0.55 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel C: the diagonal
    F.rect(10.30, ybot, 15.70, ytop, fill="WOchre", bg=True, rc=3)
    F.text(10.50, 4.32, r"\textbf{the diagonal at $n=4$}", anchor="west",
           onbg=True)
    x0, wmax = 10.55, 4.80
    bars = [(DIAG, "PTeal", r"$3668$ diagonal classes"),
            (CUP, "POchre", r"cup products: rank $\le3184$"),
            (KER, "PMag", r"kernel $\ge484$, every convolution"),
            (104, "PClay", r"$104$ allowed by the criterion")]
    for k, (val, col, lab) in enumerate(bars):
        y = 3.42 - 0.68 * k
        F.rect(x0, y - 0.13, x0 + wmax * val / DIAG, y + 0.13,
               fill=col + "!55!white", bg=True)
        F.text(x0, y + 0.17, lab, anchor="south west", font=SN, onbg=True)
    rows = [r"longer products must",
            r"remove at least $380$;",
            r"exactly $484$ for general",
            r"components"]
    for k, s in enumerate(rows):
        F.text(10.50, 0.55 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # arrows between the panels
    F.seg([(4.98, 2.45), (5.27, 2.45)], arrow)
    F.seg([(9.98, 2.45), (10.27, 2.45)], arrow)
    F.write()
    return F.name


# ================================================================== main
ALL = ["efourspread"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
