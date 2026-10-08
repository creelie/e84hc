#!/usr/bin/env python3
"""
make_round43.py

The figure of round 43.

  fig_efourthree    thm:efourthreelevels.  Left: the pieces L_zeta at three
                    consecutive shifts, one parity at s - 1 and the other
                    split between T at s and B at s - 2; a block H^3(W, V)
                    between pieces differing in three coordinates meets a
                    component of Ext degree two only in a group H^5(c, e)
                    with c in T and e in B.  Middle: the budget, 40960
                    classes against at most 30720 targets by counting and
                    18432 by the least eigenvalue, against the 104 that the
                    polarised criterion allows.  Right: the eigenvalues of
                    the Cayley graph of the targets with their
                    multiplicities, recomputed here from the dimensions of
                    the groups H^5 (code/convolutions_efour.py, part (I)).

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round43.py     (from the figures directory)
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.join(os.path.dirname(HERE), "code")
for p in (HERE, CODE):
    if p not in sys.path:
        sys.path.insert(0, p)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402
from convolutions_efour import h5                   # noqa: E402

make_round19.GEN = "make_round43.py"


# ------------------------------------------------------------ the numbers
def spectrum():
    """eigenvalue -> multiplicity for the Cayley graph of the targets"""
    G0 = [g for g in itertools.product(range(4), repeat=4)
          if sum(g) % 4 == 0]
    zero = (0, 0, 0, 0)
    w = {g: h5(zero, g) for g in G0 if g != zero}
    RE = [1, 0, -1, 0]
    mult = {}
    seen = set()
    for m in itertools.product(range(4), repeat=4):
        key = min(tuple((x + c) % 4 for x in m) for c in range(4))
        if key in seen:
            continue
        seen.add(key)
        lam = sum(v * RE[sum(a * b for a, b in zip(m, g)) % 4]
                  for g, v in w.items())
        mult[lam] = mult.get(lam, 0) + 1
    return mult, sum(w.values())


SPEC, DEG = spectrum()
LMIN = min(SPEC)
CUT = 64 * (DEG - LMIN) // 4
assert DEG == 960 and LMIN == -192 and CUT == 18432
assert sum(SPEC.values()) == 64
TOTAL, COUNTED = 64 * 640, 32 * DEG
assert TOTAL - CUT == 22528 and TOTAL - COUNTED == 10240


# ------------------------------------------------------------ fig_efourthree
def fig_efourthree():
    F = Plate("fig_efourthree",
              "Three consecutive shifts on E_0^8: blocks, targets, budget "
              "and spectrum (thm:efourthreelevels).")
    arrow = "PInk,line width=0.6pt," + TIP
    ytop, ybot = 4.62, -0.50

    # ------------------------------------------------ panel A: the shifts
    F.rect(0.05, ybot, 4.95, ytop, fill="WTeal", bg=True, rc=3)
    F.text(0.25, 4.32, r"\textbf{three consecutive shifts}", anchor="west",
           onbg=True)
    ys = {0: 3.50, -1: 2.70, -2: 1.90}
    for k, y in ys.items():
        lab = "s" if k == 0 else "s%+d" % k
        F.text(0.62, y, r"$%s$" % lab, anchor="east", color="PSlate",
               font=SN, onbg=True)
    top = [0.95 + 0.26 * j for j in range(5)]
    mid = [1.95 + 0.26 * j for j in range(5)]
    bot = [3.15 + 0.26 * j for j in range(5)]
    for xs, k, col in ((top, 0, "PBlue"), (mid, -1, "PTeal"),
                       (bot, -2, "PBlue")):
        for x in xs:
            F.disc(x, ys[k], 1.7, col, ring="white", lw=0.35)
    F.text(top[0] - 0.02, ys[0] + 0.14, r"$T$", anchor="south",
           color="PBlue", font=SN, onbg=True)
    F.text(bot[-1] + 0.02, ys[-2] - 0.14, r"$B$", anchor="north",
           color="PBlue", font=SN, onbg=True)
    W, V, E = (top[3], ys[0]), (mid[2], ys[-1]), (bot[1], ys[-2])
    # the block H^3(W, V)
    F.seg([(W[0] + 0.07, W[1] - 0.08), (V[0] - 0.07, V[1] + 0.08)],
          "PTeal,line width=0.8pt," + TIP)
    F.text((W[0] + V[0]) / 2 - 0.32, (W[1] + V[1]) / 2 - 0.02,
           r"$\mathcal{H}^{3}(W,V)$", anchor="east", color="PTeal",
           font=SN, onbg=True)
    # a component of Ext degree two from V to e
    F.seg([(V[0] + 0.07, V[1] - 0.08), (E[0] - 0.07, E[1] + 0.08)],
          "PIndigo,line width=0.8pt," + TIP)
    F.text((V[0] + E[0]) / 2 - 0.32, (V[1] + E[1]) / 2 - 0.06,
           r"$\mathcal{H}^{2}(V,e)$", anchor="east", color="PIndigo",
           font=SN, onbg=True)
    # the target H^5(W, e)
    F.bez((W[0] + 0.10, W[1] + 0.02), (W[0] + 1.55, W[1] + 0.10),
          (E[0] + 0.85, E[1] + 1.00), (E[0] + 0.07, E[1] + 0.09),
          "PMag,line width=0.8pt,dash pattern=on 2.2pt off 1.2pt," + TIP)
    F.text(3.30, 3.74, r"$\mathcal{H}^{5}(W,e)$", anchor="south west",
           color="PMag", font=SN, onbg=True)
    F.text(W[0], W[1] + 0.10, r"$W$", anchor="south", font=SN, onbg=True)
    F.text(V[0] + 0.07, V[1] + 0.13, r"$V$", anchor="south west", font=SN,
           onbg=True)
    F.text(E[0], E[1] - 0.10, r"$e$", anchor="north", font=SN, onbg=True)
    rows = [r"a block meets one component of",
            r"$\Ext$ degree two, landing in",
            r"$\mathcal{H}^{5}(c,e)$, $c\in T$, $e\in B$; runs",
            r"through the multiples drop $\ge4$"]
    for k, s in enumerate(rows):
        F.text(0.25, 1.15 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel B: the budget
    F.rect(5.30, ybot, 9.95, ytop, fill="WBlue", bg=True, rc=3)
    F.text(5.50, 4.32, r"\textbf{the budget}", anchor="west", onbg=True)
    x0, wmax = 5.55, 4.10
    bars = [(TOTAL, "PTeal", r"$40960$ classes $\mathcal{H}^{3}$"),
            (COUNTED, "POchre", r"targets $\le32\cdot960=30720$"),
            (CUT, "PMag", r"targets $\le16\cdot1152=18432$"),
            (TOTAL - CUT, "PGrass", r"$\dim\Ext^{2}\ge22528$")]
    for k, (val, col, lab) in enumerate(bars):
        y = 3.42 - 0.68 * k
        F.rect(x0, y - 0.13, x0 + wmax * val / TOTAL, y + 0.13,
               fill=col + "!55!white", bg=True)
        F.text(x0, y + 0.17, lab, anchor="south west", font=SN, onbg=True)
    yc = 3.42 - 0.68 * 4
    F.seg([(x0, yc - 0.13), (x0, yc + 0.13)], "PClay,line width=1.2pt")
    F.text(x0 + 0.10, yc, r"$104$ allowed by the criterion", anchor="west",
           color="PClay", font=SN, onbg=True)
    rows = [r"counting: $\min(|T|,|B|)\cdot960$;",
            r"eigenvalue: $16(960-\lambda)$"]
    for k, s in enumerate(rows):
        F.text(5.50, 0.30 - 0.42 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel C: spectrum
    F.rect(10.30, ybot, 15.70, ytop, fill="WOchre", bg=True, rc=3)
    F.text(10.50, 4.32, r"\textbf{eigenvalues of the targets}",
           anchor="west", onbg=True)
    ax0, ax1, ay0, hmax = 11.05, 15.10, 1.30, 2.30
    lo, hi = -192, 960
    mmax = max(SPEC.values())

    def X(v):
        return ax0 + (ax1 - ax0) * (v - lo) / (hi - lo)

    F.seg([(ax0 - 0.15, ay0), (ax1 + 0.38, ay0)],
          "PSlate,line width=0.5pt," + TIP)
    F.seg([(X(0), ay0), (X(0), ay0 + hmax + 0.25)],
          "PSlate,line width=0.5pt," + TIP)
    for v in (-192, 384, 960):
        F.seg([(X(v), ay0), (X(v), ay0 - 0.06)], "PSlate,line width=0.5pt")
        F.text(X(v), ay0 - 0.12, r"$%d$" % v, anchor="north",
               color="PMag" if v == LMIN else "PSlate", font=SN, onbg=True)
    for m in (12, 24):
        y = ay0 + hmax * m / mmax
        F.seg([(X(0) - 0.06, y), (X(0), y)], "PSlate,line width=0.5pt")
        F.text(X(0) + 0.12, y, r"$%d$" % m, anchor="west", color="PSlate",
               font=SN, onbg=True)
    for v, m in sorted(SPEC.items()):
        y = ay0 + hmax * m / mmax
        col = "PMag" if v == LMIN else "PIndigo"
        F.seg([(X(v), ay0), (X(v), y)], col + ",line width=0.9pt")
        F.disc(X(v), y, 1.6, col, ring="white", lw=0.3)
    rows = [r"least $\lambda=-192$; the cut",
            r"$\zeta_{3}\zeta_{4}\in\{1,i\}$ weighs $18432$"]
    for k, s in enumerate(rows):
        F.text(10.50, 0.30 - 0.42 * k, s, anchor="west", font=SN, onbg=True)

    # arrows between the panels
    F.seg([(4.98, 2.45), (5.27, 2.45)], arrow)
    F.seg([(9.98, 2.45), (10.27, 2.45)], arrow)
    F.write()
    return F.name


# ================================================================== main
ALL = ["efourthree"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
