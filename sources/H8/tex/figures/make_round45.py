#!/usr/bin/env python3
"""
make_round45.py

The figure of round 45.

  fig_efoursix      lem:efourlonely, prop:efoursingle, prop:efourpairs,
                    cor:efoursix.  Left: the parities at single shifts s and
                    s - g, g odd and at least five; a term on a diagonal
                    class at a piece a runs through the three multiples and
                    no other piece, and its four nodes have pairwise
                    incongruent shifts modulo 4, so the multiples serve at
                    most one of the two shifts and the 64 * 28 = 1792
                    diagonal classes at the other survive.  Middle: the
                    interleaved shifts {s, s-4} and {s-1, s-5}; the groups
                    H^3 between adjacent shifts survive and form a cut of
                    the Cayley graph of the 28 ratios that move three
                    coordinates, at least 640.  Right: the four arrangements
                    left within six values by the results for five values and
                    their bounds (1792, 640, 640, 640).  The numbers are
                    recomputed here from code/efour_six.py.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round45.py     (from the figures directory)
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
from efour_six import S3                            # noqa: E402
from efour_blocks import Dr                         # noqa: E402

make_round19.GEN = "make_round45.py"


# ------------------------------------------------------------ the numbers
CUT = sum(Dr(r) for r in S3)
LONELY = 64 * 28
assert len(S3) == 28 and CUT == 640 and LONELY == 1792
BOUNDS = [LONELY, CUT, 640, 640]


# ------------------------------------------------------------ fig_efoursix
def fig_efoursix():
    F = Plate("fig_efoursix",
              "The diagonal at a lonely shift, interleaved shifts, and the "
              "arrangements within six values on E_0^8 (cor:efoursix).")
    arrow = "PInk,line width=0.6pt," + TIP
    ytop, ybot = 4.62, -1.30

    # ------------------------------------------------ panel A: lonely shift
    F.rect(0.05, ybot, 4.95, ytop, fill="WTeal", bg=True, rc=3)
    F.text(0.25, 4.32, r"\textbf{a lonely shift}", anchor="west", onbg=True)
    yt, yb = 3.45, 1.55
    F.text(0.85, yt, r"$s$", anchor="east", color="PSlate", font=SN,
           onbg=True)
    F.text(0.85, yb, r"$s-g$", anchor="east", color="PSlate", font=SN,
           onbg=True)
    xs = [1.25 + 0.26 * j for j in range(6)]
    for j, x in enumerate(xs):
        F.disc(x, yt, 1.7, "PMag" if j == 0 else "PBlue", ring="white",
               lw=0.35)
        F.disc(x, yb, 1.7, "PTeal", ring="white", lw=0.35)
    F.text(xs[0], yt + 0.16, r"$a$", anchor="south", font=SN, onbg=True)
    # the residues modulo 4: a, M_1, M_2, M_3 on four distinct positions
    cx, cy, rr = 3.55, 2.55, 0.55
    F.back("  \\draw[PSlate!55!white,line width=0.50pt] (%.4f,%.4f) circle "
           "(%.4f);" % (cx, cy, rr))
    names = [r"$a$", r"$M_{1}$", r"$M_{2}$", r"$M_{3}$"]
    cols = ["PMag", "POchre", "POchre", "POchre"]
    pts = []
    for k in range(4):
        ang = math.pi / 2 - k * math.pi / 2
        x, y = cx + rr * math.cos(ang), cy + rr * math.sin(ang)
        pts.append((x, y))
        F.disc(x, y, 2.1, cols[k], ring="white", lw=0.4)
    offs = [(0.0, 0.16, "south"), (0.16, 0.0, "west"),
            (0.0, -0.16, "north"), (-0.16, 0.0, "east")]
    for (x, y), nm, (dx, dy, an) in zip(pts, names, offs):
        F.text(x + dx, y + dy, nm, anchor=an, font=SN, onbg=True)
    F.text(cx, cy, r"mod $4$", font=SN, color="PSlate", onbg=True)
    rows = [r"a term at $a$ passes through",
            r"$M_{1},M_{2},M_{3}$ alone; each step",
            r"adds $1$ mod $4$; $g$ odd: one",
            r"shift keeps $64\cdot28=1792$"]
    for k, s in enumerate(rows):
        F.text(0.25, 0.55 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel B: interleaved
    F.rect(5.30, ybot, 9.95, ytop, fill="WBlue", bg=True, rc=3)
    F.text(5.50, 4.32, r"\textbf{interleaved shifts}", anchor="west",
           onbg=True)
    lev = {0: 3.55, 1: 3.05, 4: 1.75, 5: 1.25}
    for k, y in lev.items():
        F.text(5.50, y, r"$s$" if k == 0 else r"$s-%d$" % k, anchor="west",
               color="PSlate", font=SN, onbg=True)
    xa = [6.55 + 0.30 * j for j in range(4)]
    xb = [7.95 + 0.30 * j for j in range(4)]
    tags = {0: r"$A$", 1: r"$B$", 4: r"$A'$", 5: r"$B'$"}
    # the surviving groups H^3: A--B and A'--B'
    for (u, v) in ((0, 1), (4, 5)):
        for i in range(4):
            for j in range(4):
                if (i + j) % 2 == 0:
                    F.seg([(xa[i], lev[u] - 0.08), (xa[j] + 0.15, lev[v] + 0.08)],
                          "PMag,line width=0.35pt")
    for k, y in lev.items():
        col = "PBlue" if k in (0, 4) else "PTeal"
        xx = xa if k in (0, 4) else [x + 0.15 for x in xa]
        for x in xx:
            F.disc(x, y, 1.6, col, ring="white", lw=0.3)
        F.text(xx[-1] + 0.22, y, tags[k], anchor="west", font=SN,
               onbg=True)
    F.text(6.95, 2.40, r"groups $\mathcal{H}^{3}$ survive", anchor="west",
           color="PMag", font=SN, onbg=True)
    rows = [r"edges $A$--$B$, $A'$--$B'$: the",
            r"cut of $A\cup B'$ in the Cayley",
            r"graph of $28$ ratios that move",
            r"three coordinates: $\ge640$"]
    for k, s in enumerate(rows):
        F.text(5.50, 0.55 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # ------------------------------------------------ panel C: six values
    F.rect(10.30, ybot, 15.70, ytop, fill="WOchre", bg=True, rc=3)
    F.text(10.50, 4.32, r"\textbf{within six values}", anchor="west",
           onbg=True)
    lv = {k: 3.55 - 0.40 * k for k in range(6)}
    for k, y in lv.items():
        F.text(10.50, y, r"$s$" if k == 0 else r"$s-%d$" % k, anchor="west",
               color="PSlate", font=SN, onbg=True)
    cols6 = [11.75, 12.70, 13.65, 14.60]
    kinds = [((0,), (5,)), ((0, 4), (1, 5)), ((0,), (1, 5)), ((0, 4), (5,))]
    for x, (A, B) in zip(cols6, kinds):
        F.seg([(x, lv[0] + 0.12), (x, lv[5] - 0.12)],
              "PSlate!45!white,line width=0.4pt")
        for k in A:
            for dx in (-0.16, 0.0, 0.16):
                F.disc(x + dx, lv[k], 1.6, "PBlue", ring="white", lw=0.3)
        for k in B:
            for dx in (-0.16, 0.0, 0.16):
                F.disc(x + dx, lv[k], 1.6, "PTeal", ring="white", lw=0.3)
    for x, tag in zip(cols6, ["(a)", "(b)", "(c)", "(d)"]):
        F.text(x, 3.75, tag, anchor="south", font=SN, onbg=True)
    for x, b in zip(cols6, BOUNDS):
        F.text(x, 1.28, r"$%d$" % b, anchor="north", color="PGrass",
               font=SN, onbg=True)
    rows = [r"(a) single shifts, (b) interleaved,",
            r"(c), (d) a gap of four; all others",
            r"by the earlier results;",
            r"green: $\dim\Ext^{2}\ge$"]
    for k, s in enumerate(rows):
        F.text(10.50, 0.55 - 0.45 * k, s, anchor="west", font=SN, onbg=True)

    # arrows between the panels
    F.seg([(4.98, 2.45), (5.27, 2.45)], arrow)
    F.seg([(9.98, 2.45), (10.27, 2.45)], arrow)
    F.write()
    return F.name


# ================================================================== main
ALL = ["efoursix"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
