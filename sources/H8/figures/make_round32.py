#!/usr/bin/env python3
"""
make_round32.py

Two plates for the convolutions of line bundles (ssec:convolutions).

  fig_convolutions  prop:nothingenters and thm:esixdiagonal(i).  Left: the
                    pieces at their values phi (phi(L_zeta) = p for the 32
                    bundles L_zeta, phi(M_i) = t_i for the three multiples of
                    the polarisation), and a cycle made of the worst run
                    through the M_i (three steps up, of excess -1 each, and
                    one step down, of excess 2n - 1) closed by a step between
                    two L_zeta, of excess at least 1: its excess is at least
                    2n - 3 > 0, while a term reaching the diagonal needs a
                    cycle of excess 0.  Right: the one path that survives at
                    n = 3, M_2 -> M_3 -> L_zeta -> M_1 in the order of the
                    convolution, with the Ext degrees 0, 6, 0 of its steps,
                    the shifts they force, and the space H^6(M_2, M_1) of
                    dimension (t_2 - t_1)^6 where its value lies.

  fig_diagonalbudget  prop:cupkernel and thm:esixdiagonal(ii), (iii).  The
                    525 diagonal classes of degree two at n = 3 as a
                    waterfall: the cup products remove 276 of them (the
                    generic rank, computed), leaving 249 = 204 + 45; the
                    fourfold products of the surviving path remove at most
                    (t_2 - t_1)^6 of these, which is 1, 64 or at least 729
                    for the gaps 1, 2, >= 3; the criterion asks for 57.
                    Beside it the graphs Gamma_tau of prop:cupkernel on the
                    32 pieces, rows by zeta_1: for tau = (2,0,0) each row is
                    one component (4 in all), for tau = (1,1,0) the
                    components are the pairs zeta, zeta' differing in the
                    sign of zeta_3 (16 in all).  The counts are recomputed
                    here from the definitions of the edges.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round32.py [name ...]     (from the figures directory)
"""
import itertools
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402

make_round19.GEN = "make_round32.py"

DASHED = "dash pattern=on 2.4pt off 1.6pt"


def shorten(a, b, s0, s1=None):
    """The segment a b with s0 cm cut from its start and s1 from its end."""
    s1 = s0 if s1 is None else s1
    dx, dy = b[0] - a[0], b[1] - a[1]
    L = math.hypot(dx, dy)
    ux, uy = dx / L, dy / L
    return ((a[0] + s0 * ux, a[1] + s0 * uy), (b[0] - s1 * ux, b[1] - s1 * uy))


# ================================================================ the data
def pieces(n=3):
    """The zeta in mu_4^n with prod zeta = +-1, as exponents mod 4."""
    return [z for z in itertools.product(range(4), repeat=n)
            if sum(z) % 2 == 0]


def cup_components(tau, n=3):
    """The connected components of Gamma_tau (prop:cupkernel): a sign change
    of one coordinate outside the support of tau, or a multiplication by
    (i,i) or (-i,-i) of two coordinates when tau is 2 on the third."""
    P = pieces(n)
    idx = {z: k for k, z in enumerate(P)}
    parent = list(range(len(P)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for z in P:
        for j in range(n):
            if tau[j] == 0:
                w = list(z)
                w[j] = (w[j] + 2) % 4
                parent[find(idx[z])] = find(idx[tuple(w)])
        for j in range(n):
            if tau[j] == 2:
                a, b = [k for k in range(n) if k != j]
                for e in (1, 3):
                    w = list(z)
                    w[a] = (w[a] + e) % 4
                    w[b] = (w[b] + e) % 4
                    parent[find(idx[z])] = find(idx[tuple(w)])
    comps = {}
    for z in P:
        comps.setdefault(find(idx[z]), []).append(z)
    return list(comps.values())


def budget():
    """The numbers of the waterfall, checked against the paper."""
    P = pieces(3)
    assert len(P) == 32
    types = [t for t in itertools.product(range(3), repeat=3) if sum(t) == 2]
    dim = {t: math.prod((1, 2, 1)[k] for k in t) for t in types}
    assert sum(dim.values()) == 15
    D2 = (32 + 3) * 15
    kerL = sum(len(cup_components(t)) * dim[t] for t in types)
    comp = {t: len(cup_components(t)) for t in types}
    assert sorted(comp.values()) == [4, 4, 4, 16, 16, 16], comp
    assert (D2, kerL) == (525, 204)
    ker = kerL + 3 * 15
    assert ker == 249 and ker - 57 == 192 and D2 - 57 == 468
    assert 2 ** 6 < 192 <= 3 ** 6
    return D2, kerL, ker


# ========================================================== convolutions
def fig_convolutions():
    F = Plate("fig_convolutions",
              "The excess of the steps of a cycle of pieces "
              "(prop:nothingenters), and the one path whose products can act "
              "on the diagonal at n = 3 (thm:esixdiagonal).")
    sy = 0.62                       # cm per unit of phi

    def Y(phi):
        return phi * sy
    p, t = 0, (2, 4, 6)
    rL, rM = 2.6, 3.4              # dot radii, pt
    cut = 0.13                      # arrow clearance at a dot, cm
    arrow = "PInk,line width=0.6pt," + TIP

    # -------------------------------------------------------------- (a)
    ax = 0.0
    F.seg([(ax, Y(-1.2)), (ax, Y(7.6))], "PSlate,line width=0.5pt," + TIP)
    F.text(ax, Y(7.6) + 0.10, r"$\phi$", anchor="south", color="PSlate")
    for v, name in ((p, "p"), (t[0], "t_{1}"), (t[1], "t_{2}"),
                    (t[2], "t_{3}")):
        F.seg([(ax - 0.08, Y(v)), (ax + 0.08, Y(v))],
              "PSlate,line width=0.45pt")
        F.text(ax - 0.16, Y(v), r"$%s$" % name, anchor="east",
               color="PSlate")
    xs = [0.75 + 0.62 * k for k in range(8)]
    for x in xs:
        F.disc(x, Y(p), rL, "PBlue", ring="white", lw=0.4)
    La, Lb = (xs[0], Y(p)), (xs[6], Y(p))
    M = [(1.55, Y(t[0])), (2.75, Y(t[1])), (3.95, Y(t[2]))]
    for q in M:
        F.disc(q[0], q[1], rM, "PClay", ring="white", lw=0.4)
    run = [La] + M + [Lb]
    for a, b in zip(run, run[1:]):
        F.seg(list(shorten(a, b, cut)), arrow)
    # the step between two L_zeta, below the row
    F.bez((Lb[0] - 0.06, Lb[1] - 0.12), (Lb[0] - 0.9, Lb[1] - 1.05),
          (La[0] + 0.9, La[1] - 1.05), (La[0] + 0.06, La[1] - 0.12), arrow)
    # names of the pieces
    F.text(xs[-1] + 0.20, Y(p), r"$L_{\zeta}$", anchor="west",
           color="PBlue")
    for k, q in enumerate(M):
        F.text(q[0] - 0.17, q[1] + 0.05, r"$M_{%d}$" % (k + 1),
               anchor="south east", color="PClay!85!black")
    # the excess of each step
    for a, b in zip(run[:3], run[1:4]):
        mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
        F.text(mx + 0.16, my - 0.10, r"$-1$", anchor="north west", font=SN)
    mx, my = (M[2][0] + Lb[0]) / 2, (M[2][1] + Lb[1]) / 2
    F.text(mx + 0.18, my + 0.10, r"$2n-1$", anchor="south west", font=SN)
    F.text((La[0] + Lb[0]) / 2, La[1] - 0.92, r"$\ge1$", anchor="north",
           font=SN)
    # the reading
    x0, y0 = ax - 0.35, Y(-1.2) - 1.05
    lines = [
        r"excess of a step of degree one: $-1$ up ($\Ext^{0}$),",
        r"$2n-1$ down ($\Ext^{2n}$), at least $1$ from $L_{\zeta}$ to "
        r"$L_{\zeta'}$",
        r"this cycle: $3\cdot(-1)+(2n-1)+1=2n-3>0$;",
        r"reaching $H^{2}(\cO_{A})$ needs a cycle of excess $0$",
    ]
    for k, s in enumerate(lines):
        F.text(x0, y0 - 0.47 * k, s, anchor="north west", font=SN)
    F.text(ax - 0.35, Y(7.6) + 0.72, r"(a) the excess of a cycle, $n\ge3$",
           anchor="south west")

    # -------------------------------------------------------------- (b)
    bx = 7.6
    B = [(bx + 0.55, Y(t[1])), (bx + 2.15, Y(t[2])), (bx + 3.75, Y(p)),
         (bx + 5.35, Y(t[0]))]
    cols = ["PClay", "PClay", "PBlue", "PClay"]
    for q, c in zip(B, cols):
        F.disc(q[0], q[1], rM if c == "PClay" else rL + 0.4, c,
               ring="white", lw=0.4)
    for a, b in zip(B, B[1:]):
        F.seg(list(shorten(a, b, cut)), arrow)
    # the value of the product, below the path
    out = "PViolet,line width=0.7pt," + DASHED + "," + TIP
    F.bez((B[0][0] + 0.02, B[0][1] - 0.15), (B[0][0] + 0.4, Y(-3.2)),
          (B[3][0] - 0.1, Y(-3.4)), (B[3][0] + 0.02, B[3][1] - 0.15), out)
    names = [r"$M_{2}[-d]$", r"$M_{3}[-d-1]$", r"$L_{\zeta}[-d+4]$",
             r"$M_{1}[-d+3]$"]
    F.text(B[0][0] - 0.16, B[0][1], names[0], anchor="east",
           color="PClay!85!black")
    F.text(B[1][0] + 0.16, B[1][1] + 0.10, names[1], anchor="south west",
           color="PClay!85!black")
    F.text(B[2][0], B[2][1] - 0.20, names[2], anchor="north",
           color="PBlue")
    F.text(B[3][0] + 0.18, B[3][1], names[3], anchor="west",
           color="PClay!85!black")
    degs = [(r"$\mathcal{H}^{0}$", "east", -0.14, 0.24),
            (r"$\mathcal{H}^{6}$", "west", 0.14, 0.05),
            (r"$\mathcal{H}^{0}$", "south east", -0.10, 0.10)]
    for (a, b), (s, an, dx, dy) in zip(zip(B, B[1:]), degs):
        mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
        F.text(mx + dx, my + dy, s, anchor=an, font=SN)
    F.text((B[1][0] + B[2][0]) / 2 + 0.05, Y(-2.2),
           r"$y\mapsto\mathcal{H}^{6}(M_{2},M_{1})$", anchor="north",
           color="PViolet", font=SN)
    x0, y0 = bx - 0.1, Y(-1.2) - 1.05
    lines = [
        r"$\Ext$ degrees $0,6,0$, excesses $-1,5,-1$: the product with",
        r"$y\in H^{2}(\cO_{A})$ lands in degree $6$, in a space of",
        r"dimension $(t_{2}-t_{1})^{6}$; the shifts force",
        r"$\sigma_{1}=\sigma_{3}=-\sigma_{2}$",
    ]
    for k, s in enumerate(lines):
        F.text(x0, y0 - 0.47 * k, s, anchor="north west", font=SN)
    F.text(bx - 0.1, Y(7.6) + 0.72,
           r"(b) the one path that acts, $n=3$", anchor="south west")
    F.write()
    return F.name


# ======================================================= diagonal budget
def fig_diagonalbudget():
    D2, kerL, ker = budget()
    F = Plate("fig_diagonalbudget",
              "The 525 diagonal classes of degree two at n = 3: what the cup "
              "products remove, what the fourfold products can remove for "
              "each gap t_2 - t_1, and the 57 the criterion asks for "
              "(prop:cupkernel, thm:esixdiagonal); beside it the components "
              "of the graphs Gamma_tau on the 32 pieces L_zeta.")
    s = 0.0118                      # cm per class
    w = 1.05                        # bar width

    def Y(v):
        return v * s
    base = 0.0
    F.seg([(-0.3, base), (10.2, base)], "PSlate,line width=0.5pt")

    def bar(x, lo, hi, fill, draw):
        F.rect(x, Y(lo), x + w, Y(hi), fill=fill, draw=draw, lw=0.45,
               bg=True)

    # 1. the diagonal
    x1 = 0.0
    bar(x1, 0, 480, "WBlue", "PBlue")
    bar(x1, 480, 525, "WTeal", "PTeal")
    F.text(x1 + w / 2, Y(240), r"$480$", color="PBlue", onbg=True)
    F.text(x1 + w / 2, Y(502.5), r"$45$", color="PTeal!85!black", font=SN,
           onbg=True)
    F.text(x1 + w / 2, Y(525) + 0.10, r"$525$", anchor="south")
    # 2. the cup products
    x2 = 2.0
    bar(x2, ker, D2, "WClay", "PClay")
    F.text(x2 + w / 2, Y((ker + D2) / 2), r"$-276$",
           color="PClay!85!black", onbg=True)
    F.seg([(x1 + w, Y(525)), (x2, Y(525))],
          "PSlate,line width=0.4pt," + DASHED)
    # 3. their kernel
    x3 = 4.0
    bar(x3, 0, kerL, "WBlue", "PBlue")
    bar(x3, kerL, ker, "WTeal", "PTeal")
    F.text(x3 + w / 2, Y(kerL / 2), r"$204$", color="PBlue", onbg=True)
    F.text(x3 + w / 2, Y((kerL + ker) / 2), r"$45$",
           color="PTeal!85!black", font=SN, onbg=True)
    F.text(x3 + w / 2, Y(ker) + 0.10, r"$249$", anchor="south")
    F.seg([(x2 + w, Y(ker)), (x3, Y(ker))],
          "PSlate,line width=0.4pt," + DASHED)
    # 4. the fourfold products, by the gap
    gx = [6.0, 7.35, 8.7]
    drops = [1, 64, ker]
    F.seg([(x3 + w, Y(ker)), (gx[-1] + w, Y(ker))],
          "PSlate,line width=0.4pt," + DASHED)
    for x, d in zip(gx, drops):
        if d == 1:
            F.rect(x, Y(ker) - 0.012, x + w, Y(ker) + 0.012, fill="PViolet",
                   draw="PViolet", lw=0.3)
        else:
            bar(x, ker - d, ker, "PViolet!14!white", "PViolet")
    F.text(gx[0] + w / 2, Y(ker) - 0.12, r"$-1$", anchor="north",
           color="PViolet", font=SN)
    F.text(gx[1] + w / 2, Y(ker - 32), r"$-64$", color="PViolet",
           font=SN, onbg=True)
    F.text(gx[2] + w / 2, Y(ker / 2 + 40), r"up to", color="PViolet",
           font=SN, onbg=True)
    F.text(gx[2] + w / 2, Y(ker / 2 - 10), r"$-249$", color="PViolet",
           font=SN, onbg=True)
    # the level r = 57
    F.seg([(x3 - 0.25, Y(57)), (gx[-1] + w + 0.25, Y(57))],
          "PInk,line width=0.7pt," + DASHED)
    F.text(gx[-1] + w + 0.35, Y(57), r"$r=57$", anchor="west")
    # the two brackets
    bxr = gx[-1] + w + 0.55
    F.seg([(bxr, Y(57) + 0.30), (bxr, Y(ker) - 0.04)],
          "PInk,line width=0.5pt,{Stealth[length=3.6pt,width=2.8pt]}-"
          "{Stealth[length=3.6pt,width=2.8pt]}")
    F.text(bxr + 0.12, Y((57 + ker) / 2) + 0.2, r"$192$ must go", anchor="west",
           font=SN)
    bxl = -0.35
    F.seg([(bxl, Y(57)), (bxl, Y(525))],
          "PInk,line width=0.5pt,{Stealth[length=3.6pt,width=2.8pt]}-"
          "{Stealth[length=3.6pt,width=2.8pt]}")
    F.text(bxl - 0.12, Y(291), r"$468$", anchor="east", font=SN)
    # the categories
    cats = [(x1, r"$D^{2}$"), (x2, r"cup products"), (x3, r"their kernel")]
    for x, c in cats:
        F.text(x + w / 2, -0.14, c, anchor="north", font=SN)
    for x, g in zip(gx, (r"$1$", r"$2$", r"$\ge3$")):
        F.text(x + w / 2, -0.14, g, anchor="north", font=SN,
               color="PViolet")
    F.text((gx[0] + gx[-1] + w) / 2, -0.62,
           r"fourfold products, by the gap $t_{2}-t_{1}$", anchor="north",
           font=SN, color="PViolet")
    # legend
    lx, ly = 0.0, -1.35
    for x, fill, draw, txt in (
            (lx + 0.12, "WBlue", "PBlue",
             r"classes at the $32$ pieces $L_{\zeta}$"),
            (lx + 5.0, "WTeal", "PTeal", r"classes at $M_{1},M_{2},M_{3}$")):
        F.rect(x - 0.1, ly - 0.1, x + 0.1, ly + 0.1, fill=fill, draw=draw,
               lw=0.45)
        F.text(x + 0.24, ly, txt, anchor="west", font=SN)

    # ------------------------------------------------------ the graphs
    P = pieces(3)
    order = sorted(P, key=lambda z: (z[0], z[1], z[2]))
    rows = [[z for z in order if z[0] == a] for a in range(4)]
    assert all(len(r) == 8 for r in rows)
    comp20 = cup_components((2, 0, 0))
    comp11 = cup_components((1, 1, 0))
    assert sorted(len(c) for c in comp20) == [8] * 4
    assert sorted(len(c) for c in comp11) == [2] * 16
    # rows are components for (2,0,0); within a row pairs are adjacent
    for c in comp20:
        assert len({z[0] for z in c}) == 1
    for r in rows:
        for k in range(0, 8, 2):
            assert sorted([r[k], r[k + 1]]) in [sorted(c) for c in comp11]
    dx, dy = 0.30, 0.34
    gx0 = 12.2
    tops = [Y(525) - 0.35, Y(525) - 3.05]
    heads = [r"$\Gamma_{\tau}$, $\tau=(2,0,0)$: $4$ components",
             r"$\Gamma_{\tau}$, $\tau=(1,1,0)$: $16$ components"]
    for g, (top, head) in enumerate(zip(tops, heads)):
        F.text(gx0 - 0.55, top + 0.42, head, anchor="south west", font=SN)
        for i, r in enumerate(rows):
            yy = top - i * dy
            if g == 0:
                F.rect(gx0 - 0.17, yy - 0.12, gx0 + 7 * dx + 0.17, yy + 0.12,
                       fill="WBlue", draw="PBlue", lw=0.45, rc=3.5)
            for k, z in enumerate(r):
                xx = gx0 + k * dx
                if g == 1 and k % 2 == 0:
                    F.seg([(xx, yy), (xx + dx, yy)],
                          "PTeal,line width=2.2pt")
                F.disc(xx, yy, 1.9, "PBlue", ring="white", lw=0.35)
        F.text(gx0 - 0.30, top - 1.5 * dy, r"$\zeta_{1}$", anchor="east",
               font=SN, color="PSlate")
    F.text(gx0 - 0.55, tops[1] - 4 * dy - 0.05,
           r"kernel on the $L_{\zeta}$:", anchor="north west", font=SN)
    F.text(gx0 - 0.55, tops[1] - 4 * dy - 0.47,
           r"$3\cdot4\cdot1+3\cdot16\cdot4=204$", anchor="north west",
           font=SN)
    F.write()
    return F.name


# ================================================================== main
ALL = ["convolutions", "diagonalbudget"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
