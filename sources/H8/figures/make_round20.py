#!/usr/bin/env python3
"""
make_round20.py

Three plates for the results of round twenty.

  fig_cmcube     the eight weights (+-1,+-1,+-1) of the Hodge torus of a
                 Mumford fourfold at a CM point as the vertices of a cube, in
                 perspective: the four diagonals are the pairs of opposite
                 weights, the two inscribed tetrahedra T_+ (an even number of
                 entries -1, solid) and T_- = -T_+ (dashed) are the only
                 zero-sum four-sets without an opposite pair, and the shaded
                 face w_3 = 1 is H^{1,0}, meeting each tetrahedron in two
                 vertices (prop:cmsource(i)).  The tetrahedra, the diagonals
                 and the face are computed from the weights, not typed in.
                 Beside the cube, the dictionary between the cube and the
                 endomorphism algebra: functions on the tetrahedra give the
                 Weil field k_c, functions on the diagonals the Rosati fixed
                 algebra K_c^+, and End^0(X_c) = K_c^+ (x) k_c.

  fig_cmsource   the 132 Hodge classes of degree four on the square at a CM
                 point (prop:cmsource(ii),(iii)): the 100 products of divisor
                 classes as a block of cells, six of them Sp-invariant; the
                 32 tetrahedron monomials in two rows by tetrahedron and five
                 columns by the number of factors from the first copy, with
                 the ten symmetric sums s_{+-,k} that the Weil field reaches;
                 the chain 6 < 100 < 110 < 132; and, below, the coefficients
                 of the symmetric sum s_{+,2} and of the exceptional class
                 pi_12 - pi_13 on the six mixed monomials of T_+, in the
                 three pairs indexed by the coordinates in which the two
                 weights of S differ.  The counts 1, 4, 6, 4, 1, the pairing
                 of the six monomials and the coefficients |a_2 - a_3|/2,
                 |a_1 - a_3|/2, |a_1 - a_2|/2 are computed here from the
                 weights and asserted against the proposition.

  fig_massgap    thm:massgap and ex:mumfordmass.  Left: the mass of a
                 current in the class dual to k c against k; the line
                 k L_h(c) is the minimum over real currents, attained by a
                 smooth positive form, the integral minima lie on or above it
                 and satisfy ||kc||_Z / k -> L_h(c) (Federer), and the class
                 is algebraic exactly when a dot lies on the line.  The dots
                 are schematic: their heights are not computed by anything.
                 Right: the exact numbers of the Mumford square, computed
                 here in the split model of item (LXIII): the seven terms
                 C(6,k) theta^k (x) theta^{6-k} of theta_Y^6, their pairings
                 with pi_0 (only k = 3 survives, 20 * 144 = 2880) and with the
                 pi_ij (zero), hence L(omega_a) = 4 a_0, L(theta_Y^2) = 56,
                 and the complete intersection D cap D' of mass 224 = L(4
                 theta_Y^2).

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round20.py [name ...]     (from the figures directory)
"""
import itertools
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_core                                    # noqa: E402
from make_core import Fig, f4, orbit_cam, fit       # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402

GEN = "make_round20.py"


# ============================================================== the weights
WEIGHTS = [(x, y, z) for x in (1, -1) for y in (1, -1) for z in (1, -1)]


def neg(w):
    return tuple(-c for c in w)


def dset(a, b):
    return frozenset(t for t in range(3) if a[t] != b[t])


def tetrahedra():
    """The zero-sum four-sets of weights without an opposite pair, computed
    from the weights, together with the check of prop:cmsource(i)."""
    zero = [S for S in itertools.combinations(WEIGHTS, 4)
            if all(sum(w[t] for w in S) == 0 for t in range(3))]
    pairs = [S for S in zero if all(neg(w) in S for w in S)]
    tets = [S for S in zero if S not in pairs]
    assert len(zero) == 8 and len(pairs) == 6 and len(tets) == 2
    tp = [T for T in tets if all(w.count(-1) % 2 == 0 for w in T)]
    tm = [T for T in tets if all(w.count(-1) % 2 == 1 for w in T)]
    assert len(tp) == 1 and len(tm) == 1
    Tp, Tm = tp[0], tm[0]
    assert set(Tm) == {neg(w) for w in Tp}
    assert all(len({min(w, neg(w)) for w in T}) == 4 for T in (Tp, Tm))
    face = [w for w in WEIGHTS if w[2] == 1]
    assert len([w for w in face if w in Tp]) == 2
    assert len([w for w in face if w in Tm]) == 2
    return Tp, Tm


def convex_hull(pts):
    """The vertices of the convex hull of a set of points in the plane
    (monotone chain), as a list."""
    pts = sorted(set(pts))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    lower, upper = [], []
    for q in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], q) <= 0:
            lower.pop()
        lower.append(q)
    for q in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], q) <= 0:
            upper.pop()
        upper.append(q)
    return lower[:-1] + upper[:-1]


# ================================================================= the cube
def fig_cmcube():
    Tp, Tm = tetrahedra()
    cam = orbit_cam((0.0, 0.0, 0.0), 33.0, 20.0, R=34.0)
    F = Fig("fig_cmcube",
            "The eight weights of the Hodge torus at a CM point as the "
            "vertices of a cube, with the four diagonals (opposite pairs), "
            "the two tetrahedra T_+ and T_- (the Weil line) and the face "
            "H^{1,0} (prop:cmsource(i)).", cam, gen=GEN)
    fit(cam, WEIGHTS, 6.3)
    edge = "PSlate!55,line width=0.4pt"
    for a, b in itertools.combinations(WEIGHTS, 2):
        if len(dset(a, b)) == 1:
            F.line3([a, b], edge, prio=0)
    # the face w_3 = 1 is H^{1,0}
    face = [(1, 1, 1), (1, -1, 1), (-1, -1, 1), (-1, 1, 1)]
    F.poly3(face, fill="WOchre", draw="POchre", lw=0.45, opacity=0.62,
            prio=-2)
    # the four diagonals through the centre
    for w in Tp:
        F.line3([w, neg(w)],
                "PSlate!80,line width=0.32pt,dash pattern=on 1.5pt off 1.1pt",
                prio=0)
    # the tetrahedra: translucent faces and edges
    for T, base, style in ((Tp, "PIndigo", "PIndigo,line width=0.8pt"),
                           (Tm, "PTeal", "PTeal,line width=0.8pt,"
                            "dash pattern=on 2.4pt off 1.4pt")):
        for tri in itertools.combinations(T, 3):
            F.poly3(list(tri), fill=base, opacity=0.09, prio=-1)
        for a, b in itertools.combinations(T, 2):
            F.line3([a, b], style, prio=1)
    F.dot3((0.0, 0.0, 0.0), "PInk", r=1.3)
    for w in WEIGHTS:
        F.dot3(w, "PIndigo" if w in Tp else "PTeal", r=2.1)
    # vertex labels, placed automatically clear of the ink; the two
    # vertices that project into the interior of the outline, and the
    # centre, get a leader that may cross the edges near them
    cx, cy = F.P((0.0, 0.0, 0.0))
    P = {w: F.P(w) for w in WEIGHTS}
    hull = convex_hull(list(P.values()))
    for w in WEIGHTS:
        x, y = P[w]
        ang = math.degrees(math.atan2(y - cy, x - cx))
        inside = (x, y) not in hull
        F.alabel((x, y), "$(%d,%d,%d)$" % w,
                 color="PIndigo" if w in Tp else "PTeal", font=SN,
                 prefer=ang, spread=180, rmin=0.16,
                 rmax=3.2 if inside else 1.6, lead=0.42,
                 free=3.2 if inside else 0.30)
    F.alabel((cx, cy), "$0$", color="PInk", font=SN, prefer=-90, spread=180,
             rmin=0.12, rmax=3.2, lead=0.5, free=3.2)

    # the dictionary beside the cube
    xs = 4.55
    ys = 2.45
    dy = 0.42
    lines = [
        (r"\textbf{At a CM point $c$}", "PInk"),
        (r"vertices: the eight weights of the Hodge torus;\\"
         r"$\End^{0}(X_{c})\otimes\bar\QQ$ is the algebra of functions\\"
         r"on them, diagonal in the weight basis", "PInk"),
        (r"diagonals: the opposite pairs $\{w,-w\}$,\\"
         r"$\psi(e_{w},e_{-w})=\pm1$; functions on the four\\"
         r"diagonals: $K_{c}^{+}=\End^{0}(X_{c})^{\dagger}$, totally real,\\"
         r"of degree four", "PInk"),
        (r"tetrahedra: $T_{+}$ (solid), $T_{-}=-T_{+}$ (dashed),\\"
         r"the zero-sum four-sets with no opposite pair;\\"
         r"functions on the two tetrahedra: $k_{c}$,\\"
         r"imaginary quadratic", "PInk"),
        (r"$t_{\pm}=\prod_{w\in T_{\pm}}e_{w}$ span the Weil line $\HW(X_{c})$",
         "PIndigo"),
        (r"shaded face: $H^{1,0}(X_{c})=V_{1}\otimes V_{2}\otimes V_{3}^{1,0}$,\\"
         r"two vertices in each tetrahedron", "POchre!80!black"),
        (r"$\End^{0}(X_{c})=K_{c}^{+}\otimes k_{c}$: a vertex is\\"
         r"its diagonal together with its tetrahedron", "PInk"),
        (r"the Galois group acts linearly, permuting the\\"
         r"vertices; it preserves the diagonals and $\{T_{+},T_{-}\}$",
         "PSlate"),
    ]
    y = ys
    for text, col in lines:
        n = text.count(r"\\") + 1
        F.label(xs, y, text, anchor="north west", color=col, font=FN,
                extra="align=left")
        y -= dy * n + 0.16
    F.write(thr=212)


# ============================================================ the 132 cells
def exceptional_profile(a1, a2, a3):
    """|coefficient| of omega_a on the pair of mixed monomials of a
    tetrahedron indexed by the difference set D (prop:cmsource(ii))."""
    return {frozenset({0, 1}): abs(Fraction(a2 - a3, 2)),
            frozenset({0, 2}): abs(Fraction(a1 - a3, 2)),
            frozenset({1, 2}): abs(Fraction(a1 - a2, 2))}


def fig_cmsource():
    Tp, Tm = tetrahedra()
    # the counts of the tetrahedron monomials by |S|, and the three pairs
    counts = [len([S for S in itertools.combinations(Tp, k)]) for k in range(5)]
    assert counts == [1, 4, 6, 4, 1] and sum(counts) == 16
    pairs = {}
    for S in itertools.combinations(Tp, 2):
        comp = tuple(w for w in Tp if w not in S)
        D = dset(*S)
        assert len(D) == 2 and dset(*comp) == D
        pairs.setdefault(D, []).append(S)
    assert sorted(len(v) for v in pairs.values()) == [2, 2, 2]
    prof = exceptional_profile(1, -1, 0)         # pi_12 - pi_13
    assert prof == {frozenset({0, 1}): Fraction(1, 2),
                    frozenset({0, 2}): Fraction(1, 2),
                    frozenset({1, 2}): Fraction(1)}
    # weight-zero monomials on the square: 132 = 100 + 32
    W16 = [(w, i) for i in (1, 2) for w in WEIGHTS]
    hodge4 = [S for S in itertools.combinations(W16, 4)
              if all(sum(w[t] for w, _ in S) == 0 for t in range(3))]
    tetmon = [S for S in hodge4 if all(neg(w) not in [v for v, _ in S]
                                       for w, _ in S)]
    assert len(hodge4) == 132 and len(tetmon) == 32
    dname = {w: "d_{%d}" % (i + 1) for i, w in enumerate(Tp)}
    F = Plate("fig_cmsource",
              "The 132 Hodge classes of degree four on the square at a CM "
              "point: 100 products of divisor classes, 32 tetrahedron "
              "monomials, the ten symmetric sums, and the coefficients of "
              "s_{+,2} and of pi_12 - pi_13 on the six mixed monomials of "
              "T_+ (prop:cmsource).")

    # ------------------------------------------ the block of 100 cells
    c = 0.17
    x0, y0 = 0.0, 0.0
    F.rect(x0 - 0.06, y0 - 0.06, x0 + 10 * c + 0.06, y0 + 10 * c + 0.06,
           fill="WSlate", bg=True)
    six = {(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0)}
    for i in range(10):
        for j in range(10):
            fill = "POchre!45!white" if (i, j) in six else "PSlate!28!white"
            F.rect(x0 + j * c, y0 + i * c, x0 + (j + 1) * c, y0 + (i + 1) * c,
                   fill=fill, draw="white", lw=0.35)
    F.text(x0 + 5 * c, y0 + 10 * c + 0.16,
           r"$100$ products of\\two divisor classes", anchor="south",
           extra="align=center")
    F.text(x0 + 5 * c, y0 - 0.16,
           r"six of them\\$\mathrm{Sp}(V,\psi)$-invariant", anchor="north",
           color="POchre!80!black", extra="align=center")

    # --------------------------------- the 32 tetrahedron monomials
    cw, ch, gap = 0.30, 0.30, 0.30
    xt = x0 + 10 * c + 1.55
    ytr = y0 + 10 * c - 0.10
    rows = {"+": ytr - ch, "-": ytr - 2 * ch - 0.36}
    colx = []
    x = xt
    for k, n in enumerate(counts):
        colx.append((x, x + n * cw))
        x += n * cw + gap
    xend = x - gap
    for sgn, T in (("+", Tp), ("-", Tm)):
        y = rows[sgn]
        for k, n in enumerate(counts):
            xa, xb = colx[k]
            for j in range(n):
                fill = ("PIndigo!55!white" if (k == 2 and sgn == "+")
                        else "PTeal!45!white" if k == 2 else "PSlate!30!white")
                F.rect(xa + j * cw, y, xa + (j + 1) * cw, y + ch, fill=fill,
                       draw="white", lw=0.4)
        F.text(xt - 0.14, y + ch / 2, r"$T_{%s}$" % sgn, anchor="east")
    ytop = rows["+"] + ch + 0.10
    for k, (xa, xb) in enumerate(colx):
        F.text((xa + xb) / 2, ytop, r"$|S|=%d$" % k, anchor="south", font=FN)
    F.text(xt - 0.55, ytop + 0.58,
           r"the $32$ tetrahedron monomials $e^{(1)}_{S}e^{(2)}_{T\setminus S}$,\\"
           r"$1,4,6,4,1$ by the number $|S|$ of factors from the first copy",
           anchor="south west", extra="align=left")
    # the ten symmetric sums: one bracket under each column
    yb = rows["-"] - 0.12
    for k, (xa, xb) in enumerate(colx):
        F.seg([(xa + 0.02, yb + 0.07), (xa + 0.02, yb), (xb - 0.02, yb),
               (xb - 0.02, yb + 0.07)], "PInk,line width=0.45pt")
        F.text((xa + xb) / 2, yb - 0.08, r"$s_{\pm,%d}$" % k, anchor="north",
               font=FN)

    # ----------------------------------------- the three statements
    ys = y0 - 1.10
    F.text(x0, ys, r"with components in the Weil field $k_{c}$, the pull-backs "
           r"of the Weil line\\add one class per column, the ten sums "
           r"$s_{\pm,k}$: $110$ with the divisor products",
           anchor="north west", extra="align=left")
    F.text(x0, ys - 0.82, r"components separating the four weights of a "
           r"tetrahedron, as those of $K_{c}^{+}$ do,\\reach every cell: "
           r"$132$", anchor="north west", extra="align=left")
    F.text(x0, ys - 1.64, r"the exceptional classes lie in the twelve mixed "
           r"cells, $|S|=2$,\\and in no combination of the $s_{\pm,k}$",
           anchor="north west", color="PIndigo", extra="align=left")

    # --------------------------------------------- the chain of spans
    ych = ys - 3.60
    chain = [(0.0, r"$6$"), (2.75, r"$100$"), (5.5, r"$110$"),
             (8.25, r"$132$")]
    desc = [r"$\mathrm{Sp}(V,\psi)$-invariant\\divisor products",
            r"all products of\\divisor classes",
            r"and the Weil line\\along $k_{c}$: the\\maps $ax+by$",
            r"and the Weil line\\along $K_{c}^{+}$"]
    xc0 = x0 + 0.85
    for (dx, num), d in zip(chain, desc):
        xx = xc0 + dx
        F.ring(xx, ych, 11.5, "PInk", lw=0.6, fill="white")
        F.text(xx, ych, num, font=FN)
        F.text(xx, ych - 0.50, d, anchor="north", font=SN,
               extra="align=center")
    for (dx, _), (dx2, _) in zip(chain, chain[1:]):
        F.seg([(xc0 + dx + 0.43, ych), (xc0 + dx2 - 0.43, ych)],
              "PInk,line width=0.5pt," + TIP)
        F.text(xc0 + (dx + dx2) / 2, ych + 0.10, r"$\subset$", anchor="south",
               font=FN)
    F.text(xc0 + 7.45, ych + 0.70, r"exceptional classes", anchor="south",
           color="PIndigo", font=FN)
    F.seg([(xc0 + 7.45, ych + 0.64), (xc0 + 7.45, ych + 0.14)],
          "PIndigo,line width=0.5pt," + TIP)

    # ---------------------------------- the six mixed monomials of T_+
    xb0 = x0 + 1.15
    yb0 = ych - 4.95
    bw, bgap = 0.30, 0.08
    slot, pgap = 1.42, 0.50
    unit = 1.15
    Ds = [frozenset({0, 1}), frozenset({0, 2}), frozenset({1, 2})]
    dtxt = {frozenset({0, 1}): r"\{1,2\}", frozenset({0, 2}): r"\{1,3\}",
            frozenset({1, 2}): r"\{2,3\}"}
    formula = {frozenset({0, 1}): r"|a_{2}-a_{3}|/2",
               frozenset({0, 2}): r"|a_{1}-a_{3}|/2",
               frozenset({1, 2}): r"|a_{1}-a_{2}|/2"}
    xaxis_end = xb0 + 6 * slot + 2 * pgap + 0.15
    F.seg([(xb0 - 0.30, yb0), (xaxis_end, yb0)], "PInk,line width=0.5pt")
    for h in (Fraction(1, 2), Fraction(1)):
        yy = yb0 + float(h) * unit
        F.seg([(xb0 - 0.38, yy), (xb0 - 0.30, yy)], "PInk,line width=0.5pt")
        F.text(xb0 - 0.44, yy,
               r"$%s$" % ("1" if h == 1 else r"\tfrac12"), anchor="east",
               font=FN)
    x = xb0
    for D in Ds:
        S1, S2 = pairs[D]
        xpair0 = x
        for j, S in enumerate((S1, S2)):
            xm = x + slot / 2
            F.rect(xm - bw - bgap / 2, yb0, xm - bgap / 2, yb0 + unit,
                   fill="PSlate!45!white", draw="PSlate", lw=0.4)
            hgt = float(prof[D]) * unit
            F.rect(xm + bgap / 2, yb0, xm + bgap / 2 + bw, yb0 + hgt,
                   fill="PIndigo!70!white", draw="PIndigo", lw=0.4)
            F.text(xm, yb0 - 0.10 - 0.34 * j,
                   r"$\{%s,%s\}$" % (dname[S[0]], dname[S[1]]),
                   anchor="north", font=FN)
            x += slot
        F.text((xpair0 + x) / 2, yb0 + unit + 0.28,
               r"$D(S)=%s$\\$%s$" % (dtxt[D], formula[D]), anchor="south",
               font=FN, extra="align=center")
        F.seg([(xpair0 + 0.12, yb0 + unit + 0.20), (x - 0.12, yb0 + unit + 0.20)],
              "PSlate,line width=0.4pt")
        x += pgap
    F.text(xb0 - 0.44, yb0 + unit + 1.20,
           r"the six mixed monomials $e^{(1)}_{S}e^{(2)}_{T_{+}\setminus S}$ "
           r"of $T_{+}$ in three pairs, with $d_{1}=(1,1,1)$, $d_{2}=(1,-1,-1)$,\\"
           r"$d_{3}=(-1,1,-1)$, $d_{4}=(-1,-1,1)$; grey: the coefficients "
           r"$\pm1$ of $s_{+,2}$; blue: those of $\pi_{12}-\pi_{13}$, "
           r"$a=(1,-1,0)$",
           anchor="south west", font=FN, extra="align=left")
    F.write()
    return F.name


# ============================================================== the mass gap
def mumford_numbers():
    """The exact numbers of ex:mumfordmass, recomputed here: the pairings of
    the seven terms of theta_Y^6 with pi_0 = theta (x) theta / 4 and with the
    primitive summands, from int theta^4 = 24."""
    top = 24                                     # int_X theta^4 = 4!
    binom = [math.comb(6, k) for k in range(7)]
    assert binom == [1, 6, 15, 20, 15, 6, 1]
    # pi_0 (theta^k (x) theta^{6-k}) = (1/4) theta^{k+1} (x) theta^{7-k}
    pair0 = [Fraction(1, 4) * top * top if (k + 1 == 4 and 7 - k == 4) else 0
             for k in range(7)]
    assert pair0 == [0, 0, 0, 144, 0, 0, 0]
    total = sum(b * p for b, p in zip(binom, pair0))
    assert total == 2880
    L_pi0 = Fraction(total, math.factorial(6))
    assert L_pi0 == 4
    # theta_Y^8 = 8! vol, so L(theta_Y^2) = int theta_Y^8 / 6! = 8!/6!
    L_theta2 = Fraction(math.factorial(8), math.factorial(6))
    assert L_theta2 == 56
    return binom, pair0, total, L_pi0, L_theta2


def fig_massgap():
    binom, pair0, total, L_pi0, L_theta2 = mumford_numbers()
    F = Plate("fig_massgap",
              "The conjecture as a mass gap (thm:massgap): the real minimum "
              "k L_h(c), the integral minima above it with ||kc||_Z / k -> "
              "L_h(c), algebraic exactly when a minimum lies on the line; "
              "and the exact numbers of the Mumford square (ex:mumfordmass).")
    # ------------------------------------------------- left: the picture
    ox, oy = 0.0, 0.0
    W, H = 6.4, 5.2
    F.seg([(ox, oy), (ox + W, oy)], "PInk,line width=0.55pt," + TIP)
    F.seg([(ox, oy), (ox, oy + H)], "PInk,line width=0.55pt," + TIP)
    F.text(ox + W + 0.10, oy, r"$k$", anchor="west")
    F.text(ox, oy + H + 0.10, r"mass", anchor="south")
    kmax = 8
    sx = (W - 0.7) / kmax
    slope = (H - 1.75) / kmax
    for k in range(1, kmax + 1):
        F.seg([(ox + k * sx, oy), (ox + k * sx, oy - 0.08)],
              "PInk,line width=0.45pt")
        F.text(ox + k * sx, oy - 0.16, r"$%d$" % k, anchor="north", font=FN)
    # the real minimum: the line k L_h(c)
    F.seg([(ox, oy), (ox + (kmax + 0.4) * sx, oy + (kmax + 0.4) * slope)],
          "PAmber,line width=0.75pt")
    F.text(ox + (kmax + 0.4) * sx + 0.10, oy + (kmax + 0.4) * slope,
           r"$k\,L_{h}(c)$", anchor="west", color="PAmber!85!black", font=FN)
    # a non-algebraic class: minima above the line, gap o(k)
    non = [(k, 0.95 * math.sqrt(k)) for k in range(1, kmax + 1)]
    alg = [(k, 0.0 if k % 4 == 0 else 0.55 + 0.22 * ((k * 5) % 3))
           for k in range(1, kmax + 1)]
    for k, g in non:
        F.disc(ox + k * sx, oy + k * slope + g * 0.40, 2.0, "PClay",
               ring="white")
    for k, g in alg:
        F.disc(ox + k * sx, oy + k * slope + g * 0.40, 2.0, "PTeal",
               ring="white")
    F.text(ox + 4 * sx + 0.18, oy + 4 * slope - 0.30,
           r"$\|4c\|_{\ZZ}=L_{h}(4c)$", anchor="north west", color="PTeal",
           font=SN)
    # legend, below the axis
    lx, ly = ox + 0.15, oy - 1.12
    F.seg([(lx, ly), (lx + 0.5, ly)], "PAmber,line width=0.75pt")
    F.text(lx + 0.62, ly + 0.02,
           r"$L_{h}(kc)=k\,L_{h}(c)$: the minimum over real\\"
           r"currents, attained by a smooth strongly\\positive form",
           anchor="west", font=FN, extra="align=left")
    F.disc(lx + 0.25, ly - 1.22, 2.0, "PClay", ring="white")
    F.text(lx + 0.62, ly - 1.22,
           r"$\|kc\|_{\ZZ}$ for a class that is not algebraic:\\"
           r"above the line for every $k$, and\\"
           r"$\|kc\|_{\ZZ}/k\to L_{h}(c)$ (Federer)",
           anchor="west", font=FN, extra="align=left")
    F.disc(lx + 0.25, ly - 2.44, 2.0, "PTeal", ring="white")
    F.text(lx + 0.62, ly - 2.44,
           r"an algebraic class: the gap closes at\\"
           r"some $k$ and at its multiples, where the\\"
           r"minimiser is an effective cycle",
           anchor="west", font=FN, extra="align=left")
    F.text(lx, ly - 3.30,
           r"the heights of the dots are schematic;\\"
           r"the line and the limit are theorems", anchor="north west",
           font=SN, color="PSlate", extra="align=left")

    # ----------------------------------------- right: the Mumford numbers
    rx, ry = ox + W + 1.75, oy + H + 0.30
    F.text(rx, ry, r"\textbf{The Mumford square} $Y=X\times X$, "
           r"$\theta_{Y}=\theta\otimes1+1\otimes\theta$", anchor="north west")
    cw, chh = 0.60, 0.58
    y1 = ry - 0.62
    F.text(rx, y1 - chh / 2, r"$\theta_{Y}^{6}=\sum_{k}\binom6k\,"
           r"\theta^{k}\otimes\theta^{6-k}$", anchor="west", font=FN)
    y2 = y1 - 0.80
    x1 = rx + 3.35
    F.text(rx, y2 - chh / 2, r"$k$", anchor="west", font=FN)
    F.text(rx, y2 - chh / 2 - chh, r"$\binom6k$", anchor="west", font=FN)
    F.text(rx, y2 - chh / 2 - 2 * chh,
           r"$\int_{Y}\pi_{0}\,\theta^{k}\!\otimes\theta^{6-k}$",
           anchor="west", font=FN)
    F.text(rx, y2 - chh / 2 - 3 * chh,
           r"$\int_{Y}\pi_{ij}\,\theta^{k}\!\otimes\theta^{6-k}$",
           anchor="west", font=FN)
    for k in range(7):
        xx = x1 + k * cw
        for r_, val, col in ((0, str(k), "PInk"), (1, str(binom[k]), "PInk"),
                             (2, str(pair0[k]),
                              "PAmber!85!black" if pair0[k] else "PSlate"),
                             (3, "0", "PSlate")):
            yy = y2 - chh / 2 - r_ * chh
            if r_ == 2 and pair0[k]:
                F.rect(xx - cw / 2 + 0.03, yy - chh / 2 + 0.03,
                       xx + cw / 2 - 0.03, yy + chh / 2 - 0.03,
                       fill="WOchre", bg=True, rc=1.5)
            F.text(xx, yy, "$%s$" % val, font=FN, color=col,
                   onbg=(r_ == 2 and bool(pair0[k])))
    F.seg([(rx, y2 - chh), (x1 + 6.5 * cw, y2 - chh)],
          "PRule,line width=0.45pt")
    y3 = y2 - 4 * chh - 0.32
    lines = [
        r"$\int_{Y}\pi_{0}\,\theta_{Y}^{6}=20\cdot144=%d$, so\\"
        r"$L_{\theta_{Y}}(\omega_{a})=%d\,a_{0}/6!=4a_{0}$" % (total, total),
        r"$L_{\theta_{Y}}(\omega)=0$ for an exceptional class with $a_{0}=0$",
        r"$L_{\theta_{Y}}(\theta_{Y}^{2})=8!/6!=%d$; $4\theta_{Y}^{2}=[D\cap D']$\\"
        r"for $D,D'\in|2\theta_{Y}|$, of mass $%d$" % (L_theta2, 4 * L_theta2),
        r"open: an integral current of mass $56NM$ in the\\"
        r"class dual to $N(M\theta_{Y}^{2}+\omega)$; known at every\\"
        r"CM point with $N,M$ depending on the point; the\\"
        r"same $N,M$ at infinitely many CM points would\\"
        r"give every member",
    ]
    yy = y3
    for t in lines:
        n = t.count(r"\\") + 1
        F.text(rx, yy, t, anchor="north west", font=FN, extra="align=left")
        yy -= 0.40 * n + 0.14
    F.write()
    return F.name


# ================================================================== main
ALL = ["cmcube", "cmsource", "massgap"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
