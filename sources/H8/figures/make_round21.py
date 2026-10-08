#!/usr/bin/env python3
"""
make_round21.py

Two plates for the results of round twenty-one.

  fig_quarticrank  thm:quarticrank and cor:quarticleast.  The rank
                   r(gamma) = 64 + 16 mu + 4 rho_1 + 4 rho_2 + R_1 + R_2 of the
                   polarised criterion at a quartic CM field, drawn over the
                   plane of the Hankel part x = 16 mu + 4 rho_1 + 4 rho_2 and
                   the part y = R_1 + R_2 carried by the two spaces W_t.  The
                   points are the tuples allowed by the two conditions of the
                   theorem (mu = 1 forces rho_1, rho_2 >= 1; R_t = 7 forces
                   rho_t = 2), enumerated here, and each is labelled with its
                   value; they are fifteen, with fifteen different values.
                   Filled points are reached with rho_1 = rho_2, as the
                   rational classes of the corollary are; the point 80 is the
                   pure shape, excluded for every CM field (thm:cmpurefalse);
                   88 is the least value a complex meeting the criterion can
                   have; and the dashed segment is the level r = 100, which
                   meets no point.

  fig_delsarte     prop:delsarte(iii).  The 29 shapes of sums of Fermat
                   terms x^6, chains and loops in six variables, each drawn
                   as six nodes: a chain as a path of arrows ending at a
                   ringed node (its term x_k^6), a loop as a cycle, a Fermat
                   term as a lone ringed node.  Under each shape the least d
                   with d A^{-1} integral, the degree of the Fermat fourfold
                   that covers it, computed here from the exponent matrix.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and each plate is audited against its own raster before it
is written (make_core.Fig and make_round19.Plate): no label meets ink or
another label, and no leader crosses ink, a label or another leader.

Run:  python3 -B make_round21.py [name ...]     (from the figures directory)
"""
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_round19                                 # noqa: E402
from make_round19 import Plate, build, TIP, FN, SN  # noqa: E402

make_round19.GEN = "make_round21.py"


# ======================================================== the quartic rank
def quartic_tuples():
    """The tuples (mu, rho_1, rho_2, R_1, R_2) allowed by thm:quarticrank."""
    out = []
    for m in (0, 1):
        for r1 in (0, 1, 2):
            for r2 in (0, 1, 2):
                for R1 in (7, 8):
                    for R2 in (7, 8):
                        if m == 1 and (r1 == 0 or r2 == 0):
                            continue
                        if (R1 == 7 and r1 != 2) or (R2 == 7 and r2 != 2):
                            continue
                        out.append((m, r1, r2, R1, R2))
    return out


def quartic_points():
    pts = {}
    for t in quartic_tuples():
        m, r1, r2, R1, R2 = t
        x = 16 * m + 4 * r1 + 4 * r2
        y = R1 + R2
        pts.setdefault((x, y), []).append(t)
    vals = sorted(64 + x + y for (x, y) in pts)
    assert vals == [80, 84, 87, 88, 91, 92, 94, 95, 96, 104, 107, 108, 110,
                    111, 112], vals
    assert len(pts) == 15 and 100 not in vals
    rational = {k for k, ts in pts.items() if any(t[1] == t[2] for t in ts)}
    assert sorted(64 + x + y for (x, y) in rational) == [
        80, 88, 94, 95, 96, 104, 110, 111, 112]
    return pts, rational


def fig_quarticrank():
    pts, rational = quartic_points()
    F = Plate("fig_quarticrank",
              "The rank of the criterion at a quartic CM field "
              "(thm:quarticrank): the fifteen allowed points of the plane of "
              "the Hankel part and of R_1 + R_2, each with its value; filled "
              "points are reached with rho_1 = rho_2 (cor:quarticleast).")
    sx, sy = 0.40, 1.45
    ox, oy = 0.0, 0.0
    X0, X1 = -1.5, 35.0

    def P(x, y):
        return ox + x * sx, oy + (y - 13.3) * sy

    # the axes
    a0 = P(X0, 13.3)
    F.seg([a0, P(X1, 13.3)], "PInk,line width=0.55pt," + TIP)
    F.seg([a0, P(X0, 16.9)], "PInk,line width=0.55pt," + TIP)
    for x in range(0, 33, 4):
        F.seg([P(x, 13.3), (P(x, 13.3)[0], P(x, 13.3)[1] - 0.08)],
              "PInk,line width=0.45pt")
        F.text(P(x, 13.3)[0], P(x, 13.3)[1] - 0.16, r"$%d$" % x,
               anchor="north", font=FN)
    for y in (14, 15, 16):
        F.seg([P(X0, y), (P(X0, y)[0] - 0.08, P(X0, y)[1])],
              "PInk,line width=0.45pt")
        F.text(P(X0, y)[0] - 0.16, P(X0, y)[1], r"$%d$" % y, anchor="east",
               font=FN)
    F.text(P(X1, 13.3)[0] + 0.10, P(X1, 13.3)[1],
           r"$16\mu+4\rho_{1}+4\rho_{2}$", anchor="west", font=FN)
    F.text(P(X0, 16.9)[0], P(X0, 16.9)[1] + 0.10, r"$R_{1}+R_{2}$",
           anchor="south", font=FN)
    # the level r = 100 meets no point
    F.seg([P(22, 14), P(20, 16)], "PSlate,line width=0.6pt,dashed")
    F.text(P(22, 14)[0] + 0.10, P(22, 14)[1] - 0.10,
           r"$r=100$: no point", anchor="north west", font=SN,
           color="PSlate")
    # the points
    for (x, y), ts in sorted(pts.items()):
        v = 64 + x + y
        cx, cy = P(x, y)
        exc = y < 16
        col = "PClay" if exc else "PBlue"
        if (x, y) in rational:
            F.disc(cx, cy, 3.0, col, ring="white", lw=0.6)
        else:
            F.ring(cx, cy, 2.6, col, lw=0.9)
        off = 0.24 if (x, y) in ((0, 16), (8, 16)) else 0.12
        F.text(cx + off, cy - off, r"$%d$" % v, anchor="north west",
               font=FN, color=col + "!85!black")
    # the two marked values
    c80 = P(0, 16)
    F.seg([(c80[0] - 0.13, c80[1] - 0.13), (c80[0] + 0.13, c80[1] + 0.13)],
          "PInk,line width=0.8pt")
    F.seg([(c80[0] - 0.13, c80[1] + 0.13), (c80[0] + 0.13, c80[1] - 0.13)],
          "PInk,line width=0.8pt")
    F.text(c80[0] + 0.45, c80[1] + 0.75,
           r"$p$ constant: the pure shape,\\excluded for every CM field",
           anchor="south west", font=SN, extra="align=left")
    F.leader((c80[0] + 0.52, c80[1] + 0.72), (c80[0] + 0.10, c80[1] + 0.18))
    c88 = P(8, 16)
    F.ring(c88[0], c88[1], 5.4, "PInk", lw=0.6, fill="none")
    F.text(c88[0] + 1.60, c88[1] + 0.75,
           r"$88$: the least value for a complex\\meeting the criterion",
           anchor="south west", font=SN, extra="align=left")
    F.leader((c88[0] + 1.67, c88[1] + 0.72), (c88[0] + 0.18, c88[1] + 0.12))
    c112 = P(32, 16)
    F.text(c112[0] - 0.45, c112[1] + 0.75, r"general $p$",
           anchor="south east", font=SN)
    F.leader((c112[0] - 0.50, c112[1] + 0.72),
             (c112[0] - 0.06, c112[1] + 0.20))
    # legend, below the axis
    lx, ly = P(X0, 13.3)[0] + 0.2, P(X0, 13.3)[1] - 1.05
    F.disc(lx, ly, 3.0, "PBlue", ring="white", lw=0.6)
    F.text(lx + 0.22, ly, r"reached with $\rho_{1}=\rho_{2}$, as for a "
           r"rational class", anchor="west", font=FN)
    F.ring(lx, ly - 0.52, 2.6, "PBlue", lw=0.9)
    F.text(lx + 0.22, ly - 0.52, r"reached only with $\rho_{1}\ne\rho_{2}$",
           anchor="west", font=FN)
    lx2 = lx + 7.4
    F.disc(lx2, ly, 3.0, "PBlue", ring="white", lw=0.6)
    F.text(lx2 + 0.22, ly, r"$R_{1}=R_{2}=8$", anchor="west", font=FN)
    F.disc(lx2, ly - 0.52, 3.0, "PClay", ring="white", lw=0.6)
    F.text(lx2 + 0.22, ly - 0.52,
           r"some $R_{t}=7$: an exceptional coefficient", anchor="west",
           font=FN)
    F.text(lx - 0.2, ly - 1.02,
           r"$r(\gamma)=64+16\mu+4\rho_{1}+4\rho_{2}+R_{1}+R_{2}$; "
           r"$\mu=1$ forces $\rho_{1},\rho_{2}\ge1$, and $R_{t}=7$ forces "
           r"$\rho_{t}=2$", anchor="north west", font=FN)
    F.write()
    return F.name


# ============================================================ Delsarte shapes
def kinds(total):
    return [("F", 1)] + [(t, k) for k in range(2, total + 1) for t in "CL"]


def multisets(total, ks, start=0):
    if total == 0:
        yield []
        return
    for i in range(start, len(ks)):
        t, k = ks[i]
        if k <= total:
            for rest in multisets(total - k, ks, i):
                yield [ks[i]] + rest


def exponent_matrix(shape, m=6):
    rows = []
    pos = 0
    for t, k in shape:
        v = list(range(pos, pos + k))
        pos += k
        if t == "F":
            rows.append({v[0]: m})
        elif t == "C":
            for a in range(k - 1):
                rows.append({v[a]: m - 1, v[a + 1]: 1})
            rows.append({v[-1]: m})
        else:
            for a in range(k):
                rows.append({v[a]: m - 1, v[(a + 1) % k]: 1})
    return [[Fraction(r.get(j, 0)) for j in range(6)] for r in rows]


def inverse(M):
    n = len(M)
    A = [row[:] + [Fraction(int(i == j)) for j in range(n)]
         for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        A[c] = [x / piv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [row[n:] for row in A]


def least_d(shape):
    inv = inverse(exponent_matrix(shape))
    d = 1
    for row in inv:
        for x in row:
            d = d * x.denominator // math.gcd(d, x.denominator)
    return d


def fig_delsarte():
    shapes = list(multisets(6, kinds(6)))
    assert len(shapes) == 29
    ds = [least_d(s) for s in shapes]
    assert sorted(ds)[:7] == [6, 24, 24, 24, 30, 30, 30]
    assert ds[shapes.index([("L", 6)])] == 15624
    assert min(d for d in ds if d > 30) == 120
    order = sorted(range(29), key=lambda i: (ds[i], i))
    F = Plate("fig_delsarte",
              "The 29 Delsarte sextic fourfolds built from Fermat terms, "
              "chains and loops (prop:delsarte), with the degree d of the "
              "least Fermat fourfold that covers each.")
    ncol = 5
    cw, ch = 3.25, 1.62
    gap = 0.40
    arrow = "PInk,line width=0.5pt,-{Stealth[length=3.0pt,width=2.4pt]}"
    for idx, i in enumerate(order):
        sh, d = shapes[i], ds[i]
        r, c = divmod(idx, ncol)
        x0, y0 = c * cw, -r * ch
        col = "PBlue" if d == 6 else ("PTeal" if d <= 30 else "PClay")
        nodes = [(x0 + 0.35 + j * gap, y0) for j in range(6)]
        pos = 0
        for t, k in sh:
            idxs = list(range(pos, pos + k))
            pos += k
            if t in "CL":
                for a in range(k - 1):
                    p, q = nodes[idxs[a]], nodes[idxs[a + 1]]
                    F.seg([(p[0] + 0.07, p[1]), (q[0] - 0.08, q[1])], arrow)
            if t == "L":
                p, q = nodes[idxs[-1]], nodes[idxs[0]]
                F.bez((p[0], p[1] - 0.08),
                      (p[0] - 0.05, p[1] - 0.42),
                      (q[0] + 0.05, q[1] - 0.42),
                      (q[0], q[1] - 0.09), arrow)
            if t in "FC":
                ends = [idxs[-1]]
            else:
                ends = []
            for j in idxs:
                px, py = nodes[j]
                if j in ends:
                    F.ring(px, py, 2.4, col, lw=0.9)
                else:
                    F.disc(px, py, 1.9, col, ring="white", lw=0.4)
        F.text(x0 + 0.35 + 2.5 * gap, y0 - 0.55, r"$d=%d$" % d,
               anchor="north", font=SN, color=col + "!85!black")
    # legend in the last cell
    r, c = divmod(29, ncol)
    x0, y0 = c * cw, -r * ch
    F.ring(x0 + 0.30, y0 + 0.28, 2.4, "PInk", lw=0.9)
    F.text(x0 + 0.48, y0 + 0.28, r"a term $x^{6}$", anchor="west", font=SN)
    F.seg([(x0 + 0.20, y0 - 0.14), (x0 + 0.52, y0 - 0.14)], arrow)
    F.text(x0 + 0.62, y0 - 0.14, r"$x_{i}^{5}x_{i+1}$", anchor="west",
           font=SN)
    ly = y0 - 1.25
    F.disc(0.35, ly, 2.4, "PBlue", ring="white", lw=0.4)
    F.text(0.55, ly, r"the Fermat sextic, in $\mathcal{A}$", anchor="west",
           font=FN)
    F.disc(4.95, ly, 2.4, "PTeal", ring="white", lw=0.4)
    F.text(5.15, ly, r"$d\le30$: covered by a Fermat fourfold of degree "
           r"$24$ or $30$", anchor="west", font=FN)
    F.disc(0.35, ly - 0.50, 2.4, "PClay", ring="white", lw=0.4)
    F.text(0.55, ly - 0.50, r"$d\ge120$", anchor="west", font=FN)
    F.text(4.80, ly - 0.32, r"each is dominated by $X^{4}_{d}$, so it "
           r"satisfies (F3$'$), and the Hodge\\conjecture for it follows "
           r"from the Hodge conjecture for $X^{4}_{d}$", anchor="north west",
           font=FN, extra="align=left")
    F.write()
    return F.name


# ================================================================== main
ALL = ["quarticrank", "delsarte"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        if name:
            build(name)
