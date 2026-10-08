#!/usr/bin/env python3
"""
make_round24.py

One plate for the results of round twenty-four.

  fig_quarticlocal   lem:freegerm, thm:quarticlocal and cor:markmanquarticfails.
                     Left, in perspective: the support of Markman's sheaf E'
                     near a point p of the glued curve C', between two of the
                     divisors Supp G_i that the curve crosses (the crossings
                     are the gluing points); at p the tangent space splits
                     into the two eigenplanes T_1, T_2 of the real
                     multiplication, drawn as two small parallelograms, the
                     tangent line of C' lying in T_1 and meeting T_2 in zero,
                     so that the bivector pi_2 of T_2 has nonzero image in
                     wedge^2 N, N = T_p X / T_p C'.  Right: for the ten germs
                     of item (LXVIII), the pairs {k,l} of coordinate directions
                     whose translation classes multiply to a nonzero germ,
                     read from the Macaulay2 transcript m2/local_germs.txt
                     (or recomputed by Macaulay2 if that file is absent),
                     with the projective dimension of each germ.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back, and the plate is audited against its own raster before it
is written (make_core.Fig): no label meets ink or another label, and no
leader crosses ink, a label or another leader.

Run:  python3 -B make_round24.py     (from the figures directory)
"""
import math
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
from make_core import Fig, f4, orbit_cam, fit       # noqa: E402
from make_round19 import FN, SN                      # noqa: E402

GEN = "make_round24.py"

GERMS = [
    ("(i)", r"$\cO_{C}$, a line bundle on a smooth curve"),
    ("(ii)", r"$k(p)$, a skyscraper"),
    ("(iii)", r"a curve ideal in a smooth divisor"),
    ("(iv)", r"a point ideal in a smooth divisor"),
    ("(v)", r"$\cO_{D}$, a smooth divisor"),
    ("(vi)", r"two planes meeting at a point"),
    ("(vii)", r"maximal Cohen--Macaulay on a node"),
    ("(viii)", r"the glued germ of Example 11.2.7"),
    ("(ix)", r"reflexive, non-Cohen--Macaulay, node"),
    ("(x)", r"$\cO_{C}^{2}$, rank two on a smooth curve"),
]
PAIRS = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
ROMAN = [g[0] for g in GERMS]


def germ_data():
    """The projective dimension and the nonzero pairs of each germ, from the
    Macaulay2 output."""
    places = [os.path.join(HERE, "..", "m2"),
              os.path.join(HERE, "..", "..", "m2"), HERE]
    outs = [os.path.join(d, "local_germs.txt") for d in places]
    out = next((o for o in outs if os.path.exists(o)), None)
    if out is None:
        src = next(os.path.join(d, "local_germs.m2") for d in places
                   if os.path.exists(os.path.join(d, "local_germs.m2")))
        out = os.path.join(HERE, "local_germs.txt")
        r = subprocess.run(["M2", "--script", src], capture_output=True,
                           text=True)
        with open(out, "w") as f:
            f.write(r.stdout)
    data = {}
    pat = re.compile(r"^\((i|ii|iii|iv|v|vi|vii|viii|ix|x)\)\s+.*?: pd = (\d+), "
                     r"nonzero squares a_k a_l at \(k,l\): \{(.*)\}")
    for line in open(out):
        m = pat.match(line.strip())
        if not m:
            continue
        pairs = set()
        for a, b in re.findall(r"\((\d), (\d)\)", m.group(3)):
            pairs.add((min(int(a), int(b)), max(int(a), int(b))))
        data["(%s)" % m.group(1)] = (int(m.group(2)), pairs)
    assert set(data) == set(ROMAN), sorted(data)
    # the facts the paper states about these germs
    assert data["(i)"] == (3, {(1, 2), (1, 3), (2, 3)})
    assert data["(x)"] == (3, {(1, 2), (1, 3), (2, 3)})
    assert data["(ii)"] == (4, set(PAIRS))
    assert data["(iii)"] == (2, {(1, 2), (1, 3)})
    assert data["(v)"] == (1, set()) and data["(vii)"] == (1, set())
    assert data["(vi)"] == (2, {(1, 3), (1, 4), (2, 3), (2, 4)})
    assert data["(viii)"][1] == {(2, 3), (2, 4), (3, 4)}
    return data


def curve(t):
    """The glued curve C' in the schematic three-space."""
    return (0.95 * math.sin(1.25 * t) + 0.25 * t,
            1.0 * t,
            0.55 * math.cos(1.05 * t) - 0.35 + 0.12 * t)


def dcurve(t, h=1e-4):
    a, b = curve(t - h), curve(t + h)
    return tuple((b[i] - a[i]) / (2 * h) for i in range(3))


def unit(v):
    L = math.sqrt(sum(c * c for c in v))
    return tuple(c / L for c in v)


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def para(c, u, v, su, sv):
    """A parallelogram centred at c spanned by su u and sv v."""
    return [tuple(c[i] + a * su * u[i] + b * sv * v[i] for i in range(3))
            for a, b in ((-1, -1), (1, -1), (1, 1), (-1, 1))]


def fig_quarticlocal():
    data = germ_data()
    cam = orbit_cam((0.0, 0.0, 0.0), 31.0, 24.0, R=30.0)
    F = Fig("fig_quarticlocal",
            "The support of E' near a point of the glued curve, the two "
            "eigenplanes of the real multiplication at that point, and the "
            "table of nonzero products of translation classes for the ten "
            "germs of the computation (lem:freegerm, thm:quarticlocal, "
            "cor:markmanquarticfails).", cam, gen=GEN)
    # the two divisor sheets that C' crosses, at y = +-1.6
    ys = 1.6
    sheets = []
    for sgn in (-1, 1):
        y = sgn * ys
        sheets.append([(-1.55, y, -1.15), (1.55, y, -1.15), (1.55, y, 0.95),
                       (-1.55, y, 0.95)])
    pts = [q for S in sheets for q in S]
    fit(cam, pts, 5.9)
    for S in sheets:
        F.poly3(S, fill="WSlate", draw="PSlate!70", lw=0.4, opacity=0.55,
                prio=-2)
    # the curve, sampled, with its two crossings (gluing points) and p
    ts = [-3.0 + 6.0 * k / 160 for k in range(161)]
    samples = [curve(t) for t in ts]
    F.curve3(samples, "PClay,line width=0.9pt", prio=2, chunk=8)
    for t in (-ys, ys):
        F.dot3(curve(t), "PClay", r=1.7, prio=4)
    p = curve(0.0)
    tan = unit(dcurve(0.0))
    # T_1 contains the tangent line; T_2 is transverse to it
    aux = unit(cross(tan, (0.0, 0.0, 1.0)))
    nrm = unit(cross(tan, aux))
    T1 = para(p, tan, aux, 1.05, 0.62)
    u2 = unit(tuple(aux[i] + 0.55 * nrm[i] for i in range(3)))
    w2 = unit(tuple(nrm[i] - 0.50 * tan[i] - 0.35 * aux[i] for i in range(3)))
    T2 = para(p, u2, w2, 0.62, 0.72)
    F.poly3(T1, fill="PIndigo", draw="PIndigo!85!black", lw=0.45,
            opacity=0.28, prio=1)
    F.poly3(T2, fill="PTeal", draw="PTeal!85!black", lw=0.45, opacity=0.28,
            prio=1)
    # the tangent line, drawn beyond the plane T_1
    ell = [tuple(p[i] - 1.45 * tan[i] for i in range(3)),
           tuple(p[i] + 1.45 * tan[i] for i in range(3))]
    F.line3(ell, "PIndigo,line width=0.55pt,dash pattern=on 2.2pt off 1.3pt",
            prio=3)
    F.dot3(p, "PInk", r=2.0, prio=5)
    # labels
    F.alabel(F.P(p), "$p$", color="PInk", font=SN, prefer=-100, spread=180,
             rmin=0.25, rmax=2.6, lead=0.3, free=1.4)
    F.alabel(F.P(curve(-2.55)), "$C'$", color="PClay", font=SN, prefer=200,
             spread=180, rmin=0.14, rmax=1.4, lead=0.3, free=0.2)
    for S, txt in zip(sheets, (r"$\Supp G_{i}$", r"$\Supp G_{i'}$")):
        c = tuple(sum(q[k] for q in S) / 4 for k in range(3))
        F.alabel(F.P((c[0] + 1.35, c[1], c[2] - 0.95)), txt, color="PSlate",
                 font=SN, prefer=-40, spread=150, rmin=0.14, rmax=1.6,
                 lead=0.35, free=0.25)
    q1 = tuple(p[i] + 1.05 * tan[i] + 0.62 * aux[i] for i in range(3))
    F.alabel(F.P(q1), r"$T_{1}\supset T_{p}C'$", color="PIndigo", font=SN,
             prefer=40, spread=180, rmin=0.16, rmax=2.2, lead=0.3, free=0.6)
    q2 = tuple(p[i] - 0.62 * u2[i] + 0.72 * w2[i] for i in range(3))
    F.alabel(F.P(q2), r"$T_{2}$", color="PTeal!80!black", font=SN,
             prefer=140, spread=180, rmin=0.16, rmax=2.2, lead=0.3, free=0.6)
    for t in (-ys, ys):
        F.alabel(F.P(curve(t)), "gluing point", color="PClay", font=SN,
                 prefer=20 if t > 0 else 200, spread=180, rmin=0.16,
                 rmax=1.8, lead=0.3, free=0.2)
    # the sentence under the picture
    bx0, by0, bx1, by1 = fit(cam, pts, 5.9)
    xs = bx0 + 0.15
    y = by0 - 0.42
    lines = [
        (r"$T_{0}X=T_{1}\oplus T_{2}$: the eigenplanes of $F_{0}$.", "PInk"),
        (r"$T_{p}C'$ lies in at most one of them; here in $T_{1}$.", "PInk"),
        (r"$T_{2}\cap T_{p}C'=0$, so $\pi_{2}$ has nonzero image in",
         "PTeal!80!black"),
        (r"$\bigwedge^{2}N$, $N=T_{p}X/T_{p}C'$, and the germ of",
         "PTeal!80!black"),
        (r"$\operatorname{ev}_{E'}(x_{2})$ at $p$ is that image:",
         "PTeal!80!black"),
        (r"$x_{2}\lrcorner\ch(E')=0$ and $\operatorname{ev}_{E'}(x_{2})\ne0$.",
         "PInk"),
    ]
    for text, col in lines:
        F.label(xs, y, text, anchor="north west", color=col, font=SN)
        y -= 0.46

    # ------------------------------------------------------------ the table
    tx = bx1 + 1.05          # left edge of the row labels
    colw, rowh = 0.44, 0.40
    ncol = len(PAIRS)
    lab_w = 6.05             # width reserved for the row labels
    gx = tx + lab_w           # left edge of the grid
    top = by1 - 0.10
    F.label(gx + ncol * colw / 2, top + 0.62,
            r"pairs $\{k,l\}$ with $a_{\partial_{k}}a_{\partial_{l}}\ne0$",
            anchor="south", color="PInk", font=FN)
    for j, (k, l) in enumerate(PAIRS):
        F.label(gx + (j + 0.5) * colw, top + 0.10, "$%d%d$" % (k, l),
                anchor="south", color="PInk", font=SN)
    F.label(gx + ncol * colw + 0.42, top + 0.10, r"$\operatorname{pd}$",
            anchor="south", color="PInk", font=SN)
    for i, (rom, name) in enumerate(GERMS):
        y1 = top - i * rowh
        y0 = y1 - rowh
        pd, pairs = data[rom]
        F.label(tx, (y0 + y1) / 2, rom, anchor="west", color="PSlate",
                font=SN)
        F.label(tx + 1.05, (y0 + y1) / 2, name, anchor="west", color="PInk",
                font=SN)
        for j, pr in enumerate(PAIRS):
            x0 = gx + j * colw
            fill = "PClay!70!white" if pr in pairs else "white"
            F.flat("  \\path[fill=%s,draw=PSlate!60,line width=0.3pt] (%s,%s) "
                   "rectangle (%s,%s);\n" % (fill, f4(x0 + 0.02), f4(y0 + 0.02),
                                             f4(x0 + colw - 0.02),
                                             f4(y1 - 0.02)))
        F.label(gx + ncol * colw + 0.42, (y0 + y1) / 2, "$%d$" % pd,
                anchor="center", color="PInk", font=SN)
    ybot = top - len(GERMS) * rowh
    F.label(tx, ybot - 0.30,
            r"coordinates adapted to the germ: a filled cell is a "
            r"nonzero Yoneda", anchor="north west", color="PSlate", font=SN)
    F.label(tx, ybot - 0.74,
            r"square in the local $\Ext^{2}$; at a point of $C'$ the pairs of "
            r"normal directions are filled,", anchor="north west",
            color="PSlate", font=SN)
    F.label(tx, ybot - 1.18,
            r"and one of $\pi_{1},\pi_{2}$ projects onto them.",
            anchor="north west", color="PSlate", font=SN)
    F.write(thr=212)


ALL = ["quarticlocal"]

if __name__ == "__main__":
    names = sys.argv[1:] or ALL
    for n in names:
        globals()["fig_" + n]()
