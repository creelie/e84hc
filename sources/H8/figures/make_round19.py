#!/usr/bin/env python3
"""
make_round19.py

Three plates for the results of round nineteen.

  fig_mumfordgroups  the four possible groups M^1 = M cap Sp(V,psi) of the
                     motives of a Mumford fourfold (prop:mumfordmotivic):
                     the chain G < G.A_3 < N < Sp(V,psi) with its indices and
                     the jump of the Lie algebra; for each case the dimension
                     of the algebraic classes in V^{(x)2m}, computed here from
                     the non-crossing pairings (c = 2 for m = 2, c = 5 for
                     m = 3) by counting orbits of A_3 and S_3, and checked
                     against the first fundamental theorem for Sp; whether
                     zeta lies in M^1, whether Det and r_1 are algebraic, and
                     whether the exceptional classes are.  Below, the cyclic
                     permutation zeta of the three tensor factors, the
                     subgroups of N/G ~ S_3 stable under a transitive Galois
                     action, and sp(V,psi) = Lie G + S^2V_1 (x) S^2V_2 (x)
                     S^2V_3, 36 = 3 + 3 + 3 + 27, with the eigenvalues -1
                     and 3 of r_1.

  fig_f3primereach   where (F3') and the Hodge conjecture are known by
                     arguments on zero-cycles and on rationally connected
                     fibrations (prop:f3primesmall, prop:f3primefibration,
                     rem:f3primesharp, rem:f3primefrontier), on the plane of
                     n = dim X and d, the least dimension of a closed subset
                     supporting CH_0(X)_Q (d <= dim R for the maximal
                     rationally connected quotient R).  The equivalences of
                     rem:f3primesharp are the arrows, and the first open
                     cases of rem:f3primefrontier are marked open.

  fig_k3threshold    the threshold of prop:k3powers(ii): for t = 1, ..., 21
                     the least n having a partition with t distinct part
                     sizes, computed here by dynamic programming over the
                     part sizes and checked to be t(t+1)/2; each bar is cut
                     into the parts 1, 2, ..., t of the staircase partition.
                     The Hodge conjecture holds for S^[n] below the bar tops;
                     at the top it is equivalent to the algebraicity of
                     det T(S) on S^t, and t = 21, n = 231 is the very
                     general K3 surface.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back.  The plates use the audited canvas of make_core.py: before a
file is written, the ink is compiled without its labels and rasterised, each
label is measured by TeX, and the generator stops if a label meets ink,
another label, or the box that checkfigs.py estimates for another label, or
if a leader crosses ink, a label or another leader.  Pale fills that carry
text (the cells of a table, the shaded regions of a plane) are drawn as a
background that labels may sit on; every stroke, mark, bar and arrow is ink.

Run:  python3 -B make_round19.py [name ...]     (from the figures directory)
This writes fig_<name>.tex, compiles fig_<name>.pdf and the 200 dpi PNG.
"""
import math
import os
import re
import subprocess
import sys
from fractions import Fraction
from itertools import permutations

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_core                                    # noqa: E402
from make_core import Fig, f4                       # noqa: E402

GEN = "make_round19.py"
TIP = "-{Stealth[length=4.6pt,width=3.6pt]}"
TIPS2 = "{Stealth[length=4.6pt,width=3.6pt]}-{Stealth[length=4.6pt,width=3.6pt]}"
FN = r"\footnotesize"
SN = r"\scriptsize"


# ================================================================== canvas
class Plate(Fig):
    """The audited canvas of make_core.Fig without a camera, with a
    background layer: pale fills that labels may sit on."""

    def __init__(self, name, blurb):
        super().__init__(name, blurb, cam=None, gen=GEN)
        self.bg = []
        self.bgrects = []        # background rectangles, in cm

    def write(self, strict=None, **kw):
        """make_core's audit, and then every label that is not marked as
        sitting on the background is tested against the background
        rectangles as well, from the exact label boxes of TeX."""
        if strict is None:
            strict = os.environ.get("FIGDRAFT") is None
        _, boxes, _, _ = self._render()
        bad = []
        for L, b in zip(self.labels, boxes):
            if L.get("onbg"):
                continue
            for (x0, y0, x1, y1) in self.bgrects:
                r = (x0 * make_core.PT, y0 * make_core.PT,
                     x1 * make_core.PT, y1 * make_core.PT)
                if (b[0] - 1.0 < r[2] and r[0] < b[2] + 1.0
                        and b[1] - 1.0 < r[3] and r[1] < b[3] + 1.0):
                    bad.append(L["text"])
                    break
        for t in bad:
            print("   ", self.name, ": label on a shaded region:", t)
        if bad and strict:
            raise SystemExit("background check failed for %s" % self.name)
        super().write(strict=strict, **kw)

    # -- layers ----------------------------------------------------------
    def back(self, s):
        self.bg.append(s if s.endswith("\n") else s + "\n")

    def ink(self, s):
        self.flat(s if s.endswith("\n") else s + "\n")

    def tex(self):
        return (make_core.HEAD.format(name=self.name, gen=self.gen,
                                      blurb=self.blurb)
                + "".join(self.bg) + self.body()
                + "".join(self._leader_tex(Q) for Q in self.leaders)
                + "".join(self._label_tex(L) for L in self.labels)
                + make_core.TAIL)

    # -- primitives ------------------------------------------------------
    def rect(self, x0, y0, x1, y1, fill=None, draw=None, lw=0.4, bg=False,
             rc=None, extra=""):
        opts = ["fill=%s" % fill if fill else "fill=none"]
        opts.append("draw=%s,line width=%.2fpt" % (draw, lw) if draw
                    else "draw=none")
        if rc:
            opts.append("rounded corners=%.1fpt" % rc)
        if extra:
            opts.append(extra)
        s = "  \\path[%s] (%s,%s) rectangle (%s,%s);" % (
            ",".join(opts), f4(x0), f4(y0), f4(x1), f4(y1))
        (self.back if bg else self.ink)(s)
        if bg and fill:
            self.bgrects.append((min(x0, x1), min(y0, y1), max(x0, x1),
                                 max(y0, y1)))

    def poly(self, pts, fill=None, draw=None, lw=0.4, bg=False, extra="",
             closed=True):
        opts = ["fill=%s" % fill if fill else "fill=none"]
        opts.append("draw=%s,line width=%.2fpt" % (draw, lw) if draw
                    else "draw=none")
        if extra:
            opts.append(extra)
        s = "  \\path[%s] %s%s;" % (
            ",".join(opts), " -- ".join("(%s,%s)" % (f4(x), f4(y))
                                       for x, y in pts),
            " -- cycle" if closed else "")
        (self.back if bg else self.ink)(s)

    def seg(self, pts, style, bg=False):
        s = "  \\draw[%s] %s;" % (style, " -- ".join(
            "(%s,%s)" % (f4(x), f4(y)) for x, y in pts))
        (self.back if bg else self.ink)(s)

    def bez(self, a, c1, c2, b, style, bg=False):
        s = ("  \\draw[%s] (%s,%s) .. controls (%s,%s) and (%s,%s) .. "
             "(%s,%s);" % (style, f4(a[0]), f4(a[1]), f4(c1[0]), f4(c1[1]),
                           f4(c2[0]), f4(c2[1]), f4(b[0]), f4(b[1])))
        (self.back if bg else self.ink)(s)

    def disc(self, x, y, r_pt, fill, ring="white", lw=0.5):
        self.ink("  \\path[fill=%s,draw=%s,line width=%.2fpt] (%s,%s) circle "
                 "(%.2fpt);" % (fill, ring, lw, f4(x), f4(y), r_pt))

    def ring(self, x, y, r_pt, draw, lw=0.8, fill="white"):
        self.ink("  \\path[fill=%s,draw=%s,line width=%.2fpt] (%s,%s) circle "
                 "(%.2fpt);" % (fill, draw, lw, f4(x), f4(y), r_pt))

    def hatch(self, x0, y0, x1, y1, color, step=0.11, lw=0.35, bg=True):
        """Diagonal hatching clipped to a rectangle."""
        lines = []
        w, h = x1 - x0, y1 - y0
        k = -h
        while k < w:
            lines.append("(%s,%s) -- (%s,%s)" % (f4(x0 + k), f4(y0),
                                                 f4(x0 + k + h), f4(y1)))
            k += step
        s = ("  \\begin{scope}\\clip (%s,%s) rectangle (%s,%s);"
             "\\draw[%s,line width=%.2fpt] %s;\\end{scope}"
             % (f4(x0), f4(y0), f4(x1), f4(y1), color, lw, " ".join(lines)))
        (self.back if bg else self.ink)(s)

    def text(self, x, y, s, anchor="center", color="PInk", font=FN,
             extra="", onbg=False):
        i = self.label(x, y, s, anchor=anchor, color=color, font=font,
                       extra=extra)
        self.labels[i]["onbg"] = onbg
        return i


def build(name):
    """pdflatex, the 200 dpi PNG, and the cleanup, in the figures folder."""
    r = subprocess.run(["pdflatex", "-interaction=nonstopmode",
                        "-halt-on-error", name + ".tex"], cwd=HERE,
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.stdout.write(r.stdout[-3000:])
        raise SystemExit("pdflatex failed on %s" % name)
    log = r.stdout
    if re.search(r"(Overfull|Underfull) \\hbox", log):
        raise SystemExit("bad box in %s" % name)
    subprocess.run(["pdftoppm", "-png", "-r", "200", "-singlefile",
                    name + ".pdf", name], cwd=HERE, check=True)
    for ext in (".aux", ".log"):
        try:
            os.remove(os.path.join(HERE, name + ext))
        except OSError:
            pass
    print("   built %s.pdf and %s.png" % (name, name))


# ====================================================== Mumford groups
def noncrossing_pairings(npts):
    """The non-crossing perfect matchings of 0, ..., npts-1 on a circle."""
    if npts == 0:
        return [()]
    out = []
    for j in range(1, npts, 2):          # 0 is paired with j
        for inner in noncrossing_pairings(j - 1):
            for outer in noncrossing_pairings(npts - j - 1):
                out.append(((0, j),)
                           + tuple((a + 1, b + 1) for a, b in inner)
                           + tuple((a + j + 1, b + j + 1) for a, b in outer))
    return out


def mumford_invariant_dims(m):
    """dim of the invariants in V^{(x)2m} of G, G.A_3, N and Sp(V,psi),
    V = V_1 (x) V_2 (x) V_3 of dimension 8: a basis of the G-invariants is
    the triples of non-crossing pairings, which zeta and the transpositions
    permute, so the A_3- and S_3-invariants are the orbits; the
    Sp-invariants are the (2m-1)!! pairings of psi, independent for
    2m <= 8."""
    c = len(noncrossing_pairings(2 * m))
    basis = [(a, b, d) for a in range(c) for b in range(c) for d in range(c)]
    cyc = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    allp = list(permutations(range(3)))

    def orbits(group):
        seen, k = set(), 0
        for x in basis:
            if x in seen:
                continue
            k += 1
            for g in group:
                seen.add(tuple(x[g[i]] for i in range(3)))
        return k
    sp = 1
    for k in range(2 * m - 1, 0, -2):
        sp *= k
    assert 2 * m <= 8
    dims = (c ** 3, orbits(cyc), orbits(allp), sp)
    # Burnside, as in the text of prop:mumfordmotivic
    assert dims[1] == Fraction(c ** 3 + 2 * c, 3)
    assert dims[2] == Fraction(c ** 3 + 3 * c * c + 2 * c, 6)
    return c, dims


def fig_mumfordgroups():
    c2, d2 = mumford_invariant_dims(2)
    c3, d3 = mumford_invariant_dims(3)
    assert (c2, d2) == (2, (8, 4, 4, 3))
    assert (c3, d3) == (5, (125, 45, 35, 15))
    dim_sp = 8 * 9 // 2
    dim_lie_g = 3 * 3
    assert dim_sp == dim_lie_g + 3 * 3 * 3 == 36
    F = Plate("fig_mumfordgroups",
              "The four possible groups M^1 of the motives of a Mumford "
              "fourfold (prop:mumfordmotivic).")

    # ---------------------------------------------------------- the chain
    ys = {"G": 0.0, "GA": 1.10, "N": 2.20, "Sp": 3.50}
    names = {"G": r"$G=\mathrm{Hg}(X)$", "GA": r"$G\cdot A_{3}$",
             "N": r"$N$", "Sp": r"$\mathrm{Sp}(V,\psi)$"}
    XC, BWD, BH = 0.95, 2.00, 0.60
    order = ["G", "GA", "N", "Sp"]
    for k in order:
        y = ys[k]
        fill = "WOchre" if k == "G" else "WSlate"
        F.rect(XC - BWD / 2, y - BH / 2, XC + BWD / 2, y + BH / 2,
               fill=fill, bg=True, rc=3)
        F.rect(XC - BWD / 2, y - BH / 2, XC + BWD / 2, y + BH / 2,
               draw="POchre" if k == "G" else "PSlate", lw=0.9 if k == "G"
               else 0.6, rc=3)
        F.text(XC, y, names[k], onbg=True)
    notes = {("G", "GA"): r"index $3$",
             ("GA", "N"): r"index $2$",
             ("N", "Sp"): r"$\dim$: $9<36$"}
    for a, b in zip(order, order[1:]):
        y0, y1 = ys[a] + BH / 2, ys[b] - BH / 2
        F.seg([(XC, y0), (XC, y1)], "PInk,line width=0.7pt")
        F.text(XC + 0.14, (y0 + y1) / 2, notes[(a, b)], anchor="west",
               color="PSlate")
    F.text(XC, ys["Sp"] + 0.62, r"$M=\mathbb{G}_{m}\cdot M^{1}$,\\"
           r"$M^{1}=M\cap\mathrm{Sp}(V,\psi)$", anchor="south",
           extra="align=center")

    # ---------------------------------------------------------- the table
    cols = [  # (centre, header, entries by case)
        (4.35, r"$X^{4}$\\$m=2$", ["$%d$" % v for v in d2]),
        (5.60, r"$X^{6}$\\$m=3$", ["$%d$" % v for v in d3]),
        (7.35, r"formula,\\$c=2$ or $5$",
         [r"$c^{3}$", r"$(c^{3}+2c)/3$", r"$(c^{3}+3c^{2}+2c)/6$",
          r"$(2m-1)!!$"]),
        (9.45, r"$\zeta\in M^{1}$", ["no", "yes", "yes", "yes"]),
        (11.05, r"$\mathrm{Det}$, $r_{1}$\\algebraic",
         ["yes", "yes", "yes", "no"]),
        (12.75, r"exceptional\\classes\\algebraic",
         ["yes", "no", "no", "no"]),
    ]
    xt0, xt1 = 3.55, 13.65
    ytab = ys["Sp"] + 0.55
    # the band of the case M^1 = G
    F.rect(xt0, ys["G"] - 0.33, xt1, ys["G"] + 0.33, fill="WOchre",
           bg=True)
    for x, head, ent in cols:
        F.text(x, ytab + 0.12, head, anchor="south", extra="align=center")
        for k, e in zip(order, ent):
            colr = "PInk"
            if e == "no":
                colr = "PSlate"
            F.text(x, ys[k], e, color=colr, onbg=(k == "G"))
    F.seg([(xt0, ytab), (xt1, ytab)], "PInk,line width=0.5pt")
    ygrp = ytab + 1.02
    F.seg([(3.75, ygrp), (8.95, ygrp)], "PInk,line width=0.35pt")
    F.text(6.35, ygrp + 0.08,
           r"$\dim$ of the algebraic classes in $V^{\otimes 2m}$",
           anchor="south")
    F.seg([(xt0, ys["G"] - 0.52), (xt1, ys["G"] - 0.52)],
          "PInk,line width=0.5pt")
    F.text((xt0 + xt1) / 2 - 1.2, ys["G"] - 0.72,
           r"$M^{1}=G$ $\Leftrightarrow$ the Hodge conjecture for every "
           r"$X^{n}$ $\Leftrightarrow$ the two exceptional classes of "
           r"$X\times X$ are algebraic\\"
           r"$\Leftrightarrow$ some algebraic class on some power of $X$ is "
           r"not fixed by $\zeta$",
           anchor="north", extra="align=center")

    # ------------------------------------------------ zeta, three factors
    yz = -3.45
    xs = [0.40, 1.65, 2.90]
    sw, sh = 0.62, 0.46
    for i, x in enumerate(xs):
        F.rect(x - sw / 2, yz - sh / 2, x + sw / 2, yz + sh / 2,
               fill="WBlue", bg=True, rc=2)
        F.rect(x - sw / 2, yz - sh / 2, x + sw / 2, yz + sh / 2,
               draw="PBlue", lw=0.6, rc=2)
        F.text(x, yz, "$V_{%d}$" % (i + 1), onbg=True)
    for a, b in zip(xs, xs[1:]):
        F.text((a + b) / 2, yz, r"$\otimes$")
    arc = "PIndigo,line width=0.75pt," + TIP
    for a, b in zip(xs, xs[1:]):
        F.bez((a + 0.10, yz + sh / 2 + 0.04), (a + 0.25, yz + 0.78),
              (b - 0.25, yz + 0.78), (b - 0.10, yz + sh / 2 + 0.04), arc)
    F.bez((xs[2] - 0.05, yz - sh / 2 - 0.04), (xs[2] - 0.35, yz - 1.05),
          (xs[0] + 0.35, yz - 1.05), (xs[0] + 0.05, yz - sh / 2 - 0.04), arc)
    F.text(xs[1], yz + 0.86, r"$\zeta$", anchor="south", color="PIndigo")
    F.text(xs[1], yz - 1.02,
           r"$v_{1}\otimes v_{2}\otimes v_{3}\mapsto "
           r"v_{3}\otimes v_{1}\otimes v_{2}$", anchor="north")

    # ------------------------------------- N/G and its stable subgroups
    bx, by = 5.30, -4.25
    pos = {"1": (bx + 1.25, by), "A3": (bx, by + 0.85),
           "t12": (bx + 0.98, by + 0.85), "t13": (bx + 1.90, by + 0.85),
           "t23": (bx + 2.82, by + 0.85), "S3": (bx + 1.25, by + 1.70)}
    txt = {"1": r"$1$", "A3": r"$A_{3}$", "S3": r"$S_{3}$",
           "t12": r"$\langle(12)\rangle$", "t13": r"$\langle(13)\rangle$",
           "t23": r"$\langle(23)\rangle$"}

    def link(a, b, style):
        (xa, ya), (xb, yb) = pos[a], pos[b]
        d = math.hypot(xb - xa, yb - ya)
        ua, ub = 0.27 / (yb - ya) * d, 0.27 / (yb - ya) * d
        F.seg([(xa + (xb - xa) * ua / d, ya + (yb - ya) * ua / d),
               (xb - (xb - xa) * ub / d, yb - (yb - ya) * ub / d)], style)
    solid = "PInk,line width=0.6pt"
    grey = "PSlate!55,line width=0.45pt,dash pattern=on 1.6pt off 1.2pt"
    link("1", "A3", solid)
    link("A3", "S3", solid)
    for t in ("t12", "t13", "t23"):
        link("1", t, grey)
        link(t, "S3", grey)
    for k, (x, y) in pos.items():
        F.text(x, y, txt[k], color="PSlate!80" if k.startswith("t")
               else "PInk")
    F.text(pos["1"][0] + 0.2, pos["S3"][1] + 0.30,
           r"subgroups of $N(\bar\QQ)/G(\bar\QQ)\cong S_{3}$;\\"
           r"dashed: not stable under the Galois group", anchor="south",
           extra="align=center")
    corr = {"1": r"$G/G$", "A3": r"$G\cdot A_{3}/G$", "S3": r"$N/G$"}
    for k, s in corr.items():
        x, y = pos[k]
        F.text(x - 0.30 if k != "A3" else x - 0.30, y, s, anchor="east",
               color="PSlate", font=SN)

    # ------------------------------------------- sp(V) = Lie G + 27
    cx0, cw, chh = 8.75, 0.15, 0.34
    yb = -3.55
    for i in range(36):
        a = cx0 + i * cw
        if i < 9:
            fill = "PIndigo!%d!white" % (46 if (i // 3) % 2 == 0 else 30)
        else:
            fill = "PAmber!%d!white" % (44 if i % 2 == 0 else 32)
        F.rect(a, yb - chh / 2, a + cw, yb + chh / 2, fill=fill,
               draw="white", lw=0.4)
    F.rect(cx0, yb - chh / 2, cx0 + 36 * cw, yb + chh / 2, draw="PInk",
           lw=0.45)
    for j in range(3):
        a = cx0 + 3 * j * cw
        F.text(a + 1.5 * cw, yb + chh / 2 + 0.07, "$T_{%d}$" % (j + 1),
               anchor="south", font=SN)

    def bracket(x0, x1, y, up=True):
        h = 0.07 if up else -0.07
        F.seg([(x0, y - h), (x0, y), (x1, y), (x1, y - h)],
              "PInk,line width=0.4pt")
    ylb = yb + chh / 2 + 0.60
    bracket(cx0 + 0.02, cx0 + 9 * cw - 0.02, ylb)
    F.text(cx0 + 4.5 * cw, ylb + 0.07,
           r"$\operatorname{Lie}G$, $\dim 9$", anchor="south")
    bracket(cx0 + 9 * cw + 0.02, cx0 + 36 * cw - 0.02, yb + chh / 2 + 0.14)
    F.text(cx0 + 22.5 * cw, yb + chh / 2 + 0.21,
           r"$S^{2}V_{1}\otimes S^{2}V_{2}\otimes S^{2}V_{3}$, $\dim 27$",
           anchor="south")
    F.text(cx0 + 4.5 * cw, yb - chh / 2 - 0.08, r"$r_{1}=-1$",
           anchor="north", font=SN, color="PIndigo")
    F.text(cx0 + 22.5 * cw, yb - chh / 2 - 0.08, r"$r_{1}=3$",
           anchor="north", font=SN, color="POchre")
    ylo = yb - chh / 2 - 0.50
    bracket(cx0 + 0.02, cx0 + 36 * cw - 0.02, ylo, up=False)
    F.text(cx0 + 18 * cw, ylo - 0.07,
           r"$\mathfrak{sp}(V,\psi)\cong S^{2}V$, $\dim 36$\\"
           r"$T_{i}\cong S^{2}V_{i}\otimes{\textstyle\bigwedge^{2}}V_{j}"
           r"\otimes{\textstyle\bigwedge^{2}}V_{k}$", anchor="north",
           extra="align=center")
    F.write()
    return F.name


# ==================================================== (F3') and zero-cycles
def fig_f3primereach():
    F = Plate("fig_f3primereach",
              "Where (F3') and the Hodge conjecture are known by arguments on "
              "zero-cycles and rationally connected fibrations.")
    CW, CH, GAP = 1.05, 0.56, 0.05
    BRX, BRY = 0.60, 0.50          # the breaks before n = 462 and d = 462

    def X(n):
        return (n - 1) * CW if n <= 7 else 7 * CW + BRX

    def Y(d):
        return d * CH if d <= 7 else 8 * CH + BRY

    def box(n, d):
        return X(n), Y(d), X(n) + CW - GAP, Y(d) + CH - GAP

    def centre(n, d):
        x0, y0, x1, y1 = box(n, d)
        return (x0 + x1) / 2, (y0 + y1) / 2

    # which statement each cell (n, d) carries, from the paper:
    #   B  HC and (F3') when n <= 5 and d <= 3        prop:f3primesmall
    #      (for n <= 3 every X qualifies, CH_0 being supported on X)
    #   C  open in general; known under a hypothesis on the maximal
    #      rationally connected quotient R        prop:f3primefibration
    #   O  open in general
    def kind(n, d):
        if n <= 5 and d <= 3:
            return "B"
        if n <= 5:
            return "C"
        return "O"
    cells = [(n, d) for n in range(1, 8) for d in range(0, n + 1)]
    cells.append((462, 462))
    fills = {"B": "PTeal!36!white", "C": "WClay", "O": "WClay"}
    for n, d in cells:
        k = kind(n, d)
        x0, y0, x1, y1 = box(n, d)
        F.rect(x0, y0, x1, y1, fill=fills[k], bg=True)
        if k == "C":
            F.hatch(x0, y0, x1, y1, "PTeal!60", step=0.12, lw=0.45)
    # region labels
    F.text(X(3) - GAP / 2, Y(1) - GAP / 2,
           r"$\mathrm{HC}$ and (F3$'$)", onbg=True)
    F.text(X(7) - GAP / 2, Y(3) + CH / 2, r"open in\\general",
           extra="align=center", color="PClay", onbg=True)

    # axes, with a break before 462 on each
    xa0, ya0 = -0.12, -0.12
    F.seg([(xa0, ya0), (X(7) + CW + 0.15, ya0)], "PInk,line width=0.5pt")
    F.seg([(X(462) - 0.12, ya0), (X(462) + CW, ya0)], "PInk,line width=0.5pt")
    F.seg([(xa0, ya0), (xa0, Y(7) + CH + 0.12)], "PInk,line width=0.5pt")
    F.seg([(xa0, Y(462) - 0.12), (xa0, Y(462) + CH)], "PInk,line width=0.5pt")
    a = X(7) + CW + 0.15
    for off in (0.0, 0.09):
        F.seg([(a + 0.08 + off, ya0 - 0.09), (a + 0.16 + off, ya0 + 0.09)],
              "PInk,line width=0.5pt")
    yb0 = Y(7) + CH + 0.12
    for off in (0.0, 0.09):
        F.seg([(xa0 - 0.09, yb0 + 0.08 + off), (xa0 + 0.09, yb0 + 0.16 + off)],
              "PInk,line width=0.5pt")
    for n in list(range(1, 8)) + [462]:
        xc = X(n) + (CW - GAP) / 2
        F.seg([(xc, ya0), (xc, ya0 - 0.08)], "PInk,line width=0.4pt")
        F.text(xc, ya0 - 0.14, "$%d$" % n, anchor="north", font=SN)
    for d in list(range(0, 8)) + [462]:
        yc = Y(d) + (CH - GAP) / 2
        F.seg([(xa0, yc), (xa0 - 0.08, yc)], "PInk,line width=0.4pt")
        F.text(xa0 - 0.14, yc, "$%d$" % d, anchor="east", font=SN)
    F.text((X(4) + X(5)) / 2, ya0 - 0.55, r"$n=\dim X$", anchor="north")
    F.text(xa0, Y(462) + CH + 0.10, r"$d$", anchor="south")

    # the equivalences of rem:f3primesharp, as double arrows
    arrow = "PAmber,line width=0.9pt," + TIPS2
    c44, c54, c60 = centre(4, 4), centre(5, 4), centre(6, 0)
    x0, y0, x1, y1 = box(4, 4)
    F.seg([(c54[0] - 0.13, c54[1]), (x1 - 0.10, c54[1])], arrow)
    F.bez((c60[0] - 0.10, c60[1] + 0.10), (c60[0] - 0.55, c60[1] + 1.35),
          (x1 - 0.05, y0 - 0.95), (x1 - 0.30, y0 + 0.06), arrow)
    F.disc(c54[0], c54[1], 2.6, "PAmber", lw=0.6)
    F.disc(c60[0], c60[1], 2.6, "PAmber", lw=0.6)
    # the first open cases (rem:f3primefrontier)
    ring44 = (x0 + 0.24, c44[1])
    F.ring(ring44[0], ring44[1], 3.0, "PClay", lw=1.0)
    c462 = centre(462, 462)
    F.ring(c462[0], c462[1], 3.0, "PClay", lw=1.0)

    # labels: the open fourfolds, in the empty corner above the diagonal
    ytop = Y(7) + CH + 0.26
    F.text(0.10, ytop,
           r"first open cases, $n=d=4$:\\"
           r"sextic fourfolds, $h^{4,0}=1$\\"
           r"$S\times S$, $S^{[2]}$, real multiplication\\"
           r"K3$^{[2]}$ type, real multiplication",
           anchor="north west", extra="align=left")
    F.leader((ring44[0], ytop - 1.555), (ring44[0], ring44[1] + 0.13),
             free=0.02, dot=False, style="PClay!80,line width=0.45pt")
    # the right-hand column: S^[231], uniruled fivefolds, rational sixfolds
    xr = X(462) - 0.10
    F.text(xr, Y(462) - 0.12,
           r"$S^{[231]}$, $S$ a very general K3 surface:\\"
           r"open; equivalent to $\det T(S)$ on $S^{21}$\\"
           r"being algebraic",
           anchor="north west", extra="align=left")
    F.text(xr, c54[1] - 0.16,
           r"uniruled fivefolds, $d\le4$: (F3$'$), or $\mathrm{HC}$,\\"
           r"for all of them $\Leftrightarrow$ in degree four\\"
           r"for every fourfold",
           anchor="south west", extra="align=left")
    F.leader((xr - 0.06, c54[1]), (c54[0] + 0.12, c54[1]), free=0.02,
             dot=False)
    F.text(xr, c60[1] - 0.20,
           r"rational sixfolds, $d=0$: all degrees but six\\"
           r"are known; (F3$'$), or $\mathrm{HC}$, for all of them\\"
           r"$\Leftrightarrow$ for every fourfold; $\mathrm{Bl}_{Y}\PP^{6}$ "
           r"for $Y\subset\PP^{5}$\\"
           r"a smooth sextic: (F3$'$) $\Leftrightarrow$ (F3$'$) for $Y$,\\"
           r"$h^{6,0},h^{5,1},h^{4,2},h^{3,3}=0,1,426,1753$",
           anchor="south west", extra="align=left")
    F.leader((xr - 0.06, c60[1]), (c60[0] + 0.12, c60[1]), free=0.02,
             dot=False)

    # legend
    yl = ya0 - 1.25
    s = 0.24
    PITCH = 0.44
    xl = -0.9
    entries = [
        ("B", r"$\mathrm{HC}$ and (F3$'$) when $n\le5$ and $d\le3$, hence "
              r"whenever $n\le3$ (Bloch--Srinivas; Conte--Murre)"),
        ("C", r"open in general; (F3$'$) if $R$ is birational to a variety "
              r"with $\Hdg^{2}=\mathrm{Ab}^{2}$, $\mathrm{HC}$ if to an "
              r"abelian fourfold"),
        ("O", r"open in general"),
    ]
    for k, t in entries:
        F.rect(xl, yl - s / 2, xl + s, yl + s / 2, fill=fills[k],
               draw="PSlate!70", lw=0.35)
        if k == "C":
            F.hatch(xl, yl - s / 2, xl + s, yl + s / 2, "PTeal!60",
                    step=0.08, lw=0.4, bg=False)
        F.text(xl + s + 0.14, yl, t, anchor="west")
        yl -= PITCH
    F.seg([(xl - 0.06, yl), (xl + s + 0.06, yl)], arrow)
    F.text(xl + s + 0.14, yl,
           r"for the varieties at the dot, (F3$'$), or $\mathrm{HC}$, is "
           r"equivalent to degree four on every fourfold",
           anchor="west")
    yl -= PITCH
    F.ring(xl + s / 2, yl, 3.0, "PClay", lw=1.0)
    F.text(xl + s + 0.14, yl,
           r"a first open case; $d=n$ whenever $H^{n,0}(X)\neq0$",
           anchor="west")
    yl -= PITCH - 0.20
    F.text(xl - 0.05, yl,
           r"$d$: the least dimension of a closed subset supporting "
           r"$\mathrm{CH}_{0}(X)_{\QQ}$;\\$d\le\dim R$, $R$ the maximal "
           r"rationally connected quotient of $X$",
           anchor="north west", extra="align=left")
    F.write()
    return F.name


# ======================================================== K3 threshold
def least_n_with_distinct_sizes(tmax, nmax):
    """least[t] = the least n having a partition with exactly t distinct part
    sizes, by dynamic programming over the part sizes s = 1, ..., nmax: a
    size is used with some multiplicity a >= 1 or not at all."""
    reach = [set() for _ in range(nmax + 1)]    # reach[n] = {t}
    reach[0].add(0)
    for s in range(1, nmax + 1):
        new = [set(x) for x in reach]
        for n0 in range(nmax + 1):
            if not reach[n0]:
                continue
            a = 1
            while n0 + a * s <= nmax:
                for t in reach[n0]:
                    if t < tmax:
                        new[n0 + a * s].add(t + 1)
                a += 1
        reach = new
    least = {}
    for n in range(nmax + 1):
        for t in reach[n]:
            least.setdefault(t, n)
    return least


def fig_k3threshold():
    TM = 21
    least = least_n_with_distinct_sizes(TM, 240)
    N = {t: t * (t + 1) // 2 for t in range(0, TM + 1)}
    for t in range(1, TM + 1):
        assert least[t] == N[t], (t, least[t])
    assert N[21] == 231
    F = Plate("fig_k3threshold",
              "The threshold t(t+1)/2 of prop:k3powers(ii): the least n with a "
              "partition of n having t distinct part sizes, t = 1..21.")
    P, BW, SY = 0.57, 0.38, 0.0255
    NTOP = 256
    W = TM * P
    H = NTOP * SY

    def xc(t):
        return (t - 0.5) * P

    # the open region, as background
    F.rect(0, 0, W, H, fill="WClay!80", bg=True)
    # the bars, cut into the parts 1, ..., t
    for t in range(1, TM + 1):
        a, b = xc(t) - BW / 2, xc(t) + BW / 2
        greyed = t <= 2
        for j in range(1, t + 1):
            y0, y1 = N[j - 1] * SY, N[j] * SY
            if greyed:
                fill = "PSlate!%d!white" % (34 if j % 2 else 20)
            else:
                fill = "PTeal!%d!white" % (52 if j % 2 else 30)
            F.rect(a, y0, b, y1, fill=fill)
        edge = "PSlate!80" if greyed else "PTeal!75!black"
        F.rect(a, 0, b, N[t] * SY, draw=edge, lw=0.45)
    # the threshold N(t) at the top of each bar, with its value
    for t in range(1, TM + 1):
        y = N[t] * SY
        F.disc(xc(t), y, 1.9, "PSlate" if t <= 2 else "PAmber", lw=0.55)
        F.text(xc(t), y + 0.13, "$%d$" % N[t], anchor="south", font=SN,
               color="PSlate" if t <= 2 else "PInk", onbg=True)
    # n = 231: a guide from the axis to the last bar
    y231 = 231 * SY
    F.seg([(0, y231), (xc(TM) - BW / 2 - 0.06, y231)],
          "PAmber,line width=0.55pt,dash pattern=on 2.4pt off 1.6pt")
    F.text(0.25, y231 - 0.13,
           r"very general $S$, so $t=21$:\\the Hodge conjecture holds for "
           r"$S^{[n]}$ with $n\le230$;\\for $S^{[231]}$ it is "
           r"equivalent to $\det T(S)$ on $S^{21}$ being algebraic",
           anchor="north west", font=FN, extra="align=left", onbg=True)
    # axes
    F.seg([(0, 0), (W, 0)], "PInk,line width=0.5pt")
    F.seg([(0, 0), (0, H)], "PInk,line width=0.5pt")
    for v in (0, 50, 100, 150, 200, 250):
        y = v * SY
        F.seg([(-0.09, y), (0, y)], "PInk,line width=0.4pt")
        F.text(-0.14, y, "$%d$" % v, anchor="east", font=SN)
    F.seg([(-0.09, y231), (0, y231)], "PAmber,line width=0.5pt")
    F.text(-0.14, y231, "$231$", anchor="east", font=SN, color="PAmber")
    for t in range(1, TM + 1):
        F.seg([(xc(t), 0), (xc(t), -0.08)], "PInk,line width=0.4pt")
        F.text(xc(t), -0.16, "$%d$" % t, anchor="north", font=SN)
    F.text(W / 2, -0.58, r"$t$: the number of distinct part sizes of a "
           r"partition of $n$; for $S$ with $E=\QQ$, $t=\dim T(S)$",
           anchor="north")
    F.text(-0.62, H / 2, r"$n$", anchor="east")
    # legend, below
    yl = -1.28
    xl = 0.0
    s = 0.24
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, fill="PTeal!40!white",
           draw="PTeal!75!black", lw=0.45)
    F.text(xl + s + 0.14, yl,
           r"$n<t(t+1)/2$: the Hodge conjecture holds for $S^{[n]}$; bar $t$ "
           r"is cut into the parts $1,2,\dots,t$",
           anchor="west")
    yl -= 0.46
    F.disc(xl + s / 2, yl, 1.9, "PAmber", lw=0.55)
    F.text(xl + s + 0.14, yl,
           r"$n=t(t+1)/2$: the Hodge conjecture for $S^{[n]}$ "
           r"$\Leftrightarrow$ $\det T(S)$ on $S^{t}$ is algebraic "
           r"$\Leftrightarrow$ it holds for every $S^{k}$",
           anchor="west")
    yl -= 0.46
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, fill="WClay!80",
           draw="PClay!70", lw=0.45)
    F.text(xl + s + 0.14, yl,
           r"$n>t(t+1)/2$: open; it follows from the algebraicity of "
           r"$\det T(S)$ on $S^{t}$",
           anchor="west")
    yl -= 0.46
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, fill="PSlate!28!white",
           draw="PSlate!80", lw=0.45)
    F.text(xl + s + 0.14, yl,
           r"$t\le2$ does not occur for a K3 surface with $E=\QQ$",
           anchor="west")
    F.write()
    return F.name


# ================================================================== main
ALL = ["mumfordgroups", "f3primereach", "k3threshold"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        build(name)
