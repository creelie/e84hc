#!/usr/bin/env python3
"""
make_closure.py

One plate for the closure theorem.

  fig_closure    the route of this paper through the rule set of the closure
                 theorem (setup:rules, thm:closure), drawn as a stack of six
                 plates, one per level of the derivation.  Each statement is
                 a block standing on the plate of its level, with its name on
                 the front face, and its standing given by the tint of the
                 block: derived by the rules, open, or proved in this paper;
                 the bounded criterion (P1), which is equivalent to its own
                 conclusion (thm:p1equivalent), is drawn apart, closed on
                 itself by a loop.

                 Level 0 carries (P2) once for each of the four kinds of
                 family, as in the rule set, and the secant route; level 1
                 the four kinds of family, W(K,n,delta) and W(K,n,delta_0) for
                 the imaginary quadratic fields and W(F,n,delta_0) and
                 W(F,n,delta) for the CM fields of degree at least four, each
                 with a small block on its top for the base point that
                 thm:everyfamily and thm:cmbasepoint put in it; level 2 the
                 two kinds of field; level 3 the Weil classes of every CM
                 field and (F2); level 4 the conjecture for abelian varieties,
                 (F3) and (F3'); level 5 HC.  The three arrows inside level 1
                 are prop:descent: descent from delta_0 to the other
                 discriminants within each field, and scalar extension from
                 the split families of F to those of K.

                 The arrows are the rules, each a theorem of tab:rules.  The
                 derivation of HC from the minimal sufficient set
                 {P2_split, (F2), (F3')} of thm:closure(ii) is computed from
                 the rule set of make_frontier.py (item (XXXIII)) and its
                 arrows are drawn heavy; the rules it does not use, (P2) for
                 the families that descent reaches, the secant route and the
                 two arrows of (F3), are drawn light.  Below level 0 a
                 bracket under the two (P2) blocks of the imaginary quadratic
                 fields records what thm:p2numerical, thm:p2support and
                 cor:hhfactor ask of an object of the first form, with Chern
                 character exactly a multiple of a Weil class, which
                 thm:p2false shows is met by no object.

Every label is written as  \\node[lbl,...] at (x,y) {...};  so that
checkfigs.py can read it back, and the figure is audited against its own
raster by make_core.Fig before it is written: the text on the front face of
each block is tested against the drawing with the front faces left blank, so
that no arrow or edge may cross it.
"""
import math
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from make_core import Fig, orbit_cam, fit  # noqa: E402
from make_frontier import (measure, minimal_sets, used_rules, BASE,  # noqa
                           RULES)

DZ = 1.50            # the height between two levels
H = 0.66             # the height of a block
D = 0.50             # the depth of a block
PX, PY = 8.05, 0.80  # the half sides of a plate
PAD = 0.20           # the free width on either side of the text on a block

TINT = {"d": "PIndigo", "o": "PClay", "p": "PGrass", "s": "PSlate"}

# name: (x, level, standing, text on the front face, statements of the rule
# set that the block stands for)
NODES = {
    "HC":       (0.0, 5, "d", r"$\mathbf{HC}$", ["HC"]),
    "HC_ab":    (0.0, 4, "d", r"$\mathbf{HC}$ for abelian varieties",
                 ["HC_ab"]),
    "F3":       (-5.0, 4, "o", r"(F3)", ["red_ab"]),
    "F3p":      (5.0, 4, "o", r"(F3$'$)", ["red_ab_mod"]),
    "weil_all": (0.0, 3, "d", r"Weil classes of every CM field",
                 ["weil_all"]),
    "F2":       (5.0, 3, "o", r"(F2)", ["red_weil"]),
    "weil_iq":  (-3.75, 2, "d", r"all $\mathbf{W}(K,n,\delta)$, "
                 r"$[K:\mathbb{Q}]=2$", ["weil_iq"]),
    "weil_cm":  (3.75, 2, "d", r"all $\mathbf{W}(F,n,\delta)$, "
                 r"$[F:\mathbb{Q}]\ge4$", ["weil_cm"]),
    "K1":       (-6.05, 1, "d", r"$\mathbf{W}(K,n,\delta\neq\delta_{0})$",
                 ["weil_nontriv"]),
    "K0":       (-1.95, 1, "d", r"$\mathbf{W}(K,n,\delta_{0})$",
                 ["weil_triv"]),
    "F0":       (1.95, 1, "d", r"$\mathbf{W}(F,n,\delta_{0})$",
                 ["weil_cm_triv"]),
    "F1":       (6.05, 1, "d", r"$\mathbf{W}(F,n,\delta\neq\delta_{0})$",
                 ["weil_cm_nontriv"]),
    "P2K1":     (-6.05, 0, "o", r"(P2)", ["P2_iq_ns"]),
    "P2K0":     (-1.95, 0, "o", r"(P2)", ["P2_iq_s"]),
    "secant":   (0.0, 0, "o", r"secant route", ["secant_all", "Q114"]),
    "P2F0":     (1.95, 0, "o", r"$\mathrm{P2}_{\mathrm{split}}$",
                 ["P2_cm_s"]),
    "P2F1":     (6.05, 0, "o", r"(P2)", ["P2_cm_ns"]),
    "P1":       (7.45, 0, "s", r"(P1)", []),
}

# (from, to, the labels of the rules the arrow stands for)
EDGES = [
    ("P2K1", "K1", ["thm:semiregclosure"]),
    ("P2K0", "K0", ["thm:semiregclosure"]),
    ("P2F0", "F0", ["thm:cmpropagation"]),
    ("P2F1", "F1", ["thm:cmpropagation"]),
    ("secant", "K0", ["prop:splitgeom"]),
    ("K0", "K1", ["prop:descent"]),
    ("F0", "F1", ["prop:descent"]),
    ("F0", "K0", ["prop:descent"]),
    ("K1", "weil_iq", ["prop:separate"]),
    ("K0", "weil_iq", ["prop:separate"]),
    ("F0", "weil_cm", ["prop:cmweil"]),
    ("F1", "weil_cm", ["prop:cmweil"]),
    ("weil_iq", "weil_all", ["app:albert"]),
    ("weil_cm", "weil_all", ["app:albert"]),
    ("weil_all", "HC_ab", ["ssec:closuremap"]),
    ("F2", "HC_ab", ["ssec:closuremap"]),
    ("F3", "HC_ab", ["prop:f3ishc"]),
    ("HC_ab", "HC", ["ssec:closuremap", "prop:f3prime"]),
    ("F3p", "HC", ["prop:f3prime"]),
    ("F3", "HC", ["ssec:closuremap"]),
]


def z_of(lv):
    return lv * DZ


class CFig(Fig):
    """make_core.Fig, with the front faces of the blocks left blank in the
    raster that the audit reads, so that the name printed on a face is tested
    against every other stroke but not against the face itself."""

    def _render(self, dpi=400):
        self._blank = True
        try:
            return Fig._render(self, dpi)
        finally:
            self._blank = False

    def body(self):
        b = Fig.body(self)
        if getattr(self, "_blank", False):
            b = re.sub(r"\\colorlet\{(FF\w+)\}\{[^}]*\}",
                       r"\\colorlet{\1}{white}", b)
        return b


def route_edges():
    """the arrows used by the derivation of HC from {P2_split, F2, F3'},
    computed from the rule set of item (XXXIII)"""
    S = {"P2_cm_s", "red_weil", "red_ab_mod"}
    assert S in minimal_sets()
    used = used_rules(BASE | S)
    heavy = set()
    for a, b, labs in EDGES:
        sa = NODES[a][4]
        sb = NODES[b][4]
        for i in used:
            prem, conc, lab = RULES[i]
            if conc in sb and lab in labs and set(sa) & set(prem):
                heavy.add((a, b))
    # the rules of the route, and nothing else
    assert heavy == {
        ("P2F0", "F0"), ("F0", "F1"), ("F0", "K0"), ("K0", "K1"),
        ("K1", "weil_iq"), ("K0", "weil_iq"), ("F0", "weil_cm"),
        ("F1", "weil_cm"), ("weil_iq", "weil_all"), ("weil_cm", "weil_all"),
        ("weil_all", "HC_ab"), ("F2", "HC_ab"), ("HC_ab", "HC"),
        ("F3p", "HC")}, heavy
    return heavy


def fig_closure():
    cam = orbit_cam((0.0, 0.0, 2.35 * DZ), 0, 17, R=60)
    F = CFig("fig_closure",
             "The route of this paper through the rule set of the closure "
             "theorem, as a stack of plates, one per level of the derivation.",
             cam, gen="make_closure.py")
    plates = [[(-PX, -PY, z_of(lv)), (PX, -PY, z_of(lv)), (PX, PY, z_of(lv)),
               (-PX, PY, z_of(lv))] for lv in range(6)]
    fit(cam, [p for pl in plates for p in pl], 14.2)
    sc = cam.scale
    heavy = route_edges()

    # the width of each block from the width of its name
    FS = r"\footnotesize"
    opts = "inner sep=0pt,font=%s" % FS
    wid = measure([(opts, NODES[n][3]) for n in NODES])
    W = {}
    for n, b in zip(NODES, wid):
        # a projected centimetre at the front of the stack is 1/sc units
        W[n] = (b[2] - b[0]) * 1.03 / sc + 2 * PAD
    W["HC"] = max(W["HC"], 1.3)
    W["P1"] = max(W["P1"], 1.0)

    def lo_hi(n):
        x, lv, _, _, _ = NODES[n]
        z = z_of(lv)
        return (x - W[n] / 2, -D / 2, z), (x + W[n] / 2, D / 2, z + H)

    order = [0]

    def put(tikz):
        F.add(1e6 - order[0], tikz)
        order[0] += 1

    for c, base in TINT.items():
        F.flat("  \\colorlet{FF%s}{%s!13!white}\n" % (c, base), under=True)

    def block(n):
        lo, hi = lo_hi(n)
        c = NODES[n][2]
        base = TINT[c]
        tones = {(0, -1, 0): "FF%s" % c, (0, 0, 1): "%s!30!white" % base,
                 (1, 0, 0): "%s!42!white" % base,
                 (-1, 0, 0): "%s!42!white" % base}
        put(F.prism_tikz(lo, hi, base, edge="%s!80!black" % base, lw=0.45,
                         tones=tones))

    HEAVY = "PIndigo,line width=1.25pt,-{Stealth[length=5pt,width=4pt]}"
    LIGHT = ("PSlate!75,line width=0.6pt,"
             "-{Stealth[length=4pt,width=3.2pt]}")

    def attach(n, dx):
        """a point on the front edge of block n, shifted towards dx"""
        x = NODES[n][0]
        m = max(0.0, W[n] / 2 - 0.25)
        return x + max(-m, min(m, 0.16 * dx))

    for lv in range(6):
        put("  \\path[fill=PSlate!5,draw=PRule,line width=0.45pt] %s -- cycle;"
            "\n" % F.path(plates[lv]))
        # the arrows arriving at this level from below
        for a, b, _ in EDGES:
            if NODES[b][1] != lv or NODES[a][1] != lv - 1:
                continue
            xa, xb = NODES[a][0], NODES[b][0]
            pa = (attach(a, xb - xa), -D / 2, z_of(lv - 1) + H)
            pb = (attach(b, xa - xb), -D / 2, z_of(lv))
            st = HEAVY if (a, b) in heavy else LIGHT
            put("  \\draw[%s] %s;\n" % (st, F.path([pa, pb])))
        for n in sorted((n for n in NODES if NODES[n][1] == lv),
                        key=lambda n: -abs(NODES[n][0])):
            block(n)
            if lv == 1:
                # the base point of the family, proved here, on the outer
                # end of the block
                lo, hi = lo_hi(n)
                xe = hi[0] - 0.25 if NODES[n][0] > 0 else lo[0] + 0.25
                m0 = (xe - 0.11, -0.10, hi[2])
                m1 = (xe + 0.11, 0.12, hi[2] + 0.16)
                put(F.prism_tikz(m0, m1, "PGrass", edge="PGrass!70!black",
                                 lw=0.35))
        # the arrows inside the level
        for a, b, _ in EDGES:
            if NODES[a][1] != lv or NODES[b][1] != lv:
                continue
            xa, xb = NODES[a][0], NODES[b][0]
            s = 1 if xb > xa else -1
            z = z_of(lv) + H / 2
            pa = (xa + s * (W[a] / 2 + 0.05), -D / 2, z)
            pb = (xb - s * (W[b] / 2 + 0.05), -D / 2, z)
            st = HEAVY if (a, b) in heavy else LIGHT
            put("  \\draw[%s] %s;\n" % (st, F.path([pa, pb])))
    # (P1), closed on itself: a loop over its block
    qx = NODES["P1"][0]
    loop = [(qx + 0.30 * math.cos(t), -D / 2,
             H + 0.36 + 0.30 * math.sin(t))
            for t in [-math.pi / 2 + 0.55 + 2 * math.pi * k / 60
                      for k in range(50)]]
    put("  \\draw[PSlate,line width=0.8pt,-{Stealth[length=4pt,width=3.2pt]}]"
        " %s;\n" % F.path(loop))

    # the names, on the front faces
    for n, (x, lv, c, t, _) in NODES.items():
        p = F.P((x, -D / 2, z_of(lv) + H / 2))
        F.label(p[0], p[1], t, font=FS,
                extra="text height=1.6ex,text depth=0.45ex")
    # the three arrows of prop:descent
    for a, b, t, up in (("K0", "K1", r"descent", 0.17),
                        ("F0", "F1", r"descent", 0.17),
                        ("F0", "K0", r"scalar extension", 0.21)):
        s = 1 if NODES[b][0] > NODES[a][0] else -1
        xm = ((NODES[a][0] + s * W[a] / 2) + (NODES[b][0] - s * W[b] / 2)) / 2
        p = F.P((xm, -D / 2, z_of(1) + H))
        F.label(p[0], p[1] + up, t,
                anchor="south", font=r"\scriptsize", color="PInk",
                extra="inner sep=0.8pt,text height=1.3ex,text depth=0pt")

    # the first form of (P2), under the two quadratic (P2)
    xa, xb = NODES["P2K1"][0], NODES["P2K0"][0]
    pa = F.P((xa, -PY, 0.0))
    pb = F.P((xb, -PY, 0.0))
    yb = pa[1] - 0.30
    F.flat("  \\draw[PSlate,line width=0.5pt] (%.4f,%.4f) -- (%.4f,%.4f) -- "
           "(%.4f,%.4f) -- (%.4f,%.4f);\n"
           % (pa[0], pa[1] - 0.10, pa[0], yb, pb[0], yb, pb[0],
              pb[1] - 0.10))
    xm = (pa[0] + pb[0]) / 2
    F.flat("  \\draw[PSlate,line width=0.5pt] (%.4f,%.4f) -- (%.4f,%.4f);\n"
           % (xm, yb, xm, yb - 0.14))
    F.label(xm, yb - 0.20,
            r"first form of (P2), $\operatorname{ch}(E)=N\omega$, met by "
            r"no $E$:\\[1pt]$\dim\operatorname{Ext}^{2}(E,E)=2n(2n-1)$, "
            r"support in codimension $<n$,\\[1pt]"
            r"$\operatorname{ev}_{E}$ factors through "
            r"$\bigwedge^{*}P\oplus\bigwedge^{*}Q$",
            anchor="north", font=r"\scriptsize", color="PInk",
            extra="align=center")

    # the key, above the top plate, on either side of HC
    q0 = F.P((-PX, PY, z_of(5)))
    ky = q0[1] + 0.62
    kx = q0[0] + 0.10
    for dx, c, t in ((0.0, "d", r"derived"), (1.62, "o", r"open"),
                     (2.90, "p", r"proved here")):
        base = TINT[c]
        F.flat("  \\path[fill=%s!30!white,draw=%s!80!black,line width=0.4pt]"
               " (%.4f,%.4f) rectangle (%.4f,%.4f);\n"
               % (base, base, kx + dx - 0.13, ky - 0.11, kx + dx + 0.13,
                  ky + 0.11))
        F.label(kx + dx + 0.24, ky, t, anchor="west", font=r"\footnotesize",
                extra="text height=1.6ex,text depth=0.45ex")
    q1 = F.P((PX, PY, z_of(5)))
    kr = q1[0] - 0.10
    rows = [(HEAVY, r"rule used by $\{\mathrm{P2}_{\mathrm{split}},"
                    r"\mathrm{F2},\mathrm{F3}'\}$"),
            (LIGHT, r"rule not used by it")]
    for i, (st, t) in enumerate(rows):
        y = ky + 0.20 - 0.46 * i
        F.flat("  \\draw[%s] (%.4f,%.4f) -- (%.4f,%.4f);\n"
               % (st, kr - 0.62, y, kr, y))
        F.label(kr - 0.74, y, t, anchor="east", font=r"\footnotesize",
                extra="text height=1.6ex,text depth=0.45ex")
    F.write()


if __name__ == "__main__":
    fig_closure()
