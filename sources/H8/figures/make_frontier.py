#!/usr/bin/env python3
"""
make_frontier.py

Six figures for the sections on the closure of the rule set, the Lefschetz
standard conjecture for abelian schemes over curves, and the Mumford target.

  fig_frontier       the rule set of the closure theorem with the rules of the
                     literature, drawn as a hypergraph: a rule with several
                     premises is a junction marked with a wedge, and each rule
                     carries a letter (a)-(i) that the caption resolves into
                     the result proving it.  The rule set of item (XXXIII) is
                     carried below as data; the five minimal sufficient sets
                     are computed here by exhaustive search, the derivation
                     of HC from each is computed and pruned, and each is drawn
                     as a thumbnail of the graph with the rules it uses
                     highlighted.  Clay marks an open statement, a double
                     frame an open statement that HC implies, grass what the
                     paper proves, slate what it quotes, indigo a derived
                     statement.

  fig_lefschetzgrid  the summands H^p(C,R^q) of the cohomology of an abelian
                     scheme of relative dimension four over a curve: the
                     eigenvalue 2^q of [2]^* and the rank C(8,q) of R^q on each
                     row, the weights of H_rel and H_C, the diagonals k = p+q,
                     the operators L_rel, Lambda_rel, L_C, Lambda_C, and in
                     magenta the value of each outer summand for a Mumford
                     family.

  fig_propagation    propagation along a compact Shimura curve, in 3D: the
                     base C drawn as a closed surface of genus two, the CM
                     points on it (visibility tested by ray casting), the
                     fibres over a CM point c, a Hecke translate c' and a very
                     general point t, the class y and its transports, and the
                     global class u that B(W) makes algebraic.

  fig_rigidity       the tangent space at Y = X_c x X_c of the Hodge locus of
                     an exceptional class, block by block over the weight
                     lattice of the torus of the first two factors, in 3D (one
                     cube per dimension: kappa, then the tangent space of the
                     diagonal Siegel space, which the Hodge locus of a class
                     with alpha rational contains, then the rest of
                     sp^{-1,1}); and the table of the scalars of the proof of
                     thm:mumfordrigid on the pieces E_J^- of HT^2(Y).

  fig_bypass         the ten routes to the Mumford target that avoid the
                     Lefschetz standard conjecture, numbered as in
                     rem:bypassaudit, with the obstruction or the reduction
                     that settles each.

  fig_hodgecount     the Hodge classes of X_t x X_t for a Mumford fourfold X_t,
                     degree by degree, computed here from the representation
                     theory of the Hodge group, against the subring generated
                     by divisor classes, at a very general point and at a CM
                     point.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back.  Beyond that, every label is measured by TeX itself (one
pdflatex run per figure, in a temporary directory) and tested against every
other label, every stroke and every filled region before the file is
written; the generator stops if any test fails.

The helpers box, arrow, curve, line, ribbon, label, junction, dot, seg,
ellipse and TIP are imported by other generators and are kept unchanged.

Run:  python3 -B make_frontier.py        (from the figures directory)
"""
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

# ------------------------------------------------ helpers (shared)
TIP = r"-{Stealth[length=5pt,width=4pt]}"


def box(x, y, text, fill, draw, w=None, lw=0.6, h=None, font=None,
        sharp=False):
    opts = []
    if w is not None:
        opts.append("minimum width=%.2fcm" % w)
    if h is not None:
        opts.append("minimum height=%.2fcm" % h)
    if font is not None:
        opts.append("font=%s" % font)
    extra = ("," + ",".join(opts)) if opts else ""
    rc = "" if sharp else "rounded corners=2.5pt,"
    return (r"  \node[draw=%s,fill=%s,%sinner sep=3pt,"
            r"line width=%.2fpt,align=center%s] at (%.2f,%.2f) {%s};"
            % (draw, fill, rc, lw, extra, x, y, text) + "\n")


def arrow(a, b, color, bend=None, style="", lw=0.8):
    bend_s = "" if bend is None else ",bend %s" % bend
    return (r"  \draw[%s,line width=%.2fpt,%s%s%s] (%.2f,%.2f) to (%.2f,%.2f);"
            % (color, lw, TIP, bend_s, style, a[0], a[1], b[0], b[1]) + "\n")


def curve(a, c1, c2, b, color, lw=0.8, tip=True, style=""):
    t = ("," + TIP) if tip else ""
    return (r"  \draw[%s,line width=%.2fpt%s%s] (%.2f,%.2f) .. controls "
            r"(%.2f,%.2f) and (%.2f,%.2f) .. (%.2f,%.2f);"
            % (color, lw, t, style, a[0], a[1], c1[0], c1[1], c2[0], c2[1],
               b[0], b[1]) + "\n")


def line(points, color, lw=0.6, style=""):
    pts = " -- ".join("(%.2f,%.2f)" % p for p in points)
    return r"  \draw[%s,line width=%.2fpt%s] %s;" % (color, lw, style, pts) + "\n"


def ribbon(points, color, width):
    """A thick smooth band under the arrows of one route."""
    pts = " ".join("(%.2f,%.2f)" % p for p in points)
    return (r"  \draw[%s,line width=%.1fpt,line cap=round,line join=round]"
            r" plot[smooth,tension=0.55] coordinates {%s};"
            % (color, width, pts) + "\n")


def label(x, y, text, color="PSlate", anchor=None, size=r"\scriptsize",
          extra=""):
    an = "" if anchor is None else ",anchor=%s" % anchor
    return (r"  \node[text=%s,inner sep=1pt,align=center,font=%s%s%s]"
            r" at (%.2f,%.2f) {%s};" % (color, size, an, extra, x, y, text)
            + "\n")


def junction(x, y, color):
    """A rule with several premises: a small disc with a wedge.  The text is
    pure mathematics with no printable letters, so checkfigs treats it as a
    dot, and it is placed by hand away from every label."""
    return (r"  \node[circle,draw=%s,fill=white,line width=0.7pt,inner sep=0.6pt,"
            r"font=\scriptsize] at (%.2f,%.2f) {$\wedge$};" % (color, x, y)
            + "\n")


def dot(x, y, color, r=1.8, hollow=False):
    if hollow:
        return (r"  \draw[%s,fill=white,line width=0.6pt] (%.2f,%.2f) circle "
                r"(%.1fpt);" % (color, x, y, r) + "\n")
    return r"  \fill[%s] (%.2f,%.2f) circle (%.1fpt);" % (color, x, y, r) + "\n"


def seg(spec):
    """The TikZ path of one edge: a straight segment or a cubic."""
    if len(spec) == 2:
        a, b = spec
        return "(%.2f,%.2f) -- (%.2f,%.2f)" % (a[0], a[1], b[0], b[1])
    a, c1, c2, b = spec
    return ("(%.2f,%.2f) .. controls (%.2f,%.2f) and (%.2f,%.2f) .. (%.2f,%.2f)"
            % (a[0], a[1], c1[0], c1[1], c2[0], c2[1], b[0], b[1]))


def ellipse(cx, cy, rx, ry, draw, fill, lw=0.7, style=""):
    return (r"  \draw[%s,fill=%s,line width=%.2fpt%s] (%.2f,%.2f) ellipse "
            r"(%.2f and %.2f);" % (draw, fill, lw, style, cx, cy, rx, ry) + "\n")


# ============================================= the measured canvas
PT_PER_CM = 72.27 / 2.54

PICTURE_OPTS = (r"x=1cm,y=1cm,line join=round,line cap=round,"
                r"font=\small,text=PInk")

MEAS_HEAD = r"""\documentclass{article}
\usepackage{amsmath,amssymb}
\usepackage{tikz}
\usetikzlibrary{arrows.meta,calc,decorations.pathreplacing,patterns}
\input{%(palette)s}
%(macros)s
\makeatletter
\newcommand{\mfcorner}[2]{\pgfpointanchor{#1}{#2}%%
  \typeout{MFMEAS #1 \strip@pt\pgf@x\space\strip@pt\pgf@y}}
\newcommand{\mfmeasure}[1]{\mfcorner{#1}{south west}\mfcorner{#1}{south east}%%
  \mfcorner{#1}{north east}\mfcorner{#1}{north west}}
\makeatother
\begin{document}
\begin{tikzpicture}[%(popts)s]
"""
MEAS_TAIL = r"""\end{tikzpicture}
\end{document}
"""

COORD = re.compile(r"\(\s*(-?\d+(?:\.\d*)?)\s*,\s*(-?\d+(?:\.\d*)?)\s*\)")
NODE = re.compile(r"\\node\[([^\]]*)\]\s*at\s*\((-?[\d.]+),\s*(-?[\d.]+)\)"
                  r"\s*\{(.*?)\};", re.S)


def measure(specs, macros=""):
    """TeX's own bounding box of each node (opts, text), in cm, relative to
    the point at which the node is placed."""
    if not specs:
        return []
    tmp = tempfile.mkdtemp(prefix="mfmeas_")
    try:
        pal = os.path.join(HERE, "palette").replace("\\", "/")
        src = [MEAS_HEAD % dict(palette=pal, macros=macros,
                                popts=PICTURE_OPTS)]
        for i, (o, t) in enumerate(specs):
            src.append(r"\node[%s] (mf%d) at (0,0) {%s};" % (o, i, t))
            src.append(r"\mfmeasure{mf%d}" % i + "\n")
        src.append(MEAS_TAIL)
        with open(os.path.join(tmp, "m.tex"), "w") as f:
            f.write("\n".join(src))
        subprocess.run(["pdflatex", "-interaction=batchmode",
                        "-halt-on-error", "m.tex"], cwd=tmp,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        log = open(os.path.join(tmp, "m.log"), errors="replace").read()
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    pts = {}
    for name, x, y in re.findall(r"MFMEAS mf(\d+) (-?[\d.]+) (-?[\d.]+)",
                                 log):
        pts.setdefault(int(name), []).append((float(x) / PT_PER_CM,
                                              float(y) / PT_PER_CM))
    out = []
    for i in range(len(specs)):
        if i not in pts:
            raise RuntimeError("could not measure node %d: %r" % (i, specs[i]))
        xs = [p[0] for p in pts[i]]
        ys = [p[1] for p in pts[i]]
        out.append((min(xs), min(ys), max(xs), max(ys)))
    return out


# ------------------------------------------------------------ geometry tests
def seg_hits_rect(p, q, r):
    x0, y0, x1, y1 = r
    dx, dy = q[0] - p[0], q[1] - p[1]
    t0, t1 = 0.0, 1.0
    for pp, qq in ((-dx, p[0] - x0), (dx, x1 - p[0]),
                   (-dy, p[1] - y0), (dy, y1 - p[1])):
        if abs(pp) < 1e-12:
            if qq < 0:
                return False
        else:
            t = qq / pp
            if pp < 0:
                t0 = max(t0, t)
            else:
                t1 = min(t1, t)
            if t0 > t1:
                return False
    return True


def point_in_poly(pt, poly):
    x, y = pt
    inside = False
    n = len(poly)
    for i in range(n):
        (xa, ya), (xb, yb) = poly[i], poly[(i + 1) % n]
        if (ya > y) != (yb > y):
            xc = xa + (y - ya) * (xb - xa) / (yb - ya)
            if xc > x:
                inside = not inside
    return inside


def poly_hits_rect(poly, r):
    x0, y0, x1, y1 = r
    xs = [p[0] for p in poly]
    ys = [p[1] for p in poly]
    if max(xs) < x0 or min(xs) > x1 or max(ys) < y0 or min(ys) > y1:
        return False
    n = len(poly)
    for i in range(n):
        if seg_hits_rect(poly[i], poly[(i + 1) % n], r):
            return True
    return point_in_poly(((x0 + x1) / 2, (y0 + y1) / 2), poly)


def rects_meet(a, b):
    return a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]


def bezier(a, c1, c2, b, n=48):
    out = []
    for k in range(n + 1):
        t = k / n
        s = 1 - t
        out.append((s ** 3 * a[0] + 3 * s * s * t * c1[0] + 3 * s * t * t * c2[0]
                    + t ** 3 * b[0],
                    s ** 3 * a[1] + 3 * s * s * t * c1[1] + 3 * s * t * t * c2[1]
                    + t ** 3 * b[1]))
    return out


def circle_pts(x, y, r, n=24):
    return [(x + r * math.cos(2 * math.pi * k / n),
             y + r * math.sin(2 * math.pi * k / n)) for k in range(n)]


def fmt(p):
    return "(%.3f,%.3f)" % (p[0], p[1])


# ------------------------------------------------------------------- canvas
class Fig:
    """The TikZ of one figure, with its geometry kept alongside, so that each
    label can be measured by TeX and tested against every other label, every
    stroke and every fill before the file is written."""

    def __init__(self, name, blurb, pad=0.045):
        self.name, self.blurb, self.pad = name, blurb, pad
        self.preamble = ""    # definitions shared by the figure and the ruler
        self.body = []
        self.labels = []      # dict(x, y, opts, text, tag, allow)
        self.segs = []        # (p, q, tag)
        self.polys = []       # (pts, tag)

    # -- emission ---------------------------------------------------------
    def raw(self, s):
        self.body.append(s if s.endswith("\n") else s + "\n")

    def node(self, x, y, text, opts, tag=None, allow=()):
        self.raw(r"  \node[%s] at (%.3f,%.3f) {%s};" % (opts, x, y, text))
        self.labels.append(dict(x=x, y=y, opts=opts, text=text, tag=tag,
                                allow=set(allow)))

    def text(self, x, y, text, color="PInk", size=r"\footnotesize",
             anchor=None, extra="", tag=None, allow=()):
        opts = "text=%s,inner sep=1pt,align=center,font=%s" % (color, size)
        if anchor:
            opts += ",anchor=%s" % anchor
        opts += extra
        self.node(x, y, text, opts, tag=tag, allow=allow)

    def size(self, text, color="PInk", size=r"\footnotesize", anchor=None,
             extra="", opts=None):
        """TeX's bounding box of a node placed at the origin."""
        if opts is None:
            opts = "text=%s,inner sep=1pt,align=center,font=%s" % (color,
                                                                     size)
            if anchor:
                opts += ",anchor=%s" % anchor
            opts += extra
        key = (opts, text)
        if not hasattr(self, "_cache"):
            self._cache = {}
        if key not in self._cache:
            self._cache[key] = measure([key], self.preamble)[0]
        return self._cache[key]

    def premeasure(self, specs):
        """Measure many (opts, text) nodes in one run of TeX."""
        if not hasattr(self, "_cache"):
            self._cache = {}
        todo = [k for k in dict.fromkeys(specs) if k not in self._cache]
        for k, b in zip(todo, measure(todo, self.preamble)):
            self._cache[k] = b

    @staticmethod
    def box_opts(fill, draw, lw=0.6, size=r"\footnotesize", w=None, h=None,
                 sharp=False, extra=""):
        opts = ("draw=%s,fill=%s,%sinner sep=2.6pt,line width=%.2fpt,"
                "align=center,font=%s"
                % (draw, fill, "" if sharp else "rounded corners=2pt,", lw,
                   size))
        if w is not None:
            opts += ",minimum width=%.2fcm" % w
        if h is not None:
            opts += ",minimum height=%.2fcm" % h
        return opts + extra

    def boxed(self, x, y, text, fill, draw, lw=0.6, size=r"\footnotesize",
              w=None, h=None, sharp=False, tag=None, allow=(), extra=""):
        opts = self.box_opts(fill, draw, lw, size, w, h, sharp, extra)
        self.node(x, y, text, opts, tag=tag, allow=allow)
        b = self.size(text, opts=opts)
        return (x + b[0], y + b[1], x + b[2], y + b[3])

    def path(self, pts, style, lw=0.6, closed=False, tag=None, record=True):
        body = " -- ".join(fmt(p) for p in pts) + (" -- cycle" if closed
                                                   else "")
        self.raw(r"  \draw[%s,line width=%.2fpt] %s;" % (style, lw, body))
        if record:
            n = len(pts)
            for i in range(n - 1 + (1 if closed else 0)):
                self.segs.append((pts[i], pts[(i + 1) % n], tag))

    def fill(self, pts, style, tag=None, record=True, draw=None, lw=0.5):
        body = " -- ".join(fmt(p) for p in pts) + " -- cycle"
        if draw:
            self.raw(r"  \filldraw[%s,draw=%s,line width=%.2fpt] %s;"
                     % (style, draw, lw, body))
        else:
            self.raw(r"  \fill[%s] %s;" % (style, body))
        if record:
            self.polys.append((list(pts), tag))

    def rect(self, x0, y0, x1, y1, style, tag=None, draw=None, lw=0.5,
             record=True):
        self.fill([(x0, y0), (x1, y0), (x1, y1), (x0, y1)], style, tag=tag,
                  draw=draw, lw=lw, record=record)

    def disc(self, x, y, r, style, tag=None, draw=None, lw=0.5):
        if draw:
            self.raw(r"  \filldraw[%s,draw=%s,line width=%.2fpt] (%.3f,%.3f) "
                     r"circle (%.3f);" % (style, draw, lw, x, y, r))
        else:
            self.raw(r"  \fill[%s] (%.3f,%.3f) circle (%.3f);"
                     % (style, x, y, r))
        self.polys.append((circle_pts(x, y, r + (lw / 72.27 * 2.54 / 2
                                                 if draw else 0)), tag))

    def scene(self, tikz, tag="scene", tagger=None):
        """Record the output of a render3d scene: every closed path is a fill,
        every open path a set of strokes.  tagger(statement) may name the
        tag of each statement."""
        self.raw(tikz.rstrip("\n"))
        for st in tikz.split(";\n"):
            st = st.strip()
            if not st or st.startswith(r"\node"):
                continue
            tg = tagger(st) if tagger else tag
            if "circle (" in st:
                m = re.search(r"\((-?[\d.]+),(-?[\d.]+)\) circle \(([\d.]+)\)",
                              st)
                if m:
                    self.polys.append((circle_pts(float(m.group(1)),
                                                  float(m.group(2)),
                                                  float(m.group(3)) + 0.01),
                                       tg))
                continue
            head = st.split("]")[0] if "]" in st else ""
            body = st[len(head) + 1:] if head else st
            coords = [(float(a), float(b)) for a, b in COORD.findall(body)]
            if not coords:
                continue
            if "cycle" in body:
                if "fill=" in head and "fill=none" not in head:
                    self.polys.append((coords, tg))
                if "draw=none" not in head and head.startswith(r"\draw"):
                    for i in range(len(coords)):
                        self.segs.append((coords[i],
                                          coords[(i + 1) % len(coords)], tg))
            else:
                for i in range(len(coords) - 1):
                    self.segs.append((coords[i], coords[i + 1], tg))

    # -- checking -----------------------------------------------------------
    def measure(self):
        specs = [(l["opts"], l["text"]) for l in self.labels]
        for l, b in zip(self.labels, measure(specs, self.preamble)):
            l["box"] = (l["x"] + b[0], l["y"] + b[1], l["x"] + b[2],
                        l["y"] + b[3])

    def check(self, verbose=True):
        self.measure()
        P = self.pad
        bad = []
        L = self.labels
        for i, a in enumerate(L):
            ra = (a["box"][0] - P, a["box"][1] - P, a["box"][2] + P,
                  a["box"][3] + P)
            for b in L[i + 1:]:
                if rects_meet(ra, b["box"]):
                    bad.append(("label/label", a["text"][:40], b["text"][:40]))
            for p, q, tag in self.segs:
                if tag is not None and (tag == a["tag"] or tag in a["allow"]):
                    continue
                if seg_hits_rect(p, q, ra):
                    bad.append(("label/stroke", a["text"][:40], tag,
                                "(%.2f,%.2f)-(%.2f,%.2f)" % (p[0], p[1], q[0],
                                                             q[1])))
                    break
            for pts, tag in self.polys:
                if tag == "bg" or (tag is not None and (tag == a["tag"]
                                                        or tag in a["allow"])):
                    continue
                if poly_hits_rect(pts, ra):
                    bad.append(("label/fill", a["text"][:40], tag))
                    break
        if verbose:
            for b in bad:
                print("   OVERLAP", b)
            print("  %s: %d labels, %d strokes, %d fills, %d problems"
                  % (self.name, len(L), len(self.segs), len(self.polys),
                     len(bad)))
        return bad

    def tikz(self):
        return "".join(self.body)


# ======================================================== figures
HEAD = r"""%% {name}.tex   (generated by make_frontier.py; do not edit by hand)
%% {blurb}
\documentclass[tikz,border=6pt]{{standalone}}
\usepackage{{amsmath,amssymb}}
\usetikzlibrary{{arrows.meta,calc,decorations.pathreplacing,patterns}}
\input{{palette}}
{preamble}\begin{{document}}
\begin{{tikzpicture}}[x=1cm,y=1cm,line join=round,line cap=round,
  font=\small,text=PInk]
"""
TAIL = r"""\end{tikzpicture}
\end{document}
"""
STIP = r"-{Stealth[length=4pt,width=3.2pt]}"
FS, SS = r"\footnotesize", r"\scriptsize"


def write(fig):
    path = os.path.join(HERE, fig.name + ".tex")
    with open(path, "w") as f:
        f.write(HEAD.format(name=fig.name, blurb=fig.blurb,
                            preamble=fig.preamble))
        f.write(fig.tikz())
        f.write(TAIL)
    print("wrote", path)


# ================================================================ Ext profile
# ================================================================== frontier
# The rule set of thm:closure as carried by item (XXXIII): the standing of
# each statement and the Horn rules, each with the label of its theorem.
STATUS = {
    'HC': 'derived', 'HC_ab': 'derived', 'weil_all': 'derived',
    'weil_iq': 'derived', 'weil_triv': 'derived', 'weil_nontriv': 'derived',
    's1': 'derived', 'w4triv': 'derived', 'known': 'derived',
    'red_ab': 'open', 'red_ab_mod': 'open', 'red_weil': 'open',
    'weil_cm': 'derived', 'weil_cm_triv': 'derived',
    'weil_cm_nontriv': 'derived', 'P2_iq_s': 'open', 'P2_iq_ns': 'open',
    'P2_cm_s': 'open', 'P2_cm_ns': 'open', 'secant_all': 'open',
    'Q114': 'open', 'smooth_exists': 'open', 'smooth_vanish': 'open',
    'sing_exists': 'open', 'sing_vanish': 'open', 'base_point': 'proved',
    'reduction': 'proved', 'orbit_dense': 'proved', 'factor': 'proved',
    'class_cond': 'proved', 'cm_line': 'proved', 'ingredients': 'proved',
    'base_point_cm': 'proved', 'reduction_cm': 'proved',
    'orbit_dense_cm': 'proved', 'mar2': 'quoted', 'mar3': 'quoted',
    'mot_def': 'quoted', 'acc_ab': 'quoted', 'lef_B': 'open', 'mot': 'open',
    'vhc': 'open'}
RULES = [
    (('HC_ab', 'red_ab'), 'HC', 'ssec:closuremap'),
    (('red_ab',), 'HC_ab', 'prop:f3ishc'),
    (('HC_ab', 'red_ab_mod'), 'HC', 'prop:f3prime'),
    (('weil_all', 'red_weil'), 'HC_ab', 'ssec:closuremap'),
    (('weil_iq', 'weil_cm'), 'weil_all', 'app:albert'),
    (('weil_triv', 'weil_nontriv'), 'weil_iq', 'prop:separate'),
    (('base_point', 'reduction', 'orbit_dense', 'P2_iq_s'), 'weil_triv',
     'thm:semiregclosure'),
    (('base_point', 'reduction', 'orbit_dense', 'P2_iq_ns'), 'weil_nontriv',
     'thm:semiregclosure'),
    (('base_point_cm', 'reduction_cm', 'orbit_dense_cm', 'P2_cm_s'),
     'weil_cm_triv', 'thm:cmpropagation'),
    (('base_point_cm', 'reduction_cm', 'orbit_dense_cm', 'P2_cm_ns'),
     'weil_cm_nontriv', 'thm:cmpropagation'),
    (('weil_cm_triv', 'weil_cm_nontriv'), 'weil_cm', 'prop:cmweil'),
    (('weil_triv',), 'weil_nontriv', 'prop:descent'),
    (('weil_cm_triv',), 'weil_cm_nontriv', 'prop:descent'),
    (('weil_cm_triv',), 'weil_triv', 'prop:descent'),
    (('secant_all', 'Q114', 'factor', 'class_cond', 'ingredients',
      'reduction'), 'weil_triv', 'prop:splitgeom'),
    (('smooth_exists', 'smooth_vanish', 'cm_line'), 's1',
     'cor:cmdichotomy'),
    (('sing_exists', 'sing_vanish', 'cm_line'), 's1', 'cor:cmdichotomy'),
    (('s1', 'Q114', 'factor', 'class_cond'), 'w4triv',
     'cor:markmancondition'),
    (('mar2', 'mar3'), 'known', 'rem:markmanscope'),
    (('lef_B', 'mot'), 'HC', 'prop:lefmot'),
    (('lef_B', 'mot_def'), 'vhc', 'prop:lefvhc'),
    (('vhc', 'acc_ab'), 'HC_ab', 'thm:vhcab'),
]
BASE = {k for k, v in STATUS.items() if v in ('proved', 'quoted')}
LEAVES = sorted(k for k, v in STATUS.items() if v == 'open')


def cn(seed):
    have = set(seed)
    changed = True
    while changed:
        changed = False
        for prem, conc, _ in RULES:
            if conc not in have and all(p in have for p in prem):
                have.add(conc)
                changed = True
    return have


def minimal_sets():
    from itertools import combinations
    found = []
    for k in range(1, len(LEAVES) + 1):
        for S in combinations(LEAVES, k):
            s = set(S)
            if any(m <= s for m in found):
                continue
            if 'HC' in cn(BASE | s):
                found.append(s)
    return found


def used_rules(seed, goal='HC'):
    """the rules of a forward derivation of goal from seed, pruned to those
    the goal depends on"""
    have, steps = set(seed), []
    while goal not in have:
        fired = False
        for i, (prem, conc, _) in enumerate(RULES):
            if conc not in have and all(p in have for p in prem):
                have.add(conc)
                steps.append(i)
                fired = True
        if not fired:
            return None
    need, keep = {goal}, set()
    for i in reversed(steps):
        prem, conc, _ = RULES[i]
        if conc in need:
            keep.add(i)
            need.update(prem)
    return keep


def rule_index(prem, conc):
    for i, (p, c, _) in enumerate(RULES):
        if set(p) == set(prem) and c == conc:
            return i
    raise KeyError((prem, conc))


def ray_exit(box, toward, gap=0.07):
    """the point where the ray from the centre of box towards a point leaves
    the box enlarged by gap"""
    x0, y0, x1, y1 = box[0] - gap, box[1] - gap, box[2] + gap, box[3] + gap
    cx, cy = (box[0] + box[2]) / 2, (box[1] + box[3]) / 2
    dx, dy = toward[0] - cx, toward[1] - cy
    t = min((x1 - cx) / dx if dx > 0 else ((x0 - cx) / dx if dx < 0 else 9e9),
            (y1 - cy) / dy if dy > 0 else ((y0 - cy) / dy if dy < 0 else 9e9))
    return (cx + t * dx, cy + t * dy)


def toward(p, q, d):
    """the point at distance d from p towards q"""
    L = math.hypot(q[0] - p[0], q[1] - p[1])
    return (p[0] + d * (q[0] - p[0]) / L, p[1] + d * (q[1] - p[1]) / L)


def _check_against_code():
    """the rule set drawn here is the rule set of item (XXXIII): compare with
    code/closure_graph.py when the verification package is next to us"""
    path = os.path.join(HERE, os.pardir, "code")
    if not os.path.exists(os.path.join(path, "closure_graph.py")):
        return
    sys.path.insert(0, os.path.abspath(path))
    try:
        import closure_graph as cg
    finally:
        sys.path.pop(0)
    st = {k: v[0] for k, v in cg.STATEMENTS.items()}
    assert st == STATUS, "fig_frontier: statements differ from item (XXXIII)"
    a = sorted((tuple(sorted(r[0])), r[1], r[2]) for r in cg.RULES)
    b = sorted((tuple(sorted(r[0])), r[1], r[2]) for r in RULES)
    assert a == b, "fig_frontier: rules differ from item (XXXIII)"
    assert set(cg.IMPLIED_BY_HC) == {"red_ab", "red_ab_mod", "red_weil",
                                     "lef_B", "mot", "vhc"}


def frontier():
    F = Fig("fig_frontier",
            "The rule set of the closure theorem with the rules of the "
            "literature, as a hypergraph, and the five minimal sufficient "
            "sets, computed.")
    _check_against_code()
    OPEN, PROV, QUOT, DER = (("PClay", "WClay"), ("PGrass", "WTeal"),
                             ("PSlate", "WSlate"), ("PIndigo", "WBlue"))
    IMPLIED = {"red_ab", "red_ab_mod", "red_weil", "lef_B", "mot", "vhc"}
    sub = lambda t: r"{\scriptsize %s}" % t
    # key: (x, y, text, standing, statements of the rule set)
    N = {
        "HC": (0.00, 9.05, r"$\mathbf{HC}$\\" + sub(
            r"every Hodge class algebraic, every $X$"), DER, ["HC"]),
        "AB": (-2.95, 5.85, r"$\mathbf{HC}$ for\\abelian varieties", DER,
               ["HC_ab"]),
        "F3": (-5.55, 7.95, r"(F3)\\" + sub(r"$\mathbf{HC}$ for $X$ not "
                                           r"abelian"), OPEN, ["red_ab"]),
        "F3P": (2.75, 5.85, r"(F3$'$)\\" + sub(
            r"$\mathrm{Hdg}^{p}(X)=\mathrm{Ab}^{p}(X)$"), OPEN,
            ["red_ab_mod"]),
        "M": (5.75, 7.95, r"(M)\\" + sub(r"every Hodge class") + r"\\" +
              sub(r"motivated"), OPEN, ["mot"]),
        "L": (5.55, 3.25, r"(L)\\" + sub(r"$B(X)$ for every $X$"), OPEN,
              ["lef_B"]),
        "V": (1.00, 3.25, r"(V)\\" + sub(r"$\xi_{s}$ algebraic $\Rightarrow$ "
                                         r"$\xi_{t}$ algebraic"), OPEN,
              ["vhc"]),
        "F2": (-3.05, 3.25, r"(F2)\\" + sub(r"classes beyond Weil lines"),
               OPEN, ["red_weil"]),
        "WA": (-6.35, 3.25, r"Weil classes\\" + sub(r"every CM field"), DER,
               ["weil_all"]),
        "WS": (-6.35, 1.10, r"$\mathbf{W}(F,n,\delta_{0})$\\" + sub(
            r"$[F:\mathbb{Q}]\ge4$, split"), DER, ["weil_cm_triv"]),
        "P2": (-6.05, -1.25, r"$\mathrm{P2}_{\mathrm{split}}$\\" + sub(
            r"(P2$'$), split, $[F:\mathbb{Q}]\ge4$"), OPEN, ["P2_cm_s"]),
        "BP": (-2.95, -1.25, r"base point,\\reduction, orbit", PROV,
               ["base_point_cm", "reduction_cm", "orbit_dense_cm"]),
        "AC": (-1.05, 1.25, r"accessibility of\\Hodge classes on\\"
               r"abelian varieties", QUOT, ["acc_ab"]),
        "MD": (3.60, 1.25, r"deformation of\\motivated classes", QUOT,
               ["mot_def"]),
    }
    # the drawn rules: letter -> (premises, conclusion, junction or None)
    R = {
        "a": (["F3"], "AB", None),
        "b": (["AB", "F3"], "HC", (-2.95, 7.95)),
        "c": (["AB", "F3P"], "HC", (0.00, 7.40)),
        "d": (["L", "M"], "HC", (3.45, 7.95)),
        "e": (["L", "MD"], "V", (3.60, 3.25)),
        "f": (["V", "AC"], "AB", (-1.05, 4.55)),
        "g": (["WA", "F2"], "AB", (-4.45, 4.55)),
        "h": (["P2", "BP"], "WS", (-4.75, 0.05)),
        "i": (["WS"], "WA", None),
    }
    # each drawn rule is one rule of the set, or (i) a chain of them
    link = {}
    for k, (prem, conc, _) in R.items():
        if k == "i":
            continue
        ps = [s for p in prem for s in N[p][4]]
        link[k] = {rule_index(ps, N[conc][4][0])}
    link["i"] = {i for i, r in enumerate(RULES)
                 if r[2] in ("prop:descent", "prop:cmweil", "prop:separate",
                             "app:albert")}
    # the five minimal sufficient sets, computed, in the order of the paper
    mins = minimal_sets()
    order = [{"red_ab"}, {"lef_B", "mot"}, {"lef_B", "red_ab_mod"},
             {"vhc", "red_ab_mod"}, {"P2_cm_s", "red_weil", "red_ab_mod"}]
    assert sorted(map(sorted, mins)) == sorted(map(sorted, order)), mins
    routes = []
    for S in order:
        used = used_rules(BASE | S)
        routes.append((S, {k for k, v in link.items() if v & used}))
    assert [sorted(r[1]) for r in routes] == [
        ["a", "b"], ["d"], ["c", "e", "f"], ["c", "f"],
        ["c", "g", "h", "i"]], routes
    # every element of a minimal set but P2_split is implied by HC
    assert set().union(*order) - {"P2_cm_s"} == IMPLIED

    # ---------------------------------------------------- the main graph
    specs = {}
    for key, (x, y, t, kind, sts) in N.items():
        extra = ""
        if any(s in IMPLIED for s in sts):
            extra = ",double=%s,double distance=0.9pt" % kind[1]
        lw = 0.9 if key == "HC" else 0.6
        specs[key] = F.box_opts(kind[1], kind[0], lw=lw, extra=extra)
    JOPT = (r"circle,draw=PInk!80,fill=white,line width=0.6pt,inner sep=0.5pt,"
            r"font=\scriptsize")
    F.premeasure([(specs[k], N[k][2]) for k in N] + [(JOPT, r"$\wedge$")])
    B = {}
    for key, (x, y, t, kind, sts) in N.items():
        b = F.size(t, opts=specs[key])
        B[key] = (x + b[0], y + b[1], x + b[2], y + b[3])
    jb = F.size(r"$\wedge$", opts=JOPT)
    RJ = (jb[2] - jb[0]) / 2
    cen = {k: ((B[k][0] + B[k][2]) / 2, (B[k][1] + B[k][3]) / 2) for k in N}
    PREM = "PSlate!85"
    CONC = "PInk," + TIP
    for k, (prem, conc, J) in R.items():
        if J is None:
            p = prem[0]
            a = ray_exit(B[p], cen[conc])
            b = ray_exit(B[conc], cen[p])
            F.path([a, b], CONC, lw=0.85, tag="e" + k)
            continue
        for p in prem:
            a = ray_exit(B[p], J)
            b = toward(J, a, RJ + 0.03)
            F.path([a, b], PREM, lw=0.75, tag="e" + k)
        a = toward(J, cen[conc], RJ + 0.03)
        b = ray_exit(B[conc], J)
        F.path([a, b], CONC, lw=0.85, tag="e" + k)
    for key, (x, y, t, kind, sts) in N.items():
        F.node(x, y, t, specs[key])
    for k, (prem, conc, J) in R.items():
        if J is not None:
            F.node(J[0], J[1], r"$\wedge$", JOPT, tag="e" + k)
    # the letters of the rules, each beside its junction or its arrow
    LET = {"a": (-4.55, 6.62, None), "b": (-2.95, 8.30, None),
           "c": (-0.28, 7.62, "east"), "d": (3.45, 8.30, None),
           "e": (3.60, 3.62, None), "f": (-0.78, 4.84, "west"),
           "g": (-4.72, 4.84, "east"), "h": (-4.47, 0.30, "west"),
           "i": (-6.53, 2.18, "east")}
    for k, (x, y, an) in LET.items():
        F.text(x, y, r"(%s)" % k, "PInk", FS, anchor=an)

    # ------------------------------------------------------------- the key
    rows = [[(OPEN, r"open", False),
             (OPEN, r"open, implied by $\mathbf{HC}$", True),
             (PROV, r"proved here", False)],
            [(QUOT, r"quoted", False), (DER, r"derived", False), None]]
    for ky, row in zip((-0.72, -1.38), rows):
        x = 0.55
        for it in row:
            if it is None:
                F.node(x + 0.14, ky, r"$\wedge$", JOPT)
                F.text(x + 0.40, ky, r"rule with several premises", "PInk",
                       SS, anchor="west")
                continue
            kind, t, dbl = it
            extra = (",double=%s,double distance=0.9pt" % kind[1]) if dbl \
                else ""
            o = F.box_opts(kind[1], kind[0], size=SS, extra=extra +
                           ",anchor=west")
            F.node(x, ky, t, o)
            x += F.size(t, opts=o)[2] + 0.26

    # ---------------------------------------- the five minimal sets, a table
    COLS = ["red_ab", "lef_B", "mot", "vhc", "red_ab_mod", "red_weil",
            "P2_cm_s"]
    HDR = {"red_ab": r"(F3)", "lef_B": r"(L)", "mot": r"(M)",
            "vhc": r"(V)", "red_ab_mod": r"(F3$'$)", "red_weil": r"(F2)",
            "P2_cm_s": r"$\mathrm{P2}_{\mathrm{split}}$"}
    cw, rh = 1.25, 0.50
    xh = -5.85                       # centre of the row headers
    x0 = -4.15                       # centre of the first statement column
    xr = x0 + len(COLS) * cw + 1.05  # centre of the rules column
    ty = -2.40                       # the header row
    left, right = xh - 1.55, xr + 1.30
    F.path([(left, ty + 0.30), (right, ty + 0.30)], "PInk", lw=0.6,
           tag="tab")
    F.path([(left, ty - 0.27), (right, ty - 0.27)], "PInk", lw=0.4,
           tag="tab")
    TD = ",text height=1.7ex,text depth=0.45ex"
    F.text(xh, ty, r"minimal set", "PInk", FS, extra=TD)
    for j, s in enumerate(COLS):
        F.text(x0 + j * cw, ty, HDR[s], "PInk", FS, extra=TD)
    F.text(xr, ty, r"rules used", "PInk", FS, extra=TD)
    for n, (S, used) in enumerate(routes):
        y = ty - 0.62 - n * rh
        F.text(xh, y, r"$S_{%d}$" % (n + 1), "PInk", FS, extra=TD)
        for j, s in enumerate(COLS):
            if s in S:
                F.disc(x0 + j * cw, y, 0.075, "PInk", tag="dot%d%d" % (n, j))
            else:
                F.disc(x0 + j * cw, y, 0.022, "PRule", tag="dot%d%d" % (n, j))
        F.text(xr, y, ", ".join("(%s)" % k for k in sorted(used)), "PInk",
               FS, extra=TD)
    yb = ty - 0.62 - 4 * rh - 0.36
    F.path([(left, yb), (right, yb)], "PInk", lw=0.4, tag="tab")
    yi = yb - 0.33
    F.text(xh, yi, r"implied by $\mathbf{HC}$", "PInk", FS, extra=TD)
    for j, s in enumerate(COLS):
        F.text(x0 + j * cw, yi, r"yes" if s in IMPLIED else r"not known",
               "PInk", SS, extra=TD)
    F.path([(left, yi - 0.28), (right, yi - 0.28)], "PInk", lw=0.6,
           tag="tab")
    return F


# ============================================================ Lefschetz grid
def arc_pts(a, b, h, n=40):
    """a circular-looking arc from a to b bulging by h to the left of a->b"""
    mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
    dx, dy = b[0] - a[0], b[1] - a[1]
    L = math.hypot(dx, dy)
    nx, ny = -dy / L, dx / L
    c = (mx + 2 * h * nx, my + 2 * h * ny)
    return bezier(a, (a[0] + (c[0] - a[0]) * 0.75, a[1] + (c[1] - a[1]) * 0.75),
                  (b[0] + (c[0] - b[0]) * 0.75, b[1] + (c[1] - b[1]) * 0.75),
                  b, n)


def lefschetzgrid():
    F = Fig("fig_lefschetzgrid",
            "The summands H^p(C,R^q) of an abelian scheme of relative "
            "dimension four over a curve, the operators of the proof, and "
            "the values for a Mumford family.")
    g = 4
    D = 0.64                     # row pitch
    XC = {0: 0.0, 1: 3.00, 2: 6.00}
    WD = {0: 2.62, 1: 1.80, 2: 2.62}
    HB = 0.46
    Y = lambda q: q * D
    # Mumford: the invariants I_q are Q l^{q/2} for q even, 0 for q odd
    # (cor:mumfordlefschetz), and H^2(C,R^q) = f u H^q_(q)
    def mum(p, q):
        if q % 2:
            return r"0"
        e = q // 2
        l = "" if e == 0 else (r"\ell" if e == 1 else r"\ell^{%d}" % e)
        if p == 0:
            return r"\mathbb{Q}" + (r"\,%s" % l if l else "")
        return r"\mathbb{Q}\," + l + " f"
    # the diagonals k = p + q, behind the boxes
    for k in range(0, 2 * g + 3):
        pts = [(XC[p], Y(k - p)) for p in (0, 1, 2) if 0 <= k - p <= 2 * g]
        if len(pts) >= 2:
            F.path(pts, "PRule,dash pattern=on 1.4pt off 1.4pt", lw=0.5,
                   tag="diag")
    # the labels k of the diagonals, in the first gap, above each line
    gx0 = XC[0] + WD[0] / 2
    gx1 = XC[1] - WD[1] / 2
    xm = (gx0 + gx1) / 2
    for k in range(1, 2 * g + 1):
        yl = Y(k) + (Y(k - 1) - Y(k)) * (xm - XC[0]) / (XC[1] - XC[0])
        F.text(xm, yl + 0.25, r"$%d$" % k, "PSlate", SS)
    F.text(xm, -0.08, r"$k$", "PSlate", FS)
    # the boxes
    for p in (0, 1, 2):
        for q in range(2 * g + 1):
            inv = p in (0, 2) and q % 2 == 0
            fill = "WOchre" if inv else ("WSlate" if p == 1 else "WBlue")
            draw = "POchre" if inv else "PSlate"
            t = r"$H^{%d}(C,R^{%d})$" % (p, q)
            if p != 1:
                t += r"\enspace\textcolor{PMag}{$%s$}" % mum(p, q)
            o = F.box_opts(fill, draw, lw=0.5, size=SS, w=WD[p], h=HB,
                           sharp=False)
            o = o.replace("inner sep=2.6pt", "inner sep=1pt")
            F.node(XC[p], Y(q), t, o, allow=("diag",))
    # the axis q = g of hard Lefschetz on the fibres, outside the columns
    xl = XC[0] - WD[0] / 2
    xr = XC[2] + WD[2] / 2
    F.path([(xl - 0.30, Y(g)), (xl - 0.06, Y(g))],
           "PMag,dash pattern=on 2.4pt off 1.6pt", lw=0.6, tag="axis")
    F.path([(xr + 0.06, Y(g)), (xr + 0.36, Y(g))],
           "PMag,dash pattern=on 2.4pt off 1.6pt", lw=0.6, tag="axis")
    F.text(xr + 0.42, Y(g), r"$q=g$", "PMag", SS, anchor="west")
    # row headers: the eigenvalue of [2]^*, the rank of R^q, and H_rel
    HX = [xl - 2.45, xl - 1.50, xl - 0.62]
    for q in range(2 * g + 1):
        F.text(HX[0], Y(q), r"$2^{%d}$" % q, "PInk", SS)
        F.text(HX[1], Y(q), r"$%d$" % math.comb(2 * g, q), "PInk", SS)
        F.text(HX[2], Y(q), r"$%+d$" % (q - g) if q != g else r"$0$",
               "PInk", SS)
    ytop = Y(2 * g) + 0.62
    F.text(HX[0], ytop, r"$[2]^{*}$", "PInk", FS)
    F.text(HX[1], ytop, r"$\mathrm{rk}\,R^{q}$", "PInk", FS)
    F.text(HX[2], ytop, r"$H_{\mathrm{rel}}$", "PInk", FS)
    # column footers
    foot = [r"$H^{q}_{(q)}\cong I_{q}$", r"$L_{C}=\Lambda_{C}=0$",
            r"$f\cup H^{q}_{(q)}$"]
    for p in (0, 1, 2):
        F.text(XC[p], -0.62, r"$p=%d$" % p, "PInk", FS)
        F.text(XC[p], -1.04, r"$H_{C}=%s$" % ("-1", "0", "+1")[p], "PInk",
               SS)
        F.text(XC[p], -1.50, foot[p], "PSlate", SS)
    # the relative operators, on the right of the last column
    qa, qb = 5, 7
    xo = xr + 0.26
    F.path([(xo, Y(qa)), (xo, Y(qb))], "PTeal," + STIP, lw=0.8, tag="Lrel")
    F.text(xo + 0.08, Y(qa + 1), r"$L_{\mathrm{rel}}$", "PTeal",
           SS, anchor="west", tag="Lrel")
    xo2 = xo + F.size(r"$L_{\mathrm{rel}}$", "PTeal", SS,
                      anchor="west")[2] + 0.36
    F.path([(xo2, Y(qb)), (xo2, Y(qa))], "PTeal," + STIP, lw=0.8,
           tag="Lamrel")
    F.text(xo2 + 0.08, Y(qa + 1), r"$\Lambda_{\mathrm{rel}}$", "PTeal", SS,
           anchor="west", tag="Lamrel")
    # the base operators over the top row
    yt = Y(2 * g) + HB / 2 + 0.10
    a = (XC[0] + 0.55, yt)
    b = (XC[2] - 0.55, yt)
    F.path(arc_pts(a, b, 0.55), "POchre," + STIP, lw=0.9, tag="LC")
    F.path(arc_pts((XC[2] + 0.55, yt), (XC[0] - 0.55, yt), -1.00),
           "POchre," + STIP, lw=0.9, tag="LC")
    F.text(XC[1], yt + 0.84, r"$L_{C}=\cup\,mf$", "POchre", SS)
    F.text(XC[1], yt + 1.72, r"$\Lambda_{C}=\sum_{j,k}(M^{-1})_{kj}\,"
           r"b_{k}\times a_{j}$", "POchre", SS)
    # Step 6 of the proof
    F.boxed(XC[1], yt + 2.55,
            r"$\Lambda=\Lambda_{\mathrm{rel}}+\Lambda_{C}$,\quad "
            r"$\Lambda_{\mathrm{rel}}=D^{-1}(\,\cdot\,)\star\gamma$,\quad "
            r"$\gamma=\ell^{g-1}/(g-1)!$\\[1pt]"
            r"$[L_{W},\Lambda]=H_{\mathrm{rel}}+H_{C}=(q-g)+(p-1)="
            r"\deg-\dim W$", "WSlate", "PSlate", lw=0.5, size=SS)
    return F


# ================================================================== rigidity
import re as _re
import random as _random
from fractions import Fraction as _Fr

_C = _re.compile(r"\((-?\d+(?:\.\d*)?),(-?\d+(?:\.\d*)?)\)")


def shift_tikz(s, dx, dy):
    return _C.sub(lambda m: "(%.4f,%.4f)" % (float(m.group(1)) + dx,
                                             float(m.group(2)) + dy), s)


def weight_blocks():
    """sp^{-1,1} for Y = X x X under the torus of the first two factors:
    H^{1,0}(Y) has the weights (+-1,+-1), each twice, and sp^{-1,1} is its
    symmetric square; the diagonal Siegel space has the symmetric square of
    one copy."""
    W = [(a, b) for a in (1, -1) for b in (1, -1)]
    two = W + W
    full, diag = {}, {}
    for i in range(len(two)):
        for j in range(i, len(two)):
            m = (two[i][0] + two[j][0], two[i][1] + two[j][1])
            full[m] = full.get(m, 0) + 1
    for i in range(len(W)):
        for j in range(i, len(W)):
            m = (W[i][0] + W[j][0], W[i][1] + W[j][1])
            diag[m] = diag.get(m, 0) + 1
    return full, diag


def rigidity():
    F = Fig("fig_rigidity",
            "The tangent space at Y = X_c x X_c of the Hodge locus of an "
            "exceptional class, block by block, and the scalars of the proof "
            "of the rigidity theorem.")
    from render3d import Camera, Scene
    full, diag = weight_blocks()
    assert sum(full.values()) == 36 and sum(diag.values()) == 10
    # at an exceptional class only kappa, in the block of weight (0,0); for
    # alpha rational the class is invariant under Sp(V) acting diagonally, so
    # the tangent space of the diagonal Siegel space, the symmetric square of
    # one copy of H^{1,0}, lies in that of the Hodge locus
    K1 = {m: (1 if m == (0, 0) else 0) for m in full}
    K10 = dict(diag)
    assert all(K1[m] <= K10[m] <= full[m] for m in full)
    # ------------------------------------------------ the columns, in 3D
    S, E = 1.45, 0.60                 # lattice pitch, cube edge
    COL = [("PClay", 0.30, 0.48), ("PTeal", 0.30, 0.48),
           ("PSlate", 0.78, 0.20)]
    EDGE = "PInk!55,line width=0.25pt"
    az, el, dist = math.radians(-128.0), math.radians(31.0), 34.0
    tgt = (0.0, 0.0, 1.9)
    eye = (tgt[0] + dist * math.cos(el) * math.cos(az),
           tgt[1] + dist * math.cos(el) * math.sin(az),
           tgt[2] + dist * math.sin(el))

    def build(scale):
        cam = Camera(eye=eye, target=tgt, focal=dist, scale=scale)
        sc = Scene(cam, light=(-0.45, -0.75, 0.95))
        R = 1.55 * S
        pr = lambda p: "(%.4f,%.4f)" % cam.project(p)[0]
        sc.add(1e9, "  \\fill[PSlate!4!white] %s -- %s -- %s -- %s -- cycle;\n"
               % (pr((-R, -R, 0)), pr((R, -R, 0)), pr((R, R, 0)),
                  pr((-R, R, 0))))
        for t in (-1, 0, 1):
            for a_, b_ in (((t * S, -R, 0), (t * S, R, 0)),
                           ((-R, t * S, 0), (R, t * S, 0))):
                sc.add(1e9 - 1, "  \\draw[PRule,line width=0.45pt] %s -- %s;"
                       "\n" % (pr(a_), pr(b_)))
        for (m1, m2), d in full.items():
            x, y = m1 / 2 * S, m2 / 2 * S
            for k in range(d):
                top = d - 1 - k          # 0 for the top cube
                if top < K1[(m1, m2)]:
                    c = COL[0]
                elif top < K10[(m1, m2)]:
                    c = COL[1]
                else:
                    c = COL[2]
                sc.box((x, y, E * (k + 0.5)), (E, E, E), base=c[0],
                       ambient=c[1], diffuse=c[2], edge_style=EDGE)
        return cam, sc.emit()
    cam, body = build(1.0)
    xs = [float(a) for a, b in _C.findall(body)]
    cam, body = build(7.0 / (max(xs) - min(xs)))
    xs = [float(a) for a, b in _C.findall(body)]
    ys = [float(b) for a, b in _C.findall(body)]
    dx, dy = -min(xs), -min(ys)
    body = shift_tikz(body, dx, dy)
    F.scene(body, tag="cubes")
    P = lambda p: (cam.project(p)[0][0] + dx, cam.project(p)[0][1] + dy)
    R = 1.55 * S
    for t in (-1, 0, 1):
        q = P((t * S, -R - 0.42, 0))
        F.text(q[0], q[1], r"$%s$" % ("-2", "0", "+2")[t + 1], "PInk", SS)
        q = P((-R - 0.42, t * S, 0))
        F.text(q[0], q[1], r"$%s$" % ("-2", "0", "+2")[t + 1], "PInk", SS)
    q = P((0, -R - 1.15, 0))
    F.text(q[0], q[1], r"$\mu_{1}$", "PInk", FS)
    q = P((-R - 1.15, 0, 0))
    F.text(q[0], q[1], r"$\mu_{2}$", "PInk", FS)
    W3 = max(xs) + dx
    top = max(ys) + dy
    # ------------------------------------------------ legend, right of the cubes
    items = [(COL[0], r"$\omega_{a}$ exceptional: $\mathbb{C}\kappa$, "
                      r"$\dim 1$"),
             (COL[1], r"$\alpha\in\mathbb{Q}$: contains $T_{Y}\{X'\times "
                      r"X'\}$, $\dim 10$"),
             (COL[2], r"$T_{Y}\mathfrak{S}=\mathfrak{sp}^{-1,1}$: "
                      r"$\dim 36$")]
    lx = W3 + 1.10
    ly = top - 1.30
    F.text(lx, ly + 0.55, r"tangent space at $Y$ of the Hodge locus of "
           r"$\omega_{a}$", "PSlate", SS, anchor="west")
    for n, (c, t) in enumerate(items):
        yy = ly - 0.46 * n
        F.rect(lx, yy - 0.12, lx + 0.24, yy + 0.12, "%s!%d!white" % (
            c[0], 62 if n < 2 else 18), draw="PInk!55", lw=0.3, tag="leg")
        F.text(lx + 0.34, yy, t, "PInk", SS, anchor="west")
    F.text(lx, ly - 1.62, r"blocks: weights $(\mu_{1},\mu_{2})$ of a maximal"
           r"\\torus of $\mathrm{SL}(V_{1})\times\mathrm{SL}(V_{2})$",
           "PSlate", SS, anchor="west", extra=",align=left")
    # ------------------------------------------------ the table of scalars
    rows = [r"$H^{1}(T_{Y})$\\diagonal", r"$H^{1}(T_{Y})$\\mixed",
            r"$H^{0}(\bigwedge^{2}T_{Y})$\\mixed"]
    cols = [r"$E_{3}^{-}$, $\dim 1$", r"$E_{13}^{-}$, $\dim 3$",
            r"$E_{23}^{-}$, $\dim 3$", r"$E_{123}^{-}$, $\dim 9$"]
    cells = [
        [r"$b_{11}=b_{22}$: $\kappa$", r"$a_{1}^{2}-a_{3}^{2}$",
         r"$a_{1}^{2}-a_{2}^{2}$", r"$a_{1},a_{2},a_{3}$\\distinct"],
        [r"$\tfrac32(a_{2}-a_{3})$", r"$-\tfrac12(a_{2}+3a_{3})$",
         r"$\tfrac12(3a_{2}+a_{3})$", r"$-\tfrac12(a_{2}-a_{3})$"],
        [r"$\tfrac14(a_{0}+9a_{1}$\\$-3a_{2}-3a_{3})$",
         r"$\tfrac14(a_{0}-3a_{1}$\\$+a_{2}-3a_{3})$",
         r"$\tfrac14(a_{0}-3a_{1}$\\$-3a_{2}+a_{3})$",
         r"$\tfrac14L_{0}(a)$"]]
    rw, cw, ch = 2.55, 2.95, 1.02
    tx0 = 0.10
    ty0 = -0.95
    for j, c in enumerate(cols):
        x = tx0 + rw + (j + 0.5) * cw
        F.text(x, ty0 + 0.30, c, "PInk", SS)
    for i, r in enumerate(rows):
        y = ty0 - (i + 0.5) * ch
        F.text(tx0 + rw / 2, y, r, "PInk", SS)
        for j in range(4):
            x = tx0 + rw + (j + 0.5) * cw
            hot = (i, j) == (0, 0)
            l0 = (i, j) == (2, 3)
            fill = "WClay" if hot else ("WTeal" if l0 else "WOchre")
            draw = "PClay" if hot else ("PTeal" if l0 else "POchre")
            F.node(x, y, cells[i][j],
                   F.box_opts(fill, draw, lw=0.5, size=SS, w=cw - 0.12,
                              h=ch - 0.12)
                   .replace("inner sep=2.6pt", "inner sep=1.2pt"))
    note = (r"$H^{0,2}$ and the unmixed pieces of $\bigwedge^{2}T_{Y}$: the "
            r"block $K=(a_{2},a_{3})$ of $P_{a}$.\quad At a rational "
            r"exceptional class no entry vanishes, by the lemma on conjugates,"
            r"\\except $b_{11}-b_{22}$, which leaves $\kappa$, and $L_{0}$, "
            r"which can be made nonzero by adding a multiple of $\pi_{0}$.")
    F.boxed(tx0 + (rw + 4 * cw) / 2, ty0 - 3 * ch - 0.62, note, "WSlate",
            "PSlate", lw=0.5, size=SS)
    return F


# ================================================================== bypass
def wedge_pts(rx, ry, r0, r1, a0, a1, n=60):
    """an annular sector of the ellipse (rx, ry), radii r0 < r1 (fractions),
    angles a0 > a1 in degrees, clockwise"""
    out = []
    for k in range(n + 1):
        t = math.radians(a0 + (a1 - a0) * k / n)
        out.append((r1 * rx * math.cos(t), r1 * ry * math.sin(t)))
    for k in range(n + 1):
        t = math.radians(a1 + (a0 - a1) * k / n)
        out.append((r0 * rx * math.cos(t), r0 * ry * math.sin(t)))
    return out


def bypass():
    F = Fig("fig_bypass",
            "The ten routes to the Mumford target that avoid the Lefschetz "
            "standard conjecture, with the status of each.")
    BLK, SPC, ONE = ("PClay", "WClay"), ("PGrass", "WTeal"), ("PIndigo",
                                                             "WBlue")
    rx, ry = 5.55, 3.40
    # (item of rem:bypassaudit, position, title, obstruction, kind, mark)
    R = [
        (1, (0.00, 3.40), r"degeneration", r"$C$ compact: no cusp", BLK,
         "bar"),
        (2, (3.95, 2.72), r"larger Hodge locus",
         r"tangent space $\mathbb{C}\kappa$", BLK, "bar"),
        (3, (5.55, 0.98), r"Hochschild deformations",
         r"$\mathrm{Ann}_{HH^{2}(Y)}(\omega)=\mathbb{C}\kappa$", BLK, "bar"),
        (4, (5.55, -0.98), r"built from line bundles",
         r"$\mathrm{ch}(E)$ is $L(X)$-invariant", BLK, "bar"),
        (5, (5.00, -2.72), r"twistor lines",
         r"none keeps $\omega$ of Hodge type", BLK, "bar"),
        (6, (0.00, -3.30), r"CM points, isogenies",
         r"algebraic at every CM point\\enough iff degrees bounded", SPC,
         "dash"),
        (7, (-5.00, -2.72), r"reduction modulo $p$",
         r"cycles at every closed point\\enough iff bounded on a dense set",
         SPC, "dash"),
        (8, (-5.55, -0.98), r"semiregularity",
         r"one $E$, $\dim\mathrm{Ext}^{2}(E,E)=119$", ONE, "arrow"),
        (9, (-5.55, 0.98), r"Kuga--Satake",
         r"one K3 surface, $\rho(S_{\lambda})=13$", ONE, "arrow"),
        (10, (-3.95, 2.72), r"motivated classes",
         r"$\Leftrightarrow B(W\times_{C}W)$", ONE, "both"),
    ]
    ang = {k: math.degrees(math.atan2(p[1] / ry, p[0] / rx))
           for k, p, *_ in R}

    def mid(i, j):
        a_, b_ = ang[i], ang[j]
        if b_ > a_:
            b_ -= 360
        return (a_ + b_) / 2
    s1, s2, s3 = mid(10, 1) + 360, mid(5, 6), mid(7, 8)
    s1 = s1 if s1 < 180 else s1 - 360
    for (a0, a1, c) in ((s1, s2, "WClay!55"), (s2, s3, "WTeal!70"),
                        (s3, s1 - 360, "WBlue!60")):
        F.fill(wedge_pts(rx, ry, 0.47, 1.20, a0, a1), c, tag="bg")
    # the target
    tb = F.boxed(0.0, 0.0, r"$\omega_{t}$ algebraic on $X_{t}\times X_{t}$"
                 r"\\{\scriptsize $t\in C$ very general}", "WOchre", "POchre",
                 lw=1.0, allow=("bg",))
    for k, (cx, cy), title, obs, kind, mark in R:
        txt = r"\textbf{(%d)} %s" % (k, title) + "".join(
            r"\\{\scriptsize %s}" % s for s in obs.split(r"\\"))
        bb = F.boxed(cx, cy, txt, kind[1], kind[0], lw=0.7, allow=("bg",))
        a = ray_exit(bb, (0, 0), gap=0.06)
        b = ray_exit(tb, (cx, cy), gap=0.08)
        tag = "s%d" % k
        if mark == "bar":
            # blocked: the spoke stops at a bar short of the target
            L = math.hypot(a[0] - b[0], a[1] - b[1])
            m = toward(b, a, 0.40)
            F.path([a, m], kind[0], lw=0.9, tag=tag)
            ux, uy = (a[0] - b[0]) / L, (a[1] - b[1]) / L
            F.path([(m[0] - 0.17 * uy, m[1] + 0.17 * ux),
                    (m[0] + 0.17 * uy, m[1] - 0.17 * ux)], kind[0], lw=1.6,
                   tag=tag)
        elif mark == "dash":
            F.path([a, b], kind[0] + ",dash pattern=on 3pt off 2pt," + TIP,
                   lw=0.9, tag=tag)
        elif mark == "arrow":
            F.path([a, b], kind[0] + "," + TIP, lw=0.9, tag=tag)
        else:
            F.path([a, b], kind[0] + ",{Stealth[length=5pt,width=4pt]}-"
                   "{Stealth[length=5pt,width=4pt]}", lw=0.9, tag=tag)
    # legend, two rows
    leg = [(BLK, "bar", r"closed off by a theorem"),
           (SPC, "dash", r"works at special points only"),
           (ONE, "arrow", r"reduced to one open statement"),
           (ONE, "both", r"equivalent to the target")]
    for n, (kind, mark, t) in enumerate(leg):
        x = -4.9 + (n % 2) * 5.4
        ly = -ry - 1.15 - 0.45 * (n // 2)
        if mark == "bar":
            F.path([(x, ly), (x + 0.50, ly)], kind[0], lw=0.9, tag="leg")
            F.path([(x + 0.50, ly - 0.15), (x + 0.50, ly + 0.15)], kind[0],
                   lw=1.6, tag="leg")
        elif mark == "dash":
            F.path([(x, ly), (x + 0.62, ly)], kind[0] + ",dash pattern=on "
                   "3pt off 2pt," + TIP, lw=0.9, tag="leg")
        elif mark == "both":
            F.path([(x, ly), (x + 0.62, ly)], kind[0] + ",{Stealth[length="
                   "5pt,width=4pt]}-{Stealth[length=5pt,width=4pt]}", lw=0.9,
                   tag="leg")
        else:
            F.path([(x, ly), (x + 0.62, ly)], kind[0] + "," + TIP, lw=0.9,
                   tag="leg")
        F.text(x + 0.78, ly, t, "PInk", SS, anchor="west")
    return F


# =============================================================== propagation
def shade_poly(sc, P, base, ambient, diffuse, normal=None):
    """one facet with the Lambert shading of render3d"""
    from render3d import cross, sub, unit, dot, norm, smul
    c = tuple(sum(p[k] for p in P) / len(P) for k in range(3))
    n = normal if normal is not None else cross(sub(P[1], P[0]),
                                                sub(P[-1], P[0]))
    if norm(n) < 1e-12:
        return
    n = unit(n)
    if dot(n, sc.cam.towards(c)) < 0:
        n = smul(-1.0, n)
    lam = max(0.0, dot(n, sc.light))
    pct = int(max(4, min(96, round(100 * (1.0 - ambient - diffuse * lam)))))
    pts, depths = zip(*[sc.cam.project(p) for p in P])
    sc.add(sum(depths) / len(depths),
           "  \\path[draw=%s!%d!white,line width=0.1pt,fill=%s!%d!white] %s "
           "-- cycle;\n" % (base, pct, base, pct,
                            " -- ".join("(%.3f,%.3f)" % q for q in pts)))


class Torus:
    """a torus with an elliptic tube: centre, major radius R, tube radii
    (rh, rv); axis 'z' (lying flat) or 'y' (standing, facing the camera)"""

    def __init__(self, centre, R, rh, rv, axis="z"):
        self.c, self.R, self.rh, self.rv, self.axis = centre, R, rh, rv, axis

    def pt(self, u, v, off=0.0):
        rr = self.R + (self.rh + off) * math.cos(v)
        a, b, h = rr * math.cos(u), rr * math.sin(u), (self.rv + off) * \
            math.sin(v)
        cx, cy, cz = self.c
        if self.axis == "z":
            return (cx + a, cy + b, cz + h)
        return (cx + a, cy + h, cz + b)

    def normal(self, u, v):
        a = math.cos(v) * math.cos(u) / self.rh
        b = math.cos(v) * math.sin(u) / self.rh
        h = math.sin(v) / self.rv
        return (a, b, h) if self.axis == "z" else (a, h, b)

    def value(self, p):
        x, y, z = p[0] - self.c[0], p[1] - self.c[1], p[2] - self.c[2]
        if self.axis != "z":
            y, z = z, y
        d = math.hypot(x, y) - self.R
        return (d / self.rh) ** 2 + (z / self.rv) ** 2 - 1.0

    def draw(self, sc, nu, nv, base, ambient, diffuse, minus=None):
        """the part outside the torus minus, refined along the junction;
        back faces culled"""
        from render3d import dot, unit

        def rec(ua, ub, va, vb, lev):
            P = [self.pt(ua, va), self.pt(ub, va), self.pt(ub, vb),
                 self.pt(ua, vb)]
            um, vm = (ua + ub) / 2, (va + vb) / 2
            if minus is not None:
                ins = [minus.value(p) < 0 for p in P]
                cin = minus.value(self.pt(um, vm)) < 0
                if all(ins) and cin:
                    return
                if any(ins) and lev < 3:
                    for a_, b_, c_, d_ in ((ua, um, va, vm), (um, ub, va, vm),
                                           (um, ub, vm, vb), (ua, um, vm, vb)):
                        rec(a_, b_, c_, d_, lev + 1)
                    return
                if cin:
                    return
            pc = self.pt(um, vm)
            n = unit(self.normal(um, vm))
            if dot(n, sc.cam.towards(pc)) < -0.08:
                return
            shade_poly(sc, P, base, ambient, diffuse, normal=n)
        for i in range(nu):
            for j in range(nv):
                rec(2 * math.pi * i / nu, 2 * math.pi * (i + 1) / nu,
                    2 * math.pi * j / nv, 2 * math.pi * (j + 1) / nv, 0)


def propagation():
    F = Fig("fig_propagation",
            "Propagation of algebraicity along a compact Shimura curve under "
            "the Lefschetz standard conjecture for the total space.")
    from render3d import Camera, Scene, dot, unit
    R, RH, RV, CX = 1.78, 0.74, 0.40, 2.02
    A = Torus((-CX, 0.0, 0.0), R, RH, RV)
    B = Torus((CX, 0.0, 0.0), R, RH, RV)
    az, el, dist = math.radians(-97.0), math.radians(31.0), 34.0
    tgt = (0.0, 0.0, 1.35)
    eye = (tgt[0] + dist * math.cos(el) * math.cos(az),
           tgt[1] + dist * math.cos(el) * math.sin(az),
           tgt[2] + dist * math.sin(el))
    # the three points: a CM point c, a Hecke translate c', and t
    pts = {"c": (A, math.radians(-118)), "cp": (A, math.radians(-38)),
           "t": (B, math.radians(-70))}
    H, RR, rr = 2.95, 0.52, 0.17
    COLS = {"c": ("PGrass", 0.42, 0.50), "cp": ("PGrass", 0.50, 0.45),
            "t": ("PClay", 0.42, 0.50)}

    def build(scale):
        cam = Camera(eye=eye, target=tgt, focal=dist, scale=scale)
        sc = Scene(cam, light=(-0.45, -0.60, 0.85))
        A.draw(sc, 64, 26, "PBlue", 0.52, 0.44, minus=B)
        B.draw(sc, 64, 26, "PBlue", 0.52, 0.44, minus=A)
        info = {}
        for key, (T, u) in pts.items():
            base = T.pt(u, math.pi / 2)
            ctr = (base[0], base[1], base[2] + H)
            ring = Torus(ctr, RR, rr, rr, axis="y")
            col = COLS[key]
            ring.draw(sc, 40, 14, col[0], col[1], col[2])
            # the stalk, in short pieces so that it sorts with the facets
            top = (base[0], base[1], ctr[2] - RR - rr)
            n = 18
            for k in range(n):
                p = [tuple(base[m] + (top[m] - base[m]) * (k + s) / n
                           for m in range(3)) for s in (0, 1)]
                sc.polyline(p, "%s,line width=0.7pt" % col[0], priority=2)
            # the class on the fibre: the front longitude of the ring
            cyc = [ring.pt(2 * math.pi * k / 72, -math.pi / 2, off=0.012)
                   for k in range(73)]
            for k in range(72):
                sc.polyline([cyc[k], cyc[k + 1]], "%s!80!black,line width="
                            "1.3pt" % col[0], priority=3)
            info[key] = (base, ctr, ring)
        # CM points: hollow dots on the visible part of the base
        import random
        rnd = random.Random(11)
        cms = []
        while len(cms) < 46:
            T, O = (A, B) if rnd.random() < 0.5 else (B, A)
            u = rnd.uniform(0, 2 * math.pi)
            v = rnd.uniform(math.radians(15), math.radians(165))
            p = T.pt(u, v, off=0.02)
            if O.value(p) < 0.15:
                continue
            if dot(unit(T.normal(u, v)), cam.towards(p)) < 0.35:
                continue
            if any(math.dist(p, q) < 0.42 for q in cms):
                continue
            if any(math.dist(p, info[k][0]) < 0.75 for k in info):
                continue
            cms.append(p)
        solids = [A, B] + [info[k][2] for k in info]

        def visible(p):
            """no solid meets the segment from p to the eye"""
            for k in range(1, 160):
                s = 0.03 + 0.06 * k
                q = tuple(p[m] + s * (eye[m] - p[m]) / dist for m in range(3))
                if any(T.value(q) < 0 for T in solids):
                    return False
            return True
        # the dots lie on the surface and are drawn last, if visible and
        # clear of the stalks
        def segdist(p, a_, b_):
            ax, ay = a_
            bx_, by_ = b_
            L2 = (bx_ - ax) ** 2 + (by_ - ay) ** 2
            t = max(0.0, min(1.0, ((p[0] - ax) * (bx_ - ax) +
                                   (p[1] - ay) * (by_ - ay)) / L2))
            return math.hypot(p[0] - ax - t * (bx_ - ax),
                              p[1] - ay - t * (by_ - ay))
        stalks = [(cam.project(info[k][0])[0],
                   cam.project((info[k][0][0], info[k][0][1],
                                info[k][1][2]))[0]) for k in info]
        for p in cms:
            if not visible(p):
                continue
            (x, y), d = cam.project(p)
            if any(segdist((x, y), s0, s1) < 0.13
                   for s0, s1 in stalks):
                continue
            sc.add(-1e6, "  \\draw[PGrass,fill=white,line width=0.45pt] "
                   "(%.3f,%.3f) circle (0.045);\n" % (x, y), 3)
        for key, (base, ctr, ring) in info.items():
            assert visible(base)
            (x, y), d = cam.project(base)
            sc.add(-1e6, "  \\fill[%s] (%.3f,%.3f) circle (0.065);\n"
                   % (COLS[key][0], x, y), 3)
        return cam, sc.emit(), info, cms
    cam, body, info, cms = build(1.0)
    xs = [float(a) for a, b in _C.findall(body)]
    cam, body, info, cms = build(9.2 / (max(xs) - min(xs)))
    xs = [float(a) for a, b in _C.findall(body)]
    ys = [float(b) for a, b in _C.findall(body)]
    dx, dy = -min(xs) + 2.05, -min(ys) + 1.55

    def tagger(st):
        if "circle (0.045)" in st:
            return "cm"
        if "circle (0.065)" in st:
            return "pt"
        if "line width=0.7pt" in st:
            return "stalk"
        if "line width=1.3pt" in st:
            return "cycle"
        if "PBlue" in st:
            return "base"
        return "fibre"
    body = shift_tikz(body, dx, dy)
    F.scene(body, tagger=tagger)
    P = lambda p: (cam.project(p)[0][0] + dx, cam.project(p)[0][1] + dy)
    X0, X1 = min(xs) + dx, max(xs) + dx
    Y0, Y1 = min(ys) + dy, max(ys) + dy
    # the projected extent of each ring
    ext = {}
    for key, (base, ctr, ring) in info.items():
        q = [P(ring.pt(2 * math.pi * i / 24, 2 * math.pi * j / 12))
             for i in range(24) for j in range(12)]
        ext[key] = (min(p[0] for p in q), min(p[1] for p in q),
                    max(p[0] for p in q), max(p[1] for p in q))
    # -- the global class and the two maps
    xm = (ext["c"][2] + ext["t"][0]) / 2
    ub = F.boxed(xm, Y1 + 0.95,
                 r"$u=m\,\Lambda_{C}(i_{c*}y)\in H^{q}_{(q)}(W)$\\"
                 r"{\scriptsize algebraic when $B(W)$ holds;\enspace "
                 r"$f\cup u=i_{c*}y$}\\{\scriptsize "
                 r"$\int_{W_{c}}u\cup w=\int_{W_{c}}y\cup w$ for every "
                 r"invariant $w$}", "WOchre", "POchre", lw=0.8)
    ec, et = ext["c"], ext["t"]
    a = ((ec[0] + ec[2]) / 2 - 0.10, ec[3] + 0.08)
    b = (ub[0] - 0.08, (ub[1] + ub[3]) / 2)
    F.path(bezier(a, (a[0], b[1] - 0.10), (b[0] - 0.80, b[1]), b),
           "PGrass," + TIP, lw=1.0, tag="gysin")
    F.text(a[0] - 0.22, (a[1] + b[1]) / 2 + 0.05, r"$i_{c*}$, then "
           r"$\Lambda_{C}$", "PGrass", SS, anchor="east")
    a2 = (ub[2] + 0.08, (ub[1] + ub[3]) / 2)
    b2 = ((et[0] + et[2]) / 2 + 0.10, et[3] + 0.08)
    F.path(bezier(a2, (a2[0] + 0.80, a2[1]), (b2[0], a2[1] - 0.10), b2),
           "PClay," + TIP, lw=1.0, tag="restr")
    F.text(b2[0] + 0.24, (a2[1] + b2[1]) / 2 + 0.05, r"restrict: "
           r"$u|_{W_{t}}=\xi_{t}$", "PClay", SS, anchor="west")
    # -- the isogeny between the two CM fibres
    ep = ext["cp"]
    a3 = (ec[2] + 0.07, (ec[1] + ec[3]) / 2 + 0.05)
    b3 = (ep[0] - 0.07, (ep[1] + ep[3]) / 2 + 0.05)
    F.path(bezier(a3, (a3[0] + 0.25, a3[1] + 0.42), (b3[0] - 0.25,
                  b3[1] + 0.42), b3),
           "PGrass,dash pattern=on 2.4pt off 1.6pt," + STIP, lw=0.8,
           tag="isog")
    F.text((a3[0] + b3[0]) / 2, max(a3[1], b3[1]) + 0.52, r"isogeny",
           "PGrass", SS)
    # -- names of the fibres and of the classes
    F.text(ec[0] - 0.10, (ec[1] + ec[3]) / 2, r"$y$ on $W_{c}$", "PGrass", FS,
           anchor="east")
    F.text(ep[2] + 0.10, (ep[1] + ep[3]) / 2 + 0.12, r"$y'$ on $W_{c'}$",
           "PGrass", FS, anchor="west")
    F.text(et[2] + 0.10, (et[1] + et[3]) / 2, r"$\xi_{t}$ on $W_{t}$",
           "PClay", FS, anchor="east" if False else "west")
    # -- the base points
    for key, name, col in (("c", r"$c$", "PGrass"), ("cp", r"$c'$", "PGrass"),
                           ("t", r"$t$", "PClay")):
        q = P(info[key][0])
        F.text(q[0] + 0.14, q[1] - 0.14, name, col, FS, anchor="north west",
               allow=("base",))
    # -- the curve and the CM points
    F.text(X0 - 0.05, Y0 + 0.55, r"$C=\Gamma\backslash\mathfrak{H}$"
           r"\\{\scriptsize compact}", "PInk", FS, anchor="east")
    F.disc(X1 - 1.85, Y0 - 0.40, 0.06, "white", draw="PGrass", lw=0.45)
    F.text(X1 - 1.70, Y0 - 0.40, r"CM points: dense, countable", "PGrass",
           SS, anchor="west")
    # -- the spreading lemma
    F.boxed((X0 + X1) / 2, Y0 - 1.25,
            r"$\xi_{t}$ algebraic for uncountably many $t$ "
            r"$\Longrightarrow$ $d\,\xi_{t}$ algebraic for every $t\in C$\\"
            r"{\scriptsize the CM points and their Hecke orbits are "
            r"countable, so they alone never suffice}", "WSlate", "PSlate",
            lw=0.6)
    return F


# ================================================================ Hodge count
def hodge_counts():
    """Hodge classes of Y = X x X for a Mumford fourfold X, degree by degree:
    the invariants of the Hodge group in wedge^{2p}(V + V), V the tensor
    product of the three standard representations of SL(2)^3 over C.  At a
    point that is not CM the group is SL(2)^3, and the invariants are counted
    by the Weyl character formula (for SL(2): m(0) - m(2)); at a CM point it
    is a maximal torus, and they are the monomials of weight zero."""
    from itertools import product
    from collections import Counter
    W = list(product((1, -1), repeat=3))
    V2 = W + W
    mult = [Counter() for _ in range(len(V2) + 1)]
    for mask in range(1 << len(V2)):
        s = [0, 0, 0]
        k = 0
        for i in range(len(V2)):
            if mask >> i & 1:
                k += 1
                for j in range(3):
                    s[j] += V2[i][j]
        mult[k][tuple(s)] += 1
    gen, cm = [], []
    for k in range(0, len(V2) + 1, 2):
        m = mult[k]
        gen.append(sum((-1) ** sum(e) * m[tuple(2 * x for x in e)]
                       for e in product((0, 1), repeat=3)))
        cm.append(m[(0, 0, 0)])
    return gen, cm


def hodgecount():
    F = Fig("fig_hodgecount",
            "Hodge classes of the square of a Mumford fourfold, degree by "
            "degree, against the subring generated by divisor classes.")
    gen, cm = hodge_counts()
    # the subring generated by divisor classes (thm:lefschetzclosure(ii)):
    # at a point that is not CM the Sp(V,psi)-invariants, at a CM point the
    # coefficients of (1 + 4y + y^2)^4
    dgen = [1, 3, 6, 10, 15, 10, 6, 3, 1]
    c = [1]
    for _ in range(4):
        c = [sum(c[i - j] * [1, 4, 1][j] for j in range(3)
                 if 0 <= i - j < len(c)) for i in range(len(c) + 2)]
    dcm = c
    # what the paper states: prop:mumfordproduct, prop:mumforddivisor
    assert gen[:3] == [1, 3, 8] and cm[:3] == [1, 16, 132]
    assert dcm == [1, 16, 100, 304, 454, 304, 100, 16, 1]
    assert all(a >= b for a, b in zip(gen, dgen)) and all(
        a >= b for a, b in zip(cm, dcm))
    pitch, bw, Hh = 0.66, 0.40, 3.30
    panels = [(0.0, gen, dgen, 30, 10, r"$t\in C$ very general"),
              (7.95, cm, dcm, 700, 100, r"$c\in C$ a CM point")]
    for x0, tot, sub, top, step, title in panels:
        S = Hh / top
        X = [x0 + 0.55 + p * pitch for p in range(9)]
        ax = x0 + 0.10
        F.path([(ax, 0), (X[-1] + 0.45, 0)], "PInk", lw=0.6, tag="ax")
        F.path([(ax, 0), (ax, top * S + 0.05)], "PInk", lw=0.6, tag="ax")
        for v in range(0, top + 1, step):
            F.path([(ax - 0.07, v * S), (ax, v * S)], "PInk", lw=0.5,
                   tag="ax")
            F.text(ax - 0.12, v * S, r"$%d$" % v, "PSlate", SS,
                   anchor="east")
        for p in range(9):
            a, b = sub[p] * S, tot[p] * S
            F.rect(X[p] - bw / 2, 0, X[p] + bw / 2, max(a, 0.02),
                   "PIndigo!55", tag="bar")
            if tot[p] > sub[p]:
                F.raw(r"  \fill[pattern=north east lines,pattern color="
                      r"PClay] (%.3f,%.3f) rectangle (%.3f,%.3f);"
                      % (X[p] - bw / 2, a, X[p] + bw / 2, b))
                F.path([(X[p] - bw / 2, a), (X[p] - bw / 2, b),
                        (X[p] + bw / 2, b), (X[p] + bw / 2, a)], "PClay",
                       lw=0.5, tag="bar")
                F.polys.append(([(X[p] - bw / 2, a), (X[p] + bw / 2, a),
                                 (X[p] + bw / 2, b), (X[p] - bw / 2, b)],
                                "bar"))
            F.path([(X[p], 0), (X[p], -0.07)], "PInk", lw=0.5, tag="ax")
            F.text(X[p], -0.36, r"$%d$" % p, "PInk", SS)
            F.text(X[p], -0.80, r"$%d$" % tot[p], "PInk", SS)
            F.text(X[p], -1.22, r"$%d$" % sub[p], "PIndigo", SS)
        F.text(ax - 0.12, -0.80, r"$\dim\mathrm{Hdg}^{p}$", "PInk", SS,
               anchor="east")
        F.text(ax - 0.12, -1.22, r"$\dim D^{p}$", "PIndigo", SS,
               anchor="east")
        F.text(ax - 0.12, -0.40, r"$p$", "PInk", SS, anchor="east")
        F.text((X[0] + X[-1]) / 2, top * S + 0.45, title, "PInk", FS)
    # legend
    ly = -1.80
    F.rect(1.2, ly - 0.10, 1.48, ly + 0.10, "PIndigo!55", tag="leg")
    F.text(1.58, ly, r"$D^{p}$: spanned by products of divisor classes; it "
           r"contains $\mathrm{ch}_{p}(E)$ for every $E\in\mathcal{L}$",
           "PInk", SS, anchor="west")
    ly2 = ly - 0.42
    F.raw(r"  \fill[pattern=north east lines,pattern color=PClay] "
          r"(1.20,%.3f) rectangle (1.48,%.3f);" % (ly2 - 0.10, ly2 + 0.10))
    F.path([(1.2, ly2 - 0.10), (1.48, ly2 - 0.10), (1.48, ly2 + 0.10),
            (1.2, ly2 + 0.10), (1.2, ly2 - 0.10)], "PClay", lw=0.5,
           tag="leg")
    F.text(1.58, ly2, r"Hodge classes outside $D^{p}$: reached by no object "
           r"of $\mathcal{L}$", "PInk", SS, anchor="west")
    return F


def build(name):
    """pdflatex in the figures folder, a check of the log for missing glyphs
    and bad boxes, and the 200 dpi PNG"""
    r = subprocess.run(["pdflatex", "-interaction=nonstopmode",
                        "-halt-on-error", name + ".tex"], cwd=HERE,
                       capture_output=True, text=True)
    log = os.path.join(HERE, name + ".log")
    text = open(log, errors="replace").read() if os.path.exists(log) else ""
    if r.returncode != 0:
        sys.stdout.write(r.stdout[-3000:])
        raise SystemExit("pdflatex failed on %s" % name)
    for bad in ("Missing character", "Overfull", "Undefined control"):
        if bad in text:
            raise SystemExit("%s: '%s' in the log" % (name, bad))
    subprocess.run(["pdftoppm", "-png", "-r", "200", "-singlefile",
                    name + ".pdf", name], cwd=HERE, check=True)
    for ext in (".aux", ".log"):
        try:
            os.remove(os.path.join(HERE, name + ext))
        except OSError:
            pass
    print("built", name + ".pdf", "and", name + ".png")


FIGURES = [frontier, lefschetzgrid, propagation, rigidity, bypass,
           hodgecount]

if __name__ == "__main__":
    names = sys.argv[1:]
    bad = 0
    for make in FIGURES:
        if names and make.__name__ not in names:
            continue
        F = make()
        problems = F.check()
        bad += len(problems)
        write(F)
        if not problems or os.environ.get("FIGDRAFT"):
            build(F.name)
    if bad:
        print("%d placement problems: fix them before building" % bad)
        sys.exit(1)
