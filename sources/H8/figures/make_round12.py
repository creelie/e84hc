#!/usr/bin/env python3
"""
make_round12.py

Two plates for the results of round twelve.

  fig_minimalsupport  the minimal support theorem at n = 4 (thm:minimalsupport,
                      ex:fourteen), drawn one dimension down: the quadric Q of
                      Lagrangians as a shaded quadric surface.  The natural
                      objects are rational points of Q; the powers of eta fill
                      the conic C_eta; the line l_W = L_+ L_- is real, but its
                      two points on Q are conjugate K-points, so it misses the
                      real quadric; a plane Pi through l_W cuts the smooth
                      conic Pi cap Q, disjoint from C_eta, and the eight graph
                      subvarieties B_(p,q) of ex:fourteen sit on it at the
                      positions that their coordinates (p:q) give, with the
                      coefficients m of the relation sum m_i [B_i] = 14 W_2.
                      The positions are computed: on the conic of
                      subvarieties the parameter is (p:q), the points L_+-
                      are (1:-+sqrt(-d)), d = 1, and a real Moebius change of
                      parameter puts l_W, the line through the two conjugate
                      points, at a finite distance from the conic.

  fig_quarticloci     where the Weil classes of an abelian eightfold of
                      (F,2,delta)-Weil type, F a quartic CM field, are known to
                      be algebraic (prop:quarticnl, cor:quarticbase,
                      prop:quarticscalar).  The period domain
                      D_F, of dimension 8, is drawn as a ball, and each
                      subdomain as a linear section of it, as in the Klein
                      model, since every locus drawn is a totally geodesic
                      subdomain: dimension 6 as a disc, dimension 4 as a
                      chord, dimension 0 as a point.  For delta trivial two
                      components D(M_1), D(M_2) of NL(R_F) (dim_F M_i = 1,
                      dimension 6) meet in D(M_1 + M_2), of dimension 4,
                      which contains the products B_1 x B_2; for delta
                      nontrivial every D(M) has dimension at most 4 and the
                      products are a component.  The locus S of scalar
                      extensions (F biquadratic, dimension 4) meets NL(R_F)
                      at (C_1 x C_2) (x) O_F; s_0 and further points of its
                      G_F(Q)-orbit lie in NL(R_F); the very general point is
                      open.  The Prym loci of rem:quarticprym are not drawn.
                      Occlusion is exact: the discs are split along their
                      common chord and painted back to front, and every curve
                      and point is tested against every disc by a ray from
                      the eye, hidden parts dashed.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back.  Beyond that every label is measured by TeX itself and
tested against every other label and every stroke before the file is
written, and the generator stops if a test fails.  The canvas below is a
self-contained copy of the measured canvas of make_frontier.py.

Run:  python3 -B make_round12.py        (from the figures directory)
"""
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
from render3d import Camera  # noqa: E402  (shared module, used unchanged)
from checkfigs import box as cf_box  # noqa: E402  (the estimate checkfigs uses)
from place import _plain  # noqa: E402


# ------------------------------------------------------------------ vectors
def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def mul(t, a):
    return (t * a[0], t * a[1], t * a[2])


def dotp(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def norm(a):
    return math.sqrt(dotp(a, a))


def unit(a):
    n = norm(a)
    return (a[0] / n, a[1] / n, a[2] / n)


def lerp(a, b, t):
    return add(a, mul(t, sub(b, a)))


# ============================================================ the canvas
PT_PER_CM = 72.27 / 2.54
PICTURE_OPTS = (r"x=1cm,y=1cm,line join=round,line cap=round,"
                r"font=\small,text=PInk")
MEAS_HEAD = r"""\documentclass{article}
\usepackage{amsmath,amssymb}
\usepackage{tikz}
\usetikzlibrary{arrows.meta,calc}
\input{%(palette)s}
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


def measure(specs):
    """TeX's own bounding box of each node (opts, text), in cm, relative to
    the point at which the node is placed."""
    if not specs:
        return []
    tmp = tempfile.mkdtemp(prefix="r12meas_")
    try:
        pal = os.path.join(HERE, "palette").replace("\\", "/")
        src = [MEAS_HEAD % dict(palette=pal, popts=PICTURE_OPTS)]
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


def segs_cross(a, b, c, d):
    """Proper crossing of the segments ab and cd."""
    def orient(p, q, r):
        return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])
    o1, o2 = orient(a, b, c), orient(a, b, d)
    o3, o4 = orient(c, d, a), orient(c, d, b)
    return o1 * o2 < 0 and o3 * o4 < 0


def rects_meet(a, b):
    return a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]


def fmt(p):
    return "(%.3f,%.3f)" % (p[0], p[1])


class Fig:
    """The TikZ of one figure, with its strokes kept alongside, so that each
    label can be measured by TeX and tested against every other label and
    every stroke before the file is written."""

    def __init__(self, name, blurb, pad=0.05):
        self.name, self.blurb, self.pad = name, blurb, pad
        self.body = []
        self.labels = []      # dict(x, y, opts, text, allow)
        self.segs = []        # (p, q, tag)
        self.leaders = []     # (p, q, tag)

    def raw(self, s):
        self.body.append(s if s.endswith("\n") else s + "\n")

    def node(self, x, y, text, opts, allow=()):
        self.raw(r"  \node[%s] at (%.3f,%.3f) {%s};" % (opts, x, y, text))
        self.labels.append(dict(x=x, y=y, opts=opts, text=text,
                                allow=set(allow)))

    def text(self, x, y, text, color="PInk", size=r"\small", anchor=None,
             allow=(), align="center"):
        opts = "text=%s,inner sep=1pt,align=%s,font=%s" % (color, align, size)
        if anchor:
            opts += ",anchor=%s" % anchor
        self.node(x, y, text, opts, allow=allow)

    def path(self, pts, style, lw=0.6, closed=False, tag=None, record=True):
        body = " -- ".join(fmt(p) for p in pts) + (" -- cycle" if closed
                                                   else "")
        self.raw(r"  \draw[%s,line width=%.2fpt] %s;" % (style, lw, body))
        if record:
            n = len(pts)
            for i in range(n - 1 + (1 if closed else 0)):
                self.segs.append((pts[i], pts[(i + 1) % n], tag))

    def fill(self, pts, style):
        self.raw(r"  \fill[%s] %s -- cycle;"
                 % (style, " -- ".join(fmt(p) for p in pts)))

    def leader(self, p, q, tag):
        """A thin rule from a label to the thing it names."""
        self.raw(r"  \draw[PSlate,line width=0.35pt] %s -- %s;" % (fmt(p),
                                                                  fmt(q)))
        self.leaders.append((p, q, tag))

    def dot(self, p, style, r_pt, tag=None):
        self.raw(r"  \draw[%s,line width=0.55pt] %s circle (%.2fpt);"
                 % (style, fmt(p), r_pt))
        r = r_pt / PT_PER_CM + 0.01
        pts = [(p[0] + r * math.cos(2 * math.pi * k / 12),
                p[1] + r * math.sin(2 * math.pi * k / 12)) for k in range(12)]
        for i in range(12):
            self.segs.append((pts[i], pts[(i + 1) % 12], tag))

    def cross_mark(self, p, color, r=0.075, tag=None):
        a, b = (p[0] - r, p[1] - r), (p[0] + r, p[1] + r)
        c, d = (p[0] - r, p[1] + r), (p[0] + r, p[1] - r)
        self.path([a, b], color, lw=0.9, tag=tag)
        self.path([c, d], color, lw=0.9, tag=tag)

    # -- checking -----------------------------------------------------------
    def check(self):
        specs = [(l["opts"], l["text"]) for l in self.labels]
        for l, b in zip(self.labels, measure(specs)):
            l["box"] = (l["x"] + b[0], l["y"] + b[1], l["x"] + b[2],
                        l["y"] + b[3])
        P = self.pad
        bad = []
        L = self.labels
        for i, a in enumerate(L):
            ra = (a["box"][0] - P, a["box"][1] - P, a["box"][2] + P,
                  a["box"][3] + P)
            for b in L[i + 1:]:
                if rects_meet(ra, b["box"]):
                    bad.append(("label/label", a["text"][:40], b["text"][:40]))
            for p, q, tag in self.segs + self.leaders:
                if tag is not None and tag in a["allow"]:
                    continue
                if seg_hits_rect(p, q, ra):
                    bad.append(("label/stroke", a["text"][:40], tag,
                                "(%.2f,%.2f)-(%.2f,%.2f)" % (p[0], p[1], q[0],
                                                             q[1])))
                    break
        # the estimate checkfigs.py makes, which must pass as well
        est = []
        for l in L:
            if _plain(l["text"]).strip():
                est.append(cf_box(l["opts"], l["x"], l["y"], l["text"]))
        for i, a in enumerate(est):
            for b in est[i + 1:]:
                if (a[0] < b[2] and b[0] < a[2] and a[1] < b[3]
                        and b[1] < a[3]):
                    bad.append(("checkfigs estimate", a[4], b[4]))
        # leaders may not cross one another
        for i, (p, q, t) in enumerate(self.leaders):
            for (r, s, u) in self.leaders[i + 1:]:
                if segs_cross(p, q, r, s):
                    bad.append(("leader/leader", t, u))
        for b in bad:
            print("   OVERLAP", b)
        print("  %s: %d labels, %d strokes, %d leaders, %d problems"
              % (self.name, len(L), len(self.segs), len(self.leaders),
                 len(bad)))
        return bad

    def tikz(self):
        return "".join(self.body)


HEAD = r"""%% {name}.tex   (generated by make_round12.py; do not edit by hand)
%% {blurb}
\documentclass[tikz,border=6pt]{{standalone}}
\usepackage{{amsmath,amssymb}}
\usetikzlibrary{{arrows.meta,calc}}
\input{{palette}}
\begin{{document}}
\begin{{tikzpicture}}[x=1cm,y=1cm,line join=round,line cap=round,
  font=\small,text=PInk]
"""
TAIL = r"""\end{tikzpicture}
\end{document}
"""


def write(fig, strict=True):
    bad = fig.check()
    if bad and strict:
        raise SystemExit("audit failed for %s" % fig.name)
    path = os.path.join(HERE, fig.name + ".tex")
    with open(path, "w") as f:
        f.write(HEAD.format(name=fig.name, blurb=fig.blurb))
        f.write(fig.tikz())
        f.write(TAIL)
    print("wrote", path)
    build(fig.name)


def build(name):
    """pdflatex, a check of the log, the 200 dpi PNG, and the cleanup."""
    r = subprocess.run(["pdflatex", "-interaction=nonstopmode",
                        "-halt-on-error", name + ".tex"], cwd=HERE,
                       capture_output=True, text=True)
    log = os.path.join(HERE, name + ".log")
    text = open(log, errors="replace").read() if os.path.exists(log) else ""
    if r.returncode != 0:
        sys.stdout.write(r.stdout[-3000:])
        raise SystemExit("pdflatex failed on %s" % name)
    for bad in ("Missing character", "Overfull", "Underfull",
                "Undefined control"):
        if bad in text:
            raise SystemExit("%s: '%s' in the log" % (name, bad))
    subprocess.run(["pdftoppm", "-png", "-r", "200", "-singlefile",
                    name + ".pdf", name], cwd=HERE, check=True)
    for ext in (".aux", ".log"):
        try:
            os.remove(os.path.join(HERE, name + ext))
        except OSError:
            pass
    print("   built %s.pdf and %s.png" % (name, name))


# ====================================================== the ball renderer
class Disc:
    """The section of the unit ball by the plane n.x = d: a flat disc."""

    def __init__(self, n, d, name):
        self.n = unit(n)
        self.d = d
        self.name = name
        self.c = mul(d, self.n)
        self.r = math.sqrt(1.0 - d * d)
        a = (0.0, 0.0, 1.0) if abs(self.n[2]) < 0.9 else (1.0, 0.0, 0.0)
        self.e1 = unit(cross(self.n, a))
        self.e2 = cross(self.n, self.e1)

    def at(self, t, rho=1.0):
        return add(self.c, add(mul(rho * self.r * math.cos(t), self.e1),
                               mul(rho * self.r * math.sin(t), self.e2)))

    def side(self, p):
        return dotp(self.n, p) - self.d

    def blocks(self, E, X, eps=1e-4):
        """Does the disc meet the open segment from the eye E to X?"""
        den = dotp(self.n, sub(X, E))
        if abs(den) < 1e-12:
            return False
        s = (self.d - dotp(self.n, E)) / den
        if not (eps < s < 1.0 - eps):
            return False
        y = add(E, mul(s, sub(X, E)))
        return norm(sub(y, self.c)) < self.r


def plane_meet(A, B):
    """The line in which the planes of two discs meet: (point, direction)."""
    u = unit(cross(A.n, B.n))
    g = dotp(A.n, B.n)
    det = 1.0 - g * g
    a = (A.d - g * B.d) / det
    b = (B.d - g * A.d) / det
    return add(mul(a, A.n), mul(b, B.n)), u


def chord(p, v):
    """The two ends of the chord of the unit ball through p along v."""
    v = unit(v)
    b = dotp(p, v)
    c = dotp(p, p) - 1.0
    s = math.sqrt(b * b - c)
    return add(p, mul(-b - s, v)), add(p, mul(-b + s, v))


class Ball:
    """A picture of the unit ball, seen by a perspective camera, holding flat
    discs, chords and points; every stroke is tested for occlusion by every
    disc it does not lie on."""

    def __init__(self, fig, cam, ox, oy, light=(-0.50, -0.40, 0.75)):
        self.fig, self.cam = fig, cam
        self.LIGHT = unit(light)
        self.ox, self.oy = ox, oy
        self.discs = []
        self.eye = cam.eye

    def P(self, p):
        (x, y), _ = self.cam.project(p)
        return (self.ox + x, self.oy + y)

    def depth(self, p):
        return self.cam.project(p)[1]

    def hidden(self, X, on=()):
        for D in self.discs:
            if D.name in on:
                continue
            if D.blocks(self.eye, X):
                return True
        return False

    def silhouette(self, n=240):
        """The outline of the ball: the circle of tangency of the cone from
        the eye, projected."""
        E = self.eye
        dE = norm(E)
        w = unit(E)
        c = mul(1.0 / dE, w)                 # centre of the tangency circle
        r = math.sqrt(1.0 - 1.0 / (dE * dE))
        a = (0.0, 0.0, 1.0)
        e1 = unit(cross(w, a))
        e2 = cross(w, e1)
        return [self.P(add(c, add(mul(r * math.cos(2 * math.pi * k / n), e1),
                                  mul(r * math.sin(2 * math.pi * k / n), e2))))
                for k in range(n)]

    def pieces(self, D, n=360):
        """D cut along the planes of the other discs, as polygons in 3D."""
        cuts = [B for B in self.discs if B is not D]
        pts = [D.at(2 * math.pi * k / n) for k in range(n)]
        polys = [pts]
        for B in cuts:
            new = []
            for poly in polys:
                for sgn in (1, -1):
                    out = []
                    m = len(poly)
                    for i in range(m):
                        p, q = poly[i], poly[(i + 1) % m]
                        sp, sq = sgn * B.side(p), sgn * B.side(q)
                        if sp >= 0:
                            out.append(p)
                        if (sp >= 0) != (sq >= 0):
                            t = sp / (sp - sq)
                            out.append(lerp(p, q, t))
                    if len(out) >= 3:
                        new.append(out)
            polys = new
        return polys

    def paint_discs(self, base="PTeal", lo=10, hi=30):
        items = []
        for D in self.discs:
            for poly in self.pieces(D):
                cen = mul(1.0 / len(poly), (sum(p[0] for p in poly),
                                            sum(p[1] for p in poly),
                                            sum(p[2] for p in poly)))
                nrm = D.n
                if dotp(nrm, sub(self.eye, cen)) < 0:
                    nrm = mul(-1.0, nrm)
                lam = max(0.0, dotp(nrm, self.LIGHT))
                pct = int(round(hi - (hi - lo) * lam))
                d = sum(self.depth(p) for p in poly) / len(poly)
                items.append((d, pct, poly))
        items.sort(key=lambda it: -it[0])
        for d, pct, poly in items:
            self.fig.fill([self.P(p) for p in poly],
                          "%s!%d!white" % (base, pct))

    def curve(self, pts, color, lw, on=(), tag=None, hidden_color=None,
              draw_hidden=True):
        """A polyline in 3D: the visible runs solid, the hidden ones dashed."""
        vis = [not self.hidden(p, on) for p in pts]
        runs, cur, state = [], [pts[0]], vis[0]
        for p, v in zip(pts[1:], vis[1:]):
            if v == state:
                cur.append(p)
            else:
                cur.append(p)
                runs.append((state, cur))
                cur, state = [p], v
        runs.append((state, cur))
        hc = hidden_color or color
        for v, run in runs:
            if len(run) < 2:
                continue
            q = [self.P(p) for p in run]
            if v:
                self.fig.path(q, color, lw=lw, tag=tag)
            elif draw_hidden:
                self.fig.path(q, hc + ",dash pattern=on 2.2pt off 1.6pt",
                              lw=0.8 * lw, tag=tag)
        return vis


# ------------------------------------------------------------- quartic loci
QL_EYE = unit((0.62, -1.0, 0.50))
QL_SCALE = 1.85


def ql_camera():
    return Camera(mul(9.0, QL_EYE), target=(0, 0, 0), up=(0, 0, 1),
                  focal=9.0, scale=QL_SCALE)


def ql_geometry():
    """The loci, in the unit ball.  D1, D2: two components D(M_1), D(M_2) of
    NL(R_F) for delta trivial; their common chord P = D(M_1 + M_2); S the
    chord of scalar extensions, through the point R of P."""
    D1 = Disc((0.05, -0.12, 1.0), -0.12, "D1")
    D2 = Disc((1.0, -0.25, 0.80), 0.12, "D2")
    p0, u = plane_meet(D1, D2)
    R = add(p0, mul(0.25, u))
    v = unit((-0.50, 0.0, 0.85))
    return dict(D1=D1, D2=D2, P=chord(p0, u), R=R, S=chord(R, v), u=u, v=v)


def seg_pts(ab, n=160):
    a, b = ab
    return [lerp(a, b, k / n) for k in range(n + 1)]


def ql_through(cam, xy):
    """The point of the ball on the ray through the screen point xy (relative
    to the centre of the picture) that is nearest the centre of the ball."""
    k = cam.focal * cam.scale
    d = unit(add(add(mul(xy[0] / k, cam.u), mul(xy[1] / k, cam.v)),
                 mul(-1.0, cam.w)))
    t = -dotp(cam.eye, d)
    return add(cam.eye, mul(t, d))


def ql_panel(fig, ox, oy, trivial):
    """One ball, with its loci; returns the screen positions of the things
    that the labels name."""
    g = ql_geometry()
    cam = ql_camera()
    B = Ball(fig, cam, ox, oy)
    D1, D2 = g["D1"], g["D2"]
    sil = B.silhouette()
    r = max(math.hypot(x - ox, y - oy) for x, y in sil)
    # the ball: a clear region with a faint rim, as for a transparent solid
    fig.raw(r"  \begin{scope}\clip (%.3f,%.3f) circle (%.3f);"
            r"\shade[inner color=white,outer color=PSlate!20!white] "
            r"(%.3f,%.3f) circle (%.3f);\end{scope}"
            % (ox, oy, r, ox - 0.15 * r, oy + 0.20 * r, 1.28 * r))
    at = {"r": r, "o": (ox, oy)}
    N = chord((-0.75, -0.10, 0.0), (-0.10, 0.50, 0.90))
    if trivial:
        B.discs = [D1, D2]
        B.paint_discs(base="PTeal", lo=8, hi=34)
        for D in B.discs:
            pts = [D.at(2 * math.pi * k / 360) for k in range(361)]
            B.curve(pts, "PTeal", 0.75, on=(D.name,), tag=D.name,
                    hidden_color="PTeal!75!white")
        B.curve(seg_pts(g["P"]), "PBlue", 1.35, on=("D1", "D2"), tag="P")
        s0 = D1.at(math.radians(212), 0.62)
        orbit = [D1.at(math.radians(300), 0.86),
                 D2.at(math.radians(250), 0.66)]
    else:
        B.curve(seg_pts(g["P"]), "PBlue", 1.35, tag="P")
        B.curve(seg_pts(N), "PTeal", 1.35, tag="N")
        s0 = lerp(N[0], N[1], 0.42)
        orbit = [lerp(N[0], N[1], 0.74), lerp(g["P"][0], g["P"][1], 0.22)]
    B.curve(seg_pts(g["S"]), "PClay", 1.35, tag="S",
            hidden_color="PClay!75!white")
    fig.path(sil, "PSlate", lw=0.75, closed=True, tag="ball")
    # the points
    at["R"] = B.P(g["R"])
    fig.dot(at["R"], "PInk,fill=white", 2.6, tag="R")
    assert not B.hidden(s0, on=("D1",)), "s0 hidden"
    at["s0"] = B.P(s0)
    fig.dot(at["s0"], "PInk,fill=PInk", 2.0, tag="s0")
    for q in orbit:
        assert not B.hidden(q, on=("D1", "D2")), q
        fig.dot(B.P(q), "PInk,fill=PInk", 1.1, tag="orbit")
    sv = ql_through(cam, (0.612 * r, 0.663 * r))
    assert norm(sv) < 0.95 and not B.hidden(sv)
    at["s"] = B.P(sv)
    fig.cross_mark(at["s"], "PMag", tag="s")
    at.update(B=B, g=g, N=N)
    return at


LH = 0.335          # the baseline skip of \footnotesize, in cm


def ql_key(fig, x0, y0, xr):
    """The key: the notation on the left, the marked points on the right.
    Each entry is a west-anchored node whose first line is level with its
    symbol."""
    FS = r"\footnotesize"
    rows_l = [
        (r"$\cD(M)$", "PTeal",
         r"the points at which the $\cQ_{\delta}$-submodule"
         r"\\$M\subseteq R_{F}$ consists of Hodge classes, of dimension"
         r"\\$2(4-\dim_{F}M)$; on $\mathrm{NL}(R_{F})=\bigcup_{M}\cD(M)$ "
         r"the Weil\\classes are polynomials in divisor classes"),
        (r"$P$", "PBlue",
         r"the products $B_{1}\times B_{2}$ of two abelian fourfolds"
         r"\\of $(F,1)$-Weil type; $P\subseteq\mathrm{NL}(R_{F})$ for every "
         r"$\delta$"),
        (r"$S$", "PClay",
         r"for $F=KF_{0}$ biquadratic, the scalar extensions"
         r"\\$C\otimes_{\cO_{K}}\cO_{F}$ of Weil fourfolds $C$ of $K$, on "
         r"which\\Markman's theorem applies; $S\not\subseteq"
         r"\mathrm{NL}(R_{F})$"),
    ]
    rows_r = [
        ("ring", r"$(C_{1}\times C_{2})\otimes_{\cO_{K}}\cO_{F}\in S\cap P$,"
                 r" with $C_{1}$, $C_{2}$\\abelian surfaces of Weil type"),
        ("dot", r"$s_{0}$, the base point, a CM point"),
        ("small", r"further points of $G_{F}(\QQ)\,s_{0}\subseteq"
                  r"\mathrm{NL}(R_{F})$,\\CM points, a dense countable set"),
        ("cross", r"$s$ very general, $\mathrm{Hg}(A_{s})=G_{F}$: whether"
                  r"\\$W_{F}(A_{s})$ is algebraic is open"),
    ]
    gap = 0.16
    y = y0
    for sym, col, txt in rows_l:
        n = txt.count(r"\\") + 1
        first = y - 0.5 * LH
        fig.text(x0 + 0.66, first, sym, color=col, size=FS, anchor="east")
        fig.text(x0 + 0.82, y - 0.5 * n * LH, txt, size=FS, anchor="west",
                 align="left")
        y -= n * LH + gap
    y = y0
    for kind, txt in rows_r:
        n = txt.count(r"\\") + 1
        g = (xr + 0.25, y - 0.5 * LH)
        if kind == "ring":
            fig.dot(g, "PInk,fill=white", 2.6, tag="key")
        elif kind == "dot":
            fig.dot(g, "PInk,fill=PInk", 2.0, tag="key")
        elif kind == "small":
            fig.dot(g, "PInk,fill=PInk", 1.1, tag="key")
        else:
            fig.cross_mark(g, "PMag", tag="key")
        fig.text(xr + 0.52, y - 0.5 * n * LH, txt, size=FS, anchor="west",
                 align="left")
        y -= n * LH + gap


def quarticloci():
    fig = Fig("fig_quarticloci",
              "Where the Weil classes of a quartic CM family are known to be "
              "algebraic.")
    XB = 6.65
    A = ql_panel(fig, 0.0, 0.0, True)
    C = ql_panel(fig, XB, 0.0, False)
    for pan, ox, title in ((A, 0.0, r"$\delta$ trivial: "
                            r"$\cQ_{\delta}\cong M_{2}(F_{0})$ is split"),
                           (C, XB, r"$\delta$ nontrivial: "
                            r"$\cQ_{\delta}$ is a division algebra")):
        B, g, r = pan["B"], pan["g"], pan["r"]
        fig.text(ox, r + 0.78, title)
        # S, named at its upper end
        top = B.P(g["S"][1])
        fig.text(top[0] + 0.10, top[1] + 0.33, r"$S$, $\dim 4$",
                 color="PClay", anchor="west")
        # P, named at the right, outside the ball
        pp = B.P(lerp(g["P"][0], g["P"][1], 0.93))
        lab = (ox + r + 0.36, pp[1] + 0.30)
        fig.leader((lab[0] - 0.05, lab[1]), pp, "P")
        fig.text(lab[0], lab[1], r"$P$, $\dim 4$", color="PBlue",
                 anchor="west", allow=("P",))
        # the domain
        fig.text(ox - 0.72 * r - 0.14, -0.72 * r - 0.22,
                 r"$\cD_{F}$, $\dim 8$", color="PSlate", anchor="east")
        # the points
        fig.text(pan["s0"][0] + 0.13, pan["s0"][1] - 0.01, r"$s_{0}$",
                 anchor="west", allow=("s0",))
        lab = (ox + 0.80 * r + 0.34, 0.80 * r + 0.42)
        fig.leader((lab[0] - 0.05, lab[1] - 0.02),
                   (pan["s"][0] + 0.09, pan["s"][1] + 0.09), "s")
        fig.text(lab[0], lab[1], r"very general $s$", color="PMag",
                 anchor="west", allow=("s",))
    # the two components of NL(R_F) in the first panel
    B, g, r = A["B"], A["g"], A["r"]
    a1 = B.P(g["D1"].at(math.radians(118), 0.86))
    lab = (-r - 0.36, a1[1] - 0.05)
    fig.leader((lab[0] + 0.05, lab[1]), a1, "D1")
    fig.text(lab[0], lab[1], r"$\cD(M_{1})$, $\dim 6$", color="PTeal",
             anchor="east", allow=("D1",))
    a2 = B.P(g["D2"].at(math.radians(308), 0.74))
    lab = (-r - 0.36, a2[1] + 0.45)
    fig.leader((lab[0] + 0.05, lab[1]), a2, "D2")
    fig.text(lab[0], lab[1], r"$\cD(M_{2})$, $\dim 6$", color="PTeal",
             anchor="east", allow=("D2",))
    # the other component in the second panel
    B, r = C["B"], C["r"]
    an = B.P(lerp(C["N"][0], C["N"][1], 0.22))
    lab = (XB - r - 0.36, an[1] + 0.30)
    fig.leader((lab[0] + 0.05, lab[1]), an, "N")
    fig.text(lab[0], lab[1], r"$\cD(M)$, $\dim\le 4$", color="PTeal",
             anchor="east", allow=("N",))
    ql_key(fig, -4.45, -2.30, 3.45)
    return fig


# ========================================================= minimal support
MS_AXES = (2.30, 1.60, 1.30)          # the semi-axes of the drawn quadric
MS_EYE = (2.0, -8.5, 5.0)
MS_LIGHT = unit((-0.35, -0.30, 0.90))
MS_SHADE = (0.22, 5, 44)      # ambient, lightest tint, range of tints
# the eight graph subvarieties B_(p,q) of ex:fourteen and their coefficients
MS_PQ = [(1, -3), (1, -2), (1, 2), (1, 3), (2, -1), (2, 1), (3, -1), (3, 1)]
MS_M = [-1, 16, -16, 1, -16, 16, 1, -1]
MS_LAMBDA = 0.60      # the real Moebius change of parameter t -> lambda t


def ms_camera():
    return Camera(MS_EYE, target=(0.25, 0.0, -0.05), up=(0, 0, 1), focal=9.0,
                  scale=MS_SCALE)


def ms_on_q(p):
    a, b, c = MS_AXES
    return p[0] ** 2 / a ** 2 + p[1] ** 2 / b ** 2 + p[2] ** 2 / c ** 2 - 1.0


def ms_normal(p):
    a, b, c = MS_AXES
    return unit((p[0] / a ** 2, p[1] / b ** 2, p[2] / c ** 2))


def plane_section(n, h):
    """The conic in which the plane n.x = h meets the drawn quadric, as
    (centre, e1, e2) with the conic {centre + cos t e1 + sin t e2}."""
    a, b, c = MS_AXES
    dg = (1 / a ** 2, 1 / b ** 2, 1 / c ** 2)
    n = unit(n)
    x0 = mul(h, n)
    f1 = unit(cross(n, (0.0, 0.0, 1.0)) if abs(n[2]) < 0.9
              else cross(n, (1.0, 0.0, 0.0)))
    f2 = cross(n, f1)

    def qf(u, v):
        return sum(dg[k] * u[k] * v[k] for k in range(3))
    G = [[qf(f1, f1), qf(f1, f2)], [qf(f2, f1), qf(f2, f2)]]
    g = [qf(f1, x0), qf(f2, x0)]
    k = qf(x0, x0)
    det = G[0][0] * G[1][1] - G[0][1] * G[1][0]
    Gi = [[G[1][1] / det, -G[0][1] / det], [-G[1][0] / det, G[0][0] / det]]
    al = -(Gi[0][0] * g[0] + Gi[0][1] * g[1])
    be = -(Gi[1][0] * g[0] + Gi[1][1] * g[1])
    rho = 1.0 - k + (g[0] * (Gi[0][0] * g[0] + Gi[0][1] * g[1])
                     + g[1] * (Gi[1][0] * g[0] + Gi[1][1] * g[1]))
    assert rho > 0, "the plane misses the quadric"
    # principal axes of G
    tr = G[0][0] + G[1][1]
    dis = math.sqrt(max(0.0, (G[0][0] - G[1][1]) ** 2 / 4 + G[0][1] ** 2))
    mus = (tr / 2 + dis, tr / 2 - dis)
    axes = []
    for mu in mus:
        if abs(G[0][1]) > 1e-12:
            w = (G[0][1], mu - G[0][0])
        else:
            w = (1.0, 0.0) if abs(G[0][0] - mu) < abs(G[1][1] - mu) else (0.0, 1.0)
        ln = math.hypot(*w)
        w = (w[0] / ln, w[1] / ln)
        axes.append(mul(math.sqrt(rho / mu), add(mul(w[0], f1), mul(w[1], f2))))
    cen = add(x0, add(mul(al, f1), mul(be, f2)))
    return cen, axes[0], axes[1]


def clip_poly(poly, n, h, sgn):
    """The part of a planar polygon (in 3D) on the side sgn*(n.x - h) >= 0."""
    out = []
    m = len(poly)
    for i in range(m):
        p, q = poly[i], poly[(i + 1) % m]
        sp, sq = sgn * (dotp(n, p) - h), sgn * (dotp(n, q) - h)
        if sp >= 0:
            out.append(p)
        if (sp >= 0) != (sq >= 0):
            out.append(lerp(p, q, sp / (sp - sq)))
    return out


class Quadric:
    """The drawn quadric, cut by the plane Pi into the part behind Pi and the
    cap in front of it, painted with a Lambert term."""

    def __init__(self, fig, cam, pi_n, pi_h):
        self.fig, self.cam = fig, cam
        self.eye = cam.eye
        self.pi_n, self.pi_h = unit(pi_n), pi_h

    def P(self, p):
        return self.cam.project(p)[0]

    def point(self, th, ph):
        a, b, c = MS_AXES
        return (a * math.cos(ph) * math.cos(th), b * math.cos(ph) * math.sin(th),
                c * math.sin(ph))

    def facets(self, nth=150, nph=76):
        main, cap = [], []
        for i in range(nth):
            for j in range(nph):
                t0, t1 = 2 * math.pi * i / nth, 2 * math.pi * (i + 1) / nth
                p0 = -math.pi / 2 + math.pi * j / nph
                p1 = -math.pi / 2 + math.pi * (j + 1) / nph
                quad = [self.point(t0, p0), self.point(t1, p0),
                        self.point(t1, p1), self.point(t0, p1)]
                cen = mul(0.25, (sum(p[0] for p in quad),
                                 sum(p[1] for p in quad),
                                 sum(p[2] for p in quad)))
                nr = ms_normal(cen)
                if dotp(nr, sub(self.eye, cen)) <= 0:
                    continue
                lam = max(0.0, dotp(nr, MS_LIGHT))
                inten = MS_SHADE[0] + (1.0 - MS_SHADE[0]) * lam
                pct = int(round(MS_SHADE[1] + MS_SHADE[2] * (1.0 - inten)))
                d = self.cam.project(cen)[1]
                for sgn, lst in ((-1, main), (1, cap)):
                    part = clip_poly(quad, self.pi_n, self.pi_h, sgn)
                    if len(part) >= 3:
                        lst.append((d, pct, part))
        return main, cap

    def paint(self, lst, base="PSlate"):
        # facets of one convex piece that face the eye do not overlap, so
        # they are merged by shade into a few paths to keep the file small
        lst.sort(key=lambda it: -it[0])
        groups = {}
        for d, pct, part in lst:
            groups.setdefault(pct, []).append(part)
        for pct in sorted(groups):
            body = " ".join(" -- ".join(fmt(self.P(p)) for p in part)
                            + " -- cycle" for part in groups[pct])
            self.fig.raw(r"  \filldraw[fill=%s!%d!white,draw=%s!%d!white,"
                         r"line width=0.15pt] %s;" % (base, pct, base, pct, body))


MS_PI = (unit((0.20, -0.20, 0.60)), 0.84)     # normal, fraction of support
MS_ETA = (unit((-0.30, -0.70, 0.20)), 0.86)
MS_PHI0 = math.radians(70)                    # where l_W lies, seen from Pi
MS_SCALE = 1.9
MS_OTHERS = ((-1.20, -0.30), (-0.82, -0.25))   # (theta, phi) on Q, behind Pi
MS_CAPPT = (0.15, 0.30)                          # (u, v) of a point of the cap
MS_PLANE = ((-1.35, -1.65), (0.32, 1.45))        # the drawn part of Pi
MS_CONIC_LABEL = 0.47                            # where Pi cap Q is named


def support(n):
    a, b, c = MS_AXES
    return math.sqrt(a * a * n[0] ** 2 + b * b * n[1] ** 2 + c * c * n[2] ** 2)


def ms_geometry():
    """The plane Pi, its conic in circle coordinates (u, v), the line l_W,
    the eight points B_(p,q), and the conic C_eta."""
    n, fr = MS_PI
    h = fr * support(n)
    cc, g1, g2 = plane_section(n, h)
    c0, s0 = math.cos(MS_PHI0), math.sin(MS_PHI0)

    def circ(u, v):
        return add(cc, add(mul(c0 * u - s0 * v, g1), mul(s0 * u + c0 * v, g2)))
    lam = MS_LAMBDA
    # the parameter (p:q) of the conic of subvarieties is sent to the angle
    # 2 atan(lambda q/p); the two points (1 : -+ i) of L_+- go to
    # u = u0, v = +- 2 i lambda/(1 - lambda^2), so l_W is the line u = u0
    u0 = (1 + lam * lam) / (1 - lam * lam)
    pts = []
    for (p, q), m in zip(MS_PQ, MS_M):
        th = 2 * math.atan(lam * q / p)
        pts.append(((p, q), m, th, circ(math.cos(th), math.sin(th))))
    # check the claims the picture makes, in exact terms of the model
    for k in range(8):
        for j in range(k + 1, 8):
            assert abs(pts[k][2] - pts[j][2]) > 1e-6
    zp = complex(0, 2 * lam / (1 - lam * lam))
    for sgn in (1, -1):
        # the conjugate points lie on the unit circle and on u = u0
        assert abs(u0 * u0 + (sgn * zp) ** 2 - 1) < 1e-12
    en, efr = MS_ETA
    ce, f1, f2 = plane_section(en, efr * support(en))
    eta = [add(ce, add(mul(math.cos(2 * math.pi * k / 360), f1),
                       mul(math.sin(2 * math.pi * k / 360), f2)))
           for k in range(361)]
    conic = [circ(math.cos(2 * math.pi * k / 360),
                  math.sin(2 * math.pi * k / 360)) for k in range(361)]
    # C_eta and Pi cap Q are disjoint: C_eta lies strictly behind Pi
    assert all(dotp(n, p) - h < -0.05 for p in eta)
    return dict(n=n, h=h, circ=circ, u0=u0, pts=pts, eta=eta, conic=conic)


def ms_draw(fig):
    """The quadric, the plane Pi, the conics, the line and the points;
    returns the screen positions that the labels need."""
    cam = ms_camera()
    g = ms_geometry()
    Qd = Quadric(fig, cam, g["n"], g["h"])
    P = Qd.P
    E = cam.eye
    main, cap = Qd.facets()
    Qd.paint(main)
    # the outline: the section by the polar plane of the eye
    a, b, c = MS_AXES
    pe = (E[0] / a ** 2, E[1] / b ** 2, E[2] / c ** 2)
    cen, e1, e2 = plane_section(pe, 1.0 / norm(pe))
    sil = [P(add(cen, add(mul(math.cos(2 * math.pi * k / 360), e1),
                          mul(math.sin(2 * math.pi * k / 360), e2))))
           for k in range(360)]
    fig.path(sil, "PSlate", lw=0.8, closed=True, tag="Q")
    # C_eta, on the part of Q behind Pi
    for p in g["eta"]:
        assert dotp(ms_normal(p), sub(E, p)) > 0, "C_eta not in view"
    fig.path([P(p) for p in g["eta"]], "PTeal", lw=1.2, tag="eta")
    # the natural objects off both conics: rational points of Q
    others = []
    for th, ph in MS_OTHERS:
        X = Qd.point(th, ph)
        assert dotp(ms_normal(X), sub(E, X)) > 0
        assert dotp(g["n"], X) - g["h"] < -0.05
        others.append(X)
    for X in others:
        fig.dot(P(X), "PSlate,fill=PSlate", 1.8, tag="other")
    # the plane Pi, drawn over the part of Q behind it
    circ, u0 = g["circ"], g["u0"]
    corners = [circ(*MS_PLANE[0]), circ(MS_PLANE[1][0] + u0, MS_PLANE[0][1]),
               circ(MS_PLANE[1][0] + u0, MS_PLANE[1][1]),
               circ(MS_PLANE[0][0], MS_PLANE[1][1])]
    fig.fill([P(p) for p in corners], "PIndigo,fill opacity=0.10")
    fig.path([P(p) for p in corners], "PIndigo!60!white", lw=0.55,
             closed=True, tag="Pi")
    # the cap of Q in front of Pi
    Qd.paint(cap)
    for p in g["conic"]:
        assert dotp(ms_normal(p), sub(E, p)) > 0, "the conic is not in view"
    fig.path([P(p) for p in g["conic"]], "PIndigo", lw=1.2, tag="conic")
    # a rational point of the cap, off the conic: the point of Q above
    # (u, v) in Pi
    X = circ(*MS_CAPPT)
    lo, hi = 0.0, 2.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if ms_on_q(add(X, mul(mid, g["n"]))) < 0:
            lo = mid
        else:
            hi = mid
    X = add(X, mul(lo, g["n"]))
    assert abs(ms_on_q(X)) < 1e-9 and dotp(ms_normal(X), sub(E, X)) > 0
    others.append(X)
    fig.dot(P(X), "PSlate,fill=PSlate", 1.8, tag="other")
    # l_W, in Pi, outside the conic: it meets Q in no real point
    lw = [circ(u0, MS_PLANE[0][1]), circ(u0, MS_PLANE[1][1])]
    fig.path([P(p) for p in lw], "PMag", lw=1.1, tag="lW")
    at = dict(sil=sil, corners=[P(p) for p in corners], lw=[P(p) for p in lw],
              eta=[P(p) for p in g["eta"]], conic=[P(p) for p in g["conic"]],
              centre=P(circ(0, 0)), others=[P(X) for X in others], pts=[])
    for (pq, m, th, X) in g["pts"]:
        fig.dot(P(X), "PIndigo,fill=PIndigo", 2.2, tag="B")
        at["pts"].append((pq, m, th, P(X)))
    at["g"] = g
    at["P"] = P
    at["sil_x0"] = min(p[0] for p in sil)
    at["qlabel"] = min(sil, key=lambda p: p[0] - 0.9 * p[1])
    return at


def box_point(b, p):
    """The point of the rectangle b nearest to p."""
    return (min(max(p[0], b[0]), b[2]), min(max(p[1], b[1]), b[3]))


def place_labels(fig, items, pad=0.06, size=r"\footnotesize"):
    """Place each label (anchor point, text, color, tag) near its point:
    the first position, in order of distance, whose box (measured by TeX,
    and as checkfigs.py estimates it) meets no stroke, no label placed
    before, and whose leader crosses no label.  Returns the placed boxes."""
    opts = ["text=%s,inner sep=1pt,align=center,font=%s" % (c, size)
            for (_, _, c, _) in items]
    sizes = measure([(o, t) for o, (_, t, _, _) in zip(opts, items)])
    placed = [(l["box"] if "box" in l else None) for l in fig.labels]
    placed = [b for b in placed if b]
    est = [cf_box(l["opts"], l["x"], l["y"], l["text"])[:4]
           for l in fig.labels if _plain(l["text"]).strip()]
    out = []
    for (pt, text, col, tag), o, sz in zip(items, opts, sizes):
        w, h = sz[2] - sz[0], sz[3] - sz[1]
        best = None
        for dist in (0.10, 0.18, 0.28, 0.40, 0.55, 0.72, 0.92):
            for k in range(24):
                a = 2 * math.pi * k / 24
                cx = pt[0] + math.cos(a) * (dist + w / 2)
                cy = pt[1] + math.sin(a) * (dist + h / 2)
                b = (cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2)
                bp = (b[0] - pad, b[1] - pad, b[2] + pad, b[3] + pad)
                if any(seg_hits_rect(p, q, bp) for p, q, t in fig.segs):
                    continue
                if any(rects_meet(bp, c) for c in placed):
                    continue
                e = cf_box(o, cx, cy, text)[:4]
                if any(rects_meet(e, c) for c in est):
                    continue
                lead = box_point(b, pt)
                if any(seg_hits_rect(pt, lead, c) for c in placed):
                    continue
                crossings = sum(1 for p, q, t in fig.segs
                                if segs_cross(p, q, pt, lead))
                cost = dist + 0.5 * crossings
                if best is None or cost < best[0]:
                    best = (cost, cx, cy, b, lead, e)
            if best is not None and best[0] < dist + 0.2:
                break
        if best is None:
            raise SystemExit("no place for the label %s" % text)
        _, cx, cy, b, lead, e = best
        if math.hypot(lead[0] - pt[0], lead[1] - pt[1]) > 0.14:
            fig.leader(lead, pt, tag)
        fig.node(cx, cy, text, o, allow=(tag,))
        placed.append(b)
        est.append(e)
        out.append(b)
    return out


def minimalsupport():
    fig = Fig("fig_minimalsupport",
              "Minimal support of a combination of natural objects at n = 4.")
    at = ms_draw(fig)
    items = []
    for pq, m, th, xy in at["pts"]:
        items.append((xy, r"$(%d,%d)$" % pq, "PIndigo", "B%d%d" % pq))
    place_labels(fig, items)
    # the conic itself, named at a point of its lower left arc
    cl = at["conic"][int(len(at["conic"]) * MS_CONIC_LABEL)]
    place_labels(fig, [(cl, r"$\Pi\cap Q$", "PIndigo", "conicL")],
                 size=r"\small")
    SM = r"\small"
    # the plane, at its far corner
    q = at["P"](at["g"]["circ"](MS_PLANE[0][0] + 0.16, MS_PLANE[0][1] + 0.34))
    fig.text(q[0], q[1], r"$\Pi\supset l_{W}$", color="PIndigo", size=SM,
             anchor="west")
    # the line, at its upper end
    top = at["lw"][0]
    fig.text(top[0] + 0.12, top[1] + 0.50,
             r"$l_{W}=L_{+}L_{-}$:\\no real point on $Q$", color="PMag",
             size=SM, anchor="west", align="left")
    # the conic of the relation, and C_eta, and Q
    e = min(at["eta"], key=lambda p: p[0] + 0.6 * p[1])
    lab = (at["sil_x0"] - 0.30, e[1] - 0.55)
    fig.leader((lab[0] + 0.04, lab[1]), e, "eta")
    fig.text(lab[0], lab[1], r"$C_{\eta}$: $\nu_{4}(C_{\eta})$\\spans the powers\\of $\eta$",
             color="PTeal", size=SM, anchor="east", align="right",
             allow=("eta",))
    ms_key(fig, at["sil_x0"] - 1.55, min(p[1] for p in at["sil"]) - 0.35)
    qp = at["qlabel"]
    fig.text(qp[0] - 0.25, qp[1] + 0.30, r"$Q=\mathrm{LG}(2,4)$", color="PSlate",
             size=SM, anchor="east")
    return fig, at


def lerp2(a, b, t):
    return (a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]))


def ms_key(fig, x0, y0):
    FS = r"\footnotesize"
    rows = [
        ("pq", r"the graph subvariety $B_{(p,q)}$, at the parameter $(p:q)$ "
               r"of the conic $\Pi\cap Q$ of subvarieties,\\"
               r"on which $L_{\pm}=(1:\mp\sqrt{-d})$; "
               r"$\sum m_{(p,q)}[B_{(p,q)}]=14\,W_{2}$ at $d=1$, with\\"
               r"$m_{(1,\mp3)}=\mp1$, $m_{(1,\mp2)}=\pm16$, "
               r"$m_{(2,\mp1)}=\mp16$, $m_{(3,\mp1)}=\pm1$"),
        ("dot", r"other natural objects, off $\Pi\cap Q$ and off $C_{\eta}$: "
                r"none of them can replace\\a $B_{(p,q)}$ in a relation of "
                r"eight terms"),
        ("", r"a nonzero Weil part needs $s\ge8$ natural characters off "
             r"$C_{\eta}$; for $s=8$ they lie\\on one smooth conic "
             r"$\Pi\cap Q$ with $\Pi\supset l_{W}$, disjoint from "
             r"$C_{\eta}$, and the relation is pure"),
    ]
    y = y0
    hs = measure([("text=PInk,inner sep=1pt,align=left,font=%s" % FS, t)
                  for _, t in rows])
    for (kind, txt), hb in zip(rows, hs):
        hh = hb[3] - hb[1]
        if kind == "pq":
            fig.text(x0 + 0.72, y - 0.5 * LH, r"$(p,q)$", color="PIndigo",
                     size=FS, anchor="east")
        elif kind == "dot":
            fig.dot((x0 + 0.50, y - 0.5 * LH), "PSlate,fill=PSlate", 1.8,
                    tag="key")
        fig.text(x0 + 0.86, y - 0.5 * hh, txt, size=FS, anchor="west",
                 align="left")
        y -= hh + 0.12
