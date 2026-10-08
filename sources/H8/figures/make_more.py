#!/usr/bin/env python3
"""
make_more.py

Two plates in three dimensions.

  fig_escape     (a) the Boolean lattice of the three hypotheses of the
                 proposition on which hypotheses Markman's construction
                 escapes, drawn as a genuine unit cube standing on its
                 vertex: the vertex (i,j,k) is the set S of hypotheses (Hm)
                 with the m-th coordinate 1, its height is |S|/sqrt(3), each
                 edge adds one hypothesis and is coloured by it, and the
                 shaded face is the set of positions where (H1) holds, which
                 is where the divisor obstruction already binds.  The eye
                 is level with the cube (elevation zero), so the vertices
                 with the same |S| are at one height and the scale |S| on
                 the left is exact.  The cube is drawn in layers (faces
                 turned away, hidden edges and vertex, faces turned towards
                 the eye, visible edges, visible vertices), so no visible
                 edge is veiled by a translucent face; the hidden vertex and
                 its three edges are dashed.
                 (b) the orbit of a Weil class alpha under K^x for K = Q(i),
                 n = 2, in W(A) (x) R = C with alpha -> 1, normalised to the
                 unit circle: iota(tau)^* acts through tau^4, so the orbit
                 directions are the points (tau / conj tau)^2; the line
                 Q alpha is the real axis.

  fig_lightcone  the Kuga-Satake picture for b = 3: the form
                 q = x^2 + y^2 - z^2 of signature (2,1), its null cone, the
                 two sheets of the hyperboloid q = -1, the positive plane
                 P = {z = 0} with its unit circle and an orthonormal basis
                 e_1, e_2, and the line P-perp meeting the upper sheet in
                 w_P = (0,0,1).  A second positive plane P' = w'-perp, with
                 w' = sinh(s) u + cosh(s) z, s = arctanh(1/2) and u the
                 horizontal direction to the right of the eye, is drawn with
                 its unit ellipse and its normal line, to show the
                 bijection between positive planes and points of one sheet.
                 P' is tilted about the line of sight, so it is seen open
                 and meets P along the line through the front and back
                 points of the unit circle.

Both use the camera of render3d.py, and both place their labels with the
Plate class of make_diagrams.py, which keeps every label off the ink of the
drawing and off every other label.
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from render3d import Camera, Scene, addv, smul, dot as dot3     # noqa: E402
from make_diagrams import (Plate, compile_plate, proj, TIP, soften,  # noqa
                           orbit_eye)

GEN = "make_more.py"


# =================================================================== escape
def fig_escape():
    """The eight positions a secant construction can occupy."""
    r, h = math.sqrt(2.0 / 3.0), 1.0 / math.sqrt(3.0)
    phi = [-90.0, 30.0, 150.0]
    E = [(r * math.cos(math.radians(f)), r * math.sin(math.radians(f)), h)
         for f in phi]
    tgt = (0.0, 0.0, 0.87)
    az, el = -38.0, 0.0
    cam = Camera(eye=orbit_eye(tgt, 30.0, az, el), target=tgt, focal=30.0,
                 scale=3.55)
    sc = Scene(cam)
    pl = Plate("fig_escape", GEN,
               "The eight positions a secant construction can occupy, as the "
               "vertices of a cube standing on its empty vertex.",
               thresh=226)

    def V(i, j, k):
        p = (0.0, 0.0, 0.0)
        for c, e in zip((i, j, k), E):
            if c:
                p = addv(p, e)
        return p

    def face(fixed_axis, val):
        def f(u, v):
            c = [0.0, 0.0, 0.0]
            others = [a for a in range(3) if a != fixed_axis]
            c[fixed_axis] = val
            c[others[0]], c[others[1]] = u, v
            p = (0.0, 0.0, 0.0)
            for ci, e in zip(c, E):
                p = addv(p, smul(ci, e))
            return p
        return f

    col = ["PClay", "PIndigo", "PGrass"]
    # E is orthonormal, so the outward normal of the face c_a = 1 is E[a]
    # and that of c_a = 0 is -E[a]; a face is turned towards the eye when
    # its normal is, and the hidden vertex is where the three faces turned
    # away meet.  The cube is drawn in layers: the faces turned away, the
    # hidden edges and vertex, the faces turned towards the eye, the
    # visible edges, the visible vertices; so no visible edge is veiled.
    light = (0.55, -0.75, 0.80)
    ln = math.sqrt(sum(c * c for c in light))
    light = tuple(c / ln for c in light)

    def facing(a, val):
        n = E[a] if val else smul(-1.0, E[a])
        c = face(a, val)(0.5, 0.5)
        return sum(n[i] * (cam.eye[i] - c[i]) for i in range(3)) > 0, n

    def face_tikz(a, val):
        _, n = facing(a, val)
        lam = max(0.0, sum(n[i] * light[i] for i in range(3)))
        f = face(a, val)
        pts = [f(0, 0), f(1, 0), f(1, 1), f(0, 1)]
        if (a, val) == (0, 1.0):          # the face where (H1) holds
            fill = "PClay!%d!white" % int(round(30 + 10 * lam))
            op = 0.50
        else:
            fill = "PSlate!%d!white" % int(round(14 + 12 * lam))
            op = 0.26
        return ("  \\path[fill=%s,fill opacity=%.2f] %s -- cycle;\n"
                % (fill, op, " -- ".join("(%.4f,%.4f)" % proj(cam, p)
                                          for p in pts)))

    faces = [(a, val) for a in range(3) for val in (0.0, 1.0)]
    back = [fv for fv in faces if not facing(*fv)[0]]
    front = [fv for fv in faces if facing(*fv)[0]]
    hidden = tuple(1 if (a, 1.0) in back else 0 for a in range(3))
    assert len(back) == 3 and hidden == (0, 0, 1) and (0, 1.0) in front
    verts = [(i, j, k) for i in range(2) for j in range(2) for k in range(2)]
    edges = []
    for v in verts:
        for a in range(3):
            if v[a] == 0:
                w = list(v)
                w[a] = 1
                edges.append((v, tuple(w), a))

    def edge_tikz(v, w, a, dashed):
        st = ("%s!70,line width=0.8pt,dash pattern=on 2.2pt off 1.8pt"
              % col[a]) if dashed else "%s,line width=1.25pt" % col[a]
        return "  \\draw[%s] (%.4f,%.4f) -- (%.4f,%.4f);\n" % (
            (st,) + proj(cam, V(*v)) + proj(cam, V(*w)))

    def vert_tikz(v):
        if v == (1, 1, 1):
            st = "circle,fill=PClay,draw=white,line width=0.7pt,inner sep=2.8pt"
        elif v == (0, 0, 0):
            st = "circle,fill=PTeal,draw=white,line width=0.7pt,inner sep=2.8pt"
        elif v == hidden:
            st = ("circle,fill=white,draw=PSlate!70,line width=0.7pt,"
                  "inner sep=1.8pt")
        else:
            st = ("circle,fill=white,draw=PInk!80,line width=0.9pt,"
                  "inner sep=2.0pt")
        return "  \\node[%s] at (%.4f,%.4f) {};\n" % ((st,) + proj(cam, V(*v)))

    pl.add("".join(face_tikz(*fv) for fv in back))
    pl.add("".join(edge_tikz(v, w, a, True) for v, w, a in edges
                   if hidden in (v, w)))
    pl.add(vert_tikz(hidden))
    pl.add("".join(face_tikz(*fv) for fv in front))
    pl.add("".join(edge_tikz(v, w, a, False) for v, w, a in edges
                   if hidden not in (v, w)))
    pl.add("".join(vert_tikz(v) for v in verts if v != hidden))

    # the grading |S|, read against the heights of the vertices
    xa = min(proj(cam, V(*v))[0] for v in [(1, 0, 0), (0, 1, 0), (0, 0, 1),
                                          (1, 1, 0), (1, 0, 1), (0, 1, 1)])
    xa -= 1.40
    ys = [proj(cam, (0.0, 0.0, m * h))[1] for m in range(4)]
    pl.add("  \\draw[PSlate,line width=0.45pt] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (xa, ys[0], xa, ys[3]))
    for m in range(4):
        pl.add("  \\draw[PSlate,line width=0.45pt] (%.3f,%.3f) -- (%.3f,%.3f);\n"
               % (xa, ys[m], xa + 0.12, ys[m]))
        pl.put(xa - 0.10, ys[m], r"$|S|=%d$" % m, color="PSlate",
               font=r"\footnotesize", anchor="e")

    def name(v):
        s = [str(a + 1) for a in range(3) if v[a]]
        return r"$\{%s\}$" % ",".join(s)

    order = [(1, 1, 1), (0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
             (1, 1, 0), (1, 0, 1), (0, 1, 1)]
    for v in order:
        if v == (1, 1, 1):
            txt, c, d = r"$\{1,2,3\}$: all three hold", "PClay", [90, 60, 120]
        elif v == (0, 0, 0):
            txt, c, d = (r"$\varnothing$: none holds; Markman's construction",
                         "PTeal", [-90, -60, -120])
        else:
            txt, c, d = name(v), "PInk", None
        pl.label(proj(cam, V(*v)), txt, color=c, dirs=d, rmin=0.12,
                 rmax=2.2, skip=0.14)
    outward = ([-150, 180, -120], [-30, 0, -60], [0, 20, -20])
    for a, t in enumerate((r"$+$(H1)", r"$+$(H2)", r"$+$(H3)")):
        mid = smul(0.5, E[a])
        pl.label(proj(cam, mid), t, color=col[a], font=r"\footnotesize",
                 dirs=outward[a], rmin=0.06, rmax=1.5, skip=0.08)
    # the shaded face: a leader from just inside its outer edge
    fp = face(0, 1.0)(0.45, 0.90)
    pl.label(proj(cam, fp), r"(H1) holds", color="PClay",
             dirs=[150, 180, 120], rmin=0.3, rmax=2.0, skip=0.30)

    # (b): the orbit of a Weil class spans the plane.  K = Q(i), n = 2, the
    # plane W(A) (x) R identified with C by alpha -> 1; iota(tau)^* acts by
    # tau^{2n} = N(tau)^n (tau/conj tau)^n, so the directions of the orbit
    # are the points (tau/conj tau)^2 of the unit circle.
    xs = [proj(cam, V(*v))[0] for v in verts]
    ysv = [proj(cam, V(*v))[1] for v in verts]
    cx, cy, rad = max(xs) + 3.95, 0.5 * (min(ysv) + max(ysv)) - 0.25, 1.75
    # the imaginary axis, and the line Q alpha along the real axis
    pl.add("  \\draw[PSlate!60,line width=0.35pt] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (cx, cy - rad - 0.40, cx, cy + rad + 0.40))
    pl.add("  \\draw[PIndigo,line width=0.8pt] (%.3f,%.3f) circle (%.3f);\n"
           % (cx, cy, rad))
    pl.add("  \\draw[PTeal,line width=1.0pt] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (cx - rad - 0.40, cy, cx + rad + 0.40, cy))
    seen = []
    for a in range(0, 9):
        for b in range(-8, 9):
            if a * a + b * b == 0 or a * a + b * b > 30 or math.gcd(a, b) != 1:
                continue
            ang = 4 * math.atan2(b, a)
            if any(abs(math.remainder(ang - t, 2 * math.pi)) < 1e-9
                   for t in seen):
                continue
            seen.append(ang)
            px, py = cx + rad * math.cos(ang), cy + rad * math.sin(ang)
            pl.add("  \\node[circle,fill=PIndigo,draw=white,line width=0.4pt,"
                   "inner sep=1.3pt] at (%.3f,%.3f) {};\n" % (px, py))
    pl.add("  \\node[circle,fill=PTeal,draw=white,line width=0.5pt,"
           "inner sep=2.0pt] at (%.3f,%.3f) {};\n" % (cx + rad, cy))
    pl.add("  \\node[circle,fill=PTeal,draw=white,line width=0.5pt,"
           "inner sep=2.0pt] at (%.3f,%.3f) {};\n" % (cx - rad, cy))
    pl.add("  \\node[circle,fill=PInk,inner sep=1.0pt] at (%.3f,%.3f) {};\n"
           % (cx, cy))
    ang = 4 * math.atan2(1, 2)
    pl.add("  \\draw[PIndigo,line width=0.6pt,%s] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (TIP, cx, cy, cx + (rad - 0.07) * math.cos(ang),
              cy + (rad - 0.07) * math.sin(ang)))
    pl.label((cx + rad, cy), r"$\alpha$", color="PTeal", dirs=[-60, -30],
             rmax=0.8, skip=0.1)
    pl.label((cx - rad, cy), r"$\iota(1+i)^{*}\alpha$",
             color="PTeal", font=r"\footnotesize", dirs=[-120, -150, -100],
             rmax=0.9, skip=0.1, penalty=2.0)
    pl.label((cx + rad * math.cos(ang), cy + rad * math.sin(ang)),
             r"$\iota(2+i)^{*}\alpha$", color="PIndigo",
             font=r"\footnotesize", dirs=[150, 120, 180], rmax=0.9, skip=0.1)
    pl.label((cx + rad + 0.40, cy), r"$\QQ\alpha$", color="PTeal",
             dirs=[30, 60, 0], rmax=0.5)
    ytop = max(cy + rad + 1.05, proj(cam, V(1, 1, 1))[1] + 0.50)
    pl.put(cx - rad - 0.35, ytop,
           r"(b)\ \ $\HW(A)\otimes\RR\cong\CC$, $K=\QQ(i)$, $n=2$",
           color="PInk", anchor="w")
    pl.put(xa - 1.05, ytop, r"(a)", color="PInk", anchor="w")
    pl.build()
    compile_plate("fig_escape")


# ================================================================ lightcone
def fig_lightcone():
    """The null cone of q = x^2 + y^2 - z^2, the two sheets of q = -1, and
    positive planes with their normal lines."""
    tgt = (0.0, 0.0, 0.05)
    AZ, EL = -55.0, 21.0
    cam = Camera(eye=orbit_eye(tgt, 18.0, AZ, EL), target=tgt,
                 focal=14.0, scale=3.15)
    sc = Scene(cam)
    pl = Plate("fig_lightcone", GEN,
               "The null cone of a form of signature (2,1), the two sheets of "
               "q = -1, and positive planes with their normal lines.",
               thresh=241)
    R = 1.60                      # height of the drawn cone
    RH = math.sqrt(R * R - 1.0)   # radius of the drawn sheet at the same height
    # the screen-right and the away-from-the-viewer directions in {z = 0}
    a = math.radians(AZ)
    U = (-math.sin(a), math.cos(a), 0.0)
    B = (-math.cos(a), -math.sin(a), 0.0)
    # the second positive plane P' = w'-perp, tilted about the line of sight
    s = math.atanh(0.5)
    ch, sh = math.cosh(s), math.sinh(s)
    w2 = addv(smul(sh, U), (0.0, 0.0, ch))      # w' = sinh s U + cosh s z
    e1p = addv(smul(ch, U), (0.0, 0.0, sh))     # q-orthonormal basis of P'
    e2p = B

    def q(v, w):
        return v[0] * w[0] + v[1] * w[1] - v[2] * w[2]
    assert abs(q(w2, w2) + 1) < 1e-12 and abs(q(e1p, e1p) - 1) < 1e-12
    assert abs(q(w2, e1p)) < 1e-12 and abs(q(w2, e2p)) < 1e-12
    # an orthonormal basis of P
    th1, th2 = math.radians(-36.0), math.radians(54.0)
    e1 = addv(smul(math.cos(th1), U), smul(math.sin(th1), B))
    e2 = addv(smul(math.cos(th2), U), smul(math.sin(th2), B))

    # the null cone q = 0
    for sgn in (1, -1):
        sc.surface(lambda t, rr, sgn=sgn: (rr * math.cos(t), rr * math.sin(t),
                                           sgn * rr),
                   (0, 2 * math.pi), (0.0, R), 48, 10, base="PBlue",
                   opacity=0.20, ambient=0.50, diffuse=0.40)
        for m in range(16):
            t = 2 * math.pi * m / 16
            sc.polyline([(0, 0, 0), (R * math.cos(t), R * math.sin(t),
                                     sgn * R)],
                        "soft,PBlue!50,line width=0.3pt", priority=1)
        sc.curve(lambda t, sgn=sgn: (R * math.cos(t), R * math.sin(t),
                                     sgn * R), (0, 2 * math.pi), 96,
                 "soft,PBlue!80,line width=0.6pt", priority=2, chunk=2)
    # the two sheets of q = -1; the upper one is the period domain
    for sgn, op in ((1, 0.58), (-1, 0.22)):
        sc.surface(lambda t, rr, sgn=sgn: (rr * math.cos(t), rr * math.sin(t),
                                           sgn * math.sqrt(1 + rr * rr)),
                   (0, 2 * math.pi), (0.0, RH), 48, 10, base="POchre",
                   opacity=op, ambient=0.40, diffuse=0.50)
        for rr in (0.45, 0.9):
            zz = sgn * math.sqrt(1 + rr * rr)
            sc.curve(lambda t, rr=rr, zz=zz: (rr * math.cos(t),
                                              rr * math.sin(t), zz),
                     (0, 2 * math.pi), 64,
                     "soft,POchre!80!black,line width=0.3pt", priority=2,
                     chunk=2)
        sc.curve(lambda t, sgn=sgn: (RH * math.cos(t), RH * math.sin(t),
                                     sgn * R), (0, 2 * math.pi), 96,
                 "soft,POchre!85!black,line width=0.6pt", priority=2, chunk=2)
    # the positive plane P = {z = 0}, its unit circle, e_1 and e_2
    L = 1.95

    def inP(u, v):
        return addv(smul(u, U), smul(v, B))
    sc.surface(inP, (-L, L), (-L, L), 12, 12, base="PClay", opacity=0.14,
               ambient=0.66, diffuse=0.26)
    corners = [inP(-L, -L), inP(L, -L), inP(L, L), inP(-L, L)]
    for c0, c1 in zip(corners, corners[1:] + corners[:1]):
        sc.polyline([c0, c1], "soft,PClay!70,line width=0.4pt", priority=1)
    sc.curve(lambda t: (math.cos(t), math.sin(t), 0.0), (0, 2 * math.pi), 96,
             "PClay,line width=1.0pt", priority=3, chunk=2)
    for e in (e1, e2):
        sc.polyline([(0, 0, 0), e], "PClay!80!black,line width=1.1pt," + TIP,
                    priority=4)
    # the second positive plane P', its unit ellipse and its normal line
    sc.surface(lambda uu, vv: addv(smul(uu, e1p), smul(vv, e2p)), (-1.0, 1.0),
               (-1.0, 1.0), 10, 10, base="PGrass", opacity=0.14, ambient=0.70,
               diffuse=0.2,
               cull=lambda Q: all(((dot3(p_, e1p) / (ch * ch + sh * sh)) ** 2
                                   + dot3(p_, e2p) ** 2) <= 1.0001
                                  for p_ in Q))
    sc.curve(lambda t: addv(smul(math.cos(t), e1p), smul(math.sin(t), e2p)),
             (0, 2 * math.pi), 96, "PGrass,line width=0.9pt", priority=3,
             chunk=2)
    k = 2.05 / ch
    sc.polyline([smul(-0.30 * k, w2), smul(k, w2)],
                "PGrass!85!black,line width=0.9pt", priority=3)
    # the line P-perp
    sc.polyline([(0, 0, -2.05), (0, 0, 2.05)], "PInk!80,line width=0.9pt",
                priority=3)
    pl.add(soften(sc.emit()))
    # the points, on top: the translucent near wall of the sheet would
    # otherwise veil them
    for p_, st in (((0, 0, 1.0), "circle,fill=POchre!80!black,draw=white,"
                    "line width=0.6pt,inner sep=2.1pt"),
                   (w2, "circle,fill=PGrass,draw=white,line width=0.6pt,"
                    "inner sep=2.1pt"),
                   ((0, 0, 0), "circle,fill=PInk,inner sep=1.3pt,draw=none")):
        pl.add("  \\node[%s] at (%.4f,%.4f) {};\n" % ((st,) + proj(cam, p_)))

    def extreme(pts, key):
        return max(pts, key=lambda p: key(proj(cam, p)))

    circ = [2 * math.pi * i / 360 for i in range(360)]
    rim = [(R * math.cos(t), R * math.sin(t), R) for t in circ]
    hrim = [(RH * math.cos(t), RH * math.sin(t), R) for t in circ]
    lrim = [(RH * math.cos(t), RH * math.sin(t), -R) for t in circ]
    cone_right = smul(0.70, extreme(rim, lambda q_: q_[0]))
    sheet_left = extreme(hrim, lambda q_: -q_[0])
    lsheet_left = extreme(lrim, lambda q_: -q_[0])
    corner = extreme(corners, lambda q_: q_[0])
    ell = [addv(smul(math.cos(t), e1p), smul(math.sin(t), e2p)) for t in circ]
    ell_right = extreme(ell, lambda q_: q_[0])

    pl.label(proj(cam, (0, 0, 2.05)), r"$P^{\perp}$", color="PInk",
             dirs=[90, 60, 120], rmax=0.5)
    pl.label(proj(cam, smul(k, w2)), r"$P'^{\perp}$", color="PGrass!85!black",
             dirs=[90, 45, 0], rmax=0.5)
    pl.label(proj(cam, (0, 0, 1.0)), r"$w_{P}$", color="POchre!80!black",
             dirs=[180, 150, 210], rmax=3.0, skip=0.12)
    pl.label(proj(cam, w2), r"$w_{P'}$", color="PGrass!85!black",
             dirs=[0, 30, -30], rmax=3.0, skip=0.12)
    pl.label(proj(cam, e1), r"$e_{1}$", color="PClay!80!black",
             dirs=[-60, -90, -30], rmax=2.0, skip=0.14)
    pl.label(proj(cam, e2), r"$e_{2}$", color="PClay!80!black",
             dirs=[-30, 0, -60], rmax=2.0, skip=0.14)
    pl.label(proj(cam, corner), r"$P=\{z=0\}$", color="PClay",
             dirs=[0, -30, 30], rmax=1.0)
    pl.label(proj(cam, cone_right), r"$q=0$", color="PBlue",
             dirs=[0, -20, 20], rmax=2.0)
    pl.label(proj(cam, sheet_left), r"$q=-1$", color="POchre!80!black",
             dirs=[180, 160, 200], rmax=2.5, skip=0.10)
    pl.label(proj(cam, lsheet_left), r"$q=-1$", color="POchre!80!black",
             dirs=[180, 160, 200], rmax=2.5, skip=0.10)
    pl.label(proj(cam, ell_right), r"$P'$", color="PGrass!85!black",
             dirs=[0, 20, -20, 40], rmax=2.5, skip=0.10)
    pl.build()
    compile_plate("fig_lightcone")


if __name__ == "__main__":
    which = sys.argv[1:] or ["escape", "lightcone"]
    if "escape" in which:
        fig_escape()
    if "lightcone" in which:
        fig_lightcone()
