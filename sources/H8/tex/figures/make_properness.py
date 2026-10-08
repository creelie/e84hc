#!/usr/bin/env python3
"""
make_properness.py

fig_properness: the dichotomy of cor:allornothing, computed in a model.

The period domain is drawn as the unit ball of R^3, and the strata as the
discs it cuts from the planes

        a x + b y + c z = e,   a, b, c, e integers, gcd 1, |e| < |(a,b,c)|,

of height h = max(|a|, |b|, |c|, |e|).  There are countably many; each is
closed; their union is dense, since it contains every rational point.  The
point

        s = (2^{1/4} - 7/10,  2^{1/2} - 6/5,  7/4 - 2^{3/4})

lies on none of them, because 1, 2^{1/4}, 2^{1/2}, 2^{3/4} are linearly
independent over Q (x^4 - 2 is irreducible by Eisenstein's criterion), so
a x + b y + c z = e at s forces a = b = c = 0.

  (a)  the ball with five strata of height at most two; the base point s_0
       on the stratum 2z = 1; the point s; and the square window of (b)
       around s, drawn to scale.
  (b)  the window: the section y = y_s, of side 0.06, with the traces of
       every stratum of height at most four that crosses it, and around s
       the largest discs free of the traces of height at most two and at
       most three, of the radii computed here.
  (c)  delta_H(s), the distance from s to the union of the strata of height
       at most H, for H = 1, ..., 10, on a logarithmic scale: positive for
       every H and tending to zero.

Every label is placed by the placer of make_plates.py and tested there.

Run:  python3 -B make_properness.py     (from the figures directory)
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from render3d import Camera, Scene, addv, smul, sub, unit, cross, dot, norm
from make_plates import (Plate, Mesh, seal, shift_tikz, extent, circle_pts,
                         silhouette_sphere, SS, FS, SM)

Q4 = 2 ** 0.25
S_PT = (Q4 - 0.7, Q4 ** 2 - 1.2, 1.75 - Q4 ** 3)
W_HALF = 0.03                       # half the side of the window of (b)


def strata(H):
    """Every stratum of height <= H meeting the open unit ball, once."""
    out = []
    for a in range(-H, H + 1):
        for b in range(-H, H + 1):
            for c in range(-H, H + 1):
                if (a, b, c) == (0, 0, 0):
                    continue
                if [v for v in (a, b, c) if v][0] < 0:
                    continue
                nn = math.sqrt(a * a + b * b + c * c)
                for e in range(-H, H + 1):
                    if math.gcd(math.gcd(a, b), math.gcd(c, e)) != 1:
                        continue
                    if abs(e) >= nn:
                        continue
                    out.append((a, b, c, e, max(abs(a), abs(b), abs(c),
                                                abs(e))))
    return out


def delta(H, P):
    s = S_PT
    return min(abs(a * s[0] + b * s[1] + c * s[2] - e)
               / math.sqrt(a * a + b * b + c * c)
               for a, b, c, e, h in P if h <= H)


def main():
    F = Plate("fig_properness",
              "The dichotomy of cor:allornothing in a model: strata cut by "
              "planes with integer coefficients, a base point on one, a very "
              "general point on none, and the distance to the strata of "
              "height at most H.", "make_properness.py")
    P10 = strata(10)
    D = [delta(H, P10) for H in range(1, 11)]
    assert all(v > 0 for v in D)
    assert all(D[k + 1] <= D[k] for k in range(9))
    s = S_PT
    assert norm(s) < 1

    # ------------------------------------------------------------ panel (a)
    az, el, dist = math.radians(-62.0), math.radians(24.0), 16.0
    eye = (dist * math.cos(el) * math.cos(az),
           dist * math.cos(el) * math.sin(az), dist * math.sin(el))
    cam = Camera(eye=eye, target=(0, 0, 0), focal=dist, scale=2.45)
    sc = Scene(cam, light=(0.30, -0.78, 0.88))
    # five strata: (a, b, c, e), colour
    BASE = (0, 0, 2, 1)
    SHOW = [((0, 0, 1, 0), "PBlue"), (BASE, "PClay"), ((1, 0, 0, 0), "PBlue"),
            ((0, 1, 1, 1), "PBlue"), ((1, 1, -1, -1), "PBlue")]

    def frame(n):
        n = unit(n)
        a = (1.0, 0, 0) if abs(n[0]) < 0.9 else (0, 1.0, 0)
        e1 = unit(cross(n, a))
        e2 = cross(n, e1)
        return e1, e2
    discs = []
    for (a, b, c, e), col in SHOW:
        nn = math.sqrt(a * a + b * b + c * c)
        n = (a / nn, b / nn, c / nn)
        ctr = smul(e / nn, n)
        r = math.sqrt(1 - (e / nn) ** 2)
        e1, e2 = frame(n)

        def f(t, phi, ctr=ctr, r=r, e1=e1, e2=e2):
            return addv(ctr, addv(smul(r * t * math.cos(phi), e1),
                                  smul(r * t * math.sin(phi), e2)))
        sc.surface(f, (0.0, 1.0), (0.0, 2 * math.pi), 10, 64, base=col,
                   ambient=0.62 if col == "PBlue" else 0.58, diffuse=0.34)
        discs.append((f, col, (a, b, c, e)))
    body = seal(sc.emit())
    sil = silhouette_sphere(cam, (0, 0, 0), 1.0, 240)
    x0 = min(p[0] for p in sil)
    y0 = min(p[1] for p in sil)
    dx, dy = -x0 + 0.55, -y0 + 0.45

    def P2(p):
        q = cam.project(p)[0]
        return (q[0] + dx, q[1] + dy)
    silp = [(p[0] + dx, p[1] + dy) for p in sil]
    C0 = P2((0, 0, 0))
    rad = (max(p[0] for p in silp) - min(p[0] for p in silp)) / 2
    F.raw(r"  \shade[ball color=WBlue!60!white,opacity=0.45] (%.3f,%.3f) "
          r"circle (%.3f);" % (C0[0], C0[1], rad))
    F.scene(shift_tikz(body, dx, dy),
            tagger=lambda st: "base" if "PClay" in st else "stratum")
    # the rims of the discs, drawn where no disc hides them
    def hidden(p):
        w = sub(p, eye)
        for f, col, (a, b, c, e) in discs:
            nn = math.sqrt(a * a + b * b + c * c)
            den = (a * w[0] + b * w[1] + c * w[2]) / nn
            if abs(den) < 1e-12:
                continue
            t = (e / nn - (a * eye[0] + b * eye[1] + c * eye[2]) / nn) / den
            if 1e-6 < t < 1 - 1e-4:
                q = addv(eye, smul(t, w))
                if norm(q) < 1.0:
                    return True
        return False
    from make_plates import visible_runs
    for f, col, pl in discs:
        pts = [f(1.0, 2 * math.pi * k / 240) for k in range(241)]
        for run in visible_runs(pts, hidden):
            F.path([P2(p) for p in run], col + "!85!black",
                   lw=0.8 if col == "PClay" else 0.6,
                   tag="base" if col == "PClay" else "stratum")
    F.path(silp, "PSlate", lw=0.75, tag="ball")
    # s_0 on the base stratum, s off every stratum
    s0 = (-0.34, -0.30, 0.5)
    assert abs(2 * s0[2] - 1) < 1e-12
    assert not hidden(s0) and not hidden(s)
    S0 = P2(s0)
    F.hollow(S0[0], S0[1], r=0.07, draw="PClay", lw=1.1, tag="s0")
    SP = P2(s)
    F.mark(SP[0], SP[1], r=0.045, fill="PInk", tag="s")
    # the window of (b), to scale, in the plane y = y_s
    wq = [addv(s, (sx * W_HALF, 0.0, sz * W_HALF))
          for sx, sz in ((-1, -1), (1, -1), (1, 1), (-1, 1))]
    wp = [P2(p) for p in wq]
    F.path(wp + [wp[0]], "PInk", lw=0.5, tag="win")
    XA1 = max(p[0] for p in silp)
    YA0, YA1 = min(p[1] for p in silp), max(p[1] for p in silp)

    # ------------------------------------------------------------ panel (b)
    SIDE = 3.9
    bx0 = XA1 + 1.05
    by0 = (YA0 + YA1) / 2 - SIDE / 2 + 0.15
    k = SIDE / (2 * W_HALF)

    def Wp(x, z):
        return (bx0 + (x - s[0] + W_HALF) * k, by0 + (z - s[2] + W_HALF) * k)
    P4 = strata(4)
    STY = {2: ("PBlue", 0.85), 3: ("PBlue!70", 0.5), 4: ("PBlue!45", 0.3)}
    nlines = {1: 0, 2: 0, 3: 0, 4: 0}
    free = {}
    for a, b, c, e, h in sorted(P4, key=lambda t: -t[4]):
        if (a, c) == (0, 0):
            continue
        # the trace a x + c z = e - b y_s on the section y = y_s
        rhs = e - b * s[1]
        dd = abs(a * s[0] + c * s[2] - rhs) / math.hypot(a, c)
        for H in (2, 3):
            if h <= H:
                free[H] = min(free.get(H, 9.0), dd)
        # clip the line to the window
        pts = []
        lo, hi = -W_HALF, W_HALF
        if abs(c) > 1e-12:
            for x in (s[0] + lo, s[0] + hi):
                z = (rhs - a * x) / c
                if s[2] + lo - 1e-12 <= z <= s[2] + hi + 1e-12:
                    pts.append((x, z))
        if abs(a) > 1e-12:
            for z in (s[2] + lo, s[2] + hi):
                x = (rhs - c * z) / a
                if s[0] + lo - 1e-12 <= x <= s[0] + hi + 1e-12:
                    pts.append((x, z))
        pts = sorted(set((round(x, 12), round(z, 12)) for x, z in pts))
        if len(pts) < 2:
            continue
        assert h >= 2
        nlines[h] += 1
        colr, lw = STY[h]
        F.path([Wp(*pts[0]), Wp(*pts[-1])], colr, lw=lw, tag="trace")
    assert abs(free[2] - 0.00525) < 5e-6 and abs(free[3] - 0.00204) < 5e-6
    SW = Wp(s[0], s[2])
    for H, sty in ((2, "PClay,dash pattern=on 2pt off 1.4pt"),
                   (3, "PClay,dash pattern=on 1.2pt off 1pt")):
        ring = circle_pts(SW[0], SW[1], free[H] * k, 90)
        F.path(ring + [ring[0]], sty, lw=0.7, tag="free")
    F.mark(SW[0], SW[1], r=0.05, fill="PInk", tag="s")
    frame_ = [(bx0, by0), (bx0 + SIDE, by0), (bx0 + SIDE, by0 + SIDE),
              (bx0, by0 + SIDE)]
    F.path(frame_ + [frame_[0]], "PInk", lw=0.6, tag="frame")
    # the zoom lines from the small square of (a) to the frame of (b)
    F.path([wp[3], frame_[3]], "PSlate!70", lw=0.35, tag="zoom")
    F.path([wp[0], frame_[0]], "PSlate!70", lw=0.35, tag="zoom")
    # the scale of the window
    F.text(bx0 + SIDE / 2, by0 - 0.24, r"$0.06$", "PInk", FS, tag="scale")
    F.path([(bx0, by0 - 0.08), (bx0, by0 - 0.40)], "PSlate", lw=0.4,
           tag="scalebar")
    F.path([(bx0 + SIDE, by0 - 0.08), (bx0 + SIDE, by0 - 0.40)], "PSlate",
           lw=0.4, tag="scalebar")
    F.path([(bx0, by0 - 0.24), (bx0 + SIDE / 2 - 0.36, by0 - 0.24)],
           "PSlate", lw=0.4, tag="scalebar")
    F.path([(bx0 + SIDE / 2 + 0.36, by0 - 0.24), (bx0 + SIDE, by0 - 0.24)],
           "PSlate", lw=0.4, tag="scalebar")
    # the legend of the heights
    ly = by0 - 0.72
    lx = bx0 + 0.05
    for h, txt in ((2, r"$h\le2$"), (3, r"$h=3$"), (4, r"$h=4$")):
        colr, lw = STY[h]
        F.path([(lx, ly), (lx + 0.40, ly)], colr, lw=max(lw, 0.45),
               tag="legend")
        F.text(lx + 0.48, ly, txt, "PInk", FS, anchor="west", tag="legend")
        lx += 1.32

    # ------------------------------------------------------------ panel (c)
    cx0 = bx0 + SIDE + 1.55
    cw, ch = 3.35, 3.30
    cy0 = by0 + 0.25
    lmin, lmax = -5.0, -1.0

    def C(H, v):
        return (cx0 + (H - 1) / 9.0 * cw,
                cy0 + (math.log10(v) - lmin) / (lmax - lmin) * ch)
    F.path([(cx0, cy0 + ch + 0.10), (cx0, cy0), (cx0 + cw + 0.12, cy0)],
           "PInk", lw=0.55, tag="axes")
    for ex in range(-5, 0):
        y = C(1, 10.0 ** ex)[1]
        F.path([(cx0 - 0.07, y), (cx0, y)], "PInk", lw=0.45, tag="axes")
        F.path([(cx0, y), (cx0 + cw, y)], "PRule!60", lw=0.25, tag="grid")
        F.text(cx0 - 0.24, y, r"$10^{%d}$" % ex, "PInk", FS, anchor="east",
               tag="ytick")
    for H in range(1, 11):
        x = C(H, 1e-3)[0]
        F.path([(x, cy0), (x, cy0 - 0.07)], "PInk", lw=0.45, tag="axes")
        if H in (1, 2, 4, 6, 8, 10):
            F.text(x, cy0 - 0.27, r"$%d$" % H, "PInk", FS, tag="xtick")
    F.text(cx0 + cw / 2, cy0 - 0.72, r"$H$", "PInk", SM, tag="xname")
    stair = []
    for H in range(1, 11):
        a = C(H, D[H - 1])
        if stair:
            stair.append((a[0], stair[-1][1]))
        stair.append(a)
    F.path(stair, "PClay", lw=0.9, tag="stair")
    for H in range(1, 11):
        a = C(H, D[H - 1])
        F.mark(a[0], a[1], r=0.045, fill="PClay", tag="stair")
    F.text(cx0 + 0.12, cy0 + ch + 0.30, r"$\delta_{H}(s)$", "PInk", SM,
           anchor="west", tag="yname")

    # ------------------------------------------------------------ labels
    RA = (-9, -9, XA1 + 0.7, 99)
    F.request(S0, r"$s_{0}$", "PClay", SM, clear=0.07, region=RA)
    F.request(SP, r"$s$", "PInk", SM, clear=0.05, region=RA, prefer=200,
              spread=80)
    F.request(P2((0.0, -0.96, 0.0)), r"$\cD_{n,n}$", "PSlate", SM,
              region=RA)
    F.request(P2(discs[1][0](1.0, 2.2)), r"$2z=1$", "PClay", FS, region=RA)
    F.request(P2(discs[0][0](1.0, 3.9)), r"$z=0$", "PBlue!80!black", FS,
              region=RA)
    F.request(P2(discs[3][0](1.0, 1.3)), r"$y+z=1$", "PBlue!80!black", FS,
              region=RA)
    F.request(SW, r"$s$", "PInk", SM, clear=0.05, prefer=0, spread=60,
              rmax=0.5)
    F.solve()
    F.text(0.0, YA1 + 0.35, r"\textup{(a)}", "PInk", SM, anchor="north west",
           tag="letter")
    F.text(bx0 - 0.05, by0 + SIDE + 0.55, r"\textup{(b)}", "PInk", SM,
           anchor="north west", tag="letter")
    F.text(cx0 - 0.95, by0 + SIDE + 0.55, r"\textup{(c)}", "PInk", SM,
           anchor="north west", tag="letter")
    print("   traces in the window by height:", nlines,
          " free radii:", {h: round(v, 5) for h, v in free.items()})
    print("   delta_H(s):", ["%.2e" % v for v in D])
    return F


if __name__ == "__main__":
    main().write()
