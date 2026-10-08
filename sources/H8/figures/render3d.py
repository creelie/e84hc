#!/usr/bin/env python3
"""
render3d.py

A small painter's-algorithm renderer that emits TikZ.  Surfaces are given
parametrically, meshed into quads, shaded by a Lambert term against a fixed
light, and merged with curves and points into a single depth-sorted draw list,
so that occlusion is correct everywhere.  The camera is a genuine perspective
camera: eye, target, up, focal length.

Nothing here is specific to the paper; the figures that use it pass their
own surfaces, curves, solids and labels.

DETAIL scales every mesh and every sampled curve.  At 1.5 each surface
carries 2.25 times as many shaded facets as its generator asks for and every
curve is sampled half as finely again, which is the setting used for the
paper; set it to 1.0 to reproduce the coarser meshes quickly.
"""

import math

DETAIL = 1.5

# ----------------------------------------------------------------- vectors

def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def addv(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def smul(t, a):
    return (t * a[0], t * a[1], t * a[2])


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def norm(a):
    return math.sqrt(dot(a, a))


def unit(a):
    n = norm(a)
    return (a[0] / n, a[1] / n, a[2] / n)


# ------------------------------------------------------------------ camera

class Camera:
    def __init__(self, eye, target=(0, 0, 0), up=(0, 0, 1), focal=7.0,
                 scale=1.0):
        self.eye = eye
        self.w = unit(sub(eye, target))              # towards the eye
        self.u = unit(cross(up, self.w))
        self.v = cross(self.w, self.u)
        self.focal = focal
        self.scale = scale

    def project(self, p):
        d = sub(p, self.eye)
        x, y, z = dot(d, self.u), dot(d, self.v), dot(d, self.w)
        depth = -z                                   # positive in front
        if depth <= 1e-6:
            depth = 1e-6
        k = self.focal / depth * self.scale
        return (x * k, y * k), depth

    def towards(self, p):
        return unit(sub(self.eye, p))


# ------------------------------------------------------------- draw buffer

class Scene:
    def __init__(self, cam, light=(0.55, -0.75, 0.80)):
        self.cam = cam
        self.light = unit(light)
        self.items = []          # (depth, priority, tikz)

    def add(self, depth, tikz, priority=0):
        self.items.append((depth, priority, tikz))

    # -- surfaces ----------------------------------------------------------
    def surface(self, f, urange, vrange, nu, nv, base="PBlue",
                ambient=0.34, diffuse=0.66, edge=None, twosided=True,
                cull=None, opacity=None):
        """f(u,v) -> point.  Meshes [u0,u1] x [v0,v1] into nu x nv quads,
        each multiplied by DETAIL when it is larger than one."""
        if nu > 1:
            nu = int(round(nu * DETAIL))
        if nv > 1:
            nv = int(round(nv * DETAIL))
        u0, u1 = urange
        v0, v1 = vrange
        for i in range(nu):
            for j in range(nv):
                ua, ub = u0 + (u1 - u0) * i / nu, u0 + (u1 - u0) * (i + 1) / nu
                va, vb = v0 + (v1 - v0) * j / nv, v0 + (v1 - v0) * (j + 1) / nv
                P = [f(ua, va), f(ub, va), f(ub, vb), f(ua, vb)]
                if cull is not None and not cull(P):
                    continue
                c = smul(0.25, [sum(p[k] for p in P) for k in range(3)]
                         and (P[0][0] + P[1][0] + P[2][0] + P[3][0],
                              P[0][1] + P[1][1] + P[2][1] + P[3][1],
                              P[0][2] + P[1][2] + P[2][2] + P[3][2]))
                n = cross(sub(P[1], P[0]), sub(P[3], P[0]))
                if norm(n) < 1e-12:
                    continue
                n = unit(n)
                if twosided and dot(n, self.cam.towards(c)) < 0:
                    n = smul(-1.0, n)
                lam = max(0.0, dot(n, self.light))
                inten = ambient + diffuse * lam
                pct = int(max(4, min(96, round(100 * (1.0 - inten)))))
                pts, depths = zip(*[self.cam.project(p) for p in P])
                path = " -- ".join("(%.4f,%.4f)" % q for q in pts)
                op = ("fill opacity=%.2f," % opacity) if opacity else ""
                estyle = ("draw=%s!%d!white,line width=0.12pt,"
                          % (base, min(96, pct + 16))) if edge else "draw=none,"
                self.add(sum(depths) / 4.0,
                         "  \\path[%s%sfill=%s!%d!white] %s -- cycle;\n"
                         % (estyle, op, base, pct, path))

    # -- curves ------------------------------------------------------------
    def curve(self, g, trange, n, style, priority=1, chunk=1):
        """g(t) -> point, drawn as n depth-sorted short segments."""
        n = max(1, int(round(n * DETAIL)))
        t0, t1 = trange
        pts = [g(t0 + (t1 - t0) * k / n) for k in range(n + 1)]
        pr = [self.cam.project(p) for p in pts]
        k = 0
        while k < n:
            m = min(k + chunk, n)
            seg = " -- ".join("(%.4f,%.4f)" % pr[q][0] for q in range(k, m + 1))
            d = sum(pr[q][1] for q in range(k, m + 1)) / (m - k + 1)
            self.add(d, "  \\draw[%s] %s;\n" % (style, seg), priority)
            k = m

    def front_runs(self, g, normal, trange, n):
        """Sample g on [t0,t1]; return the maximal runs of consecutive samples
        whose surface normal faces the camera.  Used to draw curves that lie
        on a surface without fighting the mesh for depth."""
        t0, t1 = trange
        pts = [g(t0 + (t1 - t0) * k / n) for k in range(n + 1)]
        vis = [dot(normal(p), self.cam.towards(p)) > 0.0 for p in pts]
        runs, cur = [], []
        for p, ok in zip(pts, vis):
            if ok:
                cur.append(p)
            elif cur:
                if len(cur) > 1:
                    runs.append(cur)
                cur = []
        if len(cur) > 1:
            runs.append(cur)
        return runs

    def polyline(self, pts, style, priority=2):
        pr = [self.cam.project(p) for p in pts]
        seg = " -- ".join("(%.4f,%.4f)" % q[0] for q in pr)
        d = sum(q[1] for q in pr) / len(pr)
        self.add(d, "  \\draw[%s] %s;\n" % (style, seg), priority)

    def dot3(self, p, style, priority=3):
        (x, y), d = self.cam.project(p)
        self.add(d, "  \\node[%s] at (%.4f,%.4f) {};\n" % (style, x, y),
                 priority)

    def label3(self, p, text, style="", priority=4, offset=(0, 0)):
        (x, y), d = self.cam.project(p)
        self.add(d, "  \\node[%s] at (%.4f,%.4f) {%s};\n"
                 % (style, x + offset[0], y + offset[1], text), priority)

    # -- solids ------------------------------------------------------------
    def box(self, center, size, base="PSlate", opacity=None, ambient=0.40,
            diffuse=0.52, edge_style=None, priority_edges=2):
        """An axis-parallel rectangular prism with shaded faces and, if
        edge_style is given, its twelve edges drawn in that style."""
        cx, cy, cz = center
        hx, hy, hz = size[0] / 2.0, size[1] / 2.0, size[2] / 2.0
        faces = [
            lambda u, v: (cx + u, cy + v, cz - hz),
            lambda u, v: (cx + u, cy + v, cz + hz),
            lambda u, v: (cx + u, cy - hy, cz + v),
            lambda u, v: (cx + u, cy + hy, cz + v),
            lambda u, v: (cx - hx, cy + u, cz + v),
            lambda u, v: (cx + hx, cy + u, cz + v),
        ]
        ranges = [((-hx, hx), (-hy, hy)), ((-hx, hx), (-hy, hy)),
                  ((-hx, hx), (-hz, hz)), ((-hx, hx), (-hz, hz)),
                  ((-hy, hy), (-hz, hz)), ((-hy, hy), (-hz, hz))]
        for f, (ur, vr) in zip(faces, ranges):
            self.surface(f, ur, vr, 1, 1, base=base, opacity=opacity,
                         ambient=ambient, diffuse=diffuse)
        if edge_style:
            xs, ys, zs = (cx - hx, cx + hx), (cy - hy, cy + hy), (cz - hz, cz + hz)
            for y in ys:
                for z in zs:
                    self.polyline([(xs[0], y, z), (xs[1], y, z)], edge_style,
                                  priority_edges)
            for x in xs:
                for z in zs:
                    self.polyline([(x, ys[0], z), (x, ys[1], z)], edge_style,
                                  priority_edges)
            for x in xs:
                for y in ys:
                    self.polyline([(x, y, zs[0]), (x, y, zs[1])], edge_style,
                                  priority_edges)

    def arrow(self, pts, style, priority=4):
        """A polyline whose last segment carries an arrow tip."""
        self.polyline(pts, style + ",-{Stealth[length=4.2pt,width=3.4pt]}",
                      priority)

    # -- output ------------------------------------------------------------
    def emit(self):
        self.items.sort(key=lambda it: (-it[0], it[1]))
        return "".join(it[2] for it in self.items)

    def bbox(self):
        return None
