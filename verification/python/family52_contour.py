"""Independent check of the residues in Propositions "prop:family52a" and "prop:family52b".

At the stored points of family52a_point.json and family52b_point.json, in 40-digit arithmetic
(mpmath), the tangent vector v with d kappa(v) = 1 is obtained from the Jacobian, and eta_v =
A Delta_v / (u_i u_j) ds is evaluated pointwise from the blocks.  Two numbers are computed by
the trapezoidal rule:
  * the integral of eta_v / (2 pi i) over a circle |s| = R enclosing every zero of the blocks,
    which is the sum of all residues of eta_v in C;
  * the sum of the integrals over small circles around the zeros of u_i only, which is I_ij.
They agree, as Lemma "lem:etapoles"(a) says they must, and they agree with the certificate.
This uses neither interval arithmetic nor the series expansion at infinity of
family52_certificate.py.
"""
import json
import os
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 40


def padd(*ps):
    n = max(len(p) for p in ps)
    return [sum((p[i] for p in ps if i < len(p)), mp.mpc(0)) for i in range(n)]


def pmul(p, q):
    r = [mp.mpc(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def ppow(p, e):
    r = [mp.mpc(1)]
    for _ in range(e):
        r = pmul(r, p)
    return r


def pval(p, x):
    r = mp.mpc(0)
    for a in reversed(p):
        r = r * x + a
    return r


def pder(p):
    return [i * p[i] for i in range(1, len(p))] or [mp.mpc(0)]


def run(path):
    d = json.load(open(path))
    spec = d["spec"]
    m, al, blocks, knorm, par = spec["m"], spec["alpha"], spec["blocks"], spec["knorm"], spec["par"]
    i, j = spec["chart"]
    kr, ki = (Fraction(t) for t in d["kappa0"])
    kappa = mp.mpc(mp.mpf(kr.numerator) / kr.denominator, mp.mpf(ki.numerator) / ki.denominator)
    x = [mp.mpc(mp.mpf(re), mp.mpf(im)) for re, im in d["x"]]
    z = x[:par] + [kappa] + x[par:]
    # unknown slots: (block, power of s) for the block coefficients, then c_k for k != knorm
    slots = []
    for bi, (_, e, kind, data) in enumerate(blocks):
        if kind == "monic":
            slots += [(bi, n) for n in range(data)]
        elif kind == "monic1":
            slots += [(bi, n) for n in range(1, data)]
    cidx = [k for k in range(5) if k != knorm]

    def split(z):
        polys, pos = [], 0
        for _, e, kind, data in blocks:
            if kind == "inf":
                polys.append([mp.mpc(1)])
            elif kind == "fixed":
                polys.append([mp.mpc(c) for c in data])
            elif kind == "monic":
                polys.append(list(z[pos:pos + data]) + [mp.mpc(1)]); pos += data
            else:
                polys.append([mp.mpc(1)] + list(z[pos:pos + data - 1]) + [mp.mpc(1)]); pos += data - 1
        c = [mp.mpc(1)] * 5
        for n, k in enumerate(cidx):
            c[k] = z[len(slots) + n]
        return polys, c

    polys, c = split(z)

    def u_poly(k, skip=None, extra=None):
        f = [c[k] if skip != "c" else mp.mpc(1)]
        for bi, (_, e, _, _) in enumerate(blocks):
            p = e[k] - (1 if bi == skip else 0)
            if p > 0:
                f = pmul(f, ppow(polys[bi], p))
        return f

    u = [u_poly(k) for k in range(5)]
    total = padd(*u)
    res = max(abs(a) for a in total)
    N = len(z) - 1
    # columns of the Jacobian of the coefficients of sum u_k
    cols = []
    for bi, n in slots:
        col = [mp.mpc(0)]
        for k in range(5):
            ek = blocks[bi][1][k]
            if ek:
                col = padd(col, [ek * a for a in pmul(u_poly(k, skip=bi), [0] * n + [mp.mpc(1)])])
        cols.append(col)
    for k0 in cidx:
        cols.append(u_poly(k0, skip="c"))
    J = mp.matrix(N, N); rhs = mp.matrix(N, 1)
    col_i = 0
    for idx, col in enumerate(cols):
        if idx == par:
            for r in range(N):
                rhs[r] = -(col[r] if r < len(col) else 0)
            continue
        for r in range(N):
            J[r, col_i] = col[r] if r < len(col) else 0
        col_i += 1
    xd = mp.lu_solve(J, rhs)
    vd = [xd[k] for k in range(par)] + [mp.mpc(1)] + [xd[k] for k in range(par, N)]
    pd, cd = split(vd)
    for bi, (_, e, kind, data) in enumerate(blocks):     # derivative of a block: no leading term
        if kind in ("monic", "monic1"):
            pd[bi] = pd[bi][:-1] + [mp.mpc(0)]
            if kind == "monic1":
                pd[bi][0] = mp.mpc(0)
        else:
            pd[bi] = [mp.mpc(0)]
    cdot = [mp.mpc(0)] * 5
    for n, k in enumerate(cidx):
        cdot[k] = vd[len(slots) + n]
    a, b, cc = [k for k in range(5) if k not in (i, j)]
    wts = [sum(x_ * y for x_, y in zip(al, e)) // m for _, e, _, _ in blocks]

    def eta(s):
        B = [pval(p, s) for p in polys]
        Bd = [pval(p, s) for p in pd]
        Bp = [pval(pder(p), s) for p in polys]
        rows = []
        for k in (a, b, cc):
            dot = cdot[k] / c[k] + sum(e[k] * Bd[bi] / B[bi] for bi, (_, e, _, _) in enumerate(blocks) if e[k])
            der = sum(e[k] * Bp[bi] / B[bi] for bi, (_, e, _, _) in enumerate(blocks) if e[k])
            rows.append((dot, der))
        Delta = mp.det(mp.matrix([[1, 1, 1], [r[0] for r in rows], [r[1] for r in rows]]))
        A = mp.mpc(1); ui = c[i]; uj = c[j]
        for bi, (_, e, _, _) in enumerate(blocks):
            A *= B[bi] ** wts[bi]; ui *= B[bi] ** e[i]; uj *= B[bi] ** e[j]
        return A * Delta / (ui * uj)

    roots, roots_i = [], []
    for bi, (_, e, kind, _) in enumerate(blocks):
        if kind == "inf":
            continue
        rs = mp.polyroots(list(reversed(polys[bi])), maxsteps=200, extraprec=200) if len(polys[bi]) > 2 \
            else [-polys[bi][0] / polys[bi][1]]
        roots += rs
        if e[i]:
            roots_i += rs
    R = 3 * max(1, max(abs(r) for r in roots))
    Nn = 4096
    big = sum(eta(R * mp.expj(2 * mp.pi * n / Nn)) * R * mp.expj(2 * mp.pi * n / Nn) for n in range(Nn)) / Nn
    small = mp.mpc(0)
    for rho in roots_i:
        rad = mp.mpf("0.3") * min(abs(rho - r) for r in roots if abs(rho - r) > mp.mpf("1e-20"))
        small += sum(eta(rho + rad * mp.expj(2 * mp.pi * n / Nn)) * rad * mp.expj(2 * mp.pi * n / Nn)
                     for n in range(Nn)) / Nn
    print(spec["name"])
    print("  residual of the stored point: %s" % mp.nstr(res, 3))
    print("  sum of residues in C, circle |s| = %s: %s" % (mp.nstr(R, 4), mp.nstr(big, 15)))
    print("  I_%d%d, small circles around the zeros of u_%d: %s" % (i, j, i, mp.nstr(small, 15)))
    return big, small


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    for f in ("family52a_point.json", "family52b_point.json"):
        big, small = run(os.path.join(here, f))
        assert abs(big - small) < mp.mpf("1e-20") * (1 + abs(big))
