"""Independent check of the residue in Proposition "prop:family44", by a contour integral.

At the stored point of family44_point.json, in 40-digit arithmetic (mpmath), the tangent
vector v with d kappa(v) = 1 is obtained from the Jacobian, and
  I_02 = (1/2 pi i) * integral over |s| = R of eta_v,  eta_v = A Delta_v / (u0 u2) ds,
is computed by the trapezoidal rule on a circle that encloses every zero of the blocks.  This uses
neither interval arithmetic nor the series expansion at infinity of family44_certificate.py.
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


def psc(p, c):
    return [c * a for a in p]


def ppow(p, e):
    r = [mp.mpc(1)]
    for _ in range(e):
        r = pmul(r, p)
    return r


def pder(p):
    return [i * p[i] for i in range(1, len(p))] or [mp.mpc(0)]


def pval(p, x):
    r = mp.mpc(0)
    for a in reversed(p):
        r = r * x + a
    return r


def main():
    d = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "family44_point.json")))
    kr, ki = (Fraction(t) for t in d["kappa0"])
    kappa = mp.mpc(mp.mpf(kr.numerator) / kr.denominator, mp.mpf(ki.numerator) / ki.denominator)
    x = [mp.mpc(mp.mpf(re), mp.mpf(im)) for re, im in d["x"]]
    s = [mp.mpc(0), mp.mpc(1)]
    P = x[0:5] + [mp.mpc(1)]
    Q = x[5:8] + [mp.mpc(1)]
    S = [kappa, x[8], mp.mpc(1)]
    c0, c1, c3 = x[9], x[10], x[11]
    s3 = ppow(s, 3)
    total = padd(psc(pmul(s3, pmul(P, Q)), c0), psc(pmul(P, ppow(Q, 2)), c1), [mp.mpc(1)],
                 psc(pmul(Q, ppow(S, 4)), c3), pmul(s, ppow(P, 2)))
    res = max(abs(a) for a in total)
    # Jacobian: columns s^i dP (5), s^i dQ (3), s dS (r1), d/dc0, d/dc1, d/dc3, and dS (kappa)
    dP = padd(psc(pmul(s3, Q), c0), psc(ppow(Q, 2), c1), psc(pmul(s, P), 2))
    dQ = padd(psc(pmul(s3, P), c0), psc(pmul(P, Q), 2 * c1), psc(ppow(S, 4), c3))
    dS = psc(pmul(Q, ppow(S, 3)), 4 * c3)
    cols = [pmul(ppow(s, i), dP) for i in range(5)] + [pmul(ppow(s, i), dQ) for i in range(3)]
    cols += [pmul(s, dS), pmul(s3, pmul(P, Q)), pmul(P, ppow(Q, 2)), pmul(Q, ppow(S, 4))]
    J = mp.matrix(12, 12)
    rhs = mp.matrix(12, 1)
    for k, col in enumerate(cols):
        for i in range(12):
            J[i, k] = col[i] if i < len(col) else 0
    for i in range(12):
        rhs[i] = -(dS[i] if i < len(dS) else 0)
    xd = mp.lu_solve(J, rhs)
    Pd = [xd[k] for k in range(5)]
    Qd = [xd[k] for k in range(5, 8)]
    Sd = [mp.mpc(1), xd[8]]
    c0d, c1d, c3d = xd[9], xd[10], xd[11]
    u1 = psc(pmul(P, ppow(Q, 2)), c1)
    u3 = psc(pmul(Q, ppow(S, 4)), c3)
    u4 = pmul(s, ppow(P, 2))
    u1d = padd(psc(pmul(P, ppow(Q, 2)), c1d), psc(padd(pmul(Pd, ppow(Q, 2)), psc(pmul(P, pmul(Q, Qd)), 2)), c1))
    u3d = padd(psc(pmul(Q, ppow(S, 4)), c3d), psc(padd(pmul(Qd, ppow(S, 4)), psc(pmul(Q, pmul(ppow(S, 3), Sd)), 4)), c3))
    u4d = psc(pmul(s, pmul(P, Pd)), 2)
    A_over = (P, S)                        # A/(u0 u2) = P S^3 / (c0 s^2)
    rows = [(u1, u1d), (u3, u3d), (u4, u4d)]
    roots = mp.polyroots(list(reversed(P)), maxsteps=200, extraprec=200) + \
        mp.polyroots(list(reversed(Q)), maxsteps=200, extraprec=200) + \
        mp.polyroots(list(reversed(S)), maxsteps=200, extraprec=200)
    R = 2 * max(1, max(abs(r) for r in roots))
    N = 2048
    acc = mp.mpc(0)
    for n in range(N):
        z = R * mp.expj(2 * mp.pi * n / N)
        v = [(pval(u, z), pval(ud, z), pval(pder(u), z)) for u, ud in rows]
        a = [[1, 1, 1], [w[1] / w[0] for w in v], [w[2] / w[0] for w in v]]
        Delta = mp.det(mp.matrix(a))
        f = pval(A_over[0], z) * pval(A_over[1], z) ** 3 / (c0 * z ** 2) * Delta
        acc += f * z
    I = acc / N
    print("residual of the stored point: %s" % mp.nstr(res, 3))
    print("contour radius R = %s, %d nodes" % (mp.nstr(R, 4), N))
    print("I_02 by contour integral = %s" % mp.nstr(I, 15))
    return I


if __name__ == "__main__":
    main()
