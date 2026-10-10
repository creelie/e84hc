"""Interval certificate for family II of the paper (Proposition "prop:family2"), in ball
arithmetic with python-flint (Arb).  The point is stored in family2_point.json.

Family: F monic deg 7, H monic deg 2, G monic deg 12, K = s(s-1)(s-kappa), constants a, b, c,
  u0 = F^3 K, u1 = a H F K^5, u2 = b H^5 F^2, u3 = -(1+a+b) G^2, u4 = c H K  (u4 carries t^19),
  E(x, kappa) = coefficients of s^0..s^23 of u0+u1+u2+u3+u4 (the s^24 coefficient vanishes identically).
Checks, at kappa0 = -17/10 + 3i/10:
  (1) Krawczyk: a unique zero x* of E(., kappa0) in the box X around the stored point;
  (2) on X: a, b, c, 1+a+b are nonzero, and so are the resultants of the six pairs among F, H, G, K;
  (3) the tangent dx/dkappa = -J_x^{-1} J_kappa and I = sum over the roots of F of Res eta,
      eta = D / (M F^5) ds, D = det[[u1,u2,u4],[u1',u2',u4']_dot..] (see below), M = -abc(1+a+b) K^5 H^4 G,
      is enclosed in a ball not containing 0.
"""
import json
import os
from fractions import Fraction
import flint
from flint import acb, arb, acb_poly, acb_mat, ctx
ctx.prec = int(os.environ.get("FAMILY2_PREC", "1000"))   # working precision in bits
N = 24
S = acb_poly([0, 1])

def P(coeffs): return acb_poly(list(coeffs))

def parts(x, kappa):
    F = P(list(x[0:7]) + [acb(1)]); H = P(list(x[7:9]) + [acb(1)]); G = P(list(x[9:21]) + [acb(1)])
    K = S * (S - 1) * (S - kappa)
    return F, H, G, K, x[21], x[22], x[23]

def us(x, kappa):
    F, H, G, K, a, b, c = parts(x, kappa)
    return [F ** 3 * K, a * H * F * K ** 5, b * H ** 5 * F ** 2, -(1 + a + b) * G ** 2, c * H * K]

def coeffs(p, n):
    cs = p.coeffs(); return [cs[i] if i < len(cs) else acb(0) for i in range(n)]

def E(x, kappa):
    tot = acb_poly(0)
    for u in us(x, kappa): tot += u
    return coeffs(tot, 24)

def jac(x, kappa):
    """24 x 25 Jacobian (last column: d/dkappa), from exact partial derivatives."""
    F, H, G, K, a, b, c = parts(x, kappa)
    lam = 1 + a + b
    dF = 3 * F ** 2 * K + a * H * K ** 5 + 2 * b * H ** 5 * F
    dH = a * F * K ** 5 + 5 * b * H ** 4 * F ** 2 + c * K
    dG = -2 * lam * G
    cols = [S ** i * dF for i in range(7)] + [S ** i * dH for i in range(2)] + [S ** i * dG for i in range(12)]
    cols += [H * F * K ** 5 - G ** 2, H ** 5 * F ** 2 - G ** 2, H * K]
    dK = -(S * (S - 1))
    cols.append(dK * (F ** 3 + 5 * a * H * F * K ** 4 + c * H))
    J = acb_mat(N, N + 1)
    for k, col in enumerate(cols):
        cs = coeffs(col, 24)
        for i in range(N): J[i, k] = cs[i]
    return J

def sub(J, ncols):
    M = acb_mat(N, ncols)
    for i in range(N):
        for k in range(ncols): M[i, k] = J[i, k]
    return M

def sylvester(p, q):
    p = p.coeffs(); q = q.coeffs(); m, n = len(p) - 1, len(q) - 1
    M = acb_mat(m + n, m + n)
    for i in range(n):
        for j, c in enumerate(reversed(p)): M[i, i + j] = c
    for i in range(m):
        for j, c in enumerate(reversed(q)): M[n + i, i + j] = c
    return M.det()

def main():
    d = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "family2_point.json")))
    kr, ki = (Fraction(t) for t in d["kappa0"])
    kappa = acb(arb(kr.numerator) / kr.denominator, arb(ki.numerator) / ki.denominator)
    xt = [acb(arb(re), arb(im)) for re, im in d["x"]]           # stored centre (exact decimals)
    # (1) Krawczyk
    r = arb("1e-95")
    X = [z + acb(arb(0, r), arb(0, r)) for z in xt]
    Jm = sub(jac(xt, kappa), N)
    Y = acb_mat([[Jm[i, k].mid() for k in range(N)] for i in range(N)]).inv()
    Y = acb_mat([[Y[i, k].mid() for k in range(N)] for i in range(N)])
    Ex = acb_mat([[e] for e in E(xt, kappa)])
    JX = sub(jac(X, kappa), N)
    Id = acb_mat([[1 if i == k else 0 for k in range(N)] for i in range(N)])
    dX = acb_mat([[X[k] - xt[k]] for k in range(N)])
    Kx = acb_mat([[xt[k]] for k in range(N)]) - Y * Ex + (Id - Y * JX) * dX
    inside = True
    for k in range(N):
        for part in ("real", "imag"):
            kk = getattr(Kx[k, 0], part); xx = getattr(X[k], part)
            if not (kk.lower() > xx.lower() and kk.upper() < xx.upper()): inside = False
    rad = max(max(float(Kx[k, 0].real.rad()), float(Kx[k, 0].imag.rad())) for k in range(N))
    print("(1) Krawczyk K(X) inside X:", inside, "  max radius of K(X): %.2e (box radius 1e-95)" % rad)
    assert inside
    # (2) nondegeneracy on X
    F, H, G, K, a, b, c = parts(X, kappa)
    vals = {"a": a, "b": b, "c": c, "1+a+b": 1 + a + b,
            "Res(F,G)": sylvester(F, G), "Res(F,H)": sylvester(F, H), "Res(F,K)": sylvester(F, K),
            "Res(K,G)": sylvester(K, G), "Res(H,G)": sylvester(H, G), "Res(H,K)": sylvester(H, K)}
    for name, v in vals.items():
        ok = not v.contains(0)
        print("(2) %-9s nonzero: %s   |.| >= %s" % (name, ok, abs(v).lower().str(5) if ok else "?"))
        assert ok
    # (3) tangent and residue sum
    J = jac(X, kappa)
    xd = sub(J, N).solve(acb_mat([[-J[i, N]] for i in range(N)]))
    xd = [xd[k, 0] for k in range(N)]
    Fd = P(xd[0:7]); Hd = P(xd[7:9]); Gd = P(xd[9:21]); ad, bd, cd = xd[21], xd[22], xd[23]
    Kd = -(S * (S - 1))
    lam = 1 + a + b
    u1 = a * H * F * K ** 5; u2 = b * H ** 5 * F ** 2; u4 = c * H * K
    u1d = ad * H * F * K ** 5 + a * (Hd * F * K ** 5 + H * Fd * K ** 5 + 5 * H * F * K ** 4 * Kd)
    u2d = bd * H ** 5 * F ** 2 + b * (5 * H ** 4 * Hd * F ** 2 + 2 * H ** 5 * F * Fd)
    u4d = cd * H * K + c * (Hd * K + H * Kd)
    A = [[u1, u2, u4], [u1d, u2d, u4d], [u1.derivative(), u2.derivative(), u4.derivative()]]
    D = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
         + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    M = -(a * b * c * lam) * K ** 5 * H ** 4 * G
    F5 = F ** 5                                                  # monic, degree 35
    # solve Q * M = D (mod F^5) for Q of degree < 35, then I = [s^34] Q
    cols = []
    for i in range(35):
        cols.append(coeffs(divmod(S ** i * M, F5)[1], 35))
    Mat = acb_mat([[cols[k][i] for k in range(35)] for i in range(35)])
    rhs = acb_mat([[c_] for c_ in coeffs(divmod(D, F5)[1], 35)])
    Q = Mat.solve(rhs)
    I = Q[34, 0]
    print("(3) I =", I.str(12, radius=True))
    print("    0 in I:", I.contains(0), "   |I| >=", abs(I).lower().str(8))
    assert not I.contains(0)
    print("ALL CHECKS PASSED")

if __name__ == "__main__": main()
