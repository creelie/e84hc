"""Interval certificate for the block family of degree 44 (Proposition "prop:family44"), in
ball arithmetic with python-flint (Arb).  The point is stored in family44_point.json.

Character alpha = (1, 5, 8, 33, 41) of the Fermat threefold of degree 44, <alpha> = 2.
Blocks s, t, P (monic quintic), Q (monic cubic), S (monic quadratic):
  u0 = c0 s^3 P Q,  u1 = c1 P Q^2,  u2 = t^11,  u3 = c3 Q S^4,  u4 = s P^2     (D = 11).
Unknowns x = (p0..p4, q0..q2, r1, c0, c1, c3), parameter kappa = r0 (S = s^2 + r1 s + r0).
E(x, kappa) = coefficients of s^0..s^11 of u0 + u1 + 1 + u3 + u4 (t = 1).
Chart (0,2): A/(u0 u2) = P S^3/(c0 s^2) and eta_v = N_v / (c0 c1 c3 s^3 P^2 Q^3 S) ds, where
  N_v = u1 (u3d u4' - u4d u3') - u3 (u1d u4' - u4d u1') + u4 (u1d u3' - u3d u1').
Checks at kappa0 = (4 - 3i)/10:
  (1) Krawczyk: a unique zero x* of E(., kappa0) in a box X of radius 1e-95, with J_x invertible;
  (2) on X: c0, c1, c3, p0, q0, r0 and Res(P,Q), Res(P,S), Res(Q,S) are nonzero  [condition (B1)];
  (3) with v = (xdot, kappadot = 1), xdot = -J_x^{-1} dE/dkappa, the sum of the residues of eta_v
      over C is enclosed in a ball not containing 0.  The poles of eta_v in C are at s = 0 and at the
      roots of Q (the zeros of P and S are regular points), all zeros of u0, so this sum is I_02.
      It equals [w^1] f(1/w) for eta_v = f(s) ds, computed by exact series division.
The working precision is 1000 bits; FAMILY44_PREC overrides it.
"""
import json
import os
import sys
from fractions import Fraction
from flint import acb, arb, acb_poly, acb_mat, ctx

ctx.prec = int(os.environ.get("FAMILY44_PREC", "1000"))
N = 12
S_ = acb_poly([0, 1])


def P_(cs):
    return acb_poly(list(cs))


def parts(x, kappa):
    P = P_(list(x[0:5]) + [acb(1)])
    Q = P_(list(x[5:8]) + [acb(1)])
    S = P_([kappa, x[8], acb(1)])
    return P, Q, S, x[9], x[10], x[11]


def coeffs(p, n):
    cs = p.coeffs()
    return [cs[i] if i < len(cs) else acb(0) for i in range(n)]


def total(x, kappa):
    P, Q, S, c0, c1, c3 = parts(x, kappa)
    return c0 * S_ ** 3 * P * Q + c1 * P * Q ** 2 + 1 + c3 * Q * S ** 4 + S_ * P ** 2


def E(x, kappa):
    return coeffs(total(x, kappa), N)


def jac(x, kappa):
    """12 x 13 Jacobian; the last column is d/dkappa."""
    P, Q, S, c0, c1, c3 = parts(x, kappa)
    dP = c0 * S_ ** 3 * Q + c1 * Q ** 2 + 2 * S_ * P
    dQ = c0 * S_ ** 3 * P + 2 * c1 * P * Q + c3 * S ** 4
    dS = 4 * c3 * Q * S ** 3
    cols = [S_ ** i * dP for i in range(5)] + [S_ ** i * dQ for i in range(3)]
    cols += [S_ * dS, S_ ** 3 * P * Q, P * Q ** 2, Q * S ** 4, dS]
    J = acb_mat(N, N + 1)
    for k, col in enumerate(cols):
        cs = coeffs(col, N)
        for i in range(N):
            J[i, k] = cs[i]
    return J


def sub(J, ncols):
    M = acb_mat(N, ncols)
    for i in range(N):
        for k in range(ncols):
            M[i, k] = J[i, k]
    return M


def sylvester(p, q):
    p = p.coeffs(); q = q.coeffs(); m, n = len(p) - 1, len(q) - 1
    M = acb_mat(m + n, m + n)
    for i in range(n):
        for j, c in enumerate(reversed(p)):
            M[i, i + j] = c
    for i in range(m):
        for j, c in enumerate(reversed(q)):
            M[n + i, i + j] = c
    return M.det()


def series_div(a, b, n):
    """First n coefficients of the power series a/b, b[0] != 0 (lists of acb)."""
    a = a + [acb(0)] * max(0, n - len(a)); b = b + [acb(0)] * max(0, n - len(b))
    out = []
    inv = 1 / b[0]
    for k in range(n):
        t = a[k] - sum((b[j] * out[k - j] for j in range(1, k + 1)), acb(0))
        out.append(t * inv)
    return out


def residue_sum(x, kappa):
    J = jac(x, kappa)
    xd = sub(J, N).solve(acb_mat([[-J[i, N]] for i in range(N)]))
    xd = [xd[k, 0] for k in range(N)]
    P, Q, S, c0, c1, c3 = parts(x, kappa)
    Pd = P_(xd[0:5]); Qd = P_(xd[5:8]); Sd = P_([acb(1), xd[8]])
    c0d, c1d, c3d = xd[9], xd[10], xd[11]
    u1 = c1 * P * Q ** 2; u3 = c3 * Q * S ** 4; u4 = S_ * P ** 2
    u1d = c1d * P * Q ** 2 + c1 * (Pd * Q ** 2 + 2 * P * Q * Qd)
    u3d = c3d * Q * S ** 4 + c3 * (Qd * S ** 4 + 4 * Q * S ** 3 * Sd)
    u4d = 2 * S_ * P * Pd
    d1, d3, d4 = u1.derivative(), u3.derivative(), u4.derivative()
    Nv = u1 * (u3d * d4 - u4d * d3) - u3 * (u1d * d4 - u4d * d1) + u4 * (u1d * d3 - u3d * d1)
    den = c0 * c1 * c3 * S_ ** 3 * P ** 2 * Q ** 3 * S          # degree 24, leading coefficient c0 c1 c3
    nN, nD = 32, 24
    revN = list(reversed(coeffs(Nv, nN + 1)))
    revD = list(reversed(coeffs(den, nD + 1)))
    # f(1/w) = w^(nD - nN) revN(w)/revD(w); I = [w^1] f(1/w) = [w^(1 + nN - nD)] revN/revD
    k = 1 + nN - nD
    ser = series_div(revN, revD, k + 1)
    return ser[k], xd, Nv, den


def load_point(path):
    d = json.load(open(path))
    kr, ki = (Fraction(t) for t in d["kappa0"])
    kappa = acb(arb(kr.numerator) / kr.denominator, arb(ki.numerator) / ki.denominator)
    xt = [acb(arb(re), arb(im)) for re, im in d["x"]]
    return kappa, xt


def main(path):
    kappa, xt = load_point(path)
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
            if not (kk.lower() > xx.lower() and kk.upper() < xx.upper()):
                inside = False
    rad = max(max(float(Kx[k, 0].real.rad()), float(Kx[k, 0].imag.rad())) for k in range(N))
    print("(1) Krawczyk K(X) inside X:", inside, "  max radius of K(X): %.2e (box radius 1e-95)" % rad)
    assert inside
    P, Q, S, c0, c1, c3 = parts(X, kappa)
    vals = {"c0": c0, "c1": c1, "c3": c3, "p0": P.coeffs()[0], "q0": Q.coeffs()[0], "r0": kappa,
            "Res(P,Q)": sylvester(P, Q), "Res(P,S)": sylvester(P, S), "Res(Q,S)": sylvester(Q, S)}
    for name, v in vals.items():
        ok = not v.contains(0)
        print("(2) %-9s nonzero: %s   |.| >= %s" % (name, ok, abs(v).lower().str(5) if ok else "?"))
        assert ok
    I, xd, Nv, den = residue_sum(X, kappa)
    # sanity: N_v is divisible by P^2 S (those zeros are regular points of eta_v)
    rem = divmod(Nv, P ** 2 * S)[1]
    print("    max |coefficient| of N_v mod P^2 S: %.2e" % max(float(abs(c).upper()) for c in rem.coeffs()) if rem.coeffs() else "    N_v mod P^2 S = 0")
    print("(3) I_02 =", I.str(15, radius=False), "  radius of the enclosure: %.1e"
          % max(float(I.real.rad()), float(I.imag.rad())))
    print("    0 in I_02:", I.contains(0), "   |I_02| >=", abs(I).lower().str(8))
    assert not I.contains(0)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "family44_point.json"))
