"""a1_secant.py -- the F-secant space S_F(q) on X and the Hochschild profile
theorem (analogue of prop:secantprofile for a quartic CM field F = F0(sqrt(-q))).

Checks, exactly:
 (1) S_F(q) = span of the four pure spinors exp(sum_j eps_j s_j theta_j), s_j^2 = -tau_j(q),
     equals the rational span of u, v_f (f in F0), w = theta_1 theta_2 (V-matrix form).
 (2) profile(v) = (1, 8, 2 rho + 4 N, 8, 1, 0, ...) where rho = rank V, N = #nonzero w_eps.
 (3) chi(v) = int v^vee v = 4 [ N(q) a^2 + c^2 + Tr(f^2 qbar) ] for v = a u + v_f + c w.
"""
import sys, random, time
from a1model import *

t0 = time.time()
M = RMModel()
S = M.disc


def Vmat_of(a, f, c, q):
    """V-matrix of a u + v_f + c w (entries QS)."""
    q1, q2 = M.tau(q)
    f1, f2 = M.tau(f)
    c1 = [QS(1, 0, S), QS(0, 0, S), -q1]
    c2 = [QS(1, 0, S), QS(0, 0, S), -q2]
    e = [QS(0, 0, S), QS(1, 0, S), QS(0, 0, S)]
    V = [[QS(0, 0, S)] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            V[i][j] = Fr(a) * c1[i] * c2[j] + f1 * e[i] * c2[j] + f2 * c1[i] * e[j] + Fr(c) * e[i] * e[j]
    return V


def rational(u):
    """QS-coefficient class -> rational class (asserts rationality)."""
    out = {}
    for k, c in u.items():
        assert c.b == 0, "not rational"
        if c.a != 0:
            out[k] = c.a
    return out


def rankV(V):
    # rank over Q(sqrt S) via realification of a 3x3 matrix with QS entries: use flint over Q
    # rank_{Q(s)} = rank_Q of the 6x6 matrix [[a, t b],[b, a]]
    Mq = flint.fmpq_mat(6, 6)
    for i in range(3):
        for j in range(3):
            c = V[i][j]
            Mq[i, j] = flint.fmpq(c.a.numerator, c.a.denominator)
            tb = c.b * S
            Mq[i, 3 + j] = flint.fmpq(tb.numerator, tb.denominator)
            Mq[3 + i, j] = flint.fmpq(c.b.numerator, c.b.denominator)
            Mq[3 + i, 3 + j] = flint.fmpq(c.a.numerator, c.a.denominator)
    r = Mq.rank()
    assert r % 2 == 0
    return r // 2


if __name__ == "__main__":
    print("A1 secant profile.  F0 = Q(sqrt %d), R = %s" % (S, M.Rm))
    random.seed(12)
    # q values: totally positive elements c0 + c1 R of F0
    qs = [(1, 1), (2, 1), (3, -1), (1, 0), (5, 2)]
    for q in qs:
        q1, q2 = M.tau(q)
        assert q1.val() > 0 and q2.val() > 0
    shapes = [("w=theta1theta2", 0, (0, 0), 1), ("u", 1, (0, 0), 0), ("v_1", 0, (1, 0), 0),
              ("v_R", 0, (0, 1), 0), ("u+v_1+w (rank2)", 1, (1, 0), 1)]
    for q in qs:
        Nq = M.QSel(q).norm()
        for name, a, f, c in shapes:
            V = Vmat_of(a, f, c, q)
            v = rational(M.from_V(V))
            rho = rankV(V)
            prof = M.profile(v, 8)
            # N_w: number of nonzero w_eps; rational v with F non-biquadratic has all 4 nonzero
            # (Galois-transitive on CM types).  For biquadratic F (q rational), compute:
            # W = P1^{-1} V P2^{-T} is not available over Q(sqrt S); use the formula
            # r2 = 2 rho + 4 Nw to *predict* Nw only for the check below when q irrational.
            f1, f2 = M.tau(f)
            chi_formula = 4 * (Nq * Fr(a) ** 2 + Fr(c) ** 2 + (f1 * f1 * M.tau(q)[1] + f2 * f2 * M.tau(q)[0]).a)
            chi_exact = M.chi(v)
            biq2 = (q in [(1, 0), (1, 1)])  # q in Q^x (F0^x)^2: F biquadratic (q = 1, q = phi^2)
            if not biq2:
                expect = [1, 8, 2 * rho + 16, 8, 1, 0, 0, 0, 0]
                check("q=%s %s: rho=%d profile %s == (1,8,%d,8,1)" % (q, name, rho, prof, 2 * rho + 16),
                      prof == expect)
            else:
                print("  [info] biquadratic q=%s %s: rho=%d profile %s" % (q, name, rho, prof))
            check("q=%s %s: chi exact %s == formula %s" % (q, name, chi_exact, chi_formula),
                  chi_exact == chi_formula)
    # random rational elements of S_F(q)
    for trial in range(6):
        q = qs[trial % 3]
        a = random.randint(-3, 3); c = random.randint(-3, 3)
        f = (random.randint(-3, 3), random.randint(-3, 3))
        V = Vmat_of(a, f, c, q)
        if all(x == 0 for row in V for x in row):
            continue
        v = rational(M.from_V(V))
        rho = rankV(V)
        prof = M.profile(v, 8)
        check("random q=%s a=%d f=%s c=%d: rho=%d, profile %s" % (q, a, f, c, rho, prof),
              prof == [1, 8, 2 * rho + 16, 8, 1, 0, 0, 0, 0])
    # K-type check (biquadratic, q = 1): v in P_theta(1) has profile (1,8,12,8,1)
    # P_theta(1) = span(e^{i theta} + e^{-i theta}, (e^{i theta}-e^{-i theta})/i)
    th = M.theta
    uth = add(one(), sc(Fr(-1, 2), power(th, 2)), sc(Fr(1, 24), power(th, 4)))
    vth = add(th, sc(Fr(-1, 6), power(th, 3)))
    for (a, b) in [(1, 0), (0, 1), (1, 3)]:
        v = add(sc(Fr(a), uth), sc(Fr(b), vth))
        prof = M.profile(v, 8)
        check("K-secant (d=1) a=%d b=%d: profile %s == (1,8,12,8,1)" % (a, b, prof),
              prof == [1, 8, 12, 8, 1, 0, 0, 0, 0])
    print("time %.1fs" % (time.time() - t0))
    summary()
