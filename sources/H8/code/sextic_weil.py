#!/usr/bin/env python3
"""
sextic_weil.py

Item (LVIII) of the computations: the F-Weil part of the twisted character of
an Orlov product over a sextic CM field F = F_0(sqrt(-q)), and the integral
flat secant characters for which it is nonzero (lem:sexticweil,
prop:sexticweilmin, rem:sextictargets).

Setting.  X a principally polarised abelian sixfold with real multiplication
by O = O_{F_0}, F_0 totally real cubic with real places tau_1, tau_2, tau_3,
q in F_0 totally positive, d_j = tau_j(q), s_j = sqrt(-1) sqrt(d_j);
A = X x Xhat with the action of F of prop:sexticcount(iii),(iv) (B-field 0);
kappa(v_1, v_2) = ch Phi(F_1 [x] F_2^vee) e^{ell/2} for ch F_i = v_i in
S(0,q), v_i = sum_eps w^i_eps e_eps.  tau_(j,sigma) is the embedding of F
over tau_j with tau_(j,sigma)(sqrt(-q)) = sigma s_j, and
    omega_(j,sigma) = -(gamma_j - sigma s_j ell_j)^2 / (2 d_j^2)
is the generator of eq:splitclosed (n = 2, d = d_j) of wedge^4 V_(j,sigma).
W_(j,sigma) is the coefficient of omega_(j,sigma) in the degree-four part of
kappa (the F-Weil part; the rest is a polynomial in the eta_j).

What is checked:

  (a) the model and the pair formula.  The eigenvectors of sqrt(-q) and
      omega_(j,sigma) = wedge_i (x_i + sigma (s_j/d_j) B x_i) = the closed
      form of eq:splitclosed; on one factor (n = 2) the constants of
      prop:flatall, Psi(e^{s theta} [x] e^{s theta}) = -4d e^{(s/2d) eta}
      (eta = d theta + thetahat) and
      Psi(e^{s theta} [x] e^{-s theta}) = (1/2)(gamma - s ell)^2, for
      d = 1, 4, 1/4 and both signs; and on the twelvefold, with the
      repository's orlov.py (attack/gaps/quartic_obstruction), for three
      models d = (1,1,1), (1,4,9), (4,1/4,9/4) (every d_j a rational square,
      so that everything is exact over Q(sqrt(-1)); the identities are
      formal in the d_j) and three pairs each, one of them diagonal: the
      degree-four part of kappa lies in the span of the six eta_j eta_k and
      the six omega_(j,sigma), and
          W_(j,sigma) = -16 Nm(q) d_j sum_{eps_j = sigma} w^1_eps w^2_{eps^(j)},
      eps^(j) agreeing with eps exactly at j (lem:sexticweil(i)); the
      degree-pruned transform used below agrees with orlov.py;

  (b) the secant plane of Q(sqrt(-1)): for q = 1 and ch F_i = a_i Re +
      b_i Im of e^{sqrt(-1) theta}, kappa in degrees <= 4 is
      -32(a1a2+b1b2) + 16(a1b2-a2b1) eta + 4(a1a2+b1b2) eta^2 (six pairs), so
      it has no F-Weil part; classes supported on one pair {eps_0, -eps_0}
      give no F-Weil part (d = (1,4,9)); the mixed pair (Re e^{sqrt(-1) theta},
      v(-5,0,-2,0)) has rank ch E = -8 and all six W equal to 7, the diagonal
      v(-5,0,-2,0) has rank -296 and all W equal to -21;

  (c) the closed form: sum_{eps_j = sigma} w_eps w_{eps^(j)} =
      (1/16) sum_b (C_0b + sigma C_1b/s_j)^2 / prod_{k in b} d_k (random
      classes, three models); symbolically (sympy), this equals
      R + 2 I / tau_(j,sigma)(sqrt(-q)) with R, I given by the trace formulas
      of lem:sexticweil(ii), at each of the three places; the implementation
      of R and I in F_0 against the conjugate formulas modulo a prime that
      splits F_0, for the sixteen fields and three values of q; and exactly
      over Q(alpha) on the twelvefold, for Q(zeta_7)^+ and Q(zeta_9)^+ (whose
      real places are automorphisms): the degree-four part of kappa(v, v) is
      eta-part + sum_j (-2 Nm(q) d_j tau_j(R)) P_j + (-4 Nm(q) d_j tau_j(I)) Q_j,
      omega_(j,sigma) = P_j + sigma s_j Q_j, for five classes (two with
      I != 0, one with Omega = 0); Omega(v_*) = (18 - 4a - 6a^2)/13 and
      Omega(v(1,0,-a,0)) = (6a + 6a^2)/17;

  (d) for Q(zeta_7)^+ and Q(zeta_9)^+, 2 + a = beta^2 with the units
      beta = -1 + a + a^2 (norm -1) and -2 + a + a^2 (norm 1); the classes
      with -chi = 32 of S(0, 2+a) are exactly +-Re and +-Im of
      e^{sqrt(-1) theta_beta}, with Omega = 0;

  (e) lattice scans (all 48 cases: the sixteen cubic fields of item (LVII),
      q in {1, k+a, k+1+a}; lattices as in item (LVII), enumeration after
      LLL by exact Fincke-Pohst, bound doubled until a class with
      Omega != 0 appears): the least -chi of an integral class with
      Omega != 0 is 192, attained only by +-v_* = +-v(-1,0,2-a^2,0) over
      Q(zeta_7)^+ with q = 3+a, of shape N_w = 8, (54,112); over Q(zeta_9)^+
      with q = 3+a the least value and the lattice minimum are 256, attained
      only by +-v(1,0,-a,0); for q = 1 over Q(zeta_7)^+ (Q(zeta_9)^+) every
      class with -chi < 296 (< 488) lies in Z Re + Z Im, and the least value
      296 (488) is attained by 8 classes up to sign, among them
      v(-5,0,-2,0) (v(-7,0,-2,0)), all of shape (54,112); the same least
      values for q = 2+a; for each of the 48 cases the least value lies
      between 192 and 7080, and for q = 1 between 296 and 3872;

  (f) F = F_0(sqrt(-q)) contains an imaginary quadratic field exactly in 20
      of the 48 cases: q = 1 (Q(sqrt(-1))), q = 2+a over Q(zeta_7)^+ and
      Q(zeta_9)^+ (Q(sqrt(-1))), q = 2+a over the field of discriminant 321
      and q = 4+a over that of discriminant 1509 (Q(sqrt(-3))); in these
      two cases the lattice minimum of -chi is 288 and 4608, attained with
      Omega = 0, and the least -chi with Omega != 0 is 728 and 6504.

Everything is exact (rational arithmetic, Q(sqrt(-1)), Q(alpha), and
arithmetic modulo primes in (c) and in the shapes of (e), where ranks modulo
a prime bound ranks below and (54,112) is the maximum).  Uses python-flint
(LLL, via attack/gaps/sextic/s3_weil.py) and sympy (in (c) and (f)).

Run:  python3 sextic_weil.py
"""
import os
import sys
import random
import itertools
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "attack", "gaps", "sextic"))
import s3_weil as W                                           # noqa: E402
from s3_weil import QI, QA, QL                                # noqa: E402
from ealib import add, sc, wedge, clean, pc, one, expo        # noqa: E402
import orlov as ORL                                           # noqa: E402
import s2_lattice as S                                        # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("         " + detail)


def qi_sqrt(d):
    """sqrt(d) for a rational square d"""
    d = Fr(d)
    a, b = d.numerator, d.denominator
    ra, rb = int(round(a ** 0.5)), int(round(b ** 0.5))
    assert ra * ra == a and rb * rb == b
    return Fr(ra, rb)


MODELS = [[Fr(1)] * 3, [Fr(1), Fr(4), Fr(9)], [Fr(4), Fr(1, 4), Fr(9, 4)]]


def svec_of(dvec):
    return [QI(0, qi_sqrt(d)) for d in dvec]


def toQI(u):
    return {m: (c if isinstance(c, QI) else QI(c)) for m, c in u.items()}


# ------------------------------------------------------------------ (a)
def part_a():
    # a1: eigenvectors and the closed form of omega
    ok_eig, ok_closed = True, True
    for dvec in MODELS:
        svec = svec_of(dvec)
        for j in range(3):
            d = dvec[j]
            for sg in (1, -1):
                lam = QI(sg) * svec[j]
                for i in W.FACT[j]:
                    k, s = W.Bx(i)
                    # M x_i = -B x_i = -s xi_k ; M xi_k = d B^{-1} xi_k = d s x_i
                    c = lam / QI(d) * QI(s)          # coefficient of xi_k
                    Mv = {1 << (12 + k): QI(-s), 1 << i: c * QI(d * s)}
                    lv = {1 << i: lam, 1 << (12 + k): lam * c}
                    ok_eig = ok_eig and clean(add(Mv, sc(QI(-1), lv))) == {}
                wv = W.omega_wedge(j, lam / QI(d), QI(1))
                cl = W.omega_closed(j, d, lam, QI(1))
                ok_closed = ok_closed and clean(add(wv, sc(QI(-1), cl))) == {}
    check("x_i + sigma (s_j/d_j) B x_i is an eigenvector of sqrt(-q) with "
          "eigenvalue sigma s_j, and wedge_i (x_i + sigma (s_j/d_j) B x_i) = "
          "-(gamma_j - sigma s_j ell_j)^2/(2 d_j^2), the generator of "
          "eq:splitclosed at n = 2 (18 cases)", ok_eig and ok_closed)

    # a2: the constants of prop:flatall at n = 2 (one factor, orlov.py g = 2)
    th = {(1 << 0) | (1 << 2): Fr(1), (1 << 1) | (1 << 3): Fr(1)}
    thh = {(1 << 4) | (1 << 6): Fr(1), (1 << 5) | (1 << 7): Fr(1)}
    L = add(*[{(1 << i) | (1 << (4 + i)): Fr(1)} for i in range(4)])
    E2 = toQI(expo(sc(Fr(1, 2), L)))
    ok = True
    for d in (Fr(1), Fr(4), Fr(1, 4)):
        s = QI(0, qi_sqrt(d))
        eta = add(sc(d, th), thh)
        gam = add(sc(d, th), sc(Fr(-1), thh))
        for sg in (1, -1):
            ep = toQI(expo(sc(QI(sg) * s, toQI(th))))
            em = toQI(expo(sc(QI(-sg) * s, toQI(th))))
            psi_pp = wedge(toQI(ORL.orlov(2, ep, ep)), E2)
            psi_pm = wedge(toQI(ORL.orlov(2, ep, em)), E2)
            want_pp = sc(QI(-4 * d), toQI(expo(sc(QI(sg) * s / QI(2 * d),
                                                   toQI(eta)))))
            t = add(toQI(gam), sc(QI(-sg) * s, toQI(L)))
            want_pm = sc(QI(Fr(1, 2)), wedge(t, t))
            ok = ok and clean(add(psi_pp, sc(QI(-1), want_pp))) == {} \
                and clean(add(psi_pm, sc(QI(-1), want_pm))) == {}
    check("on one factor (n = 2): Psi(e^{sigma s theta} [x] e^{sigma s theta}) "
          "= -4d exp(sigma (s/2d) eta), eta = d theta + thetahat, and "
          "Psi(e^{sigma s theta} [x] e^{-sigma s theta}) = "
          "(1/2)(gamma - sigma s ell)^2, for d = 1, 4, 1/4 and sigma = +-1",
          ok)

    # a3, a4: the pair formula on the twelvefold against orlov.py
    rng = random.Random(58)
    ok_span, ok_pair, ok_low, n = True, True, True, 0
    for dvec in MODELS:
        svec = svec_of(dvec)
        for trial in range(3):
            C1 = {a: Fr(rng.randint(-3, 3)) for a in W.SUBSETS}
            C2 = C1 if trial == 0 else \
                {a: Fr(rng.randint(-3, 3)) for a in W.SUBSETS}
            v1, v2 = W.secant_class(C1, dvec), W.secant_class(C2, dvec)
            kf = W.kappa_low(v1, v2, 4, full=True)
            kl = W.kappa_low(v1, v2, 4, full=False)
            ok_low = ok_low and clean(add(kf, sc(-1, kl))) == {}
            res = W.weil_coordinates_QI(W.degree(kf, 4), dvec, svec)
            if res is None:
                ok_span = False
                continue
            ok_pair = ok_pair and res[1] == W.pair_W(C1, C2, dvec, svec)
            n += 1
    check("the transform pruned by output degree agrees with orlov.py in "
          "degrees <= 4 on the nine pairs below", ok_low)
    check("pair formula of lem:sexticweil(i): for d = (1,1,1), (1,4,9), "
          "(4,1/4,9/4) and three pairs each (one diagonal), kappa_4 lies in "
          "the span of the eta_j eta_k and omega_(j,sigma), and W_(j,sigma) = "
          "-16 Nm(q) d_j sum_{eps_j = sigma} w1_eps w2_{eps^(j)}",
          ok_span and ok_pair and n == 9, "%d pairs" % n)


# ------------------------------------------------------------------ (b)
RE = W.C_of(Fr(1), [0, 0, 0], [Fr(-1)] * 3, Fr(0))
IM = W.C_of(Fr(0), [Fr(1)] * 3, [0, 0, 0], Fr(-1))


def part_b():
    d1 = [Fr(1)] * 3
    s1 = svec_of(d1)
    eta = add(*[W.eta_j(j, Fr(1)) for j in range(3)])
    ok = True
    for (a1, b1, a2, b2) in ((1, 0, 1, 0), (1, 0, 0, 1), (0, 1, 1, 0),
                             (0, 1, 0, 1), (2, -1, 3, 5), (1, 1, -1, 2)):
        C1 = {a: a1 * RE[a] + b1 * IM[a] for a in W.SUBSETS}
        C2 = {a: a2 * RE[a] + b2 * IM[a] for a in W.SUBSETS}
        k = W.kappa_low(W.secant_class(C1, d1), W.secant_class(C2, d1), 4)
        P, Q = a1 * a2 + b1 * b2, a1 * b2 - a2 * b1
        want = add({0: Fr(-32 * P)}, sc(Fr(16 * Q), eta),
                   sc(Fr(4 * P), wedge(eta, eta)))
        ok = ok and clean(add(k, sc(-1, want))) == {}
        ok = ok and all(x == 0 for x in W.pair_W(C1, C2, d1, s1))
    check("q = 1, ch F_i = a_i Re + b_i Im of e^{sqrt(-1) theta}: kappa in "
          "degrees <= 4 is -32(a1a2+b1b2) + 16(a1b2-a2b1) eta + "
          "4(a1a2+b1b2) eta^2, eta = beta + betahat, so no F-Weil part "
          "(six pairs)", ok)

    # classes supported on one pair {eps0, -eps0}, d = (1,4,9)
    dv = MODELS[1]
    sv = svec_of(dv)
    e0 = (1, -1, 1)

    def pair_class(w):
        C = {}
        for a in W.SUBSETS:
            z = QI(1)
            for j in range(3):
                if a[j]:
                    z = z * QI(e0[j]) * sv[j]
            c = w * z
            C[a] = 2 * c.a                  # w e_eps0 + conj(w) e_{-eps0}
        return C
    Ca, Cb = pair_class(QI(1, 2)), pair_class(QI(3, -1))
    wa = W.w_of(Ca, sv)
    supp_ok = all((wa[e] != 0) == (e in (e0, tuple(-t for t in e0)))
                  for e in W.EPS)
    k = W.kappa_low(W.secant_class(Ca, dv), W.secant_class(Cb, dv), 4)
    res = W.weil_coordinates_QI(W.degree(k, 4), dv, sv)
    check("classes supported on one pair {eps_0, -eps_0} (d = (1,4,9), "
          "eps_0 = (1,-1,1)): the Orlov product has zero F-Weil part",
          supp_ok and res is not None and all(x == 0 for x in res[1])
          and all(x == 0 for x in W.pair_W(Ca, Cb, dv, sv)))

    # the mixed pair (Re, v(-5,0,-2,0)) and the diagonal v(-5,0,-2,0)
    V5 = W.C_of(Fr(-5), [0, 0, 0], [Fr(-2)] * 3, Fr(0))
    vr, v5 = W.secant_class(RE, d1), W.secant_class(V5, d1)
    chi5 = W.integral_X(wedge(W.dual(v5), v5))
    out = []
    for (A_, B_, CA, CB) in ((vr, v5, RE, V5), (v5, v5, V5, V5)):
        k = W.kappa_low(A_, B_, 4, full=True)
        res = W.weil_coordinates_QI(W.degree(k, 4), d1, s1)
        out.append((k.get(0, 0), res[1] if res else None,
                    W.pair_W(CA, CB, d1, s1)))
    ok = (chi5 == -296 and out[0][0] == -8 and out[1][0] == -296
          and out[0][1] == [QI(7)] * 6 and out[1][1] == [QI(-21)] * 6
          and out[0][2] == out[0][1] and out[1][2] == out[1][1])
    check("q = 1: chi(v(-5,0,-2,0)) = -296; the pair (Re e^{sqrt(-1) theta}, "
          "v(-5,0,-2,0)) has rank ch E = -8 and W_(j,sigma) = 7 for all six "
          "(j,sigma); the diagonal v(-5,0,-2,0) has rank -296 and W = -21",
          ok, "ranks %s, %s; W %s, %s" % (out[0][0], out[1][0],
                                         qi_str(out[0][1][0]),
                                         qi_str(out[1][1][0])))


def qi_str(w):
    """a + b i as text (b = 0 printed as a rational number)."""
    if w.b == 0:
        return str(w.a)
    return "%s%s%si" % (w.a, "+" if w.b > 0 else "-", abs(w.b))


# ------------------------------------------------------------------ (c)
def conj_RI(qj, fj, gj, c0, c3, j):
    """the conjugate form at place j: tau_j(Nm(q) R), tau_j((Nm(q)/q) I)"""
    k, l = [t for t in range(3) if t != j]
    N = qj[0] * qj[1] * qj[2]
    NR = (N * c0 * c0 - qj[k] * qj[l] * fj[j] ** 2
          + qj[j] * (qj[k] * fj[l] ** 2 + qj[l] * fj[k] ** 2)
          + qj[j] * gj[j] ** 2 - qj[k] * gj[k] ** 2 - qj[l] * gj[l] ** 2
          - c3 * c3)
    NI = (qj[k] * qj[l] * c0 * fj[j] + qj[l] * fj[k] * gj[l]
          + qj[k] * fj[l] * gj[k] + c3 * gj[j])
    return NR, NI


def part_c():
    import sympy
    # c1: the diagonal form of the pair sum
    rng = random.Random(581)
    ok = True
    for dvec in MODELS:
        sv = svec_of(dvec)
        for _ in range(2):
            C = {a: Fr(rng.randint(-5, 5)) for a in W.SUBSETS}
            pw = W.pair_W(C, C, dvec, sv)
            df = W.diag_form(C, dvec, sv)
            Nm = dvec[0] * dvec[1] * dvec[2]
            ok = ok and all(p == QI(-16 * Nm * dvec[j // 2]) * x
                            for j, (p, x) in enumerate(zip(pw, df)))
    check("sum_{eps_j = sigma} w_eps w_{eps^(j)} = (1/16) sum_b (C_0b + "
          "sigma C_1b/s_j)^2 / prod_{k in b} d_k (three models, two random "
          "classes each)", ok)

    # c2: symbolic identity with the trace formulas, at each place
    q = sympy.symbols("q1:4", positive=True)
    f = sympy.symbols("f1:4")
    g = sympy.symbols("g1:4")
    c0, c3, u = sympy.symbols("c0 c3 u")
    ok = True
    for j in range(3):
        k, l = [t for t in range(3) if t != j]
        Y = ((c0 + u * f[j]) ** 2 + (f[k] + u * g[l]) ** 2 / q[k]
             + (f[l] + u * g[k]) ** 2 / q[l]
             + (g[j] + u * c3) ** 2 / (q[k] * q[l]))
        N = q[0] * q[1] * q[2]
        tr = lambda x: x[0] + x[1] + x[2]                       # noqa: E731
        prod = lambda x, y: [x[t] * y[t] for t in range(3)]     # noqa: E731

        def star(x, y):
            xy = prod(x, y)
            return (tr(x) - x[j]) * (tr(y) - y[j]) - (tr(xy) - xy[j])
        f2 = prod(f, f)
        qg = prod(q, g)
        qg2 = prod(q, prod(g, g))
        NR = (N * c0 ** 2 - q[k] * q[l] * f2[j] + q[j] * star(q, f2)
              + 2 * qg2[j] - tr(qg2) - c3 ** 2)
        NI = q[k] * q[l] * c0 * f[j] + star(f, qg) + c3 * g[j]
        R = NR / N
        I = NI / (q[k] * q[l])
        diff = sympy.Poly(sympy.expand((Y - R - 2 * I * u) * N), u)
        a0, a1, a2 = (diff.coeff_monomial(u ** e) for e in range(3))
        # reduce modulo u^2 = -1/tau_j(q)
        ok = ok and diff.degree() <= 2 and \
            sympy.expand(a0 * q[j] - a2) == 0 and sympy.expand(a1) == 0
        cNR, cNI = conj_RI(q, f, g, c0, c3, j)
        ok = ok and sympy.expand(NR - cNR) == 0 and sympy.expand(NI - cNI) == 0
    check("symbolically, at each place j: sum_b (C_0b + u C_1b)^2 / prod "
          "d_k = R + 2 I u modulo u^2 + 1/tau_j(q), with R, I given by the "
          "trace formulas of lem:sexticweil(ii) (equal to the conjugate "
          "formulas)", ok)

    # c3: the implementation in F_0 against the conjugate formulas mod p
    ok, cases = True, 0
    for name, poly in W.cubic_fields():
        qs, k = W.q_values(poly)
        p = S.big_primes(poly, 1, 10 ** 9)[0]
        rts = S.roots_mod(poly, p)

        def ev(x, r):
            s = 0
            for e, c in enumerate(x):
                c = Fr(c)
                s = (s + c.numerator * pow(c.denominator, p - 2, p)
                     * pow(r, e, p)) % p
            return s
        for qvec in qs:
            for _ in range(2):
                x = [Fr(rng.randint(-4, 4), rng.randint(1, 3))
                     for _ in range(8)]
                NR, NI, Nq = W.omega_RI(poly, qvec, x)
                qj = [ev(qvec, r) for r in rts]
                fj = [ev(x[1:4], r) for r in rts]
                gj = [ev(x[4:7], r) for r in rts]
                c0m, c3m = ev([x[0]], 0), ev([x[7]], 0)
                for j in range(3):
                    cr, ci = conj_RI(qj, fj, gj, c0m, c3m, j)
                    ok = ok and (cr - ev(NR, rts[j])) % p == 0 \
                        and (ci - ev(NI, rts[j])) % p == 0
                ok = ok and (Nq - qj[0] * qj[1] * qj[2]) % p == 0
            cases += 1
    check("the F_0-implementation of R and I agrees with the conjugate "
          "formulas modulo a prime that splits F_0 (16 fields, 3 values of "
          "q, two random classes each)", ok, "%d cases" % cases)

    # c4: twelvefold over Q(alpha) for the cyclic fields
    Z7, Z9 = [1, 1, -2, -1], [1, 0, -3, 1]
    cases = [("Q(zeta_7)^+", Z7, [3, 1, 0], [-1, 0, 0, 0, 2, 0, -1, 0]),
             ("Q(zeta_7)^+", Z7, [3, 1, 0], [1, 1, 1, 0, 2, -1, 0, -1]),
             ("Q(zeta_7)^+", Z7, [2, 1, 0], [1, 0, 0, 0, -1, 0, 1, 0]),
             ("Q(zeta_9)^+", Z9, [3, 1, 0], [1, 0, 0, 0, 0, -1, 0, 0]),
             ("Q(zeta_9)^+", Z9, [3, 1, 0], [0, 2, 0, 1, 1, 1, -1, 3])]
    ok_all, ok_PQ, nIz, nzero = True, True, 0, 0
    for name, poly, qvec, x in cases:
        QA.P = poly
        q = QA(*qvec)
        dvec = [W.cyc_sigma(q, j) for j in range(3)]
        f, g = QA(*x[1:4]), QA(*x[4:7])
        C = W.C_of(QA(x[0]), [W.cyc_sigma(f, j) for j in range(3)],
                   [W.cyc_sigma(g, j) for j in range(3)], QA(x[7]))
        v = W.secant_class(C, dvec)
        k4 = W.degree(W.kappa_low(v, v, 4), 4)
        basis = [wedge(W.eta_j(j, dvec[j]), W.eta_j(kk, dvec[kk]))
                 for j in range(3) for kk in range(j, 3)]
        for j in range(3):
            P, Q = W.omega_PQ(j, dvec[j])
            Pc, Qc = W.omega_closed_PQ(j, dvec[j])
            ok_PQ = ok_PQ and clean(add(P, sc(-1, Pc))) == {} \
                and clean(add(Q, sc(-1, Qc))) == {}
            basis += [P, Q]
        sol = W.solve(basis, k4, QA(0))
        NR, NI, Nq = W.omega_RI(poly, qvec, x)
        R = QA(*NR) / Nq
        I = QA(*NI) * q / Nq
        want = []
        for j in range(3):
            want += [dvec[j] * W.cyc_sigma(R, j) * (-2 * Nq),
                     dvec[j] * W.cyc_sigma(I, j) * (-4 * Nq)]
        ok_all = ok_all and sol is not None and sol[6:] == want
        nIz += int(I != 0)
        nzero += int(R == 0 and I == 0)
    check("exactly over Q(alpha) on the twelvefold (Q(zeta_7)^+, "
          "Q(zeta_9)^+, q = 3+a and 2+a, five classes): kappa_4(v,v) = "
          "eta-part + sum_j -2 Nm(q) d_j tau_j(R) P_j - 4 Nm(q) d_j tau_j(I) "
          "Q_j, where omega_(j,sigma) = P_j + sigma s_j Q_j; so W_(j,sigma) = "
          "-Nm(q) d_j tau_(j,sigma)(Omega)", ok_all and ok_PQ and nIz == 2
          and nzero == 1, "%d classes with I != 0, %d with Omega = 0"
          % (nIz, nzero))

    # c5: Omega of the two minimal classes
    QA.P = Z7
    NR, NI, Nq = W.omega_RI(Z7, [3, 1, 0], [-1, 0, 0, 0, 2, 0, -1, 0])
    o7 = (QA(*NR) / Nq == QA(18, -4, -6) / 13 and not any(NI) and Nq == 13)
    QA.P = Z9
    NR, NI, Nq = W.omega_RI(Z9, [3, 1, 0], [1, 0, 0, 0, 0, -1, 0, 0])
    o9 = (QA(*NR) / Nq == QA(0, 6, 6) / 17 and not any(NI) and Nq == 17)
    check("Omega(v(-1,0,2-a^2,0)) = (18-4a-6a^2)/13 over Q(zeta_7)^+ and "
          "Omega(v(1,0,-a,0)) = (6a+6a^2)/17 over Q(zeta_9)^+, q = 3+a "
          "(I = 0 in both)", o7 and o9)


# ------------------------------------------------------------------ (d)
def part_d(scan):
    Z7, Z9 = [1, 1, -2, -1], [1, 0, -3, 1]
    ok = True
    for poly, beta, nb in ((Z7, (-1, 1, 1), -1), (Z9, (-2, 1, 1), 1)):
        QA.P = poly
        b = QA(*beta)
        ok = ok and b * b == QA(2, 1, 0) and b.norm() == nb
    check("2 + a = beta^2 with beta = -1+a+a^2 (norm -1) over Q(zeta_7)^+ and "
          "beta = -2+a+a^2 (norm 1) over Q(zeta_9)^+: units, so "
          "F_0(sqrt(-(2+a))) = F_0(sqrt(-1))", ok)
    ok = True
    for name, poly, beta in (("Q(zeta_7)^+", Z7, (-1, 1, 1)),
                             ("Q(zeta_9)^+", Z9, (-2, 1, 1))):
        QA.P = poly
        b = QA(*beta)
        nb = b.norm()
        g = b.inv() * (-nb)
        re = [Fr(1)] + [Fr(0)] * 3 + list(g.c) + [Fr(0)]
        im = [Fr(0)] + list(b.c) + [Fr(0)] * 3 + [-nb]
        want = sorted(tuple(s * t for t in cl) for cl in (re, im)
                      for s in (1, -1))
        below = scan[(name, (2, 1, 0))][2]
        got = sorted(tuple(c) for nv, c in below if nv <= 4)
        ok = ok and got == want and all(
            not W.omega_nonzero(poly, [2, 1, 0], c) for c in (re, im))
    check("the classes of S(0, 2+a) with -chi <= 32 are exactly +-Re and "
          "+-Im of e^{sqrt(-1) theta_beta} = v(1,0,-Nm(beta)/beta,0) + "
          "sqrt(-1) v(0,beta,0,-Nm(beta)), with Omega = 0 (both fields)", ok)


# ------------------------------------------------------------------ (e)
def run_scan():
    scan = {}
    for name, poly in W.cubic_fields():
        qs, k = W.q_values(poly)
        for qvec in qs:
            Lb, G = W.lattice(poly, qvec)
            m, at, below, mn = W.least_weil(poly, qvec, Lb, G)
            scan[(name, tuple(qvec))] = (m, at, below, mn, poly, k, Lb, G)
    return scan


def shape(poly, qvec, c):
    p = S.shape_prime(poly, list(qvec), 10 ** 6)
    Nw, A, rho, Ms, r2, r3 = S.shape_invariants(poly, list(qvec), c, p)
    return Nw, r2, r3


def part_e(scan):
    # e1: nothing with Omega != 0 below 192, and at 192 only +-v_*
    vstar = [Fr(-1), 0, 0, 0, Fr(2), 0, Fr(-1), 0]
    small = []
    for key, (m, at, below, mn, poly, k, Lb, G) in scan.items():
        if m <= 24:
            small += [(key, 8 * m, tuple(c)) for c in at]
    want = sorted([(("Q(zeta_7)^+", (3, 1, 0)), 192,
                    tuple(Fr(s) * t for t in vstar)) for s in (1, -1)])
    ok_min = sorted(small) == want and len(scan) == 48
    check("over the 48 lattices (16 fields, q in {1, k+a, k+1+a}) every "
          "integral class with Omega != 0 has -chi >= 192, with equality "
          "only for +-v(-1,0,2-a^2,0) over Q(zeta_7)^+, q = 3+a", ok_min,
          "%d cases" % len(scan))

    # e3: the two cyclic fields with q = 3 + a
    ok = True
    for name, want_m, cls in (("Q(zeta_7)^+", 24, vstar),
                              ("Q(zeta_9)^+", 32,
                               [Fr(1), 0, 0, 0, 0, Fr(-1), 0, 0])):
        m, at, below, mn, poly, k, Lb, G = scan[(name, (3, 1, 0))]
        ok = ok and m == want_m and mn == want_m and below == [] and \
            sorted(tuple(c) for c in at) == sorted(
                tuple(Fr(s) * t for t in cls) for s in (1, -1)) and \
            shape(poly, (3, 1, 0), cls) == (8, 54, 112)
    check("q = 3+a: over Q(zeta_7)^+ the lattice minimum is -chi = 192, "
          "attained only by +-v(-1,0,2-a^2,0); over Q(zeta_9)^+ it is 256, "
          "attained only by +-v(1,0,-a,0); both have N_w = 8, shape "
          "(54,112), so r(kappa) = 54 + 144 + 54 = 252 < 264", ok)

    # e2: q = 1 (and q = 2 + a) over the cyclic fields
    ok = True
    info = []
    for name, want_m, cls in (("Q(zeta_7)^+", 37,
                               [Fr(-5), 0, 0, 0, Fr(-2), 0, 0, 0]),
                              ("Q(zeta_9)^+", 61,
                               [Fr(-7), 0, 0, 0, Fr(-2), 0, 0, 0])):
        m, at, below, mn, poly, k, Lb, G = scan[(name, (1, 0, 0))]
        inplane = True
        for nv, c in below:
            a_, b_ = c[0], c[1]
            inplane = inplane and a_.denominator == 1 and \
                b_.denominator == 1 and \
                list(c) == [a_, b_, 0, 0, -a_, 0, 0, -b_]
        shapes = set(shape(poly, (1, 0, 0), c) for c in at)
        ok = ok and m == want_m and len(at) == 16 and inplane and \
            tuple(cls) in set(tuple(c) for c in at) and \
            shapes == {(8, 54, 112)} and \
            scan[(name, (2, 1, 0))][0] == want_m
        info.append("%s: %d classes below, %d at -chi = %d"
                    % (name, len(below), len(at), 8 * m))
    check("q = 1: over Q(zeta_7)^+ (Q(zeta_9)^+) every integral class with "
          "-chi < 296 (< 488) lies in Z Re + Z Im; the least -chi with "
          "Omega != 0 is 296 (488), attained by 8 classes up to sign, among "
          "them v(-5,0,-2,0) (v(-7,0,-2,0)), all of shape (54,112); the same "
          "least values for q = 2+a", ok, "; ".join(info))

    # e4: ranges
    allm = [8 * v[0] for v in scan.values()]
    q1 = [8 * v[0] for key, v in scan.items() if key[1] == (1, 0, 0)]
    ok = (min(allm), max(allm)) == (192, 7080) and \
        (min(q1), max(q1)) == (296, 3872) and \
        8 * scan[("disc 985", (4, 1, 0))][0] == 7080
    check("for each of the 48 cases the least -chi with Omega != 0 lies in "
          "[192, 7080] (7080 for discriminant 985, q = 4+a), and for q = 1 "
          "in [296, 3872]", ok, "q = 1 values %s" % sorted(set(q1)))


# ------------------------------------------------------------------ (f)
def part_f(scan):
    got = {}
    for name, poly in W.cubic_fields():
        qs, k = W.q_values(poly)
        for qvec in qs:
            D, Nm = W.imag_quadratic(poly, qvec)
            if D is not None:
                got[(name, tuple(qvec))] = D
    want = {(name, (1, 0, 0)): 1 for name, _ in W.cubic_fields()}
    want[("Q(zeta_7)^+", (2, 1, 0))] = 1
    want[("Q(zeta_9)^+", (2, 1, 0))] = 1
    want[("disc 321", (2, 1, 0))] = 3
    want[("disc 1509", (4, 1, 0))] = 3
    ks = {name: W.q_values(poly)[1] for name, poly in W.cubic_fields()}
    minima = [(8 * scan[key][3], 8 * scan[key][0])
              for key in (("disc 321", (2, 1, 0)), ("disc 1509", (4, 1, 0)))]
    check("F_0(sqrt(-q)) contains an imaginary quadratic field in exactly 20 "
          "of the 48 cases: q = 1 (Q(sqrt(-1))), q = 2+a over Q(zeta_7)^+ and "
          "Q(zeta_9)^+ (Q(sqrt(-1))), q = 2+a = k+a over discriminant 321 and "
          "q = 4+a = k+1+a over discriminant 1509 (Q(sqrt(-3))); in the last "
          "two the lattice minimum of -chi is 288 and 4608, attained with "
          "Omega = 0, and the least -chi with Omega != 0 is 728 and 6504",
          got == want and ks["disc 321"] == 2 and ks["disc 1509"] == 3
          and minima == [(288, 728), (4608, 6504)],
          "%d cases; (minimum, least with Omega != 0) = %s" % (len(got),
                                                              minima))


if __name__ == "__main__":
    print("(LVIII) the F-Weil part of Orlov products over a sextic CM field")
    part_a()
    part_b()
    part_c()
    scan = run_scan()
    part_d(scan)
    part_e(scan)
    part_f(scan)
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
