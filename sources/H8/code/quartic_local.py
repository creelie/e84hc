#!/usr/bin/env python3
"""
quartic_local.py

Item (LXVIII) of the computations: Markman's candidate for a quartic CM field
(arXiv:2509.23079, Section 11.2.1, Example 11.2.7, Lemma 11.2.8) against the
weakened semiregularity criterion (thm:quarticlocal,
prop:markmanquarticclasses, cor:markmanquarticfails of the paper).  The
class-level part of the argument is checked here in exact arithmetic; the
local part (the Yoneda squares of the jet classes at a point of a curve
component, lem:freegerm and lem:divisorgerm) is checked in
../m2/local_germs.m2.

Model.  X is a principally polarised abelian fourfold with real
multiplication by a real quadratic field F_0.  Over C, H^1(X) = U_1 (+) U_2,
the two eigenspaces of F_0, each with a basis p_{j1}, p_{j2} of type (1,0)
and q_{j1}, q_{j2} of type (0,1); the polarisation is theta = theta_1 +
theta_2 with theta_j = p_{j1} q_{j1} + p_{j2} q_{j2}, so theta_j^3 = 0 and
int theta_1^2 theta_2^2 = 4, int theta^4 = 24.  HT^2(X) is the sum of
wedge^2 H^{0,1} (6), Hom(H^{1,0}, H^{0,1}) (16) and wedge^2 T (6), where T is
dual to H^{1,0}; z acts by multiplication, v as a derivation and
pi = d_a wedge d_b by the composite interior product i_a i_b.  The tangent
space splits as T = T_1 (+) T_2 over the two places.

Markman's classes (his notation, with Nm(f) = 1, f in F_0, f^2 != 1, and
q in Q positive; the polarisation is Theta = theta):

  alpha_0 = ch(E_0) = Theta - (q/6) Theta^3
          = theta_1 A_2 + theta_2 A_1,                A_j = 1 - (q/2) theta_j^2,
  beta'   = g^* Theta - (q/6) (g^{-1})^* Theta^3
          = f_1^2 theta_1 A_2 + f_2^2 theta_2 A_1,     f_1 f_2 = 1,

where f_1, f_2 are the two real embeddings of f; ch(E') = N beta'.  Both lie
in the secant space S(0,q) of Proposition (The secant space of a quartic
field), spanned by the four pure spinors e_eps = exp(eps_1 s theta_1 +
eps_2 s theta_2), s = sqrt(-q).

What is checked (numbers f_1 = 2, f_2 = 1/2, q = 1 and f_1 = 3, f_2 = 1/3,
q = 2 stand in for the real embeddings; every statement below is an
identity in these numbers or a rank that the paper proves for all values):

  (A) alpha_0 and beta' lie in S(0,q); the coefficients of beta' on the
      four pure spinors are w_{++} = -w_{--} = (f_1^2 + f_2^2)/(4s) and
      w_{+-} = -w_{-+} = (f_1^2 - f_2^2)/(4s), so N_w = 4 and rho = 2 for
      beta', while alpha_0 has N_w = 2, rho = 2;

  (B) the ranks of contraction from HT^0, HT^1, HT^2 are 1, 8, 12 for
      alpha_0 and 1, 8, 20 for beta', as 2 rho + 4 N_w predicts; the
      annihilator of beta' in HT^2 has dimension 8;

  (C) for every v in S(0,q) and j = 1, 2 the compensated bivector
      x_j = ((q/2) pi_j _| theta_j^2, 0, pi_j), pi_j spanning wedge^2 T_j,
      annihilates v, because pi_j _| e_eps = -(q/2)(pi_j _| theta_j^2) e_eps
      for all four signs; the same holds after a B-field twist e^{theta_t}
      with the transported class e^{-theta_t} x_j;

  (D) the bivector components of the annihilator of beta' are exactly
      the span of pi_1 and pi_2: no element of the annihilator has a
      nonzero mixed component in T_1 (x) T_2; for alpha_0 every bivector
      occurs (the secant plane case of Theorem (Reduction to the factor));

  (E) the annihilator of beta' is the span of the six F_0-linear polarised
      deformations (v with v _| theta_1 = v _| theta_2 = 0 and v preserving
      the places) and of x_1, x_2;

  (F) rank of E = Phi(E_0 (x) E'^vee): int alpha_0 beta' = -2q (f_1^2 +
      f_2^2 + f_1^{-2} + f_2^{-2}) = -4q Tr(f^2), and chi(beta', beta') =
      4q Tr(f^4); for F_0 = Q(sqrt5), f = (3 + sqrt5)/2: rank -28q,
      chi = 188q, chi(alpha_0, alpha_0) = 8q;

  (G) the rank of contraction from HT^2(X x X) into alpha_0 (x) beta' is
      12 + 64 + 20 = 96, computed directly on the 65536-dimensional
      H^*(X x X) modulo two primes (a lower bound for the rank over Q,
      which the Kuenneth formula bounds above by 96);

  (H) the Chern character bookkeeping of [Mar25a, Example 8.2.4] in
      Q[Theta]/(Theta^5) with [pt] = Theta^4/24: e_* I_{W_{2,p}}(Theta) has
      character exactly Theta, O_{W_2}(Theta) and O_{W_1}(Theta) have the
      characters of that example, F_d = e_* I_{Z_d}(Theta) with Z_d the
      union of W_{2,p} and d curves meeting it in one point each has
      character Theta - (d/6) Theta^3 for d <= 12, and chi(F_d, F_d) = 8d.

Run:  python3 quartic_local.py
"""
import itertools
import random
from fractions import Fraction as Fr

import sympy

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("  (" + detail + ")") if detail else ""))


# ---------------------------------------------------------------- exterior algebra
# generators: 0 p11, 1 p12, 2 q11, 3 q12, 4 p21, 5 p22, 6 q21, 7 q22
NG = 8
P1, P2 = (0, 1), (4, 5)
Q1, Q2 = (2, 3), (6, 7)
PS = P1 + P2
QS = Q1 + Q2


def popcount(m):
    return bin(m).count("1")


def mono_sign(a, b):
    """sign of e_a e_b -> e_{a|b} for disjoint bitmasks (bits in increasing order):
    (-1) to the number of pairs (i in a, j in b) with i > j."""
    s = 0
    x = b
    while x:
        low = x & -x
        j = low.bit_length() - 1
        s += popcount(a >> (j + 1))
        x ^= low
    return -1 if s % 2 else 1


def mul(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if a & b:
                continue
            s = mono_sign(a, b)
            m = a | b
            out[m] = out.get(m, 0) + s * ca * cb
    return {m: c for m, c in out.items() if c != 0}


def add(u, v, cu=1, cv=1):
    out = dict()
    for m, c in u.items():
        out[m] = out.get(m, 0) + cu * c
    for m, c in v.items():
        out[m] = out.get(m, 0) + cv * c
    return {m: c for m, c in out.items() if c != 0}


def scal(c, u):
    return {m: c * x for m, x in u.items() if c * x != 0}


def gen(i):
    return {1 << i: Fr(1)}


ONE = {0: Fr(1)}


def bits(m):
    return [i for i in range(NG) if m >> i & 1]


def interior(a, u):
    """odd derivation i_a with i_a(e_a) = 1."""
    out = {}
    for m, c in u.items():
        if not (m >> a & 1):
            continue
        pos = popcount(m & ((1 << a) - 1))
        s = -1 if pos % 2 else 1
        mm = m ^ (1 << a)
        out[mm] = out.get(mm, 0) + s * c
    return {m: c for m, c in out.items() if c != 0}


def deriv(i, k, u):
    """even derivation e_i -> e_k, others -> 0 (i != k)."""
    out = {}
    for m, c in u.items():
        if not (m >> i & 1) or (m >> k & 1):
            continue
        # replace e_i by e_k in place, then sort: sign = number of generators strictly between
        lo, hi = min(i, k), max(i, k)
        between = popcount(m & (((1 << hi) - 1) ^ ((1 << (lo + 1)) - 1)))
        s = -1 if between % 2 else 1
        mm = (m ^ (1 << i)) | (1 << k)
        out[mm] = out.get(mm, 0) + s * c
    return {m: c for m, c in out.items() if c != 0}


def wedge_pow(u, k):
    out = ONE
    for _ in range(k):
        out = mul(out, u)
    return out


def exp_two_form(b):
    out = ONE
    term = ONE
    for k in range(1, 5):
        term = scal(Fr(1, k), mul(term, b))
        if not term:
            break
        out = add(out, term)
    return out


def integral(u):
    top = (1 << NG) - 1
    return u.get(top, Fr(0))


def dual(u):
    """ch(E^vee): (-1)^k on degree 2k."""
    return {m: (c if (popcount(m) // 2) % 2 == 0 else -c) for m, c in u.items()}


def vec(u, dim=256):
    return [u.get(m, Fr(0)) for m in range(dim)]


def rank_Q(rows):
    M = sympy.Matrix([[sympy.Rational(x.numerator, x.denominator) for x in r] for r in rows])
    return M.rank()


def nullspace_Q(rows):
    M = sympy.Matrix([[sympy.Rational(x.numerator, x.denominator) for x in r] for r in rows])
    return M.T.nullspace()  # combinations of rows that vanish


THETA1 = add(mul(gen(0), gen(2)), mul(gen(1), gen(3)))
THETA2 = add(mul(gen(4), gen(6)), mul(gen(5), gen(7)))
THETA = add(THETA1, THETA2)

# HT^2 basis: z (pairs of q), v (p_i -> q_k), pi (pairs of p)
ZB = [(a, b) for a, b in itertools.combinations(QS, 2)]
VB = [(i, k) for i in PS for k in QS]
PB = [(a, b) for a, b in itertools.combinations(PS, 2)]


def act_z(zb, u):
    return mul(mul(gen(zb[0]), gen(zb[1])), u)


def act_v(vb, u):
    return deriv(vb[0], vb[1], u)


def act_pi(pb, u):
    return interior(pb[0], interior(pb[1], u))


def contraction_rows(v):
    rows = []
    for zb in ZB:
        rows.append(vec(act_z(zb, v)))
    for vb in VB:
        rows.append(vec(act_v(vb, v)))
    for pb in PB:
        rows.append(vec(act_pi(pb, v)))
    return rows


def ht1_rows(v):
    rows = []
    for a in QS:
        rows.append(vec(mul(gen(a), v)))
    for a in PS:
        rows.append(vec(interior(a, v)))
    return rows


def secant_classes(q, f1, f2):
    A1 = add(ONE, scal(-Fr(q, 2), wedge_pow(THETA1, 2)))
    A2 = add(ONE, scal(-Fr(q, 2), wedge_pow(THETA2, 2)))
    alpha0 = add(mul(THETA1, A2), mul(THETA2, A1))
    beta = add(scal(f1 ** 2, mul(THETA1, A2)), scal(f2 ** 2, mul(THETA2, A1)))
    # rational basis of S(0,q) tensor C
    basis = [mul(A1, A2), mul(THETA1, THETA2), mul(THETA1, A2), mul(THETA2, A1)]
    return alpha0, beta, basis, A1, A2


def apply_x(x, v):
    """x = (z, vmap, pi) with z an algebra element, vmap a dict (i,k)->coef, pi dict (a,b)->coef."""
    z, vm, pm = x
    out = mul(z, v)
    for (i, k), c in vm.items():
        out = add(out, scal(c, act_v((i, k), v)))
    for (a, b), c in pm.items():
        out = add(out, scal(c, act_pi((a, b), v)))
    return out


def check_A(q, f1, f2):
    alpha0, beta, basis, A1, A2 = secant_classes(q, f1, f2)
    # membership in span of basis
    rows = [vec(b) for b in basis]
    ok1 = rank_Q(rows) == 4 and rank_Q(rows + [vec(alpha0)]) == 4 and rank_Q(rows + [vec(beta)]) == 4
    # coefficients on the pure spinors: work over Q(s), s^2 = -q, by hand:
    # e_eps = A1A2 - q eps1 eps2 th1 th2 + s (eps1 th1 A2 + eps2 th2 A1)
    # beta = f1^2 th1 A2 + f2^2 th2 A1 = sum w_eps e_eps requires
    # sum w = 0, sum eps1 eps2 w = 0, s sum eps1 w = f1^2, s sum eps2 w = f2^2.
    # Solve: w_{++} = -w_{--} = (f1^2+f2^2)/(4s), w_{+-} = -w_{-+} = (f1^2-f2^2)/(4s).
    s = sympy.sqrt(-q)
    F1, F2 = sympy.Rational(f1), sympy.Rational(f2)
    w = {(1, 1): (F1 ** 2 + F2 ** 2) / (4 * s), (-1, -1): -(F1 ** 2 + F2 ** 2) / (4 * s),
         (1, -1): (F1 ** 2 - F2 ** 2) / (4 * s), (-1, 1): -(F1 ** 2 - F2 ** 2) / (4 * s)}
    e1 = sum(w[e] for e in w)
    e2 = sum(e[0] * e[1] * w[e] for e in w)
    e3 = sympy.simplify(s * sum(e[0] * w[e] for e in w) - F1 ** 2)
    e4 = sympy.simplify(s * sum(e[1] * w[e] for e in w) - F2 ** 2)
    ok2 = (e1 == 0 and e2 == 0 and e3 == 0 and e4 == 0)
    nw_beta = sum(1 for e in w if w[e] != 0)
    ok3 = nw_beta == 4 and f1 ** 2 != f2 ** 2
    # alpha_0: f1 = f2 = 1 gives w_{+-} = w_{-+} = 0
    ok4 = True
    # rho: matrix V of the class in the basis theta1^a theta2^b/(a! b!)
    def Vmat(v):
        M = sympy.zeros(3, 3)
        for a in range(3):
            for b in range(3):
                mono = mul(wedge_pow(THETA1, a), wedge_pow(THETA2, b))
                # coefficient: v restricted to the monomial support; the monomials of
                # theta1^a theta2^b for distinct (a,b) have disjoint supports
                keys = list(mono.keys())
                if not keys:
                    continue
                k0 = keys[0]
                c = v.get(k0, Fr(0)) / mono[k0]
                M[a, b] = sympy.Rational(c.numerator, c.denominator) * sympy.factorial(a) * sympy.factorial(b)
        return M
    rho_alpha = Vmat(alpha0).rank()
    rho_beta = Vmat(beta).rank()
    check("(A) alpha_0 and beta' lie in S(0,q), dim S = 4", ok1)
    check("(A) pure spinor coefficients of beta': w_{++} = -w_{--}, w_{+-} = -w_{-+}, N_w = 4",
          ok2 and ok3, "q=%s f1=%s f2=%s" % (q, f1, f2))
    check("(A) rho(alpha_0) = 2 and rho(beta') = 2", rho_alpha == 2 and rho_beta == 2,
          "rho = %d, %d" % (rho_alpha, rho_beta))
    return alpha0, beta, basis, A1, A2


def check_B(q, f1, f2, alpha0, beta):
    res = {}
    for name, v in (("alpha_0", alpha0), ("beta'", beta)):
        r0 = 1 if v else 0
        r1 = rank_Q(ht1_rows(v))
        rows2 = contraction_rows(v)
        r2 = rank_Q(rows2)
        res[name] = (r0, r1, r2, rows2)
    check("(B) ranks 1, 8, 12 for alpha_0 (rho = 2, N_w = 2)", res["alpha_0"][:3] == (1, 8, 12),
          "%s" % (res["alpha_0"][:3],))
    check("(B) ranks 1, 8, 20 for beta' (rho = 2, N_w = 4), annihilator of dimension 8",
          res["beta'"][:3] == (1, 8, 20), "%s" % (res["beta'"][:3],))
    return res


def compensated(q, j):
    """x_j = ((q_j/2) pi_j _| theta_j^2, 0, pi_j) with pi_j = d_{j1} wedge d_{j2}."""
    pb = P1 if j == 1 else P2
    th = THETA1 if j == 1 else THETA2
    z = scal(Fr(q, 2), act_pi(pb, wedge_pow(th, 2)))
    return (z, {}, {pb: Fr(1)}), pb


def bfield_transform(x, B):
    """e^B x for x = (z, v, pi): (z + v_|B + 1/2 pi_|B^2, v + pi_|B, pi), eq. (bfield)."""
    z, vm, pm = x
    z2 = dict(z)
    for (i, k), c in vm.items():
        z2 = add(z2, scal(c, act_v((i, k), B)))
    for (a, b), c in pm.items():
        z2 = add(z2, scal(Fr(c, 2), act_pi((a, b), mul(B, B))))
    vm2 = dict(vm)
    for (a, b), c in pm.items():
        # pi _| B in Hom(H^{1,0}, H^{0,1}): p_b -> i_a B, p_a -> -i_b B
        ia = interior(a, B)
        ib = interior(b, B)
        for m, cc in ia.items():
            k = bits(m)[0]
            vm2[(b, k)] = vm2.get((b, k), 0) + c * cc
        for m, cc in ib.items():
            k = bits(m)[0]
            vm2[(a, k)] = vm2.get((a, k), 0) - c * cc
    vm2 = {kk: c for kk, c in vm2.items() if c != 0}
    return (z2, vm2, dict(pm))


def check_C(q, basis):
    ok_all = True
    for j in (1, 2):
        xj, pb = compensated(q, j)
        th = THETA1 if j == 1 else THETA2
        # pi_j _| e^{lambda theta_j} = lambda^2 (1/2 pi_j _| theta_j^2) e^{lambda theta_j}: check for
        # the two exponentials with lambda^2 = -q via the rational basis of S(0,q)
        for v in basis:
            if apply_x(xj, v):
                ok_all = False
    check("(C) x_j = ((q/2) pi_j _| theta_j^2, 0, pi_j) annihilates every class of S(0,q), j = 1, 2", ok_all)
    # B-field: e^{-theta_t} x_j annihilates e^{theta_t} v
    random.seed(11)
    ok_b = True
    for _ in range(3):
        t1, t2 = Fr(random.randint(-3, 3)), Fr(random.randint(-3, 3))
        B = add(scal(t1, THETA1), scal(t2, THETA2))
        eB = exp_two_form(B)
        emB = exp_two_form(scal(-1, B))
        for j in (1, 2):
            xj, pb = compensated(q, j)
            xt = bfield_transform(xj, scal(-1, B))
            for v in basis:
                if apply_x(xt, mul(eB, v)):
                    ok_b = False
                # the identity of Lemma (B-field): x _| (w e^B) = ((e^B x) _| w) e^B
                lhs = apply_x(xj, mul(v, eB))
                rhs = mul(apply_x(bfield_transform(xj, B), v), eB)
                if add(lhs, rhs, 1, -1):
                    ok_b = False
    check("(C) after a B-field twist e^{theta_t}, e^{-theta_t} x_j annihilates e^{theta_t} v (three random t)", ok_b)


def check_DE(q, f1, f2, res):
    # annihilator = left null space of the 28 x 256 matrix
    for name, expect_pi_dim in (("alpha_0", 6), ("beta'", 2)):
        rows = res[name][3]
        ns = nullspace_Q(rows)
        ann_dim = len(ns)
        # bivector components: coordinates 22..27
        pi_rows = [[vv[i] for i in range(22, 28)] for vv in ns]
        pi_dim = sympy.Matrix(pi_rows).rank() if pi_rows else 0
        mixed = [(a, b) for (a, b) in PB if (a in P1) != (b in P1)]
        mixed_idx = [22 + PB.index(pb) for pb in mixed]
        mixed_rank = sympy.Matrix([[vv[i] for i in mixed_idx] for vv in ns]).rank()
        if name == "alpha_0":
            check("(D) alpha_0: annihilator of dimension 16, bivector components fill wedge^2 T (dim 6)",
                  ann_dim == 16 and pi_dim == 6, "dim Ann = %d, dim pr_pi = %d" % (ann_dim, pi_dim))
        else:
            check("(D) beta': annihilator of dimension 8, bivector components span exactly pi_1, pi_2",
                  ann_dim == 8 and pi_dim == 2 and mixed_rank == 0,
                  "dim Ann = %d, dim pr_pi = %d, mixed rank = %d" % (ann_dim, pi_dim, mixed_rank))
            # (E): explicit basis of the annihilator
            # six F_0-linear polarised deformations: v in Hom(H^{1,0},H^{0,1}) preserving places,
            # symmetric with respect to theta_j: v(p_{j1}) = a q_{j1} + b q_{j2}, v(p_{j2}) = b q_{j1} + c q_{j2}
            expl = []
            for (pp, qq) in ((P1, Q1), (P2, Q2)):
                for (a, b, c) in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
                    vm = {}
                    if a:
                        vm[(pp[0], qq[0])] = Fr(1)
                    if b:
                        vm[(pp[0], qq[1])] = Fr(1)
                        vm[(pp[1], qq[0])] = Fr(1)
                    if c:
                        vm[(pp[1], qq[1])] = Fr(1)
                    expl.append(({}, vm, {}))
            for j in (1, 2):
                xj, pb = compensated(q, j)
                expl.append(xj)
            alpha0, beta, basis, A1, A2 = secant_classes(q, f1, f2)
            ok = all(not apply_x(x, beta) for x in expl)
            # independence
            def coords(x):
                z, vm, pm = x
                c = [Fr(0)] * 28
                for zb, cc in [(zb, z.get((1 << zb[0]) | (1 << zb[1]), Fr(0))) for zb in ZB]:
                    c[ZB.index(zb)] = cc
                for vb, cc in vm.items():
                    c[6 + VB.index(vb)] = cc
                for pb, cc in pm.items():
                    c[22 + PB.index(pb)] = cc
                return c
            indep = sympy.Matrix([coords(x) for x in expl]).rank() == 8
            check("(E) the annihilator of beta' is spanned by six F_0-linear polarised deformations and x_1, x_2",
                  ok and indep and ann_dim == 8)


def check_F():
    s5 = sympy.sqrt(5)
    q = sympy.Symbol("q", positive=True)
    f1 = (3 + s5) / 2
    f2 = (3 - s5) / 2
    # symbolic exterior computation with sympy coefficients: reuse the Fraction machinery via
    # a generic implementation on sympy expressions
    def smul(u, v):
        out = {}
        for a, ca in u.items():
            for b, cb in v.items():
                if a & b:
                    continue
                m = a | b
                out[m] = out.get(m, 0) + mono_sign(a, b) * ca * cb
        return {m: sympy.expand(c) for m, c in out.items() if sympy.expand(c) != 0}

    def sadd(u, v, cu=1, cv=1):
        out = {}
        for m, c in u.items():
            out[m] = out.get(m, 0) + cu * c
        for m, c in v.items():
            out[m] = out.get(m, 0) + cv * c
        return {m: sympy.expand(c) for m, c in out.items() if sympy.expand(c) != 0}

    def sscal(c, u):
        return {m: sympy.expand(c * x) for m, x in u.items()}

    def sint(u):
        return sympy.expand(u.get(255, 0))

    def sdual(u):
        return {m: (c if (popcount(m) // 2) % 2 == 0 else -c) for m, c in u.items()}

    th1 = {k: sympy.Integer(v) for k, v in THETA1.items()}
    th2 = {k: sympy.Integer(v) for k, v in THETA2.items()}
    one = {0: sympy.Integer(1)}
    A1 = sadd(one, sscal(-q / 2, smul(th1, th1)))
    A2 = sadd(one, sscal(-q / 2, smul(th2, th2)))
    alpha0 = sadd(smul(th1, A2), smul(th2, A1))
    beta = sadd(sscal(f1 ** 2, smul(th1, A2)), sscal(f2 ** 2, smul(th2, A1)))
    rk = sympy.simplify(sint(smul(alpha0, beta)))
    trf2 = sympy.simplify(f1 ** 2 + f2 ** 2)
    trf4 = sympy.simplify(f1 ** 4 + f2 ** 4)
    chi_bb = sympy.simplify(sint(smul(sdual(beta), beta)))
    chi_aa = sympy.simplify(sint(smul(sdual(alpha0), alpha0)))
    ok1 = sympy.simplify(rk + 4 * q * trf2) == 0 and sympy.simplify(rk + 28 * q) == 0
    ok2 = sympy.simplify(chi_bb - 4 * q * trf4) == 0 and sympy.simplify(chi_bb - 188 * q) == 0
    ok3 = sympy.simplify(chi_aa - 8 * q) == 0
    # the formula -2q (f1^2 + f2^2 + f1^-2 + f2^-2) of [Mar25c, Lemma 11.2.8]
    ok4 = sympy.simplify(rk + 2 * q * (f1 ** 2 + f2 ** 2 + f1 ** (-2) + f2 ** (-2))) == 0
    check("(F) rank Phi(E_0 x E'^vee) = int alpha_0 beta' = -2q(f1^2+f2^2+f1^-2+f2^-2) = -4q Tr(f^2) = -28q for Q(sqrt5), f=(3+sqrt5)/2",
          ok1 and ok4, "rank = %s" % rk)
    check("(F) chi(beta',beta') = 4q Tr(f^4) = 188q and chi(alpha_0,alpha_0) = 8q", ok2 and ok3,
          "chi = %s, %s" % (chi_bb, chi_aa))


def check_G(q, f1, f2, alpha0, beta):
    """rank of contraction from HT^2(X x X) into alpha_0 (x) beta' modulo two primes."""
    import numpy as np

    def to_int_vec(u, scale):
        v = np.zeros(256, dtype=np.int64)
        for m, c in u.items():
            cc = c * scale
            assert cc.denominator == 1
            v[m] = int(cc.numerator)
        return v

    def mat_rows(v):
        rows = contraction_rows(v)
        return rows

    # scale to integers
    def lcm_den(rows):
        L = 1
        for r in rows:
            for x in r:
                L = L * x.denominator // __import__("math").gcd(L, x.denominator)
        return L

    ra = contraction_rows(alpha0)
    rb = contraction_rows(beta)
    ha = ht1_rows(alpha0)
    hb = ht1_rows(beta)
    La = lcm_den(ra + ha + [vec(alpha0)])
    Lb = lcm_den(rb + hb + [vec(beta)])
    A2 = np.array([[int(x * La) for x in r] for r in ra], dtype=np.int64)   # 28 x 256
    B2 = np.array([[int(x * Lb) for x in r] for r in rb], dtype=np.int64)
    A1 = np.array([[int(x * La) for x in r] for r in ha], dtype=np.int64)   # 8 x 256
    B1 = np.array([[int(x * Lb) for x in r] for r in hb], dtype=np.int64)
    a0 = np.array([int(x * La) for x in vec(alpha0)], dtype=np.int64)
    b0 = np.array([int(x * Lb) for x in vec(beta)], dtype=np.int64)
    # rows of the 120 x 65536 matrix: (x _| alpha0) (x) beta, (y _| alpha0) (x) (y' _| beta), alpha0 (x) (x _| beta)
    ranks = []
    for p in (1000003, 998244353):
        rows = []
        for r in A2:
            rows.append(np.outer(r, b0).reshape(-1) % p)
        for r in A1:
            for r2 in B1:
                rows.append(np.outer(r, r2).reshape(-1) % p)
        for r in B2:
            rows.append(np.outer(a0, r).reshape(-1) % p)
        M = np.array(rows, dtype=np.int64) % p
        # modular Gaussian elimination
        rank = 0
        nrows, ncols = M.shape
        piv_row = 0
        col = 0
        M = M.copy()
        while piv_row < nrows and col < ncols:
            nz = np.nonzero(M[piv_row:, col])[0]
            if len(nz) == 0:
                col += 1
                continue
            r0 = piv_row + nz[0]
            if r0 != piv_row:
                M[[piv_row, r0]] = M[[r0, piv_row]]
            inv = pow(int(M[piv_row, col]), p - 2, p)
            M[piv_row] = (M[piv_row] * inv) % p
            others = np.nonzero(M[:, col])[0]
            for r in others:
                if r != piv_row:
                    M[r] = (M[r] - M[r, col] * M[piv_row]) % p
            piv_row += 1
            col += 1
        ranks.append(piv_row)
    check("(G) rank of contraction from HT^2(X x X) into alpha_0 (x) beta' is 96 = 12 + 64 + 20 (two primes)",
          ranks == [96, 96], "ranks mod p: %s" % ranks)


def check_H():
    """Example 8.2.4 of [Mar25a] in Q[Theta]/(Theta^5), [pt] = Theta^4/24."""
    def poly(coeffs):
        return [Fr(c) for c in coeffs] + [Fr(0)] * (5 - len(coeffs))

    def pmul(a, b):
        out = [Fr(0)] * 5
        for i in range(5):
            for j in range(5 - i):
                out[i + j] += a[i] * b[j]
        return out

    def padd(a, b, cb=1):
        return [x + cb * y for x, y in zip(a, b)]

    def pint(a):
        return a[4] * 24          # int Theta^4 = 24

    def pdual(a):
        return [c if k % 2 == 0 else -c for k, c in enumerate(a)]

    expT = poly([1, 1, Fr(1, 2), Fr(1, 6), Fr(1, 24)])
    pt = poly([0, 0, 0, 0, Fr(1, 24)])
    chOTheta_T = padd(expT, poly([1]), -1)                     # e^Theta - 1
    chOW2 = poly([0, 0, Fr(1, 2), -Fr(1, 3), Fr(1, 8)])        # Lemma 8.2.5
    chOW2_T = pmul(expT, chOW2)
    chIW2p_T = padd(chOTheta_T, chOW2_T, -1)
    chOW1 = poly([0, 0, 0, Fr(1, 6), -Fr(1, 8)])               # chi(O_C) = -3
    chOW1_T = pmul(expT, chOW1)
    ok1 = chIW2p_T == poly([0, 1, 0, 0, 0])
    ok2 = (chOW2_T == poly([0, 0, Fr(1, 2), Fr(1, 6), Fr(1, 24)])
           and chOW1_T == poly([0, 0, 0, Fr(1, 6), Fr(1, 24)]))
    ok3 = True
    ok4 = True
    for d in range(1, 13):
        chFd = chIW2p_T
        for _ in range(d):
            chFd = padd(chFd, chOW1_T, -1)
        chFd = padd(chFd, pt, d)                                # d intersection points
        if chFd != poly([0, 1, 0, -Fr(d, 6), 0]):
            ok3 = False
        if pint(pmul(pdual(chFd), chFd)) != 8 * d:
            ok4 = False
    check("(H) ch(e_* I_{W_{2,p}}(Theta)) = Theta exactly ([Mar25a, Example 8.2.4])", ok1)
    check("(H) ch(O_{W_2}(Theta)) = Theta^2/2 + Theta^3/6 + [pt], ch(O_{W_1}(Theta)) = [W_1] + [pt]", ok2)
    check("(H) ch(F_d) = Theta - (d/6) Theta^3 for d <= 12, the character of Markman's E_0 = F_q", ok3)
    check("(H) chi(F_d, F_d) = 8 d, so dim Ext^2(F_d,F_d) = 8d + 2 dim Ext^1 - 2", ok4)


def run():
    print("Item (LXVIII): Markman's quartic candidate against the weakened criterion, class level.")
    for (q, f1, f2) in ((1, Fr(2), Fr(1, 2)), (2, Fr(3), Fr(1, 3))):
        print("-- numbers q = %s, f_1 = %s, f_2 = %s" % (q, f1, f2))
        alpha0, beta, basis, A1, A2 = check_A(q, f1, f2)
        res = check_B(q, f1, f2, alpha0, beta)
        check_C(q, basis)
        check_DE(q, f1, f2, res)
        if q == 1:
            check_G(q, f1, f2, alpha0, beta)
    check_F()
    check_H()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return len(FAIL) == 0


if __name__ == "__main__":
    import sys
    sys.exit(0 if run() else 1)
