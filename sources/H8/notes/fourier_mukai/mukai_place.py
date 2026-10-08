#!/usr/bin/env python3
"""
mukai_place.py

The Fourier-Mukai group of a member of a quartic CM family at n = 2, acting
place by place on Chern characters, and what it does to the characters of
rank 88 left open by the corrected criterion.

Model: that of item (LXV), imported from quartic_rank.py.  H^1(A,C) has
basis a_{s,k} (type (1,0)) and b_{s,k} (type (0,1)), s = 0..3 the embeddings,
s = 0, 1 over tau_1 and s = 2, 3 over tau_2; theta_t is the component of the
polarisation at tau_t, alpha_s spans wedge^4 V_s, omega = sum_s alpha_s.

L_t is the wedge with theta_t and Lambda_t is minus the contraction with the
bivector pi_t dual to theta_t (the pairs a_{0,k}, b_{1,k} and a_{1,k}, b_{0,k}
at tau_1).  Tensoring with a line bundle whose class is eta_b acts on H^* as
exp(b_1 L_1 + b_2 L_2); the conjugate of tensoring with a line bundle on the
dual by the Fourier-Mukai transform acts as exp(beta_1 Lambda_1 + beta_2
Lambda_2).  What is checked:

  (A) (L_t, H_t, Lambda_t), H_t = (degree in the eight generators of the
      place) - 4, is an sl_2-triple at each place, and the two triples
      commute;
  (B) Lambda_t alpha_s = 0 for every s and t, and L_t alpha_s = 0 for s over
      tau_t: each omega_t = alpha_s + alpha_s' is invariant under the sl_2
      of its own place and a lowest weight vector of weight -4 at the other;
  (C) exp(beta Lambda_t) e^{lambda theta_t} = (1 + lambda beta)^4
      e^{lambda theta_t / (1 + lambda beta)}, and at beta = -1/lambda it is
      lambda^4 theta_t^4 / 24, for several rational lambda and beta;
  (D) exp(-Lambda_1/lambda_1 - Lambda_2/lambda_2) carries
      c + sum_t a_t (e^{lambda_t theta_t} - 1) + b (e^{lambda_1 theta_1 +
      lambda_2 theta_2} - 1) + omega to
      c - a_1 - a_2 - b + sum_t a_t lambda_t^4 theta_t^4/24
      + b lambda_1^4 lambda_2^4 theta_1^4 theta_2^4/576 + omega,
      which lies in the span of the products of the alpha_s;
  (E) the rank r(gamma) of the contraction HT^2 -> H^*, xi -> xi _| gamma,
      is unchanged by exp(b L) and exp(beta Lambda), with independent
      rational parameters at the two places, at the fifteen polynomials of
      item (LXV) and at random compositions of up to four such operators;
  (F) the ranks of the characters of (D): 88 for b = 0 and 104 for b != 0,
      the same before and after the transformation;
  (G) on the linear shape exp(beta Lambda) (c + s_1 theta_1 + s_2 theta_2
      + omega) = c + 4 (s_1 beta_1 + s_2 beta_2) + s_1 theta_1 + s_2 theta_2
      + omega, of rank 88;
  (H) a combination u m^4 + v n^4 of fourth powers of independent linear
      forms with u v != 0 has four distinct roots, while the quartic
      x^3 (c x + 4 s y) of the linear shape has a triple root; and the
      linear shape at a place, as an element of S_1 (x) S_2, has left span
      containing x^3 y;
  (I) the Weyl element w = exp(L) exp(-Lambda) exp(L), at both places,
      carries 1 to the point class; w exp(beta Lambda) carries the linear
      shape into degrees >= 12, with a nonzero degree 12 part
      N (omega_1 theta_2^4 + theta_1^4 omega_2)/24 whose integral against
      every theta_i theta_j vanishes, while int (theta_1 + theta_2)^8 != 0;
  (J) on a product member B x B' (k = 0 for B, k = 1 for B'), omega lies in
      H^2(B) (x) H^2(B') with tensor rank 4, the classes theta_t have no
      component there, so the H^2 (x) H^2 part of ch_2 of the linear shape
      has tensor rank 4, while an exterior product has it of rank at most 1.
  (K) the cohomological Fourier transform F(x) = int x e^ell satisfies
      y F(x) = F(iota_y x) for y in wedge^2 H^1 of the dual, dim A <= 3;
  (L) the least rank r over the 25 monomials theta_1^i theta_2^j is 28, and
      scaling the (1,0)-generators of one place keeps r.

Exact rational arithmetic throughout.  Run:  python3 mukai_place.py
"""
import os
import random
import sys
from fractions import Fraction as Fr
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
for cand in (HERE, os.path.join(HERE, "..", "..", "code"),
             os.path.join(HERE, ".."), "/home/claude/h8/code"):
    if os.path.exists(os.path.join(cand, "quartic_rank.py")):
        sys.path.insert(0, os.path.abspath(cand))
        break
import quartic_rank as Q  # noqa: E402

import sympy  # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


gen = Q.gen
addf = Q.addf
wedge = Q.wedge


def clean(f):
    return {m: Fr(c) for m, c in f.items() if c != 0}


def scale(f, c):
    return clean({m: v * c for m, v in f.items()})


def contract2(f, g1, g2):
    out = {}
    for m, c in f.items():
        s1, m1 = Q.contract_gen(m, g2)
        if not s1:
            continue
        s2, m2 = Q.contract_gen(m1, g1)
        if not s2:
            continue
        out[m2] = out.get(m2, 0) + s1 * s2 * c
    return clean(out)


def Lam(t, f):
    """standard Lambda_t = minus the contraction with pi_t"""
    s0, s1 = 2 * t, 2 * t + 1
    out = {}
    for k in range(2):
        out = addf(out, contract2(f, gen(s0, 0, k), gen(s1, 1, k)))
        out = addf(out, contract2(f, gen(s1, 0, k), gen(s0, 1, k)))
    return scale(out, -1)


def Lt(t, f):
    return clean(wedge(Q.TH[t], f))


def deg_t(m, t):
    return sum(1 for s in (2 * t, 2 * t + 1) for kind in (0, 1)
               for k in (0, 1) if m >> gen(s, kind, k) & 1)


def Ht(t, f):
    return clean({m: c * (deg_t(m, t) - 4) for m, c in f.items()})


def comm(X, Y, f):
    return clean(addf(X(Y(f)), Y(X(f)), -1))


def expop(op, f, c):
    """exp(c * op) f for a nilpotent op"""
    out, term, j = dict(clean(f)), dict(clean(f)), 0
    while term:
        j += 1
        term = scale(op(term), Fr(c) / j)
        out = addf(out, term)
    return clean(out)


def g_apply(word, f):
    """word: list of (kind, t, c) applied right to left as written: the last
    element acts first"""
    for kind, t, c in reversed(word):
        op = (lambda h, t=t: Lt(t, h)) if kind == "L" else \
            (lambda h, t=t: Lam(t, h))
        f = expop(op, f, c)
    return f


def fourier_check(G, rng):
    """the cohomological Fourier transform F(x) = int_A x e^{ell} of an
    abelian variety of dimension G turns wedge with y in wedge^2 H^1(A^) into
    contraction with y: y F(x) = F(iota_y x)"""
    n = 2 * G
    NB = 2 * n

    def wd(f, h):
        out = {}
        for m1, c1 in f.items():
            for m2, c2 in h.items():
                if m1 & m2:
                    continue
                sgn = 1
                for i in range(NB):
                    if m1 >> i & 1:
                        sgn *= (-1) ** bin(m2 & ((1 << i) - 1)).count("1")
                out[m1 | m2] = out.get(m1 | m2, 0) + sgn * c1 * c2
        return clean(out)

    def ctr(f, g):
        out = {}
        for m, c in f.items():
            if m >> g & 1:
                mm = m & ~(1 << g)
                out[mm] = out.get(mm, 0) + \
                    (-1) ** bin(m & ((1 << g) - 1)).count("1") * c
        return clean(out)
    ell = {}
    for i in range(n):
        ell = addf(ell, wd({1 << i: 1}, {1 << (n + i): 1}))
    expl, term = {0: Fr(1)}, {0: Fr(1)}
    for k in range(1, n + 1):
        term = scale(wd(term, ell), Fr(1, k))
        expl = addf(expl, term)
    alle = (1 << n) - 1

    def F(x):
        out = {}
        for m, c in wd(x, expl).items():
            if m & alle == alle:
                out[m >> n] = out.get(m >> n, 0) + c
        return clean(out)
    ok = True
    for _ in range(5):
        y = {}
        for i in range(n):
            for j in range(i + 1, n):
                c = rng.randint(-2, 2)
                if c:
                    y = addf(y, {(1 << i) | (1 << j): c})
        for _ in range(4):
            x = clean({rng.getrandbits(n): rng.randint(-3, 3)
                       for _ in range(6)})
            lhs = wd(y, F(x))
            rhs = {}
            for m, c in y.items():
                i, j = [k for k in range(n) if m >> k & 1]
                rhs = addf(rhs, ctr(ctr(x, j), i), c)
            ok &= lhs == F(rhs)
    return ok


ONE = {0: Fr(1)}
OMEGA = clean(Q.omega())


def thpow(t, k):
    return scale(Q.powf(Q.TH[t], k), Fr(1, factorial(k)))


def expth(t, lam):
    out = {}
    for k in range(5):
        out = addf(out, thpow(t, k), Fr(lam) ** k)
    return clean(out)


def poly(e):
    """sum e_ij theta_1^i theta_2^j / (i! j!)"""
    out = {}
    for (i, j), c in e.items():
        if c:
            out = addf(out, Q.THP[(i, j)], Fr(c))
    return clean(out)


def rank_of(f):
    return Q.sparse_rank([Q.apply_op(op, f) for op in Q.OPS])


def degree_parts(f):
    parts = {}
    for m, c in f.items():
        parts.setdefault(bin(m).count("1"), {})[m] = c
    return parts


TOP = (1 << 16) - 1


def integral(f):
    return f.get(TOP, 0)


def random_class(rng, n=40):
    f = {}
    for _ in range(n):
        m = rng.getrandbits(16)
        f[m] = f.get(m, 0) + rng.randint(-3, 3)
    return clean(f)


FIFTEEN = [
    {}, {(1, 0): 1}, {(2, 0): 2}, {(2, 0): 2, (0, 1): 1},
    {(2, 0): 2, (0, 2): 2}, {(1, 1): 1}, {(1, 2): 2}, {(2, 2): 4},
    {(2, 0): 1}, {(2, 0): 1, (0, 1): 1}, {(2, 0): 1, (0, 2): 2},
    {(2, 0): 1, (0, 2): 1}, {(2, 0): 1, (1, 1): 1},
    {(2, 0): 1, (1, 1): 1, (0, 2): 2}, {(2, 0): 1, (1, 1): 1, (0, 2): 1},
]
FIFTEEN_R = [80, 84, 88, 92, 96, 104, 108, 112, 87, 91, 95, 94, 107, 111,
             110]


def main():
    rng = random.Random(20260929)

    print("(A) an sl_2 at each real place")
    ok_triple, ok_comm = True, True
    for _ in range(4):
        f = random_class(rng)
        for t in (0, 1):
            L = (lambda h, t=t: Lt(t, h))
            La = (lambda h, t=t: Lam(t, h))
            H = (lambda h, t=t: Ht(t, h))
            ok_triple &= comm(L, La, f) == Ht(t, f)
            ok_triple &= comm(H, L, f) == scale(Lt(t, f), 2)
            ok_triple &= comm(H, La, f) == scale(Lam(t, f), -2)
        for X in (lambda h: Lt(0, h), lambda h: Lam(0, h)):
            for Y in (lambda h: Lt(1, h), lambda h: Lam(1, h)):
                ok_comm &= comm(X, Y, f) == {}
    check("[L_t, Lambda_t] = H_t, [H_t, L_t] = 2 L_t, [H_t, Lambda_t] = "
          "-2 Lambda_t on random classes", ok_triple)
    check("the operators of the two places commute", ok_comm)
    check("Lambda_t theta_t = 4 (so exp(beta Lambda) theta = theta + 4 beta)",
          Lam(0, Q.TH[0]) == {0: 4} and Lam(1, Q.TH[1]) == {0: 4})

    print("(B) the Weil classes")
    ok = all(Lam(t, clean(Q.alpha(s))) == {} for t in (0, 1)
             for s in range(4))
    check("Lambda_t alpha_s = 0 for all s, t", ok)
    ok = all(Lt(s // 2, clean(Q.alpha(s))) == {} for s in range(4))
    check("L_t alpha_s = 0 for s over tau_t", ok)
    ok = all(Lt(1 - s // 2, clean(Q.alpha(s))) != {} for s in range(4))
    check("L_t alpha_s != 0 for s over the other place", ok)
    ok = all(Ht(s // 2, clean(Q.alpha(s))) == {} and
             Ht(1 - s // 2, clean(Q.alpha(s))) ==
             scale(clean(Q.alpha(s)), -4) for s in range(4))
    check("H_t alpha_s = 0 at its own place and -4 alpha_s at the other",
          ok)

    print("(C) the exponential curve and the cusp")
    ok = True
    for lam, beta in [(Fr(1), Fr(3)), (Fr(2), Fr(-1, 5)), (Fr(-3, 7), Fr(2)),
                      (Fr(5, 2), Fr(1, 3))]:
        for t in (0, 1):
            lhs = expop(lambda h, t=t: Lam(t, h), expth(t, lam), beta)
            k = 1 + lam * beta
            rhs = scale(expth(t, lam / k), k ** 4)
            ok &= lhs == rhs
    check("exp(beta Lambda) e^{lambda theta} = (1 + lambda beta)^4 "
          "e^{lambda theta/(1 + lambda beta)}", ok)
    ok = True
    for lam in [Fr(1), Fr(2), Fr(-1, 3), Fr(7, 4)]:
        for t in (0, 1):
            lhs = expop(lambda h, t=t: Lam(t, h), expth(t, lam), -1 / lam)
            ok &= lhs == scale(thpow(t, 4), lam ** 4)
    check("at beta = -1/lambda the image is lambda^4 theta^4 / 24", ok)

    print("(D) the exponential characters go to Weil tori characters")
    ok, ok_span = True, True
    SPAN = set()
    for S in range(16):
        f = {0: 1}
        for s in range(4):
            if S >> s & 1:
                f = wedge(f, Q.alpha(s))
        SPAN |= set(f)
    for (c, a1, a2, b, l1, l2) in [
            (3, 2, 5, 0, Fr(1), Fr(2)), (1, Fr(1, 2), -3, 0, Fr(-1, 3), Fr(4)),
            (0, 1, 1, 2, Fr(1), Fr(1)), (2, -1, 3, Fr(1, 4), Fr(3), Fr(-2)),
            (5, 0, 0, 1, Fr(1, 2), Fr(5))]:
        g = addf(dict(OMEGA), ONE, c - a1 - a2 - b)
        g = addf(g, expth(0, l1), a1)
        g = addf(g, expth(1, l2), a2)
        g = addf(g, wedge(expth(0, l1), expth(1, l2)), b)
        g = clean(g)
        word = [("La", 0, -1 / l1), ("La", 1, -1 / l2)]
        img = g_apply(word, g)
        want = addf(dict(OMEGA), ONE, c - a1 - a2 - b)
        want = addf(want, thpow(0, 4), a1 * l1 ** 4)
        want = addf(want, thpow(1, 4), a2 * l2 ** 4)
        want = addf(want, wedge(thpow(0, 4), thpow(1, 4)),
                    b * l1 ** 4 * l2 ** 4)
        ok &= img == clean(want)
        ok_span &= set(img) <= SPAN
    check("exp(-Lambda_1/lambda_1 - Lambda_2/lambda_2) gives the theta^4 "
          "shape (five examples)", ok)
    check("the image lies in the span of the products alpha_Sigma", ok_span)

    print("(E) the rank of the contraction is invariant")
    ok, n = True, 0
    for e, r0 in zip(FIFTEEN, FIFTEEN_R):
        g = clean(addf(dict(OMEGA), poly(e)))
        if rank_of(g) != r0:
            ok = False
        word = [("L", rng.randint(0, 1), Fr(rng.randint(-5, 5),
                                           rng.randint(1, 4))),
                ("La", rng.randint(0, 1), Fr(rng.randint(-5, 5),
                                            rng.randint(1, 4)))]
        img = g_apply(word, g)
        ok &= rank_of(img) == r0
        n += 1
    check("the fifteen values of item (LXV) are kept by a random pair "
          "exp(b L_t) exp(beta Lambda_t')", ok, "%d characters" % n)
    ok = True
    for trial in range(6):
        e = {(i, j): Fr(rng.randint(-3, 3), rng.randint(1, 3))
             for (i, j) in [(1, 0), (0, 1), (2, 0), (1, 1)]
             if rng.random() < 0.6}
        g = clean(addf(dict(OMEGA), poly(e)))
        r0 = rank_of(g)
        word = []
        for _ in range(4):
            word.append((rng.choice(["L", "La"]), rng.randint(0, 1),
                         Fr(rng.randint(-4, 4), rng.randint(1, 3))))
        ok &= rank_of(g_apply(word, g)) == r0
    check("r(g gamma) = r(gamma) for words of length four in the generators",
          ok, "six random characters")

    print("(F) the ranks of the excluded characters")
    res = []
    for (c, a1, a2, b, l1, l2) in [
            (3, 2, 5, 0, Fr(1), Fr(2)), (0, 1, Fr(-2, 3), 0, Fr(3), Fr(-1)),
            (0, 1, 1, 2, Fr(1), Fr(1)), (2, -1, 3, Fr(1, 4), Fr(3), Fr(-2)),
            (1, 0, 0, 3, Fr(2), Fr(-1, 2))]:
        g = addf(dict(OMEGA), ONE, c - a1 - a2 - b)
        g = addf(g, expth(0, l1), a1)
        g = addf(g, expth(1, l2), a2)
        g = addf(g, wedge(expth(0, l1), expth(1, l2)), b)
        g = clean(g)
        img = g_apply([("La", 0, -1 / l1), ("La", 1, -1 / l2)], g)
        res.append((b != 0, rank_of(g), rank_of(img)))
    ok = all((r == r2 == (104 if hasb else 88)) for hasb, r, r2 in res)
    check("rank 88 without the mixed exponential, 104 with it", ok,
          str([(r, r2) for _, r, r2 in res]))

    print("(G) the linear shape: normal form of the rank")
    ok = True
    for (c, s1, s2, b1, b2) in [(3, 1, 2, Fr(1), Fr(-1)), (0, Fr(1, 2), -1,
                                                          Fr(2), Fr(3)),
                                (5, 2, 2, Fr(-1, 4), Fr(1, 3))]:
        g = clean(addf(addf(addf(dict(OMEGA), ONE, c), Q.TH[0], s1),
                       Q.TH[1], s2))
        img = g_apply([("La", 0, b1), ("La", 1, b2)], g)
        want = clean(addf(addf(addf(dict(OMEGA), ONE,
                                    c + 4 * (s1 * b1 + s2 * b2)),
                               Q.TH[0], s1), Q.TH[1], s2))
        ok &= img == want and rank_of(g) == 88 and rank_of(img) == 88
    check("exp(beta Lambda)(c + eta_s + omega) = c + 4 Tr(s beta) + eta_s + "
          "omega, rank 88", ok)

    print("(H) the linear shape is not a Weil tori character after any g")
    x, y, u, v, p, q, r, s = sympy.symbols("x y u v p q r s")
    m = p * x + q * y
    nn = r * x + s * y
    f = sympy.expand(u * m ** 4 + v * nn ** 4)
    disc = sympy.discriminant(f.subs(y, 1), x)
    target = 256 * u ** 3 * v ** 3 * (p * s - q * r) ** 12
    check("disc(u m^4 + v n^4) = 256 u^3 v^3 det(m, n)^12, nonzero when "
          "u v det != 0", sympy.expand(disc - target) == 0)
    c0, s0 = sympy.symbols("c0 s0")
    lin = sympy.expand(x ** 3 * (c0 * x + 4 * s0 * y))
    check("x^3 (c x + 4 s y) has x = 0 as a root of multiplicity three",
          sympy.div(lin, x ** 3, x)[1] == 0)
    # left span of the linear shape in S_1 (x) S_2, via the basis
    # theta^k/k! <-> C(4,k) x^{4-k} y^k
    Mrows = []
    c, s1, s2 = 3, 1, 2
    coeff = {(0, 0): c, (1, 0): s1, (0, 1): s2}
    Mat = sympy.zeros(5, 5)
    for (i, j), val in coeff.items():
        Mat[i, j] = val * comb(4, i) * comb(4, j)
    cols = Mat.columnspace()
    left = [sum(col[k] * x ** (4 - k) * y ** k for k in range(5))
            for col in cols]
    ok = len(left) == 2 and all(sympy.expand(lf.subs(x, 0)) == 0
                                for lf in left)
    ok &= sympy.Matrix([[sympy.Poly(lf, x, y).coeff_monomial(x ** (4 - k) *
                                                             y ** k)
                         for k in range(5)] for lf in left]).rank() == 2
    check("the left span of the linear shape is span(x^4, x^3 y), which "
          "contains x^3 y", ok, str(left))

    print("(I) the linear shape under the Weyl element")
    W = [("L", 0, 1), ("La", 0, -1), ("L", 0, 1),
         ("L", 1, 1), ("La", 1, -1), ("L", 1, 1)]
    w1 = g_apply(W, ONE)
    pt = clean(wedge(thpow(0, 4), thpow(1, 4)))
    check("the Weyl element w = exp(L) exp(-Lambda) exp(L) at both places "
          "carries 1 to the point class theta_1^4 theta_2^4 / 576",
          w1 == pt)
    ok_low, ok_nz, ok_pair = True, True, True
    kappa = clean(addf(Q.TH[0], Q.TH[1]))
    for trial in range(6):
        b1 = Fr(rng.randint(-4, 4), rng.randint(1, 3))
        b2 = Fr(rng.randint(-4, 4), rng.randint(1, 3))
        word = W + [("La", 0, b1), ("La", 1, b2)]
        cc, s1, s2 = Fr(rng.randint(-3, 3)), Fr(rng.randint(1, 3)), \
            Fr(rng.randint(-3, -1))
        gam = clean(addf(addf(addf(dict(OMEGA), ONE, cc), Q.TH[0], s1),
                         Q.TH[1], s2))
        img = g_apply(word, gam)
        parts = degree_parts(img)
        ok_low &= all(d >= 12 for d in parts)
        d12 = parts.get(12, {})
        ok_nz &= bool(d12)
        for i in range(3):
            q2 = wedge(Q.powf(Q.TH[0], i), Q.powf(Q.TH[1], 2 - i))
            ok_pair &= integral(wedge(d12, q2)) == 0
        ok_pair &= integral(wedge(d12, wedge(kappa, kappa))) == 0
    check("w exp(beta Lambda) carries the linear shape into degrees >= 12 "
          "(six examples)", ok_low)
    check("its degree 12 part is nonzero", ok_nz)
    check("the degree 12 part has integral 0 against theta_i theta_j and "
          "(theta_1 + theta_2)^2", ok_pair)
    k8 = integral(Q.powf(kappa, 8))
    check("the polarisation theta_1 + theta_2 has nonzero top power",
          k8 != 0, "int kappa^8 = %s" % k8)
    d12 = degree_parts(g_apply(W, OMEGA)).get(12, {})
    want = clean(addf(wedge(clean(addf(clean(Q.alpha(0)), clean(Q.alpha(1)))),
                            thpow(1, 4)),
                      wedge(thpow(0, 4),
                            clean(addf(clean(Q.alpha(2)),
                                       clean(Q.alpha(3)))))))
    check("w(omega) = omega_1 theta_2^4/24 + theta_1^4 omega_2/24",
          g_apply(W, OMEGA) == want)

    print("(J) a product member B x B'")
    # H^2(B) (x) H^2(B'): components of a degree 4 class with exactly one
    # (1,0)- and one (0,1)-generator... in the k = 0 generators and the same
    # in the k = 1 generators, i.e. two generators from each factor
    def factor_split(f):
        mat = {}
        for mm, cc in f.items():
            gB = [g for g in range(16) if mm >> g & 1 and g % 2 == 0]
            gC = [g for g in range(16) if mm >> g & 1 and g % 2 == 1]
            if len(gB) == 2 and len(gC) == 2:
                mB = sum(1 << g for g in gB)
                mC = sum(1 << g for g in gC)
                # sign of splitting mm into mB ^ mC
                sgn = 1
                for g in gC:
                    sgn *= (-1) ** bin(mB >> (g + 1)).count("1")
                mat.setdefault(mB, {})[mC] = sgn * cc
        rowsB = sorted(mat)
        colsC = sorted({c_ for r_ in mat.values() for c_ in r_})
        M = sympy.Matrix([[mat[rB].get(cC, 0) for cC in colsC]
                          for rB in rowsB]) if rowsB else sympy.zeros(1, 1)
        return M.rank()
    # generator index: gen(s, kind, k) = 4 s + 2 kind + k, so k = index % 2
    rk_omega = factor_split(OMEGA)
    rk_theta = max(factor_split(clean(Q.TH[t])) for t in (0, 1))
    gam = clean(addf(addf(addf(dict(OMEGA), ONE, 3), Q.TH[0], 1), Q.TH[1],
                     -2))
    ch2 = degree_parts(gam).get(4, {})
    check("omega has tensor rank 4 in H^2(B) (x) H^2(B')", rk_omega == 4)
    check("ch_2 of the linear shape has tensor rank 4 there",
          factor_split(ch2) == 4)
    # exterior product of classes with arbitrary degree-2 parts:
    # (1 + D) (x) (1 + D'), with D in the k = 0 part, D' in the k = 1 part
    D = clean(addf(wedge({1 << gen(0, 0, 0): 1}, {1 << gen(1, 1, 0): 1}),
                   wedge({1 << gen(2, 0, 0): 1}, {1 << gen(3, 1, 0): 1}), 3))
    Dp = clean(addf(wedge({1 << gen(0, 0, 1): 1}, {1 << gen(1, 1, 1): 1}),
                    wedge({1 << gen(3, 0, 1): 1}, {1 << gen(2, 1, 1): 1}), -2))
    prod = clean(wedge(addf(dict(ONE), D), addf(dict(ONE), Dp)))
    check("an exterior product has H^2 (x) H^2 part of tensor rank 1",
          factor_split(degree_parts(prod).get(4, {})) == 1)

    print("(K) the Fourier transform conjugates wedge into contraction")
    check("y F(x) = F(iota_y x) for y in wedge^2 H^1(A^), dim A = 1, 2, 3",
          all(fourier_check(G, rng) for G in (1, 2, 3)))

    print("(L) characters without a Weil part")
    mono_r = {ij: rank_of(clean(Q.THP[ij])) for ij in Q.IJ}
    check("the least rank r(theta_1^i theta_2^j) over the 25 monomials is 28",
          min(mono_r.values()) == 28,
          "attained at %s" % sorted(ij for ij, v in mono_r.items() if v == 28))

    def torus(f, k1, k2):
        out = {}
        for m, c in f.items():
            fac = Fr(1)
            for s_ in range(4):
                for k in range(2):
                    if m >> gen(s_, 0, k) & 1:
                        fac *= (k1 if s_ < 2 else k2)
            out[m] = c * fac
        return clean(out)
    ok = torus(clean(Q.TH[0]), 3, 5) == scale(clean(Q.TH[0]), 3) and \
        torus(clean(Q.TH[1]), 3, 5) == scale(clean(Q.TH[1]), 5)
    for _ in range(4):
        e = {ij: Fr(rng.randint(-2, 2)) for ij in Q.IJ if rng.random() < 0.3}
        p0 = poly(e)
        if not p0:
            continue
        ok &= rank_of(p0) == rank_of(torus(p0, Fr(2), Fr(-3, 2))) >= 28
    check("scaling the (1,0)-generators of a place multiplies theta_t alone "
          "and keeps r; random polynomials have r >= 28", ok)

    print()
    print("%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    raise SystemExit(main())
