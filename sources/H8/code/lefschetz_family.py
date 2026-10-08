#!/usr/bin/env python3
"""
lefschetz_family.py

Item (XLII) of COMPUTATIONS.md: the finite linear algebra behind
the Lefschetz standard conjecture for the total space of an abelian scheme
over a curve whose invariant cycles are algebraic, and in particular for the
total space of a Mumford family (the theorems of the subsection "A new case of
the Lefschetz standard conjecture").

Everything is exact: exterior algebras over Q with Fraction coefficients, and
exact ranks.  Nothing is assumed about signs: the Pontryagin product is
computed from its definition, x * y = mu_*(p_1^* x . p_2^* y), with mu_*
defined by the projection formula against mu^*, and the operator Lambda is
certified by the relation [L, Lambda] = H, which determines it.

What is checked:

  (a) on an abelian variety of dimension g <= 4, for several polarisation
      types (d_1, ..., d_g), the operator Lambda of degree -2 with
      [L, Lambda] = H is x -> D^{-1} (x * gamma), where
      gamma = l^{g-1}/(g-1)!, D = int l^g / g! = d_1 ... d_g, and * is the
      Pontryagin product; so Lambda is induced by an algebraic cycle, the
      image of A x (a cycle representing gamma) under (a, b) -> (a, a + b);

  (b) the normalisation l * gamma = g D, which fixes the one global sign;

  (c) the whole construction of the theorem on a product family, where
      every class is invariant: on W = E x A with E an elliptic curve, the
      operator Lambda_rel + Lambda_C, with Lambda_rel the relative Pontryagin
      operator divided by D and Lambda_C built from bases of invariant
      classes and the inverse of their pairing matrix, satisfies
      [L, Lambda] = H for L = l + m [W_c]; and the cross relations
      [l, Lambda_C] = 0 and [[W_c], Lambda_rel] = 0 hold;

  (d) for the Hodge group of a Mumford fourfold, a Q-form of SL_2^3 acting
      on V = V_1 (x) V_2 (x) V_3, the invariants in wedge^q V have dimension
      1, 0, 1, 0, 1, 0, 1, 0, 1 for q = 0, ..., 8, spanned by the powers of
      the invariant 2-form; so the monodromy invariants of a Mumford family
      are the powers of the polarisation, which are algebraic.

Run:  python3 lefschetz_family.py
"""
from fractions import Fraction
from itertools import combinations, product
from math import factorial

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ------------------------------------------------------ exterior algebra
# A form is a dict {mask: Fraction}; generator i is bit i; a monomial is the
# wedge of its generators in increasing order.

def popcount(m):
    return bin(m).count("1")


def mono_sign(a, b):
    """sign of (monomial a) ^ (monomial b) against the sorted monomial"""
    if a & b:
        return 0
    s = 0
    bb = b
    while bb:
        j = (bb & -bb).bit_length() - 1
        s += popcount(a >> (j + 1))
        bb &= bb - 1
    return -1 if s % 2 else 1


def wedge(x, y):
    out = {}
    for a, ca in x.items():
        for b, cb in y.items():
            s = mono_sign(a, b)
            if s:
                out[a | b] = out.get(a | b, 0) + s * ca * cb
    return {k: v for k, v in out.items() if v != 0}


def add(x, y, c=1):
    out = dict(x)
    for k, v in y.items():
        out[k] = out.get(k, 0) + c * v
    return {k: v for k, v in out.items() if v != 0}


def scale(x, c):
    return {k: c * v for k, v in x.items() if c * v != 0}


def power(x, n, unit):
    out = dict(unit)
    for _ in range(n):
        out = wedge(out, x)
    return out


def integral(x, top):
    return x.get(top, Fraction(0))


def degree_basis(nbits, k):
    return [sum(1 << i for i in c) for c in combinations(range(nbits), k)]


# ------------------------------------------------ one abelian variety
# Generators of H^1(A): x_i = bit 2i, y_i = bit 2i+1, i = 0..g-1.
# Polarisation l = sum d_i x_i y_i; orientation x_1 y_1 ... x_g y_g, so that
# int l^g = g! d_1...d_g > 0.

def polarisation(g, d, off=0):
    return {(3 << (2 * i + off)): Fraction(d[i]) for i in range(g)}


def lam_sl2(g, d, x, off=0):
    """contraction by sum d_i^{-1} dy_i dx_i on the fibre generators"""
    out = {}
    for m, c in x.items():
        for i in range(g):
            pair = 3 << (2 * i + off)
            if m & pair == pair:
                # remove x_i, then y_i: each contraction carries the sign
                # (-1)^(number of generators below 2i), so the product is +1
                out[m ^ pair] = out.get(m ^ pair, 0) + c / d[i]
    return {k: v for k, v in out.items() if v != 0}


def pontryagin(g, x, y):
    """x * y = mu_*(p_1^* x . p_2^* y) on A, computed from the definition"""
    n = 2 * g
    full = (1 << n) - 1
    # p_1^* x . p_2^* y on A x A: block 1 is bits 0..n-1, block 2 bits n..2n-1
    y2 = {m << n: c for m, c in y.items()}
    z = wedge(x, y2)
    if not z:
        return {}
    k = popcount(next(iter(z)))
    tdeg = k - n
    if tdeg < 0:
        return {}
    top2 = (1 << (2 * n)) - 1
    out = {}
    for u in degree_basis(n, tdeg):
        comp = full ^ u
        s = mono_sign(u, comp)
        ustar = {comp: Fraction(s)}          # int u . ustar = 1
        # mu^* of ustar: each generator v -> v(1) + v(2)
        img = {0: Fraction(1)}
        bits = [i for i in range(n) if comp >> i & 1]
        for i in bits:
            img = wedge(img, {1 << i: Fraction(1), 1 << (i + n): Fraction(1)})
        img = scale(img, Fraction(s))
        cu = integral(wedge(z, img), top2)
        if cu:
            out[u] = cu
    return out


def op_matrix_equal(f, g_, basis):
    for m in basis:
        if f({m: Fraction(1)}) != g_({m: Fraction(1)}):
            return False
    return True


def check_fibre(g, d):
    n = 2 * g
    l = polarisation(g, d)
    D = 1
    for di in d:
        D *= di
    gamma = scale(power(l, g - 1, {0: Fraction(1)}), Fraction(1, factorial(g - 1)))
    allb = [m for k in range(n + 1) for m in degree_basis(n, k)]

    def L(x):
        return wedge(l, x)

    def Lam(x):
        return lam_sl2(g, d, x)

    # [L, Lambda] = H with H = k - g on degree k
    ok_sl2 = True
    for m in allb:
        x = {m: Fraction(1)}
        lhs = add(L(Lam(x)), Lam(L(x)), -1)
        if lhs != scale(x, Fraction(popcount(m) - g)):
            ok_sl2 = False
            break

    def P(x):
        return scale(pontryagin(g, x, gamma), Fraction(1, D))

    ok_pont = op_matrix_equal(P, Lam, allb)
    lg = pontryagin(g, l, gamma)
    return ok_sl2, ok_pont, lg.get(0, 0), g * D


def run_fibres():
    cases = [(1, (1,)), (1, (3,)), (2, (1, 1)), (2, (1, 2)), (2, (2, 5)),
             (3, (1, 1, 1)), (3, (1, 1, 3)), (3, (1, 2, 4)),
             (4, (1, 1, 1, 1)), (4, (1, 1, 2, 2))]
    all_sl2, all_p, all_norm = True, True, True
    for g, d in cases:
        a, b, lg, gD = check_fibre(g, d)
        all_sl2 &= a
        all_p &= b
        all_norm &= (lg == gD)
        print("         g=%d type %-12s  [L,Lambda]=H: %s   D^-1(x*gamma)=Lambda x: %s"
              "   l*gamma = %s = gD" % (g, str(d), a, b, lg))
    check("the contraction by the dual bivector satisfies [L, Lambda] = H, so "
          "it is the operator of B(A)", all_sl2,
          "%d abelian varieties, g <= 4, several polarisation types"
          % len(cases))
    check("Lambda = D^{-1} (x * gamma), gamma = l^{g-1}/(g-1)!: the operator "
          "of B(A) is a Pontryagin product with an algebraic class", all_p,
          "the Pontryagin product computed from mu_* and mu^*, every degree")
    check("the normalisation l * gamma = g D fixes the sign", all_norm)

    # negative control: without the factor D^{-1} the identity fails as soon
    # as the polarisation is not principal
    g, d = 2, (1, 2)
    l = polarisation(g, d)
    gamma = power(l, g - 1, {0: Fraction(1)})
    allb = [m for k in range(2 * g + 1) for m in degree_basis(2 * g, k)]
    differs = not op_matrix_equal(lambda x: pontryagin(g, x, gamma),
                                  lambda x: lam_sl2(g, d, x), allb)
    check("the factor D^{-1} is needed: for type (1,2) the bare Pontryagin "
          "product differs from Lambda", differs)


# ---------------------------------------------- the product family E x A

def run_family(g, d, m_mult=3):
    """W = E x A over E; base generators u = bit 0, v = bit 1 (pt = u v);
    fibre generators shifted by 2."""
    n = 2 * g
    N = n + 2
    top = (1 << N) - 1
    ptE = {3: Fraction(1)}
    l = polarisation(g, d, off=2)
    D = 1
    for di in d:
        D *= di
    gamma = scale(power(l, g - 1, {0: Fraction(1)}),
                  Fraction(1, factorial(g - 1)))
    fibre_mask = ((1 << n) - 1) << 2

    # relative Pontryagin: W x_E W = E x A x A, generators u, v, block1, block2
    def T(x):
        # p_1^*x (u,v and block1 as is), p_2^*gamma (fibre bits -> block2)
        g2 = {(mm >> 2) << (2 + n): c for mm, c in gamma.items()}
        z = wedge(x, g2)
        if not z:
            return {}
        k = popcount(next(iter(z)))
        tdeg = k - n
        if tdeg < 0:
            return {}
        top3 = (1 << (2 + 2 * n)) - 1
        out = {}
        for u in degree_basis(N, tdeg):
            comp = top ^ u
            s = mono_sign(u, comp)
            img = {0: Fraction(1)}
            for i in range(N):
                if comp >> i & 1:
                    if i < 2:
                        img = wedge(img, {1 << i: Fraction(1)})
                    else:
                        img = wedge(img, {1 << i: Fraction(1),
                                          1 << (i + n): Fraction(1)})
            img = scale(img, Fraction(s))
            cu = integral(wedge(z, img), top3)
            if cu:
                out[u] = cu
        return out

    def Lrel(x):
        return wedge(l, x)

    def LC(x):
        return wedge(scale(ptE, Fraction(m_mult)), x)

    # Lambda_C from bases of invariant classes (here all fibre classes)
    lamC_data = {}
    for q in range(n + 1):
        a = [mm << 2 for mm in degree_basis(n, q)]
        b = [mm << 2 for mm in degree_basis(n, n - q)]
        M = [[integral(wedge(wedge({aj: Fraction(1)}, ptE), {bk: Fraction(1)}), top)
              for bk in b] for aj in a]
        lamC_data[q] = (a, b, inverse(M))

    def LamC(x):
        out = {}
        for mm, c in x.items():
            k = popcount(mm)
            q = k - 2
            if q < 0 or q > n:
                continue
            a, b, Minv = lamC_data[q]
            xm = {mm: c}
            pair = [integral(wedge(xm, {bk: Fraction(1)}), top) for bk in b]
            for j, aj in enumerate(a):
                coef = sum(Minv[kk][j] * pair[kk] for kk in range(len(b)))
                if coef:
                    out[aj] = out.get(aj, 0) + coef
        out = {k: v for k, v in out.items() if v != 0}
        return scale(out, Fraction(1, m_mult))

    def Lam(x):
        return add(scale(T(x), Fraction(1, D)), LamC(x))

    def L(x):
        return add(Lrel(x), LC(x))

    allb = [mm for k in range(N + 1) for mm in degree_basis(N, k)]
    ok, ok1, ok2 = True, True, True
    for mm in allb:
        x = {mm: Fraction(1)}
        if add(L(Lam(x)), Lam(L(x)), -1) != scale(x, Fraction(popcount(mm) - (g + 1))):
            ok = False
        if add(Lrel(LamC(x)), LamC(Lrel(x)), -1) != {}:
            ok1 = False
        if add(LC(T(x)), T(LC(x)), -1) != {}:
            ok2 = False
    return ok, ok1, ok2


def inverse(M):
    n = len(M)
    A = [list(map(Fraction, row)) + [Fraction(int(i == j)) for j in range(n)]
         for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [v / pv for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [vr - f * vc for vr, vc in zip(A[r], A[c])]
    return [row[n:] for row in A]


def run_families():
    res = []
    for g, d in [(1, (1,)), (1, (2,)), (2, (1, 1)), (2, (1, 3))]:
        ok, ok1, ok2 = run_family(g, d)
        print("         W = E x A, g=%d type %-8s  [L,Lambda]=H: %s   "
              "[l,Lambda_C]=0: %s   [[W_c],Lambda_rel]=0: %s"
              % (g, str(d), ok, ok1, ok2))
        res.append((ok, ok1, ok2))
    check("on a product family the operator Lambda_rel + Lambda_C built as in "
          "the theorem satisfies [L, Lambda] = H for L = l + m[W_c]",
          all(r[0] for r in res), "four families, every degree")
    check("the cross relations [l, Lambda_C] = 0 and [[W_c], Lambda_rel] = 0 "
          "hold", all(r[1] and r[2] for r in res))


# ---------------------------------------------- the Mumford invariants

def rank(rows):
    A = [list(r) for r in rows]
    rk, col = 0, 0
    ncol = len(A[0]) if A else 0
    while rk < len(A) and col < ncol:
        p = next((r for r in range(rk, len(A)) if A[r][col] != 0), None)
        if p is None:
            col += 1
            continue
        A[rk], A[p] = A[p], A[rk]
        for r in range(rk + 1, len(A)):
            if A[r][col] != 0:
                f = A[r][col] / A[rk][col]
                A[r] = [a - f * b for a, b in zip(A[r], A[rk])]
        rk += 1
        col += 1
    return rk


def run_mumford():
    # V = V1 (x) V2 (x) V3, basis index (a,b,c) in {0,1}^3 -> 4a+2b+c
    e = [[0, 1], [0, 0]]
    f = [[0, 0], [1, 0]]
    idx = {t: 4 * t[0] + 2 * t[1] + t[2] for t in product((0, 1), repeat=3)}

    def lift(mat, slot):
        M = [[Fraction(0)] * 8 for _ in range(8)]
        for t in product((0, 1), repeat=3):
            for s in (0, 1):
                c = mat[s][t[slot]]
                if c:
                    t2 = list(t)
                    t2[slot] = s
                    M[idx[tuple(t2)]][idx[t]] += c
        return M

    gens = [lift(mat, sl) for sl in range(3) for mat in (e, f)]
    dims = []
    for q in range(9):
        basis = [sum(1 << i for i in c) for c in combinations(range(8), q)]
        pos = {m: i for i, m in enumerate(basis)}
        rows = []
        for X in gens:
            # derivation action of X on wedge^q V, as a matrix
            Mq = [[Fraction(0)] * len(basis) for _ in range(len(basis))]
            for j, m in enumerate(basis):
                bits = [i for i in range(8) if m >> i & 1]
                for pos_k, i in enumerate(bits):
                    for r in range(8):
                        c = X[r][i]
                        if not c:
                            continue
                        rest = m ^ (1 << i)
                        if rest >> r & 1:
                            continue
                        # replace generator i at position pos_k by r
                        left = sum(1 << b for b in bits[:pos_k])
                        right = sum(1 << b for b in bits[pos_k + 1:])
                        s1 = mono_sign(left, 1 << r)
                        s2 = mono_sign(left | (1 << r), right)
                        new = left | (1 << r) | right
                        Mq[pos[new]][j] += c * s1 * s2
            rows.extend(Mq)
        dims.append(len(basis) - rank(rows) if rows else len(basis))
    check("the invariants of the Mumford group in wedge^q V have dimensions "
          "1,0,1,0,1,0,1,0,1", dims == [1, 0, 1, 0, 1, 0, 1, 0, 1],
          "computed: %s" % dims)


if __name__ == "__main__":
    print("(XLII) the Lefschetz operator of an abelian scheme over a curve")
    run_fibres()
    run_families()
    run_mumford()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
