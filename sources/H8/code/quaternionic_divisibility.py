#!/usr/bin/env python3
"""
quaternionic_divisibility.py

The quaternionic points of the n = 2 Weil family, with the integral lattice
Lambda_b = O_b^2, O_b = Z<1, i, j, ij>, i^2 = -d, j^2 = b, ij = -ji, and the
polarisation E_b(x,y) = sum_k a_k trd(conj(x_k) i y_k).  Put

    g_b(x,y)  = E_b(j x, y),     lam_b(x,y) = -g_b(i x, y) / d,
    Z_b = g_b^2 - d lam_b^2,     Z'_b = 2 g_b lam_b,

so that Z_b + sqrt(-d) Z'_b = (g_b + sqrt(-d) lam_b)^2 spans the Weil plane.
Writing x = u + v j with u, v in K = Q(sqrt(-d)), one finds

    E_b = E_u + b E_v,     g_b = b g',     lam_b = b lam',

with E_u, E_v, g', lam' integral and independent of b.  The checks are:

  (D1) the scale-free numbers of the quaternionic model:
       int g^2 eta^2 / int eta^4 = -b/3,  int Z^2 / int eta^4 = 4 b^2 / 3,
       sigma^2 = 1/12, for every b, d and weight vector tested;
  (D2) the decomposition E_b = E_u + b E_v and g_b = b g', lam_b = b lam',
       with g', lam' integral on Lambda and the same for every b;
  (D3) hence Z_b = b^2 Z_1 and Z'_b = b^2 Z'_1 exactly, as elements of
       wedge^4 Lambda^*, where Z_1 = g'^2 - d lam'^2 is an integral
       algebraic class independent of b;
  (D4) the degree int eta_b^4 grows like b^2: the growth sits in the
       polarisation, not in the cycle;
  (D5) replacing j by alpha j, alpha in K^x, keeps the algebra and the
       point and multiplies both ratios of (D1) by N(alpha) and N(alpha)^2,
       so b is a presentation, determined only modulo N(K^x);
  (D6) the integral Weil lattice W = (Q Z + Q Z') cap wedge^4 Lambda^* has
       Gram matrix diag(8d, 8d^2) for every b, and the Z-span of products
       of two integral divisor classes meets W in a sublattice of index
       2 (a_1 a_2)^2, for every b.

Everything is exact rational and integer arithmetic.
"""

import os
import sys
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quaternionic import Model, matmul, transpose, scale  # noqa: E402

N8 = 8
K2 = list(combinations(range(N8), 2))
K4 = list(combinations(range(N8), 4))


def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("           " + detail)
    return (1, 0) if ok else (0, 1)


# ---------------------------------------------------- exterior algebra

def form(M):
    n = len(M)
    return {(a, c): F(M[a][c]) for a in range(n) for c in range(a + 1, n)
            if M[a][c] != 0}


def _sign(I, J):
    s = sum(1 for x in I for y in J if y < x)
    return -1 if s % 2 else 1


def wedge(A, B):
    R = {}
    for I, x in A.items():
        for J, y in B.items():
            if set(I) & set(J):
                continue
            K = tuple(sorted(I + J))
            R[K] = R.get(K, 0) + _sign(I, J) * x * y
    return {k: v for k, v in R.items() if v != 0}


def lin(*pairs):
    R = {}
    for c, A in pairs:
        for k, v in A.items():
            R[k] = R.get(k, 0) + c * v
    return {k: v for k, v in R.items() if v != 0}


def integ(A):
    return A.get(tuple(range(N8)), F(0))


def vec(A, keys):
    return [A.get(k, F(0)) for k in keys]


def unvec(v, keys):
    return {k: F(x) for k, x in zip(keys, v) if x != 0}


def same(A, B):
    return lin((1, A), (-1, B)) == {}


# ------------------------------------------------------ integer lattices

def int_kernel(A):
    """integer basis of {x in Z^m : A x = 0}, by column reduction."""
    k, m = len(A), len(A[0])
    A = [r[:] for r in A]
    U = [[1 if r == c else 0 for c in range(m)] for r in range(m)]
    pc = 0
    for r in range(k):
        while True:
            nz = [c for c in range(pc, m) if A[r][c] != 0]
            if len(nz) <= 1:
                break
            c0 = min(nz, key=lambda c: abs(A[r][c]))
            for c in nz:
                if c != c0:
                    q = A[r][c] // A[r][c0]
                    for rr in range(k):
                        A[rr][c] -= q * A[rr][c0]
                    for rr in range(m):
                        U[rr][c] -= q * U[rr][c0]
        nz = [c for c in range(pc, m) if A[r][c] != 0]
        if nz:
            c = nz[0]
            for rr in range(k):
                A[rr][c], A[rr][pc] = A[rr][pc], A[rr][c]
            for rr in range(m):
                U[rr][c], U[rr][pc] = U[rr][pc], U[rr][c]
            pc += 1
    return [[U[rr][c] for rr in range(m)] for c in range(pc, m)]


def complement(V):
    """integer rows C with C v = 0 exactly for v in the Q-span of V."""
    m = len(V[0])
    R = [[F(x) for x in r] for r in V]
    piv, row = [], 0
    for c in range(m):
        p = next((i for i in range(row, len(R)) if R[i][c] != 0), None)
        if p is None:
            continue
        R[row], R[p] = R[p], R[row]
        pv = R[row][c]
        R[row] = [x / pv for x in R[row]]
        for i in range(len(R)):
            if i != row and R[i][c] != 0:
                f = R[i][c]
                R[i] = [a - f * b for a, b in zip(R[i], R[row])]
        piv.append(c)
        row += 1
    out = []
    for fc in (c for c in range(m) if c not in piv):
        x = [F(0)] * m
        x[fc] = F(1)
        for i, p in enumerate(piv):
            x[p] = -R[i][fc]
        L = reduce(lambda a, b: a * b // gcd(a, b), [v.denominator for v in x])
        out.append([int(v * L) for v in x])
    return out


def saturation(V):
    return int_kernel(complement(V))


def covolume2(B):
    """gcd of the 2x2 minors of a generating set of a rank-2 lattice."""
    g = 0
    for a in range(len(B)):
        for c in range(a + 1, len(B)):
            for s, t in combinations(range(len(B[0])), 2):
                g = gcd(g, int(B[a][s] * B[c][t] - B[a][t] * B[c][s]))
    return g


def content(A):
    vals = [F(v) for v in A.values()]
    num = reduce(gcd, [v.numerator for v in vals])
    den = reduce(lambda a, b: a * b // gcd(a, b), [v.denominator for v in vals])
    return F(num, den)


# ------------------------------------------------------------- the model

def model(d, b, w=None, alpha=(1, 0)):
    M = Model(2, d, b, w)
    Bq = M.B
    Li = M.left(Bq.i())
    aj = Bq.mul((F(alpha[0]), F(alpha[1]), F(0), F(0)), Bq.j())
    Lj = M.left(aj)
    E = M.E()
    g = matmul(transpose(Lj), E)
    lam = scale(F(-1, d), matmul(transpose(Li), g))
    eta, g, lam = form(E), form(g), form(lam)
    Z = lin((1, wedge(g, g)), (-d, wedge(lam, lam)))
    Zp = lin((2, wedge(g, lam)),)
    return eta, g, lam, Z, Zp


def ratios(d, b, w=None, alpha=(1, 0)):
    eta, g, lam, Z, Zp = model(d, b, w, alpha)
    e2 = wedge(eta, eta)
    e4 = integ(wedge(e2, e2))
    gg = integ(wedge(wedge(g, g), e2)) / e4
    zz = integ(wedge(Z, Z)) / e4
    return e4, gg, zz


def weil_data(d, b, w=None):
    eta, g, lam, Z, Zp = model(d, b, w)
    NS = [unvec(v, K2) for v in saturation([vec(eta, K2), vec(g, K2),
                                            vec(lam, K2)])]
    prods = [vec(wedge(NS[a], NS[c]), K4) for a in range(len(NS))
             for c in range(a, len(NS))]
    Zv, Zpv = vec(Z, K4), vec(Zp, K4)
    W = saturation([Zv, Zpv])
    CW = complement([Zv, Zpv])
    Mt = [[int(sum(F(cw[t]) * p[t] for t in range(len(K4)))) for p in prods]
          for cw in CW]
    Mt = [r for r in Mt if any(r)]
    D = [[sum(c[k] * prods[k][t] for k in range(len(prods)))
          for t in range(len(K4))] for c in int_kernel(Mt)]
    D = [v for v in D if any(v)]
    Wf = [unvec(v, K4) for v in W]
    gram = [[integ(wedge(Wf[a], Wf[c])) for c in range(2)] for a in range(2)]
    return len(NS), F(covolume2(D), covolume2(W)), gram, W


# ----------------------------------------------------------------- runs

if __name__ == "__main__":
    NP = NF = 0
    BS = (1, 2, 3, 5, 6, 7, 10, 11, 13, 17, 23, 29, 41, 59, 101)
    DS = (1, 3)
    WS = (None, [1, 3])

    print("(D1) scale-free numbers of the quaternionic model, n = 2")
    ok = True
    for d in DS:
        for w in WS:
            for b in BS:
                e4, gg, zz = ratios(d, b, w)
                s2 = gg * gg / zz
                if not (gg == F(-b, 3) and zz == F(4 * b * b, 3)
                        and s2 == F(1, 12)):
                    ok = False
    p, f = check("int g^2 eta^2/int eta^4 = -b/3, int Z^2/int eta^4 = "
                 "4b^2/3, sigma^2 = 1/12  (%d cases)"
                 % (len(DS) * len(WS) * len(BS)), ok)
    NP += p
    NF += f

    print("(D2) E_b = E_u + b E_v, g_b = b g', lam_b = b lam'")
    ok = True
    for d in DS:
        for w in WS:
            eta0 = model(d, 0, w)[0]            # b = 0 gives E_u
            eta1 = model(d, 1, w)[0]
            Ev = lin((1, eta1), (-1, eta0))
            _, g1, l1, Z1, Zp1 = model(d, 1, w)
            integral = all(v.denominator == 1 for v in
                           list(g1.values()) + list(l1.values()))
            for b in BS:
                eta, g, lam, Z, Zp = model(d, b, w)
                ok = ok and same(eta, lin((1, eta0), (b, Ev)))
                ok = ok and same(g, lin((b, g1),)) and same(lam, lin((b, l1),))
            ok = ok and integral
    p, f = check("the decomposition holds exactly, and g' = g_1, "
                 "lam' = lam_1 are integral on Lambda", ok)
    NP += p
    NF += f

    print("(D3) the named cycle is b^2 times a b-independent integral cycle")
    ok = True
    for d in DS:
        for w in WS:
            _, _, _, Z1, Zp1 = model(d, 1, w)
            for b in BS:
                _, _, _, Z, Zp = model(d, b, w)
                ok = ok and same(Z, lin((b * b, Z1),)) \
                    and same(Zp, lin((b * b, Zp1),))
    p, f = check("Z_b = b^2 Z_1 and Z'_b = b^2 Z'_1 in wedge^4 Lambda^*", ok)
    NP += p
    NF += f

    print("(D4) the degree of the polarisation")
    ok = True
    rows = []
    for d in DS:
        for w in WS:
            e41 = ratios(d, 1, w)[0]
            for b in BS:
                e4 = ratios(d, b, w)[0]
                ok = ok and e4 == b * b * e41
            rows.append("d=%d, weights %s: int eta_b^4 = %s b^2"
                        % (d, w if w else [1, 1], e41))
    for r in rows:
        print("    " + r)
    p, f = check("int eta_b^4 = b^2 int eta_1^4", ok)
    NP += p
    NF += f

    print("(D5) b is a presentation: j -> alpha j inside one algebra")
    ok = True
    for d in DS:
        for alpha in [(1, 1), (2, 1), (F(1, 2), 0), (F(1, 3), F(1, 3)),
                      (3, 2)]:
            Na = alpha[0] ** 2 + d * alpha[1] ** 2
            e4, gg, zz = ratios(d, 1, None, alpha)
            ok = ok and gg == -Na / F(3) and zz == F(4, 3) * Na * Na \
                and gg * gg / zz == F(1, 12)
    p, f = check("the ratios become -N(alpha)/3 and 4N(alpha)^2/3 at one "
                 "and the same point", ok)
    NP += p
    NF += f

    print("(D6) the integral Weil lattice and the divisor sublattice")
    ok = True
    BS6 = (1, 2, 3, 5, 7, 11, 13)
    for d in (1, 2, 3, 7):
        for w in (None, [1, 3], [2, 5]):
            a = w if w else [1, 1]
            seen = set()
            for b in BS6:
                rk, idx, gram, W = weil_data(d, b, w)
                seen.add((rk, idx, tuple(map(tuple, gram))))
            want = (3, F(2 * (a[0] * a[1]) ** 2),
                    ((F(8 * d), F(0)), (F(0), F(8 * d * d))))
            ok = ok and seen == {want}
        print("    d=%d: Gram(W) = diag(%d, %d), index 2(a_1 a_2)^2, "
              "for every b tested" % (d, 8 * d, 8 * d * d))
    p, f = check("W and the index of the divisor-product sublattice do "
                 "not depend on b", ok)
    NP += p
    NF += f

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    sys.exit(0 if NF == 0 else 1)
