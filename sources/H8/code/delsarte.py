#!/usr/bin/env python3
"""
delsarte.py

Item (LXVI) of the computations: Delsarte fourfolds and the Fermat cover
that puts them in the domain of (F3').

A Delsarte hypersurface in P^{r+1} is X_A = { sum_i prod_j x_j^{a_ij} = 0 },
with A = (a_ij) an invertible (r+2) x (r+2) matrix of non-negative integers
whose rows all sum to the degree m.  With d = |det A| and B = +-adj(A), so that
A B = d I, the rows of B all sum to d/m, an integer, and the monomial map
y -> (prod_k y_k^{b_jk + c})_j (c chosen to make the exponents non-negative)
carries the Fermat hypersurface of degree d into X_A:
F_A(psi(y)) = (y_0 ... y_{r+1})^{c m} (y_0^d + ... + y_{r+1}^d).
On the tori it is an isogeny, so it is dominant.

What is checked:

  (A) the shapes: the sums of Fermat terms x^6, chains
      x_1^5 x_2 + ... + x_{k-1}^5 x_k + x_k^6 and loops
      x_1^5 x_2 + ... + x_k^5 x_1 (k >= 2) in six variables number 29, the
      coefficient of t^6 in 1/(1-t) prod_{k>=2} (1-t^k)^{-2};

  (B) for each of the 29: A is invertible, A adj(A) = det(A) I, the rows of
      adj(A) all sum to det(A)/6, an integer, and after the shift c the
      exponent vectors of F_A(psi(y)) are d e_i + 6c (1, ..., 1), which is the
      identity F_A(psi(y)) = (y_0 ... y_5)^{6c} sum_i y_i^d;

  (C) for each of the 29, and for the loops and chains of every length from 2
      to 6 and every degree m from 3 to 8 (completed by Fermat terms of
      degree m), the reduced Groebner basis over Q of the partial
      derivatives has, for every variable, a leading monomial that is a pure
      power of it; so the partials vanish together only at 0 and the
      hypersurface is smooth;

  (D) the loop sextic x_0^5 x_1 + ... + x_5^5 x_0: det A = 5^6 - 1 = 15624,
      adj(A) is the circulant with first row (3125, -625, 125, -25, 5, -1),
      and the standard monomials of the Groebner basis number 1, 426, 1751,
      426, 1 in the degrees 0, 6, 12, 18, 24, and 5^6 = 15625 in all: the
      Hodge numbers h^{4,0}, h^{3,1}, h^{2,2}_prim of the smooth sextic
      fourfold, and the Milnor number;

  (E) the product argument used in the paper for loops: at a common zero of
      the partials with every coordinate nonzero, the product of the
      relations x_{j-1}^{m-1} = -(m-1) x_j^{m-2} x_{j+1} gives
      1 = (1-m)^k, which fails for m >= 3, k >= 1; the polynomial identity
      and the inequality are checked for k <= 8, m <= 12.

Everything is exact rational arithmetic.

Run:  python3 delsarte.py
"""
import itertools

import numpy as np
import sympy

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("  (" + detail + ")") if detail else ""))


X = sympy.symbols("x0:6")
NV = 6


def kinds(total):
    return [("F", 1)] + [(t, k) for k in range(2, total + 1) for t in "CL"]


def multisets(total, ks, start=0):
    if total == 0:
        yield []
        return
    for i in range(start, len(ks)):
        t, k = ks[i]
        if k <= total:
            for rest in multisets(total - k, ks, i):
                yield [ks[i]] + rest


def shape_poly(shape, m):
    """the polynomial of a shape of degree m in X, and its exponent matrix."""
    rows = []
    pos = 0
    for t, k in shape:
        v = list(range(pos, pos + k))
        pos += k
        if t == "F":
            rows.append({v[0]: m})
        elif t == "C":
            for a in range(k - 1):
                rows.append({v[a]: m - 1, v[a + 1]: 1})
            rows.append({v[-1]: m})
        else:
            for a in range(k):
                rows.append({v[a]: m - 1, v[(a + 1) % k]: 1})
    A = sympy.Matrix([[r.get(j, 0) for j in range(NV)] for r in rows])
    F = sum(sympy.Mul(*[X[j] ** e for j, e in r.items()]) for r in rows)
    return F, A


def leading_monomials(F):
    J = [sympy.diff(F, v) for v in X]
    G = sympy.groebner(J, *X, order="grevlex", domain=sympy.QQ)
    return [sympy.Poly(g, *X).monoms(order="grevlex")[0] for g in G.exprs]


def pure_powers(lm):
    return all(any(mon[i] > 0 and sum(mon) == mon[i] for mon in lm)
               for i in range(NV))


def cover_identity(A, m):
    det = A.det()
    adj = A.adjugate()
    d = abs(det)
    B = adj if det > 0 else -adj
    ok = A * adj == det * sympy.eye(NV)
    sums = [sum(B.row(i)) for i in range(NV)]
    ok &= all(s * m == d for s in sums)
    c = max(0, -min(B))
    Bs = B + c * sympy.ones(NV, NV)
    E = A * Bs
    want = d * sympy.eye(NV) + c * m * sympy.ones(NV, NV)
    ok &= E == want and min(Bs) >= 0
    return ok, d


def main():
    print("(A) the shapes of degree six in six variables")
    shapes = list(multisets(6, kinds(6)))
    t = sympy.symbols("t")
    gf = 1 / (1 - t)
    for k in range(2, 7):
        gf *= 1 / (1 - t ** k) ** 2
    coeff = sympy.series(gf, t, 0, 7).removeO().coeff(t, 6)
    check("the sums of Fermat, chain and loop blocks number 29, the "
          "coefficient of t^6 in the generating function",
          len(shapes) == 29 == coeff, "%d shapes" % len(shapes))

    print("(B) the Fermat cover of each shape")
    ok = True
    ds = []
    for sh in shapes:
        F, A = shape_poly(sh, 6)
        o, d = cover_identity(A, 6)
        ok &= o and A.det() != 0
        ds.append(d)
    check("for each of the 29: A invertible, A adj(A) = det(A) I, rows of "
          "adj(A) summing to det(A)/6, and F_A(psi(y)) = (y_0...y_5)^{6c} "
          "sum y_i^d", ok, "d from %d to %d" % (min(ds), max(ds)))

    print("(C) smoothness")
    ok = True
    for sh in shapes:
        F, A = shape_poly(sh, 6)
        ok &= pure_powers(leading_monomials(F))
    check("each of the 29 sextic fourfolds is smooth: the Groebner basis of "
          "the partials has a pure power of every variable among its "
          "leading monomials", ok)
    ok = True
    ntest = 0
    for m in range(3, 9):
        for k in range(2, 7):
            for t_ in "CL":
                sh = [(t_, k)] + [("F", 1)] * (6 - k)
                F, A = shape_poly(sh, m)
                ok &= pure_powers(leading_monomials(F))
                o, d = cover_identity(A, m)
                ok &= o
                ntest += 1
    check("the loops and chains of every length 2..6 and degree 3..8, "
          "completed by Fermat terms, are smooth and have the Fermat cover",
          ok, "%d hypersurfaces" % ntest)

    print("(D) the loop sextic")
    F, A = shape_poly([("L", 6)], 6)
    adj = A.adjugate()
    row = [3125, -625, 125, -25, 5, -1]
    circ = sympy.Matrix(6, 6, lambda i, j: row[(j - i) % 6])
    lm = leading_monomials(F)
    lead = np.array(lm, dtype=np.int64)
    counts = []
    for deg in range(0, 26):
        mons = np.array([np.bincount(c, minlength=NV) for c in
                         itertools.combinations_with_replacement(range(NV),
                                                                 deg)],
                        dtype=np.int64).reshape(-1, NV)
        div = (mons[:, None, :] >= lead[None, :, :]).all(axis=2).any(axis=1)
        counts.append(int((~div).sum()))
    check("det A = 15624 = 5^6 - 1 and adj(A) is the circulant "
          "(3125, -625, 125, -25, 5, -1)",
          A.det() == 15624 == 5 ** 6 - 1 and adj == circ)
    check("the Jacobian ring has dimensions 1, 426, 1751, 426, 1 in degrees "
          "0, 6, 12, 18, 24, is zero in degree 25, and has total dimension "
          "15625 = 5^6",
          [counts[k] for k in (0, 6, 12, 18, 24)] == [1, 426, 1751, 426, 1]
          and counts[25] == 0 and sum(counts) == 15625,
          "h^{4,0}, h^{3,1}, h^{2,2}_prim = %d, %d, %d"
          % (counts[0], counts[6], counts[12]))

    print("(E) the product argument for loops")
    ok = True
    for m in range(3, 13):
        for k in range(1, 9):
            y = sympy.symbols("y0:%d" % k)
            lhs = sympy.Mul(*[-(m - 1) * y[j] ** (m - 2) * y[(j + 1) % k]
                              for j in range(k)])
            rhs = (1 - m) ** k * sympy.Mul(*[y[(j - 1) % k] ** (m - 1)
                                             for j in range(k)])
            ok &= sympy.expand(lhs - rhs) == 0 and (1 - m) ** k != 1
    check("prod_j (-(m-1) x_j^{m-2} x_{j+1}) = (1-m)^k prod_j x_{j-1}^{m-1} "
          "and (1-m)^k != 1 for 3 <= m <= 12, 1 <= k <= 8", ok)

    print()
    print("%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    raise SystemExit(main())
