#!/usr/bin/env python3
# Supporting script for item (LXI), code/k3_hodge.py (round 19, (F3') through motives).
"""
The cohomology of a generalized Kummer variety K = K_{m-1}(A) (A an abelian
surface, dim K = 2(m-1)) sector by sector, with the action of A[m].

Decomposition (Goettsche-Soergel; motivic form: Fu-Tian-Vial, Xu):
  H^*(K) = sum over partitions nu of m, with l = l(nu), d = gcd(nu):
           H^{* - 2(m - l)}( F_nu )^{C(nu)},
  F_nu = {y in A^l : sum nu_i y_i = 0}  = disjoint union of d^4 translates of
  an abelian variety B_nu of dimension 2(l-1); C(nu) permutes the y_i with equal
  nu_i; H^1(B_nu) = H^1(A) (x) W^vee, W = {w in Q^l : sum nu_i w_i = 0}.
  A[m] acts by diagonal translation; it permutes the d^4 components transitively
  (tau -> tau + (m/d) a), so the sector contributes one copy of
  H^*(B_nu)^{C(nu)} to the A[m]-invariant part and d^4 - 1 copies to the rest.

Checks (all exact, with sympy polynomials):
  * Euler numbers  e(K_{m-1}(A)) = m^3 sigma(m)   (Goettsche);
  * the invariant part equals P(A^[m]) / (1+z)^4, computed independently from
    Goettsche's formula for Hilbert schemes of an abelian surface; this is the
    part reached through the etale cover A x K -> A^[m];
  * known Betti numbers b_0..b_4 = 1,0,7,8,108 (m=3) and 1,0,7,8,51,56,458 (m=4).
Output: the non-invariant part, sector by sector.  For m = 3 it is the 80
classes of H^4 carried by the 81 points of A[3] (algebraic: Hassett-Tschinkel's
planes).  For m >= 4 it contains, in the sector nu = (2,2,...), copies of H^2 of
an abelian variety, hence transcendental classes: the invariant part alone does
not put K in the class A of the paper.
"""
import itertools
from math import gcd
from functools import reduce
import sympy as sp

z, tt = sp.symbols('z t')

def partitions(m, maxpart=None):
    if maxpart is None:
        maxpart = m
    if m == 0:
        yield ()
        return
    for k in range(min(m, maxpart), 0, -1):
        for rest in partitions(m - k, k):
            yield (k,) + rest

def cycle_type(perm):
    n = len(perm); seen = [False]*n; ct = []
    for i in range(n):
        if not seen[i]:
            L = 0; j = i
            while not seen[j]:
                seen[j] = True; j = perm[j]; L += 1
            ct.append(L)
    return ct

def invariant_series(nu):
    """graded dims of H^*(B_nu)^{C(nu)} as a polynomial in z."""
    l = len(nu)
    # group: product of symmetric groups on blocks of equal parts
    blocks = {}
    for i, p in enumerate(nu):
        blocks.setdefault(p, []).append(i)
    blocklists = list(blocks.values())
    total = 0; count = 0
    for perms in itertools.product(*[list(itertools.permutations(b)) for b in blocklists]):
        perm = list(range(l))
        for b, pb in zip(blocklists, perms):
            for src, dst in zip(b, pb):
                perm[src] = dst
        ct = cycle_type(perm)
        detQl = sp.prod([1 - (-z)**c for c in ct])       # det(1 + z*pi | Q^l)
        detW = sp.cancel(detQl / (1 + z))                 # det(1 + z*pi | W)
        total += sp.expand(detW**4)
        count += 1
    return sp.expand(total / count)

def kummer_sectors(m):
    inv = 0; non = 0; rows = []
    for nu in partitions(m):
        l = len(nu); d = reduce(gcd, nu)
        I = invariant_series(nu)
        shift = z**(2*(m - l))
        inv += sp.expand(shift*I)
        non += sp.expand((d**4 - 1)*shift*I)
        rows.append((nu, l, d, 2*(m - l), sp.Poly(I, z).all_coeffs()[::-1]))
    return sp.expand(inv), sp.expand(non), rows

def hilb_abelian_surface(m):
    """Goettsche's formula, as a truncated power series in t with integer
    polynomial coefficients in z (no symbolic series expansion)."""
    from math import comb
    b = [1, 4, 6, 4, 1]
    ser = [dict() for _ in range(m + 1)]
    ser[0][0] = 1
    for k in range(1, m + 1):
        for i in range(5):
            a = 2*k - 2 + i
            # factor = sum_j c_j x^j, x = z^a t^k
            if i % 2 == 0:
                cj = lambda j: comb(b[i] + j - 1, j)       # (1 - x)^(-b)
            else:
                cj = lambda j: comb(b[i], j)               # (1 + x)^(+b)
            new_ser = [dict() for _ in range(m + 1)]
            for tdeg in range(m + 1):
                for zdeg, c in ser[tdeg].items():
                    j = 0
                    while tdeg + j*k <= m:
                        cc = cj(j)
                        if cc:
                            key = zdeg + j*a
                            new_ser[tdeg + j*k][key] = new_ser[tdeg + j*k].get(key, 0) + c*cc
                        j += 1
            ser = new_ser
    return sp.expand(sum(c*z**e for e, c in ser[m].items()))

def coeffs(p, deg):
    P = sp.Poly(p, z)
    return [P.coeff_monomial(z**k) for k in range(deg + 1)]

known = {3: [1, 0, 7, 8, 108, 8, 7, 0, 1], 4: [1, 0, 7, 8, 51, 56, 458, 56, 51, 8, 7, 0, 1]}
allok = True
for m in range(2, 6):
    inv, non, rows = kummer_sectors(m)
    tot = sp.expand(inv + non)
    dimK = 2*(m - 1)
    b = coeffs(tot, 2*dimK)
    euler = sum((-1)**k*bk for k, bk in enumerate(b))
    sigma = sum(dd for dd in range(1, m + 1) if m % dd == 0)
    ok_e = (euler == m**3*sigma)
    hil = hilb_abelian_surface(m)
    q_inv = sp.cancel(hil/(1 + z)**4)
    ok_inv = sp.expand(q_inv - inv) == 0
    ok_known = (m not in known) or (b == known[m])
    allok &= ok_e and ok_inv and ok_known
    print(f"\n=== K_{m-1}(A), dim {dimK}: Betti numbers {b}")
    print(f"    Euler number {euler} = m^3 sigma(m) = {m**3*sigma}: {ok_e};"
          f" invariant part = P(A^[{m}])/(1+z)^4: {ok_inv}; known Betti numbers: {ok_known}")
    print(f"    A[{m}]-invariant part : {coeffs(inv, 2*dimK)}")
    print(f"    non-invariant part    : {coeffs(non, 2*dimK)}")
    for nu, l, d, sh, I in rows:
        if d > 1:
            print(f"      sector nu={nu}: l={l}, d={d}, {d**4 - 1} nontrivial characters, "
                  f"shift {sh}, H^*(B_nu)^C(nu) dims {I}  (dim B_nu = {2*(l-1)})")
    # transcendental content of the non-invariant part: sectors with d>1 and l>=2
    trans = [(nu, l, d) for nu, l, d, sh, I in rows if d > 1 and l >= 2]
    if trans:
        print(f"    => non-invariant sectors with dim B_nu > 0: {trans}; their H^2(B_nu) "
              f"contains H^2 of an abelian surface, hence T(A) != 0: transcendental classes")
    else:
        print("    => every non-invariant sector is a set of points: the non-invariant part is spanned "
              "by algebraic classes (fibres of the Hilbert-Chow map)")
print("\nALL CHECKS PASSED" if allok else "\nSOME CHECK FAILED")
