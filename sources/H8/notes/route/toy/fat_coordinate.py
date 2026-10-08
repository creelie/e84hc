"""
Chern character of the symbolic-power thickenings Z_m of the union Z_1 of the six
coordinate abelian surfaces in X = E^4 (product of four elliptic curves, product
principal polarisation Theta = theta_1 + ... + theta_4, theta_i^2 = 0).

Locally at the origin, I_{Z_1} is the Stanley-Reisner ideal of the complete graph
K_4 (uniform matroid U_{2,4}) and I_{Z_m} = I_{Z_1}^{(m)} = cap_{i<j} (x_i, x_j)^m.
By Minh-Trung / Varbaro, S/I^{(m)} is Cohen-Macaulay for every m because K_4 is a
matroid.  So Z_m is a CM codimension-two subscheme of class m * Theta^2 / 2.

For a monomial ideal J the K-polynomial K(z) = H(z) prod_i (1 - z_i), with H the
multigraded Hilbert series of S/J, is a polynomial, and
    ch(O_X / J~) = K(1 - theta_1, ..., 1 - theta_4)  in  Q[theta]/(theta_i^2),
because a multigraded free resolution of S/J globalises to a resolution of O_{Z}
by the line bundles O(-sum a_i D_i), D_i = pr_i^{-1}(0), and ch O(-a.D) = prod (1 - a_i theta_i).

The degree of K in each variable is at most m, so a truncation at degree m+1 is exact.

Target (paper, Theorem thm:smoothinvariants): a secant object
I_Z(b Theta) with ch = u + b v needs
    ch_2(O_Z) = N Theta^2,   ch_3(O_Z) = -(2 b N / 3) Theta^3,   chi(O_Z) = 4 N (2 b^2 - N),
with N = (b^2 + d)/2.  On E^4: Theta^2 = 2 sum theta_i theta_j, Theta^3 = 6 sum theta_i theta_j theta_k.
So with m = 2N the requirements are
    coefficient of theta_i theta_j theta_k in ch_3 = -4 b N = -2 b m,
    chi = 4 m b^2 - m^2,
    d = m - b^2 > 0.
"""
from fractions import Fraction
from itertools import product, combinations
import sys

def k_moments(m):
    """Return (mult, c3, chi): multiplicity along each plane, coefficient of
    theta_i theta_j theta_k in ch_3, and chi(O_{Z_m}), all exact integers.
    Also returns the full dictionary of theta_S coefficients for checking symmetry."""
    D = m + 1                       # truncation degree per variable (exact, deg_i K <= m)
    # H truncated: standard monomials a with some pair a_i + a_j <= m-1
    rng = range(D + 2)              # a little slack for the multiplication by (1 - z_i)
    H = {}
    for a in product(rng, repeat=4):
        if any(a[i] + a[j] <= m - 1 for i, j in combinations(range(4), 2)):
            H[a] = 1
    # multiply by prod (1 - z_i)
    K = dict(H)
    for i in range(4):
        newK = {}
        for a, c in K.items():
            newK[a] = newK.get(a, 0) + c
            b = list(a); b[i] += 1; b = tuple(b)
            newK[b] = newK.get(b, 0) - c
        K = newK
    # keep only exact region: all exponents <= D (the slack region is garbage)
    K = {a: c for a, c in K.items() if c != 0 and max(a) <= D}
    # sanity: no term of degree > m in any variable should survive
    bad = [a for a in K if max(a) > m]
    if bad:
        raise RuntimeError(f"truncation not exact at m={m}: {bad[:5]}")
    # ch = sum_a K_a prod_i (1 - a_i theta_i);  coefficient of theta_S = (-1)^|S| sum_a K_a prod_{i in S} a_i
    coeff = {}
    for S in [()] + [s for r in (1, 2, 3, 4) for s in combinations(range(4), r)]:
        tot = 0
        for a, c in K.items():
            p = 1
            for i in S:
                p *= a[i]
            tot += c * p
        coeff[S] = (-1) ** len(S) * tot
    # symmetry checks
    c0 = coeff[()]
    c1 = {coeff[(i,)] for i in range(4)}
    c2 = {coeff[S] for S in combinations(range(4), 2)}
    c3 = {coeff[S] for S in combinations(range(4), 3)}
    assert c0 == 0 and c1 == {0}, (c0, c1)          # codimension two: ch_0 = ch_1 = 0
    assert len(c2) == 1 and len(c3) == 1, (c2, c3)  # S_4 symmetry
    return c2.pop(), c3.pop(), coeff[(0, 1, 2, 3)]

def squarefree(n):
    if n <= 0: return False
    p = 2
    while p * p <= n:
        if n % (p * p) == 0: return False
        p += 1
    return True

if __name__ == "__main__":
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    print(f"{'m':>3} {'2N':>5} {'c3':>8} {'chi':>8} | {'b=-c3/4N':>10} {'chi_req':>8} {'d=2N-b^2':>8}  verdict")
    for m in range(1, mmax + 1):
        mult, c3, chi = k_moments(m)
        assert mult == m * (m + 1) // 2, (m, mult)   # length of C[x,y]/(x,y)^m
        N2 = mult                                     # 2N = multiplicity along each plane
        b = Fraction(-c3, 2 * N2)                     # c3 = -4 b N = -2 b (2N)
        verdict = ""
        if b.denominator == 1 and b > 0:
            b = int(b)
            N = Fraction(N2, 2)
            chi_req = 4 * N * (2 * b * b - N)
            d = N2 - b * b
            ok = (chi == chi_req) and d > 0
            verdict = ("MATCH" if ok else "no") + (f"  (d={d}, squarefree={squarefree(d)})" if ok else "")
            print(f"{m:>3} {mult:>5} {c3:>8} {chi:>8} | {b:>10} {str(chi_req):>8} {d:>8}  {verdict}")
        else:
            print(f"{m:>3} {mult:>5} {c3:>8} {chi:>8} | {str(b):>10} {'-':>8} {'-':>8}  b not a positive integer")
