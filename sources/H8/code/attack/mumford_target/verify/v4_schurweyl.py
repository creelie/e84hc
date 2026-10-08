#!/usr/bin/env python3
"""
v4_schurweyl.py  (round 12, adversarial verification of track T2, Theorem A steps 2-4)

Exact checks (Fractions):
 (a) Casimir identity for sl2 with the trace form: E(x)F + F(x)E + H(x)H/2 = P - I/2.
 (b) dim of the image of Q[S_3] in End((Q^2)^{(x)3}) = 5, and of Q[S_2] in
     End((Q^2)^{(x)2}) = 2; so End_G(V^{(x)3}) has dim 5^3 = 125 and End_G(V (x) V)
     dim 2^3 = 8 (commutant of a product group = tensor product of commutants,
     Schur-Weyl for each SL2).
 (c) dim (Q^2)^{(x)6} SL2-invariants = 5 (Catalan), so dim (V^{(x)6})^G = 125, and the
     S_6-orbit of eps^{(x)3} spans them (transitivity on perfect matchings).
 (d) The rational combinations sum_k sigma_k(a_j) s_k, a_j a Q-basis of a totally
     real cubic field (here F = Q(zeta_7 + zeta_7^{-1}), as a test), have the same
     Q-bar span as s_1, s_2, s_3: det(sigma_k(a_j)) != 0 (discriminant check, exact).
"""
import sys
from fractions import Fraction as Fr
from itertools import permutations, product

PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("PASS " if cond else "FAIL ") + name)


def kron(A, B):
    n, m = len(A), len(B)
    return [[A[i // m][j // m] * B[i % m][j % m] for j in range(n * m)] for i in range(n * m)]


def add(A, B, c=1):
    return [[a + c * b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


E = [[0, 1], [0, 0]]; F = [[0, 0], [1, 0]]; H = [[1, 0], [0, -1]]; I2 = [[1, 0], [0, 1]]
P = [[0] * 4 for _ in range(4)]
for a in range(2):
    for b in range(2):
        P[2 * a + b][2 * b + a] = 1
cas = add(add(kron(E, F), kron(F, E)), [[Fr(x, 2) for x in r] for r in kron(H, H)])
I4 = kron(I2, I2)
check("(a) E(x)F + F(x)E + H(x)H/2 = P - I/2", cas == add(P, [[Fr(x, 2) for x in r] for r in I4], -1))


def rank(rows):
    rows = [[Fr(x) for x in r] for r in rows]
    r = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def perm_matrix(p, N):
    n = 2 ** N
    M = [[0] * n for _ in range(n)]
    for idx in range(n):
        bits = [(idx >> (N - 1 - t)) & 1 for t in range(N)]
        nb = [0] * N
        for t in range(N):
            nb[p[t]] = bits[t]
        j = int("".join(map(str, nb)), 2)
        M[j][idx] = 1
    return M


for N, expect in [(2, 2), (3, 5), (4, 14)]:
    mats = [sum(perm_matrix(p, N), []) for p in permutations(range(N))]
    r = rank(mats)
    print(f"(b) dim image of Q[S_{N}] on (Q^2)^(x){N}: {r}")
    check(f"(b) = {expect}", r == expect)
print("    => dim End_G(V(x)V) = 2^3 = 8, dim End_G(V^(x)3) = 5^3 = 125")

# (c) invariants of SL2 on (Q^2)^{(x)6}: kernel of E and zero weight; and span of S_6-orbit of eps^{(x)3}
N = 6
zero = [idx for idx in range(2 ** N) if bin(idx).count("1") == 3]
eqs = {}
for idx in zero:
    bits = [(idx >> (N - 1 - t)) & 1 for t in range(N)]
    for t in range(N):
        if bits[t] == 1:
            nb = bits[:]; nb[t] = 0
            j = int("".join(map(str, nb)), 2)
            eqs.setdefault(j, {})[idx] = 1
M = [[eqs[j].get(i, 0) for i in zero] for j in eqs]
dim_inv = len(zero) - rank(M)
check("(c) dim (Q^2)^{(x)6} SL2-invariants = 5", dim_inv == 5)
eps = {(0, 1): 1, (1, 0): -1}
def eps3():
    v = [0] * 64
    for idx in range(64):
        bits = [(idx >> (5 - t)) & 1 for t in range(6)]
        c = 1
        for a in (0, 2, 4):
            c *= eps.get((bits[a], bits[a + 1]), 0)
        v[idx] = c
    return v
e3 = eps3()
orbit = []
for p in permutations(range(6)):
    Pm = perm_matrix(p, 6)
    orbit.append([sum(Pm[i][j] * e3[j] for j in range(64)) for i in range(64)])
check("(c) the S_6-orbit of eps^(x)3 spans the 5-dim invariant space", rank(orbit) == 5)

# (d) F = Q(c), c = 2cos(2pi/7), min poly x^3 + x^2 - 2x - 1; basis 1, c, c^2.
# det(sigma_k(c^j))^2 = disc(x^3+x^2-2x-1) = 49 != 0 (exact via the discriminant formula)
a, b, cc, d = 1, 1, -2, -1
disc = b * b * cc * cc - 4 * a * cc ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * cc * d
print("(d) disc of x^3+x^2-2x-1:", disc)
check("(d) Vandermonde det(sigma_k(a_j)) is nonzero (disc = 49)", disc == 49)

print(f"\n{len(PASS)} checks passed, {len(FAIL)} failed")
sys.exit(1 if FAIL else 0)
