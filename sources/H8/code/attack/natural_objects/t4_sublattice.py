#!/usr/bin/env python3
"""
t4_sublattice.py d H -- Lambda_sub = Z-span of the classes [B_(p,q)] (primitive,
|p|,|q| <= H), in the coordinates of the integral classes C_0..C_8 with
[B_(p,q)] = sum_k p^k q^(8-k) C_k (t4_basic.py (B4)); its intersection with the
Weil plane, spanned in these coordinates by
   w1 = Re P(1,-delta) = W1/24,  w2 = Im P(1,-delta)/delta = W2/24.
Exact integer HNF (python-flint).  Also: index of Lambda_sub in Z^9.
"""
import sys
from math import gcd
import flint
d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
H = int(sys.argv[2]) if len(sys.argv) > 2 else 6
vecs = []
for p in range(0, H + 1):
    for q in range(-H, H + 1):
        if gcd(p, q) != 1 or (p == 0 and q != 1):
            continue
        vecs.append([p ** k * q ** (8 - k) for k in range(9)])
M = flint.fmpz_mat(vecs)
Hn = M.hnf()
rows = [[int(Hn[i, j]) for j in range(9)] for i in range(Hn.nrows()) if any(Hn[i, j] != 0 for j in range(9))]
det = 1
for i, r in enumerate(rows):
    det *= r[i]
print("d=%d H=%d: %d subtori; Lambda_sub has rank %d and index %d in Z^9 (C_k-coordinates)"
      % (d, H, len(vecs), len(rows), abs(det)))
# Weil vectors: P(1,t) = sum_k C_k t^(8-k); at t = -delta: t^m, m = 8-k
w1 = [0] * 9; w2 = [0] * 9
for k in range(9):
    m = 8 - k
    c = (-1) ** m * (-d) ** (m // 2)
    if m % 2 == 0:
        w1[k] = c
    else:
        w2[k] = c
print("w1 =", w1, " w2 =", w2)
# Lambda_sub cap span(w1, w2): solve x w1 + y w2 = sum a_i rows_i with a integral.
# Since rows is a basis (upper triangular), coordinates a = (x w1 + y w2) B^{-1};
# the set of (x,y) in Q^2 with integral a is a lattice: compute via B^{-1}.
B = flint.fmpq_mat(rows)
Binv = B.inv()
import fractions
a1 = [fractions.Fraction(int((flint.fmpq_mat([w1]) * Binv)[0, j].p), int((flint.fmpq_mat([w1]) * Binv)[0, j].q)) for j in range(9)]
a2 = [fractions.Fraction(int((flint.fmpq_mat([w2]) * Binv)[0, j].p), int((flint.fmpq_mat([w2]) * Binv)[0, j].q)) for j in range(9)]
# lattice {(x,y): x a1 + y a2 in Z^9} = dual of the Z-span of the column pairs (a1_j, a2_j)
den = 1
for z in a1 + a2:
    den = den * z.denominator // gcd(den, z.denominator)
cols = [[int(a1[j] * den), int(a2[j] * den)] for j in range(9)] + [[den, 0], [0, den]]
C = flint.fmpz_mat(cols).hnf()
G = [[int(C[i, j]) for j in range(2)] for i in range(2)]   # basis of Z-span of columns (times den)
# dual lattice: {v : G v^T in den Z} ... v = (x,y) with (x,y).col in Z for all cols/den
# columns/den generate lattice Lc with basis G/den; dual basis = (G/den)^{-T}
F_ = fractions.Fraction
g = [[F_(G[i][j], den) for j in range(2)] for i in range(2)]
dt = g[0][0] * g[1][1] - g[0][1] * g[1][0]
inv = [[g[1][1] / dt, -g[0][1] / dt], [-g[1][0] / dt, g[0][0] / dt]]
D = [[inv[j][i] for j in range(2)] for i in range(2)]   # inverse transpose
print("Lambda_sub cap W = Z-span of x w1 + y w2 for (x,y) in", [[str(z) for z in r] for r in D])
print("   i.e. in terms of W1 = 24 w1, W2 = 24 w2:", [[str(z / 24) for z in r] for r in D])
