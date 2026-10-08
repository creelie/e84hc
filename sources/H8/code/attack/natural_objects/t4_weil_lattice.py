#!/usr/bin/env python3
"""
t4_weil_lattice.py d H -- the Weil classes sum m_i [B_(p_i,q_i)] (m_i integers,
8 distinct primitive (p:q), |p|,|q| <= H) written as x W1 + y W2 (W1, W2 of
ext.Split.weil_pair), and the Z-span of all (x, y) found; compared with the
integral classes W1/24, W2/24 (Re, Im of the integral polynomial P(1,-delta)).
Uses exact linear algebra in the 9-dim span of the C_k.
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd
from ext import *
d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
H = int(sys.argv[2]) if len(sys.argv) > 2 else 3
S = Split(4, d)
W1, W2 = S.weil_pair()
pts = []
for p in range(0, H + 1):
    for q in range(-H, H + 1):
        if gcd(p, q) != 1 or (p == 0 and q != 1):
            continue
        pts.append((p, q))
cls = {pq: S.subtorus(*pq) for pq in pts}
# coordinates: choose a basis of span{C_k} -- use the classes of 9 fixed subtori
E = Echelon()
basis = []
for pq in pts:
    if E.add(cls[pq]):
        basis.append(pq)
    if E.rank() == 9:
        break
# express everything in terms of the basis via a fixed linear solve
import itertools
def coords(v):
    # solve v = sum c_j cls[basis_j]
    keys = sorted(set().union(*[set(cls[b]) for b in basis]) | set(v))
    rows = [[Fr(cls[b].get(k, 0)) for b in basis] + [Fr(v.get(k, 0))] for k in keys]
    m = len(basis)
    r = 0
    piv = []
    for c in range(m):
        pr = next(i for i in range(r, len(rows)) if rows[i][c] != 0)
        rows[r], rows[pr] = rows[pr], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    assert all(rows[i][m] == 0 for i in range(r, len(rows)))
    return [rows[i][m] for i in range(m)]
cW1, cW2 = coords(W1), coords(W2)
cB = {pq: coords(cls[pq]) for pq in pts}
def mults(Sset):
    lam = []
    for i, (pi, qi) in enumerate(Sset):
        pr = Fr(1)
        for j, (pj, qj) in enumerate(Sset):
            if j != i:
                pr *= (pi * qj - pj * qi)
        pr *= (qi * qi + d * pi * pi)
        lam.append(1 / pr)
    den = 1
    for x in lam:
        den = den * x.denominator // gcd(den, x.denominator)
    m = [int(x * den) for x in lam]
    g = 0
    for x in m:
        g = gcd(g, x)
    return [x // g for x in m]
vecs = set()
for Sset in combinations(pts, 8):
    m = mults(list(Sset))
    tot = [sum(mi * cB[pq][j] for mi, pq in zip(m, Sset)) for j in range(9)]
    # tot = x cW1 + y cW2
    # solve using two coordinates
    A = [[cW1[j], cW2[j]] for j in range(9)]
    # least: pick independent rows
    for (j1, j2) in combinations(range(9), 2):
        det = A[j1][0] * A[j2][1] - A[j1][1] * A[j2][0]
        if det != 0:
            x = (tot[j1] * A[j2][1] - A[j1][1] * tot[j2]) / det
            y = (A[j1][0] * tot[j2] - tot[j1] * A[j2][0]) / det
            break
    assert all(tot[j] == x * cW1[j] + y * cW2[j] for j in range(9))
    vecs.add((x, y))
# Z-span of vecs in Q^2 via HNF on scaled integers
den = 1
for (x, y) in vecs:
    for z in (x, y):
        den = den * z.denominator // gcd(den, z.denominator)
iv = [(int(x * den), int(y * den)) for (x, y) in vecs]
# 2D lattice basis by repeated gcd (HNF)
def hnf2(vs):
    a = [0, 0]; b = [0, 0]
    # compute lattice generated: use extended gcd on first coords
    import math
    g = 0
    for v in vs:
        g = math.gcd(g, v[0])
    # elements with x = 0 form the y-lattice after reduction
    # simple approach: row-reduce a list
    L = [list(v) for v in vs if v != (0, 0)]
    while True:
        L = [v for v in L if v != [0, 0]]
        nz = [v for v in L if v[0] != 0]
        if len(nz) <= 1:
            break
        nz.sort(key=lambda v: abs(v[0]))
        p = nz[0]
        for v in L:
            if v is not p and v[0] != 0:
                q = v[0] // p[0]
                v[0] -= q * p[0]; v[1] -= q * p[1]
    first = [v for v in L if v[0] != 0]
    rest = [v for v in L if v[0] == 0]
    gy = 0
    for v in rest:
        gy = math.gcd(gy, v[1])
    if first:
        f = first[0]
        if gy:
            f[1] %= gy
        return f, [0, gy]
    return None, [0, gy]
f, s = hnf2(iv)
print("d=%d H=%d: %d distinct Weil vectors from %d points" % (d, H, len(vecs), len(pts)))
print("Z-span of realised (x,y) (x W1 + y W2) has basis", [Fr(z, den) for z in f] if f else None,
      [Fr(z, den) for z in s])
print("reference: W1/24 and W2/24 are integral classes (Re, Im of the integral P(1,-delta))")
