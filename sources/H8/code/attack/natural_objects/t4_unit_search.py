#!/usr/bin/env python3
"""search for 8 subtori B_(p,q) whose Weil relation has all |m_i| equal (d=1),
among unions of two orbits of the symmetry group of p^2+q^2 on P^1, and among
all 8-sets with |p|,|q| <= H (H small)."""
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd
d = 1
def mults(S):
    lam = []
    for i, (pi, qi) in enumerate(S):
        pr = Fr(1)
        for j, (pj, qj) in enumerate(S):
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
def orbit(r, s):
    return [(s, r), (s, -r), (r, s), (r, -s)]
found = []
H = 12
cands = [(r, s) for r in range(1, H + 1) for s in range(1, H + 1) if gcd(r, s) == 1 and r < s]
for (a, b) in combinations(cands, 2):
    S = orbit(*a) + orbit(*b)
    if len(set(S)) < 8:
        continue
    m = mults(S)
    if len(set(abs(x) for x in m)) == 1:
        found.append((S, m))
print("two-orbit configurations with all |m_i| = 1 (H=%d):" % H, len(found))
for S, m in found[:10]:
    print("  ", S, m)
# also orbits including (0,1),(1,0),(1,1),(1,-1)
special = [[(0, 1), (1, 0)], [(1, 1), (1, -1)]]
for sp in special:
    for a in cands:
        for rest in [orbit(*a)]:
            pass
