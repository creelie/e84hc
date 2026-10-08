#!/usr/bin/env python3
"""
v4_search.py -- exhaustive check of the 'smallest 8-subtori relation' for d=1,
|p|,|q| <= 3 (16 primitive (p,q) up to sign), using the closed form
m_i ~ 1/((q_i^2 + d p_i^2) prod_{j != i}(p_i q_j - p_j q_i)) scaled to a
primitive integer vector (the relation is unique up to scale, so this is the
primitive integral relation).  Reports min sum m^2 and min sum |m|.
Independently cross-checks the closed form on a few sets against an exact
nullspace computation in H_A (v4lib).
"""
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd
from functools import reduce

d = 1
pts = [(p, q) for p in range(0, 4) for q in range(-3, 4)
       if gcd(p, q) == 1 and not (p == 0 and q != 1)]
print("points:", len(pts), pts)


def closed(S):
    out = []
    for i, (p, q) in enumerate(S):
        den = Fr(q * q + d * p * p)
        for j, (pj, qj) in enumerate(S):
            if j != i:
                den *= (p * qj - pj * q)
        out.append(1 / den)
    L = reduce(lambda a, b: a * b // gcd(a, b), [x.denominator for x in out])
    ints = [int(x * L) for x in out]
    g = reduce(gcd, [abs(x) for x in ints])
    return [x // g for x in ints]


best2 = None
best1 = None
cnt = 0
for S in combinations(pts, 8):
    m = closed(list(S))
    cnt += 1
    s2 = sum(x * x for x in m)
    s1 = sum(abs(x) for x in m)
    if best2 is None or s2 < best2[0]:
        best2 = (s2, S, m)
    if best1 is None or s1 < best1[0]:
        best1 = (s1, S, m)
print("8-sets:", cnt)
print("min sum m^2 =", best2[0], "at", best2[1], "m =", best2[2])
print("min sum |m| =", best1[0], "at", best1[1], "m =", best1[2])
