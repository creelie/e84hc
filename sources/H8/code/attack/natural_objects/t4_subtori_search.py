#!/usr/bin/env python3
"""
t4_subtori_search.py d H -- over all 8-sets of primitive (p:q) with |p|,|q| <= H,
the integer multiplicities m_i (coprime) of the unique relation
   sum_i m_i [B_(p_i,q_i)] in W,
from the closed form m_i ~ 1 / ( prod_{j != i} (p_i q_j - p_j q_i) * (q_i^2 + d p_i^2) )
(the divided-difference identity for binary octics at the 8 points and the
conjugate pair (1 : -+delta)); the minimum of sum m_i^2 and of sum |m_i|.
The closed form is checked against the exact linear algebra of t4_example.py
for the set used there.
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd
d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
H = int(sys.argv[2]) if len(sys.argv) > 2 else 2
pts = []
for p in range(0, H + 1):
    for q in range(-H, H + 1):
        if gcd(p, q) != 1:
            continue
        if p == 0 and q != 1:
            continue
        pts.append((p, q))
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
ref = [(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1), (1, -2), (2, -1)]
print("closed form on the set of t4_example.py:", mults(ref))
best2 = best1 = None
for S in combinations(pts, 8):
    m = mults(list(S))
    s2 = sum(x * x for x in m)
    s1 = sum(abs(x) for x in m)
    if best2 is None or s2 < best2[0]:
        best2 = (s2, S, m)
    if best1 is None or s1 < best1[0]:
        best1 = (s1, S, m)
print("d=%d, H=%d, %d points, %d 8-sets" % (d, H, len(pts), sum(1 for _ in combinations(pts, 8))))
print("min sum m^2 = %d at %s, m = %s" % best2)
print("min sum |m| = %d at %s, m = %s" % best1)
