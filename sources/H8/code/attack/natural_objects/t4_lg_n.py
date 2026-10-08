#!/usr/bin/env python3
"""
t4_lg_n.py n d -- the Veronese model of H_A for general n (n = 2, 3, 4):
H_A = Sp(U)-invariants of wedge^*(U (x) Q^2), dim = (n+1)(n+2)(2n+3)/6, and
ch(F) = Phi_n(P(L_F)^n) for natural F.  The fit uses line bundles e^{D_S} on
the FULL grid S11,S12,S22 in {0..2n} (a unisolvent set for polynomials of
degree <= 2n in each variable, so the identity e^{D_S} = Phi_n(P(L_S)^n) is
proved for all rational S once the graph has rank dim H_A); subtori and
twisted subtori are tested on a grid in (p,q) as well.
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations_with_replacement, product
from ext import *
from lg import pl_from_rows, L_S, L_sub, L_point, twist_rows

n = int(sys.argv[1]); d = int(sys.argv[2])
S = Split(n, d)
b, bh, l = S.beta(), S.betahat(), S.ell()
MONO = list(combinations_with_replacement(range(5), n))
def mono(Pv):
    out = {}
    for idx, m in enumerate(MONO):
        v = 1
        for i in m:
            v = v * Pv[i]
        if v != 0:
            out[idx] = v
    return out
def ch_lb(a, c, e):
    return exp_class(add(add(scale(b, a), scale(bh, e)), scale(l, -c)), 4 * n)
def combined(Pv, ch):
    v = {(0, k): Fr(c) for k, c in mono(Pv).items()}
    for k, c in ch.items():
        v[(1, k)] = -Fr(c)
    return v
dimHA = (n + 1) * (n + 2) * (2 * n + 3) // 6
E = Echelon()
grid = list(product(range(0, 2 * n + 1), repeat=3))
for (a, c, e) in grid:
    E.add(combined(L_S(a, c, e), ch_lb(a, c, e)))
print("n=%d d=%d: graph rank on the full grid (%d line bundles) = %d, dim H_A = %d"
      % (n, d, len(grid), E.rank(), dimHA))
ok = True
for p in range(-n, n + 1):
    for q in range(0, n + 2):
        from math import gcd
        if gcd(p, q) != 1:
            continue
        Bpq = S.subtorus(p, q)
        if E.reduce(combined(L_sub(p, q), Bpq)) and E.reduce(combined(L_sub(p, q), scale(Bpq, -1))):
            ok = False
        for (s11, s12, s22) in [(1, 0, 0), (0, 1, 1), (2, -1, 1)]:
            rows = twist_rows([(q, p, 0, 0), (0, 0, p, -q)], s11, s12, s22)
            chB = wedge(Bpq, ch_lb(s11, s12, s22))
            if E.reduce(combined(pl_from_rows(*rows), chB)) and E.reduce(combined(pl_from_rows(*rows), scale(chB, -1))):
                ok = False
ok = ok and not E.reduce(combined(L_point(), S.point()))
print("   subtori, twisted subtori, point consistent with the same Phi_n (up to sign, P -> -P):", ok)
