#!/usr/bin/env python3
"""v_binomial.py -- exact ranks r(omega + a*m1 + b*m2) for ALL pairs of theta-monomials m1<m2
and coefficient ratios b/a in a fixed set (both signs).  Tests the T1 claim (iii) that
monomial and binomial shapes give r in {80,84,88,104,108,112}."""
import itertools
from fractions import Fraction as Fr
from v_ann import gamma_of, rank, THP
cs = [Fr(2), Fr(3), Fr(5), Fr(7)]   # same omega coefficients as t1_shapes_explore.py
mons = sorted(THP)
ratios = [Fr(1), Fr(-1), Fr(2), Fr(-2), Fr(-5, 4), Fr(1, 3), Fr(-7, 3)]
vals = {}
for m1, m2 in itertools.combinations(mons, 2):
    for t in ratios:
        r = rank(gamma_of(cs, {m1: Fr(1), m2: t}))
        vals.setdefault(r, []).append((m1, m2, str(t)))
for r in sorted(vals):
    print(r, len(vals[r]), vals[r][:6])
