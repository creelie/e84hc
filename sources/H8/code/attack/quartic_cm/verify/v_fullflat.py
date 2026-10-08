#!/usr/bin/env python3
"""v_fullflat.py -- independent: r(gamma) for gamma a random flat Hodge class
sum_S sum_{i,j} c_{S,i,j} vol_S theta_0^i theta_1^j with nonzero Weil part; exact over Q."""
import random, itertools
from fractions import Fraction as Fr
from v_ann import vol, wedge, add, THP, rank
rng = random.Random(99)
subsets = [S for k in range(5) for S in itertools.combinations(range(4), k)]
volS = {}
for S in subsets:
    f = {0: Fr(1)}
    for s in S: f = wedge(f, vol(s))
    volS[S] = f
for trial in range(3):
    g = {}
    for S in subsets:
        for ij, t in THP.items():
            if rng.random() < 0.4 or (len(S) == 1 and ij == (0, 0)):
                prod = wedge(volS[S], t)
                if prod: g = add(g, prod, Fr(rng.randint(-9, 9) or 1, rng.randint(1, 9)))
    print("general flat gamma: r =", rank(g))
