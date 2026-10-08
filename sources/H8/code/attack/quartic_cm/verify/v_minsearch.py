#!/usr/bin/env python3
"""v_minsearch.py -- exploratory (exact over Q): how small can r(omega + p(theta_0,theta_1)) be?
Not a proof of any minimum; only records exact ranks at exact rational points."""
import random, itertools
from fractions import Fraction as Fr
from v_ann import gamma_of, rank, THP
from math import factorial

rng = random.Random(7)
mons = sorted(THP)
cs = [Fr(2), Fr(-3), Fr(5), Fr(7, 2)]
hist = {}
def rec(r, tag):
    hist.setdefault(r, []).append(tag)

# random sparse supports
for trial in range(1500):
    k = rng.choice([1, 2, 3, 4, 6, 10])
    S = rng.sample(mons, k)
    poly = {m: Fr(rng.choice([-1, 1]) * rng.randint(1, 6), rng.randint(1, 3)) for m in S}
    rec(rank(gamma_of(cs, poly)), ("sparse", tuple(sorted(poly.items()))))
# exponential-type shapes N*omega + sum_i r_i e^{a_i th0 + b_i th1}
def expo(r0, a, b):
    return {(i, j): Fr(r0) * Fr(a) ** i * Fr(b) ** j / (factorial(i) * factorial(j)) for i in range(5) for j in range(5)}
for trial in range(300):
    poly = {}
    for _ in range(rng.randint(1, 3)):
        e = expo(rng.randint(-4, 4), Fr(rng.randint(-3, 3), rng.randint(1, 3)), Fr(rng.randint(-3, 3), rng.randint(1, 3)))
        for m, v in e.items():
            poly[m] = poly.get(m, 0) + v
    rec(rank(gamma_of(cs, poly)), ("expo",))
for r in sorted(hist):
    print(r, len(hist[r]), hist[r][0] if hist[r][0][0] == "sparse" else "")
print("minimum found:", min(hist))
