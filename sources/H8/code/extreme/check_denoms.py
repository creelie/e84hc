#!/usr/bin/env python3
"""Replays the random members used in parts F (weil_tori_ext.py) and B
(weil_tori_B.py) and checks that no denominator of any scalar entering the
reduction mod q is divisible by q, so that reduction is a ring homomorphism
Z_(q)[delta] -> F_q and ranks can only drop."""
import os, random, sys
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wt_engine as E

def ok_member(M, q):
    worst = 1
    for col in M.Phi.values():
        for x in col.values():
            for y in x:
                if y.denominator % q == 0:
                    return False, y.denominator
                worst = max(worst, y.denominator)
    for vecs in (M.hol, M.antihol):
        for v in vecs:
            for x in v.values():
                for y in x:
                    if y.denominator % q == 0:
                        return False, y.denominator
    return True, worst

allok = True
# part F
rng = random.Random(20260927)
for n, d, nmem in ((3, 1, 3), (3, 7, 3), (4, 1, 3)):
    KF = E.Kfield(d); q = E.choose_prime(d)
    for _ in range(nmem):
        M = E.random_member(KF, n, rng)
        ok, w = ok_member(M, q); allok &= ok
        print("F n=%d d=%d member ok=%s largest denominator %d" % (n, d, ok, w))
# part B
configs = {"base": [(4, 1, (2, 3, 4, 5, 6), 2, 3), (4, 3, (3, 4, 5), 2, 3), (4, 7, (4,), 2, 3)],
           "balanced": [(4, 1, (3, 5, 4), 2, 1)], "two": [(4, 1, (4,), 2, 2)],
           "n5": [(5, 1, tuple(range(1, 10)), 2, 5), (5, 3, (4, 5, 6), 2, 5)]}
for mode, cfgs in configs.items():
    for n, d, ks, nrand, ndiag in cfgs:
        for k in ks:
            seed = 1000 * n + 10 * d + k
            rng = random.Random(seed)
            allS = list(combinations(range(2 * n), n))
            rng.sample(allS[1:], ndiag - 1)
            KF = E.Kfield(d); q = E.choose_prime(d)
            for _ in range(nrand):
                M = E.random_member(KF, n, rng)
                ok, w = ok_member(M, q); allok &= ok
            print("B %s n=%d d=%d k=%d members ok=%s (last largest denominator %d)" % (mode, n, d, k, ok, w))
print("ALL DENOMINATORS PRIME TO q:", allok)
