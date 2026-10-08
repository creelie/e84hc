import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import gcd
from itertools import combinations
from split import Split
from subvar import Zclass
from ext import *
for n, d in [(2, 1), (2, 2), (3, 1)]:
    S = Split(n, d)
    w1, w2 = S.weil()
    small = [(0,1),(1,0),(1,1),(1,-1),(1,2),(2,1),(1,-2),(2,-1),(1,3),(3,1),(1,-3),(3,-1)]
    best = None
    for k in (2*n, 2*n+1):
        for sub in combinations(small, k):
            x = solve_in_span(w1, [Zclass(S, p, q) for (p, q) in sub])
            if x is None: continue
            if any(c.denominator != 1 for c in x):
                continue
            tot = sum(abs(c) for c in x)
            if best is None or tot < best[0]:
                best = (tot, sub, x)
    print("n=%d d=%d: w1 = sum m_i [Z_{p:q}] with integer m_i, smallest sum|m_i| found = %s:" % (n, d, best[0] if best else None))
    if best:
        print("   ", ", ".join("%s*[Z_%d:%d]" % (c, p, q) for c, (p, q) in zip(best[2], best[1])))
