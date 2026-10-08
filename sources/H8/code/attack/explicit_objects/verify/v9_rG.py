"""v9_rG.py -- r(ch G), G = F1 [x] F2^vee on X x X (no Orlov transform), secant F_i:
expected 18 (n=2), 6n^2-2n (n>=3), for every d (thm:factor(iv) of the paper)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from ea import *
from model import Model
from orl import secant, dualch
t0 = time.time()
for n, ds in [(2, [1, 7, 13]), (3, [1, 7, 13]), (4, [1, 5, 7])]:
    for d in ds:
        M = Model(n, d)
        res = []
        for p, q in [((0, 1), (0, 1)), ((1, 0), (0, 1)), ((2, 3), (1, -1))]:
            c1 = secant(n, d, *p)
            c2 = dualch(secant(n, d, *q))
            c2s = linsub(c2, {i: g(2 * n + i) for i in range(2 * n)})   # second factor
            G = mul(c1, c2s)
            res.append(M.r(G))
        print("n=%d d=%d: r(ch G) for 3 pairs = %s (expected %d)  (%.1fs)" % (n, d, res, 18 if n == 2 else 6 * n * n - 2 * n, time.time() - t0), flush=True)
