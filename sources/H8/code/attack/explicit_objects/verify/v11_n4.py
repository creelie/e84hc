"""v11_n4.py -- validate orlov_fast vs orlov (n=2,3), then n=4 flatness of ch(E)e^{ell/2} for extra d."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import factorial
from ea import *
from model import Model
from orl import secant, dualch, orlov
from orl_fast import orlov_fast
t0 = time.time()
for n, d in [(2, 3), (3, 2)]:
    ok = all(orlov(n, secant(n, d, *p), dualch(secant(n, d, *q))) == orlov_fast(n, secant(n, d, *p), dualch(secant(n, d, *q)))
             for p in [(1, 0), (0, 1), (2, -1)] for q in [(1, 0), (0, 1)])
    print("orlov_fast == orlov at n=%d d=%d: %s" % (n, d, ok), flush=True)
n = 4
for d in [int(x) for x in (sys.argv[1].split(",") if len(sys.argv) > 1 else ["1", "7", "21"])]:
    M = Model(n, d)
    e = M.eta(); re, im = M.weil_pm()
    basis = [power(e, k) for k in range(2 * n + 1)] + [re, im]
    eh = expo(sc(F(1, 2), M.ell()))
    good = True
    for p in [(1, 0), (0, 1)]:
        for q in [(1, 0), (0, 1)]:
            ch = orlov_fast(n, secant(n, d, *p), dualch(secant(n, d, *q)))
            x = solve(mul(ch, eh), basis)
            x0 = solve(ch, basis)
            if x is None or x0 is not None:
                good = False; continue
            mu = [factorial(k) * x[k] for k in range(2 * n + 1)]
            good &= all(mu[k + 2] == -mu[k] / (4 * d) for k in range(2 * n - 1))
    print("n=4 d=%d: four basis pairs: ch(E) not flat, ch(E)e^{ell/2} flat, mu_{m+2}=-mu_m/(4d): %s  (%.1fs)" % (d, good, time.time() - t0), flush=True)
