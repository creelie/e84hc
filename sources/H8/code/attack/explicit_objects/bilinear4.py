import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial
from ext import *
from orlov import secant, dual, orlov_ch_fast
from split import Split
n = 4
allok = True
for d in [5, 6, 7, 10, 11, 13, 14, 15, 17, 19]:
    S = Split(n, d); B = eexp(escale(Fr(1, 2), S.ell()), 4 * n); ok = True
    for p in [(1, 0), (0, 1)]:
        for q in [(1, 0), (0, 1)]:
            g = orlov_ch_fast(n, secant(n, d, *p), dual(secant(n, d, *q)))
            cc = S.corrected_coords(wedge(g, B))
            if cc is None: ok = False; continue
            mu = [factorial(m) * cc[0][m] for m in range(2 * n + 1)]
            ok = ok and all(mu[m + 2] == -mu[m] / (4 * d) for m in range(2 * n - 1))
    print("n=4 d=%d: flat + rho<=2 for all secant pairs: %s" % (d, ok)); allok = allok and ok
print("ALL", allok)
