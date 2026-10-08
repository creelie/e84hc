import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial, comb
from ext import *
from orlov import secant, dual, beta_X, orlov_ch_fast
from xrank import rk_profile
from split import Split

def chi_X(n, v):
    top = (1 << (2*n)) - 1
    vol = escale(Fr(1, factorial(n)), epow(beta_X(n), n))
    x = wedge(dual(v), v)
    return x.get(top, 0) / vol[top]

print("Euler characteristic chi(F,F) = int ch^vee ch of secant classes a u_t + b v_t:")
for n in [2, 3, 4, 5, 6]:
    for d in [1, 2, 3]:
        row = []
        for (a, b) in [(1, 0), (0, 1), (1, 1), (2, 1)]:
            v = secant(n, d, a, b)
            c = chi_X(n, v)
            pred = 0 if n % 2 else 2**(n-1) * (-1)**(n//2) * d**(n//2 - 1) * Fr(a*a*d + b*b)
            row.append("%s%s" % (c, "" if c == pred else "(!=%s)" % pred))
        print("  n=%d d=%d:" % (n, d), row)
print()
print("full Hochschild profile r^k_X(v), k = 0..2n, for v = u_t (d=1) and minimal-profile Euler char:")
for n in [2, 3, 4, 5]:
    t0 = time.time()
    p = rk_profile(n, secant(n, 1, 1, 0), 2 * n)
    chi_min = sum((-1)**k * p[k] for k in range(n + 1))
    print("  n=%d  %s   sum_{k<=n} (-1)^k r^k = %d  (%.1fs)" % (n, p, chi_min, time.time()-t0))
