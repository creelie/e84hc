import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial
from ext import *
from orlov import secant, dual, orlov_ch_fast
from split import Split
n = 4
for d, v1, v2 in [(1, (0,1), (0,1)), (1, (1,0), (0,1)), (2, (1,1), (1,0))]:
    t0 = time.time()
    S = Split(n, d)
    g = orlov_ch_fast(n, secant(n, d, *v1), dual(secant(n, d, *v2)))
    print("d=%d v1=%s v2=%s: ch(E) has %d terms, rank %s (%.1fs)" % (d, v1, v2, len(g), g.get(0,0), time.time()-t0), flush=True)
    B = eexp(escale(Fr(1, 2), S.ell()), 4 * n)
    kb = wedge(g, B)
    cc = S.corrected_coords(kb)
    print("   ch.e^{ell/2} flat:", cc is not None, " weil:", (cc[1], cc[2]) if cc else None, "(%.1fs)" % (time.time()-t0), flush=True)
    if cc:
        c = cc[0]; print("   mu =", [str(factorial(k)*c[k]) for k in range(2*n+1)])
    r = S.r_of(g)
    print("   r(ch E) =", r, " (6n^2-2n =", 6*n*n-2*n, ")  (%.1fs)" % (time.time()-t0), flush=True)
