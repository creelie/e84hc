import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from split import Split
from orlov import *
from ext import *
n = 3
for d in [1, 2]:
    S = Split(n, d)
    for (v1, v2) in [((1,0),(1,0)), ((0,1),(0,1)), ((1,1),(1,1)), ((1,0),(0,1)), ((1,0),(1,1))]:
        t0 = time.time()
        g = orlov_ch_fast(n, secant(n,d,*v1), dual(secant(n,d,*v2)))
        rk = g.get(0, 0)
        if rk == 0:
            print(d, v1, v2, "rank 0; c1 =", degree_part(g,2) != {})
            c1 = degree_part(g, 2)
            cc = S.corrected_coords(g)
            print("   ch itself corrected?", cc is not None)
            continue
        c1 = degree_part(g, 2)
        co = [c / rk for c in solve_in_span(c1, [S.beta(), S.betahat(), S.ell()])]
        kappa = wedge(g, eexp(escale(Fr(-1)/rk, c1), 4*n))
        cc = S.corrected_coords(kappa)
        r = S.r_of(g)
        print("d=%d v1=%s v2=%s rk=%s c1/rk=%s kappa_flat=%s weil=%s r=%d  (%.1fs)" % (
            d, v1, v2, rk, co, cc is not None, (cc[1], cc[2]) if cc else None, r, time.time()-t0))
        if cc:
            c = cc[0]
            mu = [factorial(k) * c[k] for k in range(2*n+1)]
            print("     c_k =", c, " mu =", mu)
