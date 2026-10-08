import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from split import Split
from orlov import *
from ext import *
n = 3
for d in [1, 2, 6]:
    S = Split(n, d)
    for (v1, v2) in [((0,1),(0,1)), ((1,0),(1,0)), ((1,1),(1,1)), ((1,0),(0,1))]:
        g = orlov_ch_fast(n, secant(n,d,*v1), dual(secant(n,d,*v2)))
        B = eexp(escale(Fr(1,2), S.ell()), 4*n)
        kb = wedge(g, B)
        cc = S.corrected_coords(kb)
        r = S.r_of(g)
        print("d=%d v1=%s v2=%s rk=%s  ch.e^{ell/2} flat=%s weil=%s  r(ch)=%d" % (
            d, v1, v2, g.get(0,0), cc is not None, (cc[1],cc[2]) if cc else None, r))
        if cc:
            c = cc[0]; mu = [factorial(k)*c[k] for k in range(2*n+1)]
            print("     mu =", [str(x) for x in mu])
