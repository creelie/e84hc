"""scan_n2.py: E = Phi(F1 [x] F2^vee) on X x X^ (n = 2) for secant Mukai vectors
v = (a, b beta, -a d) (ch = a(1 - d pt) + b beta).  For each pair: rank, c1/rk in
(beta, betahat, ell), whether kappa = ch e^{-c1/rk} is flat of corrected form,
r(ch E), the Hochschild profile, and the Kunneth Ext^2 lower bound for simple F_i:
Ext*(F,F) = (1, <v,v>+2, 1)."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from split import Split
from orlov import *
from ext import *
n = 2
one = {0: Fr(1)}
def chv(n, d, a, b):
    return eadd(escale(Fr(a), one), escale(Fr(-a * d), pt_X(n)), escale(Fr(b), beta_X(n)))
for d in [1, 2, 3]:
    S = Split(n, d)
    vs = [(1,0),(0,1),(1,1),(1,-1),(2,1)]
    for i, v1 in enumerate(vs):
        for v2 in vs[i:]:
            g = orlov_ch(n, chv(n,d,*v1), dual(chv(n,d,*v2)))
            rk = g.get(0, 0)
            m1 = 2*v1[1]**2 + 2*d*v1[0]**2; m2 = 2*v2[1]**2 + 2*d*v2[0]**2
            ext2 = 2 + (m1+2)*(m2+2)
            if rk == 0:
                print(d, v1, v2, "rank 0"); continue
            c1 = degree_part(g, 2)
            co = solve_in_span(c1, [S.beta(), S.betahat(), S.ell()])
            co = [c / rk for c in co]
            kappa = wedge(g, eexp(escale(Fr(-1)/rk, c1), 4*n))
            cc = S.corrected_coords(kappa)
            prof = S.profile(g, 4)
            print("d=%d v1=%s v2=%s rk=%s c1/rk=(%s,%s,%s) kappa_flat=%s weil=%s r=%d prof=%s Ext2(simple)=%d"
                  % (d, v1, v2, rk, co[0], co[1], co[2], cc is not None,
                     (cc[1], cc[2]) if cc else None, prof[2], prof, ext2))
