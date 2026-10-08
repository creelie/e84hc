import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from split import Split
from orlov import *
from ext import *
n = 2
one = {0: Fr(1)}
d = 1
S = Split(n, d)
chF = eadd(one, escale(Fr(-d), pt_X(n)))
g = orlov_ch(n, chF, dual(chF))
c1 = degree_part(g, 2); r = g[0]
kappa = wedge(g, eexp(escale(Fr(-1)/r, c1), 4*n))
print("r(ch E) =", S.r_of(g))
print("r(kappa) =", S.r_of(kappa))
print("profile ch E:", S.profile(g))
print("profile kappa:", S.profile(kappa))
