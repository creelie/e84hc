import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from split import Split
from orlov import *
from ext import *
n = 2
one = {0: Fr(1)}
for d in [1, 2]:
    S = Split(n, d)
    chF = eadd(one, escale(Fr(-d), pt_X(n)))
    g = orlov_ch(n, chF, dual(chF))
    c1 = degree_part(g, 2)
    print("d", d, "c1 in (beta, betahat, ell):", solve_in_span(c1, [S.beta(), S.betahat(), S.ell()]))
    r = g[0]
    kappa = wedge(g, eexp(escale(Fr(-1)/r, c1), 4*n))
    cc = S.corrected_coords(kappa)
    print("  kappa corrected form?", cc)
    # also try with F2 = F1 (no dual), and with ell sign flipped via different shear
