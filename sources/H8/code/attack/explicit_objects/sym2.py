"""sym2.py -- untwisting by symmetric square: for E = Phi(F [x] F^vee) with
kappa_B = ch(E) e^{ell/2} flat, the summands S^2 E (x) P and Lambda^2 E (x) P of
E (x) E (x) P (c_1(P) = ell) have flat untwisted Chern characters
(kappa^2 +- psi^2 kappa)/2.  Check flatness, Weil parts, and r."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial
from ext import *
from orlov import secant, dual, orlov_ch_fast
from split import Split
def psi2(u):
    return {m: c * (2 ** (popcount(m) // 2)) for m, c in u.items()}
for n, d, v in [(2, 1, (0, 1)), (2, 1, (1, 0)), (2, 2, (0, 1)), (3, 2, (0, 1))]:
    S = Split(n, d)
    f = secant(n, d, *v)
    g = orlov_ch_fast(n, f, dual(f))
    P = eexp(S.ell(), 4 * n)
    sq = wedge(g, g)
    for name, sgn in (("S^2", 1), ("L^2", -1)):
        c = wedge(escale(Fr(1, 2), eadd(sq, escale(Fr(sgn), psi2(g)))), P)
        cc = S.corrected_coords(c)
        r = S.r_of(c) if cc else None
        print("n=%d d=%d v=%s  %s E (x) P: rank %s, flat %s, weil %s, r = %s" % (
            n, d, v, name, c.get(0, 0), cc is not None, (cc[1], cc[2]) if cc else None, r))
