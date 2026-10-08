"""locus.py -- for the certificate objects: dim of Ann_{H^1(T_A)}(kappa_B) (the
first-order Hodge locus of kappa_B among all complex tori), dim Ann_{HT^2}, the
ratio R = c_2^2 int eta^4 / int omega^2 at n = 2, and the rank of ev_E in degree 1."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from ext import *
from orlov import secant, dual, orlov_ch_fast
from split import Split
def h1t_ann(S, x):
    xc = S.to_complex(x); m = S.m
    imgs = [wedge_left(m + b, interior(a, xc)) for b in range(m) for a in range(m)]
    return m * m - rank_and_kernel(imgs)
for n, d, v in [(2, 1, (1, 0)), (2, 1, (0, 1)), (2, 2, (0, 1)), (2, 3, (0, 1)), (3, 2, (0, 1)), (3, 6, (0, 1))]:
    S = Split(n, d)
    f = secant(n, d, *v)
    g = orlov_ch_fast(n, f, dual(f))
    kb = wedge(g, eexp(escale(Fr(1, 2), S.ell()), 4 * n))
    c, a, b = S.corrected_coords(kb)
    w1, w2 = S.weil()
    om = eadd(escale(a, w1), escale(b, w2))
    line = "n=%d d=%d v=%s: dim Ann_{H^1(T)}(kappa_B) = %d, dim Ann_{H^1(T)}(ch E) = %d, dim Ann_{HT^2}(ch E) = %d, rank HT^1 -> = %d" % (
        n, d, v, h1t_ann(S, kb), h1t_ann(S, g), (4*n*(4*n-1))//2 - S.r_of(g), S.profile(g, 1)[1])
    if n == 2:
        R = c[2] ** 2 * S.integral(epow(S.eta(), 4)) / S.integral(wedge(om, om))
        line += ", c_1 = %s, c_3 = %s, R = %s" % (c[1], c[3], R)
    print(line)
