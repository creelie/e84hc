import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from ext import *
from orlov import secant, dual, orlov_ch_fast
from split import Split
def psi2(u):
    return {m: c * (2 ** (popcount(m) // 2)) for m, c in u.items()}
for d, v in [(1, (0, 1)), (1, (1, 0)), (2, (0, 1)), (3, (0, 1))]:
    n = 2
    S = Split(n, d)
    f = secant(n, d, *v)
    g = orlov_ch_fast(n, f, dual(f))
    c = wedge(escale(Fr(1, 2), eadd(wedge(g, g), escale(Fr(-1), psi2(g)))), eexp(S.ell(), 8))
    ck, a, b = S.corrected_coords(c)
    # twist by e^{-t eta} with t = c1/c0 to kill c_1
    t = ck[1] / ck[0]
    c2 = wedge(c, eexp(escale(-t, S.eta()), 8))
    ck2, a2, b2 = S.corrected_coords(c2)
    w1, w2 = S.weil()
    om = eadd(escale(a2, w1), escale(b2, w2))
    R = ck2[2] ** 2 * S.integral(epow(S.eta(), 4)) / S.integral(wedge(om, om))
    print("d=%d v=%s: Lambda^2E(x)P twisted to c_1=0: c = %s, Weil = (%s,%s), c_3 = %s, R = c_2^2 int eta^4 / int omega^2 = %s"
          % (d, v, [str(x) for x in ck2], a2, b2, ck2[3], R))
