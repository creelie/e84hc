"""v6_sym2.py -- independent check of T3 claim 8 (untwisting by S^2 / Lambda^2)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import factorial
from ea import *
from model import Model
from orl import secant, dualch, orlov
t0 = time.time()
def psi2(u):
    return {k: c * (2 ** (len(k) // 2)) for k, c in u.items()}
def flat_coords(M, u):
    e = M.eta(); re, im = M.weil_pm()
    basis = [power(e, k) for k in range(2 * M.n + 1)] + [re, im]
    x = solve(u, basis)
    return None if x is None else (x[:2 * M.n + 1], x[-2], x[-1])
for n, d in [(2, 1), (2, 2), (2, 3), (2, 7), (3, 1), (3, 2)]:
    M = Model(n, d)
    f = secant(n, d, 0, 1)
    ch = orlov(n, f, dualch(f))
    P = expo(M.ell())
    for name, sgn in (("S^2(E[1])(x)P", -1), ("L^2(E[1])(x)P", +1)):
        # ch(S^2 x) = (ch x^2 + psi^2 ch x)/2 with ch x = -ch E  ->  (chE^2 - psi^2 chE)/2
        # ch(L^2 x) = (ch x^2 - psi^2 ch x)/2                      ->  (chE^2 + psi^2 chE)/2
        c = mul(sc(F(1, 2), add(mul(ch, ch), sc(F(sgn), psi2(ch)))), P)
        cc = flat_coords(M, c)
        line = "n=%d d=%d %s: rank %s flat %s" % (n, d, name, c.get((), 0), cc is not None)
        if cc:
            line += " weil(my norm.)=(%s,%s)" % (cc[1], cc[2])
            if n == 2 and cc[0][0] != 0 and (cc[1], cc[2]) != (0, 0):
                t = cc[0][1] / cc[0][0]
                c2 = mul(c, expo(sc(-t, M.eta())))
                k2 = flat_coords(M, c2)
                re, im = M.weil_pm(); om = add(sc(k2[1], re), sc(k2[2], im))
                R = k2[0][2] ** 2 * M.integral(power(M.eta(), 4)) / M.integral(mul(om, om))
                line += " after eta-twist c1=%s c3=%s R=%s" % (k2[0][1], k2[0][3], R)
            line += " r=%d" % M.r(c)
        print(line + "  (%.1fs)" % (time.time() - t0), flush=True)
