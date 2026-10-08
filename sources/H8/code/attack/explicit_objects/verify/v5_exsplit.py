"""v5_exsplit.py -- side check of the paper's ex:splitsmall formulas (n=2,3) against the Weil plane."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from ea import *
from model import Model
for n, d in [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)]:
    M = Model(n, d)
    re, im = M.weil_pm()
    gam = add(sc(F(d), M.beta()), sc(F(-1), M.betahat())); l = M.ell()
    if n == 2:
        w1 = add(sc(F(d), mul(l, l)), sc(F(-1), mul(gam, gam))); w2 = sc(F(2), mul(gam, l))
    else:
        w1 = add(mul(gam, mul(l, l)), sc(F(-1, 3), power(gam, 3)))
        w2 = add(mul(mul(gam, gam), l), sc(F(-d, 3), power(l, 3)))
    alt = add(sc(F(d), mul(gam, mul(l, l))), sc(F(-1, 3), power(gam, 3))) if n == 3 else None
    print("n=%d d=%d: paper omega1 in Weil plane: %s; paper omega2 in Weil plane: %s%s" % (
        n, d, solve(w1, [re, im]) is not None, solve(w2, [re, im]) is not None,
        ("; d*gamma*l^2 - gamma^3/3 in plane: %s" % (solve(alt, [re, im]) is not None)) if alt else ""))
