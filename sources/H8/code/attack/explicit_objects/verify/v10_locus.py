"""v10_locus.py -- first-order Hodge locus (Ann in H^1(T_A)) of kappa_B = ch(E) e^{ell/2} for the certificates."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from ea import *
from model import Model
from orl import secant, dualch, orlov
t0 = time.time()
for n, d, v in [(2, 1, (0, 1)), (2, 1, (1, 0)), (2, 7, (0, 1)), (3, 2, (0, 1)), (3, 6, (0, 1)), (3, 7, (0, 1))]:
    M = Model(n, d); m = M.m
    f = secant(n, d, *v); ch = orlov(n, f, dualch(f))
    kb = mul(ch, expo(sc(F(1, 2), M.ell())))
    out = []
    for x in (kb, ch):
        xc = M.cx(x)
        imgs = [M.Dv({(b, a): Qm(1, 0, 1)}, xc) for b in range(m) for a in range(m)]
        out.append(m * m - rank(imgs))
    ext1 = M.profile(ch, 1)[1]
    print("n=%d d=%d v=%s: dim Ann_{H^1(T)}(kappa_B) = %d, dim Ann_{H^1(T)}(ch E) = %d, rank HT^1 -> = %d  (%.1fs)"
          % (n, d, v, out[0], out[1], ext1, time.time() - t0), flush=True)
