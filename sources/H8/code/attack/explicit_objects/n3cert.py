"""n3cert.py: the n = 3 certificate.  F = i_* L on the theta divisor of a genus-3
Jacobian with ch(F) = v_t = Theta - d pt (d = k(k+1)); E = Phi(F [x] F^vee).
Checks: ch(E) e^{ell/2} flat with Weil part; full Hochschild profile of ch(E)
equals (1,6,6,1) (x) (1,6,6,1) = (1,12,48,74,48,12,1)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial
from ext import *
from orlov import secant, dual, orlov_ch_fast
from split import Split
n = 3
def tensor_profile(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out
print("expected (1,6,6,1)^2 =", tensor_profile([1,6,6,1],[1,6,6,1]))
for d in [2, 6]:
    t0 = time.time()
    S = Split(n, d)
    v = secant(n, d, 0, 1)
    g = orlov_ch_fast(n, v, dual(v))
    kb = wedge(g, eexp(escale(Fr(1, 2), S.ell()), 4 * n))
    cc = S.corrected_coords(kb)
    print("d=%d: rank %s; ch e^{ell/2} = sum c_k eta^k + (%s) w1 + (%s) w2; c =" % (d, g.get(0,0), cc[1], cc[2]), [str(x) for x in cc[0]])
    prof = S.profile(g, 6)
    print("   Hochschild profile of ch(E):", prof, "(%.1fs)" % (time.time()-t0))
