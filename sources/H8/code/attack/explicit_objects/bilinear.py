"""bilinear.py -- ch(Phi(F1 [x] F2^vee)) is bilinear in (ch F1, ch F2).  For the
four basis pairs (u,u),(u,v),(v,u),(v,v) of the secant plane P_t check:
 (1) kappa_B = ch(E) e^{ell/2} lies in Q[eta] + HW  (so for every pair);
 (2) its moments mu_m = m! c_m satisfy mu_{m+2} = -mu_m/(4d)  (so rho <= 2);
 (3) the Weil part as a quadratic form in v = a u + b v_t (pair (v,v)).
"""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial
from ext import *
from orlov import secant, dual, orlov_ch_fast
from split import Split
ok_all = True
for n, ds in [(2, [1, 2, 3, 5]), (3, [1, 2, 6, 30, 42]), (4, [1, 2, 3])]:
    for d in ds:
        t0 = time.time()
        S = Split(n, d)
        B = eexp(escale(Fr(1, 2), S.ell()), 4 * n)
        basis = {"u": secant(n, d, 1, 0), "v": secant(n, d, 0, 1)}
        W = {}
        good = True
        for p in "uv":
            for q in "uv":
                g = orlov_ch_fast(n, basis[p], dual(basis[q]))
                cc = S.corrected_coords(wedge(g, B))
                if cc is None:
                    good = False; continue
                c, a, b = cc
                mu = [factorial(m) * c[m] for m in range(2 * n + 1)]
                rec = all(mu[m + 2] == -mu[m] / (4 * d) for m in range(2 * n - 1))
                good = good and rec
                W[(p, q)] = (a, b)
        # Weil part of the pair (v,v) for v = a u + b v_t:  sum a_p a_q W[p,q]
        print("n=%d d=%d: flat & recurrence for all 4 basis pairs: %s;  Weil(a u + b v_t, same) = "
              "(%s a^2 + %s ab + %s b^2) w1 + (%s a^2 + %s ab + %s b^2) w2   (%.1fs)" % (
              n, d, good,
              W[("u","u")][0], W[("u","v")][0] + W[("v","u")][0], W[("v","v")][0],
              W[("u","u")][1], W[("u","v")][1] + W[("v","u")][1], W[("v","v")][1], time.time() - t0))
        ok_all = ok_all and good
print("ALL:", ok_all)
