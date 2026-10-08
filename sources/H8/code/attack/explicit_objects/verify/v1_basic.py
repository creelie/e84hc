"""v1_basic.py -- independent checks of the model, T, T-flat classes, Weil classes, and
the Orlov-product flatness claims (T3 claims 3, 5, 6)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import factorial, comb
from itertools import combinations
from ea import *
from model import Model
from orl import secant, dualch, orlov

t0 = time.time()


def flat_coords(M, u):
    """u = sum c_k eta^k + a*re + b*im ?"""
    e = M.eta(); re, im = M.weil_pm()
    basis = [power(e, k) for k in range(2 * M.n + 1)] + [re, im]
    x = solve(u, basis)
    if x is None:
        return None
    return x[:2 * M.n + 1], x[-2], x[-1]


for n, d in [(2, 1), (2, 2), (2, 3), (2, 7), (3, 1), (3, 2)]:
    M = Model(n, d)
    T = M.tangent()
    e = M.eta(); re, im = M.weil_pm()
    # consistency: eta, re, im of type (k,k); T kills re, im
    ok_types = M.is_type(M.cx(e), 1) and M.is_type(M.cx(re), n) and M.is_type(M.cx(im), n)
    kills = all(not M.Dv(v, M.cx(w)) for v in T for w in (re, im))
    # compare with the paper's closed formula: omega_pm prop (gamma -+ sqrt(-d) ell)^n
    gam = add(sc(F(d), M.beta()), sc(F(-1), M.betahat()))
    l = M.ell()
    cre = {}; cim = {}
    for k in range(n + 1):
        term = sc(F(comb(n, k)), mul(power(gam, n - k), power(l, k)))
        # (-sqrt(-d))^k : k even -> (-d)^{k/2}; k odd -> -(-d)^{(k-1)/2} sqrt(-d)
        if k % 2 == 0:
            cre = add(cre, sc(F((-d) ** (k // 2)), term))
        else:
            cim = add(cim, sc(F(-((-d) ** ((k - 1) // 2))), term))
    span_ok = solve(cre, [re, im]) is not None and solve(cim, [re, im]) is not None
    print("n=%d d=%d: dim T = %d (n^2=%d); eta,Weil of Hodge type: %s; T kills Weil: %s; closed formula in span: %s  (%.1fs)"
          % (n, d, len(T), n * n, ok_types, kills, span_ok, time.time() - t0), flush=True)
