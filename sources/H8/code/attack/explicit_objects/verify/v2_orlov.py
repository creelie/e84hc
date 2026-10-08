"""v2_orlov.py -- independent recomputation of T3 claims 5 and 6 (Orlov products, certificates)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import factorial, comb
from ea import *
from model import Model
from orl import secant, dualch, orlov

t0 = time.time()
args = sys.argv[1:]
n = int(args[0]) if args else 2
ds = [int(x) for x in args[1].split(",")] if len(args) > 1 else [1, 2, 3, 5, 6, 7, 11]
do_prof = (len(args) > 2 and args[2] == "prof")


def flat_coords(M, u):
    e = M.eta(); re, im = M.weil_pm()
    basis = [power(e, k) for k in range(2 * M.n + 1)] + [re, im]
    x = solve(u, basis)
    if x is None:
        return None
    return x[:2 * M.n + 1], x[-2], x[-1]


def hankel_rank(mu, n):
    rows = [{(i,): F(mu[j + i]) for i in range(3) if mu[j + i] != 0} for j in range(2 * n - 1)]
    return rank([r for r in rows])


for d in ds:
    M = Model(n, d)
    l = M.ell()
    eh = expo(sc(F(1, 2), l)); emh = expo(sc(F(-1, 2), l))
    for p, q in [((0, 1), (0, 1)), ((1, 0), (1, 0)), ((1, 0), (0, 1)), ((0, 1), (1, 0)), ((1, 1), (2, -1))]:
        f1 = secant(n, d, *p); f2 = secant(n, d, *q)
        ch = orlov(n, f1, dualch(f2))
        flat0 = flat_coords(M, ch) is not None
        kp = flat_coords(M, mul(ch, eh)); km = flat_coords(M, mul(ch, emh))
        # try other B-fields: ell/2 + beta, ell/2 + betahat, ell/2 + eta
        others = {}
        for name, B in [("l/2+beta", add(sc(F(1, 2), l), M.beta())), ("l/2+bhat", add(sc(F(1, 2), l), M.betahat())),
                        ("l/2+eta", add(sc(F(1, 2), l), M.eta())), ("l", l), ("0", {})]:
            others[name] = flat_coords(M, mul(ch, expo(B))) is not None
        line = "n=%d d=%d F1=%s F2=%s: rk=%s flat(ch)=%s flat(ch e^{l/2})=%s flat(ch e^{-l/2})=%s others=%s" % (
            n, d, p, q, ch.get((), 0), flat0, kp is not None, km is not None, others)
        if kp is not None:
            c, a, b = kp
            mu = [factorial(k) * c[k] for k in range(2 * n + 1)]
            rho = hankel_rank(mu, n)
            rec = all(mu[k + 2] == -mu[k] / (4 * d) for k in range(2 * n - 1))
            line += " weil=(%s,%s) rho=%d rec(-1/4d)=%s" % (a, b, rho, rec)
            if n == 2:
                re, im = M.weil_pm()
                om = add(sc(a, re), sc(b, im))
                if om:
                    R = c[2] ** 2 * M.integral(power(M.eta(), 4)) / M.integral(mul(om, om))
                    line += " c1=%s c3=%s R=%s" % (c[1], c[3], R)
        r = M.r(ch)
        line += " r(chE)=%d (6n^2-2n=%d)" % (r, 6 * n * n - 2 * n)
        if do_prof and p == (0, 1) and q == (0, 1):
            line += " profile=%s" % M.profile(ch, min(2 * n, 3))
        print(line + "  (%.1fs)" % (time.time() - t0), flush=True)
