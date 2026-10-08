"""v8_xprofile.py -- T3 claim 4: contraction ranks HT^k(X) -> H^*(X) into a secant class, and chi(F,F)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import comb, factorial
from itertools import combinations
from ea import *
from orl import secant, dualch, betaX
t0 = time.time()
def cxX(n, u):
    h = Qm(F(1, 2), 0, 1); mh = Qm(0, F(-1, 2), 1)
    im = {}
    for j in range(n):
        im[j] = {(j,): h, (n + j,): h}
        im[n + j] = {(j,): mh, (n + j,): -mh}
    return linsub({k: Qm(c, 0, 1) for k, c in u.items()}, im)
def prof(n, v, kmax):
    vc = cxX(n, v)
    ops = [("w", n + i) for i in range(n)] + [("c", i) for i in range(n)]
    out = []
    for k in range(kmax + 1):
        imgs = []
        for S in combinations(range(2 * n), k):
            w = vc
            for s in reversed(S):
                op = ops[s]
                w = mul({(op[1],): Qm(1, 0, 1)}, w) if op[0] == "w" else contract(op[1], w)
            imgs.append(w)
        out.append(rank(imgs))
    return out
for n in (2, 3, 4, 5):
    for d in (1, 7, 10):
        for (a, b) in [(1, 0), (0, 1), (3, -2)]:
            p = prof(n, secant(n, d, a, b), 2 * n if n <= 4 else n + 1)
            exp = [1] + [2 * comb(n, k) for k in range(1, n)] + [1] + [0] * n
            ok = p == exp[:len(p)]
            if not ok:
                print("MISMATCH n=%d d=%d (a,b)=(%d,%d): %s vs %s" % (n, d, a, b, p, exp))
    print("n=%d profiles checked (d=1,7,10; 3 secant vectors)  (%.1fs)" % (n, time.time() - t0), flush=True)
for n in (2, 3, 4, 5, 6):
    ok = True
    for d in (1, 7, 10):
        for (a, b) in [(1, 0), (0, 1), (3, -2)]:
            v = secant(n, d, a, b)
            top = tuple(range(2 * n))
            vol = sc(F(1, factorial(n)), power(betaX(n), n))
            chi = mul(dualch(v), v).get(top, 0) / vol[top]
            pred = 0 if n % 2 else 2 ** (n - 1) * (-1) ** (n // 2) * d ** (n // 2 - 1) * F(a * a * d + b * b)
            ok &= chi == pred
    print("n=%d chi formula: %s" % (n, ok), flush=True)
