"""v7_tflat.py -- rational classes x in H^{2k}(A,Q) with v _| x = 0 for all v in T (Lemma B, step 2)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from itertools import combinations
from ea import *
from model import Model, kernel
t0 = time.time()
for n, d, degs in [(2, 1, range(5)), (2, 2, range(5)), (2, 5, range(5)), (3, 1, range(4)), (3, 2, [1, 2, 3])]:
    M = Model(n, d); T = M.tangent()
    dims = []
    for k in degs:
        monos = list(combinations(range(M.N), 2 * k))
        cols = []
        for mo in monos:
            xc = M.cx({mo: F(1)})
            eq = {}
            for ti, v in enumerate(T):
                for key, c in M.Dv(v, xc).items():
                    eq[(ti, key, 0)] = c.a
                    eq[(ti, key, 1)] = c.b
            cols.append(clean(eq))
        r = rank(cols)
        dims.append((k, len(monos) - r))
    print("n=%d d=%d: dim of rational T-flat classes by degree 2k: %s  (%.1fs)" % (n, d, dims, time.time() - t0), flush=True)
