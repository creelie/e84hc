"""xrank.py: ranks r^k_X(v) of HT^k(X) -> H^*(X), xi |-> xi _| v, for secant
classes v = a u_t + b v_t on X = E_i^n (t = beta principal), exact over Q(i)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from itertools import combinations
from ext import *
from orlov import secant, beta_X

def to_complex_X(n, u):
    # dz_j -> bit j, dzbar_j -> bit n+j ; x_j = (dz+dzb)/2, x_{n+j} = (dz - dzb)/(2i)
    half = GQ(Fr(1,2)); mhi = GQ(0, Fr(-1,2))
    images = {}
    for j in range(n):
        images[j] = {1 << j: half, 1 << (n + j): half}
        images[n + j] = {1 << j: mhi, 1 << (n + j): -mhi}
    out = {}
    for mask, c in u.items():
        piece = {0: GQ(c)}
        for i in range(2 * n):
            if mask >> i & 1:
                piece = wedge(piece, images[i])
        out = eadd(out, piece)
    return out

def ops_X(n):
    return [("w", n + i) for i in range(n)] + [("c", i) for i in range(n)]

def apply(op, u):
    return wedge_left(op[1], u) if op[0] == "w" else interior(op[1], u)

def rk_profile(n, v, kmax):
    vc = to_complex_X(n, v)
    ops = ops_X(n)
    prof = []
    for k in range(kmax + 1):
        imgs = []
        for S in combinations(range(len(ops)), k):
            w = vc
            for s in reversed(S):
                w = apply(ops[s], w)
            imgs.append(w)
        prof.append(rank_and_kernel(imgs))
    return prof

if __name__ == "__main__":
    for n in [2, 3, 4, 5]:
        for d in [1, 2, 3]:
            for (a, b) in [(1, 0), (0, 1), (1, 1), (2, 1)]:
                t0 = time.time()
                v = secant(n, d, a, b)
                p = rk_profile(n, v, min(n, 3) if n > 3 else n)
                print("n=%d d=%d (a,b)=(%d,%d) r^k_X = %s  (%.1fs)" % (n, d, a, b, p, time.time()-t0))
