"""tflat.py -- rational classes x in H^{2k}(A,Q) with v _| x = 0 for all v in T
(T = tangent space of the polarised Weil family at the split point).
Expected: Q eta^k, plus the Weil plane when k = n."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from itertools import combinations
from split import Split
from subvar import tangent_T
from ext import *

def tflat_dims(n, d):
    S = Split(n, d)
    T, act = tangent_T(S)
    N = S.N
    out = []
    for k in range(0, 2 * n + 1):
        deg = 2 * k
        monos = [sum(1 << i for i in c) for c in combinations(range(N), deg)]
        # unknown rational coefficients c_mono; equations: real and imaginary parts of
        # act(v, to_complex(mono)) summed.
        cols = []
        for mo in monos:
            xc = S.to_complex({mo: Fr(1)})
            img = {}
            for ti, v in enumerate(T):
                y = act(v, xc)
                for key, c in y.items():
                    img[(ti, key, 0)] = c.a
                    img[(ti, key, 1)] = c.b
            cols.append({kk: c for kk, c in img.items() if c != 0})
        r = rank_and_kernel(cols)
        out.append(len(monos) - r)
    return out

if __name__ == "__main__":
    for n, d in [(2, 1), (2, 2), (2, 3)]:
        t0 = time.time()
        print("n=%d d=%d  dim of T-flat rational classes in degrees 0,2,..,4n:" % (n, d), tflat_dims(n, d), "(%.1fs)" % (time.time()-t0))
