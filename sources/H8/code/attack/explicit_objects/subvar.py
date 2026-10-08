"""subvar.py -- abelian subvarieties Z_{p:q} of A = X x X^ and the tangent
space T of the polarised Weil family, exact.  n = 2, 3."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial, gcd
from itertools import combinations
from split import Split
from ext import *

def Bx(S, i):
    """B x_j = xi_{n+j}, B x_{n+j} = -xi_j  (paper's B)."""
    n = S.n
    if i < n:
        return {1 << S.xi(n + i): Fr(1)}
    return {1 << S.xi(i - n): Fr(-1)}

def Zclass_wedge(S, p, q):
    """wedge_i (q x_i + p B x_i): the pulled-back point class of A/Z."""
    r = {0: Fr(1)}
    for i in range(S.m):
        v = eadd({1 << S.x(i): Fr(q)}, escale(Fr(p), Bx(S, i)))
        r = wedge(r, v)
    return r

def D(S, p, q):
    return eadd(escale(Fr(q*q), S.beta()), escale(Fr(-p*q), S.ell()), escale(Fr(p*p), S.betahat()))

def Zclass(S, p, q):
    z = escale(Fr(1, factorial(S.n)), epow(D(S, p, q), S.n))
    return z

def tangent_T(S):
    """v in H^1(T_A) = span{ dzbar_b (x) d/dz_a } acting as w(b) c(a);
    T = {v : v _| eta = v _| w1 = v _| w2 = 0}."""
    m = S.m
    etac = S.to_complex(S.eta())
    w1, w2 = S.weil()
    w1c, w2c = S.to_complex(w1), S.to_complex(w2)
    basis = [(b, a) for b in range(m) for a in range(m)]   # w(m+b) c(a)
    def act(v, x):
        out = {}
        for (b, a), c in v.items():
            y = wedge_left(m + b, interior(a, x))
            out = eadd(out, escale(c, y))
        return out
    # build linear map v -> (v.eta, v.w1, v.w2) and find kernel
    cols = []
    for (b, a) in basis:
        v = {(b, a): GQ(1)}
        img = {}
        for tag, x in (("e", etac), ("1", w1c), ("2", w2c)):
            y = act(v, x)
            for k, c in y.items():
                img[(tag, k)] = c
        cols.append(img)
    r, ker = rank_and_kernel(cols, want_kernel=True)
    T = [{basis[i]: c for i, c in combo.items()} for combo in ker]
    return T, act

def main():
    for n, d in [(2, 1), (2, 2), (3, 1), (3, 2)]:
        t0 = time.time()
        S = Split(n, d)
        eta = S.eta(); w1, w2 = S.weil()
        print("=== n=%d d=%d" % (n, d))
        slopes = [(0, 1), (1, 0), (1, 1), (1, -1), (1, 2), (2, 1), (-1, 3), (2, 3)]
        Zs = {}
        for (p, q) in slopes:
            zw = Zclass_wedge(S, p, q)
            z = Zclass(S, p, q)
            sgn = None
            if zw == z: sgn = 1
            elif zw == escale(Fr(-1), z): sgn = -1
            deg = S.integral(wedge(z, epow(eta, n)))
            hodge = S.hodge_type_ok(S.to_complex(z), n)
            Zs[(p, q)] = z
            print("  Z_{%d:%d}: wedge = %s * D^n/n!,  int [Z] eta^n = %s,  type (n,n): %s,  [Z]^2 = 0: %s"
                  % (p, q, sgn, deg, hodge, wedge(z, z) == {}))
        # intersection numbers
        pairs = [((0,1),(1,0)), ((1,1),(1,-1)), ((0,1),(1,2)), ((1,2),(2,1)), ((1,1),(2,3))]
        for s, t in pairs:
            I = S.integral(wedge(Zs[s], Zs[t]))
            det = s[0]*t[1] - s[1]*t[0]
            print("  int Z_%s Z_%s = %s   (det^{2n} = %s)" % (s, t, I, det ** (2*n)))
        # span of Z classes
        allZ = [Zs[s] for s in slopes]
        print("  dim span of the %d classes [Z]:" % len(allZ), rank_and_kernel(allZ), "(2n+1 =", 2*n+1, ")")
        print("  w1 in span:", solve_in_span(w1, allZ) is not None,
              " w2 in span:", solve_in_span(w2, allZ) is not None,
              " eta^n in span:", solve_in_span(epow(eta, n), allZ) is not None)
        # tangent space T
        T, act = tangent_T(S)
        print("  dim T =", len(T), "(n^2 =", n*n, ")")
        # K-linearity check: T vectors commute with M? check via killing gamma0 +- delta ell not needed
        for (p, q) in [(0, 1), (1, 1), (1, 2)]:
            zc = S.to_complex(Zs[(p, q)])
            imgs = [act(v, zc) for v in T]
            rk = rank_and_kernel(imgs)
            print("  dim {v in T: v _| [Z_%d:%d] = 0} =" % (p, q), len(T) - rk, "(n(n+1)/2 =", n*(n+1)//2, ")")
        print("  (%.1fs)" % (time.time() - t0))

if __name__ == "__main__":
    main()
