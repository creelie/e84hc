"""zsums.py -- which integer combinations of [Z_{p:q}] equal N w1 (+ c eta^n)?
Minimal |N| over the Z-span of all [Z_{p:q}] with |p|,|q| <= B; minimal numbers
of slopes; Ext^2 of the resulting direct sums (6 per component at n = 2,
cross terms avoided by shifts)."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import gcd
from itertools import combinations
from split import Split
from subvar import Zclass
from ext import *

def lattice_min_multiple(vectors, target, keys):
    """smallest positive integer N with N*target in the Z-span of vectors
    (all with rational coords): Hermite normal form over Z."""
    import functools
    den = 1
    for v in vectors + [target]:
        for c in v.values():
            den = den * c.denominator // gcd(den, c.denominator)
    M = [[int(v.get(k, 0) * den) for k in keys] for v in vectors]
    t = [int(target.get(k, 0) * den) for k in keys]
    # row-reduce M over Z (HNF-like)
    rows = [r[:] for r in M if any(r)]
    basis = []
    col = 0
    ncols = len(keys)
    while rows and col < ncols:
        piv = [r for r in rows if r[col] != 0]
        if not piv:
            col += 1
            continue
        while len([r for r in rows if r[col] != 0]) > 1:
            nz = sorted([r for r in rows if r[col] != 0], key=lambda r: abs(r[col]))
            p = nz[0]
            for r in nz[1:]:
                q = r[col] // p[col]
                for j in range(ncols):
                    r[j] -= q * p[j]
            rows = [r for r in rows if any(r)]
        p = [r for r in rows if r[col] != 0][0]
        basis.append((col, p))
        rows = [r for r in rows if r is not p]
        col += 1
    # find minimal N: t*N reduced by basis must vanish; solve over Q then take denominators
    # reduce t over Q in the echelon basis to get coefficients
    coeffs = []
    res = [Fr(x) for x in t]
    for (c, p) in basis:
        f = res[c] / p[c]
        coeffs.append(f)
        for j in range(ncols):
            res[j] -= f * p[j]
    if any(res):
        return None
    N = 1
    for f in coeffs:
        N = N * f.denominator // gcd(N, f.denominator)
    return N

for n, d in [(2, 1), (2, 2), (2, 3), (3, 1)]:
    S = Split(n, d)
    w1, w2 = S.weil()
    Bd = 4
    slopes = sorted({(p // gcd(p, q), q // gcd(p, q)) if q > 0 or (q == 0 and p > 0) else (-p // gcd(p, q), -q // gcd(p, q))
                     for p in range(-Bd, Bd + 1) for q in range(-Bd, Bd + 1) if (p, q) != (0, 0)})
    Zs = [Zclass(S, p, q) for (p, q) in slopes]
    keys = sorted({k for z in Zs + [w1, w2] for k in z})
    N1 = lattice_min_multiple(Zs, w1, keys)
    N2 = lattice_min_multiple(Zs, w2, keys)
    print("n=%d d=%d: %d slopes with |p|,|q|<=%d; minimal N with N w1 in Z-span of [Z]'s: %s ; for w2: %s"
          % (n, d, len(slopes), Bd, N1, N2))
    # minimal number of slopes: search subsets of size 2n among small slopes
    small = [s for s in slopes if abs(s[0]) <= 3 and abs(s[1]) <= 3]
    found = None
    for sub in combinations(small, 2 * n):
        x = solve_in_span(w1, [Zclass(S, p, q) for (p, q) in sub])
        if x is not None:
            found = (sub, x)
            break
    if found:
        sub, x = found
        den = 1
        for c in x:
            den = den * c.denominator // gcd(den, c.denominator)
        m = [int(c * den) for c in x]
        g = 0
        for c in m: g = gcd(g, c)
        m = [c // g for c in m]; Nw = Fr(den, g)
        print("   2n = %d slopes suffice: %s, integer multiplicities %s give %s * w1;"
              % (2 * n, sub, m, Nw))
        if n == 2:
            print("   Ext^2 of the direct sum of translates (shifts distinct across slopes) = 6 * %d = %d, r(N w1) = 12"
                  % (sum(abs(c) for c in m), 6 * sum(abs(c) for c in m)))
    else:
        print("   no 2n-subset of small slopes represents w1")
