"""a1_lattice.py -- the integral F0-Hodge ring R_Z = R cap H^ev(X,Z) of a principally
polarised abelian fourfold with RM by F0 = Q(sqrt5), the Mukai form chi(v) = int v^vee v on
it, the V-matrix, and the classification of 'admissible' characters for a
Hochschild-minimal F-secant object (track A1).

A class v in R is F'-secant for some quartic CM field F' = F0(sqrt(-q')) (up to a rational
F0-B-field, i.e. an SL_2(F0)-conjugate of the standard structure) iff its 3x3 V-matrix has
rank <= 2 and the left kernel contains (A,B,C) with B^2 - 4AC < 0 at both real places
(the secant line meets the conic of pure spinors {(1,t,t^2)} in two complex points).
A Hochschild-minimal object (Ext^{<0} = 0, Ext^{0,1,2} = (1, 8, r^2)) with ch = v needs
  chi(v) = 2 - 16 + r^2(v) = 4 (rank V = 1, r^2 = 18) or 6 (rank V = 2, r^2 = 20).
"""
import sys, time, itertools
from fractions import Fraction as Fr
import flint
import numpy as np
from ealib import *
from a1model import RMModel, QS

M = RMModel()


def Rbasis_rational():
    th, thR = M.theta, M.thetaR
    gens = []
    for i in range(5):
        for j in range(5 - i):
            gens.append(wedge(power(th, i), power(thR, j)))
    return gens


def saturate(vecs, nbits=8):
    """Z-basis of span_Q(vecs) cap Z^{2^nbits} (vecs: dicts mask->Fraction)."""
    keys = sorted(set(k for v in vecs for k in v))
    # rational basis
    Mq = flint.fmpq_mat(len(vecs), len(keys))
    kid = {k: i for i, k in enumerate(keys)}
    for r, v in enumerate(vecs):
        for k, c in v.items():
            Mq[r, kid[k]] = flint.fmpq(c.numerator, c.denominator)
    Rr, rk = Mq.rref()
    B = [[Fr(int(Rr[i, j].p), int(Rr[i, j].q)) for j in range(len(keys))] for i in range(rk)]
    # columns of B span a lattice Lc in Q^rk; integral points = { c B : c in Lc^dual }
    from math import lcm
    den = 1
    for row in B:
        for x in row:
            den = lcm(den, x.denominator)
    cols = flint.fmpz_mat(len(keys), rk)
    for j in range(len(keys)):
        for i in range(rk):
            cols[j, i] = int(B[i][j] * den)
    H = cols.hnf()
    # nonzero rows of H give a basis of the column lattice (scaled by den)
    Lrows = [[Fr(int(H[i, j]), den) for j in range(rk)] for i in range(H.nrows()) if any(H[i, j] != 0 for j in range(rk))]
    assert len(Lrows) == rk
    Lm = flint.fmpq_mat(rk, rk)
    for i in range(rk):
        for j in range(rk):
            Lm[i, j] = flint.fmpq(Lrows[i][j].numerator, Lrows[i][j].denominator)
    Dual = Lm.inv().transpose()   # rows = dual basis
    out = []
    for i in range(rk):
        c = [Fr(int(Dual[i, j].p), int(Dual[i, j].q)) for j in range(rk)]
        v = {}
        for j in range(len(keys)):
            s = sum(c[a] * B[a][j] for a in range(rk))
            if s != 0:
                v[keys[j]] = s
        out.append(v)
    for v in out:
        assert all(x.denominator == 1 for x in v.values())
    return out


if __name__ == "__main__":
    t0 = time.time()
    gens = Rbasis_rational()
    check("R has rank 9 over Q", rank_Q(gens) == 9)
    RZ = saturate(gens)
    check("R_Z = R cap H^ev(X,Z) has a Z-basis of 9 integral classes", len(RZ) == 9)
    # LLL-reduce for readability: use the Gram matrix of the monomial coefficients
    G = [[M.chi(a, b) for b in RZ] for a in RZ]
    print("Mukai form chi on R_Z (Gram matrix):")
    for r in G:
        print("   ", [int(x) for x in r])
    Gm = flint.fmpz_mat([[int(x) for x in r] for r in G])
    print("   det =", Gm.det())
    # V matrices of the basis
    Vs = [M.to_V(b) for b in RZ]
    for i, (b, V) in enumerate(zip(RZ, Vs)):
        print("  b%d: rank %s, deg %s, V = %s" % (i, b.get(0, 0), degrees(b), V))
    import pickle
    pickle.dump({"RZ": RZ, "G": G, "V": Vs}, open("a1_lattice.pkl", "wb"))
    print("time %.1fs" % (time.time() - t0))
    summary()
