#!/usr/bin/env python3
"""
t4_contr.py -- contraction checks at n = 4 on the split member (tau = iI), mod p.

  (K1) beta, betahat, ell, eta have no (2,0) part; M preserves H^{1,0}
  (K2) T = { v in H^1(T_A) : v K-linear, v _| eta = 0 } has dim 16 = n^2 (mod p)
       and kills W1, W2 and eta
  (K3) rank HT^2 _| ch(F) = 28 for natural F (line bundles, subtori, twisted
       subtori); 28 is also the upper bound dim Ext^2(F,F), so it is exact,
       and sigma_F is injective (ker ev_F subset Ann(ch F), both of dim 92)
  (K4) r(gamma) for corrected characters gamma = N W + sum c_k eta^k of Hankel
       rank rho = 0,1,2,3 against (4+rho) 16 - 8 = 56, 72, 88, 104
  (K5) dim Ann_T(ch F) for natural F: line bundles, subtori, theta-bundles
"""
import sys, os, time
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ext import *
from contraction import *

n, d = 4, int(sys.argv[1]) if len(sys.argv) > 1 else 1
S = Split(n, d)
b, bh, l, eta = S.beta(), S.betahat(), S.ell(), S.eta()
t0 = time.time()

# (K1)
def two_zero_part(cls):
    v = dense(cls)
    tot = 0
    for a in range(8):
        va = op_apply(('c', TAN[a]), v)
        for bb in range(8):
            w = op_apply(('c', TAN[bb]), va)
            tot += int(np.count_nonzero(w))
    return tot
print("(K1) (2,0)-part of beta, betahat, ell, eta vanishes:",
      [two_zero_part(c) == 0 for c in (b, bh, l, eta)])
# M on generators: x_j -> -xi_{4+j}, x_{4+j} -> xi_j, xi_j -> -d x_{4+j}, xi_{4+j} -> d x_j
def M_gen(g):
    j = g + 1
    if j <= 4:            # x_j
        return {xig(4 + j): P - 1}
    if j <= 8:            # x_{4+jj}
        return {xig(j - 4): 1}
    jj = j - 8            # xi_jj
    if jj <= 4:
        return {xg(4 + jj): (P - d) % P}
    return {xg(jj - 4): d % P}
def M_form(f):
    out = {}
    for g, c in f.items():
        for g2, c2 in M_gen(g).items():
            out[g2] = (out.get(g2, 0) + c * c2) % P
    return {k: v for k, v in out.items() if v}
def in_span(vec, basis):
    rows = [[bv.get(g, 0) for g in range(16)] for bv in basis]
    r0 = rank_mod([np.array(r, dtype=np.int64) for r in rows])
    r1 = rank_mod([np.array(r, dtype=np.int64) for r in rows] +
                  [np.array([vec.get(g, 0) for g in range(16)], dtype=np.int64)])
    return r0 == r1
print("     M preserves H^{1,0}:", all(in_span(M_form(h), HOL) for h in HOL))

# (K2) T: V (8x8) with v(hol_m) = sum_l V[m,l] anti_l
def coords(f, basis):
    """coordinates of a 1-form f in a basis (list of dicts) mod P: solve"""
    A = np.array([[bv.get(g, 0) for bv in basis] for g in range(16)], dtype=np.int64)
    rhs = np.array([f.get(g, 0) for g in range(16)], dtype=np.int64)
    # solve A x = rhs mod P (16 x 8, full column rank) by elimination
    M = np.concatenate([A, rhs[:, None]], axis=1) % P
    r = 0
    piv = []
    for c in range(8):
        nz = np.nonzero(M[r:, c])[0]
        pr = r + nz[0]
        M[[r, pr]] = M[[pr, r]]
        M[r] = M[r] * pow(int(M[r, c]), P - 2, P) % P
        for rr in range(16):
            if rr != r and M[rr, c]:
                M[rr] = (M[rr] - M[rr, c] * M[r]) % P
        piv.append(c)
        r += 1
    assert not M[8:, 8].any()
    return [int(M[k, 8]) for k in range(8)]
Mh = np.array([coords(M_form(h), HOL) for h in HOL], dtype=np.int64)   # row m: M hol_m
Ma = np.array([coords(M_form(a), ANTI) for a in ANTI], dtype=np.int64)
# unknown V flattened (64); equations: (Mh V - V Ma)[m, l] = 0
eqs = []
for m in range(8):
    for ll in range(8):
        row = np.zeros(64, dtype=np.int64)
        for k in range(8):
            row[k * 8 + ll] = (row[k * 8 + ll] + Mh[m, k]) % P
        for lp in range(8):
            row[m * 8 + lp] = (row[m * 8 + lp] - Ma[lp, ll]) % P
        eqs.append(row)
veta = dense(eta)
etaimgs = [h1t_apply(k, ll, veta) for k in range(8) for ll in range(8)]
# eta-condition: sum V[k,l] etaimgs[k*8+l] = 0 : columns are unknowns
E_eta = np.array(etaimgs, dtype=np.int64).T      # SIZE x 64
nzrows = np.nonzero(E_eta.any(axis=1))[0]
for r_ in nzrows:
    eqs.append(E_eta[r_])
A = np.array(eqs, dtype=np.int64) % P
# nullspace mod P
def nullspace(A):
    M = A.copy() % P
    nr, nc = M.shape
    r = 0
    pivcols = []
    for c in range(nc):
        if r == nr:
            break
        nz = np.nonzero(M[r:, c])[0]
        if not len(nz):
            continue
        pr = r + nz[0]
        M[[r, pr]] = M[[pr, r]]
        M[r] = M[r] * pow(int(M[r, c]), P - 2, P) % P
        oth = np.nonzero(M[:, c])[0]
        oth = oth[oth != r]
        if len(oth):
            M[oth] = (M[oth] - M[oth, c][:, None] * M[r][None, :]) % P
        pivcols.append(c)
        r += 1
    free = [c for c in range(nc) if c not in pivcols]
    basis = []
    for f in free:
        x = np.zeros(nc, dtype=np.int64)
        x[f] = 1
        for i, pc in enumerate(pivcols):
            x[pc] = (-M[i, f]) % P
        basis.append(x)
    return basis
Tbasis = nullspace(A)
print("(K2) dim T (mod p) =", len(Tbasis), "(expect n^2 = 16)")

def T_apply(Vflat, v):
    out = np.zeros(SIZE, dtype=np.int64)
    for idx in np.nonzero(Vflat)[0]:
        k, ll = divmod(int(idx), 8)
        out = (out + int(Vflat[idx]) * h1t_apply(k, ll, v)) % P
    return out

W1, W2 = S.weil_pair()
for name, cls in (("W1", W1), ("W2", W2), ("eta", eta), ("eta^3", power(eta, 3))):
    v = dense(cls)
    ok = all(not T_apply(V, v).any() for V in Tbasis)
    print("     T kills %s: %s" % (name, ok))

# (K3) natural objects
def ch_lb(a, c, e):
    return exp_class(add(add(scale(b, a), scale(bh, e)), scale(l, -c)), 16)
nat = {
    "O(beta)": ch_lb(1, 0, 0),
    "O(beta+betahat-ell)": ch_lb(1, 1, 1),
    "O(2beta-betahat+3ell)": ch_lb(2, -3, -1),
    "[B_(1,0)]": S.subtorus(1, 0),
    "[B_(2,1)]": S.subtorus(2, 1),
    "[B_(1,1)]e^{beta}": wedge(S.subtorus(1, 1), ch_lb(1, 0, 0)),
    "O(eta)": exp_class(eta, 16),
}
for name, cls in nat.items():
    v = dense(cls)
    r = rank_mod(ht2_images(v))
    TA = rank_mod([T_apply(V, v) for V in Tbasis])
    print("(K3/K5) %-22s rank HT^2_|ch = %3d   rank T_|ch = %2d  => dim Ann_T(ch) <= %d"
          % (name, r, TA, 16 - TA))

# (K4) corrected characters with each Hankel rank
from math import factorial
def hankel_rank(c):
    mu = [Fr(factorial(m)) * Fr(c[m]) for m in range(9)]
    H = [[mu[j + i] for i in range(3)] for j in range(7)]
    return rank_of([{i: x for i, x in enumerate(row) if x} for row in H])
shapes = {
    "pure (rho=0)": [0] * 9,
    "e^{eta} (rho=1)": [Fr(1, factorial(k)) for k in range(9)],
    "e^{eta}+e^{2eta} (rho=2)": [Fr(1, factorial(k)) + Fr(2 ** k, factorial(k)) for k in range(9)],
    "theta^4 (rho=3)": [0, 0, 0, 0, 1, 0, 0, 0, 0],
    "1+eta+eta^2 (rho=3)": [1, 1, 1, 0, 0, 0, 0, 0, 0],
}
vW = dense(W1)
for name, c in shapes.items():
    g = scale(W1, 1)
    for k in range(9):
        if c[k]:
            g = add(g, power(eta, k), 1, Fr(c[k]))
    rho = hankel_rank(c)
    r = rank_mod(ht2_images(dense(g)))
    print("(K4) %-26s rho = %d   r(gamma) mod p = %3d   formula (4+rho)16-8 = %d"
          % (name, rho, r, (4 + rho) * 16 - 8))
print("time %.1fs" % (time.time() - t0))
