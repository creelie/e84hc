"""
tspace.py -- T = T_[A] D_{4,4} inside H^1(T_A) at the split member tau = iI,
mod p: v in Hom(H^{1,0}, H^{0,1}) commuting with M and killing eta.
"""
import numpy as np
from contraction import *


def M_gen(g, d):
    j = g + 1
    if j <= 4:
        return {xig(4 + j): P - 1}
    if j <= 8:
        return {xig(j - 4): 1}
    jj = j - 8
    if jj <= 4:
        return {xg(4 + jj): (P - d) % P}
    return {xg(jj - 4): d % P}


def M_form(f, d):
    out = {}
    for g, c in f.items():
        for g2, c2 in M_gen(g, d).items():
            out[g2] = (out.get(g2, 0) + c * c2) % P
    return {k: v for k, v in out.items() if v}


def coords(f, basis):
    A = np.array([[bv.get(g, 0) for bv in basis] for g in range(16)], dtype=np.int64)
    rhs = np.array([f.get(g, 0) for g in range(16)], dtype=np.int64)
    Mx = np.concatenate([A, rhs[:, None]], axis=1) % P
    r = 0
    for c in range(8):
        nz = np.nonzero(Mx[r:, c])[0]
        pr = r + nz[0]
        Mx[[r, pr]] = Mx[[pr, r]]
        Mx[r] = Mx[r] * pow(int(Mx[r, c]), P - 2, P) % P
        for rr in range(16):
            if rr != r and Mx[rr, c]:
                Mx[rr] = (Mx[rr] - Mx[rr, c] * Mx[r]) % P
        r += 1
    assert not Mx[8:, 8].any()
    return [int(Mx[k, 8]) for k in range(8)]


def nullspace(A):
    Mx = A.copy() % P
    nr, nc = Mx.shape
    r = 0
    pivcols = []
    for c in range(nc):
        if r == nr:
            break
        nz = np.nonzero(Mx[r:, c])[0]
        if not len(nz):
            continue
        pr = r + nz[0]
        Mx[[r, pr]] = Mx[[pr, r]]
        Mx[r] = Mx[r] * pow(int(Mx[r, c]), P - 2, P) % P
        oth = np.nonzero(Mx[:, c])[0]
        oth = oth[oth != r]
        if len(oth):
            Mx[oth] = (Mx[oth] - Mx[oth, c][:, None] * Mx[r][None, :]) % P
        pivcols.append(c)
        r += 1
    free = [c for c in range(nc) if c not in pivcols]
    basis = []
    for f in free:
        x = np.zeros(nc, dtype=np.int64)
        x[f] = 1
        for i, pc in enumerate(pivcols):
            x[pc] = (-Mx[i, f]) % P
        basis.append(x)
    return basis


def compute_T(d, eta_cls):
    Mh = np.array([coords(M_form(h, d), HOL) for h in HOL], dtype=np.int64)
    Ma = np.array([coords(M_form(a, d), ANTI) for a in ANTI], dtype=np.int64)
    eqs = []
    for m in range(8):
        for ll in range(8):
            row = np.zeros(64, dtype=np.int64)
            for k in range(8):
                row[k * 8 + ll] = (row[k * 8 + ll] + Mh[m, k]) % P
            for lp in range(8):
                row[m * 8 + lp] = (row[m * 8 + lp] - Ma[lp, ll]) % P
            eqs.append(row)
    veta = dense(eta_cls)
    E_eta = np.array([h1t_apply(k, ll, veta) for k in range(8) for ll in range(8)],
                     dtype=np.int64).T
    for r_ in np.nonzero(E_eta.any(axis=1))[0]:
        eqs.append(E_eta[r_])
    return nullspace(np.array(eqs, dtype=np.int64) % P)


def T_apply(Vflat, v):
    out = np.zeros(SIZE, dtype=np.int64)
    for idx in np.nonzero(Vflat)[0]:
        k, ll = divmod(int(idx), 8)
        out = (out + int(Vflat[idx]) * h1t_apply(k, ll, v)) % P
    return out
