"""
contraction.py -- the action of HT^*(A) on H^*(A,C) for A = X x Xhat, n = 4,
at the member with period matrix tau = i*I (X = E_i^4 with product principal
polarisation), modulo a prime p = 1 mod 4 with i -> sqrt(-1) mod p.

Why one member suffices for classes of H_A: H^1(A) = U (x) Q^2, H^{1,0}(A) =
W0 (x) C^2 with W0 = H^{1,0}(X) a positive Lagrangian of (U_C, psi), the K-action
is 1 (x) M0, and eta, the Weil classes and every class of H_A are
Sp(U)-invariant.  Sp(U_R) acts transitively on positive Lagrangians, commutes
with M and fixes H_A pointwise, and it carries the contraction action at one
member to that at another.  So every rank below (of contraction of HT^2 or of
T = T_[A] D_{4,4} into classes of H_A) is the same at every split member
X x Xhat with X any principally polarised fourfold.

Ranks mod p are LOWER bounds for ranks over Q(i) (entries have no p in their
denominators).  Upper bounds are supplied separately (theory or exact kernels).

Generators g_0..g_15 = x_1..x_8, xi_1..xi_8 (bit positions as in ext.py).
H^{1,0}: e_j = x_j + i x_{4+j},  e'_j = xi_j + i xi_{4+j}   (j = 1..4)
(checked: M preserves H^{1,0}, beta, betahat, ell are of type (1,1)).
"""
import numpy as np
from fractions import Fraction as Fr

P = 1000000009           # prime, = 1 mod 4
NB = 16
SIZE = 1 << NB


def _sqrtm1(p):
    # find i with i^2 = -1 mod p
    for a in range(2, 1000):
        c = pow(a, (p - 1) // 4, p)
        if c * c % p == p - 1:
            return c
    raise ValueError
I = _sqrtm1(P)


def md(x):
    """Fraction / int -> residue mod P"""
    x = Fr(x)
    return x.numerator % P * pow(x.denominator % P, P - 2, P) % P


# precomputed index maps for elementary wedge / contraction by generator g
_masks = np.arange(SIZE, dtype=np.int64)
_pc_below = {}
_W = {}
_C = {}
for g in range(NB):
    bit = 1 << g
    below = _masks & (bit - 1)
    # popcount parity of 'below'
    par = np.zeros(SIZE, dtype=np.int64)
    t = below.copy()
    while t.any():
        par ^= (t & 1)
        t >>= 1
    sgn = np.where(par == 1, P - 1, 1).astype(np.int64)
    without = _masks[(_masks & bit) == 0]
    withg = _masks[(_masks & bit) != 0]
    _W[g] = (without, without | bit, sgn[without])
    _C[g] = (withg, withg ^ bit, sgn[withg])


def wedge_gen(g, v):
    src, dst, s = _W[g]
    out = np.zeros(SIZE, dtype=np.int64)
    out[dst] = v[src] * s % P
    return out


def contr_gen(g, v):
    src, dst, s = _C[g]
    out = np.zeros(SIZE, dtype=np.int64)
    out[dst] = v[src] * s % P
    return out


def op_apply(op, v):
    """op = ('w' or 'c', {g: coeff mod P})"""
    kind, coeffs = op
    out = np.zeros(SIZE, dtype=np.int64)
    f = wedge_gen if kind == 'w' else contr_gen
    for g, c in coeffs.items():
        if c % P:
            out = (out + c * f(g, v)) % P
    return out


def dense(cls):
    """dict {mask: Fraction/int} -> dense vector mod P"""
    v = np.zeros(SIZE, dtype=np.int64)
    for k, c in cls.items():
        v[k] = md(c)
    return v


# ---- H^{1,0}, H^{0,1}, tangent vectors (as coefficient dicts over generators)
def xg(j):
    return j - 1


def xig(j):
    return 8 + j - 1


def forms():
    """lists hol (8 forms of type (1,0)) and antihol (8 of type (0,1)),
    each a dict {generator index: coeff mod P}"""
    hol, anti = [], []
    for j in range(1, 5):
        hol.append({xg(j): 1, xg(4 + j): I})
        anti.append({xg(j): 1, xg(4 + j): P - I})
    for j in range(1, 5):
        hol.append({xig(j): 1, xig(4 + j): I})
        anti.append({xig(j): 1, xig(4 + j): P - I})
    return hol, anti


def tangents():
    """dual vectors d_k with d_k(hol_l) = delta_kl, d_k(anti_l) = 0, as
    coefficient dicts over the dual generators g^*: d = (g_a^* - i g_b^*)/2"""
    inv2 = pow(2, P - 2, P)
    out = []
    for j in range(1, 5):
        out.append({xg(j): inv2, xg(4 + j): (P - I) * inv2 % P})
    for j in range(1, 5):
        out.append({xig(j): inv2, xig(4 + j): (P - I) * inv2 % P})
    return out


HOL, ANTI = forms()
TAN = tangents()
HT1 = [('w', a) for a in ANTI] + [('c', t) for t in TAN]    # 16 operators


def ht2_images(v):
    """the 120 vectors xi _| v for xi = o_a o_b, a < b, in the basis of HT^2"""
    first = [op_apply(o, v) for o in HT1]
    out = []
    for a in range(16):
        for b in range(a + 1, 16):
            out.append(op_apply(HT1[a], first[b]))
    return out


def h1t_ops():
    """the 64 operators v_kl = w(anti_l) c(tan_k) spanning H^1(T_A)"""
    return [(k, l) for k in range(8) for l in range(8)]


def h1t_apply(k, l, v):
    return op_apply(('w', ANTI[l]), op_apply(('c', TAN[k]), v))


def rank_mod(rows):
    """rank mod P of a list of dense vectors (numpy int64), by elimination
    restricted to the nonzero columns"""
    if not rows:
        return 0
    M = np.array(rows, dtype=np.int64) % P
    cols = np.nonzero(M.any(axis=0))[0]
    M = M[:, cols].copy()
    r = 0
    nr, nc = M.shape
    for c in range(nc):
        if r == nr:
            break
        piv = None
        nzr = np.nonzero(M[r:, c])[0]
        if len(nzr) == 0:
            continue
        piv = r + nzr[0]
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), P - 2, P)
        M[r] = M[r] * inv % P
        others = np.nonzero(M[:, c])[0]
        others = others[others != r]
        if len(others):
            f = M[others, c][:, None]
            M[others] = (M[others] - f * M[r][None, :]) % P
        r += 1
    return r


def span_basis(rows):
    """a list of independent rows (mod P) spanning the same space"""
    if not rows:
        return []
    M = np.array(rows, dtype=np.int64) % P
    cols = np.nonzero(M.any(axis=0))[0]
    A = M[:, cols].copy()
    keep = []
    r = 0
    basis_rows = []
    # incremental: test each row
    red = []   # list of (pivot col, row) normalised
    for idx in range(A.shape[0]):
        row = A[idx].copy()
        for pc, pr in red:
            if row[pc]:
                row = (row - row[pc] * pr) % P
        nz = np.nonzero(row)[0]
        if len(nz):
            pc = nz[0]
            row = row * pow(int(row[pc]), P - 2, P) % P
            red.append((pc, row))
            keep.append(idx)
    return [rows[i] for i in keep]
