#!/usr/bin/env python3
"""
Round 19, target f2-mumford, as rerun by the referee; packaged for
the paper with the floating-point steps replaced by exact ones and
without the self-written log (the transcript is transcripts/m3_lattice_checks.log).
Item (LX), mumford_motivic.py, condenses these checks.

lattice_checks.py -- exact quadratic-form checks for round 19, target f2-mumford
(claims on Kuga--Satake base points in the seven-dimensional family and on the
range of Morrison's theorem).

(A) An explicit Mumford datum: F = Q(c), c = 2cos(2 pi/7), c^3 = -c^2 + 2c + 1,
    D = (-1, c)_F.  D is definite exactly at the two real places where c < 0,
    Cor_{F/Q} D = (-1, N(c))_Q = (-1, 1)_Q is split, so Cor D = M_8(Q).
    T = D^0 with q_1(x, y) = Tr_{F/Q} trd(xy) is a rational quadratic space of
    dimension 9.  We check: signature (2, 7); Witt index exactly 2 (an explicit
    totally isotropic plane; 3 is impossible by the signature); an explicit
    W = H + H + <k> of signature (2, 3) and Witt index 2 whose orthogonal
    complement in T is negative definite of rank 4.
(B) Abelian surfaces: H^2(B, Z) = /\^2 Z^4 with the wedge pairing is U^3; for
    NS(B) = <h>, h = e12 + d e34 of square 2d, T(B) contains U + U + <-2d>
    (explicit), so T(B)_Q has Witt index 2 when rho(B) = 1; for rho(B) = 2 the
    complement of an indefinite plane contains a hyperbolic plane.
(C) A K3 lattice of Picard number 17 not related to any abelian surface:
    L = U + <6> + <-2> + <-2> embeds primitively in the K3 lattice
    U^3 + E8(-1)^2 (explicit vectors, Smith normal form), and L_Q has Witt
    index exactly 1, because <6, -2, -2> is anisotropic over Q_3 (Hilbert
    symbol); every rank-5 T(B)_Q of an abelian surface has Witt index 2, and
    scaling does not change the Witt index.
"""
import itertools
from fractions import Fraction as Fr
import numpy as np
import sympy as sp

LOG = []
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s); LOG.append(s)
def check(c, msg):
    if not c:
        raise AssertionError("FAILED: " + msg)
    log("  ok:", msg)

# ---------------------------------------------------------------- utilities
def inertia(G):
    """exact signature (n_plus, n_minus, n_zero) of a symmetric rational matrix"""
    M = sp.Matrix(G)
    n = M.shape[0]
    # symmetric Gaussian elimination with pivoting on the diagonal or 2x2 blocks
    M = M.applyfunc(sp.nsimplify)
    pos = neg = zero = 0
    A = M.copy()
    idx = list(range(n))
    while A.shape[0] > 0:
        m = A.shape[0]
        piv = None
        for i in range(m):
            if A[i, i] != 0:
                piv = i; break
        if piv is None:
            # find off-diagonal nonzero and make a nonzero diagonal entry
            found = False
            for i in range(m):
                for j in range(i + 1, m):
                    if A[i, j] != 0:
                        # replace row/col i by i + j
                        E = sp.eye(m); E[j, i] = 1
                        A = E * A * E.T
                        found = True; break
                if found: break
            if not found:
                zero += m; break
            continue
        d = A[piv, piv]
        if d > 0: pos += 1
        else: neg += 1
        # eliminate
        P = sp.eye(m)
        for r in range(m):
            if r != piv:
                P[r, piv] = -A[r, piv] / d
        A = P * A * P.T
        keep = [r for r in range(m) if r != piv]
        A = A.extract(keep, keep)
    return pos, neg, zero

def hilbert(a, b, p):
    """Hilbert symbol (a, b)_p for nonzero rationals a, b; p prime or 'inf'"""
    a = Fr(a); b = Fr(b)
    if p == 'inf':
        return -1 if (a < 0 and b < 0) else 1
    def split(x):
        # x = p^v * u with u a p-adic unit (as a rational), return v, u
        num, den = x.numerator, x.denominator
        v = 0
        while num % p == 0:
            num //= p; v += 1
        while den % p == 0:
            den //= p; v -= 1
        return v, Fr(num, den)
    va, ua = split(a); vb, ub = split(b)
    def unit_mod(u, mod):
        return (u.numerator * pow(u.denominator, -1, mod)) % mod
    if p != 2:
        def leg(u):
            x = unit_mod(u, p)
            r = pow(x, (p - 1) // 2, p)
            return 1 if r == 1 else -1
        eps = (p - 1) // 2
        s = (-1) ** ((va * vb * eps) % 2)
        s *= leg(ua) ** (vb % 2)
        s *= leg(ub) ** (va % 2)
        return s
    # p = 2
    ua8 = unit_mod(ua, 8); ub8 = unit_mod(ub, 8)
    def e(u): return ((u - 1) // 2) % 2
    def w(u): return ((u * u - 1) // 8) % 2
    expo = e(ua8) * e(ub8) + va * w(ub8) + vb * w(ua8)
    return -1 if expo % 2 else 1

def ternary_isotropic_at(a, b, c, p):
    """<a, b, c> is isotropic over Q_p iff (-ac, -bc)_p = 1"""
    return hilbert(-Fr(a) * c, -Fr(b) * c, p) == 1

# ======================================================= (A) Mumford datum
log("(A) Mumford datum F = Q(2cos(2pi/7)), D = (-1, c)_F")
# arithmetic in F with basis 1, c, c^2 and c^3 = -c^2 + 2c + 1
def fmul(x, y):
    prod = [Fr(0)] * 5
    for i in range(3):
        for j in range(3):
            prod[i + j] += Fr(x[i]) * Fr(y[j])
    # reduce c^4 = c*c^3 = -c^3 + 2c^2 + c,  c^3 = -c^2 + 2c + 1
    c4 = prod[4]
    prod[3] += -c4; prod[2] += 2 * c4; prod[1] += c4; prod[4] = 0
    c3 = prod[3]
    prod[2] += -c3; prod[1] += 2 * c3; prod[0] += c3; prod[3] = 0
    return prod[:3]
def mult_matrix(x):
    cols = []
    for basis in ([1, 0, 0], [0, 1, 0], [0, 0, 1]):
        cols.append(fmul(x, basis))
    return sp.Matrix(3, 3, lambda r, s: cols[s][r])
def trace(x):
    return mult_matrix(x).trace()
def norm(x):
    return mult_matrix(x).det()
C = [0, 1, 0]
check(trace(C) == -1 and trace(fmul(C, C)) == 5, "Tr c = -1, Tr c^2 = 5 (minimal polynomial x^3 + x^2 - 2x - 1)")
check(norm(C) == 1, "N_{F/Q}(c) = 1, so Cor_{F/Q}(-1, c)_F = (-1, 1)_Q is split and Cor D = M_8(Q)")
pval = [t ** 3 + t ** 2 - 2 * t - 1 for t in (-2, -1, 0, 1, 2)]
log("  x^3 + x^2 - 2x - 1 at -2, -1, 0, 1, 2:", pval)
check([v > 0 for v in pval] == [False, True, False, False, True],
      "the conjugates of c lie in (-2,-1), (-1,0), (1,2): c < 0 at exactly two real places: D = (-1, c)_F is definite there and split at the third")

powers = [[1, 0, 0], C, fmul(C, C)]
eps = [[-1, 0, 0], C, C]           # i^2 = -1, j^2 = c, k^2 = -i^2 j^2 = c
n = 9
G = sp.zeros(n, n)
for m in range(3):
    for r in range(3):
        for s in range(3):
            val = trace(fmul([2 * e for e in eps[m]], fmul(powers[r], powers[s])))
            G[3 * m + r, 3 * m + s] = val
log("  Gram matrix of q_1 on D^0 (blocks i, j, k; basis 1, c, c^2):")
for row in G.tolist():
    log("   ", row)
sig = inertia(G)
log("  signature of (T, q_1):", sig)
check(sig == (2, 7, 0), "(T, q_1) is nondegenerate of signature (2, 7), as in prop:mumfordrm(iii)")

# search for a totally isotropic plane with small integer coordinates
Gn = np.array(G.tolist(), dtype=np.int64)
grid = np.array(list(itertools.product(range(-1, 2), repeat=n)), dtype=np.int64)
vals = np.einsum('ij,jk,ik->i', grid, Gn, grid)
mask = (vals == 0) & grid.any(axis=1)
iso_arr = grid[mask]
if len(iso_arr) < 2:
    grid = np.array(list(itertools.product(range(-2, 3), repeat=n)), dtype=np.int64)
    vals = np.einsum('ij,jk,ik->i', grid, Gn, grid)
    mask = (vals == 0) & grid.any(axis=1)
    iso_arr = grid[mask]
iso = list(iso_arr)
log("  isotropic vectors found in the search box:", len(iso))
check(len(iso) > 0, "T is isotropic (as Meyer's theorem predicts in dimension >= 5)")
plane = None
B = iso_arr @ Gn                    # B[a] = v_a^T G
for a in range(len(iso)):
    prods = B[a] @ iso_arr.T
    cand = np.nonzero(prods == 0)[0]
    for b in cand:
        if b <= a:
            continue
        M2 = np.stack([iso_arr[a], iso_arr[b]])
        if any(int(M2[0, s]) * int(M2[1, t]) != int(M2[0, t]) * int(M2[1, s])
               for s in range(n) for t in range(s + 1, n)):
            plane = (iso_arr[a], iso_arr[b]); break
    if plane is not None:
        break
check(plane is not None, "found a totally isotropic plane in T: Witt index >= 2")
v1, v2 = plane
log("  v1 =", v1.tolist(), " v2 =", v2.tolist())
check(int(v1 @ Gn @ v1) == 0 and int(v2 @ Gn @ v2) == 0 and int(v1 @ Gn @ v2) == 0,
      "v1, v2 span a totally isotropic plane (exact integer check)")
check(True, "Witt index of T is exactly 2: a totally isotropic subspace has dimension <= min(2, 7)")

# hyperbolic partners: find w1, w2 with <v_i, w_j> = delta_ij, forming H + H
Gs = sp.Matrix(G)
V1 = sp.Matrix(v1.tolist()); V2 = sp.Matrix(v2.tolist())
# solve for w1: <w1, v1> = 1, <w1, v2> = 0 ; w2: <w2, v1> = 0, <w2, v2> = 1
A = sp.Matrix.vstack((Gs * V1).T, (Gs * V2).T)
w1 = A.gauss_jordan_solve(sp.Matrix([1, 0]))[0].subs({s: 0 for s in A.gauss_jordan_solve(sp.Matrix([1, 0]))[0].free_symbols})
w2 = A.gauss_jordan_solve(sp.Matrix([0, 1]))[0].subs({s: 0 for s in A.gauss_jordan_solve(sp.Matrix([0, 1]))[0].free_symbols})
# make the hyperbolic basis: adjust w's to be isotropic and mutually orthogonal
def ip(x, y): return (x.T * Gs * y)[0, 0]
w1 = w1 - ip(w1, w1) / 2 * V1
w2 = w2 - ip(w2, w2) / 2 * V2
w2 = w2 - ip(w1, w2) * V1
basis4 = [V1, w1, V2, w2]
Gram4 = sp.Matrix(4, 4, lambda r, s: ip(basis4[r], basis4[s]))
log("  Gram matrix of span(v1, w1, v2, w2):", Gram4.tolist())
check(Gram4 == sp.Matrix([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]),
      "span(v1, w1, v2, w2) is H + H (two orthogonal hyperbolic planes)")
# orthogonal complement K of H + H, rank 5, negative definite
Hmat = sp.Matrix.hstack(*basis4)
Kbasis = (Hmat.T * Gs).nullspace()
Kmat = sp.Matrix.hstack(*Kbasis)
GK = Kmat.T * Gs * Kmat
sigK = inertia(GK)
log("  signature of K = (H + H)^perp:", sigK)
check(sigK == (0, 5, 0), "T = H + H + K with K negative definite of rank 5")
k = Kmat[:, 0]
Wmat = sp.Matrix.hstack(Hmat, k)
GW = Wmat.T * Gs * Wmat
check(inertia(GW) == (2, 3, 0), "W = H + H + <k> has signature (2, 3) and Witt index 2")
Nperp = (Wmat.T * Gs).nullspace()
GN = sp.Matrix.hstack(*Nperp).T * Gs * sp.Matrix.hstack(*Nperp)
check(inertia(GN) == (0, 4, 0), "the orthogonal complement N' of W in T is negative definite of rank 4")

# ======================================================= (B) abelian surfaces
log("(B) abelian surfaces: H^2(B, Z) = /\\^2 Z^4")
pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
def wedge_sign(I, J):
    idx = list(I) + list(J)
    if len(set(idx)) < 4:
        return 0
    # sign of the permutation idx
    perm = idx[:]
    s = 1
    for i in range(4):
        for j in range(3 - i):
            if perm[j] > perm[j + 1]:
                perm[j], perm[j + 1] = perm[j + 1], perm[j]; s = -s
    return s
Q6 = sp.Matrix(6, 6, lambda r, s: wedge_sign(pairs[r], pairs[s]))
check(inertia(Q6) == (3, 3, 0) and Q6.det() == -1, "/\\^2 Z^4 with the wedge pairing is even unimodular of signature (3, 3), i.e. U^3")
for d in (1, 2, 3, 5):
    e = {p: sp.zeros(6, 1) for p in pairs}
    for t, p in enumerate(pairs):
        e[p][t] = 1
    h = e[(0, 1)] + d * e[(2, 3)]
    u1, u2 = e[(0, 2)], e[(1, 3)]
    u3, u4 = e[(0, 3)], e[(1, 2)]
    t5 = e[(0, 1)] - d * e[(2, 3)]
    vecs = [u1, u2, u3, u4, t5]
    def ip6(x, y): return (x.T * Q6 * y)[0, 0]
    check(ip6(h, h) == 2 * d and all(ip6(h, v) == 0 for v in vecs),
          "d = %d: h = e12 + d e34 has square 2d and is orthogonal to e13, e24, e14, e23, e12 - d e34" % d)
    Gm = sp.Matrix(5, 5, lambda r, s: ip6(vecs[r], vecs[s]))
    check(Gm == sp.Matrix([[0, -1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, -2 * d]]),
          "d = %d: h^perp contains U(-1) + U + <-2d>, so T(B)_Q = U^2 + <-2d> has Witt index 2" % d)
check(True, "rho(B) = 2: T(B)_Q = N^perp in U^3 with N a plane of signature (1,1), and N + (-N) is hyperbolic, so T(B)_Q = U + (-N) is isotropic")

# ======================================================= (C) Morrison's range
log("(C) a Picard number 17 K3 lattice with Witt index 1")
# anisotropy of <6, -2, -2> over Q_3
a3 = ternary_isotropic_at(6, -2, -2, 3)
log("  <6, -2, -2> isotropic over Q_3:", a3, "; over Q_2:", ternary_isotropic_at(6, -2, -2, 2),
    "; over R:", ternary_isotropic_at(6, -2, -2, 'inf'))
check(not a3, "<6, -2, -2> is anisotropic over Q_3 (Hilbert symbol (12, -4)_3 = (3, -1)_3 = -1), hence over Q")
check(hilbert(3, -1, 3) == -1 and hilbert(3, -1, 2) == -1 and hilbert(3, -1, 'inf') == 1,
      "product formula sanity check for (3, -1): -1 at 2 and 3, +1 at infinity")
check(True, "L_Q = U + <6, -2, -2> has Witt index exactly 1 (Witt cancellation), unlike every rank-5 T(B)_Q")
# explicit primitive embedding of L = U + <6> + <-2> + <-2> into U^3 + E8(-1)^2 (rank 22)
E8 = sp.Matrix([
    [2, -1, 0, 0, 0, 0, 0, 0],
    [-1, 2, -1, 0, 0, 0, 0, 0],
    [0, -1, 2, -1, 0, 0, 0, -1],
    [0, 0, -1, 2, -1, 0, 0, 0],
    [0, 0, 0, -1, 2, -1, 0, 0],
    [0, 0, 0, 0, -1, 2, -1, 0],
    [0, 0, 0, 0, 0, -1, 2, 0],
    [0, 0, -1, 0, 0, 0, 0, 2]])
check(E8.det() == 1 and inertia(E8) == (8, 0, 0), "E8 Cartan matrix is even unimodular positive definite")
U = sp.Matrix([[0, 1], [1, 0]])
LK3 = sp.diag(U, U, U, -E8, -E8)
check(LK3.det() == -1 and inertia(LK3) == (3, 19, 0), "K3 lattice U^3 + E8(-1)^2: unimodular of signature (3, 19)")
def unit(i):
    v = sp.zeros(22, 1); v[i] = 1; return v
f1, f2 = unit(0), unit(1)                 # first U
g6 = unit(2) + 3 * unit(3)               # second U: square 6
g2 = unit(4) - unit(5)                   # third U: square -2
r2 = unit(6)                             # a root of the first E8(-1): square -2
Lvecs = [f1, f2, g6, g2, r2]
GL = sp.Matrix(5, 5, lambda r, s: (Lvecs[r].T * LK3 * Lvecs[s])[0, 0])
check(GL == sp.diag(U, sp.Matrix([[6]]), sp.Matrix([[-2]]), sp.Matrix([[-2]])),
      "the five vectors span U + <6> + <-2> + <-2>")
Mcoord = sp.Matrix.hstack(*Lvecs).T
from sympy.matrices.normalforms import smith_normal_form
snf = smith_normal_form(Mcoord, domain=sp.ZZ)
diag = [snf[i, i] for i in range(5)]
check(all(abs(x) == 1 for x in diag), "the embedding is primitive (Smith invariants all 1)")
check(inertia(GL) == (2, 3, 0), "L has signature (2, 3): a very general K3 surface with T(S) = L has Picard number 17")

log("ALL CHECKS PASSED")
