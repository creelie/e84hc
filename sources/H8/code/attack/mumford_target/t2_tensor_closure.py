#!/usr/bin/env python3
"""
t2_tensor_closure.py  (round 12, track T2)

Question: do the Hodge classes of X x X (X a Mumford fourfold, Hodge group
G = SL(2)^3 over Q-bar acting on V = V1 (x) V2 (x) V3) generate, under the
operations that preserve algebraicity (exterior products, pull-back along
homomorphisms = permutation/linear substitution of tensor legs, and
push-forward = contraction of two legs with the invariant form psi^{-1}),
all Hodge classes of all powers X^n?

Model.  G-invariant tensors in V^{(x)N} are I_N (x) I_N (x) I_N, where
I_N = (V_k^{(x)N})^{SL2} has the basis of non-crossing perfect matchings
(dimension Catalan(N/2)); the symmetric group S_N permutes legs diagonally,
and contraction with psi^{-1} = eps^{-1} (x) eps^{-1} (x) eps^{-1} acts
factorwise.  All matrices on I_N are computed exactly (integers/Fractions)
from explicit vectors in (Q^2)^{(x)N}.  Spans of many tensors are computed by
rank mod a prime p: rank mod p <= rank over Q for integral vectors, so a
FULL rank mod p proves fullness over Q; non-fullness claims are proved by an
exact invariant (the S_4-trivial isotypic projection), not by ranks mod p.

 (1) dim (V^{(x)4})^G = 8, and as an S_4-module it is (4) + (1^4) + 3 (2,2).
     The trivial summand is spanned by one tensor Det (Cayley's
     hyperdeterminant of the 2x2x2 tensor, a G-invariant in Sym^4 V).
 (2) T4_0 := S_4-span of the Hodge classes of X x X of degree 4 (the
     G-invariants of wedge^a V (x) wedge^b V, a+b = 4, placed on legs
     1..a | a+1..4) and of psi (x) psi: dimension 7, and it is exactly the
     kernel of the S_4-symmetriser.  So Det is NOT in it: the (1,1,1,1)
     Kunneth component of Hdg^2(X^4) is not reached by pull-backs and cup
     products of Hodge classes of X x X.  (Exact.)
 (3) Contractions of T4_0 (x) T4_0 along two disjoint pairs of legs (a
     composite of correspondences) have nonzero symmetriser image: Det is
     reached, and T4 := everything generated = all 8 dimensions.
 (4) With T4 full, the S_6-span of T4 (x) psi and of the single-pair
     contractions of T4 (x) T4 is all of (V^{(x)6})^G, of dimension 125.
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations
import numpy as np
import sympy

P = 1000003
PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("PASS " if cond else "FAIL ") + name)


# ---------------- non-crossing matchings and their vectors
def nc_matchings(pts):
    if not pts:
        return [[]]
    a = pts[0]
    out = []
    for idx in range(1, len(pts), 2):
        b = pts[idx]
        inside = pts[1:idx]
        outside = pts[idx + 1:]
        for m1 in nc_matchings(inside):
            for m2 in nc_matchings(outside):
                out.append([(a, b)] + m1 + m2)
    return out


def matching_vector(m, N):
    v = np.zeros(2 ** N, dtype=np.int64)
    for idx in range(2 ** N):
        bits = [(idx >> (N - 1 - t)) & 1 for t in range(N)]
        val = 1
        for (a, b) in m:
            if bits[a] == 0 and bits[b] == 1:
                pass
            elif bits[a] == 1 and bits[b] == 0:
                val = -val
            else:
                val = 0
                break
        v[idx] = val
    return v


class Inv:
    """SL2-invariants of (Q^2)^{(x)N}"""
    def __init__(self, N):
        self.N = N
        self.m = nc_matchings(list(range(N)))
        self.C = len(self.m)
        self.B = np.array([matching_vector(m, N) for m in self.m], dtype=np.int64).T  # 2^N x C
        # exact left inverse via a set of C independent rows
        M = sympy.Matrix(self.B.tolist())
        _, piv = M.T.rref()
        self.rows = list(piv)
        sub = sympy.Matrix(self.B[self.rows, :].tolist())
        self.subinv = sub.inv()

    def coords(self, v):
        """v in the span (exact check) -> Fraction coordinates"""
        c = self.subinv * sympy.Matrix([int(v[r]) for r in self.rows])
        c = [Fr(int(sympy.fraction(x)[0]), int(sympy.fraction(x)[1])) for x in c]
        recon = [sum(c[j] * int(self.B[i, j]) for j in range(self.C)) for i in range(self.B.shape[0])]
        assert all(recon[i] == int(v[i]) for i in range(len(recon))), "vector not in the invariant span"
        return c


INV = {N: Inv(N) for N in (0, 2, 4, 6, 8)} if False else None


def build_inv():
    d = {}
    for N in (2, 4, 6, 8):
        d[N] = Inv(N)
    return d


INV = build_inv()
check("Catalan dimensions 1,2,5,14", [INV[N].C for N in (2, 4, 6, 8)] == [1, 2, 5, 14])


def perm_vector(v, N, perm):
    """leg t of the input goes to leg perm[t] of the output"""
    out = np.zeros_like(v)
    for idx in range(2 ** N):
        bits = [(idx >> (N - 1 - t)) & 1 for t in range(N)]
        nb = [0] * N
        for t in range(N):
            nb[perm[t]] = bits[t]
        j = 0
        for t in range(N):
            j = 2 * j + nb[t]
        out[j] = v[idx]
    return out


def rho(N, perm):
    I = INV[N]
    cols = [I.coords(perm_vector(I.B[:, c], N, perm)) for c in range(I.C)]
    return np.array(cols, dtype=object).T  # C x C


def contract_vector(v, N, pairs):
    """contract the given disjoint pairs (a,b) of legs with eps: e1(x)e2 -> 1, e2(x)e1 -> -1"""
    used = set(x for p in pairs for x in p)
    rest = [t for t in range(N) if t not in used]
    M = len(rest)
    out = np.zeros(2 ** M, dtype=np.int64)
    for idx in range(2 ** N):
        if v[idx] == 0:
            continue
        bits = [(idx >> (N - 1 - t)) & 1 for t in range(N)]
        val = int(v[idx])
        for (a, b) in pairs:
            if bits[a] == 0 and bits[b] == 1:
                pass
            elif bits[a] == 1 and bits[b] == 0:
                val = -val
            else:
                val = 0
                break
        if val == 0:
            continue
        j = 0
        for t in rest:
            j = 2 * j + bits[t]
        out[j] += val
    return out


def kappa(N, pairs):
    I, J = INV[N], INV[N - 2 * len(pairs)]
    cols = [J.coords(contract_vector(I.B[:, c], N, pairs)) for c in range(I.C)]
    return np.array(cols, dtype=object).T  # C_{N-2k} x C_N


def concat_index(N, M):
    """index map I_N x I_M -> I_{N+M} (concatenated non-crossing matchings stay non-crossing)"""
    I, J, K = INV[N], INV[M], INV[N + M]
    pos = {tuple(sorted(m)): i for i, m in enumerate(K.m)}
    table = np.zeros((I.C, J.C), dtype=np.int64)
    for a, ma in enumerate(I.m):
        for b, mb in enumerate(J.m):
            key = tuple(sorted(ma + [(x + N, y + N) for (x, y) in mb]))
            table[a, b] = pos[key]
    return table


# ---------------- tensors in I_N^{(x)3}, stored as object arrays (exact) or int mod P
def act3(Mat, T):
    """apply the same C'xC matrix on each of the three axes"""
    T = np.tensordot(Mat, T, axes=([1], [0]))
    T = np.tensordot(Mat, T, axes=([1], [1])).transpose(1, 0, 2)
    T = np.tensordot(Mat, T, axes=([1], [2])).transpose(1, 2, 0)
    return T


def tensor_prod(T, U, N, M):
    tab = concat_index(N, M)
    C = INV[N + M].C
    out = np.zeros((C, C, C), dtype=object)
    for a in range(T.shape[0]):
        for b in range(T.shape[1]):
            for c in range(T.shape[2]):
                if T[a, b, c] == 0:
                    continue
                for a2 in range(U.shape[0]):
                    for b2 in range(U.shape[1]):
                        for c2 in range(U.shape[2]):
                            if U[a2, b2, c2] == 0:
                                continue
                            out[tab[a, a2], tab[b, b2], tab[c, c2]] += T[a, b, c] * U[a2, b2, c2]
    return out


def fr_to_mod(x):
    x = Fr(x)
    return (x.numerator % P) * pow(x.denominator % P, P - 2, P) % P


def vec_mod(T):
    return np.array([fr_to_mod(x) for x in T.reshape(-1)], dtype=np.int64)


class Span:
    """row-echelon span mod P (rank mod P <= rank over Q)"""
    def __init__(self, n):
        self.n = n
        self.rows = []  # (pivot, row)

    def reduce(self, v):
        v = v % P
        for piv, row in self.rows:
            if v[piv]:
                v = (v - v[piv] * row) % P
        return v

    def add(self, v):
        v = self.reduce(v)
        nz = np.nonzero(v)[0]
        if len(nz) == 0:
            return False
        piv = nz[0]
        v = (v * pow(int(v[piv]), P - 2, P)) % P
        for t, (pv, row) in enumerate(self.rows):
            if row[piv]:
                self.rows[t] = (pv, (row - row[piv] * v) % P)
        self.rows.append((piv, v))
        return True

    def dim(self):
        return len(self.rows)


def exact_rank(vectors):
    if not vectors:
        return 0
    M = sympy.Matrix([[sympy.Rational(x.numerator, x.denominator) if isinstance(x, Fr) else x for x in v]
                      for v in vectors])
    return M.rank()


# ---------------- N = 4
N = 4
C4 = INV[4].C
adj4 = [rho(4, [1, 0, 2, 3]), rho(4, [0, 2, 1, 3]), rho(4, [0, 1, 3, 2])]
allperm4 = {p: rho(4, list(p)) for p in permutations(range(4))}


def sign(p):
    s, p = 1, list(p)
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s = -s
    return s


# full invariant space basis of I4^(x)3
full4 = []
for a in range(C4):
    for b in range(C4):
        for c in range(C4):
            T = np.zeros((C4, C4, C4), dtype=object)
            T[a, b, c] = 1
            full4.append(T)
check("dim (V^(x)4)^G = 8", len(full4) == 8)

# S_4 characters on (V^(x)4)^G: trace of rho(p)^{(x)3}
def trace3(M):
    t = sum(M[i, i] for i in range(M.shape[0]))
    return t ** 3


classes = {"e": (0, 1, 2, 3), "(12)": (1, 0, 2, 3), "(12)(34)": (1, 0, 3, 2), "(123)": (1, 2, 0, 3),
           "(1234)": (1, 2, 3, 0)}
chars = {k: trace3(allperm4[v]) for k, v in classes.items()}
print("character of S_4 on (V^(x)4)^G:", chars)
# (4)+(1^4)+3(2,2): e:1+1+6=8, (12):1-1+0=0, (12)(34):1+1+6=8, (123):1+1-3=-1, (1234):1-1+0=0
check("S_4-module (V^(x)4)^G = (4) + (1^4) + 3 (2,2)",
      chars == {"e": 8, "(12)": 0, "(12)(34)": 8, "(123)": -1, "(1234)": 0})

# symmetriser and the tensor Det spanning the trivial summand
Sym = sum(allperm4.values()) / 24
Sym = np.array([[Fr(x) for x in row] for row in Sym], dtype=object)
Det = None
for T in full4:
    D = act3(Sym, T) if False else None
# symmetriser on tensors: average of p acting diagonally
def sym_tensor(T):
    out = np.zeros_like(T)
    for p, M in allperm4.items():
        out = out + act3(M, T)
    return out * Fr(1, 24)


sym_images = [sym_tensor(T) for T in full4]
r_sym = exact_rank([list(t.reshape(-1)) for t in sym_images])
check("the S_4-trivial part of (V^(x)4)^G is one-dimensional (the hyperdeterminant)", r_sym == 1)
Det = next(t for t in sym_images if any(x != 0 for x in t.reshape(-1)))


def alt_proj(a, b):
    """projector Alt_{1..a} (x) Alt_{a+1..a+b} on I4^(x)3 as a function"""
    def f(T):
        out = np.zeros_like(T)
        cnt = 0
        for p1 in permutations(range(a)):
            for p2 in permutations(range(b)):
                p = list(p1) + [a + x for x in p2]
                out = out + sign(p1) * sign(p2) * act3(allperm4[tuple(p)], T)
                cnt += 1
        return out * Fr(1, cnt)
    return f


gens4 = []
for (a, b) in [(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)]:
    f = alt_proj(a, b)
    imgs = [f(T) for T in full4]
    r = exact_rank([list(t.reshape(-1)) for t in imgs])
    print(f"  dim (wedge^{a} V (x) wedge^{b} V)^G = {r}")
    gens4.extend(imgs)
psi2 = np.ones((1, 1, 1), dtype=object)
psipsi = tensor_prod(psi2, psi2, 2, 2)
gens4.append(psipsi)
check("Hodge classes of X x X of degree 4 over Q-bar: 1,1,4,1,1 in the Kunneth components",
      [exact_rank([list(alt_proj(a, b)(T).reshape(-1)) for T in full4]) for (a, b) in
       [(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)]] == [1, 1, 4, 1, 1])

# S_4-closure (exact): span of p.g over all p in S_4
cl = []
for Tg in gens4:
    for p, M in allperm4.items():
        cl.append(list(act3(M, Tg).reshape(-1)))
dimT40 = exact_rank(cl)
check(f"T4_0 = S_4-span of Hdg(XxX) in degree 4 has dimension 7 (exact) [got {dimT40}]", dimT40 == 7)
# every element of T4_0 is killed by the symmetriser (exact): enough on the generators, since Sym is S_4-invariant
check("the symmetriser kills every generator, so Det is not in T4_0 (exact)",
      all(all(x == 0 for x in sym_tensor(Tg).reshape(-1)) for Tg in gens4))

# ---------------- level 1: contractions of T4_0 (x) T4_0 along two disjoint pairs
# a basis of T4_0 (exact)
M = sympy.Matrix([[sympy.Rational(Fr(x).numerator, Fr(x).denominator) for x in row] for row in cl])
rref, piv = M.T.rref()
basisT40 = [np.array([Fr(int(sympy.fraction(x)[0]), int(sympy.fraction(x)[1])) for x in cl[i]],
                     dtype=object).reshape(C4, C4, C4) for i in piv]
check("basis of T4_0 has 7 elements", len(basisT40) == 7)
pairs2 = []
for p1 in combinations(range(8), 2):
    rest = [t for t in range(8) if t not in p1]
    for p2 in combinations(rest, 2):
        if p1 < p2:
            pairs2.append((p1, p2))
check("210 ways to contract two disjoint pairs among 8 legs", len(pairs2) == 210)
kap = {pp: kappa(8, list(pp)) for pp in pairs2}
found = None
span4 = Span(8)
for T in basisT40:
    span4.add(vec_mod(T))
prods = {}
for i, T in enumerate(basisT40):
    for j, U in enumerate(basisT40):
        prods[(i, j)] = tensor_prod(T, U, 4, 4)
for (i, j), TU in prods.items():
    for pp in pairs2:
        R = act3(kap[pp], TU)
        if found is None and any(x != 0 for x in sym_tensor(R).reshape(-1)):
            found = ((i, j), pp)
        span4.add(vec_mod(R))
print("  first contraction with nonzero hyperdeterminant component:", found)
check("a contraction of two Hodge classes of X x X (a composite of correspondences) has nonzero "
      "hyperdeterminant component (exact)", found is not None)
check(f"T4 generated = all of (V^(x)4)^G, dim 8 (rank mod p = {span4.dim()} is a lower bound)", span4.dim() == 8)

# ---------------- N = 6 from T4 = full
C6 = INV[6].C
span6 = Span(C6 ** 3)
adj6 = [rho(6, [t if t not in (i, i + 1) else (i + 1 if t == i else i) for t in range(6)]) for i in range(5)]
seeds = []
for T in full4:
    seeds.append(tensor_prod(T, psi2, 4, 2))
pairs1 = list(combinations(range(8), 2))
kap1 = {pp: kappa(8, [pp]) for pp in pairs1}
for T in full4:
    for U in full4:
        TU = tensor_prod(T, U, 4, 4)
        for pp in pairs1:
            seeds.append(act3(kap1[pp], TU))
frontier = []
for Sd in seeds:
    if span6.add(vec_mod(Sd)):
        frontier.append(vec_mod(Sd).reshape(C6, C6, C6))
adj6m = [np.array([[fr_to_mod(x) for x in row] for row in A], dtype=np.int64) for A in adj6]


def act3_mod(Mat, T):
    T = np.tensordot(Mat, T, axes=([1], [0])) % P
    T = np.tensordot(Mat, T, axes=([1], [1])).transpose(1, 0, 2) % P
    T = np.tensordot(Mat, T, axes=([1], [2])).transpose(1, 2, 0) % P
    return T


while frontier:
    new = []
    for T in frontier:
        for A in adj6m:
            R = act3_mod(A, T)
            if span6.add(R.reshape(-1)):
                new.append(R)
    frontier = new
check(f"T6 generated = all of (V^(x)6)^G, dim 125 (rank mod p = {span6.dim()} is a lower bound)",
      span6.dim() == 125)

print(f"\n{len(PASS)} checks passed, {len(FAIL)} failed")
sys.exit(1 if FAIL else 0)
