#!/usr/bin/env python3
"""
Round 19, target f2-mumford, as rerun by the referee; packaged for
the paper with the floating-point steps replaced by exact ones and
without the self-written log (the transcript is transcripts/m1_split_model.log).
Item (LX), mumford_motivic.py, condenses these checks.

split_model.py  --  exact checks on the split model of a Mumford fourfold
(round 19, target f2-mumford).

V = Q^2 (x) Q^2 (x) Q^2, psi = eps (x) eps (x) eps, G = SL2^3 acting factorwise,
N = normaliser of G in Sp(V,psi) = G x| S_3 (permutations of the three factors).

Checks (all exact: python ints, fractions, python-flint):
  A. g = sl2^3 lies in sp(V,psi); sp(V,psi) = S^2 V decomposes under G as
     T1 + T2 + T3 + (2,2,2) with the last summand irreducible of dim 27, so
     End_g(sp) has dim 4 and g is a maximal Lie subalgebra of sp(V,psi).
  B. The factor permutations P_s preserve psi and normalise g, and permute
     T1,T2,T3; the Galois-stable subgroups of S_3 under conjugation by a
     transitive subgroup are exactly 1, A_3, S_3.
  C. dim (V^{(x)2m})^H for H = G, G.A3, G.S3, Sp(V):  m=1: 1,1,1,1;
     m=2: 8,4,4,3;  m=3: 125,45,35,15.  (Racah-Speiser upper bounds for G and
     Sp; explicit spanning sets and exact Gram ranks for all four.)
  D. r_1 = s_1+s_2+s_3 in End_G(V (x) V) is S_3-invariant and not
     Sp-invariant; the 3-cycle permutes the projectors pi_12, pi_13, pi_23
     cyclically, so the A_3-invariant part of span(pi_0,pi_12,pi_13,pi_23)
     is span(pi_0, pi_12+pi_13+pi_23) (the divisor part).
  E. Cayley's hyperdeterminant (the Det class of rem:mumforddet restricted to
     the diagonal) is invariant under g and S_3 but not under sp(V,psi).
"""
import itertools
from fractions import Fraction
import numpy as np
from flint import fmpz_mat, fmpq_mat, fmpq

def Q(x):
    x = Fraction(x)
    return fmpq(x.numerator, x.denominator)

LOG = []
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)

def check(cond, msg):
    if not cond:
        raise AssertionError("FAILED: " + msg)
    log("  ok:", msg)

# ---------------------------------------------------------------- basics
I2 = np.eye(2, dtype=np.int64)
E = np.array([[0, 1], [0, 0]], dtype=np.int64)
F = np.array([[0, 0], [1, 0]], dtype=np.int64)
H = np.array([[1, 0], [0, -1]], dtype=np.int64)
eps = np.array([[0, 1], [-1, 0]], dtype=np.int64)

def k3(a, b, c):
    return np.kron(np.kron(a, b), c)

psi = k3(eps, eps, eps)            # 8x8 antisymmetric
check((psi.T == -psi).all(), "psi = eps(x)eps(x)eps is alternating")
check((psi @ psi == -np.eye(8, dtype=np.int64)).all(), "psi nondegenerate (psi^2 = -1)")

gl = []
for X in (E, F, H):
    gl.append(k3(X, I2, I2)); gl.append(k3(I2, X, I2)); gl.append(k3(I2, I2, X))
g_basis = gl                       # 9 elements

def in_sp(X):
    return (X.T @ psi + psi @ X == 0).all()

check(all(in_sp(X) for X in g_basis), "g = sl2^3 lies in sp(V,psi)")

def rank_int(rows):
    """exact rank of a list of integer vectors"""
    if len(rows) == 0:
        return 0
    M = fmpz_mat([[int(x) for x in r] for r in rows])
    return M.rank()

def rank_q(rows):
    if len(rows) == 0:
        return 0
    M = fmpq_mat([[Q(x) for x in r] for r in rows])
    return M.rank()

check(rank_int([X.flatten() for X in g_basis]) == 9, "dim g = 9")

# sp(V,psi) basis: X = psi^{-1} S with S symmetric (X^T psi + psi X = 0 <=> psi X symmetric)
psi_inv = -psi                     # psi^2 = -1
check((psi_inv @ psi == np.eye(8, dtype=np.int64)).all(), "psi^{-1} integral")
sp_basis = []
for i in range(8):
    for j in range(i, 8):
        S = np.zeros((8, 8), dtype=np.int64)
        S[i, j] += 1
        S[j, i] += 1 if i != j else 0
        if i == j:
            S[i, i] = 1
        sp_basis.append(psi_inv @ S)
check(all(in_sp(X) for X in sp_basis), "constructed sp basis lies in sp")
check(rank_int([X.flatten() for X in sp_basis]) == 36, "dim sp(V,psi) = 36")

# ---------------------------------------------------------------- A: characters
# weights of V for the maximal torus of SL2^3, in units where the standard
# rep of sl2 has weights +-1 (so rho = (1,1,1) and dominant weights are >= 0)
def conv(m1, m2):
    out = {}
    for a, x in m1.items():
        for b, y in m2.items():
            c = tuple(p + q for p, q in zip(a, b))
            out[c] = out.get(c, 0) + x * y
    return out

wV = {}
for s in itertools.product((1, -1), repeat=3):
    wV[s] = wV.get(s, 0) + 1

def sym2_weights(wmult):
    # character of S^2 M: (chi(g)^2 + chi(g^2))/2
    sq = conv(wmult, wmult)
    dbl = {}
    for a, x in wmult.items():
        c = tuple(2 * p for p in a)
        dbl[c] = dbl.get(c, 0) + x
    out = {}
    for c in set(sq) | set(dbl):
        v = sq.get(c, 0) + dbl.get(c, 0)
        assert v % 2 == 0
        if v:
            out[c] = v // 2
    return out

def decompose_sl2cube(wmult):
    """peel highest weights: returns {highest weight: multiplicity}"""
    w = dict(wmult)
    res = {}
    while any(v != 0 for v in w.values()):
        dom = [c for c, v in w.items() if v > 0]
        hw = max(dom, key=lambda c: (sum(c), c))
        m = w[hw]
        res[hw] = res.get(hw, 0) + m
        # subtract character of L(hw) = product of sl2 strings
        for c in itertools.product(*[range(-n, n + 1, 2) for n in hw]):
            w[c] = w.get(c, 0) - m
        w = {c: v for c, v in w.items() if v != 0}
        assert all(v >= 0 for v in w.values())
    return res

dec = decompose_sl2cube(sym2_weights(wV))
log("  S^2 V = sp(V,psi) under SL2^3:", dec)
check(dec == {(2, 2, 2): 1, (2, 0, 0): 1, (0, 2, 0): 1, (0, 0, 2): 1},
      "sp(V,psi) = T1+T2+T3+L(2,2,2), L(2,2,2) irreducible of dim 27")
check(sum(m * m for m in dec.values()) == 4,
      "End_g(sp(V,psi)) has dim 4, so every g-submodule containing g is g or sp: "
      "g is a maximal subalgebra of sp(V,psi)")

# ---------------------------------------------------------------- B: permutations
def perm_matrix(sigma):
    """P_sigma e_{a1 a2 a3} = e_{b} with b_{sigma(k)} = a_k  (moves factor k to sigma(k))"""
    P = np.zeros((8, 8), dtype=np.int64)
    for a in itertools.product((0, 1), repeat=3):
        b = [0, 0, 0]
        for k in range(3):
            b[sigma[k]] = a[k]
        P[4 * b[0] + 2 * b[1] + b[2], 4 * a[0] + 2 * a[1] + a[2]] = 1
    return P

S3 = list(itertools.permutations(range(3)))
Pm = {s: perm_matrix(s) for s in S3}
check(all((Pm[s].T @ psi @ Pm[s] == psi).all() for s in S3),
      "the six factor permutations preserve psi (lie in Sp(V,psi))")
gflat = [X.flatten() for X in g_basis]
r_g = rank_int(gflat)
for s in S3:
    P = Pm[s]
    Pinv = P.T
    conj = [(P @ X @ Pinv).flatten() for X in g_basis]
    assert rank_int(gflat + conj) == r_g
check(True, "each factor permutation normalises g")
# action on the simple factors: T_k = span of X in k-th slot
def factor_of(X):
    for k in range(3):
        blocks = [gl[3 * t + k] for t in range(3)]
        if rank_int([Y.flatten() for Y in blocks] + [X.flatten()]) == 3:
            return k
    return None
for s in S3:
    P = Pm[s]
    img = [factor_of(P @ gl[k] @ P.T) for k in range(3)]
    assert img == [s[k] for k in range(3)], (s, img)
check(True, "conjugation by P_sigma carries T_k to T_sigma(k)")

def compose(s, t):   # (s o t)(k) = s(t(k))
    return tuple(s[t[k]] for k in range(3))
def inverse(s):
    inv = [0] * 3
    for k in range(3):
        inv[s[k]] = k
    return tuple(inv)
def subgroups_S3():
    subs = set()
    for r in range(1, 7):
        for c in itertools.combinations(S3, r):
            cs = set(c)
            if all(compose(a, b) in cs for a in cs for b in cs):
                subs.add(frozenset(cs))
    return subs
cyc = (1, 2, 0)
A3 = frozenset({(0, 1, 2), cyc, compose(cyc, cyc)})
for image in (A3, frozenset(S3)):
    stable = [H_ for H_ in subgroups_S3()
              if all(frozenset(compose(compose(g_, h), inverse(g_)) for h in H_) == H_
                     for g_ in image)]
    sizes = sorted(len(H_) for H_ in stable)
    check(sizes == [1, 3, 6],
          "subgroups of S_3 stable under conjugation by the Galois image "
          + ("A_3" if len(image) == 3 else "S_3") + ": exactly 1, A_3, S_3")

# ---------------------------------------------------------------- C: invariant dimensions
def weights_tensor_power(wmult, k):
    out = {tuple(0 for _ in next(iter(wmult))): 1}
    for _ in range(k):
        out = conv(out, wmult)
    return out

def racah_speiser_trivial(wmult, rho, weyl):
    """multiplicity of the trivial rep: sum_w eps(w) m(w(rho) - rho)"""
    tot = 0
    for (act, sgn) in weyl:
        mu = tuple(a - r for a, r in zip(act(rho), rho))
        tot += sgn * wmult.get(mu, 0)
    return tot

weyl_A1cube = []
for signs in itertools.product((1, -1), repeat=3):
    weyl_A1cube.append((lambda v, s=signs: tuple(x * y for x, y in zip(v, s)),
                        signs[0] * signs[1] * signs[2]))

def perm_sign(p):
    s = 1
    p = list(p)
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s = -s
    return s
weyl_C4 = []
for p in itertools.permutations(range(4)):
    for signs in itertools.product((1, -1), repeat=4):
        def act(v, p=p, signs=signs):
            out = [0] * 4
            for i in range(4):
                out[p[i]] = signs[i] * v[i]
            return tuple(out)
        weyl_C4.append((act, perm_sign(p) * signs[0] * signs[1] * signs[2] * signs[3]))
wV_C4 = {}
for i in range(4):
    for sg in (1, -1):
        e = [0] * 4; e[i] = sg
        wV_C4[tuple(e)] = 1

ub_G, ub_Sp = {}, {}
for m in (1, 2, 3):
    ub_G[m] = racah_speiser_trivial(weights_tensor_power(wV, 2 * m), (1, 1, 1), weyl_A1cube)
    ub_Sp[m] = racah_speiser_trivial(weights_tensor_power(wV_C4, 2 * m), (4, 3, 2, 1), weyl_C4)
log("  Racah-Speiser: dim (V^{(x)2m})^G =", ub_G, " dim (V^{(x)2m})^Sp(8) =", ub_Sp)
check(ub_G == {1: 1, 2: 8, 3: 125} and ub_Sp == {1: 1, 2: 3, 3: 15},
      "dim (V^{(x)2m})^G = 1, 8, 125 and dim (V^{(x)2m})^Sp = 1, 3, 15 (m = 1, 2, 3)")

# explicit operators on V^{(x)m} as permutations of the basis (tuples of 3m bits)
# index of a basis vector of V^{(x)m}: bits (a_{i,k}) i = copy 0..m-1, k = factor 0..2
def basis_m(m):
    return list(itertools.product((0, 1), repeat=3 * m))

def op_from_map(m, fn):
    """permutation of basis given by fn on bit tuples -> list 'perm' with perm[idx]=idx'"""
    B = basis_m(m)
    index = {b: i for i, b in enumerate(B)}
    return tuple(index[fn(b)] for b in B)

def slot_perm(m, k, tau):
    """permute the m copies of factor k by tau (a permutation of range(m))"""
    def fn(b):
        b = list(b)
        vals = [b[3 * i + k] for i in range(m)]
        new = [0] * m
        for i in range(m):
            new[tau[i]] = vals[i]
        for i in range(m):
            b[3 * i + k] = new[i]
        return tuple(b)
    return op_from_map(m, fn)

def factor_perm(m, sigma):
    """apply P_sigma to every copy of V"""
    def fn(b):
        b = list(b)
        out = [0] * (3 * m)
        for i in range(m):
            for k in range(3):
                out[3 * i + sigma[k]] = b[3 * i + k]
        return tuple(out)
    return op_from_map(m, fn)

def pcompose(p, q):  # (p o q)[x] = p[q[x]]
    return tuple(p[x] for x in q)

def pinv(p):
    inv = [0] * len(p)
    for i, x in enumerate(p):
        inv[x] = i
    return tuple(inv)

def fixed_points(p):
    return sum(1 for i, x in enumerate(p) if i == x)

def gram_full(perms):
    """Gram matrix <P_a, P_b> = tr(P_a^T P_b) = #fixed points of p_a^{-1} p_b"""
    n = len(perms)
    inv = [pinv(p) for p in perms]
    G_ = [[0] * n for _ in range(n)]
    for a_ in range(n):
        for b_ in range(a_, n):
            v = fixed_points(pcompose(inv[a_], perms[b_]))
            G_[a_][b_] = v
            G_[b_][a_] = v
    return G_

def rank_of_combos(coeff_rows, Gfull):
    """rank of span of sum_j c_ij P_j, via C Gfull C^T (exact)"""
    Cm = fmpq_mat([[Q(x) for x in r] for r in coeff_rows])
    Gm = fmpq_mat([[Q(x) for x in r] for r in Gfull])
    return (Cm * Gm * Cm.transpose()).rank()

def group_closure(gens):
    ident = tuple(range(len(gens[0])))
    seen = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g_ in gens:
                y = pcompose(g_, x)
                if y not in seen:
                    seen.add(y); new.append(y)
        frontier = new
    return sorted(seen)

def brauer_generators(m):
    """generators of the Brauer algebra image in End(V^{(x)m}) (m <= 3):
    adjacent transpositions of copies and the contraction c_{01}:
    v_0 (x) v_1 -> psi(v_0, v_1) Omega, Omega = sum (psi^{-1})_{ab} e_a (x) e_b.
    Also returns a spanning set (words of length <= 3 in these generators)."""
    n = 8 ** m
    B = basis_m(m)
    index = {b: i for i, b in enumerate(B)}
    def vec_index(ws):
        bits = []
        for w in ws:
            bits += [(w >> 2) & 1, (w >> 1) & 1, w & 1]
        return index[tuple(bits)]
    gens = []
    for i in range(m - 1):
        M = np.zeros((n, n), dtype=np.int64)
        for ws in itertools.product(range(8), repeat=m):
            new = list(ws); new[i], new[i + 1] = new[i + 1], new[i]
            M[vec_index(new), vec_index(list(ws))] = 1
        gens.append(M)
    if m >= 2:
        M = np.zeros((n, n), dtype=np.int64)
        for ws in itertools.product(range(8), repeat=m):
            col = vec_index(list(ws))
            val = psi[ws[0], ws[1]]
            if val == 0:
                continue
            for a_ in range(8):
                for b_ in range(8):
                    w_ = psi_inv[a_, b_]
                    if w_:
                        new = list(ws); new[0] = a_; new[1] = b_
                        M[vec_index(new), col] += val * w_
        gens.append(M)
    # closure of the monoid generated by gens, up to nonzero scalars
    from math import gcd
    def normalise(M):
        nz = M[M != 0]
        if nz.size == 0:
            return None
        g_ = 0
        for x in np.unique(np.abs(nz)):
            g_ = gcd(g_, int(x))
        M2 = M // g_
        first = M2.flatten()[np.flatnonzero(M2.flatten())[0]]
        if first < 0:
            M2 = -M2
        return M2
    ident = np.eye(n, dtype=np.int64)
    seen = {ident.tobytes(): ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for W in frontier:
            for g_ in gens:
                P_ = normalise(g_ @ W)
                if P_ is None:
                    continue
                key = P_.tobytes()
                if key not in seen:
                    seen[key] = P_
                    nxt.append(P_)
        frontier = nxt
    words = list(seen.values())
    return gens, words

def rank_int_mats(mats):
    """exact rank of a list of integer matrices via the Gram matrix"""
    Fm = np.array([M.flatten() for M in mats], dtype=np.int64)
    G_ = Fm @ Fm.T
    return fmpz_mat([[int(x) for x in row] for row in G_]).rank()

def commutes_with_sp(M, m):
    n = 8 ** m
    for X in sp_basis:
        A_ = np.zeros((n, n), dtype=np.int64)
        for i in range(m):
            left = np.eye(8 ** i, dtype=np.int64)
            right = np.eye(8 ** (m - i - 1), dtype=np.int64)
            A_ += np.kron(np.kron(left, X), right)
        if not (A_ @ M == M @ A_).all():
            return False
    return True

results = {}
for m in (1, 2, 3):
    gens = []
    for k in range(3):
        for i in range(m - 1):
            tau_ = list(range(m)); tau_[i], tau_[i + 1] = tau_[i + 1], tau_[i]
            gens.append(slot_perm(m, k, tuple(tau_)))
    if not gens:
        gens = [tuple(range(8 ** m))]
    grp = group_closure(gens)            # S_m x S_m x S_m permuting copies, factorwise
    pos = {p: i for i, p in enumerate(grp)}
    Gf = gram_full(grp)
    ident_rows = [[Fraction(int(i == j)) for j in range(len(grp))] for i in range(len(grp))]
    dG = rank_of_combos(ident_rows, Gf)
    Fp = {sg: factor_perm(m, sg) for sg in S3}
    def avg_rows(Hs):
        rows = []
        for p in grp:
            row = [Fraction(0)] * len(grp)
            for sg in Hs:
                q = pcompose(Fp[sg], pcompose(p, pinv(Fp[sg])))
                row[pos[q]] += Fraction(1, len(Hs))   # conjugates stay in the group
            rows.append(row)
        return rows
    dA3 = rank_of_combos(avg_rows(list(A3)), Gf)
    dS3 = rank_of_combos(avg_rows(S3), Gf)
    bgens, words = brauer_generators(m)
    dSp = rank_int_mats(words)
    ok_sp = all(commutes_with_sp(M, m) for M in bgens)
    results[m] = (dG, dA3, dS3, dSp)
    log("  m = %d: dim End_H(V^{(x)%d}) for H = G, G.A3, G.S3, Sp :" % (m, m),
        (dG, dA3, dS3, dSp), "(|S_m^3| = %d; Brauer generators commute with sp: %s)" % (len(grp), ok_sp))
    assert ok_sp
check(results[1] == (1, 1, 1, 1), "m = 1: 1, 1, 1, 1")
check(results[2] == (8, 4, 4, 3), "m = 2 (classes on X^4 in V^{(x)4}): 8, 4, 4, 3")
check(results[3] == (125, 45, 35, 15), "m = 3 (classes on X^6 in V^{(x)6}): 125, 45, 35, 15")
check(results[2][0] == ub_G[2] and results[3][0] == ub_G[3]
      and results[2][3] == ub_Sp[2] and results[3][3] == ub_Sp[3],
      "explicit spanning sets attain the Racah-Speiser values (so they span the invariant spaces)")

# ---------------------------------------------------------------- D: r_1 and the projectors
def dense_perm(p):
    n = len(p)
    M = np.zeros((n, n), dtype=np.int64)
    for i, x in enumerate(p):
        M[x, i] = 1
    return M

s = [dense_perm(slot_perm(2, k, (1, 0))) for k in range(3)]
Id = np.eye(64, dtype=np.int64)
r1 = s[0] + s[1] + s[2]
FP2 = {sg: dense_perm(factor_perm(2, sg)) for sg in S3}
check(all((FP2[sg] @ r1 == r1 @ FP2[sg]).all() for sg in S3),
      "r_1 = s_1+s_2+s_3 commutes with the S_3 factor permutations")
def gV2(X):
    return np.kron(X, np.eye(8, dtype=np.int64)) + np.kron(np.eye(8, dtype=np.int64), X)
check(all((gV2(X) @ r1 == r1 @ gV2(X)).all() for X in g_basis), "r_1 is G-invariant")
check(not all((gV2(X) @ r1 == r1 @ gV2(X)).all() for X in sp_basis),
      "r_1 is not Sp(V,psi)-invariant (not in the divisor subring)")
# projectors on /\^2 V: the (-1)-eigenspace of the full swap s1 s2 s3
tau = s[0] @ s[1] @ s[2]
def proj(signs):   # product over k of (1 + sign_k s_k)/2, times 8
    M = Id.copy()
    for k in range(3):
        M = M @ (Id + signs[k] * s[k])
    return M   # = 8 * projector
alt = Id - tau   # 2 * projector onto /\^2 V
pi = {
    "12": proj((1, 1, -1)), "13": proj((1, -1, 1)), "23": proj((-1, 1, 1)),
    "0": proj((-1, -1, -1)),
}
for key, M in pi.items():
    check((M @ alt == 2 * M).all(), "pi_%s is supported in /\\^2 V" % key)
ranks = {key: rank_int([row for row in M]) for key, M in pi.items()}
log("  ranks of pi_12, pi_13, pi_23, pi_0:", ranks)
check(ranks == {"12": 9, "13": 9, "23": 9, "0": 1}, "U_12, U_13, U_23 have dim 9, Q theta dim 1")
C = FP2[cyc]
Ci = FP2[inverse(cyc)]
# where does the cycle send pi_12 ?
names = {"12": (0, 1), "13": (0, 2), "23": (1, 2)}
for key, (i, j) in names.items():
    img = tuple(sorted((cyc[i], cyc[j])))
    target = {v: k for k, v in names.items()}[img]
    check((C @ pi[key] @ Ci == pi[target]).all(),
          "the 3-cycle (0->1->2->0) carries pi_%s to pi_%s" % (key, target))
check((C @ pi["0"] @ Ci == pi["0"]).all(), "the 3-cycle fixes pi_0")

# ---------------------------------------------------------------- E: hyperdeterminant
import sympy as sp_
a = {bits: sp_.Symbol("a%d%d%d" % bits) for bits in itertools.product((0, 1), repeat=3)}
def A(i, j, k):
    return a[(i, j, k)]
Det = (A(0,0,0)**2*A(1,1,1)**2 + A(0,0,1)**2*A(1,1,0)**2 + A(0,1,0)**2*A(1,0,1)**2
       + A(1,0,0)**2*A(0,1,1)**2
       - 2*(A(0,0,0)*A(0,0,1)*A(1,1,0)*A(1,1,1) + A(0,0,0)*A(0,1,0)*A(1,0,1)*A(1,1,1)
            + A(0,0,0)*A(1,0,0)*A(0,1,1)*A(1,1,1) + A(0,0,1)*A(0,1,0)*A(1,0,1)*A(1,1,0)
            + A(0,0,1)*A(1,0,0)*A(0,1,1)*A(1,1,0) + A(0,1,0)*A(1,0,0)*A(0,1,1)*A(1,0,1))
       + 4*(A(0,0,0)*A(0,1,1)*A(1,0,1)*A(1,1,0) + A(0,0,1)*A(0,1,0)*A(1,0,0)*A(1,1,1)))
keys = list(itertools.product((0, 1), repeat=3))
vec = [a[k] for k in keys]
def act_derivation(X, poly):
    # derivative of poly(v) along the vector field v -> X v (X acting on coordinates)
    out = 0
    for r, kr in enumerate(keys):
        comp = sum(int(X[r, c]) * vec[c] for c in range(8))
        out += sp_.diff(poly, a[kr]) * comp
    return sp_.expand(out)
check(all(act_derivation(X, Det) == 0 for X in g_basis), "Det is sl2^3-invariant")
for sg in S3:
    P = Pm[sg]
    sub = {vec[c]: sum(int(P[r, c]) * vec[r] for r in range(8)) for c in range(8)}
    assert sp_.expand(Det.xreplace(sub) - Det) == 0
check(True, "Det is invariant under the six factor permutations (N(G)-invariant)")
check(any(act_derivation(X, Det) != 0 for X in sp_basis),
      "Det is not sp(V,psi)-invariant (so not in the divisor subring)")

log("ALL CHECKS PASSED")
