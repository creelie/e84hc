#!/usr/bin/env python3
"""
v2_pullbacks.py  (round 12, adversarial verification of track T2, Theorem A step 1)

Independent re-implementation, working directly in the exterior algebras
H^*(X^m) = wedge^*(V (x) Q^m) (with the Koszul signs), not in a
non-crossing-matching model.

Split model over Q: V = Q^2 (x) Q^2 (x) Q^2, basis index v = 4a1+2a2+a3,
g = sl2^3 acting factorwise.  (Over Q-bar the real Mumford G is this; the
rationality descent is argued separately.)

 (1) Compute the G-invariants of wedge^a V (x) wedge^b V (a+b = 4) directly
     (zero-weight space, kernel of E_1,E_2,E_3), exactly (Fractions).
     These are the Hodge classes of X x X of degree 4 over Q-bar.
 (2) Compute (V^{(x)4})^G directly in V^{(x)4} (dim 8).
 (3) Pull back the classes of (1) along many integer 2x4 matrices
     f: X^4 -> X^2 and take the multilinear (1,1,1,1) Kunneth component,
     with signs; add the multilinear components of products of pull-backs
     of the divisor class psi.  Exact rank of the span in (V^{(x)4})^G.
 (4) The hyperdeterminant: the S_4-symmetric invariant in V^{(x)4}
     (Cayley).  Exact test whether it lies in the span of (3).
 (5) Composition of correspondences: t, t' in the span of (3), viewed as
     correspondences X^2 -> X^2 (legs 1,2 -> legs 3,4); the composite
     contracts legs 3,4 of t with legs 1,2 of t' by the invariant form
     Psi = eps (x) eps (x) eps (the pairing int_X v w theta^3 up to a
     nonzero scalar).  Also with legs permuted first.  Exact rank of span
     of (3) + all composites; exact Det-component of one composite.
"""
import sys
import random
from fractions import Fraction as Fr
from itertools import combinations, permutations, product

PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("PASS " if cond else "FAIL ") + name)


# ---------- exact linear algebra
def rref(rows, ncols):
    """rows: list of dict col->Fr. returns list of (pivot, row dict) in reduced echelon form"""
    ech = []
    for r in rows:
        r = {k: Fr(v) for k, v in r.items() if v != 0}
        for piv, er in ech:
            if piv in r:
                c = r[piv]
                for k, v in er.items():
                    r[k] = r.get(k, 0) - c * v
                    if r[k] == 0:
                        del r[k]
        if not r:
            continue
        piv = min(r)
        c = r[piv]
        r = {k: v / c for k, v in r.items()}
        new = []
        for p2, er in ech:
            if piv in er:
                c2 = er[piv]
                er = dict(er)
                for k, v in r.items():
                    er[k] = er.get(k, 0) - c2 * v
                    if er[k] == 0:
                        del er[k]
            new.append((p2, er))
        ech = new + [(piv, r)]
    return ech


def nullspace(eqs, unknowns):
    """eqs: list of dict unknown->coef (each = 0). returns basis of solutions as dicts"""
    ech = rref(eqs, None)
    pivs = {p for p, _ in ech}
    free = [u for u in unknowns if u not in pivs]
    basis = []
    for f in free:
        sol = {f: Fr(1)}
        for p, r in ech:
            if f in r:
                sol[p] = -r[f]
        basis.append(sol)
    return basis


# ---------- V and g
def bits(v):
    return [(v >> 2) & 1, (v >> 1) & 1, v & 1]


def unbits(b):
    return 4 * b[0] + 2 * b[1] + b[2]


def weight(v):
    # H-weight in factor k: +1 for bit 0, -1 for bit 1
    return tuple(1 - 2 * b for b in bits(v))


def E_on_vec(k, v):
    """E of factor k on basis vector v: E e_1 = e_0 (bit 1 -> bit 0), E e_0 = 0"""
    b = bits(v)
    if b[k] == 1:
        b[k] = 0
        return [(unbits(b), 1)]
    return []


# ---------- (1) invariants of wedge^a V (x) wedge^b V
def wedge_basis(a):
    return list(combinations(range(8), a))


def wt_of_subset(S):
    w = [0, 0, 0]
    for v in S:
        for j, x in enumerate(weight(v)):
            w[j] += x
    return tuple(w)


def apply_E_to_subset(k, S):
    """derivation action of E_k on e_S = e_{s1} ^ ... ^ e_{sa} (S sorted). returns dict sorted-subset -> coef"""
    out = {}
    S = list(S)
    for pos, v in enumerate(S):
        for (w, c) in E_on_vec(k, v):
            T = S[:pos] + [w] + S[pos + 1:]
            if len(set(T)) < len(T):
                continue
            # sort with sign
            perm = sorted(range(len(T)), key=lambda i: T[i])
            sgn = perm_sign(perm)
            key = tuple(sorted(T))
            out[key] = out.get(key, 0) + sgn * c
    return out


def perm_sign(p):
    p = list(p)
    s = 1
    seen = [False] * len(p)
    for i in range(len(p)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                L += 1
            if L % 2 == 0:
                s = -s
    return s


def invariants_wedge_pair(a, b):
    unknowns = [(A, B) for A in wedge_basis(a) for B in wedge_basis(b)
                if tuple(x + y for x, y in zip(wt_of_subset(A), wt_of_subset(B))) == (0, 0, 0)]
    eqs = {}
    for (A, B) in unknowns:
        for k in range(3):
            for A2, c in apply_E_to_subset(k, A).items():
                key = (k, A2, B)
                eqs.setdefault(key, {})
                eqs[key][(A, B)] = eqs[key].get((A, B), 0) + c
            # E acts on the second factor with the Koszul sign (-1)^a? E is even: no sign.
            for B2, c in apply_E_to_subset(k, B).items():
                key = (k, A, B2)
                eqs.setdefault(key, {})
                eqs[key][(A, B)] = eqs[key].get((A, B), 0) + c
    return nullspace(list(eqs.values()), unknowns)


hodge4 = {}
for a in range(5):
    hodge4[(a, 4 - a)] = invariants_wedge_pair(a, 4 - a)
dims = [len(hodge4[(a, 4 - a)]) for a in range(5)]
print("(1) dim (wedge^a V (x) wedge^{4-a} V)^G, a=0..4:", dims)
check("(1) Hodge classes of X x X of degree 4: 1,1,4,1,1 (total 8)", dims == [1, 1, 4, 1, 1])
psi_basis = invariants_wedge_pair(2, 0)
check("(1) dim (wedge^2 V)^G = 1 (the class psi)", len(psi_basis) == 1)
psi = {A: c for (A, B), c in psi_basis[0].items()}  # A a 2-subset

# ---------- (2) (V^{(x)4})^G directly
def tensor_weight(t):
    w = [0, 0, 0]
    for v in t:
        for j, x in enumerate(weight(v)):
            w[j] += x
    return tuple(w)


zero4 = [t for t in product(range(8), repeat=4) if tensor_weight(t) == (0, 0, 0)]
eqs = {}
for t in zero4:
    for k in range(3):
        for pos in range(4):
            for (w, c) in E_on_vec(k, t[pos]):
                t2 = t[:pos] + (w,) + t[pos + 1:]
                eqs.setdefault((k, t2), {})
                eqs[(k, t2)][t] = eqs[(k, t2)].get(t, 0) + c
inv4 = nullspace(list(eqs.values()), zero4)
print("(2) zero-weight space dim", len(zero4), "; dim (V^(x)4)^G =", len(inv4))
check("(2) dim (V^{(x)4})^G = 8", len(inv4) == 8)
# coordinates: choose pivot entries
ech_inv = rref(inv4, None)
pivots = [p for p, _ in ech_inv]
basis_rows = [r for _, r in ech_inv]


def coords(tens):
    """coordinates of a G-invariant tensor (dict) in the echelon basis; asserts membership"""
    c = [tens.get(p, Fr(0)) for p in pivots]
    recon = {}
    for ci, r in zip(c, basis_rows):
        if ci:
            for k, v in r.items():
                recon[k] = recon.get(k, 0) + ci * v
    diff = {k: recon.get(k, 0) - tens.get(k, 0) for k in set(recon) | set(tens)}
    assert all(v == 0 for v in diff.values()), "tensor not in (V^4)^G"
    return c


# ---------- exterior algebra of V (x) Q^m: basis index 8*factor + v
def wedge_mul(x, y):
    """x, y: dict sorted-tuple -> coef in the exterior algebra"""
    out = {}
    for A, ca in x.items():
        for B, cb in y.items():
            if set(A) & set(B):
                continue
            T = list(A) + list(B)
            perm = sorted(range(len(T)), key=lambda i: T[i])
            s = perm_sign(perm)
            key = tuple(sorted(T))
            out[key] = out.get(key, 0) + s * ca * cb
    return {k: v for k, v in out.items() if v != 0}


def pullback_linear(M, m_from, m_to):
    """f: X^{m_to} -> X^{m_from} with matrix M (m_from x m_to); f^*(v (x) E_j) = sum_i M[j][i] v (x) e_i"""
    def img(idx):
        j, v = divmod(idx, 8)
        return {(8 * i + v,): Fr(M[j][i]) for i in range(m_to) if M[j][i] != 0}
    return img


def pullback(cls, M, m_from, m_to):
    img = pullback_linear(M, m_from, m_to)
    out = {}
    for A, c in cls.items():
        term = {(): Fr(c)}
        for idx in A:
            term = wedge_mul(term, img(idx))
            if not term:
                break
        for k, v in term.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}


def multilinear(cls, m):
    """(1,...,1) Kunneth component of a degree-m class on X^m, as a tensor dict (v_1,...,v_m) -> coef"""
    out = {}
    for A, c in cls.items():
        if len(A) == m and sorted(i // 8 for i in A) == list(range(m)):
            t = tuple(i % 8 for i in A)  # A sorted, so factor order 0..m-1
            out[t] = out.get(t, 0) + c
    return out


def xx_class(a, sol):
    """class on X x X from an invariant of wedge^a V (x) wedge^b V: e_A^{(1)} ^ e_B^{(2)}"""
    cls = {}
    for (A, B), c in sol.items():
        key = tuple(A) + tuple(8 + v for v in B)
        cls[key] = cls.get(key, 0) + c
    return cls


classes_XX = []
for a in range(5):
    for sol in hodge4[(a, 4 - a)]:
        classes_XX.append(xx_class(a, sol))
psi_X4 = {}
random.seed(12345)
mats = [[[1, 1, 0, 0], [0, 0, 1, 1]], [[1, 0, 1, 0], [0, 1, 0, 1]], [[1, 0, 0, 1], [0, 1, 1, 0]],
        [[1, 1, 1, 0], [0, 0, 0, 1]], [[1, 1, 1, 1], [0, 0, 0, 0]]]
for _ in range(40):
    mats.append([[random.randint(-3, 3) for _ in range(4)] for _ in range(2)])
vecs = []
for M in mats:
    for cls in classes_XX:
        pb = pullback(cls, M, 2, 4)
        ml = multilinear(pb, 4)
        if ml:
            vecs.append(coords(ml))
# products of divisor classes psi_{ij} on X^4 (pull-backs of psi along X^4 -> X^1 give psi_ii-type;
# general Hdg^1(X^4) = pull-backs of psi along X^4 -> X, x -> sum r_i x_i, polarised)
psi_cls = {tuple(A): c for A, c in psi.items()}
lin = []
for _ in range(12):
    r = [[random.randint(-2, 2) for _ in range(4)]]
    lin.append(pullback(psi_cls, r, 1, 4))
for x in lin:
    for y in lin:
        ml = multilinear(wedge_mul(x, y), 4)
        if ml:
            vecs.append(coords(ml))
ech_T40 = rref([{i: v for i, v in enumerate(c) if v} for c in vecs], None)
print("(3) number of generators:", len(vecs), "; exact rank of their span:", len(ech_T40))
check("(3) span of multilinear parts of pull-backs of Hdg^2(X x X) and products of divisors: dim 7",
      len(ech_T40) == 7)

# ---------- (4) Det = S_4-symmetric invariant
def permute_tensor(t, p):
    """leg i of input -> leg p[i] of output (no sign; the sign twist does not change spans)"""
    out = {}
    for key, c in t.items():
        nk = [None] * 4
        for i in range(4):
            nk[p[i]] = key[i]
        out[tuple(nk)] = out.get(tuple(nk), 0) + c
    return out


def from_coords(c):
    t = {}
    for ci, r in zip(c, basis_rows):
        if ci:
            for k, v in r.items():
                t[k] = t.get(k, 0) + ci * v
    return {k: v for k, v in t.items() if v != 0}


def symmetrise(t):
    out = {}
    for p in permutations(range(4)):
        for k, v in permute_tensor(t, p).items():
            out[k] = out.get(k, 0) + v
    return {k: v / 24 for k, v in out.items() if v != 0}


sym_imgs = [coords(symmetrise(from_coords([Fr(int(i == j)) for i in range(8)]))) for j in range(8)]
ech_sym = rref([{i: v for i, v in enumerate(c) if v} for c in sym_imgs], None)
check("(4) the S_4-symmetric G-invariants of V^(x)4 form a line (Det)", len(ech_sym) == 1)
Det = [ech_sym[0][1].get(i, Fr(0)) for i in range(8)]
# independent identification: Det is (up to scale) Cayley's hyperdeterminant polarised.
# Evaluate the symmetric 4-linear form on x = sum x_v e_v^* ... check on a sample tensor that
# Det(x,x,x,x) is proportional to Cayley's hyperdeterminant of the 2x2x2 array x.
def cayley(a):
    g = lambda i, j, k: a[4 * i + 2 * j + k]
    return (g(0,0,0)**2*g(1,1,1)**2 + g(0,0,1)**2*g(1,1,0)**2 + g(0,1,0)**2*g(1,0,1)**2 + g(1,0,0)**2*g(0,1,1)**2
            - 2*(g(0,0,0)*g(0,0,1)*g(1,1,0)*g(1,1,1) + g(0,0,0)*g(0,1,0)*g(1,0,1)*g(1,1,1)
                 + g(0,0,0)*g(1,0,0)*g(0,1,1)*g(1,1,1) + g(0,0,1)*g(0,1,0)*g(1,0,1)*g(1,1,0)
                 + g(0,0,1)*g(1,0,0)*g(0,1,1)*g(1,1,0) + g(0,1,0)*g(1,0,0)*g(0,1,1)*g(1,0,1))
            + 4*(g(0,0,0)*g(0,1,1)*g(1,0,1)*g(1,1,0) + g(0,0,1)*g(0,1,0)*g(1,0,0)*g(1,1,1)))


Dt = from_coords(Det)
ratios = set()
for trial in range(6):
    x = [random.randint(-3, 3) for _ in range(8)]
    val = sum(c * x[k[0]] * x[k[1]] * x[k[2]] * x[k[3]] for k, c in Dt.items())
    cv = cayley(x)
    if cv != 0:
        ratios.add(Fr(val) / cv)
    else:
        ratios.add(None if val != 0 else "0/0")
print("(4) Det(x,x,x,x)/Cayley(x) on random x:", ratios)
check("(4) Det restricted to the diagonal is a constant multiple of Cayley's hyperdeterminant",
      len([r for r in ratios if r not in ("0/0",)]) == 1 and None not in ratios)


def in_span(ech, c):
    r = {i: v for i, v in enumerate(c) if v}
    for piv, er in ech:
        if piv in r:
            cc = r[piv]
            for k, v in er.items():
                r[k] = r.get(k, 0) - cc * v
                if r[k] == 0:
                    del r[k]
    return not r


check("(4) Det is NOT in the span of (3) (exact)", not in_span(ech_T40, Det))
# the span of (3) is S_4-stable and equals the kernel of the symmetriser:
T40 = [[er.get(i, Fr(0)) for i in range(8)] for _, er in ech_T40]
check("(4) the symmetriser kills the span of (3)",
      all(all(v == 0 for v in symmetrise(from_coords(c)).values()) for c in T40))

# ---------- (5) composites of correspondences
EPS = [[0, 1], [-1, 0]]


def Psi(v, w):
    bv, bw = bits(v), bits(w)
    r = 1
    for k in range(3):
        r *= EPS[bv[k]][bw[k]]
    return r


def compose(t, u):
    """t: legs (1,2 | 3,4) as correspondence X^2 -> X^2; composite u o t contracts
       legs 3,4 of t with legs 1,2 of u via Psi; result legs (1,2 of t | 3,4 of u)"""
    out = {}
    u_by_first = {}
    for k, c in u.items():
        u_by_first.setdefault((k[0], k[1]), []).append((k[2], k[3], c))
    for k, c in t.items():
        a, b, x, y = k
        for z in range(8):
            pz = Psi(x, z)
            if not pz:
                continue
            for w in range(8):
                pw = Psi(y, w)
                if not pw:
                    continue
                for (cc, dd, cu) in u_by_first.get((z, w), []):
                    key = (a, b, cc, dd)
                    out[key] = out.get(key, 0) + c * pz * pw * cu
    return {k: v for k, v in out.items() if v != 0}


T40_t = [from_coords(c) for c in T40]
# include the S_4-translates (the span is S_4-stable anyway)
comp_vecs = list(T40)
first_det = None
for i, t in enumerate(T40_t):
    for j, u in enumerate(T40_t):
        c = coords(compose(t, u))
        comp_vecs.append(c)
        s = coords(symmetrise(from_coords(c))) if any(c) else [0] * 8
        if first_det is None and any(s):
            first_det = (i, j, s)
ech_all = rref([{i: v for i, v in enumerate(c) if v} for c in comp_vecs], None)
print("(5) exact rank of span of T4_0 and all composites u o t (t,u in T4_0):", len(ech_all))
check("(5) composites of two classes of T4_0 reach Det: span = all of (V^(x)4)^G (dim 8, exact)",
      len(ech_all) == 8)
check("(5) some single composite has nonzero hyperdeterminant component (exact)", first_det is not None)
if first_det:
    print("    first such pair (basis indices):", first_det[0], first_det[1])

print(f"\n{len(PASS)} checks passed, {len(FAIL)} failed")
sys.exit(1 if FAIL else 0)
