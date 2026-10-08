#!/usr/bin/env python3
"""
v_ann.py -- INDEPENDENT re-implementation (bitmask exterior algebra, own generator
ordering) of the T1 (P2)/(P2') numbers for an abelian eightfold of (F,2)-Weil type,
F a quartic CM field.  Exact arithmetic over Q (python-flint fmpq_mat) unless a
line says 'mod p', in which case it is only used as a LOWER bound on a rank
(rank mod p <= rank over Q for an integer matrix), matched by an exact upper bound.

Model (derived independently, see report): H^1(A,C) = sum over 4 embeddings sigma
(bar: 0<->1, 2<->3; real place tau(0)=tau(1)=0, tau(2)=tau(3)=1) of
V_sigma = <x_{s,0}, x_{s,1}> (type (1,0)) + <y_{s,0}, y_{s,1}> (type (0,1)).
Generator index 4*s + slot, slot 0,1 = x, slot 2,3 = y.
Weil classes: vol_s = x_{s0} x_{s1} y_{s0} y_{s1}; omega = sum c_s vol_s.
Polarisations: theta_tau = sum_{s|tau} sum_i x_{s,i} y_{bar s,i}.
HT^2 = wedge^2 H^{0,1} (wedge y y) + H^{0,1} (x) T (y wedge contract_x) + wedge^2 T (contract contract).
"""
import sys, random, itertools
from fractions import Fraction as Fr
import flint

BAR = {0: 1, 1: 0, 2: 3, 3: 2}
TAU = {0: 0, 1: 0, 2: 1, 3: 1}
def X(s, i): return 4 * s + i
def Y(s, i): return 4 * s + 2 + i
XS = [X(s, i) for s in range(4) for i in range(2)]
YS = [Y(s, i) for s in range(4) for i in range(2)]

def pc(m): return bin(m).count("1")

def wedge_g(g, f):
    b = 1 << g
    out = {}
    for m, c in f.items():
        if m & b: continue
        sg = -1 if pc(m & (b - 1)) % 2 else 1
        out[m | b] = out.get(m | b, 0) + sg * c
    return {k: v for k, v in out.items() if v != 0}

def contr_g(g, f):
    b = 1 << g
    out = {}
    for m, c in f.items():
        if not m & b: continue
        sg = -1 if pc(m & (b - 1)) % 2 else 1
        out[m ^ b] = out.get(m ^ b, 0) + sg * c
    return {k: v for k, v in out.items() if v != 0}

def mono_sign(A, B):
    """sign of e_A ^ e_B (sorted) ; 0 if overlap"""
    if A & B: return 0
    s = 0
    bb = B
    while bb:
        low = bb & -bb
        g = low.bit_length() - 1
        s += pc(A >> (g + 1))  # elements of A greater than g must pass over it
        bb ^= low
    return -1 if s % 2 else 1

def wedge(f, h):
    out = {}
    for a, c in f.items():
        for b, d in h.items():
            sg = mono_sign(a, b)
            if sg:
                out[a | b] = out.get(a | b, 0) + sg * c * d
    return {k: v for k, v in out.items() if v != 0}

def add(f, h, c=1):
    out = dict(f)
    for k, v in h.items():
        out[k] = out.get(k, 0) + c * v
    return {k: v for k, v in out.items() if v != 0}

def gens_form(*gs):
    f = {0: Fr(1)}
    for g in reversed(gs):
        f = wedge_g(g, f)
    return f

def vol(s): return gens_form(X(s, 0), X(s, 1), Y(s, 0), Y(s, 1))

def theta(t):
    f = {}
    for s in range(4):
        if TAU[s] == t:
            for i in range(2):
                f = add(f, gens_form(X(s, i), Y(BAR[s], i)))
    return f

TH = [theta(0), theta(1)]
def tpow(f, k):
    o = {0: Fr(1)}
    for _ in range(k): o = wedge(o, f)
    return o
THP = {(i, j): wedge(tpow(TH[0], i), tpow(TH[1], j)) for i in range(5) for j in range(5)}

# HT^2 basis operators
OPS = []
for a, b in itertools.combinations(YS, 2):
    OPS.append(("z", (a, b), lambda f, a=a, b=b: wedge_g(a, wedge_g(b, f))))
for b in YS:
    for k in XS:
        OPS.append(("v", (b, k), lambda f, b=b, k=k: wedge_g(b, contr_g(k, f))))
for k, l in itertools.combinations(XS, 2):
    OPS.append(("pi", (k, l), lambda f, k=k, l=l: contr_g(k, contr_g(l, f))))

def matrix(gamma, ops=OPS):
    imgs = [op[2](gamma) for op in ops]
    keys = sorted({k for f in imgs for k in f})
    pos = {k: i for i, k in enumerate(keys)}
    M = flint.fmpq_mat(max(1, len(keys)), len(ops))
    for c, f in enumerate(imgs):
        for k, v in f.items():
            v = Fr(v)
            M[pos[k], c] = flint.fmpq(v.numerator, v.denominator)
    return M

def rank(gamma, ops=OPS):
    return matrix(gamma, ops).rank()

def gamma_of(cs, poly):
    g = {}
    for s in range(4):
        g = add(g, vol(s), Fr(cs[s]))
    for ij, c in poly.items():
        if c: g = add(g, THP[ij], Fr(c))
    return g

def kinds_ann(gamma):
    out = {}
    for kind in ("z", "v", "pi"):
        ops = [o for o in OPS if o[0] == kind]
        out[kind] = len(ops) - rank(gamma, ops)
    return out

def main():
    rng = random.Random(2026)
    res = {}
    print("dim HT^2 =", len(OPS)); res["dimHT2"] = len(OPS)
    # sanity: theta_tau^5 = 0, theta^4 nonzero ; vol_s is killed by theta-preserving group? (checked below)
    print("theta_0^4 terms:", len(THP[(4, 0)]), " theta_0^4 theta_1^4 terms:", len(THP[(4, 4)]))
    # pure omega with several coefficient vectors
    for trial in range(4):
        cs = [Fr(rng.choice([-1, 1]) * rng.randint(1, 20), rng.randint(1, 7)) for _ in range(4)]
        g = gamma_of(cs, {})
        r = rank(g)
        print("pure omega cs=%s: r = %d, Ann by summand %s" % ([str(c) for c in cs], r, kinds_ann(g)))
    # tangent space: F-linear v-operators y_{s,j} contract x_{s,i}, killing theta_0, theta_1
    flin = [o for o in OPS if o[0] == "v" and o[1][0] // 4 == o[1][1] // 4]
    print("F-linear v-operators:", len(flin))
    # linear conditions: sum a_o * o(theta_t) = 0
    imgs = [add(o[2](TH[0]), {}) for o in flin]
    imgs1 = [o[2](TH[1]) for o in flin]
    keys = sorted({(t, k) for t, L in ((0, imgs), (1, imgs1)) for f in L for k in f})
    pos = {k: i for i, k in enumerate(keys)}
    M = flint.fmpq_mat(len(keys), len(flin))
    for c in range(len(flin)):
        for t, L in ((0, imgs), (1, imgs1)):
            for k, v in L[c].items():
                M[pos[(t, k)], c] = flint.fmpq(int(v), 1)
    R, rk = M.rref()
    tdim = len(flin) - rk
    print("tangent space (F-linear, preserving theta_0, theta_1): dim", tdim)
    # explicit kernel vectors
    piv = []
    row = 0
    for j in range(len(flin)):
        if row < rk and R[row, j] != 0:
            piv.append(j); row += 1
    free = [j for j in range(len(flin)) if j not in piv]
    tang = []
    for f in free:
        v = [Fr(0)] * len(flin); v[f] = Fr(1)
        for i, pj in enumerate(piv):
            c = R[i, f]; v[pj] = -Fr(int(c.p), int(c.q))
        tang.append(v)
    def apply_comb(vec, f):
        out = {}
        for c, o in zip(vec, flin):
            if c: out = add(out, o[2](f), c)
        return out
    # generic gamma
    gen = []
    for trial in range(3):
        cs = [Fr(rng.choice([-1, 1]) * rng.randint(1, 20), rng.randint(1, 7)) for _ in range(4)]
        poly = {ij: Fr(rng.randint(-30, 30), rng.randint(1, 9)) for ij in THP}
        g = gamma_of(cs, poly)
        killed = all(not apply_comb(v, g) for v in tang)
        r = rank(g)
        gen.append((r, killed))
        print("generic gamma: r = %d ; 8-dim tangent space kills gamma: %s" % (r, killed))
    # monomial shapes gamma = omega + theta0^i theta1^j
    cs = [Fr(2), Fr(3), Fr(5), Fr(7)]
    shape = {}
    for ij in sorted(THP):
        shape[ij] = rank(gamma_of(cs, {ij: 1}))
    print("monomial shapes r:", shape)
    print("set of values:", sorted(set(shape.values())))
    # lower bound, independent derivation: p-support = all products of subsets of the 8 pairs
    pairs = [(X(s, i), Y(BAR[s], i)) for s in range(4) for i in range(2)]
    psupp = set()
    for k in range(9):
        for S in itertools.combinations(pairs, k):
            m = 0
            for a, b in S: m |= (1 << a) | (1 << b)
            psupp.add(m)
    # cross-check psupp against actual THP supports
    thsupp = set()
    for f in THP.values(): thsupp |= set(f)
    print("p-support monomials: %d (from THP: %d, equal: %s)" % (len(psupp), len(thsupp), psupp == thsupp))
    reach = set()
    for m in psupp:
        for o in OPS:
            reach |= set(o[2]({m: 1}).keys())
    for cs in ([Fr(1)] * 4, [Fr(2), Fr(-3), Fr(5, 7), Fr(11)]):
        om = gamma_of(cs, {})
        imgs = [{k: v for k, v in o[2](om).items() if k not in reach} for o in OPS]
        keys = sorted({k for f in imgs for k in f})
        pos = {k: i for i, k in enumerate(keys)}
        M = flint.fmpq_mat(len(keys), len(OPS))
        for c, f in enumerate(imgs):
            for k, v in f.items():
                v = Fr(v); M[pos[k], c] = flint.fmpq(v.numerator, v.denominator)
        print("p-independent lower bound (cs=%s): %d" % ([str(c) for c in cs], M.rank()))

if __name__ == "__main__":
    main()
