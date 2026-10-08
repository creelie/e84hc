"""a1_rkappa.py -- the contraction rank r(kappa) on A for Orlov products (track A1).

r(kappa) = rank of HT^2(A) -> H^*(A,C), xi -> xi _| kappa, kappa = ch(E) e^{ell/2},
E = Phi(F [x] F^vee).  Prediction (Kunneth + Orlov transport + independence of blocks):
  r(kappa) = r^2(v) + r^1(v)^2 + r^2(v) = 2 r^2(v) + 64,  i.e. 100 (rank-1 V) or 104 (rank-2 V).
Method:  complex structure z_j = x_j + i x_{4+j}, w_j = xi_j + i xi_{4+j} on A;
  LOWER bound: rank mod p (p = 1 mod 4, i -> sqrt(-1) mod p) <= rank over Q(i);
  UPPER bound: an exact kernel over Q(i) of the restriction to a set of columns, of the
  predicted dimension, each vector of which is then checked to annihilate kappa exactly.
"""
import sys, time, random, itertools
from fractions import Fraction as Fr
import flint
from ealib import *
from amodel import AModel
from orlov import orlov
import a1_secant as SEC

P = 1000000009   # prime, = 1 mod 4


def sqrtm1(p):
    for a in range(2, 1000):
        x = pow(a, (p - 1) // 4, p)
        if x * x % p == p - 1:
            return x
    raise ValueError


I_P = sqrtm1(P)


def to_complex_A(u):
    """real generators x_j, x_{4+j} (pair (j,4+j)) and xi_j, xi_{4+j} (pair (8+j,12+j))
    -> complex generators at the same positions: z_j/zbar_j and w_j/wbar_j. QI coefficients.
    x = (z + zbar)/2, x' = -i (z - zbar)/2."""
    cur = {m: QI(c) for m, c in u.items()}
    half = Fr(1, 2)
    for base in (0, 8):
        for j in range(4):
            p0, p1 = base + j, base + 4 + j
            b0, b1 = 1 << p0, 1 << p1
            between = ((1 << p1) - 1) ^ ((1 << (p0 + 1)) - 1)
            nxt = {}
            for m, c in cur.items():
                h0, h1 = bool(m & b0), bool(m & b1)
                if h0 and h1:
                    nxt[m] = nxt.get(m, 0) + c * QI(0, half)
                elif h0:
                    s = -1 if pc(m & between) & 1 else 1
                    nxt[m] = nxt.get(m, 0) + c * QI(half)
                    m2 = (m ^ b0) | b1
                    nxt[m2] = nxt.get(m2, 0) + c * QI(half * s)
                elif h1:
                    s = -1 if pc(m & between) & 1 else 1
                    nxt[m] = nxt.get(m, 0) + c * QI(0, half)
                    m2 = (m ^ b1) | b0
                    nxt[m2] = nxt.get(m2, 0) + c * QI(0, -half * s)
                else:
                    nxt[m] = nxt.get(m, 0) + c
            cur = {k: v for k, v in nxt.items() if v != 0}
    return cur


HOL = [0, 1, 2, 3, 8, 9, 10, 11]          # z_j, w_j
ANTI = [4, 5, 6, 7, 12, 13, 14, 15]       # zbar_j, wbar_j


def HT2_ops():
    ops = []
    for a, b in itertools.combinations(ANTI, 2):
        ops.append(("ww", a, b))
    for a in ANTI:
        for h in HOL:
            ops.append(("wc", a, h))
    for h1, h2 in itertools.combinations(HOL, 2):
        ops.append(("cc", h1, h2))
    return ops


def act(op, u):
    t, a, b = op
    one_ = QI(1)
    if t == "ww":
        return lwedge(a, lwedge(b, u, one_), one_)
    if t == "wc":
        return lwedge(a, contract(b, u), one_)
    return contract(a, contract(b, u))


def qi_modp(c):
    c = c if isinstance(c, QI) else QI(c)
    a = c.a.numerator * pow(c.a.denominator, -1, P) % P
    b = c.b.numerator * pow(c.b.denominator, -1, P) % P
    return (a + b * I_P) % P


def analyse(kappa, label, predicted):
    t0 = time.time()
    ck = to_complex_A(kappa)
    ops = HT2_ops()
    assert len(ops) == 120
    vecs = [act(op, ck) for op in ops]
    keys = sorted(set(k for v in vecs for k in v))
    kidx = {k: i for i, k in enumerate(keys)}
    M = flint.nmod_mat(len(keys), 120, P)
    for j, v in enumerate(vecs):
        for k, c in v.items():
            M[kidx[k], j] = qi_modp(c)
    rp = M.rank()
    check("%s: r(kappa) mod p = %d (lower bound), prediction %d  [%d terms in C-coords, %d rows]"
          % (label, rp, predicted, len(ck), len(keys)), rp == predicted)
    # exact kernel on a column subset
    rng = random.Random(5)
    sub_keys = rng.sample(keys, min(len(keys), 400))
    subvecs = [{k: v[k] for k in sub_keys if k in v} for v in vecs]
    # realify: unknowns (a_j, b_j); equations Re and Im per key
    n = 120
    Mq = flint.fmpq_mat(2 * len(sub_keys), 2 * n)
    for r, k in enumerate(sub_keys):
        for j in range(n):
            c = subvecs[j].get(k)
            if c is None:
                continue
            c = c if isinstance(c, QI) else QI(c)
            # (a + ib)(cr + i ci) = (a cr - b ci) + i (a ci + b cr)
            Mq[2 * r, j] = flint.fmpq(c.a.numerator, c.a.denominator)
            Mq[2 * r, n + j] = flint.fmpq((-c.b).numerator, (-c.b).denominator)
            Mq[2 * r + 1, j] = flint.fmpq(c.b.numerator, c.b.denominator)
            Mq[2 * r + 1, n + j] = flint.fmpq(c.a.numerator, c.a.denominator)
    ker = fmpq_nullspace(Mq)
    kdimC = len(ker) // 2
    # pick complex-independent vectors a + i b and verify on all of kappa
    cands = []
    for vec in ker:
        cands.append([QI(vec[j], vec[n + j]) for j in range(n)])
    # choose a maximal Q(i)-independent subset via realified rank
    chosen = []
    def realrank(lst):
        if not lst:
            return 0
        Mr = flint.fmpq_mat(2 * len(lst), 2 * n)
        for r, cv in enumerate(lst):
            for j, c in enumerate(cv):
                Mr[2 * r, j] = flint.fmpq(c.a.numerator, c.a.denominator)
                Mr[2 * r, n + j] = flint.fmpq(c.b.numerator, c.b.denominator)
                Mr[2 * r + 1, j] = flint.fmpq((-c.b).numerator, (-c.b).denominator)
                Mr[2 * r + 1, n + j] = flint.fmpq(c.a.numerator, c.a.denominator)
        return Mr.rank() // 2
    for cv in cands:
        if realrank(chosen + [cv]) > len(chosen):
            chosen.append(cv)
    ok = True
    for cv in chosen:
        tot = {}
        for j, c in enumerate(cv):
            if c == 0:
                continue
            for k, x in vecs[j].items():
                tot[k] = tot.get(k, 0) + c * x
        if any(x != 0 for x in tot.values()):
            ok = False
            break
    check("%s: exact annihilator over Q(i) of dimension %d (each vector verified on all of kappa)"
          % (label, len(chosen)), ok and len(chosen) == 120 - predicted)
    if ok:
        print("     => r(kappa) = %d exactly  (%.1fs)" % (120 - len(chosen), time.time() - t0), flush=True)
    return rp


if __name__ == "__main__":
    q = (2, 1)
    Am = AModel(q)
    ell = Am.ell()
    eh = expo(sc(Fr(1, 2), ell))
    shapes = [("w (rank-1 V)", (0, (0, 0), 1), 100), ("v_1 (rank-2 V)", (0, (1, 0), 0), 104),
              ("u (rank-1 V)", (1, (0, 0), 0), 100)]
    for name, (a, f, c), pred in shapes:
        v = SEC.rational(SEC.M.from_V(SEC.Vmat_of(a, f, c, q)))
        ch = orlov(4, v, SEC.M.dual(v))
        kappa = wedge(ch, eh)
        analyse(kappa, "q=%s F=%s" % (q, name), pred)
        # r(ch E) = r(kappa) (e^{ell/2} with ell of type (1,1) conjugates the action)
        if name.startswith("w"):
            analyse(ch, "q=%s F=%s [untwisted ch(E)]" % (q, name), pred)
    summary()
