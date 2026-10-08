#!/usr/bin/env python3
"""
mumford_object.py

Item (XLV) of COMPUTATIONS.md: what a perfect complex with the
Chern character of an exceptional class on the square Y = X x X of a Mumford
fourfold must look like.  The model is that of mumford_rigidity.py:
H^1(Y) = V (+) V with V = V_1 (x) V_2 (x) V_3, the Hodge structure coming from
the third factor, and omega_a = a0 pi_0 + a1 pi_12 + a2 pi_13 + a3 pi_23.
HT^k(Y) = wedge^k(H^{0,1} (+) T) acts by wedging the classes of H^{0,1} and
contracting those of H^{1,0}; r_k(c) is the rank of x -> x _| c on HT^k.

What is checked:

  (A) at a* = (3, 5, -7, 11) the ranks r_k(omega), computed exactly over Q
      block by block (type, weight of the first two factors, exchange
      parity), are 1, 16, 119, 328, 560, 328, 119, 16, 1 for k = 0..8, and 0
      for k = 9..16;

  (B) the same ranks hold, modulo a prime p = 1 mod 7 at which the minimal
      polynomial x^3 + x^2 - 2x - 1 of 2cos(2pi/7) splits, at the class with
      a0 = 2 and (a1, a2, a3) the three conjugates in each of the six
      orders; on the hyperplane a0 + a1 + a2 + a3 = 0 they drop to
      1, 16, 110, 328, 548, 328, 110, 16, 1;

  (C) duality: for a random class with components of Hodge type (p,p) for
      p = 0, 1, 2, 3 the ranks are symmetric, r_k = r_{8-k}, and vanish for
      k > 8;

  (D) the Euler characteristic bookkeeping: sum (-1)^k r_k = 112, while
      chi(E, E) = 0 for ch(E) = N omega; and 2 r_0 + 2 r_2 + r_4 = 800;

  (E) at a CM point, where the Hodge classes of Y are the monomials of
      weight zero: 16 divisor classes, 132 Hodge classes in degree four, the
      products of divisor classes span 100 of them, and the combinations of
      the four tensors pi that lie in that span are exactly those with
      a1 = a2 = a3;

  (F) at a CM point the fourfold X_c has 8 Hodge classes in degree four, of
      which the products of its 4 divisor classes span 6.

Run:  python3 mumford_object.py
"""
import itertools
import random
from collections import defaultdict

import sympy

import mumford_rigidity as MR
from mumford_rigidity import wt, mono_sign, popcount, NB

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


pieces, PI, raise_ops = MR.build_tensors()
KEYS = ["0", "12", "13", "23"]
hol = [i for i in range(NB) if wt(i)[2] == 1]
anti = [i for i in range(NB) if wt(i)[2] == -1]
gens = [("w", i) for i in anti] + [("c", i) for i in hol]
gidx = {g: k for k, g in enumerate(gens)}


def apply(g, x, p=None):
    kind, i = g
    out = {}
    for m, c in x.items():
        if kind == "w":
            if m >> i & 1:
                continue
            s = mono_sign(1 << i, m)
            nm = m | (1 << i)
        else:
            if not (m >> i & 1):
                continue
            s = (-1) ** popcount(m & ((1 << i) - 1))
            nm = m ^ (1 << i)
        v = out.get(nm, 0) + s * c
        out[nm] = v % p if p else v
    return {k: v for k, v in out.items() if v != 0}


def gwt(g):
    kind, i = g
    w = wt(i)
    return w if kind == "w" else tuple(-x for x in w)


def sw(i):
    return i + 8 if i < 8 else i - 8


def swapS(S):
    T = [gidx[(gens[g][0], sw(gens[g][1]))] for g in S]
    s, arr = 1, T[:]
    for i in range(len(arr)):
        for j in range(len(arr) - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                s = -s
    return tuple(arr), s


# ------------------------------------------------------------ exact blocks
_cache = {}


def act(S):
    if S not in _cache:
        res = {}
        for key in PI:
            x = PI[key]
            for g in reversed(S):
                x = apply(gens[g], x)
                if not x:
                    break
            res[key] = x
        _cache[S] = res
    return _cache[S]


def exact_rank(K, avals):
    blocks = defaultdict(list)
    for S in itertools.combinations(range(16), K):
        mu = [0, 0]
        for g in S:
            w = gwt(gens[g])
            mu[0] += w[0]
            mu[1] += w[1]
        a = sum(1 for g in S if gens[g][0] == "w")
        blocks[(a, K - a, tuple(mu))].append(S)
    total = 0
    for key, Ss in blocks.items():
        for par in (1, -1):
            vecs, seen = [], set()
            for S in Ss:
                if S in seen:
                    continue
                T, s = swapS(S)
                seen.update((S, T))
                if T == S:
                    if s * par == 1:
                        vecs.append({S: 1})
                    continue
                vecs.append({S: 1, T: s * par})
            cols = []
            for v in vecs:
                c = {}
                for S, co in v.items():
                    for k, a in zip(KEYS, avals):
                        for m, x in act(S)[k].items():
                            c[m] = c.get(m, 0) + co * a * x
                cols.append({m: x for m, x in c.items() if x != 0})
            rows = sorted({m for c in cols for m in c})
            if not rows:
                continue
            M = sympy.Matrix(len(rows), len(cols),
                             lambda i, j: cols[j].get(rows[i], 0))
            total += M.rank()
    return total


# ------------------------------------------------------------ modular ranks
def modp(x, p):
    x = sympy.Rational(x)
    return (int(x.p) * pow(int(x.q), p - 2, p)) % p


def omega_mod(avals, p):
    om = {}
    for key, c in zip(KEYS, avals):
        for m, x in PI[key].items():
            om[m] = (om.get(m, 0) + c * modp(x, p)) % p
    return {k: v for k, v in om.items() if v}


def rank_mod(rows, p):
    piv, r = {}, 0
    for row in rows:
        row = dict(row)
        while row:
            c = min(row)
            if c in piv:
                f = row[c]
                for k, v in piv[c].items():
                    row[k] = (row.get(k, 0) - f * v) % p
                    if row[k] == 0:
                        del row[k]
            else:
                inv = pow(row[c], p - 2, p)
                piv[c] = {k: v * inv % p for k, v in row.items()}
                r += 1
                break
    return r


def rk_mod(om, k, p):
    rows = []
    for S in itertools.combinations(range(16), k):
        x = om
        for g in reversed(S):
            x = apply(gens[g], x, p)
            if not x:
                break
        if x:
            rows.append(x)
    return rank_mod(rows, p)


def isprime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


# ------------------------------------------------------------ weight helpers
def mweight(m):
    s = [0, 0, 0]
    for i in range(NB):
        if m >> i & 1:
            w = wt(i)
            for t in range(3):
                s[t] += w[t]
    return tuple(s)


def wedge(x, y):
    out = {}
    for m1, c1 in x.items():
        for m2, c2 in y.items():
            if m1 & m2:
                continue
            out[m1 | m2] = out.get(m1 | m2, 0) + mono_sign(m1, m2) * c1 * c2
    return {k: v for k, v in out.items() if v != 0}


PROFILE = [1, 16, 119, 328, 560, 328, 119, 16, 1]
PROFILE_L0 = [1, 16, 110, 328, 548, 328, 110, 16, 1]


def run():
    # (A)
    astar = (3, 5, -7, 11)
    ranks = [exact_rank(k, astar) for k in range(9)]
    check("the ranks of contraction into omega at (3,5,-7,11), exact over "
          "Q, are 1,16,119,328,560,328,119,16,1 in degrees 0..8",
          ranks == PROFILE, "computed %s" % ranks)
    high = [exact_rank(k, astar) for k in (9, 10, 12, 16)]
    check("they vanish in degrees above eight", high == [0, 0, 0, 0])

    # (B)
    p = 1000000
    while not (p % 7 == 1 and isprime(p)):
        p += 1
    roots = [x for x in range(p) if (x ** 3 + x * x - 2 * x - 1) % p == 0]
    ok = len(roots) == 3
    for order in itertools.permutations(roots):
        om = omega_mod((2,) + order, p)
        if [rk_mod(om, k, p) for k in range(9)] != PROFILE:
            ok = False
    check("the same ranks, modulo p = %d, at a0 = 2 and the conjugates of "
          "2cos(2pi/7) in each of the six orders" % p, ok,
          "a rational exceptional class for the cubic subfield of Q(zeta_7)")
    om = omega_mod((3, 1, 3, p - 7), p)
    l0 = [rk_mod(om, k, p) for k in range(9)]
    check("on the hyperplane a0 + a1 + a2 + a3 = 0 the ranks drop to "
          "1,16,110,328,548,328,110,16,1", l0 == PROFILE_L0,
          "computed %s" % l0)

    # (C)
    random.seed(20260924)
    c = {}
    for pp in (0, 1, 2, 3):
        for _ in range(6):
            H = random.sample(hol, pp)
            A = random.sample(anti, pp)
            c[sum(1 << i for i in H + A)] = random.randint(1, p - 1)
    mixed = [rk_mod(c, k, p) for k in range(11)]
    check("for a random class with components of types (0,0) to (3,3) the "
          "ranks are palindromic, r_k = r_{8-k}, and zero above eight",
          all(mixed[k] == mixed[8 - k] for k in range(9))
          and mixed[9] == mixed[10] == 0, "computed %s" % mixed)

    # (D)
    alt = sum((-1) ** k * PROFILE[k] for k in range(9))
    check("the alternating sum of the ranks is 112, and 2r_0 + 2r_2 + r_4 "
          "= 800", alt == 112 and 2 * PROFILE[0] + 2 * PROFILE[2]
          + PROFILE[4] == 800,
          "so chi(E,E) = 0 forces Ext^1 + Ext^3 >= 400 when Ext^{<0} = 0")

    # (E)
    H2 = [m for m in range(1 << 16) if popcount(m) == 2
          and mweight(m) == (0, 0, 0)]
    H4 = [m for m in range(1 << 16) if popcount(m) == 4
          and mweight(m) == (0, 0, 0)]
    prods = []
    for i in range(len(H2)):
        for j in range(i + 1, len(H2)):
            q = wedge({H2[i]: 1}, {H2[j]: 1})
            if q:
                prods.append(q)
    D = sympy.Matrix([[q.get(m, 0) for m in H4] for q in prods])
    rD = D.rank()
    N = sympy.Matrix.hstack(D.T, *[sympy.Matrix([[PI[k].get(m, 0)
                                                  for m in H4]]).T
                                   for k in KEYS])
    combos = sympy.Matrix([list(v[-4:]) for v in N.nullspace()])
    span = combos.rref()[0]
    span = [list(span.row(i)) for i in range(span.rows) if any(span.row(i))]
    check("at a CM point: 16 divisor classes, 132 Hodge classes in degree "
          "four, products of divisor classes spanning 100",
          (len(H2), len(H4), rD) == (16, 132, 100))
    check("the combinations of the pi in that span are exactly those with "
          "a1 = a2 = a3", span == [[1, 0, 0, 0], [0, 1, 1, 1]],
          "so no rational exceptional class is a polynomial in divisor "
          "classes at any point")

    # (F)
    V2 = [m for m in range(1 << 8) if popcount(m) == 2
          and mweight(m) == (0, 0, 0)]
    V4 = [m for m in range(1 << 8) if popcount(m) == 4
          and mweight(m) == (0, 0, 0)]
    pr4 = []
    for i in range(len(V2)):
        for j in range(i + 1, len(V2)):
            q = wedge({V2[i]: 1}, {V2[j]: 1})
            if q:
                pr4.append(q)
    d4 = sympy.Matrix([[q.get(m, 0) for m in V4] for q in pr4]).rank()
    check("at a CM point X_c has 4 divisor classes and 8 Hodge classes in "
          "degree four, of which products of divisors span 6",
          (len(V2), len(V4), d4) == (4, 8, 6),
          "the other two are not products of divisor classes")


if __name__ == "__main__":
    print("(XLV) what an object with the Chern character of an exceptional "
          "class must look like")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
