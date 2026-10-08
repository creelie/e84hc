#!/usr/bin/env python3
"""
p2prime.py

The corrected criterion (P2') as a number.  Item (LII).

(P2') asks, at one base point of a family of abelian 2n-folds of Weil type,
for a perfect complex E with

    ch(E) = N omega_1 + sum_{k=0}^{2n} c_k theta^k ,   N != 0,

whose semiregularity map sigma_E is injective.  Since sigma_E o ev_E is
contraction into ch(E), the rank r of

    HT^2(A) -> H^*(A),   xi |-> xi _| ch(E),

is a lower bound for dim Ext^2(E,E), and dim Ext^2(E,E) = r forces sigma_E
to be injective (the argument of thm:p2numerical).  This script computes r.

Model (that of hochschild_annihilator.py).  H^1(A,C) has basis e_0..e_{2n-1}
of V_+ and f_0..f_{2n-1} of V_-, complex conjugation exchanging e_j and f_j;
H^{1,0} is spanned by e_j (j < n) and f_j (j >= n).  The polarisation is
theta = i sum_j s_j e_j ^ f_j with s_j = +1 for j < n and -1 for j >= n, the
Weil classes are alpha_+ = e_0 ^ ... ^ e_{2n-1} and alpha_- = f_0 ^ ... ^
f_{2n-1}, and a real class on the Weil line is u alpha_+ + conj(u) alpha_-.
HT^1 = H^{0,1} (+) T acts by wedging with the (0,1) generators and
contracting the (1,0) ones; HT^2 is spanned by the products of two of these
4n operators.  The group preserving the Hodge structure, theta and the Weil
line acts transitively on the polarised Weil family, so the ranks found here
hold at every member.

Put mu_m = m! c_m and let rho be the rank of the (2n-1) x 3 Hankel matrix
[mu_{j+i}] (j = 0..2n-2, i = 0..2).  What is checked:

  (A) the closed form: for n >= 3 and every u != 0,
          dim Ann_{HT^2}(ch) = n^2 (4 - rho),   r = (4 + rho) n^2 - 2n,
      exactly over Q(i) for n = 3, 4 on shapes of every rank rho, with two
      values of u; the pure case rho = 0 is the paper's 2n(2n-1);

  (B) the generic annihilator is the tangent space of the polarised Weil
      family: for rho = 3 it is spanned by the n^2 vectors v1 + v2 (one for
      each pair a < n <= b), all in H^1(T), for n = 2, 3, 4;

  (C) the strata: rho <= 1 exactly on C e^{t theta} and C theta^{2n}; the
      shapes with only c_1, only c_0 and c_1, or c_0 and c_{2n} nonzero have
      rho = 2; twisting by e^{t theta} does not change rho or r;

  (D) n = 2, where two K-characters meet: dim Ann = 4(4 - rho) + e with
      e = dim ker((HK)^2 - |u|^2), K = antidiag(1,-2,1); for theta^2 + omega
      the rank r is 24 in general, 22 at |u|^2 = 4 and 23 at |u|^2 = 16;

  (E) the first-order Hodge locus Ann_{H^1(T)}(ch): n^2 (the polarised Weil
      family) as soon as some c_k != 0 with 1 <= k <= 2n-1, and 2n^2 (all
      K-linear deformations) otherwise, n = 3, 4; at n = 2 it is 4 in
      general, 8 in the pure case, and 5 exactly at c_1 = c_3 = 0,
      |u| = 4|c_2|;

  (F) the Euler characteristic: int ch^vee ch = (2n)! Q(c) + 2|u|^2 in the
      normalisation int theta^{2n} = (2n)!, with Q(c) = sum_k (-1)^k c_k
      c_{2n-k}, for n = 2, 3; and in the rational model of explicit_weil.py
      at n = 2, int omega_1^2 = 8 d^2 and int eta^4 = 24, so the exceptional
      ratio of (E) is c_2 = +-dN/2 for the class N omega_1 + c_2 eta^2;

  (G) the exceptional ratio at n = 2: the stabiliser of gamma = omega +
      c_2 theta^2 in gl(H^1) has dimension 21 at |u| = 4|c_2|, with Hodge
      pieces 5, 11, 5 (the 5 is the Hodge locus of (E)), commutant on H^1
      the scalars, and a real form whose trace form has signature (12, 9),
      so it is so(4,3) acting on H^1 by its spin representation; its
      invariants in wedge^k H^1 have dimensions 1,0,0,0,1,0,0,0,1, so a very
      general member of the Hodge locus has no divisor classes.  At an
      ordinary ratio the stabiliser is su(2,2), of dimension 15, with
      invariants 1,0,1,0,3,0,1,0,1.  At the exceptional ratio
      int gamma kappa_h^2 = (sigma_2(h) + 4 Re det h[01,23]) / 6 for the
      Kaehler class of a positive hermitian h (c_2 = 1), which has constant
      sign on the Kaehler cone; at R = 3/16 it changes sign.

With --extreme the closed form is checked further, exactly over Q(i), for
n = 5, ..., 9 (or up to --nmax=N) on five shapes.  All ranks are computed by
blocks: the torus (C^*)^{2n}, acting by e_j -> tau_j e_j and f_j -> tau_j^{-1}
f_j, fixes theta and scales alpha_+ and alpha_- by (prod tau_j)^{+-1}, so
elements of HT^2 whose weights differ by something other than a multiple of
(1,...,1) have images in different weight spaces, and the rank is the sum of
the ranks of the blocks.

Nothing here constructs an object with dim Ext^2(E,E) = r, and nothing here
bears on whether one exists.

Run:  python3 p2prime.py            (a few seconds)
      python3 p2prime.py --extreme  (n up to 9)
"""

import sys
import random
from fractions import Fraction as Fr
from math import comb, factorial

PASS, FAIL = [], []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % (tag, name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


# ------------------------------------------------------------------ fields
class GQ:
    """a Gaussian rational a + b i"""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(self, o):
        return GQ(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        return GQ(self.a - o.a, self.b - o.b)

    def __mul__(self, o):
        return GQ(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)

    def __neg__(self):
        return GQ(-self.a, -self.b)

    def inv(self):
        d = self.a * self.a + self.b * self.b
        return GQ(self.a / d, -self.b / d)

    def zero(self):
        return self.a == 0 and self.b == 0


class Exact:
    name = "exact over Q(i)"

    def num(self, a, b=0):
        return GQ(a, b)

    def add(self, x, y):
        return x + y

    def mul(self, x, y):
        return x * y

    def neg(self, x):
        return -x

    def inv(self, x):
        return x.inv()

    def zero(self, x):
        return x.zero()


# -------------------------------------------------- exterior algebra by masks
def op_apply(kind, bit, vec, F):
    """wedge ('w') or contract ('c') with generator `bit`, with the sign
    (-1)^(number of generators of the monomial below `bit`)"""
    out = {}
    m = 1 << bit
    low = m - 1
    for mask, c in vec.items():
        if kind == "w":
            if mask & m:
                continue
            k = mask | m
        else:
            if not mask & m:
                continue
            k = mask ^ m
        if bin(mask & low).count("1") & 1:
            c = F.neg(c)
        if k in out:
            s = F.add(out[k], c)
            if F.zero(s):
                del out[k]
            else:
                out[k] = s
        else:
            out[k] = c
    return out


def merge_sign(m1, m2):
    """sign of the permutation sorting the generators of m1 followed by
    those of m2 (disjoint masks): (-1)^#{(i, j) : i in m1, j in m2, i > j}"""
    s, x = 0, m2
    while x:
        low = x & -x
        s += bin(m1 & ~((low << 1) - 1)).count("1")
        x ^= low
    return -1 if s & 1 else 1


def vadd(x, y, F, s=None):
    out = dict(x)
    for k, v in y.items():
        if s is not None:
            v = F.mul(s, v)
        if k in out:
            t = F.add(out[k], v)
            if F.zero(t):
                del out[k]
            else:
                out[k] = t
        elif not F.zero(v):
            out[k] = v
    return out


class Model:
    """the abelian 2n-fold of Weil type and its HT^1, HT^2"""

    def __init__(self, n):
        self.n = n
        g = self.g = 2 * n
        self.e = lambda j: j
        self.f = lambda j: g + j
        ops = []
        ops += [("w", self.e(j), "V+01") for j in range(n, g)]
        ops += [("w", self.f(j), "V-01") for j in range(n)]
        ops += [("c", self.e(j), "T+") for j in range(n)]
        ops += [("c", self.f(j), "T-") for j in range(n, g)]
        self.ops = ops
        self.ht2 = [(s, t) for s in range(len(ops)) for t in range(s + 1, len(ops))]
        self.opindex = {(o[0], o[1]): i for i, o in enumerate(ops)}

    def kind(self, s, t):
        """H02, H1T or W2T"""
        ks = {self.ops[s][0], self.ops[t][0]}
        return {frozenset("w"): "H02", frozenset("c"): "W2T"}.get(
            frozenset(ks), "H1T")

    def apply2(self, s, t, vec, F):
        o1, o2 = self.ops[s], self.ops[t]
        return op_apply(o1[0], o1[1], op_apply(o2[0], o2[1], vec, F), F)

    def theta_powers(self, F):
        n, g = self.n, self.g
        theta = {}
        for j in range(g):
            mask = (1 << self.e(j)) | (1 << self.f(j))
            theta[mask] = F.num(0, 1 if j < n else -1)       # i s_j e_j f_j
        pw = [{0: F.num(1)}]
        for _ in range(g):
            prev, out = pw[-1], {}
            for m1, c1 in prev.items():
                for m2, c2 in theta.items():
                    if m1 & m2:
                        continue
                    k = m1 | m2
                    v = F.mul(F.mul(c1, c2), F.num(merge_sign(m1, m2)))
                    out[k] = F.add(out[k], v) if k in out else v
            pw.append({k: v for k, v in out.items() if not F.zero(v)})
        return pw

    def ch(self, c, u, F, pw=None):
        """sum c_k theta^k + u alpha_+ + conj(u) alpha_-"""
        g = self.g
        pw = pw or self.theta_powers(F)
        out = {}
        for k, ck in enumerate(c):
            if ck:
                out = vadd(out, pw[k], F, F.num(ck))
        ap = sum(1 << self.e(j) for j in range(g))
        am = sum(1 << self.f(j) for j in range(g))
        out = vadd(out, {ap: F.num(u[0], u[1])}, F)
        out = vadd(out, {am: F.num(u[0], -u[1])}, F)
        return out


def rank_and_kernel(cols, F, want_kernel=False):
    """rank of the matrix whose columns are the sparse vectors `cols`; with
    want_kernel, also a basis of the kernel (as dicts column -> coefficient)"""
    piv = {}            # pivot row -> (reduced column, combination)
    kernel = []
    for j, col in enumerate(cols):
        v = dict(col)
        comb_ = {j: F.num(1)} if want_kernel else None
        while v:
            p = min(v)
            if p not in piv:
                break
            w, cw = piv[p]
            f = F.neg(F.mul(v[p], F.inv(w[p])))
            v = vadd(v, w, F, f)
            if want_kernel:
                comb_ = vadd(comb_, cw, F, f)
        if v:
            piv[min(v)] = (v, comb_)
        elif want_kernel:
            kernel.append(comb_)
    return len(piv), kernel


def hankel_rank(c, n):
    mu = [factorial(m) * Fr(c[m]) for m in range(2 * n + 1)]
    rows = [[mu[j + i] for i in range(3)] for j in range(2 * n - 1)]
    return rank_q(rows)


def rank_q(rows):
    rows = [list(map(Fr, r)) for r in rows]
    r, ncol = 0, len(rows[0]) if rows else 0
    for col in range(ncol):
        p = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col] / rows[r][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def weight_class(M, s, t):
    """torus weight of op_s op_t modulo Z(1,...,1).  The torus (C^*)^{2n}
    acting by e_j -> tau_j e_j, f_j -> tau_j^{-1} f_j fixes theta and scales
    alpha_+ and alpha_- by (prod tau_j)^{+-1}; contraction is equivariant, so
    images of elements in different classes lie in different weight spaces
    and the rank is the sum of the ranks of the blocks."""
    w = [0] * M.g
    for o in (M.ops[s], M.ops[t]):
        kind, bit = o[0], o[1]
        j, pos = bit % M.g, bit < M.g
        w[j] += (1 if pos else -1) * (1 if kind == "w" else -1)
    return tuple(x - w[0] for x in w)


def annihilator(M, c, u, F, kernel=False, pw=None):
    chv = M.ch(c, u, F, pw)
    blocks = {}
    for idx, (s, t) in enumerate(M.ht2):
        blocks.setdefault(weight_class(M, s, t), []).append(idx)
    r, ker = 0, []
    for members in blocks.values():
        cols = [M.apply2(*M.ht2[i], chv, F) for i in members]
        rb, kb = rank_and_kernel(cols, F, want_kernel=kernel)
        r += rb
        for vec in kb:
            ker.append({members[j]: v for j, v in vec.items()})
    return r, len(M.ht2) - r, ker


def shapes(n, rng):
    """named Chern-character shapes, coefficients c_0..c_{2n}"""
    g = 2 * n
    z = [0] * (g + 1)

    def at(**kw):
        c = list(z)
        for k, v in kw.items():
            c[int(k[1:])] = v
        return c
    expo = [Fr(1, factorial(k)) for k in range(g + 1)]
    two = [Fr(1, factorial(k)) + Fr(3) * Fr(2) ** k / factorial(k)
           for k in range(g + 1)]
    gen = [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(g + 1)]
    out = [("pure", z), ("c_0 only", at(c0=1)), ("c_2n only", at(**{"c%d" % g: 1})),
           ("e^theta", expo), ("c_1 only", at(c1=1)), ("c_0 + c_1", at(c0=2, c1=1)),
           ("c_0 + c_2n", at(c0=1, **{"c%d" % g: 3})), ("two exponentials", two),
           ("c_n only", at(**{"c%d" % n: 1})), ("generic", gen)]
    return out


# ------------------------------------------------------ (A)-(C) closed form
def item_ABC(nlist, F, rng):
    for n in nlist:
        M = Model(n)
        pw = M.theta_powers(F)
        for name, c in shapes(n, rng):
            rho = hankel_rank(c, n)
            ok, dims = True, []
            for u in ((1, 0), (2, 3)):
                r, a, _ = annihilator(M, c, u, F, pw=pw)
                dims.append(a)
                ok = ok and a == n * n * (4 - rho) and r == (4 + rho) * n * n - 2 * n
            check("n=%d, %s: rho = %d, dim Ann = n^2(4-rho) = %d, r = %d" %
                  (n, name, rho, n * n * (4 - rho), (4 + rho) * n * n - 2 * n),
                  ok, "" if ok else "found %s" % dims)


def tangent_vectors(M, F):
    """v1 + v2 = w(e_b)c(e_a) + w(f_a)c(f_b) for a < n <= b, as dicts on HT^2"""
    idx = {st: i for i, st in enumerate(M.ht2)}
    out = []
    for a in range(M.n):
        for b in range(M.n, M.g):
            vec = {}
            for (x, y) in ((("w", M.e(b)), ("c", M.e(a))),
                           (("w", M.f(a)), ("c", M.f(b)))):
                s, t = M.opindex[x], M.opindex[y]
                sign = 1 if s < t else -1           # op_s op_t = -op_t op_s
                key = idx[(min(s, t), max(s, t))]
                vec[key] = F.add(vec.get(key, F.num(0)), F.num(sign))
            out.append(vec)
    return out


def item_B(F, rng):
    for n in (2, 3, 4):
        M = Model(n)
        c = [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(2 * n + 1)]
        u = (1, 2)
        chv = M.ch(c, u, F)
        tp = tangent_vectors(M, F)
        kills = True
        for vec in tp:
            img = {}
            for key, coef in vec.items():
                s, t = M.ht2[key]
                img = vadd(img, M.apply2(s, t, chv, F), F, coef)
            kills = kills and not img
        r, a, ker = annihilator(M, c, u, F, kernel=True)
        in_h1t = all(M.kind(*M.ht2[k]) == "H1T" for v in ker for k in v)
        # the explicit tangent vectors span the whole annihilator
        rk_tp, _ = rank_and_kernel(tp, F)
        rk_both, _ = rank_and_kernel(tp + ker, F)
        check("n=%d, generic: Ann_{HT^2}(ch) is the n^2-dimensional tangent "
              "space of the polarised Weil family, inside H^1(T)" % n,
              kills and a == n * n and in_h1t and rk_tp == n * n and rk_both == n * n)


def item_C(F):
    for n in (2, 3):
        g = 2 * n
        M = Model(n)
        pw = M.theta_powers(F)
        # rho <= 1 on exponentials and on theta^{2n}; rho = 2 on the listed
        # supports; twist invariance of rho and of r
        ok = True
        for t in (Fr(1), Fr(-1, 2), Fr(3)):
            ok = ok and hankel_rank([t ** k / factorial(k) for k in range(g + 1)], n) == 1
        ok = ok and hankel_rank([0] * g + [1], n) == 1
        check("n=%d: rho = 1 on C e^(t theta) and on C theta^(2n)" % n, ok)
        base = [Fr(1), Fr(2), Fr(-1), Fr(1, 2)] + [Fr(1, 3)] * (g - 3)
        ok = True
        for t in (Fr(1), Fr(-1, 2)):
            tw = [sum(base[j] * t ** (k - j) / factorial(k - j) for j in range(k + 1))
                  for k in range(g + 1)]
            ok = ok and hankel_rank(tw, n) == hankel_rank(base, n)
            r1 = annihilator(M, base, (1, 1), F, pw=pw)[0]
            r2 = annihilator(M, tw, (1, 1), F, pw=pw)[0]
            ok = ok and r1 == r2
        check("n=%d: twisting ch by e^(t theta) (t = 1, -1/2) keeps rho and r" % n, ok)


# ------------------------------------------------------------ (D) n = 2
def n2_extra(c, X):
    """e = dim ker((HK)^2 - X) at n = 2, exactly"""
    mu = [factorial(m) * Fr(c[m]) for m in range(5)]
    H = [[mu[j + i] for i in range(3)] for j in range(3)]
    K = [[0, 0, 1], [0, -2, 0], [1, 0, 0]]
    HK = [[sum(H[i][k] * K[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    Y2 = [[sum(HK[i][k] * HK[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    A = [[Y2[i][j] - (X if i == j else 0) for j in range(3)] for i in range(3)]
    return 3 - rank_q(A)


def item_D(F):
    M = Model(2)
    pw = M.theta_powers(F)
    c = [0, 0, 1, 0, 0]                      # theta^2 + u alpha_+ + ...
    rho = hankel_rank(c, 2)
    rows = []
    ok = True
    for u in ((1, 0), (2, 0), (4, 0), (0, 2), (3, 1), (12, 16)):
        X = u[0] ** 2 + u[1] ** 2
        r, a, _ = annihilator(M, c, u, F, pw=pw)
        e = n2_extra(c, Fr(X) if u != (12, 16) else Fr(X, 25))
        rows.append("|u|^2 = %s: r = %d, dim Ann = %d" % (X, r, a))
        if u != (12, 16):
            ok = ok and a == 4 * (4 - rho) + e
    # u = (12,16)/5 has |u|^2 = 16: run it with rational u
    r, a, _ = annihilator(M, c, (Fr(12, 5), Fr(16, 5)), F, pw=pw)
    rows.append("|u|^2 = 16 (u = (12+16i)/5): r = %d" % r)
    ok = ok and r == 23
    r4 = annihilator(M, c, (2, 0), F, pw=pw)[0]
    r1 = annihilator(M, c, (1, 0), F, pw=pw)[0]
    ok = ok and r4 == 22 and r1 == 24
    check("n=2, theta^2 + omega: dim Ann = 4(4-rho) + dim ker((HK)^2 - |u|^2); "
          "r = 24 in general, 22 at |u|^2 = 4, 23 at |u|^2 = 16", ok, "\n".join(rows))
    rng = random.Random(11)
    ok = True
    for _ in range(4):
        c = [Fr(rng.randint(-5, 5), rng.randint(1, 4)) for _ in range(5)]
        u = (rng.randint(1, 5), rng.randint(0, 5))
        X = u[0] ** 2 + u[1] ** 2
        a = annihilator(M, c, u, F, pw=pw)[1]
        ok = ok and a == 4 * (4 - hankel_rank(c, 2)) + n2_extra(c, Fr(X))
    check("n=2, four random shapes: the same formula", ok)


# --------------------------------------------- (E) the first-order locus
def h1t_annihilator(M, c, u, F, pw=None):
    chv = M.ch(c, u, F, pw)
    cols = [M.apply2(s, t, chv, F) for (s, t) in M.ht2 if M.kind(s, t) == "H1T"]
    r, _ = rank_and_kernel(cols, F)
    return len(cols) - r


def item_E(F, rng):
    for n in (3, 4):
        M = Model(n)
        pw = M.theta_powers(F)
        ok = True
        for name, c in shapes(n, rng):
            want = 2 * n * n if all(c[k] == 0 for k in range(1, 2 * n)) else n * n
            ok = ok and h1t_annihilator(M, c, (1, 2), F, pw) == want
        check("n=%d: the first-order Hodge locus of ch is n^2-dimensional unless "
              "c_1 = ... = c_(2n-1) = 0, when it is 2n^2" % n, ok)
    M = Model(2)
    pw = M.theta_powers(F)
    got = []
    for c, u in (([0, 0, 1, 0, 0], (4, 0)), ([0, 0, 1, 0, 0], (0, 4)),
                 ([1, 0, 1, 0, 3], (4, 0)), ([0, 0, 1, 0, 0], (3, 0)),
                 ([0, 0, 1, 0, 0], (2, 0)), ([0, 1, 1, 0, 0], (4, 0)),
                 ([0, 0, 0, 0, 0], (1, 0))):
        got.append(h1t_annihilator(M, c, u, F, pw))
    check("n=2: the first-order Hodge locus is 5-dimensional exactly at "
          "c_1 = c_3 = 0, |u| = 4|c_2|, 4 otherwise, 8 in the pure case",
          got == [5, 5, 5, 4, 4, 4, 8], "dimensions %s" % got)


# ------------------------------------------------ (F) Euler characteristic
def item_F(F, rng):
    for n in (2, 3):
        M = Model(n)
        g = 2 * n
        pw = M.theta_powers(F)
        top = (1 << (2 * g)) - 1
        ok = True
        for _ in range(3):
            c = [Fr(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(g + 1)]
            u = (rng.randint(-3, 3), rng.randint(1, 3))
            chv = M.ch(c, u, F, pw)
            # ch^vee: sign (-1)^k on the degree 2k part
            dual = {m: (v if (bin(m).count("1") // 2) % 2 == 0 else F.neg(v))
                    for m, v in chv.items()}
            prod = {}
            for m1, c1 in dual.items():
                for m2, c2 in chv.items():
                    if m1 & m2 or (m1 | m2) != top:
                        continue
                    v = F.mul(F.mul(c1, c2), F.num(merge_sign(m1, m2)))
                    prod[top] = F.add(prod[top], v) if top in prod else v
            integral = prod.get(top, F.num(0))
            vol = pw[g][top]                              # theta^{2n} coefficient
            chi = F.mul(integral, F.mul(F.inv(vol), F.num(factorial(g))))
            Qc = sum((-1) ** k * c[k] * c[g - k] for k in range(g + 1))
            want = factorial(g) * Qc + 2 * (u[0] ** 2 + u[1] ** 2)
            ok = ok and chi.a == want and chi.b == 0
        check("n=%d: int ch^vee ch = (2n)! Q(c) + 2|u|^2 in the normalisation "
              "int theta^(2n) = (2n)!" % n, ok)
    try:
        import explicit_weil as EW
    except ImportError:
        check("explicit_weil.py importable", False)
        return
    ok, rows = True, []
    for d in (1, 2, 3, 5, 7):
        Mw = EW.Model(2, d)
        key = tuple(range(1, Mw.N + 1))
        w1, eta = Mw.omega1(), Mw.eta()
        i_w = EW.wedge(w1, w1, d).get(key, EW.sc())[0]
        i_e = EW.ewedgepow(eta, 4, d).get(key, EW.sc())[0]
        # orient so that int eta^4 > 0
        s = 1 if i_e > 0 else -1
        i_w, i_e = s * i_w, s * i_e
        # the ratio R = c^2 int eta^4 / (N^2 int omega_1^2) equals 3/4
        # exactly at c = +-dN/2
        R = Fr(d, 2) ** 2 * i_e / i_w
        rows.append("d=%d: int omega_1^2 = %s, int eta^4 = %s, R(c = dN/2) = %s"
                    % (d, i_w, i_e, R))
        ok = ok and i_w == 8 * d * d and i_e == 24 and R == Fr(3, 4)
    check("rational model, n=2: int omega_1^2 = 8d^2 and int eta^4 = 24, so the "
          "exceptional ratio c^2 int eta^4 = (3/4) N^2 int omega^2 is c = +-dN/2",
          ok, "\n".join(rows))


# --------------------------------------- (G) the exceptional ratio at n = 2
def conj_gq(x):
    return GQ(x.a, -x.b)


def der_apply(ab, vec, F):
    """the derivation of the exterior algebra extending E_ab : x_b -> x_a"""
    a, b = ab
    out = {}
    for mask, c in vec.items():
        if not mask >> b & 1:
            continue
        if a == b:
            k = mask
        else:
            if mask >> a & 1:
                continue
            k = (mask ^ (1 << b)) | (1 << a)
            lo, hi = min(a, b), max(a, b)
            between = mask & (((1 << hi) - 1) ^ ((1 << (lo + 1)) - 1))
            if bin(between).count("1") & 1:
                c = F.neg(c)
        out = vadd(out, {k: c}, F)
    return out


def op_apply_mat(X, vec, F):
    out = {}
    for ab, x in X.items():
        out = vadd(out, der_apply(ab, vec, F), F, x)
    return out


def mat_mul_trace(X, Y, F):
    t = F.num(0)
    for (a, b), x in X.items():
        y = Y.get((b, a))
        if y is not None:
            t = F.add(t, F.mul(x, y))
    return t


def congruence_signature(G):
    """signature (p, q) of a real symmetric rational matrix, by congruence"""
    G = [[Fr(x) for x in row] for row in G]
    n, p, q = len(G), 0, 0
    idx = list(range(n))
    while idx:
        piv = next((i for i in idx if G[i][i] != 0), None)
        if piv is None:
            pair = next(((i, j) for i in idx for j in idx if i < j and G[i][j] != 0), None)
            if pair is None:
                break
            i, j = pair                     # replace row/col i by i + j
            for k in range(n):
                G[i][k] += G[j][k]
            for k in range(n):
                G[k][i] += G[k][j]
            piv = i
        d = G[piv][piv]
        p, q = (p + 1, q) if d > 0 else (p, q + 1)
        idx.remove(piv)
        for i in idx:
            f = G[i][piv] / d
            if f:
                for k in range(n):
                    G[i][k] -= f * G[piv][k]
                for k in range(n):
                    G[k][i] -= f * G[k][piv]
    return p, q


def stabiliser(M, gamma, F):
    g2 = 2 * M.g
    basis = [(a, b) for a in range(g2) for b in range(g2)]
    cols = [der_apply(ab, gamma, F) for ab in basis]
    _, ker = rank_and_kernel(cols, F, want_kernel=True)
    return [{basis[j]: v for j, v in vec.items()} for vec in ker], basis


def item_G(F):
    M = Model(2)
    pw = M.theta_powers(F)
    g2 = 2 * M.g
    h10 = {M.e(j) for j in range(M.n)} | {M.f(j) for j in range(M.n, M.g)}
    swap = {x: (x + M.g) % g2 for x in range(g2)}

    def hodge_type(ab):
        a, b = ab
        if b in h10 and a not in h10:
            return -1
        if b not in h10 and a in h10:
            return 1
        return 0

    def invariants(stab):
        dims = []
        for k in range(g2 + 1):
            masks = [m for m in range(1 << g2) if bin(m).count("1") == k]
            cols = []
            for m in masks:
                col = {}
                for x, X in enumerate(stab):
                    for mm, v in op_apply_mat(X, {m: F.num(1)}, F).items():
                        col[x * (1 << g2) + mm] = v
                cols.append(col)
            r, _ = rank_and_kernel(cols, F)
            dims.append(len(masks) - r)
        return dims

    for label, u, want_dim, want_inv in (
            ("exceptional, |u| = 4|c_2|", (4, 0), 21, [1, 0, 0, 0, 1, 0, 0, 0, 1]),
            ("ordinary, |u| = 3|c_2|", (3, 0), 15, [1, 0, 1, 0, 3, 0, 1, 0, 1])):
        gamma = M.ch([0, 0, 1, 0, 0], u, F, pw)
        stab, basis = stabiliser(M, gamma, F)
        # graded pieces for the Hodge grading of gl(H^1)
        pieces = []
        for t in (-1, 0, 1):
            sub = [ab for ab in basis if hodge_type(ab) == t]
            cols = [der_apply(ab, gamma, F) for ab in sub]
            r, _ = rank_and_kernel(cols, F)
            pieces.append(len(sub) - r)
        inv = invariants(stab)
        detail = "dim = %d, Hodge pieces %s, invariants in wedge^k H^1: %s" % (
            len(stab), pieces, inv)
        ok = len(stab) == want_dim and sum(pieces) == want_dim and inv == want_inv
        if want_dim == 21:
            # irreducible on H^1: the commutant is the scalars
            cols = []
            for (a, b) in basis:
                col = {}
                for x, X in enumerate(stab):
                    for (i, j), v in X.items():
                        if i == b:                      # (E_ab X)_{a j} = X_{b j}
                            col[(x, a, j)] = F.add(col.get((x, a, j), F.num(0)), v)
                        if j == a:                      # (X E_ab)_{i b} = X_{i a}
                            col[(x, i, b)] = F.add(col.get((x, i, b), F.num(0)), F.neg(v))
                cols.append({k: v for k, v in col.items() if not F.zero(v)})
            rc, _ = rank_and_kernel(cols, F)
            commutant = len(basis) - rc
            # a real basis: X + conj X and i(X - conj X), conj E_ab = E_{a'b'}
            real = []
            for X in stab:
                cX = {(swap[a], swap[b]): conj_gq(v) for (a, b), v in X.items()}
                real.append(vadd(X, cX, F))
                real.append({k: F.mul(F.num(0, 1), v) for k, v in vadd(X, cX, F, F.num(-1)).items()})
            keep, cols = [], []
            for Y in real:
                trial = cols + [{basis.index(k): v for k, v in Y.items()}]
                if rank_and_kernel(trial, F)[0] == len(trial):
                    keep.append(Y)
                    cols = trial
            gram = [[mat_mul_trace(Y1, Y2, F) for Y2 in keep] for Y1 in keep]
            real_ok = all(x.b == 0 for row in gram for x in row)
            sig = congruence_signature([[x.a for x in row] for row in gram])
            detail += ("\ncommutant on H^1: %d; real form of dimension %d with trace "
                       "form of signature %s" % (commutant, len(keep), sig))
            ok = ok and pieces == [5, 11, 5] and commutant == 1 and len(keep) == 21 \
                and real_ok and sig == (12, 9)
        check("n=2, gamma = omega + c_2 theta^2, %s: the stabiliser of gamma in "
              "gl(H^1) has dimension %d and its invariants are as stated"
              % (label, want_dim), ok, detail)
    # the Kaehler classes kappa_h = i sum h_jk z_j ^ zbar_k, h positive definite
    top = (1 << g2) - 1
    z = [M.e(j) for j in range(M.n)] + [M.f(j) for j in range(M.n, M.g)]
    zb = [swap[x] for x in z]
    vol = pw[4][top]

    def wedge(x, y):
        out = {}
        for m1, c1 in x.items():
            for m2, c2 in y.items():
                if not m1 & m2:
                    out = vadd(out, {m1 | m2: F.mul(F.mul(c1, c2),
                                                    F.num(merge_sign(m1, m2)))}, F)
        return out

    def integral(gamma, h):
        k = {}
        for j in range(4):
            for l in range(4):
                k = vadd(k, wedge({1 << z[j]: F.num(1)}, {1 << zb[l]: F.num(1)}),
                         F, F.mul(F.num(0, 1), h[j][l]))
        v = wedge(wedge(gamma, k), k).get(top, F.num(0))
        return F.mul(v, F.inv(vol))

    rng = random.Random(77)

    def rand_pd(rank, eps):
        h = [[GQ(eps if i == j else 0) for j in range(4)] for i in range(4)]
        for _ in range(rank):
            r = [GQ(rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(4)]
            for i in range(4):
                for j in range(4):
                    h[i][j] = h[i][j] + r[i] * conj_gq(r[j])
        return h

    gamma = M.ch([0, 0, 1, 0, 0], (4, 0), F, pw)
    ok = True
    for _ in range(8):
        h = rand_pd(4, Fr(1))
        s2 = GQ(0)
        for i in range(4):
            for j in range(i + 1, 4):
                s2 = s2 + h[i][i] * h[j][j] - h[i][j] * h[j][i]
        S = h[0][2] * h[1][3] - h[0][3] * h[1][2]
        q = integral(gamma, h)
        ok = ok and q.b == 0 and q.a == (s2.a + 4 * S.a) / 6
    check("n=2, exceptional ratio, c_2 = 1: int gamma kappa_h^2 = (sigma_2(h) + 4 Re "
          "det h[01,23]) / 6 at eight random h, as a multiple of int theta^4", ok)
    # the identity is linear in gamma: at |u| = 2 (R = 3) the coefficient is 2
    gamma3 = M.ch([0, 0, 1, 0, 0], (2, 0), F, pw)
    ok = True
    for _ in range(6):
        h = rand_pd(4, Fr(1))
        s2 = GQ(0)
        for i in range(4):
            for j in range(i + 1, 4):
                s2 = s2 + h[i][i] * h[j][j] - h[i][j] * h[j][i]
        S = h[0][2] * h[1][3] - h[0][3] * h[1][2]
        q = integral(gamma3, h)
        ok = ok and q.b == 0 and q.a == (s2.a + 2 * S.a) / 6
    check("n=2, c_2 = 1, |u| = 2 (R = 3): int gamma kappa_h^2 = (sigma_2(h) + 2 Re "
          "det h[01,23]) / 6 at six random h, so the identity is (c sigma_2 + |u| "
          "Re det) / 6", ok)
    signs = {}
    for label, u, c2 in (("R = 3/4, c_2 > 0", (4, 0), Fr(1)),
                         ("R = 3/4, c_2 < 0", (4, 0), Fr(-1)),
                         ("R = 3/16", (4, 0), Fr(1, 2))):
        gam = M.ch([0, 0, c2, 0, 0], u, F, pw)
        found = set()
        for _ in range(150):
            q = integral(gam, rand_pd(rng.choice([1, 2, 2, 3, 4]), Fr(1, rng.randint(1, 50))))
            found.add((q.a > 0) - (q.a < 0))
        signs[label] = sorted(found)
    check("n=2: at the exceptional ratio int gamma kappa^2 has the sign of c_2 at 150 "
          "random Kaehler classes, while at R = 3/16 both signs occur",
          signs == {"R = 3/4, c_2 > 0": [1], "R = 3/4, c_2 < 0": [-1],
                    "R = 3/16": [-1, 1]}, "%s" % signs)


# ------------------------------------------------------------ --extreme
def extreme(nlist):
    """exact over Q(i), by blocks of torus weight, for larger n"""
    rng = random.Random(2026)
    E = Exact()
    for n in nlist:
        M = Model(n)
        pw = M.theta_powers(E)
        for name, c in shapes(n, rng):
            if name not in ("pure", "c_0 only", "c_1 only", "c_n only", "generic"):
                continue
            rho = hankel_rank(c, n)
            r, a, _ = annihilator(M, c, (1, 2), E, pw=pw)
            check("extreme, n=%d, %s: dim Ann = %d = n^2(4-rho), r = %d = (4+rho)n^2-2n, "
                  "exact" % (n, name, a, r),
                  a == n * n * (4 - rho) and r == (4 + rho) * n * n - 2 * n)


def main():
    rng = random.Random(1111)
    E = Exact()
    print("  (A) the closed form n^2(4-rho), n >= 3")
    item_ABC((3, 4), E, rng)
    print("  (B) the generic annihilator is the polarised Weil tangent space")
    item_B(E, rng)
    print("  (C) the strata and the twist by e^(t theta)")
    item_C(E)
    print("  (D) n = 2, where two K-characters meet")
    item_D(E)
    print("  (E) the first-order Hodge locus of ch")
    item_E(E, rng)
    print("  (F) the Euler characteristic and the rational model")
    item_F(E, rng)
    print("  (G) the exceptional ratio at n = 2")
    item_G(E)
    if "--extreme" in sys.argv:
        nmax = 9
        for a in sys.argv:
            if a.startswith("--nmax="):
                nmax = int(a.split("=")[1])
        print("  (X) extreme: exact for n = 5, ..., %d" % nmax)
        extreme(range(5, nmax + 1))


if __name__ == "__main__":
    print("(LII) the corrected criterion (P2') as a number")
    main()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
