#!/usr/bin/env python3
"""
secant_kernel.py

The Hochschild classes of an abelian n-fold X that preserve the Chern
character of a secant sheaf, and the reduction of the weakened semiregularity
criterion from X x Xhat to X.  Item (XXVIII).

Setting.  X = E_i^n with the principal polarisation t = sum_j x_j ^ x_{n+j},
everything modulo a prime p = 1 mod 4 in the Hodge basis p_a = x_a + i
x_{n+a} of H^{1,0} and q_a = conj(p_a) of H^{0,1}.  A secant sheaf F has
ch(F) = a u_t + b v_t with

    u_t = sum_j (-d)^j t^{2j} / (2j)!,     v_t = sum_j (-d)^j t^{2j+1} / (2j+1)!,

so that ch(F) = c e^{s t} + conj(c) e^{-s t} with s = sqrt(-d) and
c = (a + b/s)/2.  Hochschild cohomology acts on H^*(X) through

    HT^1 = H^{0,1} (+) H^0(T)                       (z, theta)
    HT^2 = H^{0,2} (+) H^1(T) (+) H^0(wedge^2 T)    (z, v, pi)

by multiplication, by the derivation v _|, by the contraction theta _| and
the double contraction pi _|.  The paper proves (Theorem "reduction to the
factor") that

  (K1) no nonzero class in HT^1 preserves ch(F), because the relevant
       determinant is -(a^2 d + b^2) = -N(b + a sqrt(-d));
  (K2) the classes in HT^2 preserving ch(F) are exactly
           { v : v _| t = 0 }  (+)  { (d/2 (pi _| t^2), 0, pi) },
       the polarised deformations of (X, t) and the Poisson directions with
       their gerbe compensation, of dimension n(n+1)/2 + n(n-1)/2 = n^2;
  (K3) for a class B of type (1,1) the B-field transform
           e^B (z, v, pi) = (z + v _| B + 1/2 pi _| B^2,  v + pi _| B,  pi)
       satisfies  x _| (w e^B) = ((e^B x) _| w) e^B  for every class w, which
       is the identity behind the equivalence of the twisted and untwisted
       forms of the criterion.

Checks.

  (S1) (K1) for (n, d, a, b) in a list: the kernel on HT^1 is zero.
  (S2) (K2) for the same list: the kernel on HT^2 has dimension n^2, contains
       the polarised deformations (dimension n(n+1)/2) and the n(n-1)/2
       compensated Poisson classes, and equals their sum.
  (S3) (K3) on random classes w, random x and B = k t, for n = 3, 4.
  (S4) the count n(n+1)/2 + n(n-1)/2 = n^2 = dim D_{n,n}, so the classes of
       (K2) on each factor account for the 2n^2 classes on X x X, twice the
       dimension of the Weil family.
"""

import random
import sys
from itertools import combinations
from math import comb

P = 2147483629


def find_sqrt_minus_one(p):
    for g in range(2, 200):
        t = pow(g, (p - 1) // 4, p)
        if (t * t) % p == p - 1:
            return t
    raise RuntimeError("no sqrt(-1)")


I = find_sqrt_minus_one(P)


def inv(a):
    return pow(a % P, P - 2, P)


def wsign(a, b):
    s = 0
    bb = b
    while bb:
        low = bb & -bb
        j = low.bit_length() - 1
        s += bin(a >> (j + 1)).count("1")
        bb ^= low
    return -1 if s & 1 else 1


def wedge(u, v):
    out = {}
    for ka, ca in u.items():
        for kb, cb in v.items():
            if ka & kb:
                continue
            t = ca * cb % P
            if wsign(ka, kb) < 0:
                t = (-t) % P
            k = ka | kb
            out[k] = (out.get(k, 0) + t) % P
    return {k: c for k, c in out.items() if c}


def eadd(*us):
    out = {}
    for u in us:
        for k, c in u.items():
            out[k] = (out.get(k, 0) + c) % P
    return {k: c for k, c in out.items() if c}


def escale(c, u):
    c %= P
    return {k: v * c % P for k, v in u.items() if v * c % P}


def epow(u, k):
    r = {0: 1}
    for _ in range(k):
        r = wedge(r, u)
    return r


def interior(a, u):
    out = {}
    for m, c in u.items():
        if not (m >> a) & 1:
            continue
        below = bin(m & ((1 << a) - 1)).count("1")
        s = c if below % 2 == 0 else (-c) % P
        k = m ^ (1 << a)
        out[k] = (out.get(k, 0) + s) % P
    return {k: c for k, c in out.items() if c}


def rank_mod(cols):
    keys = sorted({k for c in cols for k in c})
    idx = {k: i for i, k in enumerate(keys)}
    rows = [[0] * len(cols) for _ in keys]
    for j, c in enumerate(cols):
        for k, v in c.items():
            rows[idx[k]][j] = v
    nr, nc = len(rows), len(cols)
    r = 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if rows[i][c] % P), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = inv(rows[r][c])
        rows[r] = [v * pv % P for v in rows[r]]
        for i in range(nr):
            if i != r and rows[i][c] % P:
                f = rows[i][c]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == nr:
            break
    return r


def nullspace(M, ncols):
    rows = [[v % P for v in r] for r in M]
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        iv = inv(rows[r][c])
        rows[r] = [x * iv % P for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [0] * ncols
        v[f] = 1
        for i, c in enumerate(piv):
            v[c] = (-rows[i][f]) % P
        basis.append(v)
    return basis


def rank_rows(vecs):
    if not vecs:
        return 0
    return rank_mod([{i: v for i, v in enumerate(vec) if v % P} for vec in vecs])


# ------------------------------------------------------------ the model

class Fold:
    """H^*(X) for X = E_i^n in the Hodge basis: bits 0..n-1 are p_a, bits
    n..2n-1 are q_a; the polarisation t = sum x_j ^ x_{n+j} = (i/2) sum
    p_a ^ q_a, and we use t = sum_a p_a ^ q_a up to the harmless scalar."""

    def __init__(self, n):
        self.n = n
        self.t = eadd(*[{(1 << a) | (1 << (n + a)): 1} for a in range(n)])

    def h02_basis(self):
        n = self.n
        return [{(1 << (n + a)) | (1 << (n + b)): 1}
                for a, b in combinations(range(n), 2)]

    def h01_basis(self):
        return [{1 << (self.n + a): 1} for a in range(self.n)]

    def deriv(self, c, u):
        """v(p_a) = sum_b c[a*n+b] q_b as a derivation."""
        n = self.n
        out = {}
        for a in range(n):
            ia = interior(a, u)
            if not ia:
                continue
            va = {1 << (n + b): c[a * n + b] % P for b in range(n) if c[a * n + b] % P}
            if va:
                out = eadd(out, wedge(va, ia))
        return out

    def theta(self, c, u):
        """theta = sum_a c[a] d_a acting by interior product."""
        out = {}
        for a in range(self.n):
            if c[a] % P:
                out = eadd(out, escale(c[a], interior(a, u)))
        return out

    def bivec(self, pc, u):
        out = {}
        for (a, b), coef in pc.items():
            if coef % P:
                out = eadd(out, escale(coef, interior(b, interior(a, u))))
        return out

    def bivec_contract_form(self, pc, B):
        """pi _| B as an element of Hom(H^{1,0}, H^{0,1}), for B of type
        (1,1): (pi _| B)(p_a) = sum_b pi_{ab} iota_b B, with pi antisymmetric."""
        n = self.n
        c = [0] * (n * n)
        for (a, b), coef in pc.items():
            if not coef % P:
                continue
            for (x, y, s) in ((a, b, coef % P), (b, a, (-coef) % P)):
                ib = interior(y, B)            # a (0,1) class
                for k, v in ib.items():
                    bb = k.bit_length() - 1 - n
                    c[x * n + bb] = (c[x * n + bb] + s * v) % P
        return c

    def secant_ch(self, d, a, b):
        n = self.n
        u, v = {}, {}
        for j in range(0, n + 1):
            if 2 * j <= n:
                u = eadd(u, escale(((-d) ** j) * inv(fact(2 * j)) % P, epow(self.t, 2 * j)))
            if 2 * j + 1 <= n:
                v = eadd(v, escale(((-d) ** j) * inv(fact(2 * j + 1)) % P, epow(self.t, 2 * j + 1)))
        return eadd(escale(a, u), escale(b, v))

    def act(self, x, w):
        z, c, pc, th = x
        out = {}
        if z:
            out = eadd(out, wedge(z, w))
        if c is not None:
            out = eadd(out, self.deriv(c, w))
        if pc is not None:
            out = eadd(out, self.bivec(pc, w))
        if th is not None:
            out = eadd(out, self.theta(th, w))
        return out


def fact(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    return (1, 0) if ok else (0, 1)


def kernel_of(action, basis, nb):
    imgs = [action(b) for b in basis]
    ks = sorted({k for im in imgs for k in im})
    if not ks:
        return [[1 if i == j else 0 for j in range(nb)] for i in range(nb)]
    M = [[imgs[j].get(k, 0) for j in range(nb)] for k in ks]
    return nullspace(M, nb)


def main():
    print("the Hochschild classes preserving a secant Chern character")
    NP = NF = 0
    random.seed(41)
    cases = [(3, 3, 1, 1), (3, 3, 1, 3), (4, 3, 1, 3), (4, 5, 1, 3), (4, 7, 2, 1),
             (5, 3, 1, 3)]

    # (S1)
    rows, ok = [], True
    for (n, d, a, b) in cases:
        X = Fold(n)
        ch = X.secant_ch(d, a, b)
        basis1 = [({}, None, None, [1 if i == j else 0 for j in range(n)]) for i in range(n)] + \
                 [(z, None, None, None) for z in X.h01_basis()]
        ker1 = kernel_of(lambda x: X.act(x, ch), basis1, len(basis1))
        ok = ok and len(ker1) == 0
        rows.append("n=%d, d=%d, (a,b)=(%d,%d): kernel on HT^1 (dim %d) = %d; "
                    "determinant -(a^2 d + b^2) = %d" % (n, d, a, b, 2 * n, len(ker1),
                                                        -(a * a * d + b * b)))
    p, f = check("(S1) no class in HT^1 preserves a secant Chern character",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    # (S2)
    rows, ok = [], True
    for (n, d, a, b) in cases:
        X = Fold(n)
        ch = X.secant_ch(d, a, b)
        zb = X.h02_basis()
        vb = []
        for u in range(n * n):
            c = [0] * (n * n)
            c[u] = 1
            vb.append(c)
        pb = [{(i, j): 1} for i, j in combinations(range(n), 2)]
        basis2 = [(z, None, None, None) for z in zb] + \
                 [({}, c, None, None) for c in vb] + \
                 [({}, None, pc, None) for pc in pb]
        ker2 = kernel_of(lambda x: X.act(x, ch), basis2, len(basis2))
        # the polarised deformations, as vectors in the same coordinates
        kpol = kernel_of(lambda c: X.deriv(c, X.t), vb, len(vb))
        pol_vecs = [[0] * len(zb) + kv + [0] * len(pb) for kv in kpol]
        # the compensated Poisson classes (d/2 pi _| t^2, 0, pi)
        keys2 = [next(iter(z)) for z in zb]     # the same order as the basis
        pois_vecs = []
        for k, pc in enumerate(pb):
            zc = escale(d * inv(2) % P, X.bivec(pc, wedge(X.t, X.t)))
            vec = [zc.get(kk, 0) for kk in keys2] + [0] * (n * n) + \
                  [1 if kk == k else 0 for kk in range(len(pb))]
            pois_vecs.append(vec)
        dim_ker = len(ker2)
        inside = rank_rows(ker2 + pol_vecs + pois_vecs) == dim_ker
        spans = rank_rows(pol_vecs + pois_vecs) == dim_ker
        # controls: the bare Poisson class (0, 0, pi) and the class with the
        # compensation of the wrong sign do not preserve ch(F)
        bare = all(X.act(({}, None, pc, None), ch) for pc in pb)
        wrong = all(X.act((escale((-d) * inv(2) % P, X.bivec(pc, wedge(X.t, X.t))), None, pc, None), ch)
                    for pc in pb)
        good = (dim_ker == n * n and len(kpol) == n * (n + 1) // 2 and inside and spans
                and bare and wrong)
        ok = ok and good
        rows.append("n=%d, d=%d, (a,b)=(%d,%d): dim HT^2 = %d, kernel %d = n^2; polarised %d, "
                    "Poisson %d, sum equals kernel: %s; bare and wrongly compensated Poisson "
                    "classes act nontrivially: %s"
                    % (n, d, a, b, len(basis2), dim_ker, len(kpol), len(pb), inside and spans,
                       bare and wrong))
    p, f = check("(S2) the classes in HT^2 preserving ch(F) are the polarised deformations "
                 "and the compensated Poisson classes, n^2 in all", ok, "\n".join(rows))
    NP += p
    NF += f

    # (S3) the B-field identity
    rows, ok = [], True
    for n in (3, 4):
        X = Fold(n)
        zb, pb = X.h02_basis(), [{(i, j): 1} for i, j in combinations(range(n), 2)]
        for trial in range(4):
            k = random.randint(1, 5)
            B = escale(k, X.t)
            eB = {0: 1}
            pw = {0: 1}
            for j in range(1, n + 1):
                pw = wedge(pw, B)
                eB = eadd(eB, escale(inv(fact(j)), pw))
            z = {}
            for zz in zb:
                z = eadd(z, escale(random.randrange(P), zz))
            c = [random.randrange(P) for _ in range(n * n)]
            pc = {key: random.randrange(P) for key in combinations(range(n), 2)}
            # a random even class w
            w = {}
            for _ in range(6):
                m = 0
                for _ in range(random.choice((0, 2, 4))):
                    m |= 1 << random.randrange(2 * n)
                if bin(m).count("1") % 2 == 0:
                    w = eadd(w, {m: random.randrange(P)})
            lhs = X.act((z, c, pc, None), wedge(w, eB))
            # e^B x
            zB = eadd(z, X.deriv(c, B), escale(inv(2), X.bivec(pc, wedge(B, B))))
            cB = [(ci + di) % P for ci, di in zip(c, X.bivec_contract_form(pc, B))]
            rhs = wedge(X.act((zB, cB, pc, None), w), eB)
            ok = ok and lhs == rhs
        rows.append("n=%d: x _| (w e^B) = ((e^B x) _| w) e^B on four random (x, w, B = k t)" % n)
    p, f = check("(S3) the B-field transform intertwines the actions", ok, "\n".join(rows))
    NP += p
    NF += f

    # (S4)
    ok = all(n * (n + 1) // 2 + n * (n - 1) // 2 == n * n for n in range(1, 40))
    p, f = check("(S4) n(n+1)/2 + n(n-1)/2 = n^2 = dim D_{n,n}, for n < 40", ok)
    NP += p
    NF += f

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
