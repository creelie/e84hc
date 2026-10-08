#!/usr/bin/env python3
"""
semireg_fast.py

The same computation as semiregularity.py, carried out modulo a prime so that
it reaches n = 3 and n = 4.  Full rank modulo p implies full rank over Q(i),
so a positive answer here is a certificate; a negative answer is only evidence
and is rechecked exactly.

The prime is chosen congruent to 1 mod 4 so that sqrt(-1) exists in F_p, and
the Hodge decomposition of the split member with X = E_i^n is then defined
over F_p.
"""

import sys
from itertools import combinations

P = 2147483629                      # prime, 1 mod 4


def find_sqrt_minus_one(p):
    for g in range(2, 200):
        t = pow(g, (p - 1) // 4, p)
        if (t * t) % p == p - 1:
            return t
    raise RuntimeError("no sqrt(-1)")


I = find_sqrt_minus_one(P)


# ------------------------------------------------ exterior algebra over F_p
# an element is a dict {bitmask: coefficient mod P}

def wsign(a, b):
    """sign of shuffling the sorted support of b past that of a."""
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
            s = wsign(ka, kb)
            k = ka | kb
            t = ca * cb % P
            if s < 0:
                t = (-t) % P
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


def inv(a):
    return pow(a % P, P - 2, P)


# ------------------------------------------------------------- the model

class Model:
    def __init__(self, n, d):
        self.n, self.d = n, d
        self.m = 2 * n
        self.N = 4 * n
        self.beta = eadd(*[{(1 << self.x(j)) | (1 << self.x(n + j)):
                            wsign(1 << self.x(j), 1 << self.x(n + j))% P}
                           for j in range(1, n + 1)])
        self.betahat = eadd(*[{(1 << self.xi(j)) | (1 << self.xi(n + j)):
                               wsign(1 << self.xi(j),
                                     1 << self.xi(n + j)) % P}
                              for j in range(1, n + 1)])
        self.ell = eadd(*[{(1 << self.x(i)) | (1 << self.xi(i)):
                           wsign(1 << self.x(i), 1 << self.xi(i)) % P}
                          for i in range(1, self.m + 1)])
        # the Weil polarisation: the combination of beta and betahat on which
        # the K-action acts by the norm character (see split_geometry.py, S1)
        self.eta = eadd(escale(d, self.beta), self.betahat)
        self.gamma = eadd(escale(d, self.beta), escale(-1, self.betahat))
        self._hodge()

    def x(self, i):
        return i - 1

    def xi(self, i):
        return self.m + i - 1

    def _hodge(self):
        n = self.n
        for e in (1, P - 1):
            H10 = []
            for k in range(1, n + 1):
                H10.append({1 << self.x(k): 1, 1 << self.x(n + k): I})
            for k in range(1, n + 1):
                H10.append({1 << self.xi(k): 1,
                            1 << self.xi(n + k): e * I % P})
            H01 = [{kk: (-cc) % P if kk in
                    (1 << self.x(n + t) for t in range(1, n + 1)) else cc
                    for kk, cc in v.items()} for v in H10]
            # conjugation: replace I by -I in every coefficient
            H01 = []
            for v in H10:
                w = {}
                for kk, cc in v.items():
                    w[kk] = conj(cc)
                H01.append(w)
            self.H10, self.H01, self.esign = H10, H01, e
            if self.is11(self.ell) and self.is11(self.beta) \
                    and self.is11(self.betahat):
                return
        raise RuntimeError("no sign works")

    # the Hodge type test, done by expanding in the p/q basis
    def basis_inverse(self):
        cols = self.H10 + self.H01
        N = self.N
        M = [[0] * N for _ in range(N)]
        for j, v in enumerate(cols):
            for kk, cc in v.items():
                M[kk.bit_length() - 1][j] = cc
        return matinv(M)

    def gens_in_hodge(self):
        if not hasattr(self, "_g"):
            inv_ = self.basis_inverse()
            self._g = []
            for i in range(self.N):
                self._g.append({1 << j: inv_[j][i] for j in range(self.N)
                                if inv_[j][i]})
        return self._g

    def to_hodge(self, u):
        gens = self.gens_in_hodge()
        out = {}
        for kk, cc in u.items():
            term = {0: cc}
            j = 0
            mm = kk
            while mm:
                low = mm & -mm
                idx = low.bit_length() - 1
                term = wedge(term, gens[idx])
                mm ^= low
            out = eadd(out, term)
        return out

    def is11(self, u):
        h = self.to_hodge(u)
        m = self.m
        for kk in h:
            a = bin(kk & ((1 << m) - 1)).count("1")
            b = bin(kk >> m).count("1")
            if (a, b) != (1, 1):
                return False
        return True

    def klass(self, t):
        a, b, c = t
        return eadd(escale(a, self.beta), escale(b, self.betahat),
                    escale(c, self.ell))

    def expcl(self, lam):
        out = {0: 1}
        pw = {0: 1}
        fact = 1
        for k in range(1, 2 * self.n + 1):
            pw = wedge(pw, lam)
            fact = fact * k % P
            out = eadd(out, escale(inv(fact), pw))
        return out

    def h02(self):
        return [wedge(self.H01[a], self.H01[b])
                for a, b in combinations(range(self.m), 2)]


def conj(c):
    """complex conjugation on F_p, where I stands for sqrt(-1): the
    coefficients we build are of the form u + v I with u, v integers, and we
    store them already reduced, so conjugation is applied at construction
    time by the caller.  Here we only need it on the generators, whose
    coefficients are 1 or +-I."""
    if c == I:
        return (-I) % P
    if c == (-I) % P:
        return I
    return c


def matinv(M):
    n = len(M)
    A = [row[:] + [1 if i == j else 0 for j in range(n)]
         for i, row in enumerate(M)]
    r = 0
    for c in range(n):
        p = None
        for i in range(r, n):
            if A[i][c] % P:
                p = i
                break
        if p is None:
            raise RuntimeError("singular")
        A[r], A[p] = A[p], A[r]
        pv = inv(A[r][c])
        A[r] = [v * pv % P for v in A[r]]
        for i in range(n):
            if i != r and A[i][c] % P:
                f = A[i][c]
                A[i] = [(a - f * b) % P for a, b in zip(A[i], A[r])]
        r += 1
    return [row[n:] for row in A]


def rank_mod(cols):
    """cols: list of dicts.  Returns the rank of the matrix whose columns
    they are."""
    keys = sorted({k for c in cols for k in c})
    idx = {k: i for i, k in enumerate(keys)}
    rows = [[0] * len(cols) for _ in keys]
    for j, c in enumerate(cols):
        for k, v in c.items():
            rows[idx[k]][j] = v
    nr, nc = len(rows), len(cols)
    r = 0
    for c in range(nc):
        p = None
        for i in range(r, nr):
            if rows[i][c] % P:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = inv(rows[r][c])
        rows[r] = [v * pv % P for v in rows[r]]
        for i in range(nr):
            if i != r and rows[i][c] % P:
                f = rows[i][c]
                ri = rows[i]
                rr = rows[r]
                rows[i] = [(a - f * b) % P for a, b in zip(ri, rr)]
        r += 1
        if r == nr:
            break
    return r


def injectivity(mod, lams):
    zb = mod.h02()
    cols = []
    for lam in lams:
        e = mod.expcl(lam)
        for z in zb:
            cols.append(wedge(e, z))
    return rank_mod(cols), len(cols)


def _check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    return (1, 0) if ok else (0, 1)


def main():
    import random
    print("the semiregularity rank modulo a prime, reaching n = 3")
    NP = NF = 0
    random.seed(17)

    rows, ok = [], True
    mf = Model(2, 2)
    for s in (3, 4):
        best = 0
        for _ in range(3):
            ts = [(random.randint(-3, 3), random.randint(-3, 3),
                   random.randint(-3, 3)) for _ in range(s)]
            if len(set(ts)) < s:
                continue
            r, c = injectivity(mf, [mf.klass(t) for t in ts])
            best = max(best, r)
        rows.append("n=2, s=%d: rank %2d of %2d" % (s, best, 6 * s))
        ok = ok and (best == 6 * s if s <= 3 else best < 6 * s)
    p, f = _check("modulo p the n = 2 ranks agree with the exact computation",
                  ok, "\n".join(rows))
    NP += p
    NF += f

    mf3 = Model(3, 3)
    rows, ok = [], True
    for s in (4, 6, 8, 10):
        best = 0
        for _ in range(2):
            ts = [(random.randint(-5, 5), random.randint(-5, 5),
                   random.randint(-5, 5)) for _ in range(s)]
            if len(set(ts)) < s:
                continue
            r, c = injectivity(mf3, [mf3.klass(t) for t in ts])
            best = max(best, r)
        rows.append("n=3, s=%2d: rank %3d of %3d" % (s, best, 15 * s))
        ok = ok and best == 15 * s
    p, f = _check("at n = 3 the map is injective for a general choice of up "
                  "to ten classes, unlike n = 2", ok, "\n".join(rows))
    NP += p
    NF += f

    obj = [(3, -1, 3), (-6, 2, 0), (3, -1, -3),
           (-3, 1, -3), (6, -2, 0), (-3, 1, 3)]
    r, c = injectivity(mf3, [mf3.klass(t) for t in obj])
    p, f = _check("the explicit object of the paper fails injectivity by "
                  "exactly one copy of H^2(O)", r == 75 and c == 90,
                  "rank %d of %d, kernel %d, dim H^2(O) = 15" % (r, c, c - r))
    NP += p
    NF += f

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
