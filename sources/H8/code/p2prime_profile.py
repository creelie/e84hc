#!/usr/bin/env python3
"""
p2prime_profile.py

The whole Hochschild profile of a Chern character of the corrected form
(P2').  Item (LIII).

In the model of p2prime.py, let ch = sum_k c_k theta^k + u alpha_+ +
conj(u) alpha_-, u != 0, and let rho_k be the rank of contraction

    HT^k(A) -> H^*(A),   xi |-> xi _| ch.

Granting the compatibility sigma_E o ev_E = ( ) _| ch(E) in degree k, as
cor:hhfactor(iii) does, rho_k is a lower bound for dim Ext^k(E,E); in degree
two no compatibility beyond the one used for thm:p2numerical is needed.

Put C_l = l! c_l, let H be the (n+1) x (n+1) Hankel matrix [C_{p+q}] and
r = rank H (the border rank of the binary form sum_k c_k x^k y^{2n-k} /
(2n-k)!), K = antidiag((-1)^a binom(n,a)), and
d = dim ker((KH)^2 - |u|^2) computed in the normalisation of the model.
What is checked, exactly over Q(i):

  (A) the closed formula
          rho_0 = rho_2n = 1,   rho_k = 0 for k > 2n,
          rho_k = 2 binom(2n,k) + M_k min(k+1, 2n+1-k, r) - [k = n] d
      for 1 <= k <= 2n-1, with M_k = sum_{i+j=k, 1<=i,j<=n-1}
      binom(n,i) binom(n,j), for n = 2, 3 in every degree and for eight
      shapes (pure, c_0 only, c_1 only, c_n only, c_2n only, e^theta, two
      exponentials, generic), with two values of u; the pure case gives the
      paper's 2 binom(2n,k);

  (B) the symmetry rho_k = rho_{2n-k};

  (C) the middle degeneracy: for c_n theta^n alone, KH is diagonal with
      entries (-1)^a binom(n,a) n! c_n, and rho_n drops by d exactly at
      |u| = binom(n,a) n! |c_n| (n = 2, 3), and only in degree n;

  (D) chi(E,E) is even: on the lattice wedge^{2n} H^1(A,Z) the form
      int x ^ y pairs each monomial with its complement only, so int x^2 is
      even (checked on all of wedge^{2n} Z^{4n} for n = 1, 2, 3 by the
      Gram matrix), and chi(E,E) = sum_k (-1)^k int ch_k ch_{2n-k} is a sum
      of such terms and of 2 int ch_k ch_{2n-k}, k < n.  At n = 2 the
      special points with d = 1 have rho_2 = 23, so dim Ext^2 = rho_2 is
      impossible there.

With --extreme, (A) is also run for n = 4 in every degree (HT^k has
dimension up to 12870) and for n = 5 in degrees up to 3.

Nothing here constructs an object, and nothing bears on whether (P2') holds.

Run:  python3 p2prime_profile.py            (about half a minute)
      python3 p2prime_profile.py --extreme
"""

import sys
import random
from fractions import Fraction as Fr
from math import comb, factorial
from itertools import combinations

from p2prime import (Exact, Model, op_apply, rank_and_kernel, rank_q)

PASS, FAIL = [], []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % (tag, name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


# ----------------------------------------------------------- the formula
def middle_hankel(c, n):
    C = [factorial(l) * Fr(c[l]) for l in range(2 * n + 1)]
    return [[C[p + q] for q in range(n + 1)] for p in range(n + 1)]


def hankel_rank_k(c, n, k):
    C = [factorial(l) * Fr(c[l]) for l in range(2 * n + 1)]
    return rank_q([[C[p + q] for q in range(2 * n - k + 1)] for p in range(k + 1)])


def degeneracy(c, n, X):
    H = middle_hankel(c, n)
    K = [[((-1) ** a * comb(n, a)) if a + b == n else 0 for b in range(n + 1)]
         for a in range(n + 1)]
    KH = [[sum(K[i][l] * H[l][j] for l in range(n + 1)) for j in range(n + 1)]
          for i in range(n + 1)]
    Y2 = [[sum(KH[i][l] * KH[l][j] for l in range(n + 1)) for j in range(n + 1)]
          for i in range(n + 1)]
    A = [[Y2[i][j] - (X if i == j else 0) for j in range(n + 1)] for i in range(n + 1)]
    return n + 1 - rank_q(A)


def formula(c, n, X):
    g = 2 * n
    r = rank_q(middle_hankel(c, n))
    out = []
    for k in range(2 * g + 1):
        if k == 0 or k == g:
            out.append(1)
        elif k > g:
            out.append(0)
        else:
            Mk = sum(comb(n, i) * comb(n, k - i) for i in range(1, n) if 1 <= k - i <= n - 1)
            v = 2 * comb(g, k) + Mk * min(k + 1, g + 1 - k, r)
            if k == n:
                v -= degeneracy(c, n, X)
            out.append(v)
    return out


# ------------------------------------------------------- exact ranks
def weight_key(M, mask_ops):
    """torus weight of an HT monomial, modulo (1,...,1)"""
    w = [0] * M.g
    for s in mask_ops:
        kind, bit = M.ops[s][0], M.ops[s][1]
        j = bit % M.g
        pos = bit < M.g              # an e-generator
        if kind == "w":
            w[j] += 1 if pos else -1
        else:
            w[j] += -1 if pos else 1
    return tuple(x - w[0] for x in w)


def profile(M, c, u, F, kmax=None, pw=None):
    chv = M.ch(c, u, F, pw)
    nops = len(M.ops)
    kmax = nops if kmax is None else kmax
    out = []
    for k in range(kmax + 1):
        blocks = {}
        for sub in combinations(range(nops), k):
            img = chv
            for s in reversed(sub):
                o = M.ops[s]
                img = op_apply(o[0], o[1], img, F)
                if not img:
                    break
            if img:
                blocks.setdefault(weight_key(M, sub), []).append(img)
        out.append(sum(rank_and_kernel(cols, F)[0] for cols in blocks.values()))
    return out


def shapes(n, rng):
    g = 2 * n
    z = [0] * (g + 1)

    def at(k, v=1):
        c = list(z)
        c[k] = v
        return c
    return [("pure", z), ("c_0 only", at(0)), ("c_1 only", at(1)),
            ("c_n only", at(n)), ("c_2n only", at(g)),
            ("e^theta", [Fr(1, factorial(k)) for k in range(g + 1)]),
            ("two exponentials", [Fr(1, factorial(k)) + 3 * Fr(2) ** k / factorial(k)
                                  for k in range(g + 1)]),
            ("generic", [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(g + 1)])]


def item_A(nlist, rng, kmax=None):
    F = Exact()
    for n in nlist:
        M = Model(n)
        pw = M.theta_powers(F)
        for name, c in shapes(n, rng):
            ok, shown = True, None
            for u in ((1, 0), (2, 3)):
                X = u[0] ** 2 + u[1] ** 2
                got = profile(M, c, u, F, kmax=kmax, pw=pw)
                want = formula(c, n, X)[:len(got)]
                ok = ok and got == want
                shown = got
            check("n=%d, %s: rho_k = 2 binom(2n,k) + M_k min(k+1,2n+1-k,r) - [k=n]d"
                  % (n, name), ok, "profile %s" % shown[:2 * n + 1])


def item_B(rng):
    F = Exact()
    for n in (2, 3):
        M = Model(n)
        ok = True
        for name, c in shapes(n, rng):
            p = profile(M, c, (1, 2), F)
            ok = ok and all(p[k] == p[2 * n - k] for k in range(2 * n + 1)) and \
                all(v == 0 for v in p[2 * n + 1:])
        check("n=%d: rho_k = rho_(2n-k), and rho_k = 0 for k > 2n, on every shape" % n, ok)


def item_C():
    F = Exact()
    for n in (2, 3):
        M = Model(n)
        pw = M.theta_powers(F)
        c = [0] * (2 * n + 1)
        c[n] = 1
        rows, ok = [], True
        base = profile(M, c, (1, 0), F, pw=pw)
        specials = sorted({comb(n, a) * factorial(n) for a in range(n + 1)})
        for s in specials:
            p = profile(M, c, (s, 0), F, pw=pw)
            d = degeneracy(c, n, Fr(s * s))
            drop = [base[k] - p[k] for k in range(len(p))]
            rows.append("|u| = %d: rho = %s, d = %d" % (s, p[:2 * n + 1], d))
            ok = ok and d > 0 and drop[n] == d and \
                all(drop[k] == 0 for k in range(len(p)) if k != n)
        check("n=%d, c_n theta^n: rho_n drops by d exactly at |u| = binom(n,a) n! |c_n|, "
              "and only in degree n" % n, ok, "\n".join(rows))


def item_D():
    ok, rows = True, []
    for n in (1, 2, 3):
        g = 2 * n
        N = 2 * g
        mons = list(combinations(range(N), g))
        idx = {m: i for i, m in enumerate(mons)}
        # Gram matrix of int x ^ y on wedge^g Z^N: each monomial pairs only
        # with its complement, with sign +-1
        diag_even = True
        pairs = 0
        for m in mons:
            comp = tuple(x for x in range(N) if x not in m)
            if comp in idx:
                pairs += 1
                if m == comp:
                    diag_even = False
        ok = ok and diag_even and pairs == len(mons)
        rows.append("n=%d: %d monomials, each paired with its complement only, "
                    "no monomial paired with itself" % (n, len(mons)))
    check("int x^2 is even on wedge^(2n) H^1(A,Z), so chi(E,E) is even", ok,
          "\n".join(rows))
    # n = 2, a point with d = 1: rho_2 = 23 is odd
    F = Exact()
    M = Model(2)
    c = [0, 0, 1, 0, 0]
    p = profile(M, c, (4, 0), F, kmax=2)
    check("n=2, theta^2 + omega at |u| = 4: rho_2 = 23, odd, so the numerical "
          "criterion dim Ext^2 = rho_2 cannot hold there", p[2] == 23,
          "rho_0..rho_2 = %s" % p)


def main():
    rng = random.Random(53)
    print("  (A) the closed formula, n = 2, 3, every degree")
    item_A((2, 3), rng)
    print("  (B) the symmetry")
    item_B(rng)
    print("  (C) the middle degeneracy")
    item_C()
    print("  (D) parity")
    item_D()
    if "--extreme" in sys.argv:
        print("  (X) extreme: n = 4 in every degree, n = 5 up to degree 3")
        item_A((4,), rng)
        item_A((5,), rng, kmax=3)


if __name__ == "__main__":
    print("(LIII) the Hochschild profile of a (P2') Chern character")
    main()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
