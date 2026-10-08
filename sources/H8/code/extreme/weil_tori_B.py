#!/usr/bin/env python3
"""
weil_tori_B.py  (round 11, track E, item 1, part B)

An independent upper bound at n = 4 (and n = 5 where it fits) that uses only
THREE diagonal members (the balanced one and two others) instead of all
binom(2n,n), so that the special CM-like members play a much smaller role:

  1. the joint (k,k) space of the three diagonal members is spanned by the
     monomials (eigenbasis e, f) of weight zero for the three diagonal
     operators Phi_S; it is computed exactly by counting;
  2. on that monomial space, the (k,k) condition at r random members is
     imposed with criterion (D) (D_Phi c = 0), reduced modulo a prime q in
     which -d is a square;
  3. the rank is computed after a random compression S = R * M (R with
     entries < 2^10, M the sparse condition matrix, every intermediate sum
     below 2^50, then reduced mod q), followed by dense Gaussian elimination
     mod q.  rank(S) <= rank(M mod q) <= rank over Q(delta), so the kernel
     found is an UPPER bound for the complex (k,k) classes at the members
     used, hence for the rational Hodge classes of a very general member.

Run:  python3 weil_tori_B.py
"""
import random
import os
import sys
import time
from itertools import combinations

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wt_engine as E            # noqa: E402
from weil_tori_ext import rank_mod_q   # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("\n         " + detail) if detail else ""), flush=True)


def weight_zero(n, k, Ss):
    m = 2 * n
    out = []
    for mu in combinations(range(2 * m), 2 * k):
        v = [0] * m
        for g in mu:
            if g < m:
                v[g] += 1
            else:
                v[g - m] -= 1
        tot = sum(v)
        if all(2 * sum(v[j] for j in S) - tot == 0 for S in Ss):
            out.append(sum(1 << g for g in mu))
    return out


def run(n, d, k, nrand, seed, ndiag=3):
    t0 = time.time()
    rng = random.Random(seed)
    m = 2 * n
    allS = list(combinations(range(m), n))
    Ss = [tuple(range(n))] + rng.sample(allS[1:], ndiag - 1)
    cols = weight_zero(n, k, Ss)
    C = len(cols)
    KF = E.Kfield(d)
    FQ = E.Fq(d)
    q = FQ.q
    want = 2 if k == n else 0
    mems = [E.random_member(KF, n, rng).reduce_mod(FQ) for _ in range(nrand)]
    # sparse condition rows: key (member, output monomial) -> {col: val}
    rows = {}
    for j, mask in enumerate(cols):
        for mi, M in enumerate(mems):
            for key, v in E.derivation(FQ, M.Phi, mask, 1).items():
                rows.setdefault((mi, key), {})[j] = v % q
    rows = [r for r in rows.values() if any(x % q for x in r.values())]
    Rn = C + 40
    S = np.zeros((Rn, C), dtype=np.int64)
    nprng = np.random.default_rng(seed)
    for r in rows:
        js = np.fromiter(r.keys(), dtype=np.int64)
        vs = np.fromiter(r.values(), dtype=np.int64)
        coef = nprng.integers(0, 1 << 10, size=Rn, dtype=np.int64)
        S[:, js] += np.outer(coef, vs)
        # column j lies in at most nrand * 2k * 2n rows, each contributing
        # less than 2^10 * 2^31 = 2^41, so every entry stays below 2^50
    S %= q
    rk = rank_mod_q(S, q)
    kern = C - rk
    check("B n=%d, d=%d, k=%d: diagonal members %s give %d monomial columns; "
          "with %d random members the kernel mod q is %d (lower bound %d)"
          % (n, d, k, Ss, C, nrand, kern, want), kern == want,
          "%d condition rows compressed to %d; q = %d; %.1fs"
          % (len(rows), Rn, q, time.time() - t0))
    return kern


if __name__ == "__main__":
    T = time.time()
    mode = sys.argv[1] if len(sys.argv) > 1 else "base"
    if mode == "base":
        configs = [(4, 1, (2, 3, 4, 5, 6), 2, 3), (4, 3, (3, 4, 5), 2, 3),
                   (4, 7, (4,), 2, 3)]
    elif mode == "balanced":
        # only ONE diagonal member, the balanced one (which lies on the
        # polarised family), plus random members
        configs = [(4, 1, (3, 5, 4), 2, 1)]
    elif mode == "two":
        # two diagonal members (the balanced one and one other)
        configs = [(4, 1, (4,), 2, 2)]
    elif mode == "n5":
        configs = [(5, 1, tuple(range(1, 10)), 2, 5),
                   (5, 3, (4, 5, 6), 2, 5)]
    for n, d, ks, nrand, ndiag in configs:
        for k in ks:
            kern = run(n, d, k, nrand, seed=1000 * n + 10 * d + k,
                       ndiag=ndiag)
            if kern > (2 if k == n else 0):
                run(n, d, k, nrand + 1, seed=1000 * n + 10 * d + k + 7,
                    ndiag=ndiag)
    print()
    print("  %d checks passed, %d failed  (%.1fs)"
          % (len(PASS), len(FAIL), time.time() - T))
    raise SystemExit(0 if not FAIL else 1)
