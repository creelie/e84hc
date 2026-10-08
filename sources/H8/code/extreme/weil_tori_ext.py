#!/usr/bin/env python3
"""
weil_tori_ext.py  (round 11, track E, item 1)

Stress test of item (LI) / lem:weiltorushodge at larger (n, d):
a very general member of the family S of Weil tori has Hdg^k = 0 for
1 <= k <= 2n-1, k != n, and Hdg^n = the rational Weil plane.

An upper bound for the rational Hodge classes of degree 2k at a very general
member of S is the dimension of the rational classes of type (k,k) at ANY set
of members (the Hodge locus of a rational class is analytic and S is
connected), and that is at most the complex dimension of the intersection of
the spaces H^{k,k} of those members.  The Weil classes give the lower bound 2
in degree 2n, and 0 is the lower bound otherwise.

Parts:
  V  validations of the engine (wt_engine.py) against the paper's code
     (code/weil_tori.py, code/explicit_weil.py, imported read-only):
       V1  Phi_s = +1 on H^{1,0}, -1 on H^{0,1} at random and diagonal members;
       V2  at one member, both criteria (W) and (D) give h^{k,k} =
           binom(2n,k)^2 over all monomials (n = 2, 3; mod q);
       V3  the joint (k,k) space of the binom(2n,n) diagonal members is
           spanned by the weight-zero monomials, binom(2n,k) + 2 delta_{k,n}
           of them (counted over all monomials, n = 2, 3, 4), and the paper's
           own hodge_dimension() at those members, in the x,y basis, returns
           the same number (n = 2 all k; n = 3, k = 1, 4, 5).
  A  the paper's code verbatim (weil_tori.member, is_type_kk, hodge_dimension,
     5 random members for n = 3, 3 for n = 2, ranks mod q with both square
     roots of -d): n = 2, d = 1, 2, 3, 7 and n = 3, d = 1, 2, 3, 7, degrees
     k = 1..2n-1 (the paper runs k <= n only), plus checks (A), (B), (D);
     n = 4, d = 1: checks (B) and hodge_dimension at k = 1.
  C  exact computation over K = Q(delta) on W_k (the joint (k,k) space of all
     diagonal members), cut down by the (k,k) condition at 1 and then 2
     random members, with criterion (W) (n <= 4) and criterion (D) (n <= 5),
     for d = 1, 2, 3, 7 and every k = 1..2n-1.
  F  full columns, random members only (no diagonal member), criterion (D),
     rank mod q by dense elimination: n = 3 all k, n = 4 (d = 1) for
     k = 1, 2, 6, 7 (120 or 1820 columns).
  D  item (D) of (LI): alpha_+ ^ kappa^n = alpha_- ^ kappa^n = 0 for kappa in
     V_+ (x) V_-; and with a component beta in wedge^2 V_- added, which of
     the two products becomes nonzero (n = 2, 3 with the paper's code; n = 4,
     5 with the engine).

Every number is exact (Fractions over Q(delta)) or a rank modulo a prime q in
which -d is a square; a rank mod q is a LOWER bound for the rank over
Q(delta), hence the kernel dimensions mod q are UPPER bounds.

Run:  python3 weil_tori_ext.py [parts]     parts from "VACFD" (default all)
"""
import random
import os
import sys
import time
from fractions import Fraction as F
from itertools import combinations
from math import comb

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import explicit_weil as EW   # noqa: E402
import weil_tori as WT       # noqa: E402
import wt_engine as E        # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("\n         " + detail) if detail else ""), flush=True)


# ----------------------------------------------------------- dense mod q
def rank_mod_q(A, q):
    """rank of the int64 matrix A (entries in [0,q)) modulo q < 2^31, by
    Gaussian elimination in place; every product of two residues fits in a
    signed 64-bit integer"""
    A = A % q
    nr, nc = A.shape
    r = 0
    for c in range(nc):
        if r == nr:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        p = r + int(nz[0])
        if p != r:
            A[[r, p]] = A[[p, r]]
        inv = pow(int(A[r, c]), q - 2, q)
        A[r, c:] = A[r, c:] * inv % q
        below = r + 1 + np.nonzero(A[r + 1:, c])[0]
        if len(below):
            A[below, c:] = (A[below, c:]
                            - np.outer(A[below, c], A[r, c:]) % q) % q
        r += 1
    return r


# ----------------------------------------------------------- part V
def part_V():
    print("=" * 72)
    print("V: validation of the engine")
    rng = random.Random(11)
    for n in (2, 3, 4):
        KF = E.Kfield(1 if n != 3 else 7)
        mems = [E.random_member(KF, n, rng) for _ in range(2)]
        mems += [E.diagonal_member(KF, n, S)
                 for S in list(combinations(range(2 * n), n))[:3]]
        check("V1 n=%d, d=%d: Phi = +1 on H^{1,0} and -1 on H^{0,1} at 2 "
              "random and 3 diagonal members (exact)" % (n, KF.d),
              all(M.check_phi() for M in mems))

    # V2: one member, all monomials, both criteria, mod q
    for n, d in ((2, 1), (2, 3), (3, 2)):
        KF = E.Kfield(d)
        FQ = E.Fq(d)
        M = E.random_member(KF, n, rng).reduce_mod(FQ)
        dims_W, dims_D = [], []
        for k in range(1, 2 * n):
            monos = [sum(1 << g for g in mu)
                     for mu in combinations(range(4 * n), 2 * k)]
            col = {m: i for i, m in enumerate(monos)}
            # (D)
            rows = {}
            for m in monos:
                for key, v in E.derivation(FQ, M.Phi, m, 1).items():
                    rows.setdefault(key, {})[col[m]] = v
            A = np.zeros((len(rows), len(monos)), dtype=np.int64)
            for i, rw in enumerate(rows.values()):
                for j, v in rw.items():
                    A[i, j] = v
            dims_D.append(len(monos) - rank_mod_q(A, FQ.q))
            # (W): c ^ h_I = 0 and c ^ hbar_I = 0, |I| = 2n-k+1
            rowsW = {}
            for side, vecs in (("h", M.hol), ("hb", M.antihol)):
                for I, hI in E.hI_products(FQ, vecs, 2 * n - k + 1).items():
                    for m in monos:
                        for key, v in E.wedge(FQ, {m: 1}, hI).items():
                            rowsW.setdefault((side, I, key), {})[col[m]] = v
            A = np.zeros((len(rowsW), len(monos)), dtype=np.int64)
            for i, rw in enumerate(rowsW.values()):
                for j, v in rw.items():
                    A[i, j] = v
            dims_W.append(len(monos) - rank_mod_q(A, FQ.q))
        want = [comb(2 * n, k) ** 2 for k in range(1, 2 * n)]
        check("V2 n=%d, d=%d: at one random member both criteria give "
              "dim H^{k,k} = binom(2n,k)^2 over all monomials, k = 1..%d"
              % (n, d, 2 * n - 1), dims_W == want and dims_D == want,
              "(W) %s  (D) %s  expected %s" % (dims_W, dims_D, want))

    # V3: weight-zero monomials of the diagonal members
    for n in (2, 3, 4):
        t0 = time.time()
        counts = []
        okmask = True
        KF = E.Kfield(1)
        for k in range(1, 2 * n):
            cnt, good = E.weight_zero_monomials(n, k)
            counts.append(cnt)
            Wmasks = sorted(next(iter(el)) for _, el in E.W_basis(KF, n, k))
            okmask = okmask and Wmasks == sorted(good)
        want = [comb(2 * n, k) + (2 if k == n else 0) for k in range(1, 2 * n)]
        check("V3 n=%d: the monomials of weight zero for all %d diagonal "
              "members are exactly the basis of W_k; counts k = 1..%d: %s"
              % (n, comb(2 * n, n), 2 * n - 1, counts),
              counts == want and okmask, "expected %s (%.1fs)"
              % (want, time.time() - t0))

    # V3': the paper's own hodge_dimension at the diagonal members (x,y basis)
    for n, d, ks in ((2, 1, (1, 2, 3)), (2, 3, (1, 2, 3)),
                     (3, 2, (1, 4, 5))):
        M = EW.Model(n, d)
        m = 2 * n
        members = []
        for S in combinations(range(1, m + 1), n):
            members.append([M.eigvec(j, +1) for j in S]
                           + [M.eigvec(j, -1) for j in range(1, m + 1)
                              if j not in S])
        got = {}
        for k in ks:
            t0 = time.time()
            got[k] = WT.hodge_dimension(M, k, members)
        want = {k: comb(m, k) + (2 if k == n else 0) for k in ks}
        check("V3' n=%d, d=%d: weil_tori.hodge_dimension at all %d diagonal "
              "members (paper's code, x,y basis) = binom(2n,k) + 2 delta_{k,n}"
              " for k in %s" % (n, d, len(members), list(ks)), got == want,
              "got %s, expected %s" % (got, want))


# ----------------------------------------------------------- part A
def part_A():
    print("=" * 72)
    print("A: the paper's own code (weil_tori.py), extended")
    rng = random.Random(20260925)
    for n, d, count in ((2, 1, 3), (2, 3, 3), (2, 2, 3), (2, 7, 3),
                        (3, 2, 5), (3, 1, 5), (3, 3, 5), (3, 7, 5)):
        t0 = time.time()
        M = EW.Model(n, d)
        members = [WT.member(M, rng) for _ in range(count)]
        w1, w2 = M.omega1(), M.omega2()
        okA = all(WT.is_type_kk(M, w, n, hol) for w in (w1, w2)
                  for hol in members)
        check("A n=%d, d=%d: omega_1, omega_2 of type (n,n) at %d members"
              % (n, d, count), okA)
        eta = M.eta()
        bal = WT.balanced(M)
        okB = WT.is_type_kk(M, eta, 1, bal) and \
            not any(WT.is_type_kk(M, eta, 1, hol) for hol in members)
        check("A n=%d, d=%d: eta of type (1,1) at the balanced member and at "
              "none of the members used" % (n, d), okB)
        dims = {}
        for k in range(1, 2 * n):
            tk = time.time()
            dims[k] = WT.hodge_dimension(M, k, members)
            print("      k=%d: dim %d  (%.1fs, q = %d)"
                  % (k, dims[k], time.time() - tk, WT.PRIME), flush=True)
        want = {k: (2 if k == n else 0) for k in range(1, 2 * n)}
        check("A n=%d, d=%d: rational (k,k) classes at all %d members, "
              "k = 1..%d: %s (upper bounds mod q)"
              % (n, d, count, 2 * n - 1, [dims[k] for k in sorted(dims)]),
              dims == want, "%.1fs" % (time.time() - t0))
        # (D)
        vp = [M.eigvec(j, +1) for j in range(1, M.m + 1)]
        vm = [M.eigvec(j, -1) for j in range(1, M.m + 1)]
        kappa = {}
        for a in vp:
            for b in vm:
                c = EW.sc(rng.randint(-4, 4), rng.randint(-4, 4))
                kappa = EW.eadd(kappa, EW.emulsc(EW.wedge(a, b, d), c, d))
        kn = EW.ewedgepow(kappa, n, d)
        ap, am = M.omega(+1), M.omega(-1)
        mixed_zero = not EW.wedge(ap, kn, d) and not EW.wedge(am, kn, d)
        beta = {}
        for j in range(n):
            beta = EW.eadd(beta, EW.wedge(vm[2 * j], vm[2 * j + 1], d))
        kappa2 = EW.eadd(kappa, beta)
        kn2 = EW.ewedgepow(kappa2, n, d)
        plus_nz = bool(EW.wedge(ap, kn2, d))
        minus_nz = bool(EW.wedge(am, kn2, d))
        check("A n=%d, d=%d: alpha_+ ^ kappa^n = alpha_- ^ kappa^n = 0; with "
              "beta in wedge^2 V_- added, alpha_+ ^ (kappa+beta)^n != 0"
              % (n, d), mixed_zero and plus_nz)
        check("A n=%d, d=%d: with beta in wedge^2 V_- added, alpha_- ^ "
              "(kappa+beta)^n is STILL ZERO (the paper's text says both "
              "products become nonzero)" % (n, d), not minus_nz,
              "alpha_+ ^ (kappa+beta)^n nonzero: %s; alpha_- ^ "
              "(kappa+beta)^n nonzero: %s" % (plus_nz, minus_nz))

    # n = 4, d = 1: (B) and k = 1 with the paper's code
    n, d, count = 4, 1, 3
    t0 = time.time()
    M = EW.Model(n, d)
    rng4 = random.Random(4)
    members = [WT.member(M, rng4) for _ in range(count)]
    eta = M.eta()
    okB = WT.is_type_kk(M, eta, 1, WT.balanced(M)) and \
        not any(WT.is_type_kk(M, eta, 1, hol) for hol in members)
    check("A n=4, d=1: eta of type (1,1) at the balanced member and at none "
          "of %d random members" % count, okB, "%.1fs" % (time.time() - t0))
    t0 = time.time()
    dim1 = WT.hodge_dimension(M, 1, members)
    check("A n=4, d=1: weil_tori.hodge_dimension, degree 2 (k = 1), %d random "
          "members: %d" % (count, dim1), dim1 == 0,
          "%.1fs, q = %d" % (time.time() - t0, WT.PRIME))


# ----------------------------------------------------------- part C
def columns_D(KF, M, basis):
    return [E.apply_derivation(KF, M.Phi, el) for el in basis]


def part_C(cases):
    print("=" * 72)
    print("C: exact computation over Q(delta) on W_k (all diagonal members) "
          "cut by random members")
    rng = random.Random(20260926)
    for n, d, crits in cases:
        KF = E.Kfield(d)
        mems = [E.random_member(KF, n, rng, name="R%d" % i) for i in range(2)]
        for k in range(1, 2 * n):
            t0 = time.time()
            basis = [el for _, el in E.W_basis(KF, n, k)]
            want = 2 if k == n else 0
            info = []
            finals = []
            if "D" in crits:
                # criterion (D), every condition, after 1 and after 2 members
                cols1 = columns_D(KF, mems[0], basis)
                cols2 = columns_D(KF, mems[1], basis)
                r1, _ = E.sparse_rank(KF, cols1)
                merged = []
                for c1, c2 in zip(cols1, cols2):
                    v = {(0, key): x for key, x in c1.items()}
                    v.update({(1, key): x for key, x in c2.items()})
                    merged.append(v)
                r12, _ = E.sparse_rank(KF, merged)
                seq = [len(basis) - r1, len(basis) - r12]
                info.append("(D) after 1, 2 members: %s" % seq)
                finals.append(seq[-1])
            if "W" in crits:
                # criterion (W): conditions c ^ h_I, c ^ hbar_I at both
                # members, added in batches until the kernel reaches the
                # lower bound `want` (it cannot go lower: the Weil classes
                # lie in it), or all conditions are used
                size = 2 * n - k + 1
                conds = []
                prods = [[E.hI_products(KF, vecs, size).items()
                          for vecs in (M.hol, M.antihol)] for M in mems]
                lists = [list(p) for pm in prods for p in pm]
                # interleave: member 0 hol, member 1 hol, member 0 antihol...
                order = [lists[0], lists[2], lists[1], lists[3]]
                L = max(len(x) for x in order)
                for t in range(L):
                    for li, lst in enumerate(order):
                        if t < len(lst):
                            conds.append((li, lst[t][0], lst[t][1]))
                cols = [dict() for _ in basis]
                used = 0
                kern = len(basis)
                batch = 1
                while used < len(conds) and kern > want:
                    new = conds[used:used + batch]
                    for bi, el in enumerate(basis):
                        for li, I, hI in new:
                            for key, x in E.wedge(KF, el, hI).items():
                                cols[bi][(li, I, key)] = x
                    used += len(new)
                    batch *= 2
                    r, _ = E.sparse_rank(KF, cols)
                    kern = len(basis) - r
                info.append("(W) %d of %d conditions used, kernel %d"
                            % (used, len(conds), kern))
                finals.append(kern)
            check("C n=%d, d=%d, k=%d: dim W_k = %d; %s (expected %d)"
                  % (n, d, k, len(basis), "; ".join(info), want),
                  all(f == want for f in finals),
                  "exact over Q(sqrt(-%d)), %.1fs" % (d, time.time() - t0))
            if k == n:
                okw = all(not E.apply_derivation(KF, M.Phi, el)
                          for M in mems for el in basis[-2:])
                check("C n=%d, d=%d: D_Phi(alpha_+) = D_Phi(alpha_-) = 0 at "
                      "both random members" % (n, d), okw)


# ----------------------------------------------------------- part F
def part_F(cases):
    print("=" * 72)
    print("F: all monomials, random members only, criterion (D), rank mod q")
    rng = random.Random(20260927)
    for n, d, ks, nmem in cases:
        KF = E.Kfield(d)
        FQ = E.Fq(d)
        mems = [E.random_member(KF, n, rng).reduce_mod(FQ)
                for _ in range(nmem)]
        for k in ks:
            t0 = time.time()
            monos = [sum(1 << g for g in mu)
                     for mu in combinations(range(4 * n), 2 * k)]
            col = {m: i for i, m in enumerate(monos)}
            N = len(monos)
            want = 2 if k == n else 0
            blocks = []
            seq = []
            for mi, M in enumerate(mems):
                B = np.zeros((N, N), dtype=np.int64)
                for m in monos:
                    j = col[m]
                    for key, v in E.derivation(FQ, M.Phi, m, 1).items():
                        B[col[key], j] = (B[col[key], j] + v) % FQ.q
                blocks.append(B)
                if mi == 0 and N > 200:
                    continue            # single member: see V2
                A = np.vstack(blocks)
                seq.append((mi + 1, N - rank_mod_q(A, FQ.q)))
                del A
                if seq[-1][1] == want:
                    break
            check("F n=%d, d=%d, k=%d: %d columns; kernel mod q with "
                  "(members, kernel): %s (expected final %d)"
                  % (n, d, k, N, seq, want), seq[-1][1] == want,
                  "q = %d, %.1fs" % (FQ.q, time.time() - t0))
            del blocks


# ----------------------------------------------------------- part D
def part_D():
    print("=" * 72)
    print("D: alpha_pm ^ kappa^n, engine, n = 4, 5")
    rng = random.Random(5)
    for n in (4, 5):
        KF = E.Kfield(1)
        m = 2 * n
        kappa = {}
        for a in range(m):
            for b in range(m):
                c = (F(rng.randint(-4, 4)), F(rng.randint(-4, 4)))
                if KF.iszero(c):
                    continue
                key = (1 << a) | (1 << (m + b))
                kappa[key] = KF.add(kappa.get(key, KF.zero), c)
        beta = {}
        for j in range(n):
            beta[(1 << (m + 2 * j)) | (1 << (m + 2 * j + 1))] = KF.one
        ap = {(1 << m) - 1: KF.one}
        am = {((1 << (2 * m)) - 1) ^ ((1 << m) - 1): KF.one}

        def power(u, e):
            r = {0: KF.one}
            for _ in range(e):
                r = E.wedge(KF, r, u)
            return r
        kn = power(kappa, n)
        k2 = dict(kappa)
        for key, v in beta.items():
            k2[key] = KF.add(k2.get(key, KF.zero), v)
        kn2 = power(k2, n)
        z1 = not E.wedge(KF, ap, kn) and not E.wedge(KF, am, kn)
        p2 = bool(E.wedge(KF, ap, kn2))
        m2 = bool(E.wedge(KF, am, kn2))
        check("D n=%d: alpha_+ ^ kappa^n = alpha_- ^ kappa^n = 0 for random "
              "kappa in V_+ (x) V_-; with beta in wedge^2 V_- added: "
              "alpha_+ product nonzero %s, alpha_- product nonzero %s"
              % (n, p2, m2), z1 and p2 and not m2)


if __name__ == "__main__":
    parts = sys.argv[1] if len(sys.argv) > 1 else "VACFD"
    T = time.time()
    if "V" in parts:
        part_V()
    if "A" in parts:
        part_A()
    if "C" in parts:
        cases = []
        for n in (2, 3, 4):
            for d in (1, 2, 3, 7):
                cases.append((n, d, ("W", "D")))
        for d in (1, 2, 3, 7):
            cases.append((5, d, ("D",)))
        part_C(cases)
    if "F" in parts:
        part_F([(3, 1, range(1, 6), 3), (3, 7, range(1, 6), 3),
                (4, 1, (1, 2, 6, 7), 3)])
    if "D" in parts:
        part_D()
    print()
    print("  %d checks passed, %d failed  (%.1fs)"
          % (len(PASS), len(FAIL), time.time() - T))
    raise SystemExit(0 if not FAIL else 1)
