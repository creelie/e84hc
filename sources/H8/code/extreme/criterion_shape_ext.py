#!/usr/bin/env python3
"""
criterion_shape_ext.py  (round 11, track E, item 3)

Stress test of item (L), code/criterion_shape.py, at larger n.  The original
modules are imported read-only; nothing under /home/user/H8 is written.

(D) The Euler characteristic argument.  With e_k = dim Ext^k(E,E),
    Serre duality e_k = e_{2n-k}, the lower bounds of item (XXXVIII)
        e_0 >= 1,  e_1 >= 4n,  e_k >= m_k = 2 binom(2n,k)  (2 <= k <= n),
    the criterion e_2 = m_2 = 2n(2n-1), and chi(E,E) >= 1 (thm:p2endo(i)),
    what is the least possible e_0 = dim End(E)?
    Writing x_k = e_k - m_k >= 0 (x_0 = e_0 - 1, x_2 = 0),
        chi = -2 + sum_k (-1)^k w_k x_k,   w_k = 2 (k < n), w_n = 1,
    so the question is a finite integer program.  It is solved here by
    exhaustive enumeration of all excess vectors with entries 0..B (B = 4,
    which suffices: see the report), for n = 2..7, together with the closed
    form of the answer.  Every lower bound m_k with k >= 3 is the one that
    cor:hhfactor(iii) grants only under the compatibility in degree k; using
    them all makes the constraint set as strong as the paper allows, and a
    profile admissible under all of them is admissible under fewer.

(A) primitivity of the rational Weil classes and the sign of the
    intersection form on the rational Weil plane, extended to n = 4 (d = 1, 2,
    3) and n = 5 (d = 1, 2), with the paper's own model explicit_weil.py.

(B) the (p,p) classes killed by all 4n^2 monomials of P ^ Q, extended to
    n = 4 and n = 5 in every degree, with the paper's own routines.

(C) the top traces c_P, c_Q, injectivity on wedge^{2n-2}P + wedge^{2n-2}Q,
    and the perfect pairing, extended to n = 4 and n = 5.

Run:  python3 criterion_shape_ext.py
"""
import os
import sys
import time
from fractions import Fraction as Fr
from itertools import product
from math import comb

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import explicit_weil as EW          # noqa: E402
import hochschild_annihilator as HA  # noqa: E402
import criterion_shape as CS        # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("\n         " + detail) if detail else ""), flush=True)


# ------------------------------------------------------------------ (D)
def lower_bounds(n):
    """m_k for k = 0..2n as used by item (L); e_1 >= 4n = m_1"""
    return CS.minimal_profile(n)


def chi_of(e):
    return sum((-1) ** k * x for k, x in enumerate(e))


def enumerate_profiles(n, B):
    """all symmetric profiles e with e_k = m_k + x_k, 0 <= x_k <= B for
    k = 0..n (k != 2, and k != 2n-2 when 2n-2 <= n), e_2 = m_2, and chi >= 1"""
    m = lower_bounds(n)
    free = [k for k in range(0, n + 1) if k != 2 and k != 2 * n - 2]
    out = []
    for xs in product(range(B + 1), repeat=len(free)):
        x = [0] * (n + 1)
        for k, v in zip(free, xs):
            x[k] = v
        half = [m[k] + x[k] for k in range(n + 1)]
        e = half + [half[2 * n - k] for k in range(n + 1, 2 * n + 1)]
        c = chi_of(e)
        if c >= 1:
            out.append((e, c))
    return out, free


def item_D(ns=range(2, 8), B=4):
    print("(D) the Euler characteristic, n = %s, excess per degree 0..%d"
          % (list(ns), B))
    check("sum_k (-1)^k m_k = -2 for n = 1..200",
          all(chi_of(lower_bounds(n)) == -2 for n in range(1, 201)))
    summary = {}
    for n in ns:
        t0 = time.time()
        profs, free = enumerate_profiles(n, B)
        e0min = min(e[0] for e, c in profs)
        at_min = [(e, c) for e, c in profs if e[0] == e0min]
        # smallest total dimension among the profiles with least e_0
        tot = min(sum(e) for e, c in at_min)
        smallest = sorted((e, c) for e, c in at_min if sum(e) == tot)
        # the degrees that can carry the even excess other than 0
        even_free = [k for k in free if k % 2 == 0 and k != 0]
        summary[n] = (e0min, even_free, smallest)
        # closed form: e0min = 3 for n = 2, 3 and 1 for n >= 4
        want = 3 if n in (2, 3) else 1
        check("n=%d: least dim End(E) allowed by the constraints is %d "
              "(expected %d); free even degrees other than 0 (up to n): %s"
              % (n, e0min, want, even_free), e0min == want,
              "%d admissible profiles enumerated in %.1fs; smallest ones "
              "with e_0 = %d: %s"
              % (len(profs), time.time() - t0, e0min,
                 "; ".join("%s chi=%d" % (tuple(e), c) for e, c in smallest)))
        if n in (2, 3):
            ok = all(2 * e[0] >= c + 4 for e, c in profs)
            check("n=%d: 2 e_0 >= chi + 4 on every enumerated profile" % n,
                  ok)
    # the proof for every n >= 4: put 3 in the middle degree (n even) or 2 in
    # degrees 4 and 2n-4 (n odd), keep e_0 = 1
    allok = True
    for n in range(4, 201):
        m = lower_bounds(n)
        e = list(m)
        if n % 2 == 0:
            e[n] += 3
        else:
            e[4] += 2
            e[2 * n - 4] += 2
        c = chi_of(e)
        ok = (e[0] == 1 and e[2] == m[2] and e[2 * n - 2] == m[2]
              and all(e[k] >= m[k] for k in range(2 * n + 1))
              and all(e[k] == e[2 * n - k] for k in range(2 * n + 1))
              and c >= 1)
        allok = allok and ok
    check("for every n = 4..200 an explicit profile with e_0 = 1, e_2 = m_2 "
          "and chi in {1, 2} exists (3 added in the middle degree for n even, "
          "2 in degrees 4 and 2n-4 for n odd)", allok)
    return summary


# ------------------------------------------------------------------ (A)
def item_A(cases=((4, (1, 2, 3)), (5, (1, 2)))):
    print("(A) primitivity and the sign of the intersection form on the "
          "rational Weil plane")
    for n, ds in cases:
        for d in ds:
            t0 = time.time()
            M = EW.Model(n, d)
            N = M.N
            w1, w2, eta = M.omega1(), M.omega2(), M.eta()
            prim = (not EW.wedge(eta, w1, d)) and (not EW.wedge(eta, w2, d))
            vol = CS.top_coefficient(EW.ewedgepow(eta, 2 * n, d), N)
            g11 = CS.top_coefficient(EW.wedge(w1, w1, d), N)
            g12 = CS.top_coefficient(EW.wedge(w1, w2, d), N)
            g22 = CS.top_coefficient(EW.wedge(w2, w2, d), N)
            s = 1 if vol > 0 else -1
            G = [[s * g11, s * g12], [s * g12, s * g22]]
            sign = (-1) ** n
            definite = sign * G[0][0] > 0 and \
                G[0][0] * G[1][1] - G[0][1] ** 2 > 0
            pat = (G[0][1] == 0 and G[0][0] == sign * 2 ** (2 * n - 1) * d ** n
                   and G[1][1] == sign * 2 ** (2 * n - 1) * d ** (n - 1))
            check("n=%d, d=%d: eta ^ omega_1 = eta ^ omega_2 = 0, and "
                  "(-1)^n int omega^2 > 0 on the whole rational Weil plane"
                  % (n, d), prim and vol != 0 and definite,
                  "Gram matrix %s (pattern diag((-1)^n 2^(2n-1) d^n, "
                  "(-1)^n 2^(2n-1) d^(n-1)): %s), %.1fs"
                  % ([[str(x) for x in r] for r in G], pat, time.time() - t0))


# ------------------------------------------------------------------ (B)
def item_B(ns=(4, 5)):
    print("(B) the Hodge classes annihilated by P ^ Q")
    for n in ns:
        t0 = time.time()
        N, XS, YS, BXS, BYS, apply_mono, top = CS.model(n)
        hol = 0
        for i in XS + YS:
            hol |= 1 << i
        PQ = [(1 << s) | (1 << t) for s in range(2 * n)
              for t in range(2 * n, 4 * n)]
        kernel = {}
        for p in range(0, 2 * n + 1):
            monos = [m for m in range(1 << N)
                     if bin(m & hol).count("1") == p
                     and bin(m & ~hol).count("1") == p]
            vecs = []
            for m in monos:
                v = {}
                for oi, op in enumerate(PQ):
                    for key, c in apply_mono(op, {m: Fr(1)}).items():
                        v[(oi, key)] = v.get((oi, key), Fr(0)) + c
                vecs.append({k: c for k, c in v.items() if c != 0})
            kernel[p] = len(monos) - CS.sparse_rank(vecs)
        a_p = top(XS + BXS)
        a_m = top(YS + BYS)
        killed = all(not apply_mono(op, a_p) and not apply_mono(op, a_m)
                     for op in PQ)
        ok = killed and kernel[n] == 2 and \
            all(kernel[p] == 0 for p in kernel if p != n)
        check("n=%d: in every degree the (p,p) classes killed by all %d "
              "monomials of P ^ Q are exactly C alpha_+ + C alpha_-"
              % (n, len(PQ)), ok,
              "kernel dimensions by p: %s  (%.1fs)" % (kernel,
                                                       time.time() - t0))


# ------------------------------------------------------------------ (C)
def item_C(ns=(4, 5)):
    print("(C) the top traces and degree 2n-2")
    for n in ns:
        N, XS, YS, BXS, BYS, apply_mono, top = CS.model(n)
        a_p = top(XS + BXS)
        a_m = top(YS + BYS)
        a, b = Fr(3), Fr(-5)
        omega = {k: a * v for k, v in a_p.items()}
        for k, v in a_m.items():
            omega[k] = omega.get(k, Fr(0)) + b * v
        pmask = (1 << (2 * n)) - 1
        qmask = ((1 << N) - 1) ^ pmask
        cP = apply_mono(pmask, omega)
        cQ = apply_mono(qmask, omega)
        topH01 = top(BXS + BYS)
        prop = bool(cP) and bool(cQ) and set(cP) == set(topH01) \
            and set(cQ) == set(topH01)
        check("n=%d: top(P) and top(Q) contract omega to nonzero multiples of "
              "the generator of H^{0,2n}" % n, prop,
              "c_P = %s, c_Q = %s" % (list(cP.values())[0],
                                      list(cQ.values())[0]))
        k = 2 * n - 2
        masks = [m for m in range(1 << N) if bin(m).count("1") == k
                 and (not (m & qmask) or not (m & pmask))]
        vecs = [apply_mono(m, omega) for m in masks]
        r = CS.sparse_rank(vecs)
        check("n=%d: contraction with omega is injective on wedge^{2n-2} P + "
              "wedge^{2n-2} Q, of dimension 2 binom(2n,2) = %d"
              % (n, 2 * comb(2 * n, 2)),
              r == len(masks) == 2 * comb(2 * n, 2))
        P2 = [m for m in range(1 << (2 * n)) if bin(m).count("1") == 2]
        Pk = [m for m in range(1 << (2 * n)) if bin(m).count("1") == k]
        rows = [[Fr(HA.wedge_sign(m, m2)) if not (m & m2) else Fr(0)
                 for m2 in Pk] for m in P2]
        check("n=%d: the pairing wedge^2 P x wedge^{2n-2} P -> wedge^{2n} P "
              "is perfect" % n, HA.rank_q(rows) == len(P2) == len(Pk))


if __name__ == "__main__":
    t = time.time()
    item_D()
    item_C()
    item_B()
    item_A()
    print()
    print("  %d checks passed, %d failed  (%.1fs)"
          % (len(PASS), len(FAIL), time.time() - t))
    raise SystemExit(0 if not FAIL else 1)
