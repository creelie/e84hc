#!/usr/bin/env python3
"""
criterion_shape.py

Item (L) of COMPUTATIONS.md: what an object meeting the numerical
criterion of the theorem "the criterion is a dimension" must look like.

Let A be an abelian 2n-fold of (K,-1,n)-Weil type, omega = a alpha_+ + b
alpha_- a nonzero rational Weil class, and E a perfect complex with
ch(E) = N omega and no other component.  Write e_k = dim Ext^k(E,E).  Item
(XXXVIII) gives e_k >= m_k with

    m_0 = m_{2n} = 1,     m_k = 2 binom(2n,k)   (1 <= k <= 2n-1),

and the criterion is e_2 = m_2 = 2n(2n-1).  This script checks, in exact
arithmetic, every finite ingredient of the theorem on the shape of such an
object:

  (A) the rational Weil classes are primitive for the polarisation eta of the
      coordinate model, eta ^ omega_1 = eta ^ omega_2 = 0, and the
      intersection form on the rational Weil plane is (-1)^n-definite, as the
      Hodge-Riemann relations require; hence
          chi(E,E) = (-1)^n N^2 int omega^2 > 0
      for every such E.  Checked for n = 2, 3 and several discriminants.

  (B) the Hodge classes annihilated by the whole of P ^ Q, in every degree,
      are exactly C alpha_+ + C alpha_-; so in a direct sum decomposition of
      an object meeting the criterion every summand has its Chern character
      on the rational Weil plane.  Checked for n = 2, 3 in all degrees.

  (C) the two traces c_P, c_Q of the top classes of wedge^{2n} P and
      wedge^{2n} Q are nonzero, and contraction with omega is injective on
      wedge^{2n-2} P + wedge^{2n-2} Q, so Ext^{2n-2}(E,E) is the image of
      that space when the criterion holds.  Checked for n = 2, 3.

  (D) the arithmetic of the Euler characteristic: sum (-1)^k m_k = -2 for
      every n; for n = 2 and n = 3 (where e_3 >= 40 is the bound that the
      paper's corollary on the Hochschild action grants in degree three),
      e_2 = m_2 together with chi >= 1 forces
      dim End(E) = e_0 >= 3, indeed 2 e_0 >= chi + 4, and the smallest
      admissible profiles are listed; for n = 4 and n = 5 the same data allow e_0 = 1, so the bound
      is special to n <= 3; and for the Mumford square the same identity with
      chi = 0 returns the 800 odd self-extensions of item (XLV).

By the theorem that the pure form of the criterion is never met
(thm:p2false, item (LI)), no object satisfies these hypotheses: the checks
here are the finite ingredients of a theorem whose hypotheses are empty, kept
as the record of what the pure form asked for.

Run:  python3 criterion_shape.py
"""
from fractions import Fraction as Fr
from math import comb

import explicit_weil as EW
import hochschild_annihilator as HA

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ------------------------------------------------------------------ (A)
def top_coefficient(u, N):
    key = tuple(range(1, N + 1))
    assert set(u) <= {key}, "not a top degree element"
    c = u.get(key, EW.sc())
    assert EW.isrational(c)
    return c[0]


def item_A():
    print("(A) primitivity and the sign of the intersection form on the "
          "rational Weil plane")
    for n in (2, 3):
        for d in ((1, 2, 3, 5, 7) if n == 2 else (1, 2, 3)):
            M = EW.Model(n, d)
            N = M.N
            w1, w2, eta = M.omega1(), M.omega2(), M.eta()
            prim = (not EW.wedge(eta, w1, d)) and (not EW.wedge(eta, w2, d))
            vol = top_coefficient(EW.ewedgepow(eta, 2 * n, d), N)
            g11 = top_coefficient(EW.wedge(w1, w1, d), N)
            g12 = top_coefficient(EW.wedge(w1, w2, d), N)
            g22 = top_coefficient(EW.wedge(w2, w2, d), N)
            # the orientation is the one in which eta^{2n} is positive
            s = 1 if vol > 0 else -1
            G = [[s * g11, s * g12], [s * g12, s * g22]]
            sign = (-1) ** n
            definite = sign * G[0][0] > 0 and \
                G[0][0] * G[1][1] - G[0][1] ** 2 > 0
            check("n=%d, d=%d: eta ^ omega_1 = eta ^ omega_2 = 0, and "
                  "(-1)^n int omega^2 > 0 on the whole rational Weil plane"
                  % (n, d), prim and vol != 0 and definite,
                  "Gram matrix %s, determinant %s"
                  % ([[str(x) for x in r] for r in G],
                     G[0][0] * G[1][1] - G[0][1] ** 2))


# ------------------------------------------------------------------ (B), (C)
def sparse_rank(vectors):
    """rank over Q of a list of sparse vectors {key: Fraction}"""
    pivots = {}
    r = 0
    for v in vectors:
        v = dict(v)
        while v:
            k = min(v)
            if k in pivots:
                pv = pivots[k]
                f = v[k] / pv[k]
                for kk, c in pv.items():
                    v[kk] = v.get(kk, Fr(0)) - f * c
                    if v[kk] == 0:
                        del v[kk]
            else:
                pivots[k] = v
                r += 1
                break
    return r


def model(n):
    """the model of item (XXXVIII): generators x (hol, alpha_+ side),
    y (hol, alpha_- side), bar x, bar y; P = wedge bar x + contract y,
    Q = wedge bar y + contract x"""
    N = 4 * n
    XS = list(range(0, n))
    YS = list(range(n, 2 * n))
    BXS = list(range(2 * n, 3 * n))
    BYS = list(range(3 * n, 4 * n))
    ops = ([("w", i) for i in BXS] + [("c", j) for j in YS]
           + [("w", i) for i in BYS] + [("c", j) for j in XS])

    def apply_op(t, u):
        kind, i = ops[t]
        return HA.wedge_gen(i, u) if kind == "w" else HA.contract_gen(i, u)

    def apply_mono(mask, u):
        for t in sorted(HA.bits(mask), reverse=True):
            u = apply_op(t, u)
            if not u:
                return {}
        return u

    def top(idx):
        u = {0: Fr(1)}
        for i in idx:
            u = HA.wedge_gen(i, u)
        return u

    return N, XS, YS, BXS, BYS, apply_mono, top


def item_B():
    print("(B) the Hodge classes annihilated by P ^ Q")
    for n in (2, 3):
        N, XS, YS, BXS, BYS, apply_mono, top = model(n)
        hol = set(XS + YS)
        PQ = [(1 << s) | (1 << t) for s in range(2 * n)
              for t in range(2 * n, 4 * n)]
        kernel = {}
        for p in range(0, 2 * n + 1):
            monos = [m for m in range(1 << N)
                     if sum(1 for i in HA.bits(m) if i in hol) == p
                     and sum(1 for i in HA.bits(m) if i not in hol) == p]
            vecs = []
            for m in monos:
                v = {}
                for oi, op in enumerate(PQ):
                    for key, c in apply_mono(op, {m: Fr(1)}).items():
                        v[(oi, key)] = v.get((oi, key), Fr(0)) + c
                vecs.append({k: c for k, c in v.items() if c != 0})
            kernel[p] = len(monos) - sparse_rank(vecs)
        a_p = top(XS + BXS)
        a_m = top(YS + BYS)
        killed = all(not apply_mono(op, a_p) and not apply_mono(op, a_m)
                     for op in PQ)
        ok = killed and kernel[n] == 2 and \
            all(kernel[p] == 0 for p in kernel if p != n)
        check("n=%d: in every degree the (p,p) classes killed by all %d "
              "monomials of P ^ Q are exactly C alpha_+ + C alpha_-"
              % (n, len(PQ)), ok,
              "kernel dimensions by p: %s" % kernel)


def item_C():
    print("(C) the top traces and degree 2n-2")
    for n in (2, 3):
        N, XS, YS, BXS, BYS, apply_mono, top = model(n)
        a_p = top(XS + BXS)
        a_m = top(YS + BYS)
        a, b = Fr(3), Fr(-5)          # any omega with a b != 0
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
              "the generator of H^{0,2n}, so c_P and c_Q are nonzero" % n,
              prop, "c_P = %s, c_Q = %s (times the generator)"
              % (list(cP.values())[0], list(cQ.values())[0]))
        k = 2 * n - 2
        masks = [m for m in range(1 << N) if bin(m).count("1") == k
                 and (not (m & qmask) or not (m & pmask))]
        vecs = [apply_mono(m, omega) for m in masks]
        r = sparse_rank(vecs)
        check("n=%d: contraction with omega is injective on "
              "wedge^{2n-2} P + wedge^{2n-2} Q, of dimension "
              "2 binom(2n,2) = %d" % (n, 2 * comb(2 * n, 2)),
              r == len(masks) == 2 * comb(2 * n, 2))
        # the pairing wedge^2 P x wedge^{2n-2} P -> wedge^{2n} P is perfect
        P2 = [m for m in range(1 << (2 * n)) if bin(m).count("1") == 2]
        P4 = [m for m in range(1 << (2 * n)) if bin(m).count("1") == k]
        rows = []
        for m in P2:
            rows.append([Fr(HA.wedge_sign(m, m2)) if not (m & m2) else Fr(0)
                         for m2 in P4])
        check("n=%d: the pairing wedge^2 P x wedge^{2n-2} P -> wedge^{2n} P "
              "is perfect" % n, HA.rank_q(rows) == len(P2) == len(P4))


# ------------------------------------------------------------------ (D)
def minimal_profile(n):
    return [1] + [2 * comb(2 * n, k) for k in range(1, 2 * n)] + [1]


def item_D():
    print("(D) the Euler characteristic")
    check("sum (-1)^k m_k = -2 for every n from 1 to 60",
          all(sum((-1) ** k * m for k, m in enumerate(minimal_profile(n)))
              == -2 for n in range(1, 61)))

    # n = 2: e = (e0, e1, 12, e1, e0), chi = 2 e0 - 2 e1 + 12
    feas2 = []
    for e1 in range(8, 80):
        for chi in range(1, 80):
            t = chi + 2 * e1 - 12
            if t % 2 == 0 and t // 2 >= 1:
                feas2.append((t // 2, e1, chi))
    m2 = min(f[0] for f in feas2)
    best2 = sorted(f for f in feas2 if f[0] == m2)
    check("n=2: the criterion e_2 = 12 with chi >= 1 forces e_0 >= 3, and "
          "the bound is attained", m2 == 3,
          "smallest profiles (e0,e1,12,e1,e0) with chi: %s"
          % ["(%d,%d,12,%d,%d) chi=%d" % (a, b, b, a, c) for a, b, c in best2])

    # n = 3: e = (e0, e1, 30, e3, 30, e1, e0), chi = 2 e0 - 2 e1 + 60 - e3
    feas3 = []
    for e1 in range(12, 60):
        for e3 in range(40, 140):
            for chi in range(1, 60):
                t = chi + 2 * e1 + e3 - 60
                if t % 2 == 0 and t // 2 >= 1:
                    feas3.append((t // 2, e1, e3, chi))
    m3 = min(f[0] for f in feas3)
    best3 = sorted(f for f in feas3 if f[0] == m3)
    check("n=3: the criterion e_2 = 30 with chi >= 1 forces e_0 >= 3, and "
          "the bound is attained", m3 == 3,
          "smallest profiles: %s" % ["(%d,%d,30,%d,30,%d,%d) chi=%d"
                                     % (a, b, c, b, a, x)
                                     for a, b, c, x in best3])
    # the bound on Ext^1 in terms of End at n = 3
    check("n=3: in every admissible profile e_1 <= e_0 + 9",
          all(b <= a + 9 for a, b, c, x in feas3))
    check("n=2 and n=3: in every admissible profile 2 e_0 >= chi + 4, that "
          "is dim End(E) >= 2 + chi(E,E)/2",
          all(2 * a >= c + 4 for a, b, c in feas2)
          and all(2 * a >= x + 4 for a, b, c, x in feas3))

    # n = 4, 5: the criterion leaves e_0 = 1 possible
    for n in (4, 5):
        m = minimal_profile(n)
        # put the whole even excess in degree 4, keep e_0 = 1
        e = list(m)
        e[4] += 3
        e[2 * n - 4] += 3 if 2 * n - 4 != 4 else 0
        chi = sum((-1) ** k * x for k, x in enumerate(e))
        check("n=%d: a profile with e_0 = 1, e_2 = m_2 and chi = %d > 0 "
              "exists, so the bound on End is special to n <= 3" % (n, chi),
              e[0] == 1 and e[2] == m[2] and chi > 0
              and all(e[k] == e[2 * n - k] for k in range(2 * n + 1)))

    # the Mumford square: chi = 0, profile 1,16,119,328,560,...
    mum = [1, 16, 119, 328, 560, 328, 119, 16, 1]
    alt = sum((-1) ** k * x for k, x in enumerate(mum))
    odd_min = 2 * 16 + 2 * 328 + alt
    check("the Mumford square: the same identity with chi = 0 and "
          "e_2 = e_6 = 119 forces at least %d odd self-extensions" % odd_min,
          alt == 112 and odd_min == 800)


if __name__ == "__main__":
    print("(L) what an object meeting the numerical criterion must look like")
    item_A()
    item_B()
    item_C()
    item_D()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
