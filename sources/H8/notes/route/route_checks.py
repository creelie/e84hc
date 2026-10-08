"""Checks for the corrected route note (route_note.tex, Section 7).

Setting.  (X, Theta) a principally polarised abelian fourfold, T = Theta,
F = I_Z(b T) a secant object with ch F = u + b v = 1 + bT - dT^2/2 - dbT^3/6
+ d^2 T^4/24, N = (b^2 + d)/2, and a Hilbert-Burch resolution
0 -> E -> G -> F -> 0 by vector bundles of ranks r, r + 1 (E = E_1(bT),
G = E_0(bT)).  Chern data are written as in the route note: c_k = m_k T^k/k!,
so m_k is the number c_k . T^{4-k} / (4-k)!, and m_4 is a number of points.

  (A) the forced invariants of a smooth support at b = 3 (Table 1 of the note)
      and the class [S] = N T^2, not N T^2 / 2;
  (B) the n_k of the original numerical lemma are Whitney's formula
      c(G) = c(E) c(F), so their integrality is automatic;
  (C) the Bogomolov discriminant 2r c_2 - (r-1) c_1^2 and the difference
      formula of the lemma; the displayed definition r c_2 - (r-1) c_1^2
      gives 2, not 4, for the example;
  (D) the vanishing above the rank: the example E of rank two with
      c(E) = 1 + T^2 has c_4(G) = 180, 144, 84, 0 points at d = 1, 3, 5, 7,
      so it is a resolution datum only at d = 7; its chi(E^v G);
  (E) corrected examples: rank two data exist at d = 3, 7 and not at d = 1, 5
      (Chern classes in Q[T]); with the note's inequalities Delta(E) > 0,
      Delta(G) > 0, mu(E) < mu(G), chi(E^v G) >= 1 rank two survives only at
      d = 7; at rank three the note's own c(E) = 1 + T^2 meets everything at
      every d in {1, 3, 5, 7};
  (F) r = 1 is excluded at every d: c_4(G) = -6N(1 + d) points at b = 3;
  (G) products of curves (K^2 = 8 chi) need 5N = 4b^2, impossible at b = 3,
      and symmetric squares of curves never have the invariants of Table 1;
  (H) simple semi-homogeneous bundles on a principally polarised fourfold
      have rank q^4, so none has rank 2 or 3;
  (I) K-linear first order deformations: pq of the n(n+1)/2 polarised
      directions for signature (p, q), so 4 of 10 at (2, 2).
Exact arithmetic throughout.
"""
import os
import random
import sys
from fractions import Fraction as Fr
from itertools import product

import sympy as sp

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "code"))
from burch_rank import ch_to_chern, chern_to_ch, secant_ch, mul_chern  # noqa

PASS, FAIL = [], []
FACT = [1, 1, 2, 6, 24]


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


def to_T(m):
    """m_k (coefficient of T^k/k!) -> coefficient of T^k."""
    return [Fr(m[k - 1], FACT[k]) for k in range(1, 5)]


def from_T(c):
    return [c[k - 1] * FACT[k] for k in range(1, 5)]


def data_G(r, m, b, d):
    """Chern data of G = E + F in the m_k normalisation, via Whitney."""
    return from_T(mul_chern(to_T(m), ch_to_chern(secant_ch(b, d))))


def ch_of(r, m):
    return chern_to_ch(r, to_T(m))           # coordinates in T^k/k!


def chi_pair(chA, chB):
    """chi(A^v (x) B) = int ch(A^v) ch(B), coordinates in T^k/k!, int T^4 = 24."""
    dual = [chA[k] * (-1) ** k for k in range(5)]
    tot = Fr(0)
    for i in range(5):
        for j in range(5 - i):
            if i + j == 4:
                tot += dual[i] * chB[j] * Fr(24, FACT[i] * FACT[j])
    return tot


def bogomolov(r, m):
    """(2r c_2 - (r-1) c_1^2) / T^2 = r m_2 - (r-1) m_1^2."""
    return r * m[1] - (r - 1) * m[0] ** 2


def main():
    print("(A) the targets of a smooth support at b = 3")
    table = {1: (5, 260, 1860, 1260, 480, 120), 3: (6, 288, 2160, 1296, 576, 144),
             5: (7, 308, 2436, 1260, 672, 168), 7: (8, 320, 2688, 1152, 768, 192)}
    b = 3
    ok = True
    for d, row in table.items():
        N = (b * b + d) // 2
        chi = 4 * N * (2 * b * b - N)
        K2 = 12 * N * (4 * b * b - N)
        e = 12 * N * (4 * b * b - 3 * N)
        ok &= (N, chi, K2, e, 32 * b * N, 24 * N) == row
        ok &= 12 * chi == K2 + e and 3 * e - K2 == 24 * (b ** 4 - d * d)
    check("Table 1 of the note equals the paper's forced invariants, with "
          "Noether and the Bogomolov-Miyaoka-Yau defect 24(b^4 - d^2)", ok)
    check("lambda^2 = [S] . T^2 = 24N needs [S] = N T^2; with N T^2/2 it "
          "would be 12N, not the table's value",
          all(24 * row[0] == row[5] and 12 * row[0] != row[5]
              for row in table.values()))

    print("(B) the original numerical lemma is Whitney's formula")
    rng = random.Random(27)
    ok = True
    for _ in range(3000):
        r = rng.randint(1, 8)
        d = rng.choice([1, 3, 5, 7, 11, 15, 23])
        m1, m2, m3, m4 = (rng.randint(-30, 30) for _ in range(4))
        n = data_G(r, [m1, m2, m3, m4], 3, d)
        n1 = m1 + 3
        n2 = m2 + 6 * m1 + 9 + d
        n3 = m3 + 2 * (m1 ** 3 - n1 ** 3) - 3 * (m1 * m2 - n1 * n2) - 6 * d
        P3 = Fr(m1 ** 3) - Fr(3, 2) * m1 * m2 + Fr(m3, 2) - 3 * d
        P4 = (m1 * (m1 ** 3 - Fr(3, 2) * m1 * m2 + Fr(m3, 2))
              - Fr(m2, 2) * (m1 * m1 - m2) + Fr(m1 * m3, 6) - Fr(m4, 6) + d * d)
        n4 = 6 * n1 * P3 - 3 * n2 * (n1 * n1 - n2) + n1 * n3 - 6 * P4
        ok &= n == [n1, n2, n3, n4]
        # the Chern character adds: ch G = ch E + ch F
        chG = chern_to_ch(r + 1, to_T(n))
        chE = ch_of(r, [m1, m2, m3, m4])
        ok &= all(chG[k] == chE[k] + secant_ch(3, d)[k] for k in range(5))
        ok &= all(x.denominator == 1 for x in n)
    check("the lemma's n_1, ..., n_4 agree with c(G) = c(E) c(F) on 3000 "
          "random integral data, and are integers", ok)
    cF = from_T(ch_to_chern(secant_ch(3, 1)))
    check("c(F) itself has integral m_k (so Whitney gives integrality)",
          all(x.denominator == 1 for x in cF), "m(F) at b = 3, d = 1: "
          + str([int(x) for x in cF]))

    print("(C) the Bogomolov discriminant")
    check("for c(E) = 1 + T^2 of rank 2: 2r c_2 - (r-1)c_1^2 = 4 T^2 (the "
          "value the note uses), r c_2 - (r-1)c_1^2 = 2 T^2 (the definition "
          "it displays)",
          bogomolov(2, [0, 2]) == 4 and 2 * 1 - 0 == 2)
    ok = True
    for _ in range(2000):
        r = rng.randint(1, 8)
        d = rng.choice([1, 3, 5, 7])
        m = [rng.randint(-30, 30) for _ in range(4)]
        n = data_G(r, m, 3, d)
        ok &= (bogomolov(r + 1, n) - bogomolov(r, m)
               == m[1] - (m[0] - 3) ** 2 + 18 + (r + 1) * d)
    check("Delta(G) - Delta(E) = m_2 - (m_1 - 3)^2 + 18 + (r+1)d with "
          "Bogomolov's normalisation", ok)

    print("(D) the example of the original corollary")
    c4 = {}
    chis = {}
    for d in (1, 3, 5, 7):
        n = data_G(2, [0, 2, 0, 0], 3, d)
        c4[d] = n[3]
        chis[d] = chi_pair(ch_of(2, [0, 2, 0, 0]), chern_to_ch(3, to_T(n)))
    check("c_4(G) = 180, 144, 84, 0 points at d = 1, 3, 5, 7, so a rank "
          "three G exists numerically only at d = 7",
          [c4[d] for d in (1, 3, 5, 7)] == [180, 144, 84, 0])
    check("chi(E^v (x) G) = 48, 88, 144, 216 as the note states",
          [chis[d] for d in (1, 3, 5, 7)] == [48, 88, 144, 216])

    print("(E) corrected examples")

    def admissible(r, m, d, strict):
        n = data_G(r, m, 3, d)
        if any(m[k] != 0 for k in range(r, 4)) or any(n[k] != 0
                                                       for k in range(r + 1, 4)):
            return None
        if any(x.denominator != 1 for x in n):
            return None
        chE = ch_of(r, m)
        chG = chern_to_ch(r + 1, to_T(n))
        if chE[4].denominator != 1:
            return None
        x = chi_pair(chE, chG)
        if strict and not (bogomolov(r, m) > 0 and bogomolov(r + 1, n) > 0
                           and Fr(m[0], r) < Fr(n[0], r + 1) and x >= 1):
            return None
        return [int(v) for v in n], int(x)

    def search(r, d, strict):
        out = []
        for m1, m2, m3 in product(range(-8, 9), range(-20, 21), range(-30, 31)):
            res = admissible(r, [m1, m2, m3, 0], d, strict)
            if res:
                out.append(([m1, m2, m3, 0],) + res)
        return out

    two = {d: search(2, d, False) for d in (1, 3, 5, 7)}
    check("rank two, vanishing above the rank only: integral data exist at "
          "d = 3, 7 and not at d = 1, 5 (|m_1| <= 8)",
          [bool(two[d]) for d in (1, 3, 5, 7)] == [False, True, False, True])
    m1s = sp.symbols('m1')
    DE = sp.expand(2 * (3 * 3 - 9 - 12 * m1s) / 6 - m1s ** 2)
    check("rank two at b = 3, d = 3: Delta(E) = -4m_1 - m_1^2, so Delta(E) > 0 "
          "forces -4 < m_1 < 0", sp.expand(DE + 4 * m1s + m1s ** 2) == 0)
    ok = True
    for d in (3, 7, 11, 15, 19):
        for a in range(-8, 9):
            m = [a, Fr(3 * d - 9 - 12 * a, 6), 0, 0]
            n = data_G(2, m, 3, d)
            x = chi_pair(ch_of(2, m), chern_to_ch(3, to_T(n)))
            ok &= bogomolov(2, m) == d + 1 - (a + 2) ** 2
            ok &= bogomolov(3, n) == Fr(9 * (d + 1) - 4 * a * a, 2)
            ok &= x == Fr(24 * a ** 4 + 64 * a ** 3 - 88 * a * a * d + 104 * a * a
                          - 64 * a * d + 192 * a + 57 * d * d - 174 * d + 153, 8)
    check("rank two at b = 3 (c_1(E) = aT): Delta(E) = d + 1 - (a+2)^2, "
          "Delta(G) = (9(d+1) - 4a^2)/2, and the closed form of chi(E^v G)",
          ok)
    two_s = {d: search(2, d, True) for d in (3, 7)}
    small3 = [(x[0][0], x[2]) for x in two[3] if -4 < x[0][0] < 0]
    check("rank two with the note's inequalities: none at d = 3 (the "
          "chi(E^v G) below), three at d = 7 (m_1 = -2, -1, 0)",
          two_s[3] == [] and sorted(x[0][0] for x in two_s[7]) == [-2, -1, 0],
          "d = 3, (m_1, chi): " + str(small3))
    ok = True
    vals = []
    for d in (1, 3, 5, 7):
        res = admissible(3, [0, 2, 0, 0], d, True)
        ok &= res is not None
        vals.append(res[1] if res else None)
    check("rank three: c(E) = 1 + T^2 meets every condition at every d in "
          "{1, 3, 5, 7}", ok and vals == [53, 101, 173, 269],
          "chi(E^v G) = " + str(vals))

    print("(F) rank one")
    ok = True
    pts = []
    for d in (1, 3, 5, 7):
        N = Fr(9 + d, 2)
        # c_3(G) = 0 forces c_1(E) = -(b/3) T = -T; then c_4(G):
        n = data_G(1, [-1, 0, 0, 0], 3, d)   # c(E) = 1 - T
        ok &= n[2] == 0 and n[3] == -6 * N * (1 + d)
        pts.append(int(n[3]))
    check("r = 1 at b = 3: c_3(G) = 0 forces c_1(E) = -T, and then "
          "c_4(G) = -6N(1+d) != 0", ok, "points: " + str(pts))

    print("(G) products and symmetric squares of curves")
    bb, NN = sp.symbols('b N')
    chi_s = 4 * NN * (2 * bb ** 2 - NN)
    K2_s = 12 * NN * (4 * bb ** 2 - NN)
    check("K^2 = 8 chi reads 5N = 4b^2 (N > 0)",
          sp.factor(K2_s - 8 * chi_s) == sp.factor(4 * NN * (5 * NN - 4 * bb ** 2)))
    sols = [b_ for b_ in range(1, 61) if (4 * b_ * b_) % 5 == 0]
    check("5N = 4b^2 has an integer solution exactly when 5 | b "
          "(b <= 60); none at b = 3", sols == list(range(5, 61, 5)))
    targets = {(4 * N * (18 - N), 12 * N * (36 - N), 12 * N * (36 - 3 * N))
               for N in (5, 6, 7, 8)}
    hits = []
    for g in range(2, 2000):
        inv = ((g - 1) * (g - 2) // 2, (g - 1) * (4 * g - 9), (g - 1) * (2 * g - 3))
        if inv in targets or inv[0] in {t[0] for t in targets}:
            hits.append(g)
    check("the symmetric square of a curve of genus g < 2000 never has "
          "chi(O) in {260, 288, 308, 320}, let alone the triple", hits == [])

    print("(H) simple semi-homogeneous bundles")
    ok = True
    for s in range(1, 82):
        slopes = set()
        for q in range(2, 10):
            for p in range(1, q):
                if sp.gcd(p, q) != 1:
                    continue
                mu = Fr(p, q)
                if all((s * mu ** k).denominator == 1 for k in range(1, 5)):
                    slopes.add(q)
        expected = {q for q in range(2, 10) if s % q ** 4 == 0}
        ok &= slopes == expected
    check("s e^{(p/q) T} has integral Chern character on a principally "
          "polarised fourfold only if q^4 | s (s <= 81), so a non-integral "
          "slope needs rank at least 16", ok)

    print("(I) K-linear directions among the polarised ones")
    ok = True
    alpha = sp.I * sp.sqrt(7)
    for n in range(2, 6):
        for p in range(0, n + 1):
            q = n - p
            D = sp.diag(*([alpha] * p + [sp.conjugate(alpha)] * q))
            xs = sp.symbols(f'x0:{n * (n + 1) // 2}')
            B = sp.zeros(n, n)
            it = iter(xs)
            for i in range(n):
                for j in range(i, n):
                    B[i, j] = B[j, i] = next(it)
            eqs = list(B * D - D.conjugate() * B)
            M = sp.Matrix([[sp.diff(e, x) for x in xs] for e in eqs])
            ok &= len(xs) - M.rank() == p * q
    check("symmetric B with B D = conj(D) B has dimension pq; at n = 4, "
          "(p, q) = (2, 2): 4 of the n(n+1)/2 = 10 polarised directions", ok)

    print()
    print(f"{len(PASS)} checks passed, {len(FAIL)} failed")
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
