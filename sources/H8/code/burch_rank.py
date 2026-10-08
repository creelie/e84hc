"""Item (LXX): resolutions of rank one and two for a secant object.

Setting.  (X, Theta) a principally polarised abelian fourfold, b >= 1, d > 0,
Z in X of codimension two with a resolution by vector bundles

    0 -> E_1 -> E_0 -> I_Z -> 0,     rk E_1 = r,  rk E_0 = r + 1,

and ch(I_Z(b Theta)) = u + b v = 1 + b T - d T^2/2 - d b T^3/6 + d^2 T^4/24,
T = Theta.  Put E = E_1(b Theta), G = E_0(b Theta), F = I_Z(b Theta), so that
0 -> E -> G -> F -> 0 and c(G) = c(E) c(F) (Whitney).  A vector bundle of
rank s has c_k = 0 for k > s; this is what the checks below use.

Classes in Q[T]/(T^5) are written by their coefficients of T^k (not T^k/k!)
unless stated otherwise; the integral of T^4 is 24.

Paper: Proposition [Resolutions of rank one and two] (prop:lowrankburch) and
the correction of the route note's numerical lemma recorded after it.

  (A) c(F) = 1 + b T + N T^2 + (b N / 3) T^3 + N (b^2 - 3d)/12 T^4, N = (b^2+d)/2,
      symbolically and against Newton's identities on a grid;
  (B) hard Lefschetz: T^2 : H^2 -> H^6 is an isomorphism on a principally
      polarised abelian fourfold (rank 28 in the exterior algebra over Z);
  (C) r = 1: c_3(G) = 0 forces c_1(E) = -(b/3) T, and then
      c_4(G) = -(b^2 + d)(b^2 + 9d)/72 T^4 != 0;
  (D) r = 2 with Chern classes in Q[T]: c_4(G) = 0 reads
      6 m = 3d - b^2 - 4ab  (c_1(E) = a T, c_2(E) = m T^2/2), and
      chi(E) = a^4 - 2 a^2 m + m^2/2, so m must be even; at b = 3 this is
      d = 3 mod 4; a brute-force search with independent Newton-identity code
      confirms the set of d that admit rank two data;
  (E) the example of the route note's corollary: c_4(G) has coefficient
      180, 144, 84, 0 of T^4/24 at d = 1, 3, 5, 7, so a rank three G exists
      numerically only at d = 7;
  (F) Whitney against Newton on random data: integrality of the Chern classes
      of G is automatic, which is all the route note's lemma asserts.
Exact arithmetic throughout (fractions and sympy).
"""
import itertools
import random
import sys
from fractions import Fraction as Fr

import sympy as sp

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ----------------------------------------------------------------------
# Newton's identities in Q[T]/(T^5), coefficients of T^k

def ch_to_chern(chk):
    """chk[k] = coefficient of T^k/k! in ch (k = 0..4).  Returns the
    coefficients of T^k in c_1..c_4 (c_0 = 1)."""
    p = [None] + [Fr(chk[k]) for k in range(1, 5)]   # p_k = k! ch_k, coeff of T^k
    e = [Fr(1)] + [Fr(0)] * 4
    for k in range(1, 5):
        s = Fr(0)
        for i in range(1, k + 1):
            s += (-1) ** (i - 1) * e[k - i] * p[i]
        e[k] = s / k
    return e[1:]


def chern_to_ch(rank, c):
    """c[k-1] = coefficient of T^k in c_k.  Returns coefficients of T^k/k!
    in ch (k = 0..4)."""
    e = [Fr(1)] + [Fr(x) for x in c]
    p = [Fr(rank)] + [Fr(0)] * 4
    for k in range(1, 5):
        s = Fr(0)
        for i in range(1, k):
            s += (-1) ** (i - 1) * e[i] * p[k - i]
        s += (-1) ** (k - 1) * k * e[k]
        p[k] = s
    return p          # p_k = k! ch_k has coefficient of T^k equal to ch coord


def secant_ch(b, d):
    return [1, b, -d, -d * b, d * d]


def mul_chern(cE, cF):
    """Total Chern classes as coefficient lists of T^1..T^4, c_0 = 1."""
    x = [Fr(1)] + [Fr(v) for v in cE]
    y = [Fr(1)] + [Fr(v) for v in cF]
    z = [sum(x[i] * y[k - i] for i in range(k + 1)) for k in range(5)]
    return z[1:]


def main():
    # (A) Chern classes of F
    b, d, a, m, l = sp.symbols('b d a m l')
    N = (b ** 2 + d) / 2
    cF_closed = [b, N, b * N / 3, N * (b ** 2 - 3 * d) / 12]
    p = [None, b, -d, -d * b, d ** 2]
    e = [sp.Integer(1)] + [0] * 4
    for k in range(1, 5):
        e[k] = sp.expand(sum((-1) ** (i - 1) * e[k - i] * p[i]
                             for i in range(1, k + 1)) / k)
    check("(A) c(F) = 1 + bT + N T^2 + (bN/3) T^3 + N(b^2-3d)/12 T^4, "
          "symbolically in b and d",
          all(sp.simplify(e[k] - cF_closed[k - 1]) == 0 for k in range(1, 5)))
    ok = True
    for bb in range(1, 13):
        for dd in range(1, 61):
            cf = ch_to_chern(secant_ch(bb, dd))
            NN = Fr(bb * bb + dd, 2)
            ok &= cf == [bb, NN, bb * NN / 3, NN * (bb * bb - 3 * dd) / 12]
    check("(A) the same against Newton's identities for 1 <= b <= 12, "
          "1 <= d <= 60", ok)
    ok = True
    for bb in range(1, 13):
        for dd in range(1, 61):
            cf = ch_to_chern(secant_ch(bb, dd))
            ok &= all((cf[k - 1] * [1, 1, 2, 6, 24][k]).denominator == 1
                      for k in range(1, 5))
    check("(A) the Chern classes of F are integral: c_k(F) in Z T^k/k! "
          "for the same range", ok)

    # (B) hard Lefschetz on H^2 -> H^6 by T^2, T = sum x_i ^ y_i
    idx = list(range(8))
    basis2 = list(itertools.combinations(idx, 2))
    basis6 = list(itertools.combinations(idx, 6))
    pos6 = {s: i for i, s in enumerate(basis6)}

    def wedge_sign(sq):
        s = list(sq)
        sign = 1
        for i in range(len(s)):
            for j in range(len(s) - 1 - i):
                if s[j] > s[j + 1]:
                    s[j], s[j + 1] = s[j + 1], s[j]
                    sign = -sign
        return sign, tuple(s)

    theta = [((2 * i, 2 * i + 1), 1) for i in range(4)]
    theta2 = {}
    for (u, cu), (v, cv) in itertools.product(theta, theta):
        if set(u) & set(v):
            continue
        sg, key = wedge_sign(u + v)
        theta2[key] = theta2.get(key, 0) + sg * cu * cv
    M = sp.zeros(len(basis6), len(basis2))
    for j, w in enumerate(basis2):
        for key, c in theta2.items():
            if set(key) & set(w):
                continue
            sg, k6 = wedge_sign(key + w)
            M[pos6[k6], j] += sg * c
    check("(B) hard Lefschetz: T^2 : H^2 -> H^6 has rank 28 = dim H^2",
          M.rank() == 28)
    check("(B) T^2/2 is a primitive integral class (coefficients 1, gcd 1)",
          all(abs(c) == 2 for c in theta2.values()) and len(theta2) == 6)

    # (C) rank one
    c3G = sp.expand(cF_closed[2] + l * cF_closed[1])
    lsol = sp.solve(sp.Eq(c3G, 0), l)
    check("(C) r = 1: c_3(G) = c_3(F) + c_1(E) c_2(F) = 0 forces "
          "c_1(E) = -(b/3) T", lsol == [-b / 3])
    c4G = sp.factor(cF_closed[3] + lsol[0] * cF_closed[2])
    check("(C) r = 1: then c_4(G) = -(b^2 + d)(b^2 + 9d)/72 T^4",
          sp.simplify(c4G + (b ** 2 + d) * (b ** 2 + 9 * d) / 72) == 0,
          "c_4(G) = %s" % c4G)
    ok = True
    for bb in range(1, 13):
        for dd in range(1, 61):
            cf = ch_to_chern(secant_ch(bb, dd))
            ll = -cf[2] / cf[1]
            cg = mul_chern([ll, 0, 0, 0], cf)
            ok &= cg[2] == 0 and cg[3] != 0
    check("(C) r = 1: no rank two G for 1 <= b <= 12, 1 <= d <= 60 "
          "(exact, the unique c_1 killing c_3 leaves c_4 != 0)", ok)
    check("(C) r = 1 at the four smooth discriminants: c_4(G) coefficient "
          "-(d+9)(d+1)/8 of T^4 at b = 3",
          all(mul_chern([Fr(-1), 0, 0, 0],
                        ch_to_chern(secant_ch(3, dd)))[3]
              == Fr(-(dd + 9) * (dd + 1), 8) for dd in (1, 3, 5, 7)))

    # (D) rank two
    c4G2 = sp.expand(cF_closed[3] + a * cF_closed[2] + (m / 2) * cF_closed[1])
    msol = sp.solve(sp.Eq(c4G2, 0), m)
    check("(D) r = 2: c_4(G) = 0 reads 6m = 3d - b^2 - 4ab",
          len(msol) == 1 and
          sp.simplify(msol[0] - (3 * d - b ** 2 - 4 * a * b) / 6) == 0)
    chiE = sp.expand((a ** 4 * 24 - 4 * a ** 2 * (m / 2) * 24
                      + 2 * (m / 2) ** 2 * 24) / 24)
    check("(D) r = 2: chi(E) = a^4 - 2 a^2 m + m^2/2 (Riemann-Roch, Todd = 1)",
          sp.simplify(chiE - (a ** 4 - 2 * a ** 2 * m + m ** 2 / 2)) == 0)
    # parity: at b = 3, m = (d - 3)/2 - 2a is even iff d = 3 mod 4
    ok = True
    for dd in range(1, 400, 2):
        for aa in range(-10, 11):
            mm = Fr(3 * dd - 9 - 12 * aa, 6)
            even = mm.denominator == 1 and mm.numerator % 2 == 0
            ok &= even == (dd % 4 == 3)
    check("(D) at b = 3: m = (d-3)/2 - 2a is an even integer iff "
          "d = 3 mod 4 (odd d < 400, |a| <= 10)", ok)
    # brute force with the independent Newton code
    found = {}
    for dd in range(1, 41):
        sols = []
        for aa in range(-12, 13):
            for mm in range(-150, 151):
                chE = chern_to_ch(2, [aa, Fr(mm, 2), 0, 0])
                chiE = chE[4]              # integral of ch_4 = coefficient
                if chiE.denominator != 1:
                    continue
                chG = [chE[k] + secant_ch(3, dd)[k] for k in range(5)]
                chG[0] = 3
                cG = ch_to_chern(chG)
                if cG[3] == 0:
                    sols.append((aa, mm))
        found[dd] = sols
    check("(D) brute force, b = 3, 1 <= d <= 40, |a| <= 12, |m| <= 150: "
          "rank two data exist exactly for d = 3 mod 4",
          all((len(found[dd]) > 0) == (dd % 4 == 3) for dd in found),
          "d with solutions: %s" % [dd for dd in found if found[dd]])
    check("(D) at d = 1 and d = 5 there are none; at d = 3 and d = 7 every "
          "solution has m = (d-3)/2 - 2a",
          not found[1] and not found[5] and found[3] and found[7] and
          all(mm == (dd - 3) // 2 - 2 * aa for dd in (3, 7)
              for aa, mm in found[dd]))
    # general b: for which d is 3d - b^2 - 4ab = 0 mod 12 solvable in a
    table = {}
    for bb in range(1, 7):
        table[bb] = sorted({dd % 12 for dd in range(1, 121)
                            if any((3 * dd - bb * bb - 4 * aa * bb) % 12 == 0
                                   for aa in range(12))})
    check("(D) residues of d mod 12 admitting rank two data, b = 1..6",
          table[3] == [3, 7, 11], "%s" % table)

    # (E) the route note's example: rank 2, c_1 = 0, c_2 = T^2
    vals = []
    for dd in (1, 3, 5, 7):
        chE = chern_to_ch(2, [0, 1, 0, 0])
        chG = [chE[k] + secant_ch(3, dd)[k] for k in range(5)]
        chG[0] = 3
        cG = ch_to_chern(chG)
        vals.append(cG[3] * 24)
    check("(E) route note example E = (2; 0, T^2): c_4(G) = "
          "180, 144, 84, 0 times T^4/24 at d = 1, 3, 5, 7",
          vals == [180, 144, 84, 0], "%s" % vals)
    check("(E) so G is a rank three bundle numerically only at d = 7, "
          "which is m = 2, a = 0 in (D)",
          [v == 0 for v in vals] == [False, False, False, True])

    # (F) Whitney against Newton on random data
    rng = random.Random(27)
    ok = True
    for _ in range(300):
        r = rng.randint(1, 8)
        dd = rng.choice([1, 3, 5, 7, 11, 15, 23])
        cE = [Fr(rng.randint(-20, 20), f) for f in (1, 2, 6, 24)]
        chE = chern_to_ch(r, cE)
        chG = [chE[k] + secant_ch(3, dd)[k] for k in range(5)]
        chG[0] = r + 1
        ok &= ch_to_chern(chG) == mul_chern(cE, ch_to_chern(secant_ch(3, dd)))
    check("(F) c(G) = c(E) c(F) against Newton's identities on 300 random "
          "data: integrality of c(G) is automatic", ok)

    print()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
