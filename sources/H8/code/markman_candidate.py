#!/usr/bin/env python3
"""
markman_candidate.py

The Chern character of Markman's candidate object in dimension eight
(arXiv:2509.23403v2, Section 12), computed exactly.  Item (XXVII).

Setting.  (X, Theta) a principally polarised abelian fourfold, d an odd
squarefree integer >= 3, K = Q(sqrt(-d)), n = (d+9)/2.  Take n generic
translates D_i of Theta, cyclically indexed by Z/nZ, so that any two, three or
four of them meet transversally and any five have empty intersection.  Put
Z_i = D_i meet D_{i+1}, Z = union of the Z_i, and let nu : Ztilde -> Z be the
partial normalisation of Z at m = (d+9)(2d-1) of its isolated points of
self-intersection.  Markman states that the Chern character of

    F = [ O_X -> nu_* O_Ztilde ] (x) O_X(k Theta)

lies on the secant span{ exp(sqrt(-d) Theta), exp(-sqrt(-d) Theta) }, which
over Q is spanned by

    alpha = 1 - (d/2) Theta^2 + (d^2/24) Theta^4,
    beta  = Theta - (d/6) Theta^3,

with the twist written as O_X(Theta).  The computation below shows that the
statement holds exactly for the twist k = 3, and identifies the point of the
secant plane: ch(F) = alpha + 3 beta, the rational point (a, b) = (1, 3) of
the plane P_Theta of the paper, whose norm N(3 + sqrt(-d)) = d + 9 = 2n is
the number of divisors used.

Ingredients, all exact.  On a principally polarised abelian fourfold
chi(O_X(k Theta)) = k^4 and Theta^4 = 24 points.  Koszul complexes give
    ch(O_{Z_i}) = (1 - e^{-Theta})^2,   chi(O_{Z_i}) = 14,
    ch(O_{C})   = (1 - e^{-Theta})^3,   chi(O_C) = -36,   C = D_i D_{i+1} D_{i+2},
    ch(O_{pt})  = (1 - e^{-Theta})^4,   24 points for four divisors.
The union Z is locally a union of coordinate subspaces, so its structure
sheaf is resolved by the Mayer-Vietoris complex of the Z_i and their
scheme-theoretic intersections: adjacent pairs meet in the curves C_i (n of
them), pairs at cyclic distance >= 2 meet in 24 points (n(n-3)/2 pairs),
consecutive triples meet in 24 points (n of them), and nothing else meets.
The isolated singular points of Z are the pairs at distance >= 3, of which
there are 12 n (n-5) = (d+9)(3d-3), as Markman states; normalising one of
them raises chi by one.  Hence
    ch(nu_* O_Ztilde) = n Theta^2 - 2n Theta^3 + chi(O_Ztilde) [pt],
    chi(O_Ztilde) = 110 n - 12 n^2 + 2n(2d-1) = (d+9)(27-d).

Checks, for every odd squarefree d from 3 to 101:
  (M1) the isolated point count 12 n (n-5) equals (d+9)(3d-3) and exceeds the
       number m = (d+9)(2d-1) of points normalised;
  (M2) chi(O_Ztilde) = (d+9)(27-d) = 243 + 18d - d^2;
  (M3) ch(F) with twist k = 3 equals alpha + 3 beta in Q[Theta]/(Theta^5),
       degree by degree, and with twist k = 1 the degree two component is
       off by exactly -4 Theta^2, so the twist in Markman's text is to be
       read as 3 Theta;
  (M4) the norm of 3 + sqrt(-d) is 2n, the number of divisors, and the
       Bogomolov discriminant of F is (d+9) Theta^2;
  (M5) the rank of the transform: int_X ch(F)^2 = 8d(d-9) and
       int_X ch(F) ch(F^dual) = 8d(d+9), both nonzero for squarefree d, so the
       objects Phi(F x F) and Phi(F x F^dual) on X x Xhat have nonzero rank;
       the same formula reproduces Markman's rank 8q at n = 3 for (1,1).
"""

import sys
from fractions import Fraction as F


# ------------------------------------------------ Q[Theta]/(Theta^5), int = 24
DEG = 4
TOP = 24


def poly(*coeffs):
    c = [F(x) for x in coeffs] + [F(0)] * (DEG + 1)
    return c[:DEG + 1]


def pmul(p, q):
    out = [F(0)] * (DEG + 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            if i + j <= DEG and b != 0:
                out[i + j] += a * b
    return out


def padd(p, q):
    return [a + b for a, b in zip(p, q)]


def pscale(c, p):
    return [F(c) * a for a in p]


def integral(p):
    return p[DEG] * TOP


def pexp(c):
    """exp(c Theta)."""
    out = [F(0)] * (DEG + 1)
    fact = 1
    for k in range(DEG + 1):
        if k:
            fact *= k
        out[k] = F(c) ** k / fact
    return out


def fmt(p):
    terms = []
    for k, a in enumerate(p):
        if a != 0:
            terms.append("%s Theta^%d" % (a, k) if k else "%s" % a)
    return " + ".join(terms) if terms else "0"


def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    return (1, 0) if ok else (0, 1)


def squarefree(d):
    k = 2
    while k * k <= d:
        if d % (k * k) == 0:
            return False
        k += 1
    return True


def candidate(d):
    n = (d + 9) // 2
    one = poly(1)
    em = pexp(-1)                                    # e^{-Theta}
    u = padd(one, pscale(-1, em))                    # 1 - e^{-Theta}
    ch_surface = pmul(u, u)
    ch_curve = pmul(ch_surface, u)
    ch_point = pmul(ch_curve, u)
    chi_surface = integral(ch_surface)
    chi_curve = integral(ch_curve)
    chi_point = integral(ch_point)
    # Mayer-Vietoris for the union Z
    pairs_far = n * (n - 3) // 2                     # cyclic distance >= 2
    chZ = pscale(n, ch_surface)
    chZ = padd(chZ, pscale(-n, ch_curve))            # adjacent pairs
    chZ = padd(chZ, pscale(-pairs_far, ch_point))    # distant pairs
    chZ = padd(chZ, pscale(n, ch_point))             # consecutive triples
    isolated = 24 * (n * (n - 5) // 2)               # distance >= 3
    m = (d + 9) * (2 * d - 1)                        # points normalised
    chZt = padd(chZ, pscale(m, poly(0, 0, 0, 0, F(1, TOP))))
    chiZt = integral(chZt)
    alpha = padd(padd(one, poly(0, 0, F(-d, 2))), poly(0, 0, 0, 0, F(d * d, 24)))
    beta = padd(poly(0, 1), poly(0, 0, 0, F(-d, 6)))
    out = {"n": n, "chi_surface": chi_surface, "chi_curve": chi_curve,
           "chi_point": chi_point, "isolated": isolated, "m": m,
           "chiZt": chiZt, "alpha": alpha, "beta": beta}
    for k in (1, 3):
        chF = pmul(pexp(k), padd(one, pscale(-1, chZt)))
        out["chF%d" % k] = chF
    return out


def main():
    print("Markman's candidate object in dimension eight")
    NP = NF = 0
    ds = [d for d in range(3, 102, 2) if squarefree(d)]

    rows, ok = [], True
    for d in ds:
        c = candidate(d)
        n = c["n"]
        good = (c["isolated"] == (d + 9) * (3 * d - 3) and c["m"] <= c["isolated"]
                and c["chi_surface"] == 14 and c["chi_curve"] == -36
                and c["chi_point"] == 24)
        ok = ok and good
        if d in (3, 5, 7, 11):
            rows.append("d=%2d: n=%2d divisors, isolated points %d = (d+9)(3d-3), "
                        "normalised %d" % (d, n, c["isolated"], c["m"]))
    p, f = check("(M1) chi(O_Z_i) = 14, chi(O_C) = -36, four divisors meet in 24 "
                 "points; isolated points 12n(n-5) = (d+9)(3d-3) >= (d+9)(2d-1)",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    rows, ok = [], True
    for d in ds:
        c = candidate(d)
        good = (c["chiZt"] == (d + 9) * (27 - d) == 243 + 18 * d - d * d)
        ok = ok and good
        if d in (3, 5, 7, 11, 101):
            rows.append("d=%3d: chi(O_Ztilde) = %d = (d+9)(27-d)" % (d, c["chiZt"]))
    p, f = check("(M2) chi(O_Ztilde) = 110n - 12n^2 + 2n(2d-1) = (d+9)(27-d)",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    rows, ok = [], True
    for d in ds:
        c = candidate(d)
        target = padd(c["alpha"], pscale(3, c["beta"]))
        good3 = (c["chF3"] == target)
        diff1 = padd(c["chF1"], pscale(-1, padd(c["alpha"], c["beta"])))
        good1 = (diff1[2] == -4 and diff1[0] == 0 and diff1[1] == 0)
        ok = ok and good3 and good1
        if d in (3, 5):
            rows.append("d=%d: ch(F(3 Theta)) = %s" % (d, fmt(c["chF3"])))
            rows.append("      alpha + 3 beta  = %s" % fmt(target))
    p, f = check("(M3) with the twist by 3 Theta, ch(F) = alpha + 3 beta exactly; "
                 "with the twist by Theta the degree two part misses by -4 Theta^2",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    rows, ok = [], True
    for d in ds:
        c = candidate(d)
        n = c["n"]
        norm = 3 * 3 + d
        # Bogomolov discriminant 2a c_2 - (a-1) c_1^2 with a = 1, c_1 = 3 Theta,
        # ch_2 = -(d/2) Theta^2, c_2 = (c_1^2 - 2 ch_2)/2 = (9 + d)/2 Theta^2
        c2 = F(9 + d, 2)
        disc = 2 * c2
        good = (norm == 2 * n and disc == d + 9)
        ok = ok and good
        if d in (3, 5, 7):
            rows.append("d=%d: N(3 + sqrt(-d)) = %d = 2n, Delta(F) = %s Theta^2"
                        % (d, norm, disc))
    p, f = check("(M4) N(3 + sqrt(-d)) = d + 9 = 2n and the Bogomolov "
                 "discriminant is (d+9) Theta^2", ok, "\n".join(rows))
    NP += p
    NF += f

    rows, ok = [], True
    for d in ds:
        c = candidate(d)
        chF = c["chF3"]
        chFd = padd(c["alpha"], pscale(-3, c["beta"]))   # tau flips odd degrees
        r_same = integral(pmul(chF, chF))
        r_dual = integral(pmul(chF, chFd))
        good = (r_same == 8 * d * (d - 9) and r_dual == 8 * d * (d + 9)
                and r_same != 0 and r_dual != 0)
        ok = ok and good
        if d in (3, 5, 7, 11):
            rows.append("d=%2d: int ch(F)^2 = %d = 8d(d-9),  int ch(F) ch(F^dual) = %d = 8d(d+9)"
                        % (d, r_same, r_dual))
    # the threefold control: Markman's rank 8q for (a,b) = (1,1)
    global DEG, TOP
    DEG, TOP = 3, 6
    ctrl = True
    for q in (3, 5, 7):
        a3 = padd(poly(1), poly(0, 0, F(-q, 2)))
        b3 = padd(poly(0, 1), poly(0, 0, 0, F(-q, 6)))
        s = padd(a3, b3)
        ctrl = ctrl and integral(pmul(s, s)) == -8 * q
    DEG, TOP = 4, 24
    ok = ok and ctrl
    rows.append("threefold control: int (alpha + beta)^2 = -8q for q = 3, 5, 7, "
                "which is Markman's rank 8q up to the shift")
    p, f = check("(M5) the transforms Phi(F x F) and Phi(F x F^dual) have ranks "
                 "8d(d-9) and 8d(d+9), nonzero for squarefree d", ok,
                 "\n".join(rows))
    NP += p
    NF += f

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
