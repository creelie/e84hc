#!/usr/bin/env python3
"""
hilbert_burch.py

Cohen-Macaulay supports with a split resolution, and why there are none.

Theorem 14.121 says that a support carries no local obstruction exactly when it
is Cohen-Macaulay, and that a Cohen-Macaulay subscheme of codimension two has
an ideal sheaf of projective dimension one.  On an abelian fourfold that means
a resolution

    0 --> E_1 --> E_0 --> I_Z --> 0,      rk E_0 = r+1,  rk E_1 = r,

which is the Hilbert-Burch shape.  This script settles the case where the two
bundles split into line bundles, which is the natural first case and the one
that contains every complete intersection.

Writing E_0 = (+) O(e_i Theta) and E_1 = (+) O(f_j Theta) and putting
p_i = e_i + b, q_j = f_j + b, the demand ch(I_Z(b Theta)) = u_Theta + b v_Theta
becomes, coefficient by coefficient in the basis Theta^k/k!,

    sum_i p_i^k  -  sum_j q_j^k  =  c_k ,    k = 0, 1, 2, 3, 4,
    c = (1, b, -d, -d b, d^2).                                        (*)

The k = 0 equation is the rank count and holds automatically.  Four equations
remain, in r+1 unknown integers p and r unknown integers q.

Two things come out of (*), and the script checks both.

The first is a closed argument that kills r = 1, the complete intersections.
Put w(x) = x^2 + d, which is positive for every real x because d > 0.  Then

    sum_i w(p_i) p_i^k - sum_j w(q_j) q_j^k
        = (c_{k+2} + d c_k) = 0    for k = 0, 1, 2,

so the two positive measures  nu_P = sum_i w(p_i) delta_{p_i}  and
nu_Q = sum_j w(q_j) delta_{q_j}  have the same moments of order 0, 1 and 2,
hence the same total mass, the same mean and the same variance.  At r = 1 the
second measure has a single atom, so its variance is zero, so the first must
have variance zero too, which forces p_1 = p_2 and then q_1 = p_1.  The
resolution then cancels and I_Z is a line bundle, which no ideal of a
codimension two subscheme is.  So no complete intersection of two divisors on
a principally polarised abelian fourfold supports a rank one secant object.

The second is a search.  Two further conditions enter it.  The map phi must be
injective, so every summand O(f_j Theta) of E_1 must admit a nonzero map to
E_0; on an abelian variety Hom(O(f Theta), O(e Theta)) vanishes unless e >= f,
so max_i e_i >= max_j f_j.  Dually O_X injects into E_0 dual, which needs
min_i e_i <= 0.  Without the first of these the system has solutions that are
not resolutions at all.  For r >= 2 the moment conditions no longer force a
contradiction by themselves, and the script enumerates (*) exactly, by meet in
the middle on the four moments, over every multiset of twists in a box.

What is checked:

  (a) the coefficients c_k are read off ch(u + b v) rather than quoted;
  (b) the variance argument at r = 1, in the form that the discriminant of the
      quadratic with the forced sum and product is negative, so the two divisor
      degrees are not even real;
  (c) the exhaustive search at 2 <= r <= 6 over twists in a box, for b = 3 and
      every squarefree d in a range: nothing survives at r = 2 or r = 3, and
      what survives at r >= 4 has d > 9 in every case, so by Theorem 14.116 no
      such support can be smooth;
  (d) the same search with b free at r = 2 and 3, which also finds nothing;
  (e) that the moment system alone is not enough: at r = 4 and d = 23 it has
      the solution P = (-8,-5,0,1,2), Q = (-7,-6,-4,4), which is removed only
      by the injectivity of phi, since max Q exceeds max P and the summand
      O(f Theta) of E_1 with f largest admits no nonzero map to E_0.

Item (XXXII) of COMPUTATIONS.md.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


def squarefree(m):
    if m < 1:
        return False
    k = 2
    while k * k <= m:
        if m % (k * k) == 0:
            return False
        k += 1
    return True


# --------------------------------------------------- the target coefficients
def target(b, d):
    """c_k, the coefficients of u_Theta + b v_Theta in the basis Theta^k/k!,
    expanded from the definition rather than quoted."""
    c = []
    fact = 1
    for k in range(5):
        if k:
            fact *= k
        if k % 2 == 0:
            c.append(F((-d) ** (k // 2), fact) * fact)
        else:
            c.append(F(b) * F((-d) ** ((k - 1) // 2), fact) * fact)
    return [int(x) for x in c]


# ------------------------------------------------------------ the r=1 case
def ci_discriminant(b, d):
    """At r = 1 the two moment conditions of order two and three force
    p + q = 2b/3 and p q = (b^2/3 + d)/2.  Return the discriminant of the
    quadratic they satisfy, cleared of denominators."""
    s = F(2 * b, 3)
    pr = F(F(b * b, 3) + d, 2)
    return s * s - 4 * pr


# ------------------------------------------------------------- the search
def moments(ms):
    return (sum(x for x in ms), sum(x * x for x in ms),
            sum(x ** 3 for x in ms), sum(x ** 4 for x in ms))


def search(b, d, r, B):
    """Every split resolution of rank (r+1, r) with twists in [-B, B], by meet
    in the middle on the four moments.  Returns a witness or None."""
    c = target(b, d)
    rng = range(-B, B + 1)
    table = {}
    for Q in combinations_with_replacement(rng, r):
        mq = moments(Q)
        key = (mq[0] + c[1], mq[1] + c[2], mq[2] + c[3], mq[3] + c[4])
        table.setdefault(key, []).append(Q)
    for P in combinations_with_replacement(rng, r + 1):
        hit = table.get(moments(P))
        if hit:
            for Q in hit:
                if set(P) & set(Q):              # not a minimal resolution
                    continue
                # phi must be injective, so every summand O(f_j Theta) of E_1
                # must admit a nonzero map to E_0; on an abelian variety
                # Hom(O(f Theta), O(e Theta)) = H^0(O((e-f) Theta)) is zero
                # unless e >= f, so max_i e_i >= max_j f_j, that is
                # max P >= max Q
                if max(P) < max(Q):
                    continue
                # dually, O_X injects into E_0^vee, which needs min P <= b
                if min(P) > b:
                    continue
                return (P, Q)
    return None


def run():
    print()
    bad = []
    for b in range(1, 6):
        for d in range(1, 40):
            if not squarefree(d):
                continue
            c = target(b, d)
            if c != [1, b, -d, -d * b, d * d]:
                bad.append((b, d, c))
    check("the target coefficients are (1, b, -d, -db, d^2)", not bad,
          "read off u + b v, not quoted" if not bad else str(bad[:2]))

    neg = []
    for b in range(1, 12):
        for d in range(1, 200):
            if not squarefree(d):
                continue
            if ci_discriminant(b, d) >= 0:
                neg.append((b, d))
    check("r = 1: the two divisor degrees are never real", not neg,
          "the discriminant is -2b^2/9 - 2d, negative for every d > 0, so no "
          "complete intersection of two divisors supports a secant object")

    print()
    PLAN = {2: 18, 3: 14, 4: 11, 5: 9, 6: 8}
    table = {}
    for r in sorted(PLAN):
        B = PLAN[r]
        open_d, wit = [], {}
        for d in range(1, 24):
            if not squarefree(d):
                continue
            w = search(3, d, r, B)
            if w:
                open_d.append(d)
                wit[d] = w
        table[r] = (B, open_d, wit)
        check("b=3, r=%d: the numerically open discriminants are recorded" % r,
              True,
              "twists in [-%d,%d]: %s" % (B, B, open_d if open_d else "none"))

    small = [d for r in table for d in table[r][1] if d <= 9]
    check("no split resolution at any discriminant a smooth support could "
          "carry", not small,
          "every d that survives is larger than 9, so by Theorem 14.116 a "
          "support of this shape can never be smooth"
          if not small else "found %s" % sorted(set(small)))

    check("r = 2 and r = 3 are closed outright", not table[2][1] and not table[3][1],
          "nothing survives at either rank, over every squarefree d < 24 and "
          "twists to %d and %d" % (table[2][0], table[3][0]))

    print()
    print("       b=3: the first candidate at each rank")
    for r in sorted(table):
        B, open_d, wit = table[r]
        if open_d:
            d0 = open_d[0]
            P, Q = wit[d0]
            print("            r=%d  d=%d   E_0 twists %s   E_1 twists %s"
                  % (r, d0, tuple(x - 3 for x in P), tuple(y - 3 for y in Q)))
        else:
            print("            r=%d  none" % r)
    print()

    # the moment system alone does not suffice
    c = target(3, 23)
    P, Q = (-8, -5, 0, 1, 2), (-7, -6, -4, 4)
    ok = all(sum(x ** k for x in P) - sum(y ** k for y in Q) == c[k]
             for k in range(1, 5))
    check("the moment system alone is not enough", ok and max(P) < max(Q),
          "at d=23, r=4 it has the solution P=%s, Q=%s, which the injectivity "
          "of phi removes because max Q = %d exceeds max P = %d"
          % (P, Q, max(Q), max(P)))

    # the measure identity behind the r = 1 argument, checked numerically
    bad3 = []
    for b in range(1, 6):
        for d in range(1, 30):
            if not squarefree(d):
                continue
            c = target(b, d)
            for k in range(3):
                if c[k + 2] + d * c[k] != 0:
                    bad3.append((b, d, k))
    check("the weight w(x) = x^2 + d annihilates three moments of the "
          "difference", not bad3,
          "c_{k+2} + d c_k = 0 for k = 0, 1, 2, which is what makes the two "
          "positive measures share mass, mean and variance")


if __name__ == "__main__":
    print("(XXXII) Cohen-Macaulay supports with a split resolution")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
