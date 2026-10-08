#!/usr/bin/env python3
"""
split_resolution.py

No two-term complex of powers of the polarisation runs the weakened
criterion.  Item (XXXIV).

Theorem "No two-term complex of powers of the polarisation runs the
criterion" is a statement about cohomology, and its proof has three
ingredients which this script records as data:

  (1) the classes  x_pi = ((d/2) pi _| t^2, 0, pi)  preserve every secant
      Chern character (item (XXVIII)), and on a line bundle O(e t) the
      evaluation map takes x_pi to the scalar (e^2 + d)/2 (pi _| t^2), which
      is never zero for real e and d > 0;
  (2) on an abelian n-fold with n >= 3, H^2(O(m t)) = 0 for every m != 0:
      for m > 0 by Kodaira vanishing, for m < 0 because a negative line
      bundle has cohomology only in degree n;
  (3) in the cone of a map between sums of powers of t, after cancelling
      pairs of equal twist joined by a nonzero scalar, no summand of the
      source has the twist of a summand of the target that it maps to by a
      unit, so the image of H^2(source) in H^2(target) is zero and the
      summand inclusions are not killed by H^2(O).

The script checks (1) for a range of e and d, records (2) as the vanishing
pattern of the index theorem, and applies (3) to the three split resolutions
that item (XXXII) found at d = 15 and d = 23: in each, no twist of E_1 equals
a twist of E_0, so the resolutions are already minimal and the theorem removes
them as they stand.  It also re-derives the secant moment identities (*) of
item (XXXII) for those three, so that the objects removed are exactly the
ones with the right Chern character.
"""

import sys
from fractions import Fraction as Fr

PASS, FAIL = [], []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % (tag, name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


# the three split resolutions of Table "burch" at b = 3, as twists of Theta
CANDIDATES = [
    (23, 4, (-11, -6, 0, 2, 7), (-10, -9, 5, 6)),
    (23, 5, (-8, -4, -3, -2, 1, 6), (-7, -6, -6, 4, 5)),
    (15, 6, (-8, -4, -4, -1, -1, 1, 4), (-7, -6, -6, 0, 3, 3)),
]
B = 3


def moments(d, b, e0, e1):
    p = [e + b for e in e0]
    q = [f + b for f in e1]
    target = (1, b, -d, -d * b, d * d)
    got = tuple(sum(x ** k for x in p) - sum(y ** k for y in q) for k in range(5))
    return got, target


def run():
    # (1) the scalar on a line bundle is never zero
    bad = [(e, d) for e in range(-30, 31) for d in range(1, 60)
           if Fr(e * e + d, 2) == 0]
    check("(e^2 + d)/2 is nonzero for every twist e and every d > 0 in range",
          not bad, "e in [-30, 30], d in [1, 59]: the evaluation of the compensated "
          "Poisson class on O(e t) is this multiple of pi _| t^2")

    # (2) the vanishing pattern of H^2(O(m t)) on an n-fold, n >= 3
    def h_nonzero_degrees(m, n):
        if m > 0:
            return {0}
        if m < 0:
            return {n}
        return set(range(n + 1))
    ok = all(2 not in h_nonzero_degrees(m, n)
             for n in (3, 4, 5, 6) for m in range(-40, 41) if m != 0)
    check("H^2(O(m t)) = 0 for m != 0 on an n-fold, 3 <= n <= 6, by the index theorem",
          ok, "a positive power has cohomology in degree 0 only, a negative one in "
          "degree n only, and 2 is neither for n >= 3")

    # (3) the three candidates are minimal and have the secant character
    rows, allok = [], True
    for d, r, e0, e1 in CANDIDATES:
        common = sorted(set(e0) & set(e1))
        got, target = moments(d, B, e0, e1)
        ok = (not common) and got == target and len(e0) == r + 1 and len(e1) == r
        allok = allok and ok
        rows.append("d=%d, r=%d: E0 twists %s, E1 twists %s, common twists %s, "
                    "moments %s = target %s" % (d, r, e0, e1, common, got, target))
    check("the three split resolutions of item (XXXII) are minimal and secant, "
          "so the theorem removes them as written", allok, "\n".join(rows))

    # a control: a complete intersection resolution of the right rank count
    # is never secant, which is item (XXXII) again in one line
    ci = [(d, a, b2, tw) for d in range(1, 30) for a in range(1, 12)
          for b2 in range(a, 12) for tw in range(-6, 13)
          if moments(d, tw, (-a, -b2), (-(a + b2),))[0]
          == moments(d, tw, (-a, -b2), (-(a + b2),))[1]]
    check("control: no Koszul resolution O(-(a+b)t) -> O(-a t) (+) O(-b t), twisted "
          "by any b in [-6, 12], is secant for d < 30", not ci,
          "which is Theorem 'no complete intersection' in the searched range")


if __name__ == "__main__":
    print("(XXXIV) no split resolution runs the criterion")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
