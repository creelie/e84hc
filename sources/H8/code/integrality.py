#!/usr/bin/env python3
"""
integrality.py

Is the object the secant construction needs forbidden by its numbers?

A sheaf realising a rational point of the secant plane has Chern character

    ch = a u + b v = a + b t - (a d / 2) t^2 - (b d / 6) t^3
                       + (a d^2 / 24) t^4 + ... ,

with t a principal polarisation, so that t^k / k! is an integral class for
every k.  Two things could in principle forbid such a sheaf before any
geometry is attempted:

  (1) integrality.  On a general variety the Chern character of a perfect
      complex is not itself integral, but its Chern classes c_1, ..., c_n
      are; on a complex torus the Chern character is integral as well, so
      the test below is the weaker of the two.  If the c_i
      computed from this ch by Newton's identities failed to be integral
      combinations of the classes t^k / k!, no sheaf could have this Chern
      character, in any dimension, and the secant route would be dead on
      arithmetic alone.

  (2) Bogomolov.  A mu-semistable sheaf satisfies
      Delta = 2 r c_2 - (r - 1) c_1^2 >= 0.  A negative discriminant would
      forbid a semistable realisation.

This script settles both, exactly, for 1 <= n <= 8, every squarefree d <= 11,
and every rank 0 <= a <= 4 and twist |b| <= 4.  It also compares the Chern
classes with the recursion that proves integrality in general (the paper,
Proposition "Numerical admissibility of the secant plane"): from
(1 + d t^2) c'(t) = (b + a d t) c(t), the coefficients gamma_k = k! c_k / t^k
satisfy gamma_0 = 1, gamma_1 = b, gamma_{k+1} = b gamma_k
+ d k (a - k + 1) gamma_{k-1}, so they are integers.  The answer to both is that
nothing is forbidden: the invariants are integral and the discriminant is
positive.  That is a negative result and it is the point of the script.  It
removes the last hope that the object at n >= 4 could be ruled out, or ruled
in, by counting; what is missing is the object, not a number.

Item (XX) of COMPUTATIONS.md.
"""
from fractions import Fraction as F

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


def ch_coeffs(n, a, b, d):
    """ch_k = g[k] * t^k, from ch = a u + b v truncated at degree n."""
    g = [F(0)] * (n + 1)
    fact = [F(1)]
    for k in range(1, n + 1):
        fact.append(fact[-1] * k)
    for j in range(0, n // 2 + 1):
        g[2 * j] += F(a) * F((-d) ** j) / fact[2 * j]
    for j in range(0, (n - 1) // 2 + 1):
        if 2 * j + 1 <= n:
            g[2 * j + 1] += F(b) * F((-d) ** j) / fact[2 * j + 1]
    return g


def chern_from_ch(n, g):
    """Newton's identities.  Everything is a multiple of a power of t, so the
    bookkeeping is one rational per degree: c_k = e[k] * t^k."""
    p = [F(0)] * (n + 1)              # p[k] = k! * ch_k, the power sums
    fact = [F(1)]
    for k in range(1, n + 1):
        fact.append(fact[-1] * k)
    for k in range(1, n + 1):
        p[k] = g[k] * fact[k]
    e = [F(0)] * (n + 1)
    e[0] = F(1)
    for k in range(1, n + 1):
        s = F(0)
        for i in range(1, k + 1):
            s += F((-1) ** (i - 1)) * e[k - i] * p[i]
        e[k] = s / k
    return e


def recursion(n, a, b, d):
    """gamma_0..gamma_n from gamma_{k+1} = b gamma_k + d k (a-k+1) gamma_{k-1}."""
    gam = [1, b]
    for k in range(1, n):
        gam.append(b * gam[k] + d * k * (a - k + 1) * gam[k - 1])
    return gam[:n + 1]


def run(n):
    print()
    print("  == n = %d ==" % n)
    fact = [F(1)]
    for k in range(1, n + 1):
        fact.append(fact[-1] * k)

    bad_int, bad_bog = [], []
    for d in (1, 2, 3, 5, 6, 7, 10, 11):
        for a in range(0, 5):
            for b in range(-4, 5):
                if a == 0 and b == 0:
                    continue
                g = ch_coeffs(n, a, b, d)
                e = chern_from_ch(n, g)
                # c_k = e[k] t^k = e[k] * k! * (t^k / k!), and t^k/k! is
                # integral, so integrality of c_k is integrality of e[k]*k!
                gam = recursion(n, a, b, d)
                for k in range(1, n + 1):
                    val = e[k] * fact[k]
                    if val.denominator != 1 or val != gam[k]:
                        bad_int.append((d, a, b, k, val))
                # Bogomolov: Delta = 2 r c_2 - (r-1) c_1^2, as a multiple of t^2
                if n >= 2:
                    r = F(a)
                    c1 = e[1]
                    c2 = e[2]
                    delta = 2 * r * c2 - (r - 1) * c1 * c1
                    # the closed form the paper records
                    closed = F(a) ** 2 * F(d) + F(b) ** 2
                    if delta != closed:
                        bad_bog.append(("form", d, a, b, delta, closed))
                    elif delta < 0:
                        bad_bog.append(("sign", d, a, b, delta))

    check("n=%d: every Chern class of the required ch is integral" % n,
          not bad_int,
          "8 fields x 5 ranks x 9 twists; equal to the integer recursion"
          if not bad_int
          else str(bad_int[:2]))
    if n >= 2:
        check("n=%d: Delta = N(b + a sqrt(-d)) = a^2 d + b^2 >= 0" % n,
              not bad_bog,
              "the norm form is positive definite, so Bogomolov never binds"
              if not bad_bog else str(bad_bog[:2]))

    # show the first few Chern classes in one case, for the record
    g = ch_coeffs(n, 1, 1, 3)
    e = chern_from_ch(n, g)
    txt = ",  ".join("c_%d = %s (t^%d/%d!)" % (k, e[k] * fact[k], k, k)
                     for k in range(1, min(n, 4) + 1))
    print("       a=1, b=1, d=3:  " + txt)


if __name__ == "__main__":
    print("(XX) the invariants of the required object are not forbidden")
    for n in range(1, 9):
        run(n)
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
