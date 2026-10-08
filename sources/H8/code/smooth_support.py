#!/usr/bin/env python3
"""
smooth_support.py

A secant object of rank one whose support is a smooth surface.

Theorem 14.110 and Corollary 14.114 remove every secant object on an abelian
fourfold whose support has two transversal branches of codimension two through
a point.  What they leave open is a support that is smooth, or that meets
itself only along curves.  This script settles the numerical half of that
case.

Let X be a principally polarised abelian fourfold, d > 0 squarefree, and let

    F = I_S(b Theta),     ch(F) = u_Theta + b v_Theta,

with S a smooth surface.  Grothendieck-Riemann-Roch on the abelian fourfold,
where the Todd class is one, turns ch(F) into the complete invariant package
of S.  Writing N for the class multiple and lambda for the restriction of
Theta,

    [S]   = N Theta^2,                N = (b^2 + d)/2 = Nm(b + sqrt(-d))/2,
    i_* K_S = (4 b N / 3) Theta^3,
    chi(O_S) = 4 N (2 b^2 - N),
    K_S . lambda = 32 b N,            lambda^2 = 24 N,
    [S]^2 = 24 N^2 = K_S^2 - e(S)     (self-intersection, T_X trivial),
    12 chi(O_S) = K_S^2 + e(S)        (Noether),

and the last two give

    K_S^2 = 12 N (4 b^2 - N),         e(S) = 12 N (4 b^2 - 3 N).

Three inequalities then bracket N, and all three are available because
Omega^1_S is a quotient of the trivial bundle Omega^1_X restricted to S, so it
is globally generated, so K_S = det Omega^1_S is globally generated, hence
nef, and c_2(Omega^1_S) = e(S) >= 0:

    Hodge index on S, applied to K_S against the ample lambda:  N >= 4b^2/9,
    c_2 of a globally generated bundle is non-negative:         N <= 4b^2/3,
    Bogomolov-Miyaoka-Yau, K_S nef and big so S is minimal
    of general type:                                            N <= b^2.

In terms of the discriminant these read d >= -b^2/9, which is vacuous, then
d <= 5b^2/3, and then d <= b^2.  The third is the binding one.  At b = 3,
which is the value Proposition 14.94 forces on the fourfold, it leaves

    d in {1, 2, 3, 5, 6, 7},

and if N is required to be an integer, which is what a support built from
translates of the polarisation needs, then

    d in {1, 3, 5, 7},

four discriminants out of infinitely many.  Equality in the Hodge index would
force K_S numerically proportional to lambda, and that happens only at
N = 4b^2/9, which is never an admissible N, so K_S is never a multiple of the
restricted polarisation.

What the script checks, exactly over Q and with the Chern characters expanded
from scratch rather than quoted:

  (a) the class, the canonical pushforward, and chi(O_S) read off ch(F),
      against the closed forms above, for a range of b and d;
  (b) Noether and the self-intersection formula reproduce K_S^2 and e(S);
  (c) the three inequalities, and the exact list of admissible d at b = 3;
  (d) that d = 9 is the first value excluded by Bogomolov-Miyaoka-Yau alone,
      and that it is excluded again for being a square;
  (e) that K_S is never numerically proportional to lambda.

Item (XXX) of COMPUTATIONS.md.
"""
from fractions import Fraction as F

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


# ------------------------------------------------ the truncated Chern ring
def mul(p, q, n=4):
    """product in Q[t]/(t^{n+1}), coefficients of t^k."""
    r = [F(0)] * (n + 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, bb in enumerate(q):
            if bb and i + j <= n:
                r[i + j] += a * bb
    return r


def exp_t(c, n=4):
    """coefficients of e^{c t}."""
    out, fact = [], 1
    for k in range(n + 1):
        if k:
            fact *= k
        out.append(F(c) ** k / fact)
    return out


def secant_ch(b, d, n=4):
    """ch(F) = u_t + b v_t, coefficients of t^k."""
    out = []
    fact = 1
    for k in range(n + 1):
        if k:
            fact *= k
        if k % 2 == 0:
            out.append(F((-d) ** (k // 2), fact))
        else:
            out.append(F(b) * F((-d) ** ((k - 1) // 2), fact))
    return out


def structure_sheaf(b, d, n=4):
    """ch(O_S) = 1 - ch(F) e^{-b t}, for F = I_S(b Theta)."""
    prod = mul(secant_ch(b, d, n), exp_t(-b, n), n)
    out = [-x for x in prod]
    out[0] += 1
    return out


def run():
    print()
    bad_class, bad_can, bad_chi, bad_noether = [], [], [], []
    for b in range(1, 7):
        for d in range(1, 60):
            if not squarefree(d):
                continue
            ch = structure_sheaf(b, d)
            N = F(b * b + d, 2)
            # (a) the class: ch_2 = [S]
            if ch[0] != 0 or ch[1] != 0:
                bad_class.append(("codim", b, d))
            if ch[2] != N:
                bad_class.append(("class", b, d, ch[2], N))
            # the canonical pushforward: ch_3 = -(1/2) i_* K_S
            if -2 * ch[3] != F(4 * b, 3) * N:
                bad_can.append((b, d, -2 * ch[3], F(4 * b, 3) * N))
            # chi(O_S): ch_4 * Theta^4 with Theta^4 = 24 [pt]
            chi = ch[4] * 24
            if chi != 4 * N * (2 * b * b - N):
                bad_chi.append((b, d, chi, 4 * N * (2 * b * b - N)))
            # (b) Noether and the self-intersection formula
            K2 = 12 * N * (4 * b * b - N)
            e = 12 * N * (4 * b * b - 3 * N)
            if K2 + e != 12 * chi or K2 - e != 24 * N * N:
                bad_noether.append((b, d))

    check("ch(F) puts S in codimension two with class N Theta^2, "
          "N = Nm(b + sqrt(-d))/2", not bad_class,
          "b <= 6, d squarefree < 60" if not bad_class else str(bad_class[:2]))
    check("the canonical class pushes forward to (4bN/3) Theta^3",
          not bad_can, "read off ch_3" if not bad_can else str(bad_can[:2]))
    check("chi(O_S) = 4N(2b^2 - N)", not bad_chi,
          "read off ch_4, Theta^4 = 24 [pt]"
          if not bad_chi else str(bad_chi[:2]))
    check("Noether and self-intersection give K_S^2 = 12N(4b^2-N) and "
          "e(S) = 12N(4b^2-3N)", not bad_noether,
          "both identities hold in every case"
          if not bad_noether else str(bad_noether[:2]))

    # (c) the three inequalities
    print()
    vac = []
    for b in range(1, 7):
        for d in range(1, 400):
            if not squarefree(d):
                continue
            N = F(b * b + d, 2)
            if 9 * N < 4 * b * b:
                vac.append((b, d))
    check("the Hodge index bound N >= 4b^2/9 is implied by d > 0",
          not vac,
          "it never binds; the Bogomolov-Miyaoka-Yau bound N <= b^2 is the "
          "one that decides")

    for b in (2, 3, 4):
        gg, bmy, integral = [], [], []
        for d in range(1, 400):
            if not squarefree(d):
                continue
            N = F(b * b + d, 2)
            K2 = 12 * N * (4 * b * b - N)
            e = 12 * N * (4 * b * b - 3 * N)
            if e >= 0:
                gg.append(d)
            if K2 <= 3 * e and K2 > 0:
                bmy.append(d)
                if N.denominator == 1:
                    integral.append(d)
        check("b=%d: c_2 >= 0 gives d <= 5b^2/3 and BMY gives d <= b^2" % b,
              max(bmy) <= b * b and max(gg) <= F(5 * b * b, 3),
              "largest d surviving c_2 is %d, with 5b^2/3 = %s; surviving "
              "BMY is %d, with b^2 = %d"
              % (max(gg), F(5 * b * b, 3), max(bmy), b * b))
        if b == 3:
            check("b=3: six discriminants survive, four of them with N "
                  "an integer",
                  bmy == [1, 2, 3, 5, 6, 7] and integral == [1, 3, 5, 7],
                  "admissible d = %s; those with N in Z, which is what a "
                  "support of Markman's shape needs, are %s"
                  % (bmy, integral))

    # (d) the first exclusion
    N9 = F(9 + 9, 2)
    K2, e = 12 * N9 * (36 - N9), 12 * N9 * (36 - 3 * N9)
    check("d=9 is the equality case of Bogomolov-Miyaoka-Yau", K2 == 3 * e,
          "K^2 = %d = 3 e = %d, so d=9 would need a ball quotient; it is "
          "excluded anyway for not being squarefree" % (K2, 3 * e))

    # (e) K_S is never proportional to lambda
    prop = []
    for b in range(1, 7):
        for d in range(1, 200):
            if not squarefree(d):
                continue
            N = F(b * b + d, 2)
            if 9 * N == 4 * b * b:
                prop.append((b, d))
    check("K_S is never numerically proportional to the restricted "
          "polarisation", not prop,
          "equality in the Hodge index needs N = 4b^2/9, which no "
          "admissible (b,d) reaches")

    # the table the paper prints
    print()
    print("       b=3:   d    N    chi     K^2      e      K.lambda  lambda^2")
    for d in (1, 3, 5, 7):
        N = F(9 + d, 2)
        print("            %3d %4d %6d %7d %7d %9d %9d"
              % (d, N, 4 * N * (18 - N), 12 * N * (36 - N),
                 12 * N * (36 - 3 * N), 96 * N, 24 * N))


if __name__ == "__main__":
    print("(XXX) a rank one secant object with smooth support")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
