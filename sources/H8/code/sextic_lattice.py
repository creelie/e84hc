#!/usr/bin/env python3
"""
sextic_lattice.py

Item (LVII) of the computations: the integral classes of the flat secant
space of a sextic CM field, and the numerical condition of
prop:sexticcount(iii) on them.

Setting.  F = F_0(sqrt(-q)) with F_0 a totally real cubic field and q in F_0
totally positive; X a principally polarised abelian sixfold with real
multiplication by O = O_{F_0}; theta_1, theta_2, theta_3 the components of
the polarisation on the eigenspaces of F_0.  The rational points of the flat
secant space S(0,q) are the classes
    v(c_0, f, g, c_3) = c_0 B_1 B_2 B_3 + sum_j tau_j(f) theta_j B_k B_l
                        + sum_j tau_j(g) B_j theta_k theta_l
                        + c_3 theta_1 theta_2 theta_3,
    B_j = 1 - tau_j(q) theta_j^2 / 2,  {j, k, l} = {1, 2, 3},
with c_0, c_3 in Q and f, g in F_0, and
    chi(v, v) = -8 ( Nm(q) c_0^2 + Tr(Nm(q) f^2 / q) + Tr(q g^2) + c_3^2 ).
A minimal factor of an Orlov product with character v exists numerically
only if chi(v, v) <= -(r^3(v) - 2 r^2(v) + 22) (prop:sexticcount(iii)).

What is checked:

  (A) chi(v, v) is even for every integral class v of even degree on a
      complex torus of dimension six (random classes, and the reason:
      the terms of degree 2k and 12 - 2k pair twice, and the middle term
      is x ^ x with x of degree six, a sum of doubled products);

  (B) for every support of the coefficient tensor w and every rank pattern
      consistent with it, r^3 - 2 r^2 <= 4, with equality only for the
      general shape (r^2, r^3) = (54, 112); so the condition reads
      chi <= -T with T = r^3 - 2 r^2 + 22 <= 26 for every class, and
      T is attained only by the general shape.  The relaxation used is an
      upper bound: a slice of the tensor has rank 2 only if its support
      contains a diagonal, rho_j = 1 forces the two slices along j to be
      proportional, and then every slice along another index has rank at
      most one;

  (C) for q = 1 the classes Re exp(i theta) and Im exp(i theta), theta the
      principal polarisation, are integral points of S(0,1) with
      chi = -32 and N_w = 2, for every field below;

  (D) for sixteen totally real cubic fields (Q(zeta_7)^+, Q(zeta_9)^+ and
      the fourteen fields x^3 + a x^2 + b x + c, |a| <= 1, |b|, |c| <= 7,
      irreducible with squarefree discriminant, so that O = Z[alpha]) and
      q = 1 and q = k + alpha (k least with q totally positive): the lattice
      of integral classes of S(0,q), computed exactly (modulo three primes
      that split in F_0, rational reconstruction, confirmed modulo a fourth
      prime and by the direct integral of v^dual v), has no nonzero class
      with -chi <= 24, and -chi/8 is an integral quadratic form on it;
      so -chi >= 32 and every integral class satisfies the condition of
      prop:sexticcount(iii), whatever its shape.  For q = 1 the classes with
      -chi = 32 are exactly the four classes of (C).

Everything is exact.  Standard library only.  The model and the lattice
computation are in attack/gaps/sextic/s2_lattice.py.

Run:  python3 sextic_lattice.py
"""
import os, sys, random
from fractions import Fraction as Fr
from itertools import product, combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "attack", "gaps", "sextic"))
import s2_lattice as S                                    # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("         " + detail)


# ------------------------------------------------------------------ (A)
def part_A():
    rng = random.Random(6)
    p = (1 << 61) - 1
    top = (1 << 12) - 1
    evens = [m for m in range(1 << 12) if bin(m).count("1") % 2 == 0]
    ok = True
    for _ in range(40):
        v = {m: rng.randint(-3, 3) for m in rng.sample(evens, 60)}
        v = {m: c for m, c in v.items() if c}
        val = S.ext_mul(S.ext_dual({m: c % p for m, c in v.items()}),
                        {m: c % p for m, c in v.items()}, p).get(top, 0)
        val = val if val < p // 2 else val - p
        ok = ok and val % 2 == 0
    check("chi(v, v) = int v^dual v is even for integral classes of even "
          "degree on a six-dimensional torus (40 random classes)", ok)


# ------------------------------------------------------------------ (B)
def part_B():
    eps = list(product((1, -1), repeat=3))
    best, attained = -99, set()
    for mask in range(1, 256):
        supp = {e for i, e in enumerate(eps) if mask >> i & 1}
        N = len(supp)
        A = sum(len({(e[j], e[k]) for e in supp})
                for j, k in combinations(range(3), 2))
        opts = []
        for j in range(3):
            o = [k for k in range(3) if k != j]
            sl = {}
            for s in (1, -1):
                sup = {(e[o[0]], e[o[1]]) for e in supp if e[j] == s}
                if not sup:
                    r = [0]
                else:
                    diag = ({(1, 1), (-1, -1)} <= sup) or \
                           ({(1, -1), (-1, 1)} <= sup)
                    r = [1, 2] if diag else [1]
                sl[s] = (sup, r)
            ch = []
            for r1 in sl[1][1]:
                for r2 in sl[-1][1]:
                    if not sl[1][0] or not sl[-1][0]:
                        rhos = [1]
                    elif sl[1][0] == sl[-1][0] and r1 == r2:
                        rhos = [1, 2]
                    else:
                        rhos = [2]
                    for rho in rhos:
                        ch.append((r1, r2, rho))
            opts.append(ch)
        for c in product(*opts):
            if any(c[j][2] == 1 and max(c[k][0], c[k][1]) > 1
                   for j in range(3) for k in range(3) if k != j):
                continue
            Ms = 2 * sum(x[0] + x[1] for x in c)
            rho = sum(x[2] for x in c)
            r2, r3 = 4 * A + rho, 8 * N + 2 * Ms
            val = r3 - 2 * r2
            if val > best:
                best, attained = val, {(r2, r3)}
            elif val == best:
                attained.add((r2, r3))
    check("r^3 - 2 r^2 <= 4 for every shape of a secant class, with "
          "equality only at (r^2, r^3) = (54, 112): the condition of "
          "prop:sexticcount(iii) is implied by chi <= -26",
          best == 4 and attained == {(54, 112)},
          "maximum %d attained at %s over 255 supports" % (best,
                                                          sorted(attained)))


# ------------------------------------------------------------------ (C,D)
def cubic_fields():
    out = [("Q(zeta_7)^+", [1, 1, -2, -1]), ("Q(zeta_9)^+", [1, 0, -3, 1])]
    seen = set()

    def disc(a, b, c):
        return a*a*b*b - 4*b**3 - 4*a**3*c - 27*c*c + 18*a*b*c

    def squarefree(n):
        d = 2
        while d * d <= n:
            if n % (d * d) == 0:
                return False
            d += 1
        return n > 1

    for a in range(-1, 2):
        for b in range(-7, 8):
            for c in range(-7, 8):
                D = disc(a, b, c)
                if D <= 0 or not squarefree(D) or D in seen:
                    continue
                # irreducible: no rational (hence integral) root dividing c
                if c == 0 or any(r**3 + a*r*r + b*r + c == 0
                                 for d in range(1, abs(c) + 1) if c % d == 0
                                 for r in (d, -d)):
                    continue
                seen.add(D)
                out.append(("disc %d" % D, [1, a, b, c]))
    return out


def gram(poly, qvec, Lb):
    return [[-(S.chi_formula(poly, qvec, [x + y for x, y in zip(Lb[i], Lb[j])])
               - S.chi_formula(poly, qvec, Lb[i])
               - S.chi_formula(poly, qvec, Lb[j])) / 16 for j in range(8)]
            for i in range(8)]


def in_lattice(Lb, co):
    """solve co = sum x_b Lb[b] and test x integral"""
    Mt = [[Lb[b][i] for b in range(8)] for i in range(8)]
    inv = S.matinv(Mt)
    x = [sum(inv[i][j] * co[j] for j in range(8)) for i in range(8)]
    return all(t.denominator == 1 for t in x)


def part_CD():
    random.seed(20260928)
    fl = cubic_fields()
    total_small, total_cases, allC = 0, 0, True
    gram_integral = True
    for name, poly in fl:
        rr = sorted(z.real for z in S.durand_kerner(poly))
        k = int(-min(rr)) + 1
        for qvec in ([1, 0, 0], [k, 1, 0]):
            qs = [sum(c * r**e for e, c in enumerate(qvec)) for r in rr]
            assert all(x > 0 for x in qs)
            monos, A = S.coefficient_matrix(poly, qvec)   # asserts 4th prime
            Lb = S.integral_lattice(A)
            S.check_chi_direct(poly, qvec, Lb, trials=2)
            G = gram(poly, qvec, Lb)
            gram_integral = gram_integral and all(
                x.denominator == 1 for row in G for x in row)
            small = S.short_vectors(G, 3)
            total_small += len(small)
            total_cases += 1
            if qvec == [1, 0, 0]:
                # Re exp(i theta) = (c_0, f, g, c_3) = (1, 0, -1, 0),
                # Im exp(i theta) = (0, 1, 0, -1)  (theta = sum theta_j)
                re = [Fr(1), 0, 0, 0, Fr(-1), 0, 0, 0]
                im = [0, Fr(1), 0, 0, 0, 0, 0, Fr(-1)]
                re = [Fr(x) for x in re]
                im = [Fr(x) for x in im]
                p = S.shape_prime(poly, qvec, 10**6)
                okc = True
                for cl in (re, im):
                    okc = okc and in_lattice(Lb, cl) \
                        and S.chi_formula(poly, qvec, cl) == -32 \
                        and S.shape_invariants(poly, qvec, cl, p)[0] == 2
                four = S.short_vectors(G, 4)
                vals = sorted(tuple(sum(Fr(x[b]) * Lb[b][i] for b in range(8))
                                    for i in range(8)) for x in four)
                want = sorted(tuple(s * t for t in cl)
                              for cl in (re, im) for s in (1, -1))
                okc = okc and vals == want
                allC = allC and okc
    check("for q = 1, Re exp(i theta) and Im exp(i theta) are integral "
          "points of S(0,1) with chi = -32 and N_w = 2, and with their "
          "negatives they are the only integral classes with -chi <= 32, "
          "for all %d fields" % len(fl), allC)
    check("for %d cubic fields and q in {1, k + alpha} (%d cases) no nonzero "
          "integral class of S(0,q) has -chi(v, v) <= 24; so every integral "
          "class meets the condition of prop:sexticcount(iii); the form -chi/8 is "
          "integral on each lattice"
          % (len(fl), total_cases), total_small == 0 and gram_integral,
          "lattices computed modulo three split primes, confirmed modulo a "
          "fourth and by the direct integral of v^dual v")


if __name__ == "__main__":
    print("(LVII) integral classes of the flat secant space of a sextic CM "
          "field")
    part_A()
    part_B()
    part_CD()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
