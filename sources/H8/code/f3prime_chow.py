#!/usr/bin/env python3
"""
f3prime_chow.py

Item (LXII) of the computations: the numbers behind prop:f3primefibration
and rem:f3primesharp, the reach of the arguments on zero-cycles for (F3').

Notation.  X_d^n is a smooth hypersurface of degree d in P^{n+1}, h its
hyperplane class.  By Griffiths, the primitive part of H^{p,n-p}(X_d^n) is
the graded piece R_t of the Jacobian ring
    R = C[x_0, ..., x_{n+1}] / (dF/dx_0, ..., dF/dx_{n+1}),
    t = t(p) = (n + 1 - p) d - (n + 2),
a complete intersection of n + 2 forms of degree d - 1, with Hilbert series
((1 - s^(d-1)) / (1 - s))^(n+2) and socle degree sigma = (n + 2)(d - 2).

What is checked:

  (A) the dimensions dim R_t, computed as coefficients of the polynomial
      (1 + s + ... + s^(d-2))^(n+2) and, independently, by
      inclusion-exclusion over the generators, agree for n <= 8,
      2 <= d <= 8 and every t; R is Gorenstein-symmetric,
      dim R_t = dim R_(sigma - t), with dim R = (d - 1)^(n+2);

  (B) for the smooth sextic fourfold X_6^4 the primitive Hodge numbers
      h^{4,0}, h^{3,1}, h^{2,2}_prim, h^{1,3}, h^{0,4} are
      (1, 426, 1751, 426, 1);

  (C) the Euler number of X_d^n from these Hodge numbers equals
      ((1 - d)^(n+2) - 1)/d + n + 2 and equals d times the coefficient of
      h^n in (1 + h)^(n+2) / (1 + d h), the top Chern class of the tangent
      bundle, for n <= 8 and 2 <= d <= 8; for X_6^4 it is 2610;

  (D) h^{4,0}(X_d^4) = dim R_(d-6) is 0, 0, 0, 1, 6 for d = 3, ..., 7, equal
      to h^0(P^5, O(d - 6)) by adjunction, K = O(d - 6), so that X_d^4 is
      Fano exactly for d <= 5;

  (E) for Y = X_6^4 in a hyperplane of P^6 and X = Bl_Y P^6, the blow-up
      formula h^{p,q}(X) = h^{p,q}(P^6) + h^{p-1,q-1}(Y) gives
      h^{6,0} = 0, h^{5,1} = 1, h^{4,2} = 426, h^{3,3} = 1753 and
      h^{p,0}(X) = 0 for p > 0, Hodge symmetry, only even cohomology, and a
      total of 2617 = e(P^6) + e(Y) = e(P^6) + e(E) - e(Y), E the
      exceptional P^1-bundle over Y;

  (F) the retrieval identity of rem:f3primesharp: in the model
      H^*(E) = H^*(Y)[xi] / (xi^2 + c_1 xi + c_2) of a P^1-bundle over a
      base with H^*(Y) = Q[y]/(y^5) and random rational c_1, c_2, with
      rho_* the coefficient of xi and j^* j_* = multiplication by
      c_1(N_{E/X}) = -xi, the class -rho_* j^* j_* rho^* a equals a for
      every a, and rho_* rho^* a = 0;

  (G) the degree bookkeeping: a class of degree 2p on an n-fold needs an
      input beyond prop:f3prime(iv) and hard Lefschetz only when
      2 <= p <= n/2; for n <= 5 that is p = 2 alone; on the blow-up of a
      sixfold along a smooth centre C of codimension c >= 2 the summands
      j_*(xi^a rho^* H^(2p-2-2a)(C)), 0 <= a <= c - 2, of H^(2p) need such
      an input exactly for (p, dim C, degree on C) = (3, 4, 4); and in the
      decomposition a = Phi_* j^* a + i_* Psi_* a of a uniruled fivefold
      (Z' and D' fourfolds, Psi_* lowering the degree by two) the only
      input is degree 4 on the fourfold Z'.

Everything is exact.  Standard library only.

Run:  python3 f3prime_chow.py
"""
import random
from fractions import Fraction as Fr
from math import comb

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("         " + detail)


# ------------------------------------------------------------ Jacobian ring
def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def jacobian_series(n, d):
    """Coefficients of (1 + s + ... + s^(d-2))^(n+2)."""
    base = [1] * (d - 1)
    out = [1]
    for _ in range(n + 2):
        out = poly_mul(out, base)
    return out


def dimR_series(n, d, t):
    c = jacobian_series(n, d)
    return c[t] if 0 <= t < len(c) else 0


def dimR_ie(n, d, t):
    """Inclusion-exclusion: n + 2 generators of degree d - 1 in n + 2
    variables, a regular sequence."""
    if t < 0:
        return 0
    N = n + 2
    s = 0
    for j in range(N + 1):
        u = t - j * (d - 1)
        if u < 0:
            break
        s += (-1) ** j * comb(N, j) * comb(u + N - 1, N - 1)
    return s


def prim_hodge(n, d):
    """Primitive h^{p, n-p}, p = n, ..., 0 (Griffiths)."""
    sig = (n + 2) * (d - 2)
    out = []
    for p in range(n, -1, -1):
        t = (n + 1 - p) * d - (n + 2)
        out.append(dimR_series(n, d, t) if 0 <= t <= sig else 0)
    return out


def hodge_diamond(n, d):
    """Full Hodge numbers h[(p, q)] of X_d^n."""
    h = {}
    pr = prim_hodge(n, d)
    for p in range(n + 1):
        for q in range(n + 1):
            v = 1 if (p == q) else 0
            if p + q == n:
                v += pr[n - p]
            h[(p, q)] = v
    return h


def euler_from_hodge(h):
    return sum((-1) ** (p + q) * v for (p, q), v in h.items())


def euler_formula(n, d):
    return Fr((1 - d) ** (n + 2) - 1, d) + n + 2


def euler_chern(n, d):
    """d times the coefficient of h^n in (1 + h)^(n+2) / (1 + d h)."""
    num = [comb(n + 2, k) for k in range(n + 1)]
    inv = [(-d) ** k for k in range(n + 1)]
    coef = sum(num[k] * inv[n - k] for k in range(n + 1))
    return d * coef


def part_A():
    ok = True
    sym = True
    tot = True
    for n in range(0, 9):
        for d in range(2, 9):
            sig = (n + 2) * (d - 2)
            for t in range(0, sig + 3):
                if dimR_series(n, d, t) != dimR_ie(n, d, t):
                    ok = False
            for t in range(0, sig + 1):
                if dimR_series(n, d, t) != dimR_series(n, d, sig - t):
                    sym = False
            if sum(jacobian_series(n, d)) != (d - 1) ** (n + 2):
                tot = False
    check("dim R_t by the Hilbert series and by inclusion-exclusion agree "
          "for n <= 8, 2 <= d <= 8 and every t", ok)
    check("R is Gorenstein-symmetric about sigma = (n+2)(d-2) and "
          "dim R = (d-1)^(n+2) in the same range", sym and tot)


def part_B():
    pr = prim_hodge(4, 6)
    check("sextic fourfold: primitive (h^{4,0}, h^{3,1}, h^{2,2}_prim, "
          "h^{1,3}, h^{0,4}) = (1, 426, 1751, 426, 1)",
          pr == [1, 426, 1751, 426, 1], "computed %s" % (pr,))


def part_C():
    ok = True
    for n in range(0, 9):
        for d in range(2, 9):
            e1 = euler_from_hodge(hodge_diamond(n, d))
            e2 = euler_formula(n, d)
            e3 = euler_chern(n, d)
            if not (e1 == e2 == e3):
                ok = False
    check("Euler number from the Hodge numbers = ((1-d)^(n+2)-1)/d + n + 2 "
          "= top Chern class, for n <= 8, 2 <= d <= 8", ok)
    e = euler_from_hodge(hodge_diamond(4, 6))
    check("the smooth sextic fourfold has Euler number 2610 and b_4 = 2606",
          e == 2610 == euler_formula(4, 6)
          and sum(hodge_diamond(4, 6)[(p, 4 - p)] for p in range(5)) == 2606)


def part_D():
    h40 = [prim_hodge(4, d)[0] for d in range(3, 8)]
    adj = [comb(d - 6 + 5, 5) if d >= 6 else 0 for d in range(3, 8)]
    check("h^{4,0} of hypersurface fourfolds of degree 3..7 is "
          "(0, 0, 0, 1, 6) = h^0(P^5, O(d-6))", h40 == [0, 0, 0, 1, 6] == adj,
          "computed %s, adjunction %s" % (h40, adj))
    fano = [d for d in range(1, 12) if 6 - d > 0]
    check("K = O(d-6) on a hypersurface fourfold, so it is Fano exactly for "
          "d <= 5, and h^{4,0} = 0 exactly for d <= 5 (d <= 11)",
          fano == [1, 2, 3, 4, 5]
          and [d for d in range(2, 12) if prim_hodge(4, d)[0] == 0]
          == [2, 3, 4, 5])


def part_E():
    hy = hodge_diamond(4, 6)
    hx = {}
    for p in range(7):
        for q in range(7):
            v = 1 if p == q else 0
            v += hy.get((p - 1, q - 1), 0)
            hx[(p, q)] = v
    mid = [hx[(6, 0)], hx[(5, 1)], hx[(4, 2)], hx[(3, 3)]]
    check("Bl_Y P^6, Y a smooth sextic fourfold in a hyperplane: "
          "(h^{6,0}, h^{5,1}, h^{4,2}, h^{3,3}) = (0, 1, 426, 1753)",
          mid == [0, 1, 426, 1753], "computed %s" % (mid,))
    sym = all(hx[(p, q)] == hx[(q, p)] == hx[(6 - p, 6 - q)]
              for p in range(7) for q in range(7))
    odd = all(v == 0 for (p, q), v in hx.items() if (p + q) % 2)
    p0 = all(hx[(p, 0)] == 0 for p in range(1, 7))
    check("Bl_Y P^6 has Hodge symmetry, only even cohomology and "
          "h^{p,0} = 0 for p > 0", sym and odd and p0)
    tot = sum(hx.values())
    eY = euler_from_hodge(hy)
    check("Bl_Y P^6: total Betti number 2617 = e(P^6) + e(Y) "
          "= e(P^6) + e(E) - e(Y), e(E) = 2 e(Y)",
          tot == 2617 == 7 + eY == 7 + 2 * eY - eY)


# ------------------------------------------------- retrieval identity (F)
def part_F():
    rnd = random.Random(19)
    top = 4                                   # H^*(Y) = Q[y]/(y^5)

    def trunc(c):
        return [c[i] if i < len(c) else Fr(0) for i in range(top + 1)]

    def ymul(a, b):
        out = [Fr(0)] * (top + 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                if i + j <= top:
                    out[i + j] += x * y
        return out

    ok = True
    for _ in range(20):
        c1 = trunc([Fr(0), Fr(rnd.randint(-9, 9), rnd.randint(1, 5))])
        c2 = trunc([Fr(0), Fr(0), Fr(rnd.randint(-9, 9), rnd.randint(1, 5))])
        # an element of H^*(E) is (u, v) = u + v xi, u, v in H^*(Y);
        # xi^2 = -c1 xi - c2.

        def mul_xi(el):
            u, v = el
            return ([-x for x in ymul(v, c2)],
                    [a - b for a, b in zip(u, ymul(v, c1))])

        for k in range(top + 1):
            a = trunc([Fr(0)] * k + [Fr(rnd.randint(-9, 9) or 1)])
            pull = (a, [Fr(0)] * (top + 1))            # rho^* a
            jj = mul_xi(pull)                           # xi rho^* a
            jj = ([-x for x in jj[0]], [-x for x in jj[1]])   # j^* j_* = -xi
            back = [-x for x in jj[1]]                  # -rho_*(...)
            if back != a or pull[1] != [Fr(0)] * (top + 1):
                ok = False
        # the relation itself: xi^2 = -c1 xi - c2, so rho_* xi^2 = -c1
        sq = mul_xi(mul_xi(([Fr(1)] + [Fr(0)] * top, [Fr(0)] * (top + 1))))
        if sq[1] != [-x for x in c1] or sq[0] != [-x for x in c2]:
            ok = False
    check("-rho_* j^* j_* rho^* a = a and rho_* rho^* a = 0 on a P^1-bundle "
          "with N_{E/X} = O_E(-1) (twenty random bundles, all degrees)", ok)


# ------------------------------------------------ degree bookkeeping (G)
def needs_input(n, p):
    """True when a Hodge class of degree 2p on an n-fold is not settled by
    prop:f3prime(iv) (p in {0, 1, n-1, n}) or by hard Lefschetz from a
    lower degree (p > n/2)."""
    return 2 <= p and 2 * p <= n


def part_G():
    small = {n: [p for p in range(n + 1) if needs_input(n, p)]
             for n in range(0, 6)}
    check("for n <= 5 only degree four needs an input "
          "(and degree 2n - 4 follows by hard Lefschetz)",
          all(small[n] == ([2] if n >= 4 else []) for n in range(6)),
          "degrees 2p needing input: %s" % (small,))
    needed = set()
    for p in range(0, 4):                        # p <= n/2 = 3 suffices
        for c in range(2, 7):
            dimC = 6 - c
            for a in range(0, c - 1):
                q = p - 1 - a                    # class of degree 2q on C
                if 0 <= q <= dimC and needs_input(dimC, q):
                    needed.add((p, dimC, 2 * q))
    check("rational sixfold: the blow-up summands of H^(2p), p <= 3, need an "
          "input only for (p, dim C, degree) = (3, 4, 4)",
          needed == {(3, 4, 4)}, "needed %s" % (sorted(needed),))
    # uniruled fivefold: a = Phi_* j^* a + i_* Psi_* a, Z' and D' fourfolds
    inputs = set()
    for p in range(0, 6):
        if not needs_input(5, p):
            continue
        if needs_input(4, p):
            inputs.add(("Z'", 2 * p))
        if needs_input(4, p - 1):
            inputs.add(("D'", 2 * p - 2))
    check("uniruled fivefold: the decomposition needs only degree 4 on the "
          "fourfold Z'", inputs == {("Z'", 4)}, "inputs %s" % (sorted(inputs),))


if __name__ == "__main__":
    print("(LXII) the reach of the zero-cycle arguments for (F3')")
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
