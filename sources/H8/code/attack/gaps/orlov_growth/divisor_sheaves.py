#!/usr/bin/env python3
"""
divisor_sheaves.py -- the arithmetic of prop:divisortemplate.

The Orlov template E = Phi(F x F^vee) attains the equality of
prop:orlovequality at n = 2, 3 with sheaves on theta divisors.  This script
checks, exactly, the computations behind the statement that this does not
continue:

  (A) part (i): for n = 5..24 and a grid of (a, b, d), an integer profile
      e_0..e_n with e_k = e_{n-k}, (e_0, e_1, e_2) = (1, 2n, n(n-1)),
      e_k >= beta_k and alternating sum chi(F,F), where chi(F,F) is computed
      by integrating ch(F)^vee ch(F) term by term; the profile beta_k of the
      connected sum of two n-tori has Euler characteristic 0 (n odd) and -2
      (n even); at n = 5 the profile is forced;
  (B) part (ii): with b, d, r symbols, S(x) T_b(x) (1 - e^{-bx}) = b x S(x)
      (so ch(G) = r i^*(S T_b) gives ch(i_* G) = rb v_theta), the coefficients
      b/2 and b^2/12 - d/6, and the rank-one defect b^2/24 + d/6 > 0; in
      degree six, e^{bx/2}(1 - e^{-bx}) has b^3/24 against -bd/6 for
      b v_theta;
  (C) part (ii), rank two on a theta divisor: c_2 = (d+1)/3 theta^2, the
      primitivity of theta^2/2 in a symplectic basis, and 2(d+1)/3 integral
      exactly for d = 2 mod 3;
  (D) part (iii): h^k(O_Theta) + h^{k-1}(O_Theta(Theta)) = beta_k, with both
      Euler characteristics compared with Riemann-Roch, and the Euler
      characteristic of beta with chi(i_*O, i_*O) = int (2 - e^t - e^-t);
      h^0(O_D(D)) = b^n + n - 1 > 2n for b >= 2;
  (E) part (iv): chi(Theta, End G) = r^2 (32 d^2 - 20 d - 1)/6 at n = 5 by
      two routes, chi(O_Theta) = 1, and 6 chi(End_0 G) >= 5;
  (F) the certificate at n = 3 of thm:twistedcert(ii): with x^2 = 1,
      x theta = 3, theta^2 = 6 on C^(2) and c_1 = (2k+1)x - k theta,
      Riemann-Roch gives ch(i_* L) = Theta - k(k+1) [pt].
"""
from fractions import Fraction as Fr
from itertools import combinations
from math import comb, factorial
import sympy as sp

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


def beta(n, k):
    if k == 0 or k == n:
        return 1
    if 0 < k < n:
        return 2 * comb(n, k)
    return 0


def gamma(n, k, a, b, d):
    """coefficient of theta^k/k! in a u + b v."""
    return a * (-d) ** (k // 2) if k % 2 == 0 else b * (-d) ** ((k - 1) // 2)


def chi_secant(n, a, b, d):
    """int_X ch^vee ch, with int theta^n = n!, as an exact integer."""
    s = Fr(0)
    for i in range(n + 1):
        j = n - i
        s += Fr((-1) ** i * gamma(n, i, a, b, d) * gamma(n, j, a, b, d),
                factorial(i) * factorial(j))
    s *= factorial(n)
    assert s.denominator == 1
    return int(s)


def chi_closed(n, a, b, d):
    if n % 2:
        return 0
    return (-1) ** (n // 2) * 2 ** (n - 1) * d ** (n // 2 - 1) * (a * a * d + b * b)


# --------------------------------------------------------------------- (A)
def part_A():
    print("  (A) the profile of part (i)")
    bad_closed, bad_prof, cases = [], [], 0
    for n in range(5, 25):
        for d in (1, 2, 3, 5, 6, 7, 10, 11):
            for a in range(0, 4):
                for b in range(-3, 4):
                    if a == 0 and b == 0:
                        continue
                    cases += 1
                    chi = chi_secant(n, a, b, d)
                    if chi != chi_closed(n, a, b, d):
                        bad_closed.append((n, a, b, d))
                    e = [beta(n, k) for k in range(n + 1)]
                    if n % 2 == 0:
                        c = abs(chi)
                        e[n // 2] += c + 2 * (-1) ** (n // 2)
                    ok = (e[:3] == [1, 2 * n, n * (n - 1)]
                          and all(e[k] == e[n - k] for k in range(n + 1))
                          and all(e[k] >= beta(n, k) for k in range(n + 1))
                          and sum((-1) ** k * e[k] for k in range(n + 1)) == chi)
                    if not ok:
                        bad_prof.append((n, a, b, d))
    check("chi(F,F) by term-by-term integration equals the closed form of "
          "prop:secantprofile", not bad_closed, "%d cases, n = 5..24" % cases)
    check("the profile of part (i) meets every condition, raising e_{n/2} "
          "by c + 2(-1)^{n/2} for even n", not bad_prof, "%d cases" % cases)
    ok = all(sum((-1) ** k * beta(n, k) for k in range(n + 1))
             == (0 if n % 2 else -2) for n in range(2, 60))
    check("the Betti numbers beta_k of T^n # T^n have Euler characteristic "
          "0 (n odd) and -2 (n even)", ok, "n = 2..59")
    free = list(range(3, 5 - 3 + 1))
    check("at n = 5 no index lies in [3, n-3], so the profile is forced to "
          "(1, 10, 20, 20, 10, 1)", free == [] and
          [beta(5, k) for k in range(6)] == [1, 10, 20, 20, 10, 1])
    ok = all(abs(chi_closed(n, a, b, d)) % 2 ** (n - 1) == 0
             and abs(chi_closed(n, a, b, d)) > 2
             for n in range(6, 25, 2) for d in (1, 2, 3) for a in range(0, 3)
             for b in range(-2, 3) if (a, b) != (0, 0))
    check("for even n >= 6 and integers (a, b) != 0, c = |chi| is a positive "
          "multiple of 2^{n-1}, so c > 2", ok)


# --------------------------------------------------------------------- (B)
x, b, d, r = sp.symbols('x b d r', positive=True)
N = 12


def S():
    return sum((-d) ** j * x ** (2 * j) / sp.factorial(2 * j + 1)
               for j in range(N // 2 + 1))


def ser(f, order=N):
    return sp.expand(sp.series(f, x, 0, order).removeO())


def part_B():
    print("  (B) the character of part (ii)")
    Tb = b * x / (1 - sp.exp(-b * x))
    lhs = ser(S() * Tb * (1 - sp.exp(-b * x)))
    rhs = ser(b * x * S())
    check("S(x) T_b(x) (1 - e^{-bx}) = b x S(x), so ch(G) = r i^*(S T_b) "
          "gives ch(i_*G) = rb v_theta", sp.simplify(lhs - rhs) == 0,
          "to order x^%d, b, d symbols" % (N - 1))
    st = ser(S() * Tb, 4)
    c1 = sp.simplify(st.coeff(x, 1) - b / 2)
    c2 = sp.simplify(st.coeff(x, 2) - (b ** 2 / 12 - d / 6))
    check("S T_b = 1 + (b/2) x + (b^2/12 - d/6) x^2 + O(x^3)",
          c1 == 0 and c2 == 0 and st.coeff(x, 0) == 1)
    defect = sp.simplify((b / 2) ** 2 / 2 - (b ** 2 / 12 - d / 6))
    check("rank one: c_1^2/2 - ch_2 = b^2/24 + d/6, positive for d >= 1",
          sp.simplify(defect - (b ** 2 / 24 + d / 6)) == 0)
    lb = ser(sp.exp(b * x / 2) * (1 - sp.exp(-b * x)), 5)
    check("degree six: e^{bx/2}(1 - e^{-bx}) has x^3 coefficient b^3/24, "
          "against -bd/6 in b v_theta (so b^2 = -4d)",
          sp.simplify(lb.coeff(x, 3) - b ** 3 / 24) == 0
          and sp.simplify(lb.coeff(x, 2)) == 0
          and sp.simplify(ser(b * x * S(), 5).coeff(x, 3) + b * d / 6) == 0)


# --------------------------------------------------------------------- (C)
def shuffle_sign(A, B):
    return (-1) ** sum(1 for s_ in A for t in B if s_ > t)


def theta_half_square(n):
    """coefficients of theta^2/2 in the exterior algebra of a symplectic
    lattice e_1..e_n, f_1..f_n, theta = sum e_i ^ f_i."""
    out = {}
    for i, j in combinations(range(n), 2):
        idx = sorted([i, n + i, j, n + j])
        # e_i f_i e_j f_j reordered to increasing index
        word = [i, n + i, j, n + j]
        sign = 1
        w = word[:]
        for p in range(len(w)):
            for q in range(len(w) - 1 - p):
                if w[q] > w[q + 1]:
                    w[q], w[q + 1] = w[q + 1], w[q]
                    sign = -sign
        out[tuple(idx)] = out.get(tuple(idx), 0) + sign
    return out


def part_C():
    print("  (C) rank two on a theta divisor")
    c1 = 1                                   # c_1 = theta
    ch2 = 2 * (sp.Rational(1, 12) - sp.Rational(1, 6) * d)
    c2 = sp.simplify(sp.Rational(c1 * c1, 2) - ch2)
    check("c_2 = c_1^2/2 - ch_2 = (d+1)/3 theta^2 for r = 2, b = 1",
          sp.simplify(c2 - (d + 1) / 3) == 0)
    coeffs = theta_half_square(5)
    check("theta^2/2 has every coefficient +-1 in a symplectic basis "
          "(n = 5), so it is integral and primitive",
          coeffs and all(abs(v) == 1 for v in coeffs.values()),
          "%d monomials" % len(coeffs))
    ok = all(((2 * (dd + 1)) % 3 == 0) == (dd % 3 == 2)
             for dd in range(1, 1001))
    check("2(d+1)/3 is an integer exactly for d = 2 mod 3", ok, "d = 1..1000")


# --------------------------------------------------------------------- (D)
def part_D():
    print("  (D) the Ext groups of part (iii)")
    ok_beta, ok_rr = True, True
    for n in range(2, 40):
        hO = [comb(n, k) for k in range(n)]            # h^k(O_Theta), k < n
        hN = [comb(n, k + 1) for k in range(n)]        # h^k(O_Theta(Theta))
        prof = []
        for k in range(n + 1):
            prof.append((hO[k] if k < n else 0) + (hN[k - 1] if k >= 1 else 0))
        if prof != [beta(n, k) for k in range(n + 1)]:
            ok_beta = False
        # Riemann-Roch: chi(O_Theta) = int (1 - e^-t), chi(O_Theta(Theta))
        # = int (e^t - 1), with int t^n/n! = 1
        if sum((-1) ** k * hO[k] for k in range(n)) != -(-1) ** n:
            ok_rr = False
        if sum((-1) ** k * hN[k] for k in range(n)) != 1:
            ok_rr = False
        # chi(i_*O, i_*O) = int (1 - e^t)(1 - e^-t) = -(1 + (-1)^n)
        if sum((-1) ** k * prof[k] for k in range(n + 1)) != -(1 + (-1) ** n):
            ok_rr = False
    check("h^k(O_Theta) + h^{k-1}(O_Theta(Theta)) = beta_k for every k",
          ok_beta, "n = 2..39")
    check("both Euler characteristics and chi(i_*O, i_*O) agree with "
          "Riemann-Roch", ok_rr, "n = 2..39")
    ok = all(bb ** n + n - 1 > 2 * n for n in range(2, 40) for bb in range(2, 8))
    check("for b >= 2, h^0(O_D(D)) = b^n + n - 1 > 2n", ok)


# --------------------------------------------------------------------- (E)
def part_E():
    print("  (E) part (iv) at n = 5")
    n = 5
    t = x
    T1 = t / (1 - sp.exp(-t))
    T1m = (-t) / (1 - sp.exp(t))
    # route 1: int_D ch(End G) td(D) = int_X r^2 S^2 T1(t) T1(-t) T1(t)^{-1} t
    f1 = ser(r ** 2 * S() ** 2 * T1 * T1m / T1 * t, n + 1)
    chi1 = sp.simplify(f1.coeff(x, n) * sp.factorial(n))
    # route 2: the closed integrand S^2 t^2/(e^t - 1)
    f2 = ser(r ** 2 * S() ** 2 * t ** 2 / (sp.exp(t) - 1), n + 1)
    chi2 = sp.simplify(f2.coeff(x, n) * sp.factorial(n))
    target = r ** 2 * (32 * d ** 2 - 20 * d - 1) / 6
    check("chi(Theta, End G) = r^2 (32 d^2 - 20 d - 1)/6 by both routes",
          sp.simplify(chi1 - target) == 0 and sp.simplify(chi2 - target) == 0)
    chiO = sp.simplify(ser(1 - sp.exp(-t), n + 1).coeff(x, n) * sp.factorial(n))
    check("chi(O_Theta) = int_X (1 - e^{-theta}) = 1 at n = 5", chiO == 1)
    # 32 d^2 - 20 d - 1 - 11 = 4 (d - 1)(8 d + 3) >= 0 for d >= 1
    fac = sp.expand(32 * d ** 2 - 20 * d - 1 - 11 - 4 * (d - 1) * (8 * d + 3)) == 0
    scan = all(rr * rr * (32 * dd * dd - 20 * dd - 1) - 6 >= 5
               for rr in range(1, 200) for dd in range(1, 400))
    check("32 d^2 - 20 d - 1 - 11 = 4 (d - 1)(8 d + 3), so "
          "6 chi(End_0 G) = r^2 (32 d^2 - 20 d - 1) - 6 >= 5", fac and scan,
          "factorisation with d a symbol; scan r < 200, d < 400")


# --------------------------------------------------------------------- (F)
def part_F():
    print("  (F) the certificate at n = 3")
    ok = True
    for k in range(1, 30):
        # on C^(2): x^2 = 1, x.th = 3, th^2 = 6; td = 1 - th/2 + [pt]
        l2 = (2 * k + 1) ** 2 - 2 * (2 * k + 1) * k * 3 + k * k * 6
        lth = (2 * k + 1) * 3 - k * 6
        deg2 = Fr(l2, 2) - Fr(lth, 2) + 1          # ch_2(L) - c_1 th/2 + 1
        # degree one: i_*(l - th/2) with i_*x = Th^2/2, i_*th = Th^2
        deg1 = Fr(2 * k + 1, 2) - k - Fr(1, 2)
        if deg2 != -k * (k + 1) or deg1 != 0:
            ok = False
    check("Riemann-Roch on C^(2) gives ch(i_*L) = Theta - k(k+1)[pt] for "
          "c_1 = (2k+1)x - k theta", ok, "k = 1..29")


if __name__ == "__main__":
    print("divisor_sheaves.py: the arithmetic of prop:divisortemplate")
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
