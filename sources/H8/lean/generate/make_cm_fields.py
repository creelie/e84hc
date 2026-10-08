#!/usr/bin/env python3
"""
make_cm_fields.py

Writes the data of item (XXXVI), Weil classes of CM fields of degree four
and six, for HodgeObstruction.lean.  The model is that of code/cm_fields.py:
F = Q(zeta_r) = Q[x]/(Phi_r), the power basis omega_j = zeta^j, the
trace-dual basis omega*_j, and the eigenvectors u_{i,sigma} of F e_i with
coordinates sigma(omega*_j).  For each case it records r, the coefficients
of Phi_r below the leading one, an integer D and eta_j = D omega*_j in the
power basis, the CM type and n.  For part (B) it records integers s and
c_ab (a <= b) with

    s w_K(f) = sum_{a <= b} c_ab w(omega_a) w(omega_b),   f = 1, i,

as an identity of coefficients on the products alpha_sigma alpha_tau,
sigma < tau, where w(f) = sum_sigma sigma(f) alpha_sigma and
w_K(f) = sigma_1(f) alpha_1 alpha_5 + sigma_3(f) alpha_3 alpha_7.

Run from the repository root:  python3 lean/generate/make_cm_fields.py > out
"""
import os
import sys
from fractions import Fraction as F
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
import cm_fields as C  # noqa: E402

CASES = [
    (5, (1, 2), 2),
    (5, (1, 2), 3),
    (8, (1, 3), 2),
    (7, (1, 2, 3), 2),
    (7, (1, 2, 3), 1),
    (9, (1, 2, 4), 2),
]

POLY = {5: [1, 1, 1, 1], 7: [1, 1, 1, 1, 1, 1], 8: [1, 0, 0, 0], 9: [1, 0, 0, 1, 0, 0]}


def lcm(a, b):
    return a * b // gcd(a, b)


def field_data(r):
    Fl = C.NumberField(POLY[r])
    d = Fl.d
    omega = [Fl.power(Fl.x, j) for j in range(d)]
    T = [[Fl.trace(Fl.mul(omega[j], omega[l])) for l in range(d)] for j in range(d)]
    Tinv = C.inverse_q(T)
    ostar = []
    for l in range(d):
        e = Fl.zero
        for j in range(d):
            e = Fl.add(e, Fl.scal(Tinv[j][l], omega[j]))
        ostar.append(e)
    D = 1
    for e in ostar:
        for x in e:
            D = lcm(D, F(x).denominator)
    eta = [[int(x * D) for x in e] for e in ostar]
    return Fl, omega, D, eta


def solve_q(rows, rhs):
    """a rational solution of rows . c = rhs (consistent system)"""
    m, n = len(rows), len(rows[0])
    A = [[F(v) for v in r] + [F(b)] for r, b in zip(rows, rhs)]
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    assert all(A[i][n] == 0 for i in range(r, m))
    sol = [F(0)] * n
    for i, c in enumerate(piv):
        sol[c] = A[i][n]
    return sol


def part_b():
    Fl, omega, D, eta = field_data(8)
    auts = {k: (lambda a, k=k: Fl.embed_poly(a, k)) for k in (1, 3, 5, 7)}
    i_el = Fl.power(Fl.x, 2)
    pairs = [(s, t) for s in (1, 3, 5, 7) for t in (1, 3, 5, 7) if s < t]
    ab = [(a, b) for a in range(4) for b in range(a, 4)]
    out = []
    for f in (Fl.one, i_el):
        rows, rhs = [], []
        for (s, t) in pairs:
            coef = []
            for (a, b) in ab:
                c = Fl.add(Fl.mul(auts[s](omega[a]), auts[t](omega[b])),
                           Fl.mul(auts[t](omega[a]), auts[s](omega[b])))
                coef.append(c)
            target = auts[1](f) if (s, t) == (1, 5) else auts[3](f) if (s, t) == (3, 7) else Fl.zero
            for comp in range(4):
                rows.append([c[comp] for c in coef])
                rhs.append(target[comp])
        sol = solve_q(rows, rhs)
        den = 1
        for x in sol:
            den = lcm(den, x.denominator)
        out.append((den, [int(x * den) for x in sol]))
    return out


def main():
    print("/-- the cases of (C): `(r, Phi_r below x^d, D, eta = D omega*, CM type, n)`. -/")
    print("def cfCases : List (Nat × List Int × Nat × List (List Int) × List Nat × Nat) := [")
    rows = []
    for (r, phi, n) in CASES:
        Fl, omega, D, eta = field_data(r)
        rows.append("  (%d, %s, %d, %s, %s, %d)" % (
            r, "[" + ", ".join(str(x) for x in POLY[r]) + "]", D,
            "[" + ", ".join("[" + ", ".join(str(x) for x in e) + "]" for e in eta) + "]",
            "[" + ", ".join(str(k) for k in phi) + "]", n))
    print(",\n".join(rows) + "]")
    cert = part_b()
    print("/-- (B): `(s, c_ab)` for `f = 1` and `f = i`, `(a, b)` in the order")
    print("`(0,0), (0,1), ..., (3,3)`. -/")
    print("def cfWeilK : List (Nat × List Int) := [%s]" % ", ".join(
        "(%d, [%s])" % (s, ", ".join(str(x) for x in c)) for s, c in cert))


if __name__ == "__main__":
    main()
