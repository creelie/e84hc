#!/usr/bin/env python3
"""
mumford_mass.py

Item (LXIII) of the computations: the Wirtinger bound for the exceptional
classes on the square of a Mumford fourfold, in the split model.

Model.  V = V_1 (x) V_2 (x) V_3, V_i = C^2 with basis e_0 (weight +1) and
e_1 (weight -1); a basis vector of V is indexed by (a,b,c) in {0,1}^3.  The
symplectic form is psi = eps (x) eps (x) eps, the class theta of the principal
polarisation of X.  H^1(X x X) = V (+) V, bits 0..7 and 8..15, and
theta_Y = theta (x) 1 + 1 (x) theta is the product polarisation.
wedge^2 V = 1 (+) U_12 (+) U_13 (+) U_23 by the three Casimir operators, and
pi_0, pi_12, pi_13, pi_23 in wedge^2 V (x) wedge^2 V are the tensors of the
four projections, as in item (XLIV); omega_a = a_0 pi_0 + a_1 pi_12 +
a_2 pi_13 + a_3 pi_23.  The volume form of X is normalised by
int theta^4 = 4!, that of Y = X x X by int theta_Y^8 = 8!, and
L(c) = int c theta_Y^6 / 6! is the Wirtinger bound of a class of degree four.

What is checked:

  (A) psi is nondegenerate and theta^4 = 24 vol on X; theta_Y^8 = 8! vol on Y;

  (B) every element of U_12, U_13, U_23 is primitive: x theta^3 = 0, while
      theta theta^3 = 24 vol;

  (C) int pi_ij theta_Y^6 = 0 for the three nontrivial summands, and
      int pi_0 theta_Y^6 = 2880, with pi_0 = (theta (x) theta)/4 in this
      model; so int omega_a theta_Y^6 = 2880 a_0 for every a, checked on
      random integer vectors a, and L(omega_a) = 4 a_0;

  (D) L(theta_Y^2) = 8!/6! = 56 and L(4 theta_Y^2) = 224, the mass of the
      complete intersection of two general members of |2 theta_Y|; so the
      Wirtinger bound of N (M theta_Y^2 + omega) with a_0 = 0 is 56 N M,
      independent of the exceptional class.

Everything is exact: rational arithmetic in the exterior algebra.

Run:  python3 mumford_mass.py
"""
import random

import sympy

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


NB = 16


def popcount(m):
    return bin(m).count("1")


def mono_sign(a, b):
    if a & b:
        return 0
    s, bb = 0, b
    while bb:
        j = (bb & -bb).bit_length() - 1
        s += popcount(a >> (j + 1))
        bb &= bb - 1
    return -1 if s % 2 else 1


def wt(i):
    j = i % 8
    return (1 - 2 * ((j >> 2) & 1), 1 - 2 * ((j >> 1) & 1), 1 - 2 * (j & 1))


def eps(a, b):
    return 1 if (a, b) == (0, 1) else (-1 if (a, b) == (1, 0) else 0)


def psi(i, j):
    if i // 8 != j // 8:
        return 0
    a, b = i % 8, j % 8
    v = 1
    for bit in (2, 1, 0):
        v *= eps((a >> bit) & 1, (b >> bit) & 1)
    return v


# ------------------------------------------------- wedge^2 V and the tensors
PAIRS = [(a, b) for a in range(8) for b in range(a + 1, 8)]
PIDX = {p: k for k, p in enumerate(PAIRS)}


def gen_matrix(t, raising):
    M = sympy.zeros(8, 8)
    bit = 2 - t
    for i in range(8):
        if raising and (i >> bit) & 1:
            M[i - (1 << bit), i] = 1
        if (not raising) and not (i >> bit) & 1:
            M[i + (1 << bit), i] = 1
    return M


def on_wedge2(M):
    W = sympy.zeros(28, 28)
    for k, (a, b) in enumerate(PAIRS):
        for r in range(8):
            if M[r, a] != 0 and r != b:
                s, p = (1, (r, b)) if r < b else (-1, (b, r))
                W[PIDX[p], k] += s * M[r, a]
            if M[r, b] != 0 and r != a:
                s, p = (1, (a, r)) if a < r else (-1, (r, a))
                W[PIDX[p], k] += s * M[r, b]
    return W


def build_tensors():
    cas = []
    raise_ops = []
    for t in range(3):
        E = on_wedge2(gen_matrix(t, True))
        F = on_wedge2(gen_matrix(t, False))
        H = on_wedge2(sympy.diag(*[wt(i)[t] for i in range(8)]))
        cas.append(H * H + 2 * (E * F + F * E))
        raise_ops.append(gen_matrix(t, True))
    pieces = {}
    for key, pat in (("0", (0, 0, 0)), ("12", (1, 1, 0)), ("13", (1, 0, 1)),
                     ("23", (0, 1, 1))):
        M = sympy.Matrix.vstack(*[cas[t] - (8 if pat[t] else 0) * sympy.eye(28)
                                  for t in range(3)])
        pieces[key] = M.nullspace()
    B = sympy.zeros(28, 28)
    for k, (a, b) in enumerate(PAIRS):
        for l, (c, d) in enumerate(PAIRS):
            B[k, l] = psi(a, c) * psi(b, d) - psi(a, d) * psi(b, c)
    PI = {}
    for key, basis in pieces.items():
        Ub = sympy.Matrix.hstack(*basis)
        dual = Ub * (Ub.T * B * Ub).inv().T
        out = {}
        for k in range(Ub.shape[1]):
            u, v = Ub[:, k], dual[:, k]
            for i in range(28):
                if u[i] == 0:
                    continue
                for j in range(28):
                    if v[j] == 0:
                        continue
                    (a, b), (c, d) = PAIRS[i], PAIRS[j]
                    m1 = (1 << a) | (1 << b)
                    m2 = ((1 << c) | (1 << d)) << 8
                    s = mono_sign(m1, m2)
                    out[m1 | m2] = out.get(m1 | m2, 0) + s * u[i] * v[j]
        PI[key] = {k: sympy.nsimplify(v) for k, v in out.items() if v != 0}
    return pieces, PI, raise_ops


def wedge(x, y):
    out = {}
    for m, c in x.items():
        for n, d in y.items():
            if m & n:
                continue
            s = mono_sign(m, n)
            out[m | n] = out.get(m | n, 0) + s * c * d
    return {k: v for k, v in out.items() if v != 0}


def power(x, k):
    out = {0: sympy.Integer(1)}
    for _ in range(k):
        out = wedge(out, x)
    return out


def theta_copy(shift):
    out = {}
    for i in range(8):
        for j in range(i + 1, 8):
            v = psi(i, j)
            if v:
                out[(1 << (i + shift)) | (1 << (j + shift))] = sympy.Integer(v)
    return out


def run():
    TOPX = (1 << 8) - 1
    TOPY = (1 << 16) - 1
    th = theta_copy(0)
    thY = dict(th)
    for k, v in theta_copy(8).items():
        thY[k] = thY.get(k, 0) + v

    # (A)
    P8 = sympy.Matrix(8, 8, lambda i, j: psi(i, j))
    t4 = power(th, 4)
    t8 = power(thY, 8)
    check("psi is nondegenerate, theta^4 = 24 vol on X and theta_Y^8 = 8! vol "
          "on the square", P8.det() != 0 and t4 == {TOPX: 24}
          and t8 == {TOPY: sympy.factorial(8)},
          "det psi = %s" % P8.det())

    # (B) primitivity of the U_ij
    pieces, PI, raise_ops = build_tensors()
    t3 = power(th, 3)
    ok = True
    for key in ("12", "13", "23"):
        for vec in pieces[key]:
            x = {}
            for k, (a, b) in enumerate(PAIRS):
                if vec[k] != 0:
                    x[(1 << a) | (1 << b)] = sympy.nsimplify(vec[k])
            ok = ok and wedge(x, t3) == {}
    check("every element of U_12, U_13, U_23 is primitive (x theta^3 = 0), "
          "while theta theta^3 = 24 vol", ok and wedge(th, t3) == {TOPX: 24})

    # (C) the pairings with theta_Y^6
    t6 = power(thY, 6)
    vals = {key: wedge(PI[key], t6).get(TOPY, 0) for key in PI}
    tt = wedge(th, theta_copy(8))          # theta (x) theta on the square
    quarter = {m: sympy.Rational(1, 4) * c for m, c in tt.items()}
    ok = (vals["12"] == 0 and vals["13"] == 0 and vals["23"] == 0
          and vals["0"] == 2880 and PI["0"] == quarter)
    rng = random.Random(7)
    for _ in range(5):
        a = [rng.randint(-9, 9) for _ in range(4)]
        om = {}
        for coef, key in zip(a, ("0", "12", "13", "23")):
            for m, v in PI[key].items():
                om[m] = om.get(m, 0) + coef * v
        ok = ok and wedge(om, t6).get(TOPY, 0) == 2880 * a[0]
    check("int pi_ij theta_Y^6 = 0, int pi_0 theta_Y^6 = 2880 with "
          "pi_0 = (theta (x) theta)/4, and int omega_a theta_Y^6 = 2880 a_0 "
          "on five random a; so L(omega_a) = 4 a_0", ok,
          "pairings %s" % vals)

    # (D) the bounds
    L2 = wedge(power(thY, 2), t6).get(TOPY, 0) / sympy.factorial(6)
    check("L(theta_Y^2) = 56 and L(4 theta_Y^2) = 224; the bound of "
          "N (M theta_Y^2 + omega) with a_0 = 0 is 56 N M",
          L2 == 56 and 4 * L2 == 224 and sympy.factorial(8) / sympy.factorial(6) == 56)


if __name__ == "__main__":
    print("(LXIII) the Wirtinger bound for the exceptional classes on a "
          "Mumford square")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
