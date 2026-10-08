#!/usr/bin/env python3
"""
twistor_locus.py

Item (XLVII) of COMPUTATIONS.md: the finite computations behind the
description of the Hodge locus of an exceptional class of a Mumford square
among all complex tori, and behind the statement that no twistor line through
a member of the Mumford family keeps the class of Hodge type.

Model.  As in items (XLIII) to (XLVI): V = V_1 (x) V_2 (x) V_3 over C, with
basis indexed by (a,b,c) in {0,1}^3 and weight (1-2a, 1-2b, 1-2c), and
psi = eps (x) eps (x) eps.  The real form of the Mumford group has a compact
factor at the first two embeddings and SL_2(R) at the third, so V_R is cut
out by the real structure s = s_1 (x) s_2 (x) s_3 with s_1, s_2 quaternionic
(x -> S conj(x), S = [[0,-1],[1,0]]) and s_3 real (x -> conj(x)).
A complex structure J on V_R in the real points of the group is
J_3 = 1 (x) 1 (x) j_3 with j_3 = [[0,-1],[1,0]] (a member of the Mumford
family) or J_1 = j_1 (x) 1 (x) 1 with j_1 = diag(i, -i), a unit quaternion of
the first, compact, factor (a point of a twistor sphere).  Everything is
exact: Gaussian integers, integer characteristic polynomials, and exact
ranks over Q.

What is checked:

  (A) s is a real structure (s^2 = 1), V_R has real dimension 8, and psi is
      real and alternating on V_R;

  (B) J_3, J_1 and J_2 = 1 (x) j_1 (x) 1 preserve V_R and square to -1, and
      the symmetric forms psi(x, J y) on V_R have signature (0,8) for J_3,
      a polarisation up to sign, and (4,4) for J_1 and J_2; the unit
      quaternion k = s_1 (x) 1 (x) 1, which anticommutes with J_1, preserves
      V_R and psi and carries psi(x, J_1 y) to its negative, so psi (x) S is
      congruent to its negative, hence indefinite, for every nonzero real
      symmetric 2 x 2 matrix S at J_1, which covers every class of degree
      two invariant under the group on V (+) V;

  (C) at the complex structure of J_1, whose (1,0)-part is spanned by the
      vectors of first weight +1, every monomial of the four tensors pi has
      type (2,2), and the annihilator of omega_a, a = (3,5,-7,11), in
      H^1(T) = H^{0,1} (x) T of the square (dimension 64) is one
      dimensional, spanned by the lowering derivation of the first factor on
      both copies; at the complex structure of J_3 it is spanned by the
      lowering derivation of the third factor, as in item (XLIV);

  (D) the exchange of the first and third factors carries pi_12 to pi_23
      and fixes pi_0 and pi_13, so the computation at J_1 is the one at J_3
      for the class with a_1 and a_3 exchanged, again exceptional.

Run:  python3 twistor_locus.py
"""
import itertools
import os
import sys

import sympy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mumford_rigidity as MR  # noqa: E402
from mumford_rigidity import wt, mono_sign, popcount, NB  # noqa: E402

PASS, FAIL = [], []
I = sympy.I


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


S = sympy.Matrix([[0, -1], [1, 0]])
E2 = sympy.eye(2)


def kron3(a, b, c):
    return sympy.kronecker_product(sympy.kronecker_product(a, b), c)


def signature(G):
    """signature of a real symmetric integer matrix, from its characteristic
    polynomial: all roots are real, so Descartes' rule counts them"""
    x = sympy.symbols("x")
    p = sympy.Poly(G.charpoly(x).as_expr(), x)
    coeffs = [c for c in p.all_coeffs()]
    zero = 0
    while coeffs and coeffs[-1] == 0:
        coeffs.pop()
        zero += 1

    def changes(cs):
        cs = [c for c in cs if c != 0]
        return sum(1 for u, v in zip(cs, cs[1:]) if (u > 0) != (v > 0))
    pos = changes(coeffs)
    n = len(coeffs) - 1
    neg = changes([c * (-1) ** (n - k) for k, c in enumerate(coeffs)])
    return pos, neg, zero


def real_basis(M):
    """an R-basis of {x : M conj(x) = x}, as columns with Gaussian integer
    entries"""
    cols = []
    for k in range(8):
        y = sympy.zeros(8, 1)
        y[k] = 1
        for v in (y + M * y.conjugate(), I * y + M * (I * y).conjugate()):
            cols.append(sympy.expand(v))
    chosen, rows = [], []
    for v in cols:
        cand = rows + [[sympy.re(z) for z in v] + [sympy.im(z) for z in v]]
        if sympy.Matrix(cand).rank() > len(rows):
            rows = cand
            chosen.append(v)
        if len(chosen) == 8:
            break
    return sympy.Matrix.hstack(*chosen)


def run():
    M = kron3(S, S, E2)
    psi = kron3(S, S, S)

    # (A)
    real_structure = (M * M.conjugate()).expand() == sympy.eye(8)
    VR = real_basis(M)
    P = (VR.T * psi * VR).expand()
    check("s = s_1 (x) s_2 (x) s_3 is a real structure, V_R has real "
          "dimension 8, and psi is real and alternating on V_R",
          real_structure and VR.shape[1] == 8
          and all(sympy.im(z) == 0 for z in P) and P == -P.T)

    # (B)
    j3 = sympy.Matrix([[0, -1], [1, 0]])
    j1 = sympy.Matrix([[I, 0], [0, -I]])
    Js = {"J_3": kron3(E2, E2, j3), "J_1": kron3(j1, E2, E2),
          "J_2": kron3(E2, j1, E2)}
    sig, ok = {}, True
    for name, J in Js.items():
        pres = (J * M - M * J.conjugate()).expand() == sympy.zeros(8, 8)
        sq = (J * J).expand() == -sympy.eye(8)
        G = (VR.T * psi * J * VR).expand()
        real = all(sympy.im(z) == 0 for z in G)
        G = G.applyfunc(sympy.re)
        sym = G == G.T
        sig[name] = signature(G)
        ok = ok and pres and sq and real and sym
    check("J_3, J_1, J_2 preserve V_R and square to -1; psi(x, Jy) is real "
          "symmetric of signature (0,8) for J_3 and (4,4) for J_1 and J_2",
          ok and sig["J_3"] == (0, 8, 0) and sig["J_1"] == (4, 4, 0)
          and sig["J_2"] == (4, 4, 0), "signatures %s" % sig)
    G1 = (VR.T * psi * Js["J_1"] * VR).expand().applyfunc(sympy.re)
    # k = S (x) 1 (x) 1 is the unit quaternion of the first factor that
    # anticommutes with j_1: it preserves V_R and psi, and carries
    # psi(x, J_1 y) to its negative, so T (x) G1 is congruent to its
    # negative for every real symmetric T, and indefinite when T != 0
    k = kron3(S, E2, E2)
    zero8 = sympy.zeros(8, 8)
    k_real = (k * M - M * k.conjugate()).expand() == zero8
    k_sp = (k.T * psi * k).expand() == psi
    k_anti = (k * Js["J_1"] + Js["J_1"] * k).expand() == zero8
    Gk = (VR.T * k.T * psi * Js["J_1"] * k * VR).expand()
    k_neg = (all(sympy.im(z) == 0 for z in Gk)
             and Gk.applyfunc(sympy.re) == -G1)
    tests = [sympy.Matrix([[1, 0], [0, 0]]), sympy.Matrix([[0, 0], [0, 1]]),
             sympy.Matrix([[0, 1], [1, 0]]), sympy.eye(2),
             sympy.Matrix([[2, 1], [1, 3]]), sympy.Matrix([[5, -2], [-2, 1]])]
    balanced = True
    for T in tests:
        s = signature(sympy.kronecker_product(T, G1))
        if s[0] != s[1] or s[0] == 0:
            balanced = False
    check("at J_1 the quaternion k = s_1 (x) 1 (x) 1 preserves V_R and psi, "
          "anticommutes with J_1 and carries psi(x, J_1 y) to its negative; "
          "so psi (x) S is congruent to its negative, hence indefinite, for "
          "every nonzero real symmetric 2 x 2 matrix S: no invariant class "
          "of degree two polarises the square",
          k_real and k_sp and k_anti and k_neg and balanced,
          "signature (m,m) confirmed directly on %d matrices S" % len(tests))

    # (C)
    pieces, PI, raise_ops = MR.build_tensors()
    a = {"0": 3, "12": 5, "13": -7, "23": 11}
    om = {}
    for key, c in a.items():
        for m, v in PI[key].items():
            om[m] = om.get(m, 0) + c * v
    om = {m: v for m, v in om.items() if v != 0}

    def contract(i, x):
        out = {}
        for m, c in x.items():
            if not (m >> i & 1):
                continue
            s = (-1) ** popcount(m & ((1 << i) - 1))
            out[m ^ (1 << i)] = out.get(m ^ (1 << i), 0) + s * c
        return {k: v for k, v in out.items() if v != 0}

    def wedge1(i, x):
        out = {}
        for m, c in x.items():
            if m >> i & 1:
                continue
            s = mono_sign(1 << i, m)
            out[m | (1 << i)] = out.get(m | (1 << i), 0) + s * c
        return {k: v for k, v in out.items() if v != 0}

    def annihilator(factor):
        hol = [i for i in range(NB) if wt(i)[factor] == 1]
        anti = [i for i in range(NB) if wt(i)[factor] == -1]
        types_ok = all(sum(1 for i in hol if m >> i & 1) == 2
                       for key in PI for m in PI[key])
        pairs = [(i, j) for i in anti for j in hol]
        cols = [wedge1(i, contract(j, om)) for (i, j) in pairs]
        rows = sorted({m for c in cols for m in c})
        A = sympy.Matrix(len(rows), len(cols),
                         lambda r, c: cols[c].get(rows[r], 0))
        ker = A.nullspace()
        bit = 2 - factor
        lower = {(j | (1 << bit), j) for j in hol}
        support = None
        if len(ker) == 1:
            v = ker[0]
            support = {pairs[k] for k in range(len(pairs)) if v[k] != 0}
        return types_ok, len(pairs), len(ker), support == lower

    t1, n1, k1, s1 = annihilator(0)
    t3, n3, k3, s3 = annihilator(2)
    check("at J_1 the tensors pi have type (2,2) and the annihilator of "
          "omega_a in H^1(T) (dimension 64) is spanned by the lowering "
          "derivation of the first factor on both copies",
          t1 and n1 == 64 and k1 == 1 and s1,
          "dimension %d, kernel %d" % (n1, k1))
    check("at J_3, the Mumford family, it is spanned by the lowering "
          "derivation of the third factor, as in item (XLIV)",
          t3 and n3 == 64 and k3 == 1 and s3,
          "dimension %d, kernel %d" % (n3, k3))

    # (D)
    def swap13(m):
        out = 0
        for i in range(NB):
            if m >> i & 1:
                j = i % 8
                aa, bb, cc = (j >> 2) & 1, (j >> 1) & 1, j & 1
                k = (i - j) + (cc << 2) + (bb << 1) + aa
                out |= 1 << k
        return out

    def image(x):
        out = {}
        for m, c in x.items():
            bits = [i for i in range(NB) if m >> i & 1]
            imgs = []
            for i in bits:
                j = i % 8
                aa, bb, cc = (j >> 2) & 1, (j >> 1) & 1, j & 1
                imgs.append((i - j) + (cc << 2) + (bb << 1) + aa)
            # sign of the permutation sorting imgs
            s = 1
            arr = imgs[:]
            for p in range(len(arr)):
                for q in range(len(arr) - 1 - p):
                    if arr[q] > arr[q + 1]:
                        arr[q], arr[q + 1] = arr[q + 1], arr[q]
                        s = -s
            nm = sum(1 << k for k in imgs)
            out[nm] = out.get(nm, 0) + s * c
        return {k: v for k, v in out.items() if v != 0}

    def same(x, y):
        keys = set(x) | set(y)
        return all(sympy.simplify(x.get(k, 0) - y.get(k, 0)) == 0
                   for k in keys)
    ok = (same(image(PI["12"]), PI["23"]) and same(image(PI["23"]), PI["12"])
          and same(image(PI["13"]), PI["13"]) and same(image(PI["0"]), PI["0"]))
    check("the exchange of the first and third factors carries pi_12 to "
          "pi_23 and fixes pi_0 and pi_13", ok)


if __name__ == "__main__":
    print("(XLVII) the Hodge locus of an exceptional class among all complex "
          "tori, and twistor lines")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
