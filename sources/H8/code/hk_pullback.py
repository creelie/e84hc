#!/usr/bin/env python3
"""
hk_pullback.py

Item (XLVIII) of COMPUTATIONS.md: the finite computations behind
the description of the square of a Mumford fourfold as a holomorphic
symplectic variety whose symplectic class generates the Hodge structure T of
K3 type, behind the formula for the exceptional classes as products of two
classes of T, and behind the statement that no hyperkaehler manifold of
dimension eight receives a rational map from the square that pulls back its
symplectic form nontrivially.

Model.  As in items (XLIII) to (XLVII): V = V_1 (x) V_2 (x) V_3 over Q, basis
indexed by (a,b,c) in {0,1}^3 with weight (1-2a, 1-2b, 1-2c), psi =
eps (x) eps (x) eps, H^1(X x X) = V (+) V (bits 0..7 and 8..15), and
V^{1,0} spanned by the vectors of third weight +1.  T = sl(V_1) + sl(V_2) +
sl(V_3), with basis E_i, F_i, H_i.  Psi in wedge^2 V is the bivector dual to
psi, and iota(x) = (x (x) 1) Psi, an element of V (x) V = H^1 (x) H^1, which
is a summand of H^2(X x X).  C_i = E_i F_i + F_i E_i + H_i^2 / 2 is the
Casimir element of the trace form on sl(V_i), and iota_2(x y) is the cup
product iota(x) iota(y) in H^4(X x X).  All arithmetic is exact.

What is checked:

  (A) iota(x) is symmetric, so lies in S^2 V, and iota is equivariant:
      y.iota(x) = iota([y, x]) for all eighteen pairs of generators;

  (B) the three Casimir operators split H^2(X x X) = wedge^2(V (+) V), of
      dimension 120, into isotypic pieces of types (0,0,0) (3 copies),
      (2,2,0), (2,0,2), (0,2,2) (3 copies each), (2,2,2) (once), and
      (2,0,0), (0,2,0), (0,0,2) (once each, spanned by iota(T_1), iota(T_2),
      iota(T_3)); in the (2,0)-part, of dimension 28, the pieces have
      dimensions 0, 0, 3, 3, 9, 0, 0, 1, so among the Galois orbits of
      types only that of T has h^{2,0} = 1;

  (C) sigma_0 = iota(E_3) is of type (2,0) and pairs the (1,0)-vectors of
      the two copies through an invertible 4 x 4 block: a holomorphic
      symplectic form on X x X;

  (D) iota_2(C_1) = 3 pi_0 - pi_12 - pi_13 + 3 pi_23 and cyclically, so
      iota_2(s_1 C_1 + s_2 C_2 + s_3 C_3) = omega_a with a_0 = 3 (s_1 + s_2
      + s_3) and a_ij = 4 s_k - (s_1 + s_2 + s_3);

  (E) det(x_1 (x) 1 (x) 1 + 1 (x) x_2 (x) 1 + 1 (x) 1 (x) x_3) =
      Delta(N_1, N_2, N_3)^2, with N_i = -det(x_i) and
      Delta = N_1^2 + N_2^2 + N_3^2 - 2 N_1 N_2 - 2 N_1 N_3 - 2 N_2 N_3,
      as polynomials in the nine coordinates of x;

  (F) the top power iota(x)^8 is 8! det(x) times the volume form, up to one
      sign, at sample points; with (E) the octic form x -> int iota(x)^8
      on T is a nonzero constant times Delta(N)^2;

  (G) Delta is a nondegenerate ternary quadratic form, hence irreducible,
      so Delta(N)^2 is not a constant multiple of the fourth power of any
      linear form in N_1, N_2, N_3.

Run:  python3 hk_pullback.py
"""
import os
import random
import sys

import sympy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mumford_rigidity as MR  # noqa: E402
from mumford_rigidity import wt, mono_sign, NB, psi, gen_matrix  # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


P8 = sympy.Matrix(8, 8, lambda i, j: psi(i, j))
PSI = P8.inv()          # the bivector dual to psi, as a matrix psi^{pq}


def gen(t, kind):
    if kind == "E":
        return gen_matrix(t, True)
    if kind == "F":
        return gen_matrix(t, False)
    return sympy.diag(*[wt(i)[t] for i in range(8)])


GENS = [(t, k) for t in range(3) for k in "EFH"]


def iota_matrix(x):
    """B with iota(x) = sum_{r,q} B[r,q] e_r (x) e_q in V (x) V"""
    return x * PSI


def as_form(B):
    """the element sum B[r,q] e_r ^ e'_q of wedge^2(V (+) V)"""
    out = {}
    for r in range(8):
        for q in range(8):
            if B[r, q] == 0:
                continue
            m1, m2 = 1 << r, 1 << (8 + q)
            out[m1 | m2] = out.get(m1 | m2, 0) + mono_sign(m1, m2) * B[r, q]
    return {k: v for k, v in out.items() if v != 0}


def wedge(x, y):
    out = {}
    for m, c in x.items():
        for n, d in y.items():
            if m & n:
                continue
            out[m | n] = out.get(m | n, 0) + mono_sign(m, n) * c * d
    return {k: v for k, v in out.items() if v != 0}


def lin(pairs):
    out = {}
    for c, x in pairs:
        for m, v in x.items():
            out[m] = out.get(m, 0) + c * v
    return {k: v for k, v in out.items() if v != 0}


PAIRS16 = [(i, j) for i in range(NB) for j in range(i + 1, NB)]
P16 = {p: k for k, p in enumerate(PAIRS16)}


def derivation16(t, kind):
    """generator acting on V (+) V (block diagonal), as a 16 x 16 matrix"""
    g = gen(t, kind)
    M = sympy.zeros(16, 16)
    M[:8, :8] = g
    M[8:, 8:] = g
    return M


def on_wedge2_16(M):
    W = sympy.zeros(120, 120)
    for k, (a, b) in enumerate(PAIRS16):
        for r in range(16):
            if M[r, a] != 0 and r != b:
                s, p = (1, (r, b)) if r < b else (-1, (b, r))
                W[P16[p], k] += s * M[r, a]
            if M[r, b] != 0 and r != a:
                s, p = (1, (a, r)) if a < r else (-1, (r, a))
                W[P16[p], k] += s * M[r, b]
    return W


def run():
    # (A)
    sym, equi = True, True
    for (t, k) in GENS:
        Bx = iota_matrix(gen(t, k))
        sym = sym and Bx == Bx.T
        for (s, l) in GENS:
            y = gen(s, l)
            lhs = y * Bx + Bx * y.T
            rhs = iota_matrix(y * gen(t, k) - gen(t, k) * y)
            equi = equi and (lhs - rhs) == sympy.zeros(8, 8)
    check("iota(x) = (x (x) 1) Psi is symmetric for the nine generators of T, "
          "and y.iota(x) = iota([y, x]) for all pairs of generators",
          sym and equi)

    # (B)
    cas = []
    for t in range(3):
        E = on_wedge2_16(derivation16(t, "E"))
        F = on_wedge2_16(derivation16(t, "F"))
        H = on_wedge2_16(derivation16(t, "H"))
        cas.append(H * H + 2 * (E * F + F * E))
    hol = [i for i in range(NB) if wt(i)[2] == 1]
    idx20 = [P16[(i, j)] for (i, j) in PAIRS16 if i in hol and j in hol]
    types = [(0, 0, 0), (2, 2, 0), (2, 0, 2), (0, 2, 2), (2, 2, 2),
             (2, 0, 0), (0, 2, 0), (0, 0, 2)]
    expect_dim = {(0, 0, 0): 3, (2, 2, 0): 27, (2, 0, 2): 27, (0, 2, 2): 27,
                  (2, 2, 2): 27, (2, 0, 0): 3, (0, 2, 0): 3, (0, 0, 2): 3}
    expect_20 = {(0, 0, 0): 0, (2, 2, 0): 0, (2, 0, 2): 9, (0, 2, 2): 9,
                 (2, 2, 2): 9, (2, 0, 0): 0, (0, 2, 0): 0, (0, 0, 2): 1}
    dims, dims20, ok = {}, {}, True
    for ty in types:
        stack = sympy.Matrix.vstack(*[cas[t] - ty[t] * (ty[t] + 2) *
                                      sympy.eye(120) for t in range(3)])
        ker = stack.nullspace()
        dims[ty] = len(ker)
        sub = stack.extract(list(range(stack.rows)), idx20)
        dims20[ty] = len(sub.nullspace())
        ok = ok and dims[ty] == expect_dim[ty] and dims20[ty] == expect_20[ty]
    ok = ok and sum(dims.values()) == 120 and sum(dims20.values()) == 28
    # iota(T_i) spans the isotypic piece of type 2 on the i-th factor
    for t in range(3):
        ty = tuple(2 if s == t else 0 for s in range(3))
        vecs = []
        for k in "EFH":
            f = as_form(iota_matrix(gen(t, k)))
            v = sympy.zeros(120, 1)
            for m, c in f.items():
                bits = [i for i in range(NB) if m >> i & 1]
                v[P16[(bits[0], bits[1])]] = c
            vecs.append(v)
        Mv = sympy.Matrix.hstack(*vecs)
        stack = sympy.Matrix.vstack(*[cas[s] - ty[s] * (ty[s] + 2) *
                                      sympy.eye(120) for s in range(3)])
        ok = ok and Mv.rank() == 3 and (stack * Mv) == sympy.zeros(360, 3)
    check("the Casimirs split H^2 of the square (dimension 120) into "
          "isotypic pieces of dimensions 3, 27, 27, 27, 27, 3, 3, 3 with "
          "(2,0)-parts 0, 0, 9, 9, 9, 0, 0, 1; the pieces of types (2,0,0), "
          "(0,2,0), (0,0,2) are iota(T_1), iota(T_2), iota(T_3), and only the "
          "Galois orbit of T has h^{2,0} = 1", ok,
          "dims %s" % [dims[t] for t in types])

    # (C)
    B = iota_matrix(gen(2, "E"))
    rows = [r for r in range(8) if any(B[r, q] != 0 for q in range(8))]
    cols = [q for q in range(8) if any(B[r, q] != 0 for r in range(8))]
    typ = all(wt(r)[2] == 1 for r in rows) and all(wt(q)[2] == 1
                                                  for q in cols)
    blk = B.extract(rows, cols)
    check("sigma_0 = iota(E_3) is of type (2,0) and pairs the (1,0)-vectors "
          "of the two copies through an invertible 4 x 4 block, so it is a "
          "holomorphic symplectic form on the square",
          typ and blk.shape == (4, 4) and blk.det() != 0,
          "det of the block %s" % blk.det())

    # (D)
    pieces, PI, raise_ops = MR.build_tensors()
    Q = []
    for t in range(3):
        fE = as_form(iota_matrix(gen(t, "E")))
        fF = as_form(iota_matrix(gen(t, "F")))
        fH = as_form(iota_matrix(gen(t, "H")))
        Q.append(lin([(1, wedge(fE, fF)), (1, wedge(fF, fE)),
                      (sympy.Rational(1, 2), wedge(fH, fH))]))
    expected = [
        lin([(3, PI["0"]), (-1, PI["12"]), (-1, PI["13"]), (3, PI["23"])]),
        lin([(3, PI["0"]), (-1, PI["12"]), (3, PI["13"]), (-1, PI["23"])]),
        lin([(3, PI["0"]), (3, PI["12"]), (-1, PI["13"]), (-1, PI["23"])]),
    ]
    okD = all(lin([(1, Q[t]), (-1, expected[t])]) == {} for t in range(3))
    s1, s2, s3 = sympy.symbols("s1 s2 s3")
    tot = lin([(s1, Q[0]), (s2, Q[1]), (s3, Q[2])])
    sm = s1 + s2 + s3
    om = lin([(3 * sm, PI["0"]), (4 * s3 - sm, PI["12"]),
              (4 * s2 - sm, PI["13"]), (4 * s1 - sm, PI["23"])])
    okD = okD and all(sympy.expand(tot.get(m, 0) - om.get(m, 0)) == 0
                      for m in set(tot) | set(om))
    check("iota_2(C_1) = 3 pi_0 - pi_12 - pi_13 + 3 pi_23 and cyclically; "
          "so iota_2(sum s_i C_i) = omega_a with a_0 = 3 sum s_i and "
          "a_ij = 4 s_k - sum s_i", okD)

    # (E)
    A = sympy.symbols("a1:4")
    Bs = sympy.symbols("b1:4")
    Cs = sympy.symbols("c1:4")
    X = sympy.zeros(8, 8)
    for t in range(3):
        X += A[t] * gen(t, "H") + Bs[t] * gen(t, "E") + Cs[t] * gen(t, "F")
    d = X.det(method="berkowitz")
    N = [A[t] ** 2 + Bs[t] * Cs[t] for t in range(3)]
    Delta = (N[0] ** 2 + N[1] ** 2 + N[2] ** 2
             - 2 * N[0] * N[1] - 2 * N[0] * N[2] - 2 * N[1] * N[2])
    okE = sympy.expand(d - Delta ** 2) == 0
    # N_i is minus the determinant of x_i on V_i (checked on the 2 x 2 blocks)
    for t in range(3):
        m2 = sympy.Matrix([[A[t], Bs[t]], [Cs[t], -A[t]]])
        okE = okE and sympy.expand(-m2.det() - N[t]) == 0
    check("det(x_1 + x_2 + x_3 on V) = Delta(N_1, N_2, N_3)^2 with "
          "N_i = -det(x_i), as a polynomial identity in nine variables", okE)

    # (F)
    rng = random.Random(20260924)
    okF, ratios = True, []
    for _ in range(3):
        vals = {}
        for t in range(3):
            vals[A[t]] = rng.randint(-5, 5)
            vals[Bs[t]] = rng.randint(-5, 5)
            vals[Cs[t]] = rng.randint(-5, 5)
        Xv = X.subs(vals)
        f = as_form(iota_matrix(Xv))
        top = {0: 1}
        for _k in range(8):
            top = wedge(top, f)
        coeff = top.get((1 << 16) - 1, 0)
        dv = Xv.det()
        if dv == 0:
            okF = okF and coeff == 0
            continue
        r = sympy.Rational(coeff, dv * sympy.factorial(8))
        ratios.append(r)
    okF = okF and len(ratios) > 0 and all(abs(r) == 1 for r in ratios) \
        and len(set(ratios)) == 1
    check("iota(x)^8 = +- 8! det(x) vol at sample points, with one sign", okF,
          "ratios %s" % ratios)

    # (G)
    n1, n2, n3 = sympy.symbols("n1 n2 n3")
    Dn = n1**2 + n2**2 + n3**2 - 2*n1*n2 - 2*n1*n3 - 2*n2*n3
    Gram = sympy.hessian(Dn, (n1, n2, n3)) / 2
    irreducible = len(sympy.factor_list(Dn)[1]) == 1 and \
        sympy.factor_list(Dn)[1][0][1] == 1
    check("Delta is a nondegenerate ternary quadratic form (Gram determinant "
          "-4) and irreducible, so Delta(N)^2 is not a constant multiple of "
          "the fourth power of a linear form",
          Gram.det() == -4 and irreducible, "Gram determinant %s" % Gram.det())


if __name__ == "__main__":
    print("(XLVIII) the square as a holomorphic symplectic variety, and "
          "pull-back from hyperkaehler manifolds")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
