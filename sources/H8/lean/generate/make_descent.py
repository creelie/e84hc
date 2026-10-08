#!/usr/bin/env python3
"""
make_descent.py

Writes the certificates of item (LIV), descent and scalar extension, for
HodgeObstruction.lean.  The model and the field data are those of
code/descent.py, which this script imports.

(A) For each field F and n it records an integer matrix C and an integer
    s > 0 with  s P(w_k) = sum_j C_kj w'_j,  where w_k = Tr(z^k det_F) on
    X = B x Y, w'_j the same on B, and P the correspondence
    pr_B*(x . pr_Y^*(eta_Y^(2m-2) y')), together with 2m Q-basis tuples on
    which the forms w'_j have a nonsingular matrix (the forms depend on a
    basis tuple only through the sum of its exponents, so the tuples are
    recorded by these sums).  The kernel recomputes
    every form, checks the identity exactly, that det C != 0 and the minor
    is nonsingular (so dim W_F(B) = rank P(W_F(X)) = joint rank = 2m), and
    that P kills W_F(X) when y' is replaced by eta_Y.
(C) For each extension K in F and n it records an integer matrix C and
    s > 0 with s j^* w^F_k = sum_j C_kj w^K_j, and 2 tuples on which
    w^K_0, w^K_1 are independent; the kernel checks the identity and that C
    has rank 2.

Run from the repository root:  python3 lean/generate/make_descent.py > out
"""

import os
import sys
from fractions import Fraction as Fr
from itertools import combinations, product
from math import gcd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "code"))
import descent as Dm  # noqa: E402


def lcm(a, b):
    return a * b // gcd(a, b)


def solve_rows(A, b):
    """x with x A = b (A: r x c list of Fr rows, independent), exact"""
    r, c = len(A), len(A[0])
    # Gaussian elimination on the augmented transpose
    M = [[A[i][j] for i in range(r)] + [b[j]] for j in range(c)]
    piv_cols, row = [], 0
    for col in range(r):
        p = next((i for i in range(row, c) if M[i][col] != 0), None)
        assert p is not None
        M[row], M[p] = M[p], M[row]
        pv = M[row][col]
        M[row] = [x / pv for x in M[row]]
        for i in range(c):
            if i != row and M[i][col] != 0:
                f = M[i][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[row])]
        piv_cols.append(col)
        row += 1
    for i in range(row, c):
        assert M[i][r] == 0
    return [M[i][r] for i in range(r)]


def independent_cols(rows):
    """indices of len(rows) columns on which the rows are independent"""
    r = len(rows)
    for cols in combinations(range(len(rows[0])), r):
        if Dm.rank([[row[c] for c in cols] for row in rows]) == r:
            return list(cols)
    raise AssertionError


def int_matrix(C):
    s = 1
    for row in C:
        for x in row:
            s = lcm(s, x.denominator)
    return s, [[int(x * s) for x in row] for row in C]


def descent_data(Fd, n):
    D, m = Fd.D, Fd.m
    NB, NY = 2 * n, 2
    cB = list(range(NB))
    cY = list(range(NB, NB + NY))
    Yq = [i * D + j for i in cY for j in range(D)]
    WB = [Dm.weil_form(Fd, NB, Fd.basis(k), cB) for k in range(D)]
    WX = [Dm.weil_form(Fd, NB + NY, Fd.basis(k), cB + cY) for k in range(D)]
    yprime = Dm.weil_form(Fd, NY, Fd.one(), cY)
    hY = [Fd.one(), Fd.scal(Fr(-1), Fd.tpos)]
    etaY = Dm.herm_form_2(Fd, cY, hY)
    mt = dict(yprime)
    for _ in range(2 * m - 2):
        mt = Dm.wedge(etaY, mt)
    Ytop = tuple(Yq)

    def P(x, mform):
        out = {}
        for key, val in x.items():
            U = tuple(q for q in key if q < NB * D)
            T = tuple(q for q in key if q >= NB * D)
            comp = tuple(q for q in Ytop if q not in T)
            mv = mform.get(comp)
            if not mv:
                continue
            seq = list(U) + list(T) + list(comp)
            sgn = Dm.perm_sign(sorted(range(len(seq)), key=lambda s: seq[s]))
            out[U] = out.get(U, Fr(0)) + sgn * val * mv
        return {k: v for k, v in out.items() if v}

    keys = sorted(set().union(*[set(w) for w in WB]))
    vecB = [[w.get(k, Fr(0)) for k in keys] for w in WB]
    PX = [P(x, mt) for x in WX]
    C = [solve_rows(vecB, [p.get(k, Fr(0)) for k in keys]) for p in PX]
    s, Ci = int_matrix(C)
    # the forms depend on a basis tuple only through its exponent sum sigma;
    # record D values of sigma on which they are independent
    sig = {}
    for c, key in enumerate(keys):
        sig.setdefault(sum(q % D for q in key), c)
    sigmas = sorted(sig)
    sub = [[row[sig[x]] for x in sigmas] for row in vecB]
    cols = independent_cols(sub)
    return s, Ci, [sigmas[c] for c in cols]


def scalar_data(Fbig, Ksmall, s_in_F, n):
    DK, DF = Ksmall.D, Fbig.D
    jb = [Fbig.one(), [Fr(c) for c in s_in_F]]
    tuples = list(product(range(DK), repeat=2 * n))
    WK, JW = [], []
    for k in range(DK):
        row = []
        for js in tuples:
            pr = Ksmall.one()
            for j in js:
                pr = Ksmall.mul(pr, Ksmall.basis(j))
            row.append(Ksmall.tr(Ksmall.mul(Ksmall.basis(k), pr)))
        WK.append(row)
    for k in range(DF):
        row = []
        for js in tuples:
            pr = Fbig.one()
            for j in js:
                pr = Fbig.mul(pr, jb[j])
            row.append(Fbig.tr(Fbig.mul(Fbig.basis(k), pr)))
        JW.append(row)
    C = [solve_rows(WK, row) for row in JW]
    s, Ci = int_matrix(C)
    return s, Ci, independent_cols(WK)


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_mat(M):
    return "[" + ", ".join(lean_list(r) for r in M) + "]"


def field_tuple(row):
    name, minpoly, conj_z, xi, tpos = row
    return "(%s, %s, %s, %s)" % (lean_list(minpoly), lean_list(conj_z), lean_list(xi),
                                 lean_list(tpos))


def main():
    fields = {row[0]: row for row in Dm.FIELDS}
    plan = [("Q(i)", (1, 2, 3, 4, 5)), ("Q(sqrt-2)", (1, 2, 3, 4)), ("Q(sqrt-3)", (1, 2, 3, 4)),
            ("Q(sqrt-5)", (1, 2, 3)), ("Q(zeta5)", (1, 2, 3)), ("Q(zeta8)", (1, 2, 3)),
            ("Q(zeta7)", (1, 2))]
    out = ["/-- (A): `(field, n, s, C, sigmas)`, a field given by its monic minimal",
           "polynomial (low to high), the conjugate of `z`, `xi` and `t`. -/",
           "def dsDescent : List ((List Int × List Int × List Int × List Int) × Nat × Nat"
           " × List (List Int) × List Nat) := ["]
    rows = []
    for name, ns in plan:
        Fd = Dm.Field(*fields[name])
        for n in ns:
            s, C, masks = descent_data(Fd, n)
            rows.append("  (%s, %d, %d, %s, %s)" % (field_tuple(fields[name]), n, s, lean_mat(C),
                                                    lean_list(masks)))
    out.append(",\n".join(rows) + "]")
    out.append("")
    Qi = ("Q(i)", [1, 0, 1], [0, -1], [0, 1], [3, 0])
    Q7 = ("Q(sqrt-7)", [7, 0, 1], [0, -1], [0, 1], [2, 0])
    Q3 = ("Q(sqrt-3)", [3, 0, 1], [0, -1], [0, 1], [2, 0])
    Qz9 = ("Q(zeta9)", [1, 0, 0, 1, 0, 0, 1], [0, 0, -1, 0, 0, -1],
           [1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0])
    ext = [(fields["Q(zeta8)"], Qi, [0, 0, 1, 0]),
           (fields["Q(zeta7)"], Q7, [1, 2, 2, 0, 2, 0]),
           (Qz9, Q3, [1, 0, 0, 2, 0, 0])]
    out.append("/-- (C): `(F, K, image of sqrt(-d) in F, n, s, C, columns)`. -/")
    out.append("def dsScalar : List ((List Int × List Int × List Int × List Int)"
               " × (List Int × List Int × List Int × List Int) × List Int × Nat × Nat"
               " × List (List Int) × List Nat) := [")
    rows = []
    for Fb, Ks, sF in ext:
        for n in (1, 2):
            s, C, cols = scalar_data(Dm.Field(*Fb), Dm.Field(*Ks), sF, n)
            rows.append("  (%s, %s, %s, %d, %d, %s, %s)" % (field_tuple(Fb), field_tuple(Ks),
                                                            lean_list(sF), n, s, lean_mat(C),
                                                            lean_list(cols)))
    out.append(",\n".join(rows) + "]")
    print("\n".join(out))


if __name__ == "__main__":
    main()
