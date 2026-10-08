#!/usr/bin/env python3
"""
make_twistor_locus.py

Writes the data of item (XLVII), the Hodge locus of an exceptional class of a
Mumford square and twistor lines, for HodgeObstruction.lean.  The model is
that of code/twistor_locus.py and code/mumford_rigidity.py, which this script
imports.  It records

  * a basis of V_R = {x : M conj(x) = x}, M = S (x) S (x) 1, as eight
    Gaussian integer vectors, and eight of the sixteen real coordinates on
    which they are independent;
  * for J_3, J_1, J_2, an integer matrix P with P^T G P diagonal, where
    G = psi(x, J y) on V_R;
  * a common denominator D and the integer matrices D Gamma^(-1), Gamma the
    Gram matrix of the form B(u, v) induced by psi on wedge^2 V, on the bases
    of the four isotypic pieces used in Section 77 (theta, and the vectors
    mu(t, s) of the blocks (0,1), (0,2), (1,2)); so that
    D pi = sum_(k,l) (D Gamma^(-1))_kl u_k (x) u_l is D times the tensor pi of
    code/mumford_rigidity.py (asserted below);
  * for the factors 0 and 2, the rows (monomials) and columns of a minor of
    size 63, nonzero modulo 1000003, of the 64 vectors e_i ^ iota_j (omega),
    i of weight -1 and j of weight +1 in that factor, omega = sum a_key pi_key,
    a = (3, 5, -7, 11).

Run from the repository root:  python3 lean/generate/make_twistor_locus.py > out
"""
import os
import sys
from fractions import Fraction as Fr
from math import gcd

import sympy

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
import mumford_rigidity as MR  # noqa: E402
import twistor_locus as TL  # noqa: E402

P = 1000003
PAIRS = [(a, b) for a in range(8) for b in range(a + 1, 8)]


def lcm(a, b):
    return a * b // gcd(a, b)


def pick_minor(Mat, r):
    A = [[int(v) % P for v in row] for row in Mat]
    rows, cols = [], []
    used_r, used_c = set(), set()
    while len(rows) < r:
        found = None
        for i in range(len(A)):
            if i in used_r:
                continue
            for j in range(len(A[0])):
                if j not in used_c and A[i][j]:
                    found = (i, j)
                    break
            if found:
                break
        assert found
        i, j = found
        used_r.add(i)
        used_c.add(j)
        rows.append(i)
        cols.append(j)
        inv = pow(A[i][j], P - 2, P)
        for t in range(len(A)):
            if t != i and A[t][j]:
                f = A[t][j] * inv % P
                A[t] = [(a - f * b) % P for a, b in zip(A[t], A[i])]
    return rows, cols


def congruence(G):
    """an invertible rational P with P^T G P diagonal (symmetric elimination)"""
    n = len(G)
    A = [[Fr(x) for x in row] for row in G]
    Pm = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]

    def col_op(dst, src, c):      # column dst += c column src, and the same on rows
        for r in range(n):
            A[r][dst] += c * A[r][src]
        for r in range(n):
            A[dst][r] += c * A[src][r]
        for r in range(n):
            Pm[r][dst] += c * Pm[r][src]
    for k in range(n):
        if A[k][k] == 0:
            j = next((j for j in range(k + 1, n) if A[j][j] != 0), None)
            if j is not None:
                col_op(k, j, Fr(1))
            else:
                j = next((j for j in range(k + 1, n) if A[k][j] != 0), None)
                if j is None:
                    continue
                col_op(k, j, Fr(1))
        for j in range(k + 1, n):
            if A[k][j] != 0:
                col_op(j, k, -A[k][j] / A[k][k])
    assert all(A[i][j] == 0 for i in range(n) for j in range(n) if i != j)
    out = []
    for c in range(n):
        d = 1
        for r in range(n):
            d = lcm(d, Pm[r][c].denominator)
        out.append([int(Pm[r][c] * d) for r in range(n)])
    return [list(r) for r in zip(*out)]


def mu_vec(t, s):
    import mumford_rm as M
    A = M.mm(M.mm(M.tr(t), M.PSI), s)
    Mu = M.madd(A, M.tr(A), Fr(-1))
    Y = M.mm(M.mm(M.PSI, Mu), M.tr(M.PSI))
    return [int(Y[a][b]) for (a, b) in PAIRS]


def main():
    import mumford_rm as M
    S, E2 = TL.S, TL.E2
    Mr = TL.kron3(S, S, E2)
    psi = TL.kron3(S, S, S)
    VR = TL.real_basis(Mr)
    cols = [[(int(sympy.re(VR[r, c])), int(sympy.im(VR[r, c]))) for r in range(8)] for c in range(8)]
    real_rows = [[cols[c][r][0] for c in range(8)] for r in range(8)] + \
                [[cols[c][r][1] for c in range(8)] for r in range(8)]
    rr, _ = pick_minor(real_rows, 8)
    print("/-- the basis of `V_R`, as eight columns of Gaussian integers `(re, im)`. -/")
    print("def twVR : List (List (Int × Int)) := [%s]" % ", ".join(
        "[" + ", ".join("(%d, %d)" % z for z in col) + "]" for col in cols))
    print("/-- eight real coordinates (`0..7` real parts, `8..15` imaginary parts) on")
    print("which the columns of `twVR` are independent. -/")
    print("def twVRRows : List Nat := [%s]" % ", ".join(map(str, sorted(rr))))
    j3 = sympy.Matrix([[0, -1], [1, 0]])
    j1 = sympy.Matrix([[sympy.I, 0], [0, -sympy.I]])
    Js = [TL.kron3(E2, E2, j3), TL.kron3(j1, E2, E2), TL.kron3(E2, j1, E2)]
    certs = []
    for J in Js:
        G = (VR.T * psi * J * VR).expand()
        assert all(sympy.im(z) == 0 for z in G)
        Gi = [[int(sympy.re(G[r, c])) for c in range(8)] for r in range(8)]
        certs.append(congruence(Gi))
    print("/-- for `J_3, J_1, J_2`: `P` with `P^T G P` diagonal, `G = psi(x, J y)` on `V_R`. -/")
    print("def twCong : List (List (List Int)) := [%s]" % ", ".join(
        "[" + ", ".join("[" + ", ".join(map(str, row)) + "]" for row in Pm) + "]" for Pm in certs))
    # the four pieces
    theta = [0] * 28
    for (a, b), c in (((0, 7), 1), ((1, 6), -1), ((2, 5), -1), ((3, 4), 1)):
        theta[PAIRS.index((a, b))] = c
    Tb = [M.on_factor(i, m) for i in range(3) for m in (M.E2, M.F2, M.H2)]
    bases = {"0": [theta]}
    for key, (i, j) in (("12", (0, 1)), ("13", (0, 2)), ("23", (1, 2))):
        bases[key] = [mu_vec(Tb[3 * i + a], Tb[3 * j + b]) for a in range(3) for b in range(3)]
    B = [[MR.psi(a, c) * MR.psi(b, d) - MR.psi(a, d) * MR.psi(b, c) for (c, d) in PAIRS] for (a, b) in PAIRS]
    invs = {}
    D = 1
    for key, U in bases.items():
        Gam = sympy.Matrix([[sum(u[p] * B[p][q] * v[q] for p in range(28) for q in range(28)) for v in U] for u in U])
        Gi = Gam.inv()
        invs[key] = Gi
        for x in Gi:
            D = lcm(D, int(sympy.fraction(sympy.nsimplify(x))[1]))
    _, PI, _ = MR.build_tensors()
    out = []
    for key in ("0", "12", "13", "23"):
        U = bases[key]
        Gi = invs[key]
        Mi = [[int(Gi[k, l] * D) for l in range(len(U))] for k in range(len(U))]
        # D pi from the bases, against code/mumford_rigidity.py
        mine = {}
        for k in range(len(U)):
            for l in range(len(U)):
                if Mi[k][l] == 0:
                    continue
                for p in range(28):
                    if U[k][p] == 0:
                        continue
                    for q in range(28):
                        if U[l][q] == 0:
                            continue
                        a, b = PAIRS[p]
                        c, d = PAIRS[q]
                        m = (1 << a) | (1 << b) | (((1 << c) | (1 << d)) << 8)
                        mine[m] = mine.get(m, 0) + Mi[k][l] * U[k][p] * U[l][q]
        mine = {m: v for m, v in mine.items() if v}
        assert set(mine) == set(PI[key]) and all(mine[m] == D * PI[key][m] for m in mine), key
        out.append(Mi)
    print("/-- the common denominator `D` and `D Gamma^(-1)` for the pieces `0, 12, 13, 23`. -/")
    print("def twGinv : Nat × List (List (List Int)) := (%d, [%s])" % (D, ", ".join(
        "[" + ", ".join("[" + ", ".join(map(str, row)) + "]" for row in Mi) + "]" for Mi in out)))
    # the annihilator minors
    a = {"0": 3, "12": 5, "13": -7, "23": 11}
    om = {}
    for key, c in a.items():
        for m, v in PI[key].items():
            om[m] = om.get(m, 0) + c * v * D
    om = {m: int(v) for m, v in om.items() if v != 0}

    def contract(i, x):
        o = {}
        for m, c in x.items():
            if not (m >> i & 1):
                continue
            s = (-1) ** MR.popcount(m & ((1 << i) - 1))
            o[m ^ (1 << i)] = o.get(m ^ (1 << i), 0) + s * c
        return {k: v for k, v in o.items() if v != 0}

    def wedge1(i, x):
        o = {}
        for m, c in x.items():
            if m >> i & 1:
                continue
            s = MR.mono_sign(1 << i, m)
            o[m | (1 << i)] = o.get(m | (1 << i), 0) + s * c
        return {k: v for k, v in o.items() if v != 0}
    mins = []
    for factor in (0, 2):
        hol = [i for i in range(16) if MR.wt(i)[factor] == 1]
        anti = [i for i in range(16) if MR.wt(i)[factor] == -1]
        pairs = [(i, j) for i in anti for j in hol]
        cs = [wedge1(i, contract(j, om)) for (i, j) in pairs]
        rows = sorted({m for c in cs for m in c})
        A = [[c.get(m, 0) for c in cs] for m in rows]
        rr, cc = pick_minor(A, 63)
        mins.append(([rows[r] for r in rr], cc))
    print("/-- for the factors `0` and `2`: the monomials and the columns of a minor of")
    print("size `63` of the vectors `e_i ^ iota_j (D omega)`. -/")
    print("def twAnnMinor : List (List Nat × List Nat) := [%s]" % ", ".join(
        "([%s], [%s])" % (", ".join(map(str, r)), ", ".join(map(str, c))) for r, c in mins))


if __name__ == "__main__":
    main()
