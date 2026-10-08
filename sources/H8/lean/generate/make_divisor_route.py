#!/usr/bin/env python3
"""
make_divisor_route.py

Writes the certificates of item (XXIV), the divisor route on a fixed
lattice, for HodgeObstruction.lean.  The model is that of
code/divisor_route.py, which this script imports: Lambda = O^2 with
i^2 = -d, j^2 = 1, the polarisation E of the quaternionic model at b = 1,
R the lattice of K-bilinear classes, phi_x = E^{-1} x.  The kernel rebuilds
E and the left multiplication by i itself (Section 73); the script records

  * the pencil x_k = x + k y of code/divisor_route.py, x_k(u, v) =
    E(phi_k u, v) with phi_k left multiplication by (2d)^{-1} C_k j,
    C_k = [[1, k], [k, -1]];
  * an integer matrix S and s > 0 with E S = s I (so E^{-1} = S / s);
  * a basis of R, a left inverse of it, and a nonzero minor of size 16 of the
    linear conditions defining R (so R is the whole lattice, of rank 12);
  * an integer matrix P with P^T G P diagonal, G = (-int x_a x_b eta^2) on
    the basis of R, and det P != 0 (the signature);
  * pairs of 2 x 2 minors of the rows x_k, i.x_k, as polynomials in k, whose
    resultants have gcd 1;
  * for k = 0..10 a basis of N_k = (Q eta + Q x_k + Q i.x_k) cap Z^28 with
    certificates of membership and a left inverse, and the minimum mu_k;
  * a basis of the centraliser u of i in sp(V, E), with minors certifying
    its dimension 16;
  * for k = 0..4 a basis of the centraliser c of i and phi_{x_k} in sp(V, E),
    a minor of size 6 of the matrix of X -> [X, phi_{x_k}] on u (so c has
    dimension 10), and a basis of its invariants in wedge^2 V^*, with minors
    certifying dimension 3;
  * at k = 0, where beta(0) = (2d)^{-2} is a rational square, a rational
    complex structure J0 (as an integer matrix over a denominator), four
    relations among the [X_i, J0], and minors certifying dim [c, J0] = 6 and
    dim([c, J0] + [[c, J0], [c, J0]]) = 10.

A minor is given by its rows and columns and is nonzero modulo 1000003.

Run from the repository root:  python3 lean/generate/make_divisor_route.py > out
"""
import os
import sys
from fractions import Fraction as F
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
sys.path.insert(0, HERE)
import divisor_route as D  # noqa: E402
from make_sextic_lattice import left_inverse  # noqa: E402
from make_quaternionic import solve_combo  # noqa: E402

P = 1000003
K2 = D.K2


def lcm(a, b):
    return a * b // gcd(a, b)


def scale_int(vals):
    den = 1
    for v in vals:
        den = lcm(den, F(v).denominator)
    return den


def pick_minor(M, r):
    """r rows and r columns of the integer matrix M with a minor nonzero mod P"""
    A = [[int(v) % P for v in row] for row in M]
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
        assert found, "rank too small"
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


def mat_int(X):
    den = scale_int([v for row in X for v in row])
    return den, [[int(F(v) * den) for v in row] for row in X]


def matmul(A, B):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_mat(M):
    return "[" + ", ".join(lean_list(r) for r in M) + "]"


def lean_sparse(s):
    return "[" + ", ".join("(%d, %d)" % t for t in s) + "]"


def constraint_rows(L, phiS):
    """the 192 x 64 coefficient matrix of X -> (X^T E + E X, X Li - Li X,
    X phiS - phiS X), rows (type, r, c), unknown a * 8 + b"""
    out = []
    for (A, sym) in ((L.E, True), (L.Li, False), (phiS, False)):
        for r in range(8):
            for c in range(8):
                row = [0] * 64
                for a in range(8):
                    for b in range(8):
                        v = 0
                        if sym:
                            if b == r:
                                v += A[a][c]
                            if b == c:
                                v += A[r][a]
                        else:
                            if a == r:
                                v += A[b][c]
                            if b == c:
                                v -= A[r][a]
                        row[a * 8 + b] = int(v)
                out.append(row)
    return out


def inv_rows(Xs):
    """the rows of Y -> (X^T Y + Y X)[p][q], p < q, over the X in Xs, on the
    28 coordinates of an alternating Y"""
    out = []
    for X in Xs:
        for (p, q) in K2:
            row = []
            for (a, b) in K2:
                Y = [[0] * 8 for _ in range(8)]
                Y[a][b], Y[b][a] = 1, -1
                v = sum(X[t][p] * Y[t][q] for t in range(8)) + \
                    sum(Y[p][t] * X[t][q] for t in range(8))
                row.append(int(v))
            out.append(row)
    return out


def flat(X):
    return [X[a][b] for a in range(8) for b in range(8)]


def main():
    out = []
    pencils = {}
    for d in (1, 3):
        L = D.Lattice(d)
        sE, S = mat_int(L.Einv)
        R = L.R_basis()
        Rinv = left_inverse([[R[i][t] for i in range(12)] for t in range(28)])
        # the K-bilinear conditions: rows (r, c) on the 28 coordinates
        cond = []
        for r in range(8):
            for c in range(8):
                coeffs = []
                for (a, b) in K2:
                    X = [[0] * 8 for _ in range(8)]
                    X[a][b], X[b][a] = 1, -1
                    v = (sum(L.Li[k][r] * X[k][c] for k in range(8))
                         - sum(X[r][k] * L.Li[k][c] for k in range(8)))
                    coeffs.append(int(v))
                cond.append(coeffs)
        crow, ccol = pick_minor(cond, 16)
        # signature: symmetric elimination over Q
        G = [[-D.integ(D.wedge(D.wedge(D.form(D.mat_of(a)), D.form(D.mat_of(b))), L.e2))
              for b in R] for a in R]
        n = 12
        A = [[F(v) for v in row] for row in G]
        Pm = [[F(int(i == j)) for j in range(n)] for i in range(n)]
        for c in range(n):
            if A[c][c] == 0:
                j = next((j for j in range(c + 1, n) if A[j][j] != 0), None)
                if j is not None:
                    A[c], A[j] = A[j], A[c]
                    for row in A:
                        row[c], row[j] = row[j], row[c]
                    for row in Pm:
                        row[c], row[j] = row[j], row[c]
                else:
                    j = next(j for j in range(c + 1, n) if A[c][j] != 0)
                    for t in range(n):
                        A[t][c] += A[t][j]
                    for t in range(n):
                        A[c][t] += A[j][t]
                    for row in Pm:
                        row[c] += row[j]
            for j in range(c + 1, n):
                if A[c][j] != 0:
                    f = A[c][j] / A[c][c]
                    for t in range(n):
                        A[t][j] -= f * A[t][c]
                    for t in range(n):
                        A[j][t] -= f * A[c][t]
                    for row in Pm:
                        row[j] -= f * row[c]
        # scale the columns of Pm to integers
        Pint = [[0] * n for _ in range(n)]
        for j in range(n):
            den = scale_int([Pm[i][j] for i in range(n)])
            for i in range(n):
                Pint[i][j] = int(Pm[i][j] * den)
        Dg = matmul(matmul([list(r) for r in zip(*Pint)], G), Pint)
        assert all(Dg[i][j] == 0 for i in range(n) for j in range(n) if i != j)
        pos = sum(1 for i in range(n) if Dg[i][i] > 0)
        neg = sum(1 for i in range(n) if Dg[i][i] < 0)
        assert (pos, neg) == (8, 4)
        # (R6): minors as polynomials, and pairs whose resultants give N
        x0, x1 = D.pencil_class(d, 0), D.pencil_class(d, 1)
        x = [int(v) for v in x0]
        y = [int(b - a) for a, b in zip(x0, x1)]
        pencils[d] = (x, y)
        ix = [int(v) for v in L.times_i(x)]
        iy = [int(v) for v in L.times_i(y)]
        polys = []
        for a in range(28):
            for b in range(a + 1, 28):
                c0 = x[a] * ix[b] - x[b] * ix[a]
                c1 = (x[a] * iy[b] + y[a] * ix[b] - x[b] * iy[a] - y[b] * ix[a])
                c2 = y[a] * iy[b] - y[b] * iy[a]
                if (c0, c1, c2) != (0, 0, 0):
                    polys.append((c0, c1, c2))
        Ntarget, _ = D.index_bound(L, x, y)
        g, pairs = 0, []
        for i in range(len(polys)):
            for j in range(i + 1, len(polys)):
                r = D.resultant(polys[i], polys[j])
                if r and gcd(g, abs(r)) != g:
                    g = gcd(g, abs(r))
                    pairs.append((i, j))
                if g == Ntarget:
                    break
            if g == Ntarget:
                break
        assert g == Ntarget
        # (R5)
        eta_v = D.vec_of(L.E)
        r5 = []
        for k in range(11):
            xk = [a + k * b for a, b in zip(x, y)]
            ik = [int(v) for v in L.times_i(xk)]
            N = D.saturation([eta_v, xk, ik])
            certs = [solve_combo(v, [eta_v, xk, ik]) for v in N]
            Ninv = left_inverse([[N[i][t] for i in range(3)] for t in range(28)])
            mu, _ = D.min_off_eta(L, N, eta_v)
            assert mu.denominator == 1
            r5.append((N, certs, Ninv, int(mu)))
        # (R7), (R8): the centraliser u of i in sp(V, E), of dimension 16
        rows_u = constraint_rows(L, [[0] * 8 for _ in range(8)])[:128]
        U = [mat_int([[v[a * 8 + b] for b in range(8)] for a in range(8)])[1]
             for v in D.nullspace(rows_u, 64)]
        assert len(U) == 16
        arow, acol = pick_minor(rows_u, 48)
        urow, ucol = pick_minor([[X[a][b] for X in U] for a in range(8) for b in range(8)], 16)
        ucert = (U, urow, ucol, arow, acol)

        def cent_cert(xk):
            phiS = matmul(S, [[int(v) for v in row] for row in D.mat_of(xk)])
            c = D.centraliser_basis(L, xk)
            Xs = [mat_int(X)[1] for X in c]
            assert len(Xs) == 10
            brk = [flat(D.bracket(X, phiS)) for X in U]
            crow7, ccol7 = pick_minor([[b[t] for b in brk] for t in range(64)], 6)
            irow, icol = pick_minor([[X[a][b] for X in Xs] for a in range(8) for b in range(8)], 10)
            Yrows = inv_rows(Xs)
            inv = D.nullspace(Yrows, 28)
            Ys = [[int(v * scale_int(u)) for v in u] for u in inv]
            assert len(Ys) == 3
            yrow, ycol = pick_minor(Yrows, 25)
            jrow, jcol = pick_minor([[Y[t] for Y in Ys] for t in range(28)], 3)
            return (Xs, crow7, ccol7, irow, icol, Ys, yrow, ycol, jrow, jcol)
        r7 = [cent_cert([a + k * b for a, b in zip(x, y)]) for k in range(5)]
        kq = next(k for k in range(-6, 7)
                  if D.siegel_point(L, [a + k * b for a, b in zip(x, y)]) is not None)
        xq = [a + kq * b for a, b in zip(x, y)]
        J0 = D.siegel_point(L, xq)
        sJ, J0i = mat_int(J0)
        cq = cent_cert(xq)
        Xq = cq[0]
        pB = [D.bracket(X, J0i) for X in Xq]
        rel = D.nullspace([[flat(Pm_)[t] for Pm_ in pB] for t in range(64)], 10)
        rel = [[int(v * scale_int(u)) for v in u] for u in rel]
        assert len(rel) == 4
        prow, pcol = pick_minor([[flat(Pm_)[t] for Pm_ in pB] for t in range(64)], 6)
        rrow, rcol = pick_minor([[u[t] for u in rel] for t in range(10)], 4)
        pp = pB + [D.bracket(A_, B_) for A_ in pB for B_ in pB]
        grow, gcol = pick_minor([[flat(M)[t] for M in pp] for t in range(64)], 10)
        sJ0 = sJ
        r8 = (kq, sJ0, J0i, cq, rel, prow, pcol, rrow, rcol, grow, gcol)
        out.append((d, sE, S, R, Rinv, crow, ccol, Pint, pairs, Ntarget, r5, r7, r8, ucert))
    # emit
    print("/-- the pencils `(x, y)` of (R4) for `d = 1, 3`. -/")
    print("def drPencil : List (List Int × List Int) := [")
    print(",\n".join("  (%s,\n   %s)" % (lean_list(pencils[d][0]), lean_list(pencils[d][1]))
                     for d in (1, 3)) + "]")
    print("/-- per field: `(d, s, S, R, R^-1, minor of the conditions, P, resultant")
    print("pairs, N_d)`. -/")
    print("def drBase : List (Nat × Nat × List (List Int) × List (List Int) × List (List (Nat × Int))")
    print("    × (List Nat × List Nat) × List (List Int) × List (Nat × Nat) × Nat) := [")
    rows = []
    for (d, sE, S, R, Rinv, crow, ccol, Pint, pairs, Nt, r5, r7, r8, uc) in out:
        rows.append("  (%d, %d, %s, %s, [%s], (%s, %s), %s, %s, %d)" % (
            d, sE, lean_mat(S), lean_mat(R), ", ".join(lean_sparse(r) for r in Rinv),
            lean_list(crow), lean_list(ccol), lean_mat(Pint),
            "[" + ", ".join("(%d, %d)" % p for p in pairs) + "]", Nt))
    print(",\n".join(rows) + "]")
    print("/-- (R5): per field and `k = 0..10`: `(N_k, certificates, left inverse, mu_k)`. -/")
    print("def drMin : List (List (List (List Int) × List (Int × Int × Int × Int)"
          " × List (List (Nat × Int)) × Int)) := [")
    rows = []
    for (d, sE, S, R, Rinv, crow, ccol, Pint, pairs, Nt, r5, r7, r8, uc) in out:
        rows.append("  [" + ",\n   ".join("(%s, [%s], [%s], %d)" % (
            lean_mat(N), ", ".join("(%d, %d, %d, %d)" % (s, a, b, c) for s, (a, b, c) in certs),
            ", ".join(lean_sparse(r) for r in Ninv), mu) for N, certs, Ninv, mu in r5) + "]")
    print(",\n".join(rows) + "]")
    def cent_lean(C):
        Xs, crow7, ccol7, irow, icol, Ys, yrow, ycol, jrow, jcol = C
        return "⟨%s, %s, %s, %s, %s, %s, %s, %s, %s, %s⟩" % (
            "[" + ", ".join(lean_mat(X) for X in Xs) + "]",
            lean_list(crow7), lean_list(ccol7), lean_list(irow), lean_list(icol),
            lean_mat(Ys), lean_list(yrow), lean_list(ycol), lean_list(jrow), lean_list(jcol))
    for fi, (d, sE, S, R, Rinv, crow, ccol, Pint, pairs, Nt, r5, r7, r8, uc) in enumerate(out):
        U, urow, ucol, arow, acol = uc
        print("def drU%d : DrUnitary := ⟨%s, %s, %s, %s, %s⟩" % (
            fi, "[" + ", ".join(lean_mat(X) for X in U) + "]",
            lean_list(urow), lean_list(ucol), lean_list(arow), lean_list(acol)))
        for k, C in enumerate(r7):
            print("def drCent%d_%d : DrCent := %s" % (fi, k, cent_lean(C)))
        kq, sJ0, J0i, cq, rel, prow, pcol, rrow, rcol, grow, gcol = r8
        print("def drCentQ%d : DrCent := %s" % (fi, cent_lean(cq)))
        print("def drSiegel%d : DrSiegel := ⟨%d, %d, %s, %s, %s, %s, %s, %s, %s, %s⟩" % (
            fi, kq, sJ0, lean_mat(J0i), lean_mat(rel), lean_list(prow), lean_list(pcol),
            lean_list(rrow), lean_list(rcol), lean_list(grow), lean_list(gcol)))


if __name__ == "__main__":
    main()
