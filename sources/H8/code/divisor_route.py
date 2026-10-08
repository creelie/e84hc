#!/usr/bin/env python3
"""
divisor_route.py

The divisor route to the variational statement, at n = 2, on one fixed
polarised lattice.  Take Lambda = O^2, O = Z<1, i, j, ij> with i^2 = -d,
j^2 = 1, and the polarisation E of the quaternionic model at b = 1.  The
lattice (Lambda, E, i) is then one fixed member of the Weil family, and every
statement below is about that fixed lattice.

For a class x in H^2(Lambda, Q) put t(x) = int x eta^3 / int eta^4 and

    I(x) = t(x)^2 int eta^4 - int (x - t(x) eta)^2 eta^2 ,

the Hodge norm of x at any point where x is of type (1,1).  Let R be the
lattice of K-bilinear classes (x(i u, v) = x(u, i v)), where the divisor
classes of the quaternionic points live, and for x in R let phi_x = E^{-1} x,
so that x(u, v) = E(phi_x u, v).

  (R1) R has rank 12 and every x in R is primitive: t(x) = 0;
  (R2) -int x y eta^2 / int eta^4 = tr(phi_x phi_y) / 24 for all x, y in R,
       checked on every pair of basis vectors, so I(x) = tr(phi_x^2)/24 *
       int eta^4 on R;
  (R3) I has signature (8, 4) on R;
  (R4) the pencil x_k(u, v) = E(phi_k u, v), phi_k = left multiplication by
       (2d)^{-1} C_k j with C_k = [[1, k], [k, -1]]: x_k is an integral,
       primitive class in R, x_k = x_0 + k (x_1 - x_0), phi_k^2 =
       beta(k) = (1 + k^2)/(4 d^2), I(x_k) = beta(k) int eta^4 / 3, and
       int eta^4 = 384 d^4;
  (R5) for k = 0..10 the lattice N_k = (Q eta + Q x_k + Q (i.x_k)) cap
       H^2(Lambda, Z) is Z eta/(2d) + Z x_k + Z i.x_k, it is positive
       definite for I, and the minimum mu_k of I on N_k off Q eta, found by
       an exhaustive search, is exactly 32 d^2 (1 + k^2); by the nef bound
       I(D) <= 2 (int D eta^3)^2 / int eta^4 for effective D, every
       effective divisor outside Q eta at a very general point of
       Hdg(x_k) has degree at least sqrt(mu_k int eta^4 / 2);
  (R6) Z x_k + Z i.x_k is saturated for every integer k: the 2x2 minors of
       the matrix with rows x_k, i.x_k are integer polynomials of degree at
       most 2 in k, and the gcd of resultants of pairs of them is 1; checked
       also directly for |k| <= 200;
  (R7) the Lie algebra of the centraliser of {i, phi_{x_k}} in sp(V, E) has
       dimension 10, and its invariants in wedge^2 V^* have dimension 3, for
       k = 0..4: the rank-three statement for NS at a very general point;
  (R8) at k = 0, where beta(0) = (2d)^{-2} is a rational square, a rational
       point J0 of the Siegel locus, and the Lie algebra step: [c, J0] has
       dimension 6 and generates c with its brackets.

The paper proves all of this by hand, for every d; the script checks it
for d = 1, 3.  Everything is exact rational arithmetic; the only floating point is a
square root used to bound an enumeration box, and each bound is widened by
one before use.
"""

import os
import sys
from fractions import Fraction as F
from itertools import product
from math import isqrt, gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quaternionic import Model, matmul, signature, det  # noqa: E402
from quaternionic_divisibility import (form, wedge, integ, K2,  # noqa: E402
                                       int_kernel, saturation)

NP = NF = 0


def check(name, ok, detail=""):
    global NP, NF
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("           " + detail)
    if ok:
        NP += 1
    else:
        NF += 1


def pencil_class(d, k):
    """the class x_k(u, v) = E(phi_k u, v), phi_k = left multiplication by
    (2d)^{-1} C_k j on B^2, C_k = [[1, k], [k, -1]], as 28 coordinates."""
    M = Model(2, d, 1)
    Bq, E = M.B, M.E()
    C = [[F(1, 2 * d), F(k, 2 * d)], [F(k, 2 * d), F(-1, 2 * d)]]
    Phi = [[F(0)] * 8 for _ in range(8)]
    for l in range(2):
        for r in range(4):
            e = [F(0)] * 4
            e[r] = F(1)
            je = Bq.mul(Bq.j(), tuple(e))
            for kk in range(2):
                for t in range(4):
                    Phi[4 * kk + t][4 * l + r] += C[kk][l] * je[t]
    X = matmul([list(r) for r in zip(*Phi)], E)
    return [X[a][b] for (a, b) in K2]


def inverse(M):
    n = len(M)
    A = [[F(v) for v in r] + [F(int(i == j)) for j in range(n)]
         for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [v / pv for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [r[n:] for r in A]


def mat_of(v):
    X = [[F(0)] * 8 for _ in range(8)]
    for (a, b), c in zip(K2, v):
        X[a][b] = F(c)
        X[b][a] = -F(c)
    return X


def vec_of(X):
    return [X[a][b] for (a, b) in K2]


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def scalar(A):
    s = A[0][0]
    ok = all(A[i][j] == (s if i == j else 0)
             for i in range(8) for j in range(8))
    return ok, s


class Lattice:
    def __init__(self, d):
        M = Model(2, d, 1)
        self.d = d
        self.Li = M.left(M.B.i())
        self.E = M.E()
        self.Einv = inverse(self.E)
        self.eta = form(self.E)
        self.e2 = wedge(self.eta, self.eta)
        self.e4 = integ(wedge(self.e2, self.e2))

    def R_basis(self):
        rows = []
        for r in range(8):
            for c in range(8):
                coeffs = []
                for (a, b) in K2:
                    X = [[0] * 8 for _ in range(8)]
                    X[a][b], X[b][a] = 1, -1
                    v = (sum(self.Li[k][r] * X[k][c] for k in range(8))
                         - sum(X[r][k] * self.Li[k][c] for k in range(8)))
                    coeffs.append(int(v))
                if any(coeffs):
                    rows.append(coeffs)
        return int_kernel(rows)

    def phi(self, v):
        return matmul(self.Einv, mat_of(v))

    def t(self, v):
        return integ(wedge(form(mat_of(v)), wedge(self.eta, self.e2))) \
            / self.e4

    def pair(self, u, v):
        """the bilinear form of I."""
        x, y = form(mat_of(u)), form(mat_of(v))
        tu, tv = self.t(u), self.t(v)
        xy = integ(wedge(wedge(x, y), self.e2))
        # I(x) = t^2 e4 - int (x - t eta)^2 eta^2 = 2 t^2 e4 - int x^2 eta^2
        return 2 * tu * tv * self.e4 - xy

    def times_i(self, v):
        """the class (i.x)(u, w) = x(i u, w)."""
        X = mat_of(v)
        Y = matmul([list(r) for r in zip(*self.Li)], X)
        return vec_of(Y)


def min_off_eta(L, basis, eta_v):
    """minimum of I on the lattice spanned by basis, off Q eta."""
    G = [[L.pair(a, b) for b in basis] for a in basis]
    n = len(basis)
    Gi = inverse(G)

    def val(c):
        return sum(c[a] * c[b] * G[a][b] for a in range(n) for b in range(n))

    def on_eta(c):
        w = [sum(c[k] * basis[k][t] for k in range(n)) for t in range(28)]
        return all(w[t] * eta_v[s] == w[s] * eta_v[t]
                   for s in range(28) for t in range(28))

    best = min(G[k][k] for k in range(n) if not on_eta(
        [int(k == j) for j in range(n)]))
    box = [isqrt(int(best * Gi[k][k]) + 1) + 1 for k in range(n)]
    for c in product(*[range(-b, b + 1) for b in box]):
        if any(c) and not on_eta(c):
            v = val(c)
            if v < best:
                best = v
    return best, G


def resultant(P, Q):
    """an integer in the ideal (P, Q) of Z[k]: the resultant taken with the
    actual degrees, or gcd(P, Q) when both are constants.  It is divisible
    by gcd(P(k), Q(k)) for every integer k."""
    def strip(A):
        A = list(A)
        while len(A) > 1 and A[-1] == 0:
            A.pop()
        return A
    P, Q = strip(P), strip(Q)
    m, n = len(P) - 1, len(Q) - 1
    if m == 0 and n == 0:
        # the ideal (P, Q) is then (gcd(P, Q)) itself
        return gcd(P[0], Q[0])
    size = m + n
    S = []
    for r in range(n):
        row = [0] * size
        for c, a in enumerate(reversed(P)):
            row[r + c] = a
        S.append(row)
    for r in range(m):
        row = [0] * size
        for c, a in enumerate(reversed(Q)):
            row[r + c] = a
        S.append(row)
    return int(det([[F(v) for v in row] for row in S]))


def index_bound(L, x, y):
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
    N = 0
    for i in range(len(polys)):
        for j in range(i + 1, min(len(polys), i + 40)):
            r = resultant(polys[i], polys[j])
            if r:
                N = gcd(N, abs(r))
    direct = True
    for k in range(-200, 201):
        G = 0
        for c0, c1, c2 in polys:
            G = gcd(G, c0 + c1 * k + c2 * k * k)
        direct = direct and G != 0 and N % G == 0
    return N, direct


def nullspace(rows, m):
    R = [[F(v) for v in r] for r in rows]
    piv, row = [], 0
    for c in range(m):
        p = next((i for i in range(row, len(R)) if R[i][c] != 0), None)
        if p is None:
            continue
        R[row], R[p] = R[p], R[row]
        pv = R[row][c]
        R[row] = [v / pv for v in R[row]]
        for i in range(len(R)):
            if i != row and R[i][c] != 0:
                f = R[i][c]
                R[i] = [a - f * b for a, b in zip(R[i], R[row])]
        piv.append(c)
        row += 1
    out = []
    for fc in (c for c in range(m) if c not in piv):
        v = [F(0)] * m
        v[fc] = F(1)
        for i, p in enumerate(piv):
            v[p] = -R[i][fc]
        out.append(v)
    return out


def centraliser_invariants(L, xk):
    """dim of {X in sp(V,E): X i = i X, X phi = phi X} and of its
    invariants in wedge^2 V^*."""
    phi = L.phi(xk)
    Li, E = L.Li, L.E
    rows = []
    for (A, sym) in ((E, True), (Li, False), (phi, False)):
        for r in range(8):
            for c in range(8):
                row = [F(0)] * 64
                for a in range(8):
                    for b in range(8):
                        # X[a][b] is unknown a*8+b
                        v = F(0)
                        if sym:      # X^T E + E X
                            if b == r:
                                v += A[a][c]
                            if b == c:
                                v += A[r][a]
                        else:        # X A - A X
                            if a == r:
                                v += A[b][c]
                            if b == c:
                                v -= A[r][a]
                        row[a * 8 + b] = v
                if any(row):
                    rows.append(row)
    basis = nullspace(rows, 64)
    Xs = [[[v[a * 8 + b] for b in range(8)] for a in range(8)] for v in basis]
    rows2 = []
    for X in Xs:
        for (p, q) in K2:
            row = []
            for (a, b) in K2:
                Y = [[F(0)] * 8 for _ in range(8)]
                Y[a][b], Y[b][a] = F(1), F(-1)
                # (X^T Y + Y X)[p][q]
                v = sum(X[t][p] * Y[t][q] for t in range(8)) + \
                    sum(Y[p][t] * X[t][q] for t in range(8))
                row.append(v)
            if any(row):
                rows2.append(row)
    inv = nullspace(rows2, 28)
    return len(Xs), len(inv)


def centraliser_basis(L, xk):
    """basis of {X in sp(V,E): X i = i X, X phi = phi X} as 8 x 8 matrices."""
    phi = L.phi(xk)
    Li, E = L.Li, L.E
    rows = []
    for (A, sym) in ((E, True), (Li, False), (phi, False)):
        for r in range(8):
            for c in range(8):
                row = [F(0)] * 64
                for a in range(8):
                    for b in range(8):
                        v = F(0)
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
                        row[a * 8 + b] = v
                if any(row):
                    rows.append(row)
    basis = nullspace(rows, 64)
    return [[[v[a * 8 + b] for b in range(8)] for a in range(8)] for v in basis]


def bracket(X, Y):
    return [[sum(X[i][t] * Y[t][j] - Y[i][t] * X[t][j] for t in range(8))
             for j in range(8)] for i in range(8)]


def span_dim(mats):
    if not mats:
        return 0
    return len(mats) - len(nullspace([[m[a][b] for m in mats] for a in range(8)
                                      for b in range(8)], len(mats)))


def cartan_generation(L, xk, J0):
    """With c the centraliser Lie algebra and J0 a point of the Siegel locus
    inside it, p = [c, J0] is the tangent space to the locus.  Returns
    (dim c, dim p, dim (p + [p, p])).  The claim used in the paper is that the
    last equals the first: p and its brackets generate c."""
    c = centraliser_basis(L, xk)
    p = [bracket(X, J0) for X in c]
    dp = span_dim(p)
    pp = p + [bracket(A, B) for A in p for B in p]
    return len(c), dp, span_dim(pp)


def siegel_point(L, xk):
    """A rational complex structure J0 commuting with i and phi, compatible
    with E, when phi^2 is a rational square: J0 = J on V_+ = ker(phi - r),
    extended by J(i w) = i J w, with J built from a symplectic basis of V_+."""
    phi = L.phi(xk)
    okr, r2 = scalar(matmul(phi, phi))
    from math import isqrt
    num, den = r2.numerator, r2.denominator
    if not okr or isqrt(num) ** 2 != num or isqrt(den) ** 2 != den:
        return None
    r = F(isqrt(num), isqrt(den))
    # V_+ = kernel of (phi - r)
    rows = [[phi[a][b] - (r if a == b else 0) for b in range(8)] for a in range(8)]
    Vp = nullspace(rows, 8)          # 4 vectors
    # symplectic basis of V_+ for E by Gram-Schmidt
    def Ev(u, v):
        return sum(u[a] * L.E[a][b] * v[b] for a in range(8) for b in range(8))
    basis = [list(v) for v in Vp]
    e1 = basis[0]
    f1 = next(v for v in basis[1:] if Ev(e1, v) != 0)
    f1 = [t / Ev(e1, f1) for t in f1]
    rest = []
    for v in basis:
        w = [v[a] - Ev(v, f1) * e1[a] + Ev(v, e1) * f1[a] for a in range(8)]
        if any(w):
            rest.append(w)
    # pick e2, f2 in rest independent of e1,f1
    e2 = next(w for w in rest if any(w) and span_rank([e1, f1, w]) == 3)
    f2 = next(w for w in rest if Ev(e2, w) != 0)
    f2 = [t / Ev(e2, f2) for t in f2]
    # J: e_k -> f_k, f_k -> -e_k on V_+; on V_- = i V_+: J(i w) = i J w
    Li = L.Li
    def apply_i(v):
        return [sum(Li[a][b] * v[b] for b in range(8)) for a in range(8)]
    cols = [e1, e2, f1, f2, apply_i(e1), apply_i(e2), apply_i(f1), apply_i(f2)]
    imgs = [f1, f2, [-t for t in e1], [-t for t in e2],
            apply_i(f1), apply_i(f2), apply_i([-t for t in e1]), apply_i([-t for t in e2])]
    B = [[cols[j][a] for j in range(8)] for a in range(8)]
    Im = [[imgs[j][a] for j in range(8)] for a in range(8)]
    J0 = matmul(Im, inverse(B))
    return J0


def span_rank_vec(vs):
    """rank of a list of vectors of equal length."""
    m = len(vs[0])
    return len(vs) - len(nullspace([[v[t] for v in vs] for t in range(m)],
                                   len(vs)))


def det3(A, Bv):
    """the determinant of the change of basis between two bases of the same
    rank-3 lattice, A = (a_1, a_2, a_3) and B: solve A = M B and return det M."""
    rows = []
    for t in range(len(Bv[0])):
        rows.append([Bv[0][t], Bv[1][t], Bv[2][t]])
    # pick three independent coordinates
    idx = []
    for t in range(len(rows)):
        cand = idx + [t]
        sub = [[rows[u][c] for c in range(3)] for u in cand]
        if len(nullspace([[sub[r][c] for r in range(len(cand))] for c in range(3)],
                         len(cand))) == 0:
            idx = cand
        if len(idx) == 3:
            break
    Bm = [[F(rows[u][c]) for u in idx] for c in range(3)]
    Am = [[F(A[c][u]) for u in idx] for c in range(3)]
    M = matmul(Am, inverse(Bm))
    return det(M)


def span_rank(vs):
    return len(vs) - len(nullspace([[v[a] for v in vs] for a in range(8)], len(vs)))


if __name__ == "__main__":
    print("(XXIV) the divisor route at n = 2 on a fixed polarised lattice")
    for d in (1, 3):
        L = Lattice(d)
        R = L.R_basis()
        print("  d = %d, int eta^4 = %s" % (d, L.e4))

        ok = len(R) == 12 and all(L.t(v) == 0 for v in R)
        check("(R1) R has rank 12 and consists of primitive classes", ok)

        P = [L.phi(v) for v in R]
        ok = True
        for a in range(12):
            for b in range(a, 12):
                lhs = -integ(wedge(wedge(form(mat_of(R[a])),
                                         form(mat_of(R[b]))), L.e2)) / L.e4
                rhs = trace(matmul(P[a], P[b])) / 24
                ok = ok and lhs == rhs
        check("(R2) -int x y eta^2 / int eta^4 = tr(phi_x phi_y)/24 on all "
              "78 basis pairs", ok)

        G = [[L.pair(a, b) for b in R] for a in R]
        sg = signature(G)
        check("(R3) I has signature (8, 4) on R", sg == (8, 4),
              "signature %s" % (sg,))

        x0, x1 = pencil_class(d, 0), pencil_class(d, 1)
        x = [int(v) for v in x0]
        y = [int(b - a) for a, b in zip(x0, x1)]
        inR = span_rank_vec(R + [x]) == 12 and span_rank_vec(R + [y]) == 12
        direct = L.e4 == 384 * d ** 4 and inR
        for k in (-7, -1, 0, 1, 2, 5, 13, 40):
            xk = pencil_class(d, k)
            direct = direct and xk == [a + k * b for a, b in zip(x, y)]
            direct = direct and all(v.denominator == 1 for v in xk)
            g = 0
            for v in xk:
                g = gcd(g, int(v))
            direct = direct and g == 1
            pk = L.phi(xk)
            s_ok, s = scalar(matmul(pk, pk))
            direct = direct and s_ok and s == F(1 + k * k, 4 * d * d)
            direct = direct and L.pair(xk, xk) == s * L.e4 / 3
        check("(R4) the pencil x_k = E(phi_k ., .): integral, primitive, in R, "
              "phi_k^2 = (1 + k^2)/(4 d^2)", direct,
              "int eta^4 = 384 d^4 and I(x_k) = beta(k) int eta^4 / 3, "
              "checked at eight values of k")

        eta_v = vec_of(L.E)
        rows = []
        exact = True
        for k in range(0, 11):
            xk = [int(a + k * b) for a, b in zip(x, y)]
            ik = [int(v) for v in L.times_i(xk)]
            N = saturation([eta_v, xk, ik])
            mine = [[v / (2 * d) for v in eta_v], xk, ik]
            same = (span_rank_vec(N + mine) == 3 and
                    abs(det3(N, mine)) == 1)
            mu, Gk = min_off_eta(L, N, eta_v)
            pd = signature(Gk) == (3, 0)
            exact = exact and same and pd and mu == 32 * d * d * (1 + k * k)
            deg2 = mu * L.e4 / 2
            rows.append("k=%2d  beta=%-7s  mu_k=%-8s  deg >= sqrt(%s)"
                        % (k, F(1 + k * k, 4 * d * d), mu, deg2))
        for r in rows:
            print("      " + r)
        check("(R5) N_k = Z eta/(2d) + Z x_k + Z i.x_k, positive definite, "
              "and mu_k = 32 d^2 (1 + k^2) for k = 0..10", exact)

        N, direct = index_bound(L, x, y)
        check("(R6) Z x_k + Z i.x_k is saturated for every integer k",
              direct and N == 1,
              "the gcd of resultants of pairs of minors is %d" % N)

        dims = set(centraliser_invariants(L, [a + k * b for a, b in
                                               zip(x, y)])
                   for k in range(5))
        check("(R7) centraliser of {i, phi} in sp(V,E) has dimension 10 and "
              "3 invariants in wedge^2 V^*", dims == {(10, 3)},
              "dimensions %s for k = 0..4" % sorted(dims))

        # (R8) the Lie algebra step behind the proof of the rank-three
        # statement: at a point J0 of the Siegel locus, the tangent directions
        # p = [c, J0] and their brackets generate the whole centraliser c, so
        # a class fixed by every point of the locus is fixed by all of c.  A
        # rational J0 exists at k = 0, where beta(0) = (2d)^{-2} is a square.
        xk = x
        J0 = siegel_point(L, xk)
        if J0 is None:
            check("(R8) a rational point of the Siegel locus at k = 0", False)
        else:
            okJ = all((matmul(J0, J0)[a][b] == (-1 if a == b else 0)) for a in range(8) for b in range(8))
            JtEJ = matmul([list(r) for r in zip(*J0)], matmul(L.E, J0))
            okE = all(JtEJ[a][b] == L.E[a][b] for a in range(8) for b in range(8))
            comm = all(matmul(J0, L.Li)[a][b] == matmul(L.Li, J0)[a][b] for a in range(8) for b in range(8))
            phi = L.phi(xk)
            comm2 = all(matmul(J0, phi)[a][b] == matmul(phi, J0)[a][b] for a in range(8) for b in range(8))
            dc, dp, dg = cartan_generation(L, xk, J0)
            check("(R8) at k = 0 the tangent space p = [c, J0] of the Siegel locus "
                  "has dimension 6 and p + [p, p] is all of c",
                  okJ and okE and comm and comm2 and (dc, dp, dg) == (10, 6, 10),
                  "J0^2 = -1, E-compatible, commutes with i and phi; "
                  "dim c = %d, dim p = %d, dim(p + [p,p]) = %d" % (dc, dp, dg))

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    sys.exit(0 if NF == 0 else 1)
