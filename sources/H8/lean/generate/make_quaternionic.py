#!/usr/bin/env python3
"""
make_quaternionic.py

Writes the certificates of part (D6) of item (XXIII), the integral Weil
lattice of a quaternionic point and its divisor sublattice, for
HodgeObstruction.lean.  The model is that of code/quaternionic_divisibility.py,
which this script imports: Lambda_b = O_b^2, O_b = Z<1, i, j, ij>, i^2 = -d,
j^2 = b, E_b(x, y) = sum_k a_k trd(conj(x_k) i y_k), g = E(j., .),
lam = -g(i., .)/d, Z = g^2 - d lam^2, Z' = 2 g lam.  A 2-form or 4-form on
the eight generators is a sparse list of (bit mask, coefficient).

For each (d, weights, b) it records
  * NS, three integral 2-forms with s NS_i = x eta + y g + z (d lam), and
    integer rows R with NS_i . R_j = delta_ij, so NS is the saturation of
    the span of eta, g, lam;
  * W, two integral 4-forms with s W_i = x (d Z) + y (d Z'), and a left
    inverse, so W is the saturation of the Weil plane;
  * the coefficient vectors K in Z^6 of the products NS_a NS_c (a <= c) that
    land in Q W, each with the integers (x, y) of its image in the basis W,
    a left inverse of K, two coordinates (t1, t2) on which W has a nonzero
    2 x 2 minor, and rows and columns of a nonzero minor of size 6 - #K of
    the matrix c -> P(sum c_j NS_a NS_c), P(v) = Delta v - det(v, W_2) W_1 -
    det(W_1, v) W_2 the projection that vanishes exactly on Q W.

Run from the repository root:  python3 lean/generate/make_quaternionic.py > out
"""
import os
import sys
from fractions import Fraction as F
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
sys.path.insert(0, HERE)
import quaternionic_divisibility as Q  # noqa: E402
from make_sextic_lattice import left_inverse  # noqa: E402
from transport_growth import det_q  # noqa: E402

K2, K4 = Q.K2, Q.K4


def mask(I):
    return sum(1 << i for i in I)


def sparse(v, keys):
    return [(mask(k), int(x)) for k, x in zip(keys, v) if x != 0]


def lean_sparse(s):
    return "[" + ", ".join("(%d, %d)" % t for t in s) + "]"


def solve_combo(target, gens):
    """(s, coefficients) with s target = sum c_i gens_i, integers"""
    m = len(target)
    A = [[F(g[t]) for g in gens] + [F(target[t])] for t in range(m)]
    # least squares free: Gaussian elimination
    r, piv = 0, []
    nc = len(gens)
    for c in range(nc):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    for i in range(r, m):
        assert A[i][nc] == 0
    sol = [F(0)] * nc
    for i, c in enumerate(piv):
        sol[c] = A[i][nc]
    den = 1
    for x in sol:
        den = den * x.denominator // Q.gcd(den, x.denominator)
    return den, [int(x * den) for x in sol]


def case(d, w, b):
    eta, g, lam, Z, Zp = Q.model(d, b, w)
    lamD = {k: v * d for k, v in lam.items()}
    dZ = {k: v * d for k, v in Z.items()}
    dZp = {k: v * d for k, v in Zp.items()}
    NS = Q.saturation([Q.vec(eta, K2), Q.vec(g, K2), Q.vec(lam, K2)])
    gens2 = [Q.vec(eta, K2), Q.vec(g, K2), Q.vec(lamD, K2)]
    ns_cert = [solve_combo(v, gens2) for v in NS]
    R_ns = left_inverse([[NS[i][t] for i in range(len(NS))] for t in range(len(K2))])
    Zv, Zpv = Q.vec(dZ, K4), Q.vec(dZp, K4)
    W = Q.saturation([Zv, Zpv])
    w_cert = [solve_combo(v, [Zv, Zpv]) for v in W]
    R_w = left_inverse([[W[i][t] for i in range(2)] for t in range(len(K4))])
    NSf = [Q.unvec(v, K2) for v in NS]
    pairs = [(a, c) for a in range(3) for c in range(a, 3)]
    prods = [Q.vec(Q.wedge(NSf[a], NSf[c]), K4) for a, c in pairs]
    # coordinates with a nonzero 2 x 2 minor of W
    t1, t2 = next((s, t) for s, t in combinations(range(len(K4)), 2)
                  if W[0][s] * W[1][t] - W[0][t] * W[1][s] != 0)
    Delta = W[0][t1] * W[1][t2] - W[0][t2] * W[1][t1]

    def P(v):
        a = v[t1] * W[1][t2] - v[t2] * W[1][t1]      # det(v, W_2)
        c = W[0][t1] * v[t2] - W[0][t2] * v[t1]      # det(W_1, v)
        return [Delta * v[t] - a * W[0][t] - c * W[1][t] for t in range(len(K4))]
    Pm = [P(p) for p in prods]                      # 6 vectors of length 70
    # kernel of c -> sum c_j Pm_j
    Mt = [[int(Pm[j][t]) for j in range(6)] for t in range(len(K4))]
    Mt = [r for r in Mt if any(r)]
    Kb = Q.int_kernel(Mt) if Mt else [[int(i == j) for j in range(6)] for i in range(6)]
    k = len(Kb)
    xy = []
    for c in Kb:
        v = [sum(c[j] * prods[j][t] for j in range(6)) for t in range(len(K4))]
        s, (x, y) = solve_combo(v, W)
        assert s == 1
        xy.append((x, y))
    R_k = left_inverse([[Kb[i][j] for i in range(k)] for j in range(6)]) if k else []
    # a nonzero minor of size 6 - k of the 70 x 6 matrix Pm^T, by elimination
    need = 6 - k
    full = [[F(Pm[j][t]) for j in range(6)] for t in range(len(K4))]
    rows, cols = [], []
    M = [r[:] for r in full]
    for c in range(6):
        p = next((t for t in range(len(K4)) if t not in rows and M[t][c] != 0), None)
        if p is None:
            continue
        rows.append(p)
        cols.append(c)
        for t in range(len(K4)):
            if t != p and M[t][c] != 0:
                f = M[t][c] / M[p][c]
                M[t] = [x - f * y for x, y in zip(M[t], M[p])]
    assert len(rows) == need
    assert det_q([[full[r][c] for c in cols] for r in rows]) != 0
    idx = Q.covolume2([[sum(c[j] * prods[j][t] for j in range(6)) for t in range(len(K4))]
                       for c in Kb])
    a = w if w else [1, 1]
    assert idx == 2 * (a[0] * a[1]) ** 2, (d, w, b, idx)
    return dict(
        NS=[sparse(v, K2) for v in NS], ns_cert=ns_cert,
        R_ns=[[(mask(K2[t]), v) for t, v in r] for r in R_ns],
        W=[sparse(v, K4) for v in W], w_cert=w_cert,
        R_w=[[(mask(K4[t]), v) for t, v in r] for r in R_w],
        K=Kb, xy=xy, R_k=R_k, t=(mask(K4[t1]), mask(K4[t2])),
        rows=[mask(K4[r]) for r in rows], cols=list(cols), idx=idx)


def main():
    out = ["/-- (D6): `(d, weights, b, NS, certificates, R_NS, W, certificates, R_W,",
           "K, images, R_K, (t1, t2), minor rows, minor columns, index)`. -/",
           "def qdCases : List QdCase := ["]
    rows = []
    for d in (1, 2, 3, 7):
        for w in (None, [1, 3], [2, 5]):
            a = w if w else [1, 1]
            for b in (1, 2, 3, 5, 7, 11, 13):
                c = case(d, w, b)
                rows.append("  ⟨%d, %d, %d, %d, [%s], [%s], [%s], [%s], [%s], [%s], [%s], [%s], [%s], (%d, %d), %s, %s, %d⟩" % (
                    d, a[0], a[1], b,
                    ", ".join(lean_sparse(v) for v in c["NS"]),
                    ", ".join("(%d, %d, %d, %d)" % (s, x, y, z) for s, (x, y, z) in c["ns_cert"]),
                    ", ".join(lean_sparse(r) for r in c["R_ns"]),
                    ", ".join(lean_sparse(v) for v in c["W"]),
                    ", ".join("(%d, %d, %d)" % (s, x, y) for s, (x, y) in c["w_cert"]),
                    ", ".join(lean_sparse(r) for r in c["R_w"]),
                    ", ".join("[" + ", ".join(map(str, v)) + "]" for v in c["K"]),
                    ", ".join("(%d, %d)" % t for t in c["xy"]),
                    ", ".join(lean_sparse(r) for r in c["R_k"]),
                    c["t"][0], c["t"][1], list(c["rows"]), c["cols"], c["idx"]))
    out.append(",\n".join(rows) + "]")
    print("\n".join(out))


if __name__ == "__main__":
    main()
