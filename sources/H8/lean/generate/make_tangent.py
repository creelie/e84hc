#!/usr/bin/env python3
"""
make_tangent.py

Writes the data of Section 59 of HodgeObstruction.lean (item (XVI), the
annihilator as the tangent space), from the model of code/weil_tangent.py.
For each case (n, seed) it records

  * a basis of P' = P^perp in V_- (P itself is recomputed in Lean by the
    formula of weil_tangent.Weil._choose_P);
  * a basis of the polarisation-preserving deformations;
  * D and D times the inverse of the matrix whose columns are
    H^{1,0} + H^{0,1};
  * the deformations, as combinations of that basis, that contract the whole
    Weil line to zero;
  * for the E-dual bases of P and of a second basis of P inside Q', D' and
    D' times the inverse of the pairing matrix.

All of it is exact; Lean checks every property it relies on.

Run from the repository root:  python3 lean/generate/make_tangent.py > out
"""
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "code"))
import weil_tangent as WT  # noqa: E402
from emit import gauss_int, lean_sparse_gcombo, parts, lcm  # noqa: E402
from fractions import Fraction as Fr  # noqa: E402

CASES = [(2, 0), (3, 0), (4, 0), (2, 1), (2, 2), (3, 1)]


def scaled_inverse(M):
    """D and D * M^{-1} with Gaussian integer entries"""
    W0 = WT.Weil.__new__(WT.Weil)
    inv = WT.Weil._inverse(W0, M)
    den = 1
    for r in inv:
        for x in r:
            a, b = parts(x)
            den = lcm(den, lcm(a.denominator, b.denominator))
    out = [[(int(parts(x)[0] * den), int(parts(x)[1] * den)) for x in r] for r in inv]
    return den, out


def build(n, seed):
    W = WT.Weil(n, seed=seed)
    # replace P' by an integral basis of the same space, and rebuild
    W.Pp = [[WT.G(a, b) for a, b in gauss_int(v)] for v in W.Pp]
    W.Q = [W.conj(v) for v in W.Pp]
    W.H10 = W.P + W.Pp
    W.H01 = W.Q + W.Qp
    m = W.m
    S = [[WT.G(a, b) for a, b in gauss_int(v)] for v in WT.symmetric_space(W)]
    cols = W.H10 + W.H01
    Mrows = [[cols[j][i] for j in range(W.N)] for i in range(W.N)]
    D, inv = scaled_inverse(Mrows)
    # part (d): the kernel of S -> (contraction into omega_1, omega_2)
    w1, w2 = W.omegas()
    imgs = []
    for v in S:
        c = W.deformation_matrix(v)
        imgs.append((W.contract(c, w1), W.contract(c, w2)))
    keys = sorted({k for a, b in imgs for k in list(a) + list(b)})
    idx = {k: i for i, k in enumerate(keys)}
    mrows = [[WT.ZERO] * len(S) for _ in range(2 * len(keys))]
    for j, (a, b) in enumerate(imgs):
        for k, c in a.items():
            mrows[idx[k]][j] = c
        for k, c in b.items():
            mrows[len(keys) + idx[k]][j] = c
    ker = [gauss_int(c) for c in WT.nullspace(mrows, len(S))]
    assert len(ker) == n * n
    # part (e): the E-dual bases
    P2 = [W.P[0]] + [[x + y for x, y in zip(W.P[a], W.P[a - 1])] for a in range(1, n)]
    duals = []
    for Pb in (W.P, P2):
        D2, inv2 = scaled_inverse([[W.E(p, q) for q in W.Qp] for p in Pb])
        duals.append((D2, inv2))
    return W, S, D, inv, ker, duals


def sparse_rows(rows):
    """rows of Gaussian integers as sparse lists (index, re, im)"""
    return "[\n" + ",\n".join("  " + lean_sparse_gcombo(r) for r in rows) + "]"


def main():
    out = []
    names = []
    for n, seed in CASES:
        W, S, D, inv, ker, duals = build(n, seed)
        tag = "wt%ds%d" % (n, seed)
        names.append((tag, n, seed))
        out.append("def %sPp : List (List (Nat × Int × Int)) := %s" % (tag, sparse_rows([gauss_int(v) for v in W.Pp])))
        out.append("def %sS : List (List (Nat × Int × Int)) := %s" % (tag, sparse_rows([gauss_int(v) for v in S])))
        out.append("def %sD : Int := %d" % (tag, D))
        out.append("def %sInv : List (List (Nat × Int × Int)) := %s" % (tag, sparse_rows(inv)))
        out.append("def %sKer : List (List (Nat × Int × Int)) := [\n%s]"
                   % (tag, ",\n".join("  " + lean_sparse_gcombo(c) for c in ker)))
        for k, (D2, inv2) in enumerate(duals):
            out.append("def %sDual%d : Int × List (List (Nat × Int × Int)) := (%d, %s)"
                       % (tag, k, D2, sparse_rows(inv2)))
        out.append("")
    out.append("/-- the cases `(n, seed, P', S, D, D M^(-1), kernel, duals)`. -/")
    out.append("def wtCases : List (Nat × Nat × WtSp × WtSp × Int × WtSp × WtSp"
               " × (Int × WtSp) × (Int × WtSp)) := [")
    out.append(",\n".join("  (%d, %d, %sPp, %sS, %sD, %sInv, %sKer, %sDual0, %sDual1)"
                          % (n, s, t, t, t, t, t, t, t) for t, n, s in names) + "]")
    print("\n".join(out))


if __name__ == "__main__":
    main()
