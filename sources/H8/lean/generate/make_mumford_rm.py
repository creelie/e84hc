#!/usr/bin/env python3
"""
make_mumford_rm.py

Writes the data of item (XLI), the exceptional classes of a Mumford
fourfold as a real multiplication, for HodgeObstruction.lean.  The model is
that of code/mumford_rm.py, which this script imports: V = Q^8 with basis
index 4a + 2b + c, sl(2)^3 acting factorwise, psi = eps (x) eps (x) eps, and
the Clifford algebra C(T, q_lambda) on nine generators with lambda = (1, 2, 5).
It records

  * theta, the invariant vector of wedge^2 V spanning the image of the
    projector onto the trivial summand (as in code/mumford_rm.py), scaled to
    a primitive integer vector;
  * for each block T_i (x) T_j, i < j, nine coordinates on which the nine
    vectors mu(t, s) have a minor nonzero modulo 1000003;
  * the spin lifts as (s, Z) with lift = Z / s, Z an integer element of C(T);
  * thirty-two integer vectors of highest weight (1, 1, 1) in C^+(T), with
    the rows (monomials) and columns of a minor of size 32 nonzero modulo
    1000003;
  * the matrices N_1, N_2, N_3 on their span, defined by
    h_i w_k v_0 = sum_l N_i[l][k] w_l; each has one nonzero entry in every
    column, recorded as (l, N_i[l][k]).

Run from the repository root:  python3 lean/generate/make_mumford_rm.py > out
"""
import os
import sys
from fractions import Fraction as Fr
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
import mumford_rm as M  # noqa: E402

P = 1000003


def lcm(a, b):
    return a * b // gcd(a, b)


def den_of(vals):
    d = 1
    for v in vals:
        d = lcm(d, Fr(v).denominator)
    return d


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


def sparse(d):
    return "[" + ", ".join("(%d, %d)" % (k, v) for k, v in sorted(d.items())) + "]"


def main():
    D = len(M.PAIRS)
    # the projector onto the trivial summand, from the Casimirs
    Cs = [M.casimir(i) for i in range(3)]
    Id = M.eye(D)
    q = [M.mscale(C, Fr(1, 4)) for C in Cs]
    om = [M.madd(Id, qq, Fr(-1)) for qq in q]
    P0 = M.mm(M.mm(om[0], om[1]), om[2])
    Tbasis = [M.on_factor(i, m) for i in range(3) for m in (M.E2, M.F2, M.H2)]
    theta = None
    for c in range(D):
        col = [P0[r][c] for r in range(D)]
        if any(col):
            theta = col
            break
    dt = den_of(theta)
    theta = [x * dt for x in theta]
    g = 0
    for x in theta:
        g = gcd(g, int(x))
    theta = [x / g for x in theta]
    assert all(Fr(x).denominator == 1 for x in theta)
    print("/-- the invariant vector `theta` of `wedge^2 V`, spanning the image of the")
    print("projector onto the trivial summand. -/")
    print("def mrTheta : List Int := [%s]" % ", ".join(str(int(x)) for x in theta))

    # (C): the vectors mu(t, s), t in T_i, s in T_j, carried to wedge^2 V by psi
    def mu_vec(t, s):
        A = M.mm(M.mm(M.tr(t), M.PSI), s)
        Mu = M.madd(A, M.tr(A), Fr(-1))
        Y = M.mm(M.mm(M.PSI, Mu), M.tr(M.PSI))
        return [int(Y[a][b]) for (a, b) in M.PAIRS]
    cols = []
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        vecs = [mu_vec(Tbasis[3 * i + a], Tbasis[3 * j + b]) for a in range(3) for b in range(3)]
        rws, cls = pick_minor([list(r) for r in zip(*vecs)], 9)
        cols.append(sorted(rws))
    print("/-- for the blocks `(i, j) = (0, 1), (0, 2), (1, 2)`, nine coordinates on")
    print("which the nine vectors `mu(t, s)` have a nonsingular minor. -/")
    print("def mrBlockCols : List (List Nat) := [%s]" % ", ".join(
        "[" + ", ".join(map(str, c)) + "]" for c in cols))
    # (E)
    lifts = {(i, nm): M.spin_lift(i, M.tvec(i, nm)) for i in range(3) for nm in "efh"}
    out = []
    for i in range(3):
        for nm in "efh":
            z = lifts[(i, nm)]
            s = den_of(z.values())
            out.append("(%d, %s)" % (s, sparse({k: int(v * s) for k, v in z.items()})))
    print("/-- the spin lifts `(s, Z)`, lift `= Z / s`, in the order `(i, e), (i, f),")
    print("(i, h)`, `i = 0, 1, 2`. -/")
    print("def mrLifts : List (Nat × List (Nat × Int)) := [%s]" % ", ".join(out))
    Dd = len(M.EVEN)
    ops = {k: M.left_cols(v) for k, v in lifts.items()}
    rows = []
    for i in range(3):
        for nm, shift in (("e", 0), ("h", 1)):
            R = {}
            for j, col in enumerate(ops[(i, nm)]):
                for m, c in col.items():
                    R.setdefault(m, {})[j] = R.get(m, {}).get(j, 0) + c
            if shift:
                for j in range(Dd):
                    R.setdefault(M.EVEN[j], {})[j] = R.get(M.EVEN[j], {}).get(j, 0) - 1
            rows += [r for r in R.values() if any(r.values())]
    HW = [{M.EVEN[j]: c for j, c in v.items()} for v in M.sparse_nullspace(rows, Dd)]
    HWi = []
    for w in HW:
        s = den_of(w.values())
        HWi.append({k: int(v * s) for k, v in w.items()})
    mat = [[w.get(m, 0) for w in HWi] for m in M.EVEN]
    hrow, hcol = pick_minor(mat, 32)
    print("/-- the vectors of highest weight `(1, 1, 1)` in `C^+(T)`, and a minor. -/")
    print("def mrHW : List (List (Nat × Int)) := [%s]" % ", ".join(sparse(w) for w in HWi))
    print("def mrHWMinor : List Nat × List Nat := (%s, %s)" % (
        "[" + ", ".join(str(M.EVEN[r]) for r in hrow) + "]", "[" + ", ".join(map(str, hcol)) + "]"))
    # N_i: h_i w_k v_0 = sum_l N[l][k] w_l
    v0 = M.gen(0)
    keys = sorted(set().union(*[w.keys() for w in HWi]))
    Ns = []
    for i in range(3):
        cols = []
        for k in range(32):
            img = M.cmul(M.cmul(M.tvec(i, "h"), HWi[k]), v0)
            # solve img = sum_l c_l w_l over Q
            allk = sorted(set(keys) | set(img))
            A = [[Fr(HWi[l].get(m, 0)) for l in range(32)] + [Fr(img.get(m, 0))] for m in allk]
            n = 32
            r, piv = 0, []
            for c in range(n):
                p = next((t for t in range(r, len(A)) if A[t][c] != 0), None)
                if p is None:
                    continue
                A[r], A[p] = A[p], A[r]
                pv = A[r][c]
                A[r] = [x / pv for x in A[r]]
                for t in range(len(A)):
                    if t != r and A[t][c] != 0:
                        f = A[t][c]
                        A[t] = [x - f * y for x, y in zip(A[t], A[r])]
                piv.append(c)
                r += 1
            assert all(A[t][n] == 0 for t in range(r, len(A)))
            sol = [Fr(0)] * n
            for t, c in enumerate(piv):
                sol[c] = A[t][n]
            cols.append(sol)
        s = den_of([x for col in cols for x in col])
        Nmat = [[int(cols[k][l] * s) for k in range(32)] for l in range(32)]
        Ns.append((s, Nmat))
    for s, Nm in Ns:
        assert s == 1
        assert all(sum(1 for l in range(32) if Nm[l][k]) == 1 for k in range(32))
    print("/-- `N_1, N_2, N_3`, each with one nonzero entry in every column: column `k`")
    print("is `(l, c)` with `N_i w_k = c w_l`. -/")
    print("def mrN : List (List (Nat × Int)) := [%s]" % ", ".join(
        "[" + ", ".join("(%d, %d)" % next((l, Nm[l][k]) for l in range(32) if Nm[l][k])
                        for k in range(32)) + "]" for s, Nm in Ns))

if __name__ == "__main__":
    main()
