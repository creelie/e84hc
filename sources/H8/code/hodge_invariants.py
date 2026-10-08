#!/usr/bin/env python3
"""
hodge_invariants.py

How many Hodge classes does an abelian variety of (K,-1,n)-Weil type carry?

For A of (K,-1,n)-Weil type the Hodge classes in H^{2k}(A,Q) are the
invariants of the Hodge group Hg(A).  For A outside a countable union of
proper subvarieties of the Weil family, Hg(A) is the special unitary group
SU(V,H) of the hermitian form, and after complexification SU(V,H) becomes
SL_{2n}(C) acting on V_+ = C^{2n} and on V_- = V_+^dual.  So

    Hdg^k(A) tensor C  =  direct sum over r+s=2k of
                          ( wedge^r V_+  tensor  wedge^s V_+^dual )^{sl_{2n}}

and the whole question is a finite invariant-theory computation, carried out
below exactly over Q.

Method.  Invariants are the weight-zero vectors annihilated by every raising
operator e_i = E_{i,i+1}, 1 <= i <= 2n-1.  The weight-zero subspace of
wedge^r V tensor wedge^s V^dual is spanned by v_T tensor v_U^dual with
1_T - 1_U a multiple of (1,...,1); since the entries lie in {-1,0,1} the
multiple is 0, +1 or -1, so the only possibilities are T = U (needing r = s),
or (T,U) = ([2n], empty), or (T,U) = (empty, [2n]).  The weight-zero space is
therefore tiny and the kernel is computed directly.

Output: the dimension of Hdg^k for every k, for n = 2, 3, 4.
"""

from fractions import Fraction as F
from itertools import combinations


# ----------------------------------------------------------- linear algebra

def nullspace_dim(rows, ncols):
    """Rank-nullity over Q.  rows is a list of lists of Fractions."""
    mat = [list(r) for r in rows]
    rank = 0
    pivot_col = 0
    nrows = len(mat)
    while rank < nrows and pivot_col < ncols:
        piv = None
        for i in range(rank, nrows):
            if mat[i][pivot_col] != 0:
                piv = i
                break
        if piv is None:
            pivot_col += 1
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        pv = mat[rank][pivot_col]
        mat[rank] = [c / pv for c in mat[rank]]
        for i in range(nrows):
            if i != rank and mat[i][pivot_col] != 0:
                f = mat[i][pivot_col]
                mat[i] = [a - f * b for a, b in zip(mat[i], mat[rank])]
        rank += 1
        pivot_col += 1
    return ncols - rank


# ------------------------------------------------------------ wedge helpers

def insert_sign(T, out, into):
    """Sign of replacing element `out` of the sorted tuple T by `into`,
    then re-sorting.  Returns (sign, newT) or (0, None) if `into` is
    already present."""
    if into in T:
        return 0, None
    lst = [a for a in T if a != out]
    # position of `out` in T
    p = T.index(out)
    lst2 = sorted(lst + [into])
    q = lst2.index(into)
    return (-1) ** (p + q), tuple(lst2)


def e_on_wedge(i, T):
    """e_i = E_{i,i+1} acting on v_T in wedge^r V:  v_{i+1} -> v_i."""
    if (i + 1) not in T:
        return []
    s, T2 = insert_sign(T, i + 1, i)
    return [] if s == 0 else [(s, T2)]


def e_on_dualwedge(i, U):
    """e_i acting on v_U^dual in wedge^s V^dual:  v_i^dual -> -v_{i+1}^dual."""
    if i not in U:
        return []
    s, U2 = insert_sign(U, i, i + 1)
    return [] if s == 0 else [(-s, U2)]


# --------------------------------------------------------------- invariants

def invariant_dim(N, r, s):
    """dim of the sl_N invariants in wedge^r C^N tensor wedge^s (C^N)^dual."""
    # weight-zero basis
    basis = []
    if r == s:
        basis = [(T, T) for T in combinations(range(1, N + 1), r)]
    if r == N and s == 0:
        basis = [(tuple(range(1, N + 1)), ())]
    if r == 0 and s == N:
        basis = [((), tuple(range(1, N + 1)))]
    if not basis:
        return 0
    index = {b: k for k, b in enumerate(basis)}

    # image basis (weight of e_i . (weight zero) is alpha_i, a fixed weight)
    rows = []
    for i in range(1, N):
        target = {}
        cols = {}
        for k, (T, U) in enumerate(basis):
            terms = []
            for (sg, T2) in e_on_wedge(i, T):
                terms.append((sg, (T2, U)))
            for (sg, U2) in e_on_dualwedge(i, U):
                terms.append((sg, (T, U2)))
            for sg, key in terms:
                target.setdefault(key, len(target))
                cols.setdefault(key, {})
                cols[key][k] = cols[key].get(k, 0) + sg
        for key, coeffs in cols.items():
            row = [F(0)] * len(basis)
            for k, c in coeffs.items():
                row[k] = F(c)
            rows.append(row)
    if not rows:
        return len(basis)
    return nullspace_dim(rows, len(basis))


def hodge_dims(n):
    """dim Hdg^k(A) for k = 0..2n, for A general of (K,-1,n)-Weil type."""
    N = 2 * n
    out = []
    for k in range(0, 2 * n + 1):
        tot = 0
        detail = []
        for r in range(0, N + 1):
            s = 2 * k - r
            if s < 0 or s > N:
                continue
            dm = invariant_dim(N, r, s)
            if dm:
                detail.append(((r, s), dm))
            tot += dm
        out.append((k, tot, detail))
    return out


if __name__ == "__main__":
    print("Hodge classes on a general abelian variety of Weil type")
    npass = nfail = 0

    for n in (2, 3, 4):
        print("  n = %d   (dim A = %d)" % (n, 2 * n))
        rows = hodge_dims(n)
        for k, tot, detail in rows:
            txt = ", ".join("(%d,%d):%d" % (rs[0], rs[1], dm)
                            for rs, dm in detail)
            print("    k=%d  dim Hdg^k = %d    from %s" % (k, tot, txt))
        # the two assertions
        mid = [t for k, t, _ in rows if k == n][0]
        others = [t for k, t, _ in rows if k != n]
        ok1 = (mid == 3)
        ok2 = all(t == 1 for t in others)
        for name, ok in (("dim Hdg^n = 3", ok1),
                         ("dim Hdg^k = 1 for every k != n", ok2)):
            print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
            if ok:
                npass += 1
            else:
                nfail += 1
        # the three contributing summands at k = n
        det = [d for k, t, d in rows if k == n][0]
        want = sorted([((n, n), 1), ((2 * n, 0), 1), ((0, 2 * n), 1)])
        ok3 = sorted(det) == want
        print("    [%s] the three summands are (n,n), (2n,0), (0,2n)"
              % ("PASS" if ok3 else "FAIL"))
        npass += 1 if ok3 else 0
        nfail += 0 if ok3 else 1

    # the dimension of the Weil family against the dimension of A_{2n}
    print("  moduli dimensions")
    ok = True
    for n in range(1, 9):
        weil = n * n
        ag = n * (2 * n + 1)
        if not (weil <= ag and (weil < ag or n == 0)):
            ok = False
        if n <= 4:
            print("    n=%d: Weil family %d,  A_{2n} %d,  codimension %d"
                  % (n, weil, ag, ag - weil))
    print("    [%s] the Weil family has dimension n^2 inside A_{2n} of "
          "dimension n(2n+1)" % ("PASS" if ok else "FAIL"))
    npass += 1 if ok else 0
    nfail += 0 if ok else 1

    print()
    print("  %d checks passed, %d failed" % (npass, nfail))
    print("  overall: %s" % ("PASS" if nfail == 0 else "FAIL"))
