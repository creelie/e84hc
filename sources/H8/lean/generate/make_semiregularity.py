#!/usr/bin/env python3
"""
make_semiregularity.py

Writes the data of item (XIII), the semiregularity map of a sum of line
bundles on a split member, for HodgeObstruction.lean.  The model is that of
code/semiregularity.py, which this script imports: A = X x Xhat with
X = E_i^n, the generators x_1..x_2n, xi_1..xi_2n of H^1(A, Q), and the classes
beta, betahat, ell.

For the map Phi of the lemma on split objects the script uses the splitting of
H^*(A) into the blocks {x_j, x_{n+j}, xi_j, xi_{n+j}}.  In the Hodge basis
P1 = x + i x', Q1 = x - i x', P2 = xi + i xi', Q2 = xi - i xi' of a block,

    2 beta_j = i P1 Q1,   2 betahat_j = i P2 Q2,   2 ell_j = P1 Q2 - P2 Q1,

the even classes e^lambda of a block have coordinates v = (1, a, b, c, ab - c^2)
on (1, B, Bhat, L, V), e^lambda Q1 Q2 = Q1 Q2, and

    2 e^lambda Q1 = (2, 0, -c, -i b),   2 e^lambda Q2 = (0, 2, i a, -c)

on (Q1, Q2, R1 = P1 Q1 Q2, R2 = P2 Q1 Q2).  The columns of Phi are therefore,
up to the order of the tensor factors, Q1 Q2 (x) v^(n-1) (one component for
each block) and (2 e^lambda Q_a) (x) (2 e^lambda Q_b) (x) v^(n-2) (one
component for each pair of blocks), and

    rank Phi = n r_same + C(n, 2) r_cross.

The script checks this against the exact ranks of code/semiregularity.py at
n = 2 and against code/semireg_fast.py at n = 3, and records

  * the six degree four monomials and six coordinates with a nonsingular
    minor, for n = 2, 3, 4;
  * for the six pairs (n, d), two coordinates on which eta^2 and
    gamma^2 + d ell^2 have a nonzero 2 x 2 determinant;
  * the tuples: four classes at n = 2 (ranks 6, 12, 18, 22 for the prefixes),
    ten classes at n = 3 (rank 150), and the explicit object (rank 75);
  * for each component matrix a nonsingular minor modulo 1000033, with i
    sent to 649529;
  * kernel vectors over Z[i] of the component for a pair of blocks, two for
    the four classes at n = 2 and four for the explicit object, with
    coordinates on which they are independent.

Run from the repository root:  python3 lean/generate/make_semiregularity.py
"""
import os
import sys
from fractions import Fraction as Fr
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
import semiregularity as S  # noqa: E402
import semireg_fast as SF  # noqa: E402

P = 1000033
R = 649529
assert P % 4 == 1 and R * R % P == P - 1

TWO = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1)]
THREE = [(0, 0, 1), (0, 0, -1), (0, 1, 0), (0, -1, 0), (1, 0, 0), (-1, 0, 0),
         (0, 0, 2), (0, 0, -2), (0, 1, 1), (0, 1, -1)]
OBJECT = [((3, -1, 3), 1), ((-6, 2, 0), 1), ((3, -1, -3), 1),
          ((-3, 1, -3), -1), ((6, -2, 0), -1), ((-3, 1, 3), -1)]
PAIRS = [(2, 1), (2, 2), (2, 3), (3, 2), (3, 5), (4, 1)]


def gm(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def kron(x, y):
    return [gm(p, q) for p in x for q in y]


def vE(t):
    a, b, c = t
    return [(1, 0), (a, 0), (b, 0), (c, 0), (a * b - c * c, 0)]


def oQ(t):
    a, b, c = t
    return [[(2, 0), (0, 0), (-c, 0), (0, -b)], [(0, 0), (2, 0), (0, a), (-c, 0)]]


def same_cols(n, ts):
    out = []
    for t in ts:
        v = [(1, 0)]
        for _ in range(n - 1):
            v = kron(v, vE(t))
        out.append(v)
    return out


def cross_cols(n, ts):
    out = []
    for t in ts:
        o = oQ(t)
        w = [(1, 0)]
        for _ in range(n - 2):
            w = kron(w, vE(t))
        for a in range(2):
            for b in range(2):
                out.append(kron(kron(o[a], o[b]), w))
    return out


def modp(g):
    return (g[0] + R * g[1]) % P


def pick_minor(cols):
    """Rows (coordinates) and columns (vectors) of a nonsingular minor of
    maximal size modulo P."""
    A = [[modp(x) for x in c] for c in cols]
    used_c = set()
    rows, chosen = [], []
    live = list(range(len(A)))
    B = [r[:] for r in A]
    for j in range(len(A[0]) if A else 0):
        p = next((i for i in live if B[i][j]), None)
        if p is None:
            continue
        live.remove(p)
        rows.append(j)
        chosen.append(p)
        inv = pow(B[p][j], P - 2, P)
        for i in live:
            if B[i][j]:
                f = B[i][j] * inv % P
                B[i] = [(a - f * b) % P for a, b in zip(B[i], B[p])]
    return sorted(rows), sorted(chosen)


def det_mod(M):
    M = [r[:] for r in M]
    n = len(M)
    d = 1
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c]), None)
        if p is None:
            return 0
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d = d * M[c][c] % P
        inv = pow(M[c][c], P - 2, P)
        for i in range(c + 1, n):
            if M[i][c]:
                f = M[i][c] * inv % P
                M[i] = [(a - f * b) % P for a, b in zip(M[i], M[c])]
    return d % P


def minor_ok(cols, rc):
    rows, cs = rc
    if len(rows) != len(cs):
        return False
    return det_mod([[modp(cols[c][r]) for r in rows] for c in cs]) != 0


# Gaussian rationals as pairs of Fractions
def qadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def qmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def qinv(x):
    n = x[0] * x[0] + x[1] * x[1]
    return (x[0] / n, -x[1] / n)


def nullspace(cols):
    """Exact kernel of the matrix with the given columns, over Q(i)."""
    nc = len(cols)
    nr = len(cols[0])
    A = [[(Fr(cols[j][i][0]), Fr(cols[j][i][1])) for j in range(nc)] for i in range(nr)]
    piv, r = [], 0
    for c in range(nc):
        p = next((i for i in range(r, nr) if A[i][c] != (0, 0)), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        iv = qinv(A[r][c])
        A[r] = [qmul(iv, x) for x in A[r]]
        for i in range(nr):
            if i != r and A[i][c] != (0, 0):
                f = A[i][c]
                A[i] = [qadd(x, qmul((-f[0], -f[1]), y)) for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(nc) if c not in piv]
    out = []
    for fcol in free:
        v = [(Fr(0), Fr(0))] * nc
        v[fcol] = (Fr(1), Fr(0))
        for i, c in enumerate(piv):
            v[c] = (-A[i][fcol][0], -A[i][fcol][1])
        den = 1
        for x in v:
            for y in x:
                den = den * y.denominator // gcd(den, y.denominator)
        w = [(int(x[0] * den), int(x[1] * den)) for x in v]
        g = 0
        for x in w:
            g = gcd(g, gcd(abs(x[0]), abs(x[1])))
        out.append([(x[0] // g, x[1] // g) for x in w])
    return out


def bits(k):
    return sum(1 << t for t in k)


def coords(u):
    return {bits(k): c for k, c in u.items()}


def main():
    out = []
    # (A) the six monomials
    keys6 = []
    for n in (2, 3, 4):
        mod = S.Model(n, 2)
        gens = [mod.beta, mod.betahat, mod.ell]
        mons = [coords(S.wedge(gens[i], gens[j])) for i in range(3) for j in range(i, 3)]
        allk = sorted(set().union(*mons))
        cols = [[(m.get(k, (0, 0))[0], 0) for k in allk] for m in mons]
        assert all(m.get(k, (0, 0))[1] == 0 for m in mons for k in allk)
        rows, cs = pick_minor([[(int(x[0]), 0) for x in c] for c in cols])
        assert len(cs) == 6
        keys6.append([allk[r] for r in rows])
    out.append("/-- for `n = 2, 3, 4`, six monomials of degree four on which the six")
    out.append("products of `beta, betahat, ell` have a nonsingular minor. -/")
    out.append("def semMonoKeys : List (List Nat) := [%s]" % ", ".join(
        "[" + ", ".join(map(str, k)) + "]" for k in keys6))
    # (B) eta^2 against gamma^2 + d ell^2
    wit = []
    for n, d in PAIRS:
        mod = S.Model(n, d)
        eta = mod.eta()
        assert coords(eta) == coords(S.eadd(S.escale(S.g(d), mod.beta), mod.betahat))
        gamma = S.eadd(S.escale(S.g(d), mod.beta), S.escale(S.g(-1), mod.betahat))
        mix = coords(S.eadd(S.wedge(gamma, gamma), S.escale(S.g(d), S.wedge(mod.ell, mod.ell))))
        e2 = coords(S.wedge(eta, eta))
        ks = sorted(set(mix) | set(e2))
        found = None
        for t in ks:
            for s in ks:
                at, bt = e2.get(t, (0, 0))[0], mix.get(t, (0, 0))[0]
                as_, bs = e2.get(s, (0, 0))[0], mix.get(s, (0, 0))[0]
                if at * bs - as_ * bt != 0:
                    found = (t, s)
                    break
            if found:
                break
        assert found
        wit.append((n, d) + found)
    out.append("/-- for the six pairs `(n, d)`, two monomials on which `eta^2` and")
    out.append("`gamma^2 + d ell^2` have a nonzero `2 x 2` determinant. -/")
    out.append("def semTensorKeys : List (Nat × Nat × Nat × Nat) := [%s]" % ", ".join(
        "(%d, %d, %d, %d)" % w for w in wit))

    # the ranks: block model against the code
    mod2 = S.Model(2, 2)
    mf3 = SF.Model(3, 3)
    minors2 = []
    for s in range(1, 5):
        ts = TWO[:s]
        sc, cc = same_cols(2, ts), cross_cols(2, ts)
        ms, mc = pick_minor(sc), pick_minor(cc)
        assert minor_ok(sc, ms) and minor_ok(cc, mc)
        rs, rc = len(ms[0]), len(mc[0])
        r, c = S.injectivity(mod2, [S.klass(mod2, t) for t in ts])
        assert (r, c) == (2 * rs + rc, 6 * s), (s, r, rs, rc)
        assert (rs, rc) == ((s, 4 * s) if s <= 3 else (4, 14))
        minors2.append((ms, mc))
    ker2 = nullspace(cross_cols(2, TWO))
    assert len(ker2) == 2
    kr2 = pick_minor(ker2)
    assert len(kr2[0]) == 2 and minor_ok(ker2, kr2)
    cc = cross_cols(2, TWO)
    for k in ker2:
        tot = [(0, 0)] * len(cc[0])
        for j, col in enumerate(cc):
            tot = [(a[0] + b[0], a[1] + b[1]) for a, b in zip(tot, [gm(k[j], x) for x in col])]
        assert all(x == (0, 0) for x in tot)

    sc3, cc3 = same_cols(3, THREE), cross_cols(3, THREE)
    ms3, mc3 = pick_minor(sc3), pick_minor(cc3)
    assert len(ms3[0]) == 10 and len(mc3[0]) == 40
    r, c = SF.injectivity(mf3, [mf3.klass(t) for t in THREE])
    assert (r, c) == (150, 150)

    objt = [t for t, e in OBJECT]
    sco, cco = same_cols(3, objt), cross_cols(3, objt)
    mso, mco = pick_minor(sco), pick_minor(cco)
    assert len(mso[0]) == 5 and len(mco[0]) == 20
    r, c = SF.injectivity(mf3, [mf3.klass(t) for t in objt])
    assert (r, c) == (75, 90) == (3 * 5 + 3 * 20, 90)
    mult = [e for t, e in OBJECT]
    assert all(sum(m * col[k][0] for m, col in zip(mult, sco)) == 0 for k in range(len(sco[0])))
    kero = nullspace(cco)
    assert len(kero) == 4
    kro = pick_minor(kero)
    assert len(kro[0]) == 4 and minor_ok(kero, kro)
    for k in kero:
        assert all(sum(gm(k[j], cco[j][r])[t] for j in range(len(cco))) == 0
                   for r in range(len(cco[0])) for t in (0, 1))

    def lst(x):
        return "[" + ", ".join(map(str, x)) + "]"

    def rc(m):
        return "(%s, %s)" % (lst(m[0]), lst(m[1]))
    out.append("/-- the four classes at `n = 2`, as `(a, b, c)` for `a beta + b betahat + c ell`. -/")
    out.append("def semTwo : List (Int × Int × Int) := [%s]" % ", ".join("(%d, %d, %d)" % t for t in TWO))
    out.append("/-- the ten classes at `n = 3`. -/")
    out.append("def semThree : List (Int × Int × Int) := [%s]" % ", ".join("(%d, %d, %d)" % t for t in THREE))
    out.append("/-- the explicit object: the six classes with their multiplicities. -/")
    out.append("def semObject : List ((Int × Int × Int) × Int) := [%s]" % ", ".join(
        "((%d, %d, %d), %d)" % (t + (e,)) for t, e in OBJECT))
    out.append("/-- for the prefixes of length `1, 2, 3, 4` of `semTwo`: minors (coordinates,")
    out.append("columns) of the component of one block and of the component of the pair. -/")
    out.append("def semMinorsTwo : List ((List Nat × List Nat) × (List Nat × List Nat)) := [%s]" % ", ".join(
        "(%s, %s)" % (rc(a), rc(b)) for a, b in minors2))
    out.append("/-- two kernel vectors over `Z[i]` of the component of the pair, four classes. -/")
    out.append("def semKerTwo : List (List (Int × Int)) := [%s]" % ", ".join(
        "[" + ", ".join("(%d, %d)" % x for x in k) + "]" for k in ker2))
    out.append("def semKerTwoRows : List Nat := %s" % lst(kr2[0]))
    out.append("/-- four kernel vectors over `Z[i]` of the component of a pair, explicit object. -/")
    out.append("def semKerObject : List (List (Int × Int)) := [%s]" % ", ".join(
        "[" + ", ".join("(%d, %d)" % x for x in k) + "]" for k in kero))
    out.append("def semKerObjectRows : List Nat := %s" % lst(kro[0]))
    out.append("/-- the minors of the two components for `semThree` and for the object. -/")
    out.append("def semMinorsThree : (List Nat × List Nat) × (List Nat × List Nat) := (%s, %s)" % (rc(ms3), rc(mc3)))
    out.append("def semMinorsObject : (List Nat × List Nat) × (List Nat × List Nat) := (%s, %s)" % (rc(mso), rc(mco)))
    print("\n".join(out))


if __name__ == "__main__":
    main()
