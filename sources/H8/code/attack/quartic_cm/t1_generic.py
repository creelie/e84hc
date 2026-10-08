#!/usr/bin/env python3
"""
t1_generic.py -- the Hodge-generic member of an (F,2,delta)-Weil family, F a
quartic CM field.  Exact.

For each field F and each hermitian form H = diag(h1, h2, -h3, -h4) (h_i in
F0 totally positive, discriminant delta = h1 h2 h3 h4) on V = F^4 = H^1,
with xi = r (r^2 = -D, totally imaginary) and E = Tr_{F/Q}(xi H):

 (1) E is alternating and nondegenerate on V = Q^16;
 (2) su(V,H) (as a Q-Lie algebra) has Q-dimension 30 and preserves E;
 (3) W_F = {balanced lift of c e0^e1^e2^e3 : c in F} has Q-dimension 4 and is
     killed by all of su(V,H) (so it consists of Hodge classes on every member);
 (4) invariants of su(V,H):
        in wedge^2 V : exactly 2  (the F0-twisted polarisations),
        in wedge^4 V : exactly 7  (3 Lefschetz products + 4 Weil),
     lower bound by explicit exact invariants, upper bound by the kernel mod p
     of three elements of su(V,H) (kernel of a subset of the equations, mod p,
     contains the kernel of all of them over Q);
 (5) W_F meets the span of products of the degree-2 invariants in 0: the Weil
     classes are exceptional at a member with Hodge group Res SU(V,H).
"""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1lib import *

FIELDS = [
    (5, Fr(5, 2), Fr(1, 2), "Q(zeta_5)  [cyclic, no imag. quadratic subfield]"),
    (2, 1, 0, "Q(zeta_8)=Q(i,sqrt2)  [biquadratic]"),
    (3, 1, 0, "Q(zeta_12)=Q(i,sqrt3)  [biquadratic]"),
    (2, 3, 1, "Q(sqrt(-(3+sqrt2)))  [non-Galois, D4 closure]"),
]


def herm_E(Fd, hdiag, xi):
    """16x16 rational Gram matrix of E(x,y) = Tr(xi sum_i x_i h_i conj(y_i))"""
    n = len(hdiag)
    N = 4 * n
    Eq = [[Fr(0)] * N for _ in range(N)]
    for i in range(n):
        for k in range(4):
            for l in range(4):
                x = Fd.basis[k]
                y = Fd.basis[l]
                val = Fd.tr(Fd.mul(xi, Fd.mul(x, Fd.mul(hdiag[i], Fd.conj(y)))))
                Eq[4 * i + k][4 * i + l] = val
    return Eq


def su_basis(Fd, hdiag):
    """Q-basis of su(V,H) = {X : H X + X^dag H = 0 (H diagonal), tr X = 0}, as F-matrices"""
    n = len(hdiag)
    units = []
    for i in range(n):
        for j in range(n):
            for k in range(4):
                units.append((i, j, k))
    cols = []
    for (i, j, k) in units:
        X = [[Fd.zero] * n for _ in range(n)]
        X[i][j] = Fd.basis[k]
        # (H X + X^dag H)_{ab} = h_a X_ab + conj(X_ba) h_b
        img = []
        for a in range(n):
            for b in range(n):
                v = Fd.add(Fd.mul(hdiag[a], X[a][b]), Fd.mul(Fd.conj(X[b][a]), hdiag[b]))
                img.extend(v)
        trX = Fd.zero
        for a in range(n):
            trX = Fd.add(trX, X[a][a])
        img.extend(trX)
        cols.append(img)
    nrows = len(cols[0])
    rows = [[cols[c][r] for c in range(len(cols))] for r in range(nrows)]
    ker = nullspace_q(rows, len(units))
    mats = []
    for v in ker:
        X = [[Fd.zero] * n for _ in range(n)]
        for idx, (i, j, k) in enumerate(units):
            if v[idx] != 0:
                X[i][j] = Fd.add(X[i][j], Fd.scal(v[idx], Fd.basis[k]))
        mats.append(X)
    return mats


def bivector_of_form(Eq):
    """the invariant bivector P = E^{-1} (sum_{i<j} P_ij e_i ^ e_j)"""
    N = len(Eq)
    M = flint.fmpq_mat([[flint.fmpq(x.numerator, x.denominator) for x in row] for row in Eq])
    P = M.inv()
    out = {}
    for i in range(N):
        for j in range(i + 1, N):
            c = P[i, j]
            if c != 0:
                out[(i, j)] = Fr(int(c.p), int(c.q))
    return out


def twist_E(Fd, Eq, c):
    """Gram matrix of E_c(x,y) = E(c x, y) for c in F0"""
    N = len(Eq)
    C = fmat_to_Q(Fd, [[c if i == j else Fd.zero for j in range(N // 4)] for i in range(N // 4)])
    # E(Cx, y) = x^T C^T E y
    return [[sum(C[k][i] * Eq[k][j] for k in range(N)) for j in range(N)] for i in range(N)]


def run_field(t, a, b, name, hlist, label):
    Fd = QuarticCM(t, a, b, name)
    print("\n=== %s ; H = diag(%s) ===" % (name, label))
    hdiag = [Fd.f0(*h[:2]) if h[2] > 0 else Fd.neg(Fd.f0(*h[:2])) for h in hlist]
    for h in hlist:
        assert Fd.totally_positive_F0(Fd.f0(*h[:2]))
    xi = Fd.r
    Eq = herm_E(Fd, hdiag, xi)
    N = 16
    alt = all(Eq[i][j] == -Eq[j][i] for i in range(N) for j in range(N))
    det = flint.fmpq_mat([[flint.fmpq(x.numerator, x.denominator) for x in row] for row in Eq]).det()
    check("E alternating and nondegenerate", alt and det != 0)
    su = su_basis(Fd, hdiag)
    check("dim_Q su(V,H) = 30", len(su) == 30, "found %d" % len(su))
    suQ = [fmat_to_Q(Fd, X) for X in su]
    ok = True
    for M in suQ:
        # X^T E + E X = 0
        for i in range(N):
            for j in range(N):
                if sum(M[k][i] * Eq[k][j] for k in range(N)) + sum(Eq[i][k] * M[k][j] for k in range(N)) != 0:
                    ok = False
    check("su(V,H) preserves E", ok)
    W = [weil_lift(Fd, 4, c) for c in Fd.basis]
    check("dim_Q W_F = 4", rank_forms(W) == 4)
    killed = all(not derivation(M, w) for M in suQ for w in W)
    check("W_F killed by su(V,H) (Hodge on every member)", killed)
    # degree-2 invariants
    P1 = bivector_of_form(Eq)
    Ps = bivector_of_form(twist_E(Fd, Eq, Fd.s))
    inv2 = [P1, Ps]
    check("P_1, P_s invariant and independent",
          all(not derivation(M, P) for M in suQ for P in inv2) and rank_forms(inv2) == 2)
    random.seed(1)
    picks = random.sample(suQ, 3)
    rnd = []
    for _ in range(3):
        M = [[Fr(0)] * N for _ in range(N)]
        for X in suQ:
            c = Fr(random.randint(-5, 5))
            if c:
                M = [[M[i][j] + c * X[i][j] for j in range(N)] for i in range(N)]
        rnd.append(M)
    up2 = nullity_modp(rnd, N, 2)
    check("invariants in wedge^2: upper bound mod p = 2", up2 == 2, "nullity mod p = %d" % up2)
    prods = [wedge(P1, P1), wedge(P1, Ps), wedge(Ps, Ps)]
    lower4 = rank_forms(prods + W)
    killed4 = all(not derivation(M, f) for M in suQ for f in prods)
    check("explicit invariants in wedge^4: 3 products + 4 Weil, rank 7", lower4 == 7 and killed4)
    up4 = nullity_modp(rnd, N, 4)
    check("invariants in wedge^4: upper bound mod p = 7", up4 == 7, "nullity mod p = %d" % up4)
    check("W_F meets Lefschetz products in 0 (exceptional)", rank_forms(prods) + 4 == lower4)
    return Fd


def main():
    for (t, a, b, name) in FIELDS:
        run_field(t, a, b, name, [(1, 0, 1), (1, 0, 1), (1, 0, -1), (1, 0, -1)], "1,1,-1,-1")
    # a nontrivial discriminant candidate for Q(zeta_5): h4 = 3 (disc 3)
    run_field(5, Fr(5, 2), Fr(1, 2), "Q(zeta_5)", [(1, 0, 1), (1, 0, 1), (1, 0, -1), (3, 0, -1)], "1,1,-1,-3")
    run_field(2, 3, 1, "Q(sqrt(-(3+sqrt2)))", [(1, 0, 1), (2, 1, 1), (1, 0, -1), (3, 1, -1)], "1,2+s,-1,-(3+s)")
    return summary()


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
