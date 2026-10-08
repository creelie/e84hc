#!/usr/bin/env python3
"""
t1_T.py -- the F-balanced part T = wedge^2_F H^1 of H^2 of an (F,2,delta)
abelian eightfold, its quaternion algebra of Hodge endomorphisms, and the
exact equivalence "W_F algebraic <=> the Casimir class C_q of T is algebraic".
Exact.

 (1) q : T x T -> F, x ^_F y = q(x,y) Omega, and the hermitian form h induced
     by H; the F-semilinear phi defined by q(x,y) = h(x, phi y) satisfies
     phi(alpha y) = conj(alpha) phi(y), phi^2 = 1/det H, and commutes with
     wedge^2 X for every X in su(V,H).  So Q_delta = F + F phi, the cyclic
     algebra (F/F0, 1/det H), acts on T by Hodge endomorphisms on EVERY member.
 (2) The commutant of su(V,H) in End_Q(T_Q) (T_Q = Q^24) has Q-dimension
     exactly 8: lower bound F + F phi (exact), upper bound: commutant of three
     elements, mod p.  So End_Hdg(T) = Q_delta at a member with Hodge group
     Res SU(V,H).
 (3) For x, y in T: sum_k (w_k x) cup (w*_k y) = balanced lift of q(x,y) Omega,
     i.e. the balanced product of two classes of T is a Weil class, and every
     Weil class is one (exact, random x, y).
 (4) On B x B (H^1 = V + V, Q^32): the Casimir C_q = sum_k sum_I
     (w_k c e_I) (x) (w*_k e_I^q) in T (x) T is killed by the diagonal su(V,H)
     (a Hodge class), Delta^* C_q = 6 * (Weil class of c), and C_q lies in the
     Q-span of the pullbacks f_{a,b}^* W_F(B), f_{a,b}(x,y) = a x + b y,
     a span of Q-dimension 20.  Hence W_F(B) algebraic <=> C_q algebraic.
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1lib import *
from t1_generic import su_basis, FIELDS

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def comp(I):
    return tuple(sorted(set(range(4)) - set(I)))


def qsign(I, J):
    sg, K = sort_sign(I + J)
    return sg if K == (0, 1, 2, 3) else 0


class Tspace:
    def __init__(self, Fd, hdiag):
        self.Fd, self.h = Fd, hdiag
        self.detH = Fd.one
        for x in hdiag:
            self.detH = Fd.mul(self.detH, x)
        # h(e_I, e_I) = H_ii H_jj  (H diagonal, real)
        self.hI = {I: Fd.mul(hdiag[I[0]], hdiag[I[1]]) for I in PAIRS}

    def q(self, x, y):
        Fd = self.Fd
        s = Fd.zero
        for a, I in enumerate(PAIRS):
            for b, J in enumerate(PAIRS):
                sg = qsign(I, J)
                if sg:
                    s = Fd.add(s, Fd.scal(sg, Fd.mul(x[a], y[b])))
        return s

    def phi(self, y):
        """phi(y) = sum_J conj(y_J) phi(e_J), phi(e_J) = sum_K q(e_K,e_J)/h_K e_K"""
        Fd = self.Fd
        out = [Fd.zero] * 6
        for b, J in enumerate(PAIRS):
            cy = Fd.conj(y[b])
            for a, K in enumerate(PAIRS):
                sg = qsign(K, J)
                if sg:
                    out[a] = Fd.add(out[a], Fd.scal(sg, Fd.mul(cy, Fd.inv(self.hI[K]))))
        return out

    def wedge2X(self, X, y):
        """(wedge^2 X) y in F-coordinates, X an F-matrix acting on F^4"""
        Fd = self.Fd
        out = [Fd.zero] * 6
        idx = {I: a for a, I in enumerate(PAIRS)}
        for a, (i, j) in enumerate(PAIRS):
            if Fd.is_zero(y[a]):
                continue
            # X e_i ^ e_j + e_i ^ X e_j
            for k in range(4):
                c = X[k][i]
                if not Fd.is_zero(c):
                    sg, K = sort_sign((k, j))
                    if sg:
                        out[idx[K]] = Fd.add(out[idx[K]], Fd.scal(sg, Fd.mul(c, y[a])))
                c = X[k][j]
                if not Fd.is_zero(c):
                    sg, K = sort_sign((i, k))
                    if sg:
                        out[idx[K]] = Fd.add(out[idx[K]], Fd.scal(sg, Fd.mul(c, y[a])))
        return out

    def lift(self, y):
        """balanced lift of y in T to wedge^2_Q V"""
        Fd = self.Fd
        tot = {}
        for a, (i, j) in enumerate(PAIRS):
            if Fd.is_zero(y[a]):
                continue
            tot = addf(tot, balanced_lift(Fd, [std_vec(Fd, 4, i, y[a]), std_vec(Fd, 4, j)]))
        return tot

    def to_Q(self, y):
        out = []
        for x in y:
            out.extend(x)
        return out

    def from_Q(self, v):
        return [tuple(v[4 * a:4 * a + 4]) for a in range(6)]


def rand_F(Fd, rng):
    return tuple(Fr(rng.randint(-4, 4)) for _ in range(4))


def shift(form, off):
    return {tuple(i + off for i in K): c for K, c in form.items()}


def run(t, a, b, name, hlist, label):
    Fd = QuarticCM(t, a, b, name)
    print("\n=== %s ; H = diag(%s) ===" % (name, label))
    hdiag = [Fd.f0(*h[:2]) if h[2] > 0 else Fd.neg(Fd.f0(*h[:2])) for h in hlist]
    T = Tspace(Fd, hdiag)
    rng = random.Random(7)
    # (1) phi
    ys = [[rand_F(Fd, rng) for _ in range(6)] for _ in range(3)]
    al = rand_F(Fd, rng)
    ok_semi = all(T.phi([Fd.mul(al, x) for x in y]) == [Fd.mul(Fd.conj(al), x) for x in T.phi(y)] for y in ys)
    invdet = Fd.inv(T.detH)
    ok_sq = all(T.phi(T.phi(y)) == [Fd.mul(invdet, x) for x in y] for y in ys)
    # q(x,y) = h(x, phi y) with h(x,z) = sum_K x_K conj(z_K) h_K
    def h(x, z):
        s = Fd.zero
        for aK, K in enumerate(PAIRS):
            s = Fd.add(s, Fd.mul(Fd.mul(x[aK], Fd.conj(z[aK])), T.hI[K]))
        return s
    ok_def = all(T.q(ys[0], y) == h(ys[0], T.phi(y)) for y in ys)
    check("phi is F-semilinear, q(x,y) = h(x, phi y), phi^2 = 1/det H",
          ok_semi and ok_sq and ok_def, "det H = %s" % (T.detH,))
    su = su_basis(Fd, hdiag)
    basisT = [[Fd.one if a == c else Fd.zero for a in range(6)] for c in range(6)]
    ok_comm = all(T.phi(T.wedge2X(X, e)) == T.wedge2X(X, T.phi(e)) for X in su for e in basisT)
    check("phi commutes with wedge^2 su(V,H) (a Hodge endomorphism of T on every member)", ok_comm)
    # (2) commutant dimension: Q-linear maps of T_Q=Q^24 commuting with su
    def op_matrix(fn):
        cols = []
        for c in range(6):
            for k in range(4):
                y = [Fd.zero] * 6
                y[c] = Fd.basis[k]
                cols.append(T.to_Q(fn(y)))
        return [[cols[j][i] for j in range(24)] for i in range(24)]
    Xs = [op_matrix(lambda y, X=X: T.wedge2X(X, y)) for X in su]
    lows = [op_matrix(lambda y, al=al: [Fd.mul(al, x) for x in y]) for al in Fd.basis]
    lows += [op_matrix(lambda y, al=al: T.phi([Fd.mul(al, x) for x in y])) for al in Fd.basis]
    def commutes(A, B):
        n = len(A)
        return all(sum(A[i][k] * B[k][j] for k in range(n)) == sum(B[i][k] * A[k][j] for k in range(n))
                   for i in range(n) for j in range(n))
    ok_low = all(commutes(L, X) for L in lows for X in Xs)
    rk_low = rank_forms([{(i, j): L[i][j] for i in range(24) for j in range(24) if L[i][j] != 0} for L in lows])
    check("F + F phi: 8 independent Q-linear maps commuting with su(V,H)", ok_low and rk_low == 8)
    p = 1000003
    rnd = []
    for _ in range(3):
        M = [[Fr(0)] * 24 for _ in range(24)]
        for X in Xs:
            c = Fr(rng.randint(-5, 5))
            if c:
                M = [[M[i][j] + c * X[i][j] for j in range(24)] for i in range(24)]
        rnd.append(M)
    # unknown C (24x24), equations C M - M C = 0 for each M
    S = flint.nmod_mat(3 * 576, 576, p)
    for tM, M in enumerate(rnd):
        Mp = [[(x.numerator * pow(x.denominator, -1, p)) % p for x in row] for row in M]
        for i in range(24):
            for j in range(24):
                r = tM * 576 + 24 * i + j
                # (C M)_{ij} = sum_k C_ik M_kj ; (M C)_ij = sum_k M_ik C_kj
                for k in range(24):
                    if Mp[k][j]:
                        S[r, 24 * i + k] = (int(S[r, 24 * i + k]) + Mp[k][j]) % p
                    if Mp[i][k]:
                        S[r, 24 * k + j] = (int(S[r, 24 * k + j]) - Mp[i][k]) % p
    nul = 576 - S.rank()
    check("commutant of su(V,H) on T has Q-dimension exactly 8 (upper bound mod p)", nul == 8,
          "nullity mod p = %d" % nul)
    # (3) balanced product of classes of T
    ok3 = True
    for _ in range(2):
        x = [rand_F(Fd, rng) for _ in range(6)]
        y = [rand_F(Fd, rng) for _ in range(6)]
        lhs = {}
        for k in range(4):
            lhs = addf(lhs, wedge(T.lift([Fd.mul(Fd.basis[k], v) for v in x]),
                                  T.lift([Fd.mul(Fd.dual[k], v) for v in y])))
        rhs = weil_lift(Fd, 4, T.q(x, y))
        ok3 = ok3 and (lhs == rhs)
    check("sum_k (w_k x) cup (w*_k y) = Weil class of q(x,y), x,y in T", ok3)
    # (4) Casimir on B x B
    # q-dual basis of T: q(e_I, e_J') = delta ; e_J' = sign * e_comp(J)
    duals = []
    for J in PAIRS:
        Jc = comp(J)
        sg = qsign(J, Jc)
        v = [Fd.zero] * 6
        v[PAIRS.index(Jc)] = Fd.scal(sg, Fd.one)
        duals.append(v)
    c = Fd.add(Fd.one, Fd.r)
    Cq = {}
    for a_, I in enumerate(PAIRS):
        eI = [Fd.zero] * 6
        eI[a_] = c
        for k in range(4):
            left = T.lift([Fd.mul(Fd.basis[k], v) for v in eI])
            right = shift(T.lift([Fd.mul(Fd.dual[k], v) for v in duals[a_]]), 16)
            Cq = addf(Cq, wedge(left, right))
    suQ = [fmat_to_Q(Fd, X) for X in su]
    def diag2(M):
        N = len(M)
        D = [[Fr(0)] * (2 * N) for _ in range(2 * N)]
        for i in range(N):
            for j in range(N):
                D[i][j] = M[i][j]
                D[i + N][j + N] = M[i][j]
        return D
    ok_hodge = all(not derivation(diag2(M), Cq) for M in suQ)
    check("C_q is killed by the diagonal su(V,H) (all 30 basis elements)", ok_hodge)
    # Delta^*
    DeltaC = {}
    for K, v in Cq.items():
        J = tuple(i if i < 16 else i - 16 for i in K)
        sg, L = sort_sign(J)
        if sg:
            DeltaC[L] = DeltaC.get(L, Fr(0)) + sg * v
    DeltaC = {K: v for K, v in DeltaC.items() if v != 0}
    check("Delta^* C_q = 6 * (Weil class of c)", DeltaC == scalf(Fr(6), weil_lift(Fd, 4, c)))
    # pullbacks f_{a,b}^*: v -> (a v, b v)
    def pull(ab, form):
        a_, b_ = ab
        imgs = {}
        for i in range(16):
            blk, k = divmod(i, 4)
            e = std_vec(Fd, 4, blk, Fd.basis[k])
            va = vec_to_Q(Fd, [Fd.mul(a_, x) for x in e])
            vb = vec_to_Q(Fd, [Fd.mul(b_, x) for x in e])
            imgs[i] = vec_form(va + vb)
        out = {}
        for K, v in form.items():
            w = {(): v}
            for i in K:
                w = wedge(w, imgs[i])
            out = addf(out, w)
        return out
    dirs = [(Fd.one, Fd.zero), (Fd.zero, Fd.one), (Fd.one, Fd.one), (Fd.one, Fd.neg(Fd.one)),
            (Fd.one, Fd.scal(2, Fd.one))]
    P = [pull(ab, weil_lift(Fd, 4, cc)) for ab in dirs for cc in Fd.basis]
    rP = rank_forms(P)
    rPC = rank_forms(P + [Cq])
    check("pullbacks f_{a,b}^* W_F span Q-dimension 20 and contain C_q", rP == 20 and rPC == 20,
          "rank %d, with C_q %d" % (rP, rPC))


def main():
    for (t, a, b, name) in FIELDS[:2]:
        run(t, a, b, name, [(1, 0, 1), (1, 0, 1), (1, 0, -1), (1, 0, -1)], "1,1,-1,-1")
    run(5, Fr(5, 2), Fr(1, 2), "Q(zeta_5)", [(1, 0, 1), (1, 0, 1), (1, 0, -1), (3, 0, -1)], "1,1,-1,-3")
    run(2, 3, 1, "Q(sqrt(-(3+sqrt2)))", [(1, 0, 1), (2, 1, 1), (1, 0, -1), (3, 1, -1)], "1,2+s,-1,-(3+s)")
    return summary()


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
