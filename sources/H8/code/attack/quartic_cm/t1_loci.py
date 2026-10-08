#!/usr/bin/env python3
"""
t1_loci.py -- two special loci of an (F,2)-Weil family on which W_F is
algebraic unconditionally, and one on which it is algebraic only through
Markman's theorem.  Exact.

(S) The split (Hilbert-Siegel) locus, every quartic CM field F:
    V = V0 (x)_{F0} F, V0 = F0^4 with the standard symplectic form psi,
    H = r^{-1} psi (sesquilinear), generic Hodge group Res_{F0/Q} Sp(V0,psi).
    Checks: H is hermitian, det H is a square in F0 (trivial discriminant);
    sp4(F0) (Q-dim 20) lies in su(V,H); its invariants in wedge^2 V have
    dimension exactly 6, those in wedge^4 V are exactly the span of the
    products of the degree-2 invariants, and W_F lies in that span; the lift
    of the bivector psi^vee = e0^e2 + e1^e3 is an invariant of T, and
    W_F = { (c psi^vee) * psi^vee } (balanced product) as c runs over F.

(E) The scalar-extension locus, F = K F0 biquadratic, K = Q(r), r^2 = -D in Q:
    B_F = B (x)_{O_K} O_F for B of (K,2,delta)-Weil type, V_F = V_K (x)_K F,
    generic Hodge group SU(V_K, H_K) (Q-dim 15).
    Checks: invariants of su(V_K) in wedge^2 V_F have dimension 4 and meet
    the F-balanced part T in 0 (the locus is NOT in the Noether-Lefschetz
    locus of T, so no divisor argument applies there); in wedge^4 V_F the
    invariants are the Lefschetz products plus the 10-dimensional span of the
    pullbacks g_f^* W_K(B), g_f(v) = f v for f in F (homomorphisms
    B_F -> B); and W_F(B_F) lies in the span of those pullbacks.  With
    Markman's W(K,2,delta) for all delta this makes W_F algebraic on the
    scalar-extension locus.
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1lib import *
from t1_generic import su_basis, bivector_of_form
from t1_T import Tspace, PAIRS

J4 = [[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]


def split_locus(t, a, b, name):
    Fd = QuarticCM(t, a, b, name)
    print("\n=== split locus, %s ===" % name)
    rinv = Fd.inv(Fd.r)
    Hm = [[Fd.scal(J4[i][j], rinv) for j in range(4)] for i in range(4)]
    herm = all(Hm[j][i] == Fd.conj(Hm[i][j]) for i in range(4) for j in range(4))
    # det H = r^{-4} det J = 1/D^2
    D = (Fd.a, Fd.b, Fr(0), Fr(0))
    detH = Fd.mul(Fd.inv(D), Fd.inv(D))
    check("H = r^{-1} psi hermitian; det H = 1/D^2 is a square in F0 (trivial discriminant)",
          herm and Fd.in_F0(detH))
    # E = Tr(r H(x,y)) = Tr(x^T J conj(y))
    N = 16
    Eq = [[Fr(0)] * N for _ in range(N)]
    for i in range(4):
        for j in range(4):
            if J4[i][j] == 0:
                continue
            for k in range(4):
                for l in range(4):
                    Eq[4 * i + k][4 * j + l] = J4[i][j] * Fd.tr(Fd.mul(Fd.basis[k], Fd.conj(Fd.basis[l])))
    # sp4(F0): X in M4(F0) with X^T J + J X = 0
    units = [(i, j) for i in range(4) for j in range(4)]
    cols = []
    for (i, j) in units:
        X = [[0] * 4 for _ in range(4)]
        X[i][j] = 1
        img = []
        for u in range(4):
            for v in range(4):
                img.append(sum(X[w][u] * J4[w][v] for w in range(4)) + sum(J4[u][w] * X[w][v] for w in range(4)))
        cols.append(img)
    rows = [[Fr(cols[c][r]) for c in range(len(cols))] for r in range(16)]
    # J is rational, so sp4(F0) = sp4(Q) (x) F0: X = X0 + s X1 with X0, X1 in sp4(Q)
    ker = nullspace_q(rows, len(units))
    sp = []
    for v in ker:
        for k in range(2):
            X = [[Fd.zero] * 4 for _ in range(4)]
            for idx, (i, j) in enumerate(units):
                if v[idx] != 0:
                    X[i][j] = Fd.add(X[i][j], Fd.scal(v[idx], Fd.basis[k]))
            sp.append(X)
    check("sp4(F0) has Q-dimension 20", len(sp) == 20, "found %d" % len(sp))
    # sp4(F0) inside su(V,H): H X + X^dag H = 0, tr X = 0
    def in_su(X):
        for u in range(4):
            for v in range(4):
                s = Fd.zero
                for w in range(4):
                    s = Fd.add(s, Fd.mul(Hm[u][w], X[w][v]))
                    s = Fd.add(s, Fd.mul(Fd.conj(X[w][u]), Hm[w][v]))
                if not Fd.is_zero(s):
                    return False
        tr = Fd.zero
        for u in range(4):
            tr = Fd.add(tr, X[u][u])
        return Fd.is_zero(tr)
    check("sp4(F0) is contained in su(V,H)", all(in_su(X) for X in sp))
    spQ = [fmat_to_Q(Fd, X) for X in sp]
    # invariants in wedge^2: exact kernel
    B2 = basis_k(N, 2)
    pos2 = {K: i for i, K in enumerate(B2)}
    eqs = []
    for M in spQ:
        img_cols = [derivation(M, {I: Fr(1)}) for I in B2]
        for K in B2:
            eqs.append([img_cols[c].get(K, Fr(0)) for c in range(len(B2))])
    inv2 = nullspace_q(eqs, len(B2))
    check("invariants of sp4(F0) in wedge^2 V: dimension 6 (exact)", len(inv2) == 6, "found %d" % len(inv2))
    inv2f = [{B2[i]: v[i] for i in range(len(B2)) if v[i] != 0} for v in inv2]
    prods = [wedge(inv2f[i], inv2f[j]) for i in range(6) for j in range(i, 6)]
    rprod = rank_forms(prods)
    W = [weil_lift(Fd, 4, c) for c in Fd.basis]
    rWp = rank_forms(prods + W)
    check("W_F lies in the span of products of degree-2 invariants (divisor classes)", rWp == rprod,
          "rank(products) = %d, with W_F = %d" % (rprod, rWp))
    random.seed(3)
    rnd = []
    for _ in range(3):
        M = [[Fr(0)] * N for _ in range(N)]
        for X in spQ:
            c = Fr(random.randint(-5, 5))
            if c:
                M = [[M[i][j] + c * X[i][j] for j in range(N)] for i in range(N)]
        rnd.append(M)
    up4 = nullity_modp(rnd, N, 4)
    check("invariants in wedge^4 V: upper bound mod p equals rank of products (Hodge ring generated by divisors in degree 4)",
          up4 == rprod, "upper bound %d, products %d" % (up4, rprod))
    # the Hodge line in T
    T = Tspace(Fd, [Fd.one] * 4)  # only lift is used
    psiv = [Fd.zero] * 6
    psiv[PAIRS.index((0, 2))] = Fd.one
    psiv[PAIRS.index((1, 3))] = Fd.one
    L = T.lift(psiv)
    check("lift of psi^vee (in T) is an sp4(F0)-invariant, i.e. a divisor class of T",
          all(not derivation(M, L) for M in spQ))
    ok = True
    for c in Fd.basis:
        lhs = {}
        for k in range(4):
            lhs = addf(lhs, wedge(T.lift([Fd.mul(Fd.mul(Fd.basis[k], c), v) for v in psiv]),
                                  T.lift([Fd.mul(Fd.dual[k], v) for v in psiv])))
        # psi^vee ^_F psi^vee = 2 e0^e2^e1^e3 = -2 e0^e1^e2^e3
        ok = ok and lhs == weil_lift(Fd, 4, Fd.scal(-2, c))
    check("balanced square of c psi^vee = -2 (Weil class of c): W_F = divisor products", ok)


class Kfield:
    """K = Q(r) inside F, Q-basis [1, r], trace-dual basis"""
    def __init__(self, Fd):
        self.Fd = Fd
        Dq = Fd.a
        self.basis = [Fd.one, Fd.r]
        self.dual = [Fd.scal(Fr(1, 2), Fd.one), Fd.scal(Fr(-1, 2) / Dq, Fd.r)]


def K_to_Q(Fd, v):
    """K^4 -> Q^8, coordinates of each entry in [1, r]"""
    out = []
    for x in v:
        assert x[1] == 0 and x[3] == 0
        out.extend([x[0], x[2]])
    return out


def K_balanced_weil(Fd, Kf, c):
    total = {}
    for ks in itertools.product(range(2), repeat=3):
        coeffs = []
        for pos in range(4):
            cc = Fd.one
            if pos > 0:
                cc = Fd.mul(cc, Kf.dual[ks[pos - 1]])
            if pos < 3:
                cc = Fd.mul(cc, Kf.basis[ks[pos]])
            coeffs.append(cc)
        vs = []
        for pos in range(4):
            v = [Fd.zero] * 4
            v[pos] = Fd.mul(coeffs[pos], c if pos == 0 else Fd.one)
            vs.append(K_to_Q(Fd, v))
        total = addf(total, wedge_vectors(vs))
    return total


def scalar_extension(t, D, name, delta0):
    Fd = QuarticCM(t, D, 0, name)
    Kf = Kfield(Fd)
    print("\n=== scalar-extension locus, %s, K = Q(sqrt(-%s)), H_K = diag(1,1,-1,-%s) ===" % (name, D, delta0))
    hK = [Fd.f0(1), Fd.f0(1), Fd.f0(-1), Fd.f0(-delta0)]
    # su(V_K,H_K) over Q: X in M4(K), H X + X^dag H = 0, tr X = 0
    units = [(i, j, k) for i in range(4) for j in range(4) for k in range(2)]
    cols = []
    for (i, j, k) in units:
        X = [[Fd.zero] * 4 for _ in range(4)]
        X[i][j] = Kf.basis[k]
        img = []
        for u in range(4):
            for v in range(4):
                val = Fd.add(Fd.mul(hK[u], X[u][v]), Fd.mul(Fd.conj(X[v][u]), hK[v]))
                img.extend([val[0], val[2]])
        tr = Fd.zero
        for u in range(4):
            tr = Fd.add(tr, X[u][u])
        img.extend([tr[0], tr[2]])
        cols.append(img)
    rows = [[cols[c][r] for c in range(len(cols))] for r in range(len(cols[0]))]
    ker = nullspace_q(rows, len(units))
    suK = []
    for v in ker:
        X = [[Fd.zero] * 4 for _ in range(4)]
        for idx, (i, j, k) in enumerate(units):
            if v[idx] != 0:
                X[i][j] = Fd.add(X[i][j], Fd.scal(v[idx], Kf.basis[k]))
        suK.append(X)
    check("su(V_K,H_K) has Q-dimension 15", len(suK) == 15, "found %d" % len(suK))
    suQ = [fmat_to_Q(Fd, X) for X in suK]   # acting on V_F = F^4 = Q^16
    N = 16
    WF = [weil_lift(Fd, 4, c) for c in Fd.basis]
    check("W_F(B_F) is killed by su(V_K,H_K)", all(not derivation(M, w) for M in suQ for w in WF))
    # invariants in wedge^2 V_F (exact)
    B2 = basis_k(N, 2)
    eqs = []
    for M in suQ:
        img_cols = [derivation(M, {I: Fr(1)}) for I in B2]
        for K in B2:
            eqs.append([img_cols[c].get(K, Fr(0)) for c in range(len(B2))])
    inv2 = nullspace_q(eqs, len(B2))
    inv2f = [{B2[i]: v[i] for i in range(len(B2)) if v[i] != 0} for v in inv2]
    check("invariants of su(V_K) in wedge^2 V_F: dimension 4 (NS of B x B)", len(inv2) == 4, "found %d" % len(inv2))
    # the F-balanced part T of wedge^2 V_F
    T = Tspace(Fd, [Fd.one] * 4)
    Tgens = []
    for aI in range(6):
        for k in range(4):
            y = [Fd.zero] * 6
            y[aI] = Fd.basis[k]
            Tgens.append(T.lift(y))
    rT = rank_forms(Tgens)
    r_both = rank_forms(Tgens + inv2f)
    check("T has Q-dim 24 and meets the Hodge classes of the scalar-extension locus in 0",
          rT == 24 and r_both == 24 + len(inv2f), "rank T = %d, rank T + NS = %d" % (rT, r_both))
    # pullbacks g_f^* W_K
    WK = [K_balanced_weil(Fd, Kf, c) for c in Kf.basis]
    # sanity: W_K in wedge^4 Q^8 has rank 2
    check("W_K(B) has Q-dimension 2", rank_forms(WK) == 2)
    def g_image(f):
        imgs = {}
        for i in range(4):
            for k in range(2):
                v = [Fd.zero] * 4
                v[i] = Fd.mul(f, Kf.basis[k])
                imgs[2 * i + k] = vec_form(vec_to_Q(Fd, v))
        return imgs
    def pull(f, form):
        imgs = g_image(f)
        out = {}
        for K, v in form.items():
            w = {(): v}
            for i in K:
                w = wedge(w, imgs[i])
            out = addf(out, w)
        return out
    s_ = Fd.s
    fs = [Fd.one, s_, Fd.add(Fd.one, s_), Fd.sub(Fd.one, s_), Fd.add(Fd.one, Fd.scal(2, s_)),
          Fd.add(Fd.scal(2, Fd.one), s_), Fd.add(Fd.r, s_)]
    P = [pull(f, w) for f in fs for w in WK]
    rP = rank_forms(P)
    check("pullbacks g_f^* W_K(B), f in F, span Q-dimension 10", rP == 10, "rank %d" % rP)
    check("each pullback is a Hodge class (killed by su(V_K))", all(not derivation(M, x) for M in suQ for x in P))
    rPW = rank_forms(P + WF)
    check("W_F(B_F) lies in the span of the pullbacks g_f^* W_K(B)", rPW == rP, "rank with W_F = %d" % rPW)
    prods = [wedge(inv2f[i], inv2f[j]) for i in range(4) for j in range(i, 4)]
    rprod = rank_forms(prods)
    rall = rank_forms(prods + P)
    random.seed(5)
    rnd = []
    for _ in range(3):
        M = [[Fr(0)] * N for _ in range(N)]
        for X in suQ:
            c = Fr(random.randint(-5, 5))
            if c:
                M = [[M[i][j] + c * X[i][j] for j in range(N)] for i in range(N)]
        rnd.append(M)
    up4 = nullity_modp(rnd, N, 4)
    check("Hodge classes in H^4(B_F) = Lefschetz products + pullbacks of W_K (upper bound mod p = lower bound)",
          up4 == rall, "products %d, products+pullbacks %d, upper bound %d" % (rprod, rall, up4))


def main():
    split_locus(5, Fr(5, 2), Fr(1, 2), "Q(zeta_5)")
    split_locus(2, 3, 1, "Q(sqrt(-(3+sqrt2)))")
    split_locus(2, 1, 0, "Q(zeta_8)")
    scalar_extension(2, 1, "Q(zeta_8)=Q(i,sqrt2)", 1)
    scalar_extension(2, 1, "Q(zeta_8)=Q(i,sqrt2)", 3)
    scalar_extension(3, 1, "Q(zeta_12)=Q(i,sqrt3)", 2)
    scalar_extension(6, 2, "Q(sqrt-2,sqrt-3)", 5)
    return summary()


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
