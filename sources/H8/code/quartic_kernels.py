#!/usr/bin/env python3
"""
quartic_kernels.py

Item (LIX) of the computations: kernels on X x X for a quartic CM field at
n = 2.  A kernel that is not an external product and gives a flat character
with a Weil part; the exclusion of kernels supported on graphs and of pure
spinors; the shape of the characters of the secant Orlov products; the
arithmetic of Orlov products with negative Ext groups; and the bookkeeping
behind the Prym loci.

Setting.  F = F_0(sqrt(-q)), F_0 = Q(sqrt D) real quadratic with real places
tau_1, tau_2, q in F_0 totally positive, X a principally polarised abelian
fourfold with real multiplication by O = O_{F_0}, A = X x Xhat with the
F-action of the split member, Phi Orlov's equivalence D(X x X) -> D(A).  Over
R everything is a tensor product over the two places of classes of even
degree (proof of thm:quarticobstruction(iii)); the one-place model, with
d = tau_j(q), is attack/gaps/quartic_kernels/qk_place.py: X_j has H^1 = U_j
of dimension 4 with theta_j, A_j has the classes theta_j, thetahat_j, ell_j,
    eta_j = d theta_j + thetahat_j,  gamma_j = d theta_j - thetahat_j,
    Omega_j = gamma_j^2 - d ell_j^2,
and G_F(R) = SU_1 x SU_2.  On H^*(X_j):
    U0(y) = (int y) pt,  P(y) = int y,
    T(d): y_0 -> -(d^2/2) theta^2 y_0, y_2 -> (d/2) y_2, y_3 -> (3d/2) y_3,
          y_4 -> 3d y_4,
and Z'' is the class on X x X with correspondence
    U0_1 (x) (T_2 - P_2) + (T_1 - P_1) (x) U0_2.

What is checked:

  (A) one place: the model (Phi(X x 0) = 1, Phi(Delta) = point,
      Phi(antidiagonal) = 16 e^{-ell/2}, graph classes); the closed form
      ch Phi(T(d) - P) = -(1/4)(eta^2 + Omega) at four values of d, an
      identity of degree two in d, and in Q(sqrt5, i) at d = tau_1(2 + phi);
      flatness, pure degree four, Weil part -(1/4) Omega; (gamma -+ s ell)^2
      spans the eigenline of eigenvalue +-4s of sqrt(-q) in degree four;
      Hodge type at X x Xhat; the twisted classes with e^{+-ell/2} are not
      flat; the exceptional ratio 3/4 of rem:p2primeexceptional; the rank of
      contraction 23, with annihilator of dimension 5 in H^1(T) containing
      that of a general invariant class, of dimension 4; Phi(X x X) at one
      place is minus the class of X x 0 in A_j, not flat, so the character of
      O_X (x) F' is not flat;

  (B) the global class ch Phi(Z'') = w_1 (x) 1 + 1 (x) w_2 for four quartic
      CM fields: pure of degree four (so chi = 0), r^1 = 16, r = 94; the
      annihilator, of dimension 26, is the 16 bivectors of T_1 (x) T_2 and a
      5-dimensional subspace of H^1(T) at each place;

  (C) rationality: for five fields G'' = U0_1 (x) T_2 + T_1 (x) U0_2 is
      invariant under Gal(F_0/Q) and lies in the rational span of the
      classes (beta, alpha)_*(c), beta, alpha in O, c in Q[theta, theta_R];
      for Q(zeta_5) a combination of 36 such classes on 21 graphs
      {(beta x, x)} is found; ch O_X (x) F = (theta_1^2 + theta_2^2)/2 is
      rational, (3 theta^2 - 2 theta theta_R + 2 theta_R^2)/10 for Q(sqrt5);

  (D) secant Orlov products (ch F_i in S(0, q)), six pairs in each of two
      fields, five of the twelve of rank zero: kappa = ch(E) e^{ell/2} is flat,
      ch(E) is not,
      kappa_(4,8) = kappa_(4,0) eta_2^4 / (384 tau_2(q)^2) and symmetrically,
      and kappa has components outside C[eta_1, eta_2] + W_F whenever
      kappa_(4,0) has a Weil part;

  (E) graphs, one place: the classes (b, a)_*(c) span a space L of
      dimension 24; Phi(L) meets the invariants in span(1, pt) at three
      values of d; the 2-forms B with B ^ Phi(L) in Phi(L) form a space of
      dimension 7 containing theta, ell and all 2-forms from X, and not
      thetahat; e^{B} Phi(L) meets the invariants in e^{g eta} span(1, pt)
      for B = f theta + g thetahat + h ell (four cases); the ideal sheaf of
      the graph of R in Q(zeta_5), and its twist by p_1^* O(theta), have no
      flat character ch Phi(-) e^{t ell}, t in {0, 1/2, 1};

  (F) pure spinors, one place: su_j(d) acts irreducibly on H^1(A_j), with
      commutant span(1, M*), M*^2 = -d; the invariants have dimensions
      1, 1, 3, 1, 1 in degrees 0, 2, 4, 6, 8 and are spanned by 1, eta,
      eta^2, Omega, Lambda, eta^3, eta^4; Phi of line bundles on graphs are
      pure (annihilator of dimension 8 in V + V^*), before and after e^{ell/2};
      the flat classes w and Omega are not pure, while (gamma - s ell)^2 is
      pure over C;

  (G) Orlov products with negative Ext groups: int v_4^2 is even for
      integral classes; for chi = 4 and (rho, N_w) = (2, 4) the congruences
      (a)-(c) of prop:quarticother leave only D = 3 among the squarefree
      D < 200000;

  (H) Prym bookkeeping (the algebraicity is Schoen's theorem and is not
      recomputed): the fields with phi(N) = 4 are Q(zeta_5), Q(zeta_8),
      Q(zeta_12); 3g - 3 < (phi(N)/2)(g - 1)^2 for phi(N) >= 4, g >= 3; a
      split hermitian form of F-dimension 2n has determinant (-1)^n.

Everything is exact.  Standard library and python-flint.  The model is in
attack/gaps/quartic_kernels/ (qk_ext.py, qk_place.py, qk_coeff.py,
qk_tensor.py).

Run:  python3 quartic_kernels.py
"""
import os
import sys
import random
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "attack", "gaps", "quartic_kernels"))
from qk_ext import (popc, add, sc, sub, wedge, gen, one, expo, degrees,  # noqa: E402
                    shift, derivation, interior, field, rank_K, rank_Q,
                    dict_rank_Q, span_basis, intersection, nullspace_Q)
from qk_place import (theta_x, thetahat, ell, eta, gamma, omega_w,     # noqa: E402
                      inv_basis, U0_class, P_class, W_class, graph_class,
                      graph_geometric, orlov, Mstar, Jcx, lin_to_mat,
                      su_basis, invariants, is_flat, HT2_images, HT1_images)
import qk_coeff as QC                                                   # noqa: E402
from qk_tensor import ProjK, tensor_split                               # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("         " + detail)


def closed_form(d):
    """-(1/4)(eta^2 + gamma^2 - d ell^2) at one place."""
    e = eta(d)
    return sc(d * 0 + Fr(-1, 4), add(wedge(e, e), omega_w(d)))


def in_span(v, vecs):
    return dict_rank_Q(vecs + [v]) == dict_rank_Q(vecs)


# ------------------------------------------------------------------ (A)
def part_A():
    print("(A) one place: the kernel T(d) - P")
    delta = graph_class(1, 1, one(Fr(1)))
    anti = orlov(graph_class(1, -1, one(Fr(1))))
    ok = (orlov(U0_class()) == {0: Fr(1)} and orlov(delta) == {255: Fr(1)}
          and anti == sc(16, expo(sc(Fr(-1, 2), ell()))))
    pairs = [(1, 1), (2, 1), (1, -1), (3, 2), (1, 0), (0, 1)]
    ok_g = all(graph_class(b, a, one(Fr(1))) == graph_geometric(b, a)
               for b, a in pairs)
    ok_u = (P_class() == one(Fr(1))
            and U0_class() == shift(sc(Fr(1, 2), wedge(theta_x(), theta_x())), 4))
    check("model: Phi(X x 0) = 1, Phi(Delta) = pt, Phi(antidiagonal) = "
          "16 e^{-ell/2}; the graph formula gives the class of the graph for "
          "%d maps; P = [X x X] and U0 = pr_2^* pt" % len(pairs), ok and ok_g and ok_u)

    pP = orlov(P_class())
    check("Phi(X x X) at one place is -(the class of X x 0 in A_j), not flat; so "
          "ch Phi(O_X [x] F) = 1 (x) Phi(P_2) + Phi(P_1) (x) 1 is not flat",
          pP == {240: Fr(-1)} and all(not is_flat(pP, su_basis(d)) for d in (1, 3)))

    ds = [Fr(1), Fr(2), Fr(3), Fr(5, 2)]
    ws = {d: orlov(W_class(d)) for d in ds}
    check("ch Phi(T(d) - P) = -(1/4)(eta^2 + gamma^2 - d ell^2) at d = 1, 2, 3, "
          "5/2; both sides have degree at most two in d, so this holds for "
          "every d", all(ws[d] == closed_form(d) for d in ds))
    mk = field(5)
    dK = mk(Fr(5, 2), Fr(1, 2))
    check("the same identity in Q(sqrt5, i) at d = tau_1(2 + phi) = (5 + sqrt5)/2",
          orlov(W_class(dK)) == closed_form(dK))
    ok_flat, ok_deg, ok_weil = True, True, True
    for d in ds:
        B = su_basis(d)
        I, names = inv_basis(d)
        w = ws[d]
        ok_flat = ok_flat and is_flat(w, B) and all(is_flat(x, B) for x in I)
        ok_deg = ok_deg and degrees(w) == [4]
        # w = -(1/4) eta^2 - (1/4) Omega: Weil part -(1/4) Omega, nonzero
        ok_weil = ok_weil and (sub(w, sc(Fr(-1, 4), wedge(I[1], I[1]))) ==
                               sc(Fr(-1, 4), I[3])) and bool(I[3])
    check("w = ch Phi(T(d) - P) is flat for su_j(d), of pure degree 4, with "
          "Weil part -(1/4) Omega != 0 (d = 1, 2, 3, 5/2)",
          ok_flat and ok_deg and ok_weil)

    # Omega is a sum of two Weil classes: (gamma -+ s ell)^2 spans the eigenline
    # of eigenvalue +-4s of the derivation of sqrt(-q) in degree four
    ok = True
    for d, s in [(Fr(1), mk(0, 0, 1)), (Fr(4), mk(0, 0, 2))]:
        Mk = {k: {m: mk(c) for m, c in v.items()} for k, v in Mstar(d).items()}
        for sign in (1, -1):
            th = add(sc(mk(d), theta_x()), sc(mk(-1), thetahat()))
            x = sub(th, sc(s * sign, sc(mk(1), ell())))
            x2 = wedge(x, x)
            lhs = derivation(x2, Mk)
            ok = ok and bool(x2) and lhs == sc(s * sign * 4, x2)
    check("(gamma -+ s ell)^2, s = sqrt(-d), is an eigenvector of eigenvalue "
          "+-4s of the action of sqrt(-q) in degree four (d = 1, 4), so it spans "
          "a line wedge^4 V_sigma of Weil classes", ok)

    J = Jcx()
    JK = {k: {m: mk(c) for m, c in v.items()} for k, v in J.items()}
    ok = all(not derivation(orlov(W_class(mk(d))), JK) for d in (Fr(1), Fr(3)))
    M, Jm = lin_to_mat(Mstar(Fr(3))), lin_to_mat(J)
    MJ = [[sum(M[i][k] * Jm[k][j] for k in range(8)) for j in range(8)] for i in range(8)]
    JM = [[sum(Jm[i][k] * M[k][j] for k in range(8)) for j in range(8)] for i in range(8)]
    check("at X x Xhat the class w is of Hodge type (killed by the derivation of "
          "the complex structure, d = 1, 3), and sqrt(-q) commutes with it",
          ok and MJ == JM)

    ok = True
    for d in ds:
        B = su_basis(d)
        for t in (Fr(1, 2), Fr(-1, 2)):
            ok = ok and not is_flat(wedge(ws[d], expo(sc(t, ell()))), B)
    check("w e^{ell/2} and w e^{-ell/2} are not flat: the statement is about "
          "the untwisted character", ok)

    ok = True
    for d in ds:
        e = eta(d)
        e4 = wedge(wedge(e, e), wedge(e, e)).get(255, 0)
        o2 = wedge(omega_w(d), omega_w(d)).get(255, 0)
        ok = ok and abs(e4) == 24 * d * d and abs(o2) == 32 * d * d and e4 / o2 == Fr(3, 4)
    check("int eta^4 : int Omega^2 = 24 d^2 : 32 d^2 = 3/4, so with c = -1/4 and "
          "omega = -(1/4) Omega one has c^2 int eta^4 = (3/4) int omega^2: the "
          "exceptional ratio of rem:p2primeexceptional", ok)

    res = []
    for d in (Fr(1), Fr(3)):
        dK = mk(d)
        w = orlov(W_class(dK))
        imgs, labels = HT2_images(w, mk)
        r = rank_K(imgs, mk)
        qd = [im for im, lb in zip(imgs, labels) if lb[0] == "QD"]
        rqd = rank_K(qd, mk)
        g = add(omega_w(dK), sc(mk(Fr(1, 3)), wedge(eta(dK), eta(dK))))
        imgs2, _ = HT2_images(g, mk)
        r2 = rank_K(imgs2, mk)
        rqd2 = rank_K([im for im, lb in zip(imgs2, labels) if lb[0] == "QD"], mk)
        stacked = rank_K([add(a, shift(b, 16)) for a, b in zip(imgs, imgs2)], mk)
        res.append((r, 16 - rqd, r2, 16 - rqd2, stacked))
    check("one place: r(w) = 23 with annihilator of dimension 5 in H^1(T); the "
          "general invariant class Omega + eta^2/3 has r = 24, annihilator of "
          "dimension 4 = dim T D at one place, contained in that of w (d = 1, 3)",
          all(x == (23, 5, 24, 4, 24) for x in res), "(r, ker in H^1(T), r_gen, "
          "ker_gen, rank of both) = %s" % res)


# ------------------------------------------------------------------ (B)
FIELDS = [("Q(zeta_5), q = 2 + phi", 5, (Fr(5, 2), Fr(1, 2))),
          ("Q(sqrt5, i), q = 1", 5, (Fr(1), Fr(0))),
          ("Q(sqrt2)(sqrt(-(2 + sqrt2))), q = 2 + sqrt2", 2, (Fr(2), Fr(1))),
          ("Q(sqrt13)(sqrt(-q)), q = 2 + (1 + sqrt13)/2", 13, (Fr(5, 2), Fr(1, 2)))]


def part_B():
    print("(B) the global class ch Phi(Z'')")
    for name, D, (qa, qb) in FIELDS:
        t0 = time.time()
        mk = field(D)
        d1, d2 = mk(qa, qb), mk(qa, -qb)
        w1, w2 = orlov(W_class(d1)), orlov(W_class(d2))
        c = add(w1, shift(w2, 8))
        imgs, labels = HT2_images(c, mk, places=2)
        r = rank_K(imgs, mk)
        r1 = rank_K(HT1_images(c, mk, places=2), mk)
        cross = [im for im, lb in zip(imgs, labels)
                 if lb[0] == "DD" and lb[1] // 4 != lb[2] // 4]
        kq = [16 - rank_K([im for im, lb in zip(imgs, labels)
                           if lb[0] == "QD" and lb[1] // 4 == j and lb[2] // 4 == j], mk)
              for j in (0, 1)]
        ok = (degrees(c) == [4] and r1 == 16 and r == 94 and len(imgs) == 120
              and len(cross) == 16 and all(not x for x in cross) and kq == [5, 5])
        check("%s: ch Phi(Z'') has pure degree 4 (so chi = 0), r^1 = 16, "
              "r = 94; annihilator 26 = 16 (T_1 (x) T_2) + 5 + 5 (H^1(T) at each "
              "place)" % name, ok, "r = %d, r^1 = %d, kernels in H^1(T): %s, %.1fs"
              % (r, r1, kq, time.time() - t0))


# ------------------------------------------------------------------ (C)
def part_C():
    print("(C) rationality of Z''")
    for D, q in [(5, (2, 1)), (5, (1, 0)), (2, (2, 1)), (2, (5, 1)), (13, (2, 1))]:
        Fd = QC.F0(D)
        G = QC.G_vec(Fd, Fd.elt(q))
        cs = [(i, l) for i in range(5) for l in range(5) if i + l <= 4]
        pairs = ([((bm, bn), a) for bm in range(-2, 3) for bn in range(-2, 3)
                  for a in [(1, 0), (0, 1), (1, 1)]] + [((1, 0), (0, 0)), ((0, 0), (1, 0))])
        gens = [QC.graph_vec(Fd, b, a, QC.c_expand(Fd, i, l))
                for b, a in pairs for (i, l) in cs]
        ok, rk = QC.in_Q_span(G, gens)
        check("D = %d, q = %d + %d R: G'' is Gal(F_0/Q)-invariant, and the classes of "
              "O-graphs span all %d rational classes of graph type at both places, "
              "so G'' is a rational combination of them" % (D, q[0], q[1], rk),
              ok and rk == 81 and QC.galois(Fd, G) == G)
    Fd = QC.F0(5)
    G = QC.G_vec(Fd, Fd.elt((2, 1)))
    gens, labels = [], []
    for m in (-3, -2, -1):
        for n in range(-3, 4):
            for (i, l) in [(0, 0), (0, 2), (1, 1), (2, 0)]:
                gens.append(QC.graph_vec(Fd, (m, n), (1, 0), QC.c_expand(Fd, i, l)))
                labels.append(((m, n), (i, l)))
    sol = QC.solve_Q(G, gens)
    ok = sol is not None
    if ok:
        tot = [QC.Z0] * len(QC.BASIS)
        for a, g in zip(sol, gens):
            if a:
                tot = [Fd.ad(x, Fd.scl(a, y)) for x, y in zip(tot, g)]
        ok = tot == G
        nz = [lb for a, lb in zip(sol, labels) if a]
        ngraph = len(set(lb[0] for lb in nz))
    check("Q(zeta_5): G'' is a rational combination of %d classes (beta, 1)_*(c) "
          "on %d graphs, beta = m + n phi, c in {1, theta_R^2, theta theta_R, "
          "theta^2}" % (len(nz) if ok else -1, ngraph if ok else -1),
          ok and len(nz) == 36 and ngraph == 21)
    t = {}
    for (i, l), coef in [((2, 0), Fr(3, 10)), ((1, 1), Fr(-2, 10)), ((0, 2), Fr(2, 10))]:
        for key, v in QC.c_expand(Fd, i, l).items():
            t[key] = Fd.ad(t.get(key, QC.Z0), Fd.scl(coef, v))
    t = {k: v for k, v in t.items() if v != QC.Z0}
    check("Q(sqrt5): (theta_1^2 + theta_2^2)/2 = (3 theta^2 - 2 theta theta_R + "
          "2 theta_R^2)/10, so ch F and Z'' = G'' - ch(O_X [x] F) are rational",
          t == {(2, 0): (Fr(1, 2), Fr(0)), (0, 2): (Fr(1, 2), Fr(0))})


# ------------------------------------------------------------------ (D)
def dual(P):
    return {m: (c if popc(m) % 4 == 0 else -c) for m, c in P.items()}


def part_D():
    print("(D) secant Orlov products")
    for D, (qa, qb) in [(5, (Fr(5, 2), Fr(1, 2))), (2, (Fr(2), Fr(1)))]:
        t0 = time.time()
        mk = field(D)
        dd = [mk(qa, qb), mk(qa, -qb)]
        gen0 = ([mk(Fr(1, 2), Fr(1, 2)), mk(Fr(1, 2), Fr(-1, 2))] if D % 4 == 1
                else [mk(0, 1), mk(0, -1)])
        th = sc(mk(1), theta_x())
        u = [sub(one(mk(1)), sc(dd[j] * mk(Fr(1, 2)), wedge(th, th))) for j in range(2)]
        S = {"u": [(mk(1), u[0], u[1])], "w": [(mk(1), th, th)],
             "v1": [(mk(1), th, u[1]), (mk(1), u[0], th)],
             "vR": [(gen0[0], th, u[1]), (gen0[1], u[0], th)]}
        projs = [ProjK(dd[0], mk), ProjK(dd[1], mk)]
        names = projs[0].names
        eh = expo(sc(mk(Fr(1, 2)), sc(mk(1), ell())))
        cache = {}

        def orl(Z):
            key = tuple(sorted((m, c.v) for m, c in Z.items()))
            if key not in cache:
                cache[key] = orlov(Z)
            return cache[key]
        tests = [("(w,w)", S["w"], S["w"]), ("(u,u)", S["u"], S["u"]),
                 ("(v1,v1)", S["v1"], S["v1"]), ("(u,w)", S["u"], S["w"]),
                 ("(v1,w)", S["v1"], S["w"]),
                 ("(u+v1+w,vR)", S["u"] + S["v1"] + S["w"], S["vR"])]
        flat_k, notflat_ch, rel, nonlit, nweil, nrank0 = True, True, True, True, 0, 0
        f2 = (mk(384) * dd[1] * dd[1]).inv()
        f1 = (mk(384) * dd[0] * dd[0]).inv()
        deg4 = ("eta^2", "Omega", "Lambda")
        for tname, S1, S2 in tests:
            raw = []
            for (c1, A1, A2) in S1:
                for (c2, B1, B2) in S2:
                    raw.append((c1 * c2, orl(wedge(A1, shift(dual(B1), 4))),
                                orl(wedge(A2, shift(dual(B2), 4)))))
            II, rest = tensor_split([(c, wedge(P1, eh), wedge(P2, eh))
                                     for c, P1, P2 in raw], projs)
            _, rest_u = tensor_split(raw, projs)
            rank = sum((c * P1.get(0, mk(0)) * P2.get(0, mk(0)) for c, P1, P2 in raw), mk(0))
            nrank0 += int(rank == 0)
            flat_k = flat_k and not rest
            notflat_ch = notflat_ch and bool(rest_u)
            k40 = {names[i]: v for (i, j), v in II.items() if names[j] == "1" and names[i] in deg4}
            k48 = {names[i]: v for (i, j), v in II.items() if names[j] == "eta^4" and names[i] in deg4}
            k04 = {names[j]: v for (i, j), v in II.items() if names[i] == "1" and names[j] in deg4}
            k84 = {names[j]: v for (i, j), v in II.items() if names[i] == "eta^4" and names[j] in deg4}
            rel = rel and all(k48.get(x, mk(0)) == k40.get(x, mk(0)) * f2 and
                              k84.get(x, mk(0)) == k04.get(x, mk(0)) * f1 for x in deg4)
            weil40 = any(not (k40.get(x, mk(0)) == 0) for x in ("Omega", "Lambda"))
            lit = {"1", "eta", "eta^2", "eta^3", "eta^4"}
            weil = {"Omega", "Lambda"}
            extra = [(i, j) for (i, j) in II
                     if not ((names[i] in lit and names[j] in lit) or
                             (names[i] in weil and names[j] == "1") or
                             (names[i] == "1" and names[j] in weil))]
            if weil40:
                nweil += 1
                nonlit = nonlit and bool(extra)
        check("D = %d, q = %s + %s sqrt%d, six pairs (%d of rank zero): kappa = "
              "ch(E) e^{ell/2} is flat and ch(E) is not" % (D, qa, qb, D, nrank0),
              flat_k and notflat_ch and nrank0 >= 1)
        check("D = %d: kappa_(4,8) = kappa_(4,0) eta_2^4 / (384 tau_2(q)^2) and "
              "kappa_(8,4) = eta_1^4 kappa_(0,4) / (384 tau_1(q)^2) for the six pairs; "
              "where kappa_(4,0) has a Weil part (%d pairs) kappa has components "
              "outside C[eta_1, eta_2] + W_F" % (D, nweil), rel and nonlit and nweil >= 4,
              "%.1fs" % (time.time() - t0))


# ------------------------------------------------------------------ (E)
EVEN_X = ([one(Fr(1))] + [wedge(gen(i), gen(j)) for i in range(4) for j in range(i + 1, 4)]
          + [{15: Fr(1)}])


def reducer(basis):
    """reduction modulo the span of an rref basis (as from span_basis)."""
    piv = [(min(r), r) for r in basis]

    def red(v):
        v = dict(v)
        for p, r in piv:
            c = v.get(p, 0)
            if c != 0:
                v = sub(v, sc(c, r))
        return v
    return red


def part_E():
    print("(E) kernels supported on graphs, one place")
    pairs = [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2), (3, 1)]
    L = [graph_class(b, a, c) for b, a in pairs for c in EVEN_X]
    PL = span_basis([orlov(z) for z in L])
    check("the classes (b, a)_*(c), c of even degree, span a space L of "
          "dimension 24, and Phi(L) has dimension 24",
          len(span_basis(L)) == 24 and len(PL) == 24)
    ok = True
    for d in (Fr(1), Fr(3), Fr(2, 5)):
        inter = intersection(invariants(d), PL)
        ok = ok and len(inter) == 2 and in_span({0: Fr(1)}, inter) and in_span({255: Fr(1)}, inter)
    check("Phi(L) meets the su_j(d)-invariants exactly in span(1, pt) "
          "(d = 1, 3, 2/5)", ok)

    red = reducer(PL)
    twoforms = [wedge(gen(i), gen(j)) for i in range(8) for j in range(i + 1, 8)]
    prods = [[red(wedge(B, u)) for B in twoforms] for u in PL]
    rows = []
    for i in range(len(PL)):
        keys = sorted(set(k for v in prods[i] for k in v))
        for k in keys:
            rows.append([prods[i][c].get(k, Fr(0)) for c in range(len(twoforms))])
    ns = nullspace_Q(rows, len(twoforms))
    stab = [add(*[sc(v[c], twoforms[c]) for c in range(len(twoforms)) if v[c]]) for v in ns]
    xside = [wedge(gen(i), gen(j)) for i in range(4) for j in range(i + 1, 4)]
    ok = (len(stab) == 7 and all(in_span(x, stab) for x in xside + [theta_x(), ell()])
          and not in_span(thetahat(), stab))
    check("the 2-forms B with B ^ Phi(L) in Phi(L) form a space of dimension 7, "
          "spanned by the six 2-forms pulled back from X and ell; thetahat is not "
          "among them", ok, "dimension %d" % len(stab))

    ok = True
    for d, (f, g, h) in [(Fr(3), (Fr(0), Fr(0), Fr(-1, 2))), (Fr(3), (Fr(1), Fr(1, 2), Fr(1, 3))),
                         (Fr(3), (Fr(-2), Fr(1), Fr(-1, 2))), (Fr(2, 5), (Fr(1, 3), Fr(-1), Fr(1, 2)))]:
        B = add(sc(f, theta_x()), sc(g, thetahat()), sc(h, ell()))
        eB = expo(B)
        V = span_basis([wedge(eB, u) for u in PL])
        inter = intersection(invariants(d), V)
        eg = expo(sc(g, eta(d)))
        ok = ok and len(inter) == 2 and in_span(eg, inter) and in_span(wedge(eg, {255: Fr(1)}), inter)
    check("e^{B} Phi(L) meets the invariants exactly in e^{g eta} span(1, pt) "
          "for B = f theta + g thetahat + h ell (four cases, h = -1/2 included)", ok)

    # Lemma Q: the ideal sheaf of the graph of R in Q(zeta_5)
    mk = field(5)
    dd = [mk(Fr(5, 2), Fr(1, 2)), mk(Fr(5, 2), Fr(-1, 2))]
    Rt = [mk(Fr(1, 2), Fr(1, 2)), mk(Fr(1, 2), Fr(-1, 2))]
    projs = [ProjK(dd[0], mk), ProjK(dd[1], mk)]
    thK = sc(mk(1), theta_x())
    ok, indep = True, True
    for twist in (False, True):
        a = [expo(thK) if twist else one(mk(1)) for _ in range(2)]
        b = [graph_class(Rt[j], mk(1), expo(sc(Rt[j] * Rt[j], thK)) if twist else one(mk(1)))
             for j in range(2)]
        Pa = [orlov(x) for x in a]
        Pb = [orlov(x) for x in b]
        indep = indep and all(rank_K([Pa[j], Pb[j]], mk) == 2 for j in range(2))
        for t in (Fr(0), Fr(1, 2), Fr(1)):
            et = expo(sc(mk(t), sc(mk(1), ell())))
            pieces = [(mk(1), wedge(Pa[0], et), wedge(Pa[1], et)),
                      (mk(-1), wedge(Pb[0], et), wedge(Pb[1], et))]
            _, rest = tensor_split(pieces, projs)
            ok = ok and bool(rest)
    check("Q(zeta_5), graph of R: ch Phi(I_Gamma (x) L) e^{t ell} is not flat for "
          "L in {O, p_1^* O(theta)} and t in {0, 1/2, 1}; the two terms are "
          "independent at each place", ok and indep)


# ------------------------------------------------------------------ (F)
def annihilator_dim(u, mk=None):
    imgs = [wedge(gen(i, mk(1) if mk else Fr(1)), u) for i in range(8)]
    imgs += [interior(u, {i: (mk(1) if mk else Fr(1))}) for i in range(8)]
    r = rank_K(imgs, mk) if mk else dict_rank_Q(imgs)
    return 16 - r


def part_F():
    print("(F) pure spinors, one place")
    ok = True
    for d in (Fr(1), Fr(3), Fr(2, 5)):
        B = [lin_to_mat(X) for X in su_basis(d)]
        rows = []
        for X in B:
            for i in range(8):
                for j in range(8):
                    r = [Fr(0)] * 64
                    for k in range(8):
                        r[i * 8 + k] += X[k][j]
                        r[k * 8 + j] -= X[i][k]
                    rows.append(r)
        ns = nullspace_Q(rows, 64)
        M = lin_to_mat(Mstar(d))
        Mv = [M[i][j] for i in range(8) for j in range(8)]
        Iv = [Fr(int(i == j)) for i in range(8) for j in range(8)]
        M2 = [[sum(M[i][k] * M[k][j] for k in range(8)) for j in range(8)] for i in range(8)]
        ok = (ok and len(ns) == 2 and rank_Q(ns + [Mv, Iv], 64) == 2 and
              M2 == [[-d * Fr(int(i == j)) for j in range(8)] for i in range(8)])
    check("the commutant of su_j(d) on H^1(A_j) is span(1, M*) with M*^2 = -d, a "
          "field, so H^1(A_j) is irreducible (d = 1, 3, 2/5)", ok)

    ok = True
    for d in (Fr(1), Fr(3), Fr(2, 5)):
        inv = invariants(d)
        bydeg = [sum(1 for v in inv if popc(next(iter(v))) == k) for k in range(9)]
        I, _ = inv_basis(d)
        ok = ok and bydeg == [1, 0, 1, 0, 3, 0, 1, 0, 1] and dict_rank_Q(inv + I) == 7 \
            and dict_rank_Q(I) == 7
    check("the invariants of su_j(d) in H^*(A_j) have dimensions 1, 1, 3, 1, 1 in "
          "degrees 0, 2, 4, 6, 8, spanned by 1, eta, eta^2, Omega, Lambda, eta^3, "
          "eta^4; in degree 2 only eta (d = 1, 3, 2/5)", ok)

    cases = [(1, 1, 0), (2, 1, 1), (1, -1, 2), (3, 2, -1), (1, 0, 1), (0, 1, 1), (2, 3, 1)]
    dims = []
    for b, a, c in cases:
        v = orlov(graph_class(b, a, expo(sc(Fr(c), theta_x()))))
        dims.append(annihilator_dim(v))
        dims.append(annihilator_dim(wedge(v, expo(sc(Fr(1, 2), ell())))))
    check("Phi of line bundles on %d graphs are pure spinors: annihilator of "
          "dimension 8 in V + V^*, also after e^{ell/2}" % len(cases),
          all(x == 8 for x in dims))
    mk = field(5)
    w = orlov(W_class(Fr(1)))
    aw, ao = annihilator_dim(w), annihilator_dim(omega_w(Fr(1)))
    th = add(sc(mk(1), theta_x()), sc(mk(-1), thetahat()))
    x = sub(th, sc(mk(0, 0, 1), sc(mk(1), ell())))
    ax = annihilator_dim(wedge(x, x), mk)
    check("the flat classes w and Omega are not pure (annihilators of dimension "
          "%d and %d), while the Weil class (gamma - s ell)^2 is pure over C "
          "(dimension %d), d = 1" % (aw, ao, ax), aw < 8 and ao < 8 and ax == 8)


# ------------------------------------------------------------------ (G)
def part_G():
    print("(G) Orlov products with negative Ext groups")
    rng = random.Random(19)
    ok = True
    mons4 = [m for m in range(256) if popc(m) == 4]
    for _ in range(40):
        v = {m: Fr(rng.randint(-5, 5)) for m in rng.sample(mons4, 30)}
        v = {m: c for m, c in v.items() if c}
        top = wedge(v, v).get(255, Fr(0))
        ok = ok and top.denominator == 1 and top.numerator % 2 == 0
    check("int v_4 ^ v_4 is even for integral 4-forms on an 8-dimensional torus "
          "(40 random classes), so chi(v, v) is even", ok)

    N = 200000
    sq = bytearray([1]) * N
    for p in range(2, int(N ** 0.5) + 1):
        for k in range(p * p, N, p * p):
            sq[k] = 0
    surv = []
    for D in range(2, N):
        if not sq[D]:
            continue
        mod = D if D % 4 == 1 else 2 * D
        for m in (1, 2, 3):
            if (4 * m - 16) % mod:
                continue
            if m % 4 not in (0, 1):
                continue
            if D % 4 == 2 and m % 2:
                continue
            surv.append((D, m))
    check("chi = 4 with (rho, N_w) = (2, 4): m = mu^2 Nm(Delta) in {1, 2, 3}, and "
          "the congruences (a) 4m = 16 mod d cap Z, (b) m = 0, 1 mod 4, (c) m even "
          "when D = 2 mod 4 leave only D = 3, m = 1 among squarefree D < 200000",
          surv == [(3, 1)], "survivors: %s" % surv)
    nu = {"(1,4)": min((chi - 18 + 14) // 2 for chi in range(8, 60, 4)),
          "(2,2)": min((chi - 12 + 14) // 2 for chi in range(2, 60, 2)),
          "(2,4)": min((chi - 20 + 14) // 2 for chi in [4] + list(range(8, 60, 2)))}
    check("nu = (chi - r^2 + 14)/2 with r^2 = 18, 12, 20: nu >= 2 for (1,4) "
          "(chi in 4Z, chi >= 8) and (2,2) (chi >= 2 even); for (2,4) nu >= 1 "
          "unless chi = 4, where nu = -1", nu == {"(1,4)": 2, "(2,2)": 2, "(2,4)": -1}
          and min((chi - 6) // 2 for chi in range(8, 60, 2)) == 1, "%s" % nu)


# ------------------------------------------------------------------ (H)
def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def phi(N):
    return sum(1 for k in range(1, N + 1) if gcd(k, N) == 1)


def part_H():
    print("(H) bookkeeping for the Prym loci")
    quart = [N for N in range(3, 200) if phi(N) == 4]
    check("phi(N) = 4 exactly for N = 5, 8, 10, 12 (N < 200), and Q(zeta_10) = "
          "Q(zeta_5): the quartic cyclotomic fields are Q(zeta_5), Q(zeta_8), "
          "Q(zeta_12)", quart == [5, 8, 10, 12])
    ok = all(3 * g - 3 < (phi(N) // 2) * (g - 1) ** 2
             for N in range(3, 200) if phi(N) >= 4 for g in range(3, 60))
    ok = ok and 3 * 3 - 3 == 6 and (4 // 2) * (3 - 1) ** 2 == 8
    check("3g - 3 < (phi(N)/2)(g - 1)^2 whenever phi(N) >= 4 and g >= 3 (N < 200, "
          "g < 60): the Prym loci never fill D_F; at g = 3, phi(N) = 4 the "
          "bound is 6 < 8", ok)
    # a hyperbolic hermitian form of F-dimension 2n has det = (-1)^n
    ok = True
    for n in range(1, 6):
        M = [[Fr(0)] * (2 * n) for _ in range(2 * n)]
        for i in range(n):
            M[i][n + i] = M[n + i][i] = Fr(1)
        det = det_Q(M)
        ok = ok and det == (-1) ** n
    check("a split (hyperbolic) hermitian form of F-dimension 2n has determinant "
          "(-1)^n, so delta = [det H] is trivial for n = g - 1 = 2", ok)


def det_Q(M):
    M = [row[:] for row in M]
    n = len(M)
    det = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            det = -det
        det *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for k in range(c, n):
                M[r][k] -= f * M[c][k]
    return det


if __name__ == "__main__":
    t_start = time.time()
    print("(LIX) kernels on X x X for a quartic CM field at n = 2")
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    part_H()
    print()
    print("  total time %.0fs" % (time.time() - t_start))
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
