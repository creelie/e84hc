"""a1_flat.py -- Orlov products of F-secant classes are flat for the quartic CM
field F = F0(sqrt(-q)) (track A1).

For v1, v2 in S_F(q) (a1_secant), E = Phi(F1 [x] F2^vee) on A = X x Xhat has
ch(E) = orlov(v1, v2^vee).  We check EXACTLY over Q:
  (a) kappa = ch(E) exp(ell/2) is killed by two elements X1, X2 of g_F = su(V,H)
      which generate g_F (Lie closure of dimension 30, lower bound mod p; g_F has
      dimension 30 exactly), hence kappa is G_F-invariant, i.e. a Hodge class on
      every member of the (F,2)-family through A (flat along T_[A] D_F);
  (b) ch(E) itself is not G_F-invariant;
  (c) the degree-2 G_F-invariants form a 2-dimensional space I2 (the classes eta_t),
      and the degree-4 part kappa_4 does NOT lie in I2.I2 (the Lefschetz part):
      since H^4(A,Q)^{G_F} = I2.I2 (+) W_F (prop:quarticquat(i)), kappa_4 has a nonzero
      component in the Weil space W_F;
  (d) for a K-secant class (q = 1, v in P_theta(1)), kappa_4 lies in I2.I2 (no W_F part).
Usage: python3 a1_flat.py [cases]
"""
import sys, time, random
from fractions import Fraction as Fr
from ealib import *
from a1model import RMModel, QS
from amodel import AModel
from orlov import orlov
from gf import lie_algebra, lie_closure_dim_modp, random_element
import a1_secant as SEC

t0 = time.time()


def lift8(u):
    """class on X (8 generators) -> pr_X^* on A (x = bits 0..7)."""
    return dict(u)


def invariants_deg(k, Xs, n=16):
    """exact rational basis of the degree-k classes killed by the derivations Xs."""
    import itertools
    monos = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]
    cols = []
    for m in monos:
        img = {}
        for j, A in enumerate(Xs):
            d = derivation(A, {m: Fr(1)})
            for kk, c in d.items():
                img[(j, kk)] = c
        cols.append(img)
    ker = nullspace_Q(cols)
    return [clean({monos[i]: c for i, c in enumerate(vec) if c != 0}) for vec in ker]


def in_span(target, basis):
    r0 = rank_Q(basis)
    return rank_Q(basis + [target]) == r0


def run_case(q, v1, v2, label, Xs, I2, L4, expect_weil=True):
    tt = time.time()
    ch = orlov(4, v1, SEC.M.dual(v2))
    Am = AModel(q)
    ell = Am.ell()
    kappa = wedge(ch, expo(sc(Fr(1, 2), ell)))
    rk = ch.get(0, 0)
    flat_ch = all(derivation(X, ch) == {} for X in Xs)
    flat_k = all(derivation(X, kappa) == {} for X in Xs)
    check("%s: kappa = ch(E) e^{ell/2} is g_F-invariant (flat)  [rank ch E = %s, %d terms]" % (label, rk, len(kappa)),
          flat_k)
    check("%s: ch(E) itself is not g_F-invariant" % label, not flat_ch)
    k2 = deg(kappa, 2)
    check("%s: kappa_2 lies in the 2-dim space of degree-2 invariants" % label, in_span(k2, I2) if k2 else True)
    k4 = deg(kappa, 4)
    inL = in_span(k4, L4) if k4 else True
    if expect_weil:
        check("%s: kappa_4 not in Lefschetz part I2.I2 (nonzero W_F component)" % label, not inL)
    else:
        check("%s: kappa_4 in Lefschetz part (no W_F component), as expected for a K-secant class" % label, inL)
    print("     (%.1fs)" % (time.time() - tt), flush=True)
    return kappa


if __name__ == "__main__":
    cases = sys.argv[1:] if len(sys.argv) > 1 else ["main"]
    print("A1 flatness of Orlov products for quartic F; F0 = Q(sqrt5)")
    qlist = [(2, 1), (3, -1)] if "main" in cases else []
    for q in qlist:
        Am = AModel(q)
        eta = add(Am.beta_f(q), Am.betahat())
        B = lie_algebra(Am, eta)
        check("q=%s: dim g_F = 30" % (q,), len(B) == 30)
        rng = random.Random(7)
        Xm = [random_element(B, rng), random_element(B, rng)]
        check("q=%s: two elements generate g_F (closure dim mod p = 30)" % (q,), lie_closure_dim_modp(Xm) == 30)
        Xs = [mat_to_A(X) for X in Xm]
        I2 = invariants_deg(2, Xs)
        check("q=%s: degree-2 G_F-invariants have dimension 2" % (q,), len(I2) == 2)
        check("q=%s: eta = beta_q + betahat is invariant" % (q,), in_span(eta, I2))
        L4 = [wedge(a, b) for a in I2 for b in I2]
        check("q=%s: Lefschetz part I2.I2 has dimension 3" % (q,), rank_Q(L4) == 3)
        print("     setup %.1fs" % (time.time() - t0), flush=True)
        shapes = {"w": (0, (0, 0), 1), "u": (1, (0, 0), 0), "v_1": (0, (1, 0), 0),
                  "gen": (1, (1, 1), 2)}
        vs = {}
        for name, (a, f, c) in shapes.items():
            V = SEC.Vmat_of(a, f, c, q)
            vs[name] = SEC.rational(SEC.M.from_V(V))
        for (n1, n2) in [("w", "w"), ("v_1", "v_1"), ("u", "u"), ("gen", "gen"), ("w", "v_1")]:
            run_case(q, vs[n1], vs[n2], "q=%s F1=%s F2=%s" % (q, n1, n2), Xs, I2, L4)
    if "ktype" in cases or "main" in cases:
        q = (1, 0)
        Am = AModel(q)
        eta = add(Am.beta_f(q), Am.betahat())
        B = lie_algebra(Am, eta)
        rng = random.Random(7)
        Xm = [random_element(B, rng), random_element(B, rng)]
        check("q=1: two elements generate g_F", lie_closure_dim_modp(Xm) == 30)
        Xs = [mat_to_A(X) for X in Xm]
        I2 = invariants_deg(2, Xs)
        L4 = [wedge(a, b) for a in I2 for b in I2]
        th = SEC.M.theta
        vth = add(th, sc(Fr(-1, 6), power(th, 3)))
        run_case(q, vth, vth, "q=1 (F=Q(sqrt5,i)) K-secant v_theta", Xs, I2, L4, expect_weil=False)
        # a class of S_F(1) with both Galois orbits nonzero: w = theta1 theta2
        V = SEC.Vmat_of(0, (0, 0), 1, q)
        w = SEC.rational(SEC.M.from_V(V))
        run_case(q, w, w, "q=1 (F=Q(sqrt5,i)) w = theta1 theta2", Xs, I2, L4, expect_weil=True)
    print("total %.1fs" % (time.time() - t0))
    summary()
