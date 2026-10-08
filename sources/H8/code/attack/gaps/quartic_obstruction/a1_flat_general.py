"""a1_flat_general.py -- flatness of Orlov products of F-secant classes for quartic
CM fields F = F0(sqrt(-q)) over further real quadratic fields F0 (track A1).

a1_flat.py checks, for F0 = Q(sqrt 5), that kappa = ch(Phi(F1 [x] F2^vee)) e^{ell/2}
is killed by the Lie algebra g_F = su(V,H) of the (F,2)-family through
A = X x Xhat, hence is a Hodge class on every member, and that its degree-4 part
has a nonzero component in the Weil space W_F.  The same checks are run here, in
exact rational arithmetic, for
  Q(sqrt 2), Q(sqrt 13), Q(sqrt 17), Q(sqrt 10)   in the product model S (x) M,
  Q(sqrt 3), Q(sqrt 7)                           on the lattice O^2 + (d^-1)^2,
each with two totally positive q, and for secant classes of the shapes
w = theta_1 theta_2, u, v_1 and a general one.  The proof in the paper
(thm:quarticobstruction) is by factorisation over the two real places of F0 and
reduces to prop:flatall at n = 2; this script is an independent check of it.
Usage: python3 a1_flat_general.py [names]
"""
import sys
import time
import random
from fractions import Fraction as Fr
from ealib import *
import a1model
from a1model import RMModel
import amodel
from amodel import AModel
from orlov import orlov
from gf import lie_algebra, lie_closure_dim_modp, random_element
import a1_secant as SEC
from a1_flat import invariants_deg, in_span, mat_to_A
from a1_lattice_general import LatticeModel

PRODUCT = {"sqrt2": ((1, 1), (1, -1)), "sqrt13": ((2, 1), (1, -1)),
           "sqrt17": ((0, 2), (2, 1)), "sqrt10": ((1, 3), (3, -1))}
LATTICE = {"sqrt3": 3, "sqrt7": 7}
# totally positive q = q0 + q1 r, r the generator acting on H^1 (its eigenvalues
# are the two real embeddings of r); two choices per field
QS = {"sqrt2": [(2, 1), (3, -1)], "sqrt13": [(3, 1), (4, -1)], "sqrt17": [(4, 1), (5, -1)],
      "sqrt10": [(4, 1), (5, -1)], "sqrt3": [(2, 1), (3, -1)], "sqrt7": [(3, 1), (4, -1)]}


def model(name):
    if name in PRODUCT:
        return RMModel(PRODUCT[name])
    return LatticeModel(LATTICE[name])


def a_model(q, X):
    """AModel(q) with the fourfold X substituted for the default Q(sqrt 5) model."""
    saved = amodel.RMModel
    amodel.RMModel = lambda Rm=None: X
    try:
        return AModel(q)
    finally:
        amodel.RMModel = saved


def totally_positive(X, q):
    t1, t2 = X.tau(q)
    return t1.val() > 0 and t2.val() > 0


def run(name):
    t0 = time.time()
    X = model(name)
    SEC.M = X
    SEC.S = X.disc
    for q in QS[name]:
        check("%s q=%s: q is totally positive" % (name, q), totally_positive(X, q))
        Am = a_model(q, X)
        eta = add(Am.beta_f(q), Am.betahat())
        B = lie_algebra(Am, eta)
        check("%s q=%s: dim g_F = 30" % (name, q), len(B) == 30)
        rng = random.Random(7)
        Xm = [random_element(B, rng), random_element(B, rng)]
        check("%s q=%s: two elements generate g_F" % (name, q), lie_closure_dim_modp(Xm) == 30)
        Xs = [mat_to_A(Y) for Y in Xm]
        I2 = invariants_deg(2, Xs)
        L4 = [wedge(a, b) for a in I2 for b in I2]
        check("%s q=%s: degree-2 invariants of dimension 2, eta among them, "
              "Lefschetz part of dimension 3" % (name, q),
              len(I2) == 2 and in_span(eta, I2) and rank_Q(L4) == 3)
        shapes = {"w": (0, (0, 0), 1), "u": (1, (0, 0), 0), "v_1": (0, (1, 0), 0),
                  "gen": (1, (1, 1), 2)}
        vs = {}
        for sh, (a, f, c) in shapes.items():
            vs[sh] = SEC.rational(X.from_V(SEC.Vmat_of(a, f, c, q)))
        for (n1, n2) in [("w", "w"), ("u", "u"), ("gen", "gen"), ("w", "v_1")]:
            ch = orlov(4, vs[n1], X.dual(vs[n2]))
            kappa = wedge(ch, expo(sc(Fr(1, 2), Am.ell())))
            flat = all(derivation(Y, kappa) == {} for Y in Xs)
            k2 = deg(kappa, 2)
            k4 = deg(kappa, 4)
            weil = not in_span(k4, L4) if k4 else False
            check("%s q=%s F1=%s F2=%s: kappa is g_F-invariant, kappa_2 is in the "
                  "degree-2 invariants, and kappa_4 has a nonzero Weil component"
                  % (name, q, n1, n2),
                  flat and (in_span(k2, I2) if k2 else True) and weil)
    print("     %s: %.1fs" % (name, time.time() - t0), flush=True)


if __name__ == "__main__":
    names = sys.argv[1:] or list(PRODUCT) + list(LATTICE)
    for nm in names:
        run(nm)
    summary()
