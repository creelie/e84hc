"""a1_rkappa_general.py -- the formula r(kappa) = r^2(v_1) + 64 + r^2(v_2) of
thm:quarticobstruction for pairs of different secant classes, and for the
biquadratic case with N_w = 2 (track A1).

a1_rkappa.py checks r(kappa) = 100 and 104 for E = Phi(F [x] F^vee) over
F0 = Q(sqrt 5).  Here, with the same method (rank modulo a prime as a lower
bound, an exact annihilator over Q(i) as an upper bound):
  * F = Q(sqrt 5)(sqrt(-(2 + phi))): the mixed pair (w, v_1), r^2 = 18 and 20,
    predicted 18 + 64 + 20 = 102;
  * F = Q(sqrt 5, i), q = 1, biquadratic: the class v_theta = theta - theta^3/6
    of the secant plane of Q(i), with (rho, N_w) = (2, 2) and r^2 = 12, alone
    (12 + 64 + 12 = 88) and paired with w (12 + 64 + 18 = 94);
  * F0 = Q(sqrt 2), q = 2 + sqrt 2: the pairs (w, w) and (v_1, v_1), 100 and 104.
So the values of r(kappa) are not only 100, 102, 104: for biquadratic F the
classes with N_w = 2 give 88 and 94 (and 96 with a class of rank two).
"""
from fractions import Fraction as Fr
from ealib import *
from a1model import RMModel
import amodel
from amodel import AModel
from orlov import orlov
import a1_secant as SEC
from a1_rkappa import analyse


def a_model(q, X):
    saved = amodel.RMModel
    amodel.RMModel = lambda Rm=None: X
    try:
        return AModel(q)
    finally:
        amodel.RMModel = saved


def kappa_of(Am, X, v1, v2):
    ch = orlov(4, v1, X.dual(v2))
    return wedge(ch, expo(sc(Fr(1, 2), Am.ell())))


def secant(X, q, a, f, c):
    return SEC.rational(X.from_V(SEC.Vmat_of(a, f, c, q)))


def main():
    X5 = RMModel()
    SEC.M = X5
    SEC.S = X5.disc
    q = (2, 1)
    Am = a_model(q, X5)
    w = secant(X5, q, 0, (0, 0), 1)
    v1 = secant(X5, q, 0, (1, 0), 0)
    check("F0 = Q(sqrt 5), q = %s: the secant profiles of w and v_1 are (1, 8, 18) and "
          "(1, 8, 20)" % (q,), X5.profile(w, 2)[:3] == [1, 8, 18] and X5.profile(v1, 2)[:3] == [1, 8, 20])
    analyse(kappa_of(Am, X5, w, v1), "Q(sqrt 5), q=%s, pair (w, v_1)" % (q,), 102)
    q = (1, 0)
    Am = a_model(q, X5)
    th = X5.theta
    vth = add(th, sc(Fr(-1, 6), power(th, 3)))
    w = secant(X5, q, 0, (0, 0), 1)
    check("F = Q(sqrt 5, i): v_theta has profile (1, 8, 12) and w has (1, 8, 18)",
          X5.profile(vth, 2)[:3] == [1, 8, 12] and X5.profile(w, 2)[:3] == [1, 8, 18])
    analyse(kappa_of(Am, X5, vth, vth), "Q(sqrt 5, i), pair (v_theta, v_theta)", 88)
    analyse(kappa_of(Am, X5, vth, w), "Q(sqrt 5, i), pair (v_theta, w)", 94)
    X2 = RMModel(((1, 1), (1, -1)))
    SEC.M = X2
    SEC.S = X2.disc
    q = (2, 1)
    Am = a_model(q, X2)
    w = secant(X2, q, 0, (0, 0), 1)
    v1 = secant(X2, q, 0, (1, 0), 0)
    analyse(kappa_of(Am, X2, w, w), "Q(sqrt 2), q=%s, pair (w, w)" % (q,), 100)
    analyse(kappa_of(Am, X2, v1, v1), "Q(sqrt 2), q=%s, pair (v_1, v_1)" % (q,), 104)
    summary()


if __name__ == "__main__":
    main()
