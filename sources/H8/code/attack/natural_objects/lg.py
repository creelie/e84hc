"""
lg.py -- the Lagrangian Grassmannian model of the Hodge ring H_A of
A = X x Xhat, X very general ppav of dimension n (here n = 4).

H^1(A) = U (x) Q^2 and H^1(A) + H_1(A) = U (x) Q^4, Q^4 = <f1, f2, f1*, f2*>
with <f_a, f_b*> = delta_ab.  An Sp(U)-invariant pure spinor has annihilator
U (x) L with L a Lagrangian plane in Q^4, and ch of every natural object
(line bundle, twisted structure sheaf of an abelian subvariety, simple
semi-homogeneous bundle, their Fourier-Mukai transforms) is a rational multiple
of such a spinor.

Pluecker coordinates of L (a point of the quadric threefold Q^3 in P^4):
    P = (p12, p34, p14, p23, p13)   with  3 = f1*, 4 = f2*,
p24 = -p13 (Lagrangian), quadric  p12 p34 + p13^2 + p14 p23 = 0.

Natural points:
  line bundle e^{D_S}, D_S = S11 beta + S22 betahat - S12 ell  <->  L_S
  subtorus  [B_(p,q)]                                            <->  L_(p,q)
  point class                                                     <->  <f1, f2>
The formulas for P are verified in t4_lg.py against the exterior algebra.
"""
from fractions import Fraction as Fr
from itertools import combinations_with_replacement
from ext import *


def pl_from_rows(r1, r2):
    """Pluecker coordinates of the plane spanned by r1, r2 in basis
    (f1, f2, f1*, f2*) = (1,2,3,4); returns (p12, p34, p14, p23, p13) and
    checks Lagrangian condition p13 + p24 = 0."""
    def p(i, j):
        return r1[i] * r2[j] - r1[j] * r2[i]
    p12, p34, p14, p23, p13, p24 = p(0, 1), p(2, 3), p(0, 3), p(1, 2), p(0, 2), p(1, 3)
    assert p13 + p24 == 0, "not Lagrangian"
    return (p12, p34, p14, p23, p13)


def quadric(P):
    p12, p34, p14, p23, p13 = P
    return p12 * p34 + p13 * p13 + p14 * p23


def L_S(S11, S12, S22):
    # graph over the f*-plane:  f1* + S11 f1 + S12 f2,  f2* + S12 f1 + S22 f2
    return pl_from_rows((S11, S12, 1, 0), (S12, S22, 0, 1))


def L_sub(p, q):
    # <q f1 + p f2, p f1* - q f2*>
    return pl_from_rows((q, p, 0, 0), (0, 0, p, -q))


def L_point():
    return pl_from_rows((1, 0, 0, 0), (0, 1, 0, 0))


def twist_rows(rows, S11, S12, S22):
    """apply the transvection f* -> f* + S f (tensoring with e^{D_S})"""
    out = []
    for (a1, a2, b1, b2) in rows:
        out.append((a1 + S11 * b1 + S12 * b2, a2 + S12 * b1 + S22 * b2, b1, b2))
    return out


MONO4 = list(combinations_with_replacement(range(5), 4))


def mono4(P):
    out = {}
    for idx, m in enumerate(MONO4):
        v = 1
        for i in m:
            v = v * P[i]
        if v != 0:
            out[idx] = v
    return out
