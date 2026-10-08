#!/usr/bin/env python3
"""
A2 / lagrangian_check.py -- flatness of kappa = ch(Phi(F1 x F2^vee)) e^{ell/2} for ALL n.

Structural reduction (report, Prop. I): everything in the Orlov template is
Sp(U)-equivariant, U = H_1(X,Q) with the symplectic form t; the Mukai space of
X x X (and of X x X^) is U (x) Q^4, Phi^H is the spin lift of id_U (x) g, the
B-field e^{ell/2} is the spin lift of id_U (x) b, and the four products
e^{+-s t} [x] e^{+-s t}, the Weil classes alpha_+-, and e^{c eta} are pure spinors
of Lagrangians U (x) L with L in LG(2,4) independent of n.  Pure spinor lines
determine Lagrangians, so the four identities
     e^{ell/2} Phi^H( e^{s1 s t} [x] e^{s2 s t} )  proportional to  one of
     alpha(+s), alpha(-s), e^{(s/2d) eta}, e^{-(s/2d) eta}
hold for every n as soon as they hold for one n.  We verify them here exactly,
with d a free symbol (s^2 = -d), at n = 1 and n = 2, in the conventions of the
paper's code (code/attack/explicit_objects/orlov.py, split.py), which is imported
read-only.
"""
import os
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "explicit_objects"))
import sympy as sp
from fractions import Fraction as Fr

dsym = sp.symbols('d', positive=True)


class QS:
    """p + q*s with s^2 = -d, p, q in Q(d)."""
    __slots__ = ("p", "q")

    def __init__(self, p, q=0):
        self.p = sp.cancel(sp.sympify(p))
        self.q = sp.cancel(sp.sympify(q))

    @staticmethod
    def c(x):
        if isinstance(x, QS):
            return x
        if isinstance(x, Fr):
            return QS(sp.Rational(x.numerator, x.denominator))
        return QS(x)

    def __add__(self, o):
        o = QS.c(o); return QS(self.p + o.p, self.q + o.q)
    __radd__ = __add__

    def __sub__(self, o):
        o = QS.c(o); return QS(self.p - o.p, self.q - o.q)

    def __rsub__(self, o):
        return QS.c(o) - self

    def __neg__(self):
        return QS(-self.p, -self.q)

    def __mul__(self, o):
        o = QS.c(o)
        return QS(self.p * o.p - dsym * self.q * o.q, self.p * o.q + self.q * o.p)
    __rmul__ = __mul__

    def conj(self):
        return QS(self.p, -self.q)

    def __truediv__(self, o):
        o = QS.c(o)
        nrm = sp.cancel(o.p ** 2 + dsym * o.q ** 2)
        num = self * o.conj()
        return QS(num.p / nrm, num.q / nrm)

    def __rtruediv__(self, o):
        return QS.c(o) / self

    def iszero(self):
        return sp.simplify(self.p) == 0 and sp.simplify(self.q) == 0

    def __eq__(self, o):
        return (self - QS.c(o)).iszero()

    def __hash__(self):
        return 0

    def __repr__(self):
        return f"({self.p} + ({self.q}) s)"


import ext
_orig_iszero = ext.iszero


def _iszero(c):
    if isinstance(c, QS):
        return c.iszero()
    return _orig_iszero(c)


ext.iszero = _iszero
from ext import wedge, eadd, escale, eexp, epow
import orlov
orlov.iszero = _iszero
from orlov import orlov_ch_fast, beta_X
import split
split.iszero = _iszero
from split import Split

S_ = QS(0, 1)  # s


def to_qs(u):
    return {k: QS.c(c) for k, c in u.items()}


def proportional(u, v):
    """are the (nonzero) elements u, v proportional over Q(d)(s)?"""
    keys = set(u) | set(v)
    # find ratio from one key
    k0 = next(k for k in keys if k in u and not u[k].iszero())
    if k0 not in v or v[k0].iszero():
        return False
    lam = u[k0] / v[k0]
    for k in keys:
        a = u.get(k, QS(0)); b = v.get(k, QS(0))
        if not (a - lam * b).iszero():
            return False
    return True


def run(n):
    S = Split(n, 1)  # d enters below only through our own classes
    t = to_qs(beta_X(n))
    ell = to_qs(S.ell())
    beta, betahat = to_qs(S.beta()), to_qs(S.betahat())
    eta = eadd(escale(QS(dsym), beta), betahat)
    gamma0 = eadd(escale(QS(dsym), beta), escale(QS(-1), betahat))
    B = eexp(escale(QS(sp.Rational(1, 2)), ell), 4 * n)
    cands = {}
    for sg in (1, -1):
        delta = S_ * sg
        a = epow(eadd(gamma0, escale(-delta, ell)), n)   # (gamma0 - delta ell)^n
        cands[f"alpha({'+' if sg > 0 else '-'}s)"] = to_qs(a)
        cands[f"exp({'+' if sg > 0 else '-'}s/(2d) eta)"] = to_qs(eexp(escale(delta / QS(2 * dsym), eta), 4 * n))
    ok_all = True
    for s1 in (1, -1):
        for s2 in (1, -1):
            e1 = eexp(escale(S_ * s1, t), 2 * n)
            e2 = eexp(escale(S_ * s2, t), 2 * n)
            g = orlov_ch_fast(n, e1, e2)
            kap = to_qs(wedge(g, B))
            hits = [name for name, cv in cands.items() if proportional(kap, cv)]
            print(f"  n={n}: e^{{{'+' if s1>0 else '-'}st}} [x] e^{{{'+' if s2>0 else '-'}st}}  ->  "
                  f"proportional to {hits}", flush=True)
            ok_all = ok_all and len(hits) == 1
    return ok_all


if __name__ == "__main__":
    allok = True
    for n in (1, 2):
        allok = run(n) and allok
    print("ALL four images are pure spinors from {alpha(+-s), exp(+-s eta/2d)}:", allok)
