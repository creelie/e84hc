"""orl.py -- independent Chern character of Orlov's transform.

Phi(K) = (1 x Phi_P)(mu_* K), mu(a,b) = (a-b, b), Phi_P(G) = p_{2*}(p_1^*G (x) P) with c_1(P) = sum y_i xi_i.
ch(mu_* K)(x, y) = ch(F1)(x + y) ch(F2')(y) for K = F1 [x] F2'.
ch(Phi K) = int_y  ch(F1)(x+y) ch(F2')(y) exp(sum_i y_i xi_i)   (td = 1).
Indices: x -> 0..2n-1, xi -> 2n..4n-1, y -> 4n..6n-1 (so y's come last in sorted monomials).
int_X y_0...y_{2n-1} = (-1)^{n(n-1)/2}  (vol_X = beta^n/n!).
"""
from fractions import Fraction as F
from math import factorial
from ea import *


def betaX(n, off=0):
    return add(*[mul(g(off + j), g(off + n + j)) for j in range(n)])


def secant(n, d, a, b):
    t = betaX(n)
    u = add(*[sc(F((-d) ** j, factorial(2 * j)), power(t, 2 * j)) for j in range(n // 2 + 1)])
    v = add(*[sc(F((-d) ** j, factorial(2 * j + 1)), power(t, 2 * j + 1)) for j in range((n - 1) // 2 + 1)])
    return add(sc(F(a), u), sc(F(b), v))


def dualch(c):
    """ch(F^vee): degree 2k part times (-1)^k."""
    return {k: (x if (len(k) // 2) % 2 == 0 else -x) for k, x in c.items()}


def orlov(n, c1, c2):
    m = 2 * n
    Y = 4 * n
    # c1(x + y)
    im1 = {i: add(g(i), g(Y + i)) for i in range(m)}
    a = linsub(c1, im1)
    im2 = {i: g(Y + i) for i in range(m)}
    b = linsub(c2, im2)
    ellyx = add(*[mul(g(Y + i), g(m + i)) for i in range(m)])
    prod = mul(mul(a, b), expo(ellyx, 2 * m))
    ytop = tuple(range(Y, Y + m))
    s = F((-1) ** (n * (n - 1) // 2))
    out = {}
    for k, c in prod.items():
        if k[-m:] == ytop if len(k) >= m else False:
            rest = k[:-m]
            out[rest] = out.get(rest, 0) + s * c
    return clean(out)
