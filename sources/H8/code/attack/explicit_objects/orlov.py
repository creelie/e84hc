"""
orlov.py -- Chern character of Orlov's transform Phi(F1 [x] F2^vee) on X x X^.

Phi: D(X x X) -> D(X x X^),  Phi(K) = (1 x Phi_P)(mu_* K),  mu(a,b) = (a-b, b),
so Phi(O_Delta) = k(0)[-n].  ch(Phi K) = p_{13*}( (mu^{-1})^* ch K . e^{ell_23} ),
with ell = c_1(P) = sum_i x_i xi_i (td = 1 throughout).
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial
from ext import *

def orlov_ch(n, chF1, chF2dual):
    m = 2 * n
    X1 = lambda i: i
    X2 = lambda i: m + i
    XI = lambda i: 2 * m + i
    N3 = 3 * m
    # ch(F1)(x1 + x2)
    im1 = {i: {1 << X1(i): Fr(1), 1 << X2(i): Fr(1)} for i in range(m)}
    c1 = substitute(chF1, im1, m)
    im2 = {i: {1 << X2(i): Fr(1)} for i in range(m)}
    c2 = substitute(chF2dual, im2, m)
    ell23 = eadd(*[wedge(gen(X2(i)), gen(XI(i))) for i in range(m)])
    k = wedge(wedge(c1, c2), eexp(ell23, 2 * m))
    block = ((1 << m) - 1) << m
    sgn = Fr((-1) ** (n * (n - 1) // 2))
    out = {}
    for mask, c in k.items():
        if mask & block == block:
            rest = mask & ~block
            x1 = rest & ((1 << m) - 1)
            xi = rest >> (2 * m)
            newm = x1 | (xi << m)
            out[newm] = out.get(newm, 0) + sgn * c
    return {a: b for a, b in out.items() if b != 0}

def beta_X(n):
    return eadd(*[wedge(gen(j), gen(n + j)) for j in range(n)])

def pt_X(n):
    return escale(Fr(1, factorial(n)), epow(beta_X(n), n))

def dual(ch):
    """ch(F^vee): multiply degree-k part by (-1)^k."""
    return {m: (c if popcount(m) % 4 == 0 else -c) for m, c in ch.items()}  # degree 2j -> (-1)^j

def orlov_ch_fast(n, chF1, chF2dual):
    """same as orlov_ch, integrating e^{ell_23} monomial by monomial."""
    m = 2 * n
    im1 = {i: {1 << i: Fr(1), 1 << (m + i): Fr(1)} for i in range(m)}
    c1 = substitute(chF1, im1, m)
    im2 = {i: {1 << (m + i): Fr(1)} for i in range(m)}
    c2 = substitute(chF2dual, im2, m)
    prod = wedge(c1, c2)
    full = (1 << m) - 1
    sgn0 = (-1) ** (n * (n - 1) // 2)
    out = {}
    for mask, c in prod.items():
        A = mask & full
        B = (mask >> m) & full
        Bc = full ^ B
        k = popcount(Bc)
        s = sgn0 * ((-1) ** (k * (k - 1) // 2)) * wsign(B, Bc)
        key = A | (Bc << m)
        out[key] = out.get(key, 0) + (c if s > 0 else -c)
    return {a: b for a, b in out.items() if b != 0}

def secant(n, d, a, b):
    """a u_t + b v_t with t = beta (principal)."""
    t = beta_X(n)
    u, v = {0: Fr(1)}, {}
    for j in range(1, n // 2 + 1):
        u = eadd(u, escale(Fr((-d) ** j, factorial(2 * j)), epow(t, 2 * j)))
    for j in range(0, (n - 1) // 2 + 1):
        v = eadd(v, escale(Fr((-d) ** j, factorial(2 * j + 1)), epow(t, 2 * j + 1)))
    return eadd(escale(Fr(a), u), escale(Fr(b), v))
