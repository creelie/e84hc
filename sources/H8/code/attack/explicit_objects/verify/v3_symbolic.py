"""v3_symbolic.py -- T3 claim 5 (i),(ii),(iii) and the n=2 ratio R=3/4 for d a SYMBOL:
coefficients in the rational function field Q(d) (sympy FracElement), exact.
By bilinearity of ch(Phi(F1 [x] F2^vee)) in (ch F1, ch F2), the four basis pairs
(u,u),(u,v),(v,u),(v,v) prove flatness for all secant pairs."""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as F
from math import factorial, comb
from sympy import QQ
from sympy.polys.fields import field
from ea import *
from orl import betaX, dualch, orlov

K, D = field("d", QQ)
t0 = time.time()


def secant_sym(n, a, b):
    t = betaX(n)
    u = add(*[sc(K(QQ((-1) ** j, factorial(2 * j))) * D ** j, power(t, 2 * j)) for j in range(n // 2 + 1)])
    v = add(*[sc(K(QQ((-1) ** j, factorial(2 * j + 1))) * D ** j, power(t, 2 * j + 1)) for j in range((n - 1) // 2 + 1)])
    return add(sc(K(a), u), sc(K(b), v))


def model_sym(n):
    m = 2 * n
    x = lambda i: i
    xi = lambda i: m + i
    beta = add(*[mul(g(x(j)), g(x(n + j))) for j in range(n)])
    bhat = add(*[mul(g(xi(j)), g(xi(n + j))) for j in range(n)])
    ell = add(*[mul(g(x(i)), g(xi(i))) for i in range(m)])
    eta = add(sc(K(D), beta), bhat)

    def Bx(i):
        return g(xi(n + i)) if i < n else g(xi(i - n), F(-1))
    # S_k = coefficient of s^k in wedge_i (x_i + s B x_i): expand by subsets
    S = [dict() for _ in range(m + 1)]
    # dynamic programming over i
    cur = {0: one()}
    for i in range(m):
        nxt = {}
        for k, w in cur.items():
            a = mul(w, g(x(i)))
            b = mul(w, Bx(i))
            nxt[k] = add(nxt.get(k, {}), a)
            nxt[k + 1] = add(nxt.get(k + 1, {}), b)
        cur = nxt
    # tau = delta/d, delta^2 = -d:  tau^k = (-d)^{k/2}/d^k (k even), delta*(-d)^{(k-1)/2}/d^k (k odd)
    re, im = {}, {}
    for k, w in cur.items():
        if k % 2 == 0:
            re = add(re, sc(K(QQ((-1) ** (k // 2))) * D ** (k // 2) / D ** k, w))
        else:
            im = add(im, sc(K(QQ((-1) ** ((k - 1) // 2))) * D ** ((k - 1) // 2) / D ** k, w))
    return beta, bhat, ell, eta, re, im


for n in (2, 3):
    beta, bhat, ell, eta, re, im = model_sym(n)
    basis = [power(eta, k) for k in range(2 * n + 1)] + [re, im]
    eh = expo(sc(F(1, 2), ell))
    allok = True
    for p in [(1, 0), (0, 1)]:
        for q in [(1, 0), (0, 1)]:
            ch = orlov(n, secant_sym(n, *p), dualch(secant_sym(n, *q)))
            x0 = solve(ch, basis)
            x = solve(mul(ch, eh), basis)
            ok = x is not None and x0 is None
            line = "n=%d pair %s,%s: ch(E) flat over Q(d): %s; ch(E)e^{ell/2} flat over Q(d): %s" % (n, p, q, x0 is not None, x is not None)
            if x is not None:
                c = x[:2 * n + 1]
                mu = [c[k] * factorial(k) for k in range(2 * n + 1)]
                rec = all(mu[k + 2] + mu[k] / (4 * D) == 0 for k in range(2 * n - 1))
                ok = ok and rec
                line += "; weil coords (re,im) = (%s, %s); mu_{m+2} = -mu_m/(4d): %s" % (x[-2], x[-1], rec)
                if n == 2 and p == q:
                    om = add(sc(x[-2], re), sc(x[-1], im))
                    top = tuple(range(4 * n))
                    R = c[2] ** 2 * power(eta, 4)[top] / mul(om, om)[top]
                    line += "; c1 = %s, c3 = %s, R = %s" % (c[1], c[3], R)
            allok = allok and ok
            print(line + "  (%.1fs)" % (time.time() - t0), flush=True)
    print("n=%d: all four basis pairs flat after e^{ell/2}, not before, rho<=2 recursion, for d symbolic: %s" % (n, allok), flush=True)
