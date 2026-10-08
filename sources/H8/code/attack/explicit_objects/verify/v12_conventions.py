"""v12_conventions.py -- is the conclusion 'flat only after a B-field with ell-coefficient +-1/2' independent of
the convention for Orlov's equivalence?  Variants: mu(a,b)=(a-b,b) or (a+b,b); kernel P or P^vee;
F1 [x] F2^vee or F1^vee [x] F2."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from ea import *
from model import Model
from orl import secant, dualch
def orl_var(n, c1, c2, musign, psign):
    m = 2 * n; Y = 4 * n
    # mu_* = (mu^{-1})^*: mu(a,b) = (a + musign*(-1)*b ...) ; for mu(a,b)=(a-b,b): mu^{-1}(u,v)=(u+v,v)
    s = F(1) if musign < 0 else F(-1)
    a = linsub(c1, {i: add(g(i), sc(s, g(Y + i))) for i in range(m)})
    b = linsub(c2, {i: g(Y + i) for i in range(m)})
    A = mul(a, b)
    ell = add(*[mul(g(Y + i), g(m + i)) for i in range(m)])
    prod = mul(A, expo(sc(F(psign), ell)))
    ytop = tuple(range(Y, Y + m)); s0 = F((-1) ** (n * (n - 1) // 2))
    out = {}
    for k, c in prod.items():
        if len(k) >= m and k[-m:] == ytop:
            out[k[:-m]] = out.get(k[:-m], 0) + s0 * c
    return clean(out)
for n, d in [(2, 2), (3, 2)]:
    M = Model(n, d)
    e = M.eta(); re, im = M.weil_pm()
    basis = [power(e, k) for k in range(2 * n + 1)] + [re, im]
    l = M.ell()
    for musign in (-1, +1):
        for psign in (1, -1):
            for dualfirst in (False, True):
                res = []
                for p, q in [((0, 1), (0, 1)), ((1, 0), (0, 1)), ((1, 1), (1, 2))]:
                    f1, f2 = secant(n, d, *p), secant(n, d, *q)
                    c1, c2 = (dualch(f1), f2) if dualfirst else (f1, dualch(f2))
                    ch = orl_var(n, c1, c2, musign, psign)
                    flags = []
                    for cB in (F(0), F(1, 2), F(-1, 2), F(1), F(-1)):
                        flags.append(solve(mul(ch, expo(sc(cB, l))), basis) is not None)
                    res.append(tuple(cB for cB, fl in zip(("0", "+1/2", "-1/2", "+1", "-1"), flags) if fl))
                print("n=%d d=%d mu=(a%sb,b) kernel=%s %s: ell-coefficients c with ch(E)e^{c ell} flat, per pair: %s" % (
                    n, d, "-" if musign < 0 else "+", "P" if psign > 0 else "P^vee",
                    "F1^vee[x]F2" if dualfirst else "F1[x]F2^vee", res), flush=True)
