#!/usr/bin/env python3
# Supporting script for item (LXI), code/k3_hodge.py (round 19, (F3') through motives).
"""
Exact check of the two spanning statements used for K3 surfaces and
K3^[n]-type varieties whose transcendental endomorphism field E is CM:

  (a) the norm-one elements u (u * conj(u) = 1) span E over Q;
  (b) the elements u + conj(u), u of norm one, span the totally real subfield
      E_0 over Q.

(a) gives the Hodge conjecture for S x S when E is CM (Buskin: Hodge isometries
are algebraic); (b) gives the algebraicity of all Hodge classes of Sym^2 T on a
K3^[n]-type variety when E is CM (Markman: Hodge isometries are algebraic).

Norm-one elements are produced as u = x / conj(x) (Hilbert 90) for random x in
Z[theta]; all arithmetic is exact in Q[t]/(f(t)).
"""
import random
import sympy as sp

random.seed(7)
t = sp.symbols('t')

def field(minpoly, conj_image):
    """minpoly in t; conj_image: polynomial in t giving conj(theta)."""
    f = sp.Poly(minpoly, t, domain='QQ')
    d = f.degree()
    def red(p):
        return sp.Poly(p, t, domain='QQ').rem(f)
    def mul(a, b):
        return red(a.as_expr()*b.as_expr())
    def inv(a):
        return sp.Poly(sp.invert(a.as_expr(), f.as_expr(), t), t, domain='QQ')
    def conj(a):
        return red(a.as_expr().subs(t, conj_image))
    def vec(a):
        c = a.all_coeffs()[::-1]
        return c + [0]*(d - len(c))
    return d, red, mul, inv, conj, vec

def span_dim(vectors):
    return sp.Matrix(vectors).rank()

cases = [
    ("Q(sqrt(-5))", t**2 + 5, -t, 1),
    ("Q(zeta_5)", sp.cyclotomic_poly(5, t), t**4, 2),
    ("Q(zeta_8)=Q(i,sqrt2)", sp.cyclotomic_poly(8, t), t**7, 2),
    ("Q(zeta_12)=Q(i,sqrt3)", sp.cyclotomic_poly(12, t), t**11, 2),
    ("quartic CM, a^2=-(2+sqrt2)", t**4 + 4*t**2 + 2, -t, 2),
    ("quartic non-Galois (D4) CM, a^2=-(3+sqrt3)", t**4 + 6*t**2 + 6, -t, 2),
    ("Q(zeta_7)", sp.cyclotomic_poly(7, t), t**6, 3),
    ("Q(zeta_9)", sp.cyclotomic_poly(9, t), t**8, 3),
    ("Q(zeta_15)", sp.cyclotomic_poly(15, t), t**14, 4),
    ("Q(zeta_11)", sp.cyclotomic_poly(11, t), t**10, 5),
]

all_ok = True
for name, mp, cimg, deg0 in cases:
    d, red, mul, inv, conj, vec = field(mp, cimg)
    # sanity: conj is an involutive automorphism
    th = red(t)
    assert conj(conj(th)) == th
    assert red(sp.Poly(mp, t).as_expr().subs(t, conj(th).as_expr())).is_zero
    # CM check: E_0 = fixed field has degree d/2; totally real / totally imaginary
    roots = sp.Poly(mp, t).nroots(n=30)
    totally_imag = all(abs(sp.im(r)) > 1e-12 for r in roots)
    us, ss = [], []
    for _ in range(4*d):
        x = red(sum(random.randint(-3, 3)*t**k for k in range(d)))
        if x.is_zero:
            continue
        u = mul(x, inv(conj(x)))
        assert mul(u, conj(u)) == red(sp.Integer(1))       # norm one
        us.append(vec(u))
        ss.append(vec(red(u.as_expr() + conj(u).as_expr())))
    du, ds = span_dim(us), span_dim(ss)
    # E_0 = fixed vectors of conj
    C = sp.Matrix([vec(conj(red(t**k))) for k in range(d)]).T
    d0 = d - (C - sp.eye(d)).rank()
    ok = (du == d) and (ds == d0 == deg0) and totally_imag
    all_ok &= ok
    print(f"{name:45s} [E:Q]={d}  [E0:Q]={d0}  totally imaginary={totally_imag}  "
          f"dim span(u)={du}  dim span(u+ubar)={ds}  {'OK' if ok else 'FAIL'}")

print("ALL OK" if all_ok else "SOME CASE FAILED")
