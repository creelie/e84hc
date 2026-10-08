"""a1_lattice_local.py -- the local computation behind lem:quarticlattice: the
integral classes of the F0-Hodge ring R of a principally polarised abelian
fourfold X with real multiplication by the ring of integers O of ANY real
quadratic field F0.

Let p be a prime, O_p = O (x) Z_p, and Lambda a complete discrete valuation ring
containing O_p (Lambda = O_p when p ramifies).  Locally H_1(X, Z_p) = O_p (x) W,
with W = Z_p^4 symplectic (form omega_0 = u1 u3 + u2 u4 on the dual basis) and
E = B (x) omega_0, B(a, b) = Tr(delta^{-1} a b), delta a generator of the local
different with sigma(delta) = -delta.  Over Lambda, O_p (x) Lambda is the lattice
{(x, y) : x = y mod delta} of Lambda^2 (eigen-coordinates eps_1, eps_2), its
dual is spanned by eps_2 and (eps_1 - eps_2)/delta, so H^1(X, Lambda) has basis
    Y_i = eps_2 (x) u_i,   Z_i = (X_i - Y_i)/delta,   X_i = eps_1 (x) u_i,
and theta = B omega_0 = theta_1 + theta_2 with
    theta_1 = (X_1 X_3 + X_2 X_4)/delta,   theta_2 = -(Y_1 Y_3 + Y_2 Y_4)/delta.
A class of R is v = sum V_ab theta_1^a theta_2^b/(a! b!) with
V = [[r, hs, gs], [h, c, ks], [g, k, m]], where hs, gs, ks are the conjugates.

This script expands v in the monomial basis of Lambda^*(Y, Z), with delta, r, h,
hs, g, gs, c, k, ks, m independent symbols, and checks exactly:
  (a) [if] after substituting hs = h - delta h1, g = c + delta g2,
      gs = c - delta g2 + delta^2 g3, ks = k - delta k1, every coefficient is a
      polynomial in delta and the new parameters: the class is integral whenever
      r, c, m lie in Z_p, h, g, k in O_p and g = c mod delta.  (For x in O_p,
      x - sigma(x) lies in delta O_p; so hs = sigma(h) and ks = sigma(k) have this
      form, and g2 = (g - c)/delta in O_p gives sigma(g) = c - delta sigma(g2)
      with sigma(g2) = g2 - delta g3.)
  (b) [only if] some monomial has coefficient +-r, +-h, +-c, +-g, +-(g - c)/delta,
      +-k, +-m respectively, so integrality forces each of these conditions.
Nothing depends on p, on delta or on the field: this is the proof of the lemma
at every prime, ramified or not (for p unramified delta is a unit).
"""
import sympy as sp

PASS, FAIL = [], []


def check(name, ok):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name), flush=True)


def wedge(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            if ma & mb:
                continue
            # sign: number of pairs (i in ma, j in mb) with i > j
            s = 0
            for j in range(8):
                if mb >> j & 1:
                    s += bin(ma >> (j + 1)).count("1")
            c = ca * cb * (-1 if s % 2 else 1)
            out[ma | mb] = out.get(ma | mb, 0) + c
    return {k: sp.simplify(v) for k, v in out.items() if sp.simplify(v) != 0}


def add(*xs):
    out = {}
    for x in xs:
        for k, v in x.items():
            out[k] = out.get(k, 0) + v
    return {k: sp.expand(v) for k, v in out.items() if sp.expand(v) != 0}


def sc(c, x):
    return {k: sp.expand(c * v) for k, v in x.items()}


d, r, h, hs, g, gs, c, k, ks, m = sp.symbols("delta r h hs g gs c k ks m")
h1, g2, g3, k1 = sp.symbols("h1 g2 g3 k1")


def gen(i):
    return {1 << i: sp.Integer(1)}


Y = [gen(i) for i in range(4)]
Z = [gen(4 + i) for i in range(4)]
X = [add(Y[i], sc(d, Z[i])) for i in range(4)]
theta1 = sc(1 / d, add(wedge(X[0], X[2]), wedge(X[1], X[3])))
theta2 = sc(-1 / d, add(wedge(Y[0], Y[2]), wedge(Y[1], Y[3])))
one = {0: sp.Integer(1)}
t11 = wedge(theta1, theta1)
t22 = wedge(theta2, theta2)
v = add(sc(r, one), sc(h, theta1), sc(hs, theta2),
        sc(g / 2, t11), sc(gs / 2, t22), sc(c, wedge(theta1, theta2)),
        sc(k / 2, wedge(t11, theta2)), sc(ks / 2, wedge(theta1, t22)),
        sc(m / 4, wedge(t11, t22)))


def main():
    print("the class v has %d nonzero monomial coefficients" % len(v))
    # sanity: theta itself and its divided powers are integral (delta in numerator only)
    theta = add(theta1, theta2)
    ok = True
    p = one
    for j in range(1, 5):
        p = sc(sp.Rational(1, j), wedge(p, theta))
        for coeff in p.values():
            num, den = sp.fraction(sp.together(coeff))
            ok = ok and not sp.Poly(den, d).degree() > 0
    check("theta^j/j! is integral in the local model for j = 1..4", ok)
    top = sc(sp.Rational(1, 24), wedge(wedge(theta, theta), wedge(theta, theta)))
    check("theta^4/4! is the generator Y1..Y4 Z1..Z4 up to sign (the polarisation is principal)",
          len(top) == 1 and abs(list(top.values())[0]) == 1)
    # (a) the if direction
    subs = {hs: h - d * h1, g: c + d * g2, gs: c - d * g2 + d * d * g3, ks: k - d * k1}
    ok = True
    for coeff in v.values():
        e = sp.expand(sp.cancel(coeff.subs(subs, simultaneous=True)))
        for term in sp.Add.make_args(e):
            ok = ok and term.as_powers_dict().get(d, 0) >= 0 and \
                sp.fraction(sp.together(term))[1].free_symbols == set()
    check("[if] with r, c, m in Z_p, h, g, k in O_p and g = c mod delta every monomial "
          "coefficient of v is a polynomial in delta and the parameters", ok)
    # the substitution is not vacuous: without the congruence it fails
    subs2 = {hs: h - d * h1, gs: g - d * g3, ks: k - d * k1}
    bad = False
    for coeff in v.values():
        e = sp.expand(sp.cancel(coeff.subs(subs2, simultaneous=True)))
        for term in sp.Add.make_args(e):
            bad = bad or term.as_powers_dict().get(d, 0) < 0
    check("without the congruence g = c mod delta some coefficient keeps a negative "
          "power of delta", bad)
    # (b) the only-if direction
    vals = set(sp.expand(x) for x in v.values())
    for name, target in [("r", r), ("h", h), ("c", c), ("g", g), ("(g - c)/delta", (g - c) / d),
                         ("k", k), ("m", m)]:
        t = sp.expand(target)
        check("[only if] some monomial of v has coefficient +-%s" % name,
              t in vals or sp.expand(-t) in vals)
    # the full list of coefficient shapes, for the record
    shapes = sorted(set(str(sp.factor(x)) for x in v.values()))
    print("  coefficient shapes (%d):" % len(shapes))
    for s in shapes:
        print("     ", s)
    print()
    print("%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)


if __name__ == "__main__":
    main()
