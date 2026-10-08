"""
The secant plane, explicitly, for every n and every imaginary quadratic K,
and the Chern character equation a sheaf realising it must satisfy.

Setting.  X an abelian n-fold, t a nondegenerate class in NS(X) (x) Q,
d > 0 squarefree, s = sqrt(-d), K = Q(s).  By weiltype_family.py the two
conjugate maximal isotropic subspaces of H_1(X x Xhat) attached to t are the
graphs of the two-forms  +- s t , so the two conjugate pure spinors are
exp(+- s t).  Their span is defined over Q:

    u = (exp(st) + exp(-st))/2      = sum_j (-d)^j t^(2j) / (2j)!
    v = (exp(st) - exp(-st))/(2s)   = sum_j (-d)^j t^(2j+1) / (2j+1)!

Both are rational polynomials in t, hence rational Hodge classes, and
exp(+- s t) = u +- s v, so the line P(span(u,v)) is a rational secant of the
spinor variety through the two conjugate points.

This script computes, exactly:
  (A) u and v in each degree, for a range of n and d;
  (B) the rank, c_1, c_2 and discriminant of a sheaf with ch = a u + b v;
  (C) the identity  Delta = N_{K/Q}(b + a s) t^2 ;
  (D) at n = 3 with X a Jacobian of a genus three curve and t = Theta, the
      class of the subscheme Z for which ch(I_Z(Theta)) lies in the plane.
"""
import sympy as sp

a, b, dd = sp.symbols('a b d', positive=True)
T = sp.symbols('T')          # a formal symbol standing for the class t


def uv(n, d):
    """u and v truncated at degree n (t^k = 0 for k > n on an n-fold)."""
    u = sum(sp.Rational((-1) ** j) * d ** j * T ** (2 * j) / sp.factorial(2 * j)
            for j in range(0, n // 2 + 1))
    v = sum(sp.Rational((-1) ** j) * d ** j * T ** (2 * j + 1)
            / sp.factorial(2 * j + 1)
            for j in range(0, (n - 1) // 2 + 1))
    return sp.expand(u), sp.expand(v)


def report_uv():
    print("=" * 70)
    print("(A) the two rational generators of the plane")
    print("=" * 70)
    for n in (2, 3, 4, 5):
        for d in (1, 3):
            u, v = uv(n, d)
            print(f"  n={n}, d={d}:")
            print(f"     u = {u}")
            print(f"     v = {v}")
    print()


def chern_from_ch():
    """From ch = a u + b v read off rank, c1, ch2, c2 and the discriminant."""
    print("=" * 70)
    print("(B),(C) the Chern data of a sheaf with ch = a u + b v")
    print("=" * 70)
    u, v = uv(6, dd)
    ch = sp.expand(a * u + b * v)
    p = sp.Poly(ch, T)
    ch0 = p.coeff_monomial(1)
    ch1 = p.coeff_monomial(T)
    ch2 = p.coeff_monomial(T ** 2)
    ch3 = p.coeff_monomial(T ** 3)
    print(f"  ch_0 = rank = {ch0}")
    print(f"  ch_1 = {ch1} * t              so c_1 = {ch1} t")
    print(f"  ch_2 = {ch2} * t^2")
    print(f"  ch_3 = {ch3} * t^3")
    c1 = ch1
    # ch2 = (c1^2 - 2 c2)/2  =>  c2 = (c1^2 - 2 ch2)/2
    c2 = sp.simplify((c1 ** 2 - 2 * ch2) / 2)
    print(f"  c_2 = {sp.factor(c2)} * t^2")
    # discriminant  Delta = 2 r c2 - (r-1) c1^2
    Delta = sp.simplify(2 * ch0 * c2 - (ch0 - 1) * c1 ** 2)
    print(f"  Delta = 2 r c_2 - (r-1) c_1^2 = {sp.factor(Delta)} * t^2")
    Norm = sp.expand(b ** 2 + a ** 2 * dd)
    print(f"  N_(K/Q)(b + a sqrt(-d)) = {Norm}")
    print(f"  Delta equals the norm: {sp.simplify(Delta - Norm) == 0}")
    print(f"  Bogomolov Delta >= 0 automatically, since the norm is positive")
    print()
    return c2


def genus_three():
    print("=" * 70)
    print("(D) n = 3, X the Jacobian of a genus three curve, t = Theta")
    print("=" * 70)
    print("  For a Jacobian of genus g, Theta^(g-1)/(g-1)! is the class of the")
    print("  Abel-Jacobi curve C; at g = 3 that reads  Theta^2/2 = [C].")
    print()
    print("  Take a = 1 (rank one) and ch(F) = u + b v.  A rank one")
    print("  torsion-free sheaf with c_1 = b Theta is I_Z(b Theta) for a")
    print("  subscheme Z of codimension two, and")
    print("      ch(I_Z(bTheta)) = e^(bTheta) - [Z] - (lower),")
    print("  so matching degree four gives  [Z] = (bTheta)^2/2 - ch_2.")
    print()
    u, v = uv(3, dd)
    ch = sp.expand(1 * u + b * v)
    p = sp.Poly(ch, T)
    ch2 = p.coeff_monomial(T ** 2)
    Zclass = sp.simplify((b ** 2) / 2 - ch2)
    print(f"  ch_2 = {ch2} t^2,  so  [Z] = {sp.factor(Zclass)} * Theta^2")
    print(f"       = {sp.factor(2*Zclass)} * (Theta^2/2) = "
          f"{sp.factor(2*Zclass)} * [C]")
    print()
    print("  So Z is a union of  m = (b^2 + d)/b^2  translates of C, and for")
    print("  m to be a positive integer one needs b^2 | d.  With b = 1:")
    m = sp.simplify(2 * Zclass.subs(b, 1))
    print(f"      m = {sp.factor(m)}      translates of the Abel-Jacobi curve.")
    print()
    for dv in (1, 2, 3, 5, 7, 11):
        print(f"      d = {dv}:  m = {int(m.subs(dd, dv))}")
    print()
    print("  This is the shape of Markman's secant sheaf I_{union C_i}(Theta)")
    print("  on a genus three Jacobian, with the number of translates fixed")
    print("  by the field.")


if __name__ == "__main__":
    report_uv()
    chern_from_ch()
    genus_three()
