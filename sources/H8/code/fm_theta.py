"""
The cohomological Fourier-Mukai transform on powers of a principal
polarisation, computed exactly in the exterior algebra.

Model.  For an abelian variety A of dimension g put V = H^1(A,Q), of dimension
2g, so that H^*(A,Q) = wedge(V).  For the dual, H^1(A^v,Q) = V^dual, and
H^*(A x A^v, Q) = wedge(V (+) V^dual).  With e_1..e_{2g} a basis of V and
f_1..f_{2g} the dual basis, the first Chern class of the Poincare bundle is
the canonical element

    l = sum_i  e_i ^ f_i ,

and the transform Phi : H^*(A^v) -> H^*(A) is

    Phi(x) = p_*( q^* x . exp(l) ),

where p_* integrates over the A^v factor, that is, extracts the coefficient of
the top form f_1 ^ ... ^ f_{2g}.

A principal polarisation is the symplectic form theta = sum_j e_j ^ e_{g+j} on
A and theta' = sum_j f_j ^ f_{g+j} on A^v.

This script computes Phi(theta'^k) for every k and checks the closed form

    Phi(theta'^k) = (-1)^{g/2} (-1)^k  k! / (g-k)!  theta^{g-k} ,

for even g, and reports the constants for odd g as well.
"""
from fractions import Fraction
from math import factorial


class Ext:
    """Elements of an exterior algebra on `n` generators, as {bitmask: coeff}."""

    def __init__(self, n):
        self.n = n

    def gen(self, i):
        return {1 << i: Fraction(1)}

    @staticmethod
    def add(x, y):
        out = dict(x)
        for k, v in y.items():
            out[k] = out.get(k, Fraction(0)) + v
            if out[k] == 0:
                del out[k]
        return out

    @staticmethod
    def scal(c, x):
        c = Fraction(c)
        return {k: c * v for k, v in x.items() if c * v != 0}

    def mul(self, x, y):
        out = {}
        for kx, vx in x.items():
            for ky, vy in y.items():
                if kx & ky:
                    continue
                s = self.sign(kx, ky)
                k = kx | ky
                out[k] = out.get(k, Fraction(0)) + s * vx * vy
                if out[k] == 0:
                    del out[k]
        return out

    @staticmethod
    def sign(kx, ky):
        """Sign of shuffling the generators of ky past those of kx."""
        s = 1
        ky2 = ky
        while ky2:
            b = (ky2 & -ky2).bit_length() - 1
            # count generators of kx above b
            higher = kx >> (b + 1)
            if bin(higher).count("1") % 2:
                s = -s
            ky2 &= ky2 - 1
        return s

    def power(self, x, k):
        out = {0: Fraction(1)}
        for _ in range(k):
            out = self.mul(out, x)
        return out

    def exp(self, x, top):
        out = {0: Fraction(1)}
        term = {0: Fraction(1)}
        for k in range(1, top + 1):
            term = self.scal(Fraction(1, k), self.mul(term, x))
            if not term:
                break
            out = self.add(out, term)
        return out


def run(g, verbose=True):
    n = 4 * g                      # e_0..e_{2g-1}, f_0..f_{2g-1}
    E = Ext(n)

    def e(i):
        return E.gen(i)

    def f(i):
        return E.gen(2 * g + i)

    # l = sum_i e_i ^ f_i
    l = {}
    for i in range(2 * g):
        l = E.add(l, E.mul(e(i), f(i)))

    theta = {}
    thetap = {}
    for j in range(g):
        theta = E.add(theta, E.mul(e(j), e(g + j)))
        thetap = E.add(thetap, E.mul(f(j), f(g + j)))

    expl = E.exp(l, 4 * g)
    topf = 0
    for i in range(2 * g):
        topf |= 1 << (2 * g + i)

    def integrate(z):
        """Coefficient of f_0^...^f_{2g-1}, returned as an element of wedge(V)."""
        out = {}
        for k, v in z.items():
            if k & topf != topf:
                continue
            ke = k & ~topf
            # sign of splitting k into (e-part)(f-part)
            s = E.sign(ke, topf)
            out[ke] = out.get(ke, Fraction(0)) + s * v
            if out[ke] == 0:
                del out[ke]
        return out

    results = {}
    for k in range(g + 1):
        x = E.power(thetap, k)
        img = integrate(E.mul(x, expl))
        tgt = E.power(theta, g - k)
        if not img:
            results[k] = Fraction(0)
            continue
        key = next(iter(tgt)) if tgt else next(iter(img))
        c = img.get(key, Fraction(0)) / tgt.get(key, Fraction(1))
        ok = all(img.get(m, Fraction(0)) == c * tgt.get(m, Fraction(0))
                 for m in set(list(img) + list(tgt)))
        results[k] = c if ok else None
    return results


if __name__ == "__main__":
    print("Phi(theta'^k) as a multiple of theta^(g-k)")
    allok = True
    for g in (1, 2, 3, 4):
        res = run(g)
        eps = (-1) ** (g // 2) if g % 2 == 0 else None
        print(f"\n g = {g}")
        for k in sorted(res):
            c = res[k]
            if c is None:
                print(f"   k={k}: image is NOT a multiple of theta^(g-k)")
                allok = False
                continue
            pred = None
            if g % 2 == 0:
                pred = Fraction((-1) ** (g // 2) * (-1) ** k
                                * factorial(k), factorial(g - k))
            mark = ""
            if pred is not None:
                mark = "  matches closed form" if c == pred else \
                       f"  MISMATCH (closed form {pred})"
                if c != pred:
                    allok = False
            print(f"   k={k}: {c}{mark}")
    print()
    print("every image is a pure power of theta, with no other component:",
          allok)
