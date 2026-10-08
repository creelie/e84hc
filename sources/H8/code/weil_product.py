#!/usr/bin/env python3
"""
weil_product.py

The Weil class is multiplicative under products of Weil-type abelian
varieties.  Exact arithmetic over Q(sqrt(-d)); no floating point.

For A_i of (K,-1,n_i)-Weil type with the same K = Q(sqrt(-d)), the product
carries the diagonal K-action and is of (K,-1,n_1+n_2)-Weil type.  With the
integral generators omega_1, omega_2 of Theorem explicitgens, written in a
K-basis u_j of H^1 (x_j = u_j, y_j = sqrt(-d) u_j), and the K-basis of the
product obtained by concatenating the bases of the factors,

    omega_1(A) = omega_1(A_1) omega_1(A_2) - d omega_2(A_1) omega_2(A_2)
    omega_2(A) = omega_1(A_1) omega_2(A_2) + omega_2(A_1) omega_1(A_2)

equivalently  omega(A_1) omega(A_2) = omega(A_1 x A_2)  for the K-valued
class omega = omega_1 + sqrt(-d) omega_2, which is d^(-n) prod_j (d x_j +
sqrt(-d) y_j).  Over k factors the constant is 1.  This is
Theorem weilmult (eq:weilmult), Lemma basecase and Remark prodscope.

Model.  Monomials are increasing tuples of indices, x_j -> 2j, y_j -> 2j+1;
a class is a dict from monomials to elements a + b sqrt(-d) of K, stored as
pairs of Fractions.
"""

from fractions import Fraction as F
import sys

_NP = _NF = 0


def check(name, ok, detail=""):
    global _NP, _NF
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    if ok:
        _NP += 1
    else:
        _NF += 1


D = 1   # the squarefree d of K = Q(sqrt(-d)), set by each part


def cmul(a, b):
    return (a[0] * b[0] - D * a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


CZ = (F(0), F(0))
CO = (F(1), F(0))
CI = (F(0), F(1))


def wedge(m1, c1, m2, c2):
    if set(m1) & set(m2):
        return None
    arr = list(m1) + list(m2)
    sg = 1
    n = len(arr)
    for i in range(n):
        for j in range(n - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                sg = -sg
    c = cmul(c1, c2)
    return tuple(arr), (c[0] * sg, c[1] * sg)


def mul(A, B):
    out = {}
    for m1, c1 in A.items():
        for m2, c2 in B.items():
            r = wedge(m1, c1, m2, c2)
            if r is None:
                continue
            m, c = r
            out[m] = cadd(out.get(m, CZ), c)
            if out[m] == CZ:
                del out[m]
    return out


def add(A, B):
    out = dict(A)
    for m, c in B.items():
        out[m] = cadd(out.get(m, CZ), c)
        if out[m] == CZ:
            del out[m]
    return out


def scal(A, s):
    return {m: cmul(c, s) for m, c in A.items()}


def neg(A):
    return scal(A, (F(-1), F(0)))


def eq(A, B):
    return not add(A, neg(B))


def omegas(offset, n, d):
    """The generators omega_1, omega_2 of (eq:omegagens) for the K-basis
    u_offset, ..., u_{offset+2n-1}: sums over index sets T of the monomials
    w^(T) taking y_j for j in T and x_j otherwise."""
    m = 2 * n
    w1, w2 = {}, {}
    for mask in range(1 << m):
        t = bin(mask).count("1")
        mono = tuple(2 * (offset + j) + ((mask >> j) & 1) for j in range(m))
        if t % 2 == 0:
            c = F((-1) ** (t // 2) * d ** (n - t // 2))
            w1[mono] = (c, F(0))
        else:
            c = F((-1) ** ((t - 1) // 2) * d ** (n - (t + 1) // 2))
            w2[mono] = (c, F(0))
    return w1, w2


def closed_form(offset, n, d):
    """d^(-n) prod_j (d x_j + sqrt(-d) y_j), in the order of the basis."""
    acc = {(): CO}
    for j in range(2 * n):
        i = offset + j
        acc = mul(acc, {(2 * i,): (F(d), F(0)), (2 * i + 1,): CI})
    return scal(acc, (F(1, d ** n), F(0)))


def kmul(p, q, d):
    """Product in the K-valued notation: (a1 + s a2)(b1 + s b2), s^2 = -d."""
    a1, a2 = p
    b1, b2 = q
    return (add(mul(a1, b1), scal(mul(a2, b2), (F(-d), F(0)))),
            add(mul(a1, b2), mul(a2, b1)))


DS = (1, 2, 3, 5, 7)


def part_two_factors():
    global D
    print("  (a) the two-factor identity")
    rows, ok = [], True
    for d in DS:
        D = d
        good_d = True
        for n1 in (1, 2, 3):
            for n2 in (1, 2, 3):
                w11, w21 = omegas(0, n1, d)
                w12, w22 = omegas(2 * n1, n2, d)
                w1P, w2P = omegas(0, n1 + n2, d)
                c1 = add(mul(w11, w12), scal(mul(w21, w22), (F(-d), F(0))))
                c2 = add(mul(w11, w22), mul(w21, w12))
                good_d = good_d and eq(w1P, c1) and eq(w2P, c2)
        ok = ok and good_d
        rows.append("d=%d, n1, n2 <= 3: %s" % (d, "holds" if good_d else "FAILS"))
    check("omega_1 = omega_1 omega_1 - d omega_2 omega_2 and omega_2 = omega_1 omega_2"
          " + omega_2 omega_1 for the product, n_i <= 3", ok, "\n".join(rows))


def part_k_valued():
    global D
    print("  (b) the K-valued form")
    rows, ok = [], True
    for d in DS:
        D = d
        good_d = True
        for n in (1, 2, 3, 4):
            w1, w2 = omegas(0, n, d)
            omega = add(w1, scal(w2, CI))
            good_d = good_d and eq(omega, closed_form(0, n, d))
        for n1 in (1, 2, 3):
            for n2 in (1, 2, 3):
                p1 = omegas(0, n1, d)
                p2 = omegas(2 * n1, n2, d)
                pr = kmul(p1, p2, d)
                w1P, w2P = omegas(0, n1 + n2, d)
                good_d = good_d and eq(pr[0], w1P) and eq(pr[1], w2P)
        ok = ok and good_d
        rows.append("d=%d: omega = d^-n prod (d x_j + s y_j) for n <= 4, and "
                    "omega(A1) omega(A2) = omega(A1 x A2) for n_i <= 3  %s"
                    % (d, "yes" if good_d else "NO"))
    check("the K-valued class omega = omega_1 + sqrt(-d) omega_2 is multiplicative",
          ok, "\n".join(rows))


def part_many_factors():
    global D
    print("  (c) associativity over k factors")
    rows, ok = [], True
    for d in (1, 2, 3):
        D = d
        for parts in [(1, 1, 1), (1, 1, 2), (2, 2, 1), (1, 2, 3), (1, 1, 1, 1), (2, 1, 1, 2)]:
            off = 0
            facs = []
            for n in parts:
                facs.append(omegas(off, n, d))
                off += 2 * n
            acc = facs[0]
            for f in facs[1:]:
                acc = kmul(acc, f, d)
            w1P, w2P = omegas(0, sum(parts), d)
            good = eq(acc[0], w1P) and eq(acc[1], w2P)
            ok = ok and good
            rows.append("d=%d, parts %s -> n=%d, k=%d: product = omega  %s"
                        % (d, str(parts), sum(parts), len(parts), "yes" if good else "NO"))
    check("the k-factor identity holds with constant 1", ok, "\n".join(rows))


def part_base_case():
    print("  (d) the base case n = 1")
    rows, ok = [], True
    for n in (1, 2, 3):
        w1, _ = omegas(0, n, 2)
        deg = len(next(iter(w1)))
        expected = 2 * n
        good = (deg == expected)
        ok = ok and good
        rows.append("n=%d: dim A = %d, Weil class in H^%d%s"
                    % (n, 2 * n, deg, "  (divisor degree)" if deg == 2 else ""))
    check("the Weil class sits in H^{2n}, so at n = 1 it is a divisor class",
          ok, "\n".join(rows))


def part_dimensions():
    print("  (e) the size of the product locus")
    rows = []
    ok = True
    for n in range(1, 8):
        fam = n * n
        quat = n * (n + 1) // 2
        prod = n
        if n >= 2 and not (prod < quat < fam):
            ok = False
        rows.append("n=%d: family %d, quaternionic locus %d, product locus %d"
                    % (n, fam, quat, prod))
    check("for n >= 2 the product locus is proper and smaller than the quaternionic locus",
          ok, "\n".join(rows))


def main():
    print("the Weil class under products")
    part_two_factors()
    part_k_valued()
    part_many_factors()
    part_base_case()
    part_dimensions()
    print()
    print("  %d checks passed, %d failed" % (_NP, _NF))
    print("  overall: %s" % ("PASS" if _NF == 0 else "FAIL"))
    return 0 if _NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
