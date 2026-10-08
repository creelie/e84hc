#!/usr/bin/env python3
"""
make_section51.py

Writes the certificates of Section 51 of HodgeObstruction.lean: the rank of
contraction HT^2 -> H^*, xi |-> xi _| gamma, for the polarised characters

    gamma = sum_k c_k theta^k + u alpha_+ + conj(u) alpha_-

of Theorem (The polarised criterion as a number): at n = 3 on two shapes of
every Hankel rank rho, each with two values of u, and at n = 4 on one shape
of every Hankel rank.

For each case it records

  * a basis of the annihilator Ann_{HT^2}(gamma), as Gaussian-integer
    combinations of the basis elements op_s op_t (s < t) of HT^2, in reduced
    echelon form;
  * r basis elements of HT^2 whose images are linearly independent modulo the
    prime p = 998244353, at which i is sent to a square root of -1.

The Lean kernel recomputes gamma and its images from the model and checks
that each annihilator vector kills gamma exactly, that the vectors are
independent modulo p, that the r recorded images are independent modulo p,
and that r + dim Ann = dim HT^2.  Reduction along Z[i] -> F_p is a ring map,
so a family independent modulo p is independent over Q(i): the rank is at
least r, the annihilator has dimension at least dim Ann, and the two add up.

The model is that of code/p2prime.py, which this script imports.

Run from the repository root:  python3 lean/generate/make_section51.py > out
"""

import os
import sys
from fractions import Fraction as Fr
from math import factorial, gcd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "code"))
import p2prime as P  # noqa: E402

PRIME = 998244353
# at n = 4 one shape for each Hankel rank, with u = 2 + 3i; each is a theorem
# of its own, which keeps the kernel's memory to one case at a time
N4_SHAPES = ("pure", "expo", "c1", "generic")
SQRT_M1 = pow(3, (PRIME - 1) // 4, PRIME)
assert SQRT_M1 * SQRT_M1 % PRIME == PRIME - 1


def shapes(n):
    g = 2 * n
    z = [0] * (g + 1)

    def at(**kw):
        c = list(z)
        for k, v in kw.items():
            c[int(k[1:])] = v
        return c
    expo = [factorial(g) // factorial(k) for k in range(g + 1)]
    gen = [3, -1, 2, 5, -4, 1, 7, -2, 6][: g + 1]
    return [("pure", z), ("c0", at(c0=1)), ("expo", expo), ("c1", at(c1=1)),
            ("c0c2n", at(c0=1, **{"c%d" % g: 3})), ("cn", at(**{"c%d" % n: 1})),
            ("generic", gen)]


def gauss_int_vec(vec):
    """scale a dict index -> GQ to Gaussian integers, primitive"""
    den = 1
    for v in vec.values():
        den = den * v.a.denominator // gcd(den, v.a.denominator)
        den = den * v.b.denominator // gcd(den, v.b.denominator)
    out = {k: (int(v.a * den), int(v.b * den)) for k, v in vec.items()}
    g = 0
    for a, b in out.values():
        g = gcd(g, gcd(abs(a), abs(b)))
    return {k: (a // g, b // g) for k, (a, b) in out.items()}


def rref_kernel(ker, F):
    """reduced echelon form of the kernel vectors (dicts index -> GQ)"""
    rows = [dict(v) for v in ker]
    out = []
    while rows:
        rows.sort(key=lambda v: min(v))
        piv = rows[0]
        p = min(piv)
        inv = F.inv(piv[p])
        piv = {k: F.mul(v, inv) for k, v in piv.items()}
        rest = []
        for v in rows[1:]:
            if p in v:
                v = P.vadd(v, piv, F, F.neg(v[p]))
            if v:
                rest.append(v)
        out = [P.vadd(w, piv, F, F.neg(w[p])) if p in w else w for w in out]
        out.append(piv)
        rows = rest
    return out


def modp(a, b):
    return (a + b * SQRT_M1) % PRIME


def choose_rows(images, r):
    """r rows of the matrix (rows = images), independent modulo PRIME"""
    cols = sorted({m for img in images for m in img})
    pos = {m: j for j, m in enumerate(cols)}
    M = []
    for img in images:
        row = [0] * len(cols)
        for m, v in img.items():
            row[pos[m]] = modp(int(v.a), int(v.b)) if v.a.denominator == 1 and v.b.denominator == 1 else None
        M.append(row)
    # greedy choice of independent rows
    basis, chosen_rows = [], []
    for i, row in enumerate(M):
        v = list(row)
        for (pc, b) in basis:
            if v[pc]:
                f = v[pc]
                v = [(x - f * y) % PRIME for x, y in zip(v, b)]
        nz = next((j for j, x in enumerate(v) if x), None)
        if nz is None:
            continue
        inv = pow(v[nz], PRIME - 2, PRIME)
        v = [x * inv % PRIME for x in v]
        basis.append((nz, v))
        chosen_rows.append(i)
        if len(chosen_rows) == r:
            break
    assert len(chosen_rows) == r
    return chosen_rows


def lean_gi(a, b):
    return "(%d, %d)" % (a, b)


def main():
    F = P.Exact()
    out = []
    names = []
    for n in (3, 4):
        M = P.Model(n)
        pw = M.theta_powers(F)
        for name, c in shapes(n):
            if n == 4 and name not in N4_SHAPES:
                continue
            rho = P.hankel_rank(c, n)
            for u in ((1, 0), (2, 3)) if n == 3 else ((2, 3),):
                chv = M.ch(c, u, F, pw)
                images = [M.apply2(s, t, chv, F) for (s, t) in M.ht2]
                for img in images:
                    for v in img.values():
                        assert v.a.denominator == 1 and v.b.denominator == 1
                r, a, ker = P.annihilator(M, c, u, F, kernel=True, pw=pw)
                assert a == n * n * (4 - rho) and r == (4 + rho) * n * n - 2 * n
                ker = [gauss_int_vec(v) for v in rref_kernel(ker, F)]
                rows = choose_rows(images, r)
                tag = "pc%d%s%s" % (n, name, "a" if u == (1, 0) else "b")
                names.append((tag, n, c, u, rho, r, a))
                out.append("def %sKer : List (List (Nat × Int × Int)) := [" % tag)
                out.append(",\n".join("  [" + ", ".join("(%d, %d, %d)" % (k, x, y)
                                                        for k, (x, y) in sorted(v.items())) + "]"
                                      for v in ker) + "]")
                out.append("def %sRows : List Nat := %s" % (tag, rows))
                out.append("")
    out.append("/-- the cases: `(n, c, u, rho, r, dim Ann, annihilator, rows)`. -/")
    out.append("def pcCases : List (Nat × List Int × (Int × Int) × Nat × Nat × Nat"
               " × List (List (Nat × Int × Int)) × List Nat) := [")
    out.append(",\n".join("  (%d, %s, (%d, %d), %d, %d, %d, %sKer, %sRows)"
                          % (n, "[" + ", ".join(str(x) for x in c) + "]", u[0], u[1],
                             rho, r, a, t, t)
                          for (t, n, c, u, rho, r, a) in names) + "]")
    print("\n".join(out))
    print("-- %d cases" % len(names), file=sys.stderr)


if __name__ == "__main__":
    main()
