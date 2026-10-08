#!/usr/bin/env python3
"""
make_profile.py

Writes the certificates of the Hochschild profile of a polarised character
(item (LIII)) for HodgeObstruction.lean: for

    gamma = sum_k c_k theta^k + u alpha_+ + conj(u) alpha_-

in the model of code/p2prime.py, and every degree k = 0..4n, the rank rho_k
of contraction HT^k -> H^*, xi |-> xi _| gamma, where HT^k has the basis of
products op_(s_1) ... op_(s_k), s_1 < ... < s_k, of the 4n operators of HT^1
(lexicographic order of the subsets).

For each case and degree it records

  * rho_k indices of basis elements whose images are linearly independent
    modulo the prime p = 998244353 (i -> a square root of -1);
  * a basis of the relations among the nonzero images, as Gaussian-integer
    combinations; each relation ends at an index it alone contains.

The kernel computes every image itself, checks each relation exactly, counts
the basis elements with image zero, and checks rho_k + (number of zero
images) + (number of relations) = binom(4n, k).

Rational shapes are scaled to integers together with u; this multiplies
gamma by a nonzero constant and changes no rank.

Run from the repository root:  python3 lean/generate/make_profile.py > out
"""

import os
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import factorial, gcd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "code"))
from p2prime import Exact, Model, op_apply, rank_and_kernel  # noqa: E402
from p2prime_profile import weight_key, formula  # noqa: E402

PRIME = 998244353
SQRT_M1 = pow(3, (PRIME - 1) // 4, PRIME)


def lcm(a, b):
    return a * b // gcd(a, b)


def shapes(n):
    g = 2 * n
    z = [Fr(0)] * (g + 1)

    def at(k, v=1):
        c = list(z)
        c[k] = Fr(v)
        return c
    gen = [Fr(x) for x in [3, -1, 2, 5, -4, 1, 7, -2, 6][: g + 1]]
    return [("pure", z), ("c0", at(0)), ("c1", at(1)), ("cn", at(n)), ("c2n", at(g)),
            ("expo", [Fr(1, factorial(k)) for k in range(g + 1)]),
            ("twoexp", [Fr(1, factorial(k)) + 3 * Fr(2) ** k / factorial(k)
                        for k in range(g + 1)]),
            ("generic", gen)]


def cases():
    out = []
    for name, c in shapes(2):
        for u in ((1, 0), (2, 3)):
            out.append((2, name, c, u))
    for name, c in shapes(3):
        if name in ("pure", "cn", "generic"):
            out.append((3, name, c, (2, 3)))
    # the middle degeneracy: c_n theta^n alone at |u| = binom(n,a) n! |c_n|
    for n, us in ((2, (2, 4)), (3, (6, 18))):
        c = [Fr(0)] * (2 * n + 1)
        c[n] = Fr(1)
        for s in us:
            out.append((n, "cn-special", c, (s, 0)))
    return out


def gauss(v):
    """scale a dict index -> GQ to primitive Gaussian integers"""
    den = 1
    for x in v.values():
        den = lcm(den, x.a.denominator)
        den = lcm(den, x.b.denominator)
    out = {k: (int(x.a * den), int(x.b * den)) for k, x in v.items()}
    g = 0
    for a, b in out.values():
        g = gcd(g, gcd(abs(a), abs(b)))
    return {k: (a // g, b // g) for k, (a, b) in out.items()}


def modp(x):
    return (int(x.a) + int(x.b) * SQRT_M1) % PRIME


def independent_rows(images, idxs, r):
    """r of the indices idxs whose images are independent modulo PRIME"""
    basis, chosen = {}, []
    for i in idxs:
        v = {m: modp(x) for m, x in images[i].items() if modp(x)}
        while v:
            p = min(v)
            if p not in basis:
                inv = pow(v[p], PRIME - 2, PRIME)
                basis[p] = {m: x * inv % PRIME for m, x in v.items()}
                chosen.append(i)
                break
            f = v[p]
            for m, x in basis[p].items():
                v[m] = (v.get(m, 0) - f * x) % PRIME
                if v[m] == 0:
                    del v[m]
        if len(chosen) == r:
            break
    assert len(chosen) == r
    return sorted(chosen)


def main():
    F = Exact()
    out, rows_out = [], []
    for ci, (n, name, c, u) in enumerate(cases()):
        L = 1
        for x in c:
            L = lcm(L, x.denominator)
        ci_int = [int(x * L) for x in c]
        u_int = (u[0] * L, u[1] * L)
        M = Model(n)
        pw = M.theta_powers(F)
        chv = M.ch(ci_int, u_int, F, pw)
        nops = len(M.ops)
        prof, rows_k, rels_k = [], [], []
        for k in range(nops + 1):
            subs = list(combinations(range(nops), k))
            images = []
            for sub in subs:
                img = chv
                for s in reversed(sub):
                    o = M.ops[s]
                    img = op_apply(o[0], o[1], img, F)
                    if not img:
                        break
                images.append(img)
            blocks = {}
            for i, sub in enumerate(subs):
                if images[i]:
                    blocks.setdefault(weight_key(M, sub), []).append(i)
            r, rels = 0, []
            for idxs in blocks.values():
                rr, ker = rank_and_kernel([images[i] for i in idxs], F, True)
                r += rr
                for v in ker:
                    g = gauss({idxs[j]: x for j, x in v.items()})
                    rels.append(sorted(g.items()))
            zeros = sum(1 for im in images if not im)
            assert r + zeros + len(rels) == len(subs)
            nz = [i for i in range(len(subs)) if images[i]]
            rows_k.append(independent_rows(images, nz, r))
            rels_k.append(rels)
            prof.append(r)
        X = Fr(u[0] ** 2 + u[1] ** 2)
        assert prof == formula(c, n, X), (n, name, prof)
        tag = "pp%d" % ci
        rows_out.append((tag, n, name, ci_int, u_int, prof))
        out.append("def %sRows : List (List Nat) := [%s]" % (
            tag, ", ".join("[" + ", ".join(map(str, rk)) + "]" for rk in rows_k)))
        # one definition per degree keeps each literal small for the elaborator
        for k, rk in enumerate(rels_k):
            if rk:
                chunks, cur, size = [], [], 0
                for v in rk:
                    if cur and size + len(v) > 240:
                        chunks.append(cur)
                        cur, size = [], 0
                    cur.append(v)
                    size += len(v)
                chunks.append(cur)
                for ch_i, ch in enumerate(chunks):
                    out.append("def %sRel%d_%d : List (List (Nat × Int × Int)) := [\n%s]" % (
                        tag, k, ch_i, ",\n".join("  [" + ", ".join("(%d, %d, %d)" % (i, a, b)
                                                                   for i, (a, b) in v) + "]"
                                                  for v in ch)))
                out.append("def %sRel%d : List (List (Nat × Int × Int)) := %s" % (
                    tag, k, " ++ ".join("%sRel%d_%d" % (tag, k, j) for j in range(len(chunks)))))
        out.append("def %sRels : List (List (List (Nat × Int × Int))) := [%s]" % (
            tag, ", ".join(("%sRel%d" % (tag, k)) if rk else "[]" for k, rk in enumerate(rels_k))))
        out.append("")
    groups = [("ppTwo", lambda n, name: n == 2 and name != "cn-special"),
              ("ppThreePure", lambda n, name: n == 3 and name == "pure"),
              ("ppThreeCn", lambda n, name: n == 3 and name == "cn"),
              ("ppThreeGeneric", lambda n, name: n == 3 and name == "generic"),
              ("ppSpecialTwo", lambda n, name: n == 2 and name == "cn-special"),
              ("ppSpecialThree", lambda n, name: n == 3 and name == "cn-special")]
    for gname, pred in groups:
        out.append("/-- cases `(n, c, u, rho_0..rho_4n, rows, relations)`. -/")
        out.append("def %s : List (Nat × List Int × (Int × Int) × List Nat × List (List Nat)"
                   " × List (List (List (Nat × Int × Int)))) := [" % gname)
        out.append(",\n".join("  (%d, [%s], (%d, %d), [%s], %sRows, %sRels)" % (
            n, ", ".join(map(str, c)), u[0], u[1], ", ".join(map(str, p)), t, t)
            for t, n, name, c, u, p in rows_out if pred(n, name)) + "]")
        out.append("")
    print("\n".join(out))
    for t, n, name, c, u, p in rows_out:
        print("-- %s n=%d %s u=%s profile %s" % (t, n, name, u, p[: 2 * n + 1]), file=sys.stderr)


if __name__ == "__main__":
    main()
