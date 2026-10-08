#!/usr/bin/env python3
"""
make_targets.py

Writes the certificates of part (A) of item (XLIII), the invariant ring of
the Mumford group on X x X, for HodgeObstruction.lean.  The model is that of
code/targets_reduction.py, which this script imports: H^1(X x X) = V (+) V on
sixteen generators, the generator i of weight (1 - 2 b_2, 1 - 2 b_1, 1 - 2 b_0)
with b the bits of i mod 8.

It records
  * integer bases I2, I4 of the invariants in degrees 2 and 4 (the kernel
    checks that each monomial has weight zero and that the three raising
    operators kill each vector, so each is invariant);
  * for degrees 6 and 8, a list of recipes (j, d, g): the basis vector is the
    product of basis vector j of degree k - d with generator g of degree d;
  * for each family of vectors whose rank is claimed, as many monomials as
    the rank, on which the vectors have a minor that is nonzero modulo
    p = 1000003 (so nonzero over Z).

Run from the repository root:  python3 lean/generate/make_targets.py > out
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "code"))
import targets_reduction as T  # noqa: E402

P = 1000003


def pivots(vecs):
    """monomials on which the vectors (dicts) have a nonsingular minor mod P"""
    rows = [{k: c % P for k, c in v.items() if c % P} for v in vecs]
    cols = []
    red = []
    for r in rows:
        r = dict(r)
        for (c, b) in red:
            if c in r:
                f = r[c] * pow(b[c], P - 2, P) % P
                for k, x in b.items():
                    nv = (r.get(k, 0) - f * x) % P
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
        assert r, "dependent"
        c = min(r)
        red.append((c, r))
        cols.append(c)
    return cols


def lean_vec(v):
    return "[" + ", ".join("(%d, %d)" % (m, c) for m, c in sorted(v.items())) + "]"


def weight_polynomial():
    """the list tgGen of the Lean file, in the order its fold produces"""
    def key(q, a, b, c):
        return q * 1000000 + a * 10000 + b * 100 + c
    P = [(key(0, 8, 8, 8), 1)]
    for j in range(8):
        acc = list(P)
        for k0, c0 in P:
            q, a, b, c = k0 // 1000000, k0 // 10000 % 100, k0 // 100 % 100, k0 % 100
            w = T.weight(j)
            k = key(q + 1, a + w[0], b + w[1], c + w[2])
            for i, (kk, cc) in enumerate(acc):
                if kk == k:
                    acc[i] = (k, cc + c0)
                    break
            else:
                acc.append((k, c0))
        P = acc
    return P


def irr_table(P):
    d = dict(P)

    def mult(q, A, B, C):
        return d.get(q * 1000000 + A * 10000 + B * 100 + C, 0)
    out = []
    for q in range(9):
        xs = [0, 2, 4] if q % 2 == 0 else [1, 3]
        row = []
        for a in xs:
            for b in xs:
                for c in xs:
                    s = 0
                    for e in range(8):
                        x, y, z = 2 * (e >> 2 & 1), 2 * (e >> 1 & 1), 2 * (e & 1)
                        s += (-1) ** bin(e).count("1") * mult(q, a + 8 + x, b + 8 + y, c + 8 + z)
                    row.append(s)
        out.append(row)
    return out


def main():
    P = weight_polynomial()
    print("/-- the weight generating polynomial of `wedge^* V`, recorded. -/")
    print("def tgGenRec : List (Nat × Nat) := [" + ", ".join("(%d, %d)" % x for x in P) + "]")
    print("/-- the multiplicities of the irreducible modules in `wedge^q V`. -/")
    print("def tgIrrRec : List (List Int) := [" + ", ".join(
        "[" + ", ".join(map(str, r)) + "]" for r in irr_table(P)) + "]")
    I2 = T.exact_invariants(2)
    I4 = T.exact_invariants(4)
    out = []
    out.append("/-- the invariants of degree two. -/")
    out.append("def tgI2 : List (List (Nat × Int)) := [\n  " +
               ",\n  ".join(lean_vec(v) for v in I2) + "]")
    out.append("/-- the invariants of degree four. -/")
    out.append("def tgI4 : List (List (Nat × Int)) := [\n  " +
               ",\n  ".join(lean_vec(v) for v in I4) + "]")
    out.append("def tgPivI2 : List Nat := %s" % pivots(I2))
    out.append("def tgPivI4 : List Nat := %s" % pivots(I4))
    prods = [T.wedge(I2[a], I2[b]) for a in range(3) for b in range(a, 3)]
    out.append("def tgPivProd : List Nat := %s" % pivots(prods))
    span = {2: I2, 4: I4}
    gens = {2: I2, 4: I4}
    for k in (6, 8):
        S = T.ModSpan()
        basis, recipes = [], []
        for d in (2, 4):
            for j, a in enumerate(span[k - d]):
                for g, x in enumerate(gens[d]):
                    v = T.wedge(a, x)
                    if S.add(v):
                        basis.append(v)
                        recipes.append((j, d, g))
        span[k] = basis
        out.append("def tgRec%d : List (Nat × Nat × Nat) := %s" % (
            k, "[" + ", ".join("(%d, %d, %d)" % r for r in recipes) + "]"))
        out.append("def tgPiv%d : List Nat := %s" % (k, pivots(basis)))
        print("-- degree %d: %d vectors" % (k, len(basis)), file=sys.stderr)
    print("\n".join(out))


if __name__ == "__main__":
    main()
