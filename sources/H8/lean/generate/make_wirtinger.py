#!/usr/bin/env python3
"""
make_wirtinger.py

Writes the data of item (LXIII), the Wirtinger bound on a Mumford square,
for HodgeObstruction.lean: integral bases of the three summands U_12, U_13,
U_23 of wedge^2 V in the split model of code/mumford_mass.py (V = C^2 (x) C^2
(x) C^2, generators 0..7 indexed by (a,b,c) in {0,1}^3), as vectors of
coefficients on the monomials e_a e_b, a < b.  The kernel checks that they
are eigenvectors of the three Casimir operators with the stated eigenvalues,
that with theta they span wedge^2 V, and everything else of the item.

Run from the repository root:  python3 lean/generate/make_wirtinger.py > out
"""
import os
import sys
from math import gcd

import sympy

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "code"))
import mumford_mass as W  # noqa: E402


def main():
    pieces, PI, _ = W.build_tensors()
    out = []
    for key in ("12", "13", "23"):
        rows = []
        for vec in pieces[key]:
            den = 1
            for x in vec:
                den = sympy.ilcm(den, sympy.nsimplify(x).q)
            iv = [int(sympy.nsimplify(x) * den) for x in vec]
            g = 0
            for x in iv:
                g = gcd(g, abs(x))
            iv = [x // g for x in iv]
            rows.append("[" + ", ".join("(%d, %d)" % ((1 << a) | (1 << b), x)
                                        for (a, b), x in zip(W.PAIRS, iv) if x) + "]")
        out.append("def wmU%s : List (List (Nat × Int)) := [\n  %s]" % (key, ",\n  ".join(rows)))
    print("\n\n".join(out))


if __name__ == "__main__":
    main()
