#!/usr/bin/env python3
"""
make_k3.py

Writes the random forms of item (LXI)(B) for HodgeObstruction.lean: the
fifteen symmetric integral forms G of ranks 2 to 6 drawn by
code/k3_hodge.py (seed 191), on which the kernel checks that the pairing
G_ij G_kl + G_ik G_jl + G_il G_jk on Sym^2 has determinant
det(G)^(m+1) 2^(m-1) (m+2).

Run from the repository root:  python3 lean/generate/make_k3.py > out
"""
import random


def main():
    rng = random.Random(191)
    forms = []
    for m in range(2, 7):
        for _ in range(3):
            A = [[rng.randint(-3, 3) for _ in range(m)] for _ in range(m)]
            G = [[A[i][j] + A[j][i] + (2 * rng.randint(-2, 2) if i == j else 0)
                  for j in range(m)] for i in range(m)]
            forms.append(G)
    print("/-- the fifteen forms of item (LXI)(B). -/")
    print("def k3Forms : List (List (List Int)) := [\n%s]" % ",\n".join(
        "  [" + ", ".join("[" + ", ".join(map(str, r)) + "]" for r in G) + "]" for G in forms))


if __name__ == "__main__":
    main()
