"""
The sign in the closed form of the cohomological Fourier-Mukai transform.

Notation as in fm_theta.py.  Writing  l = sum_{i=1}^{2g} e_i f_i  and
theta' = sum_{j=1}^{g} f_j f_{g+j}, the only part of exp(l) that can complete
theta'^k to the top f-form is l^{2g-2k}/(2g-2k)!, and the f-indices it must
supply are forced:  S = [2g] \ (T u (g+T))  for each k-subset T of [g].  So
each T contributes exactly one term and the terms are in bijection with the
(g-k)-subsets U = [g] \ T, which are exactly the terms of theta^{g-k}.

What remains is the sign, computed here as a permutation sign, for a range of
g and k well beyond what a full exterior-algebra expansion can reach.
"""
from math import factorial


def perm_sign(seq):
    """Sign of the permutation sorting `seq` into increasing order."""
    s = 1
    arr = list(seq)
    for i in range(len(arr)):
        for j in range(len(arr) - 1, i, -1):
            if arr[j - 1] > arr[j]:
                arr[j - 1], arr[j] = arr[j], arr[j - 1]
                s = -s
    return s


def term_sign(g, k, T):
    """Sign with which the term indexed by T contributes.

    Generators are labelled  e_1..e_{2g} -> 1..2g  and  f_1..f_{2g} ->
    2g+1..4g.  We write the product

        ( prod_{j in T} f_j f_{g+j} ) . ( prod_{i in S} e_i f_i )

    as a word in the generators, sort it, and compare with the target word
    ( prod_{j in U} e_j e_{g+j} ) . ( f_1 ... f_{2g} ).
    """
    U = [j for j in range(1, g + 1) if j not in T]
    S = sorted([i for i in range(1, 2 * g + 1)
                if i not in T and i - g not in T])
    word = []
    for j in T:
        word += [2 * g + j, 2 * g + g + j]           # f_j f_{g+j}
    for i in S:
        word += [i, 2 * g + i]                        # e_i f_i
    s1 = perm_sign(word)

    target = []
    for j in U:
        target += [j, g + j]                          # e_j e_{g+j}
    target += [2 * g + i for i in range(1, 2 * g + 1)]  # f_1..f_{2g}
    s2 = perm_sign(target)
    return s1 * s2


if __name__ == "__main__":
    print("sign of each term, and the resulting constant")
    print(f"{'g':>3} {'k':>3}  {'signs agree':>12}  {'sigma':>6}  "
          f"{'predicted':>10}  {'match':>6}")
    allok = True
    for g in range(1, 13):
        for k in range(0, g + 1):
            from itertools import combinations
            sgns = set()
            for T in combinations(range(1, g + 1), k):
                sgns.add(term_sign(g, k, list(T)))
            agree = (len(sgns) == 1)
            sig = sgns.pop() if agree else None
            pred = (-1) ** ((g * (g + 1)) // 2 + k)
            ok = agree and sig == pred
            allok = allok and ok
            if g <= 4 or k in (0, g) or not ok:
                print(f"{g:>3} {k:>3}  {str(agree):>12}  {str(sig):>6}  "
                      f"{pred:>10}  {str(ok):>6}")
    print()
    print("closed form:  Phi(theta'^k) = (-1)^(g(g+1)/2 + k) * k!/(g-k)! * "
          "theta^(g-k)")
    print("all signs uniform and matching the closed form up to g = 12:", allok)
