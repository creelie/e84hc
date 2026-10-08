#!/usr/bin/env python3
# Supporting script for item (LXI), code/k3_hodge.py (round 19, (F3') through motives).
"""
Threshold for the Hodge conjecture on Hilbert schemes S^[n] of a K3 surface S
with End_Hdg(T(S)) = Q, t = rank T(S) = 22 - rho(S) >= 3.

By de Cataldo-Migliorini, h(S^[n]) = sum over partitions nu of n of
h(S^(nu))(l(nu)-n), S^(nu) = prod_j S^(a_j), a_j = number of parts equal to j.
A non-pairing Hodge class (a determinant of T) survives in H^*(S^(nu)) only if
nu has at least t DISTINCT part sizes (a determinant is alternating, and the
symmetric group of each block S^(a_j) permutes its factors without sign).
So HC(S^[n]) holds for n < t(t+1)/2 = min{ n : some partition of n has t
distinct parts }, and for n >= t(t+1)/2 it is equivalent to the algebraicity
of det T(S) on S^t.  This script checks the combinatorial threshold by brute
force for t <= 7 and prints the bounds for rho = 1..19.
"""
def max_distinct_parts(n):
    # the largest k with 1+2+...+k <= n
    k = 0
    while (k+1)*(k+2)//2 <= n:
        k += 1
    return k

def partitions(n, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0:
        yield (); return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n-k, k):
            yield (k,) + rest

for t in range(3, 8):
    for n in range(1, t*(t+1)//2 + 3):
        brute = max(len(set(p)) for p in partitions(n))
        assert brute == max_distinct_parts(n)
        assert (brute >= t) == (n >= t*(t+1)//2)
print("brute-force check of the threshold t(t+1)/2 for t = 3..7: OK")
print(" rho   t   HC(S^k) for k <=   HC(S^[n]) for n <=   HC(M), M moduli (Buelles), dim M <=")
for rho in range(1, 20):
    t = 22 - rho
    print(f"{rho:4d} {t:3d}   {t-1:12d}         {t*(t+1)//2 - 1:12d}            {2*((t-1)//2):12d}")
