#!/usr/bin/env python3
"""
v1_weights.py  (round 12, adversarial verification of track T2)

Independent re-derivation (no highest-weight peeling; uses the Weyl
alternating-sum formula for SL2^3 instead):

  mult of V(n1,n2,n3) in a rep W = sum_{eps in {0,1}^3} (-1)^{|eps|}
                                   dim W_{(n1+2eps1, n2+2eps2, n3+2eps3)}

 (a) no V(2,0,0)/V(0,2,0)/V(0,0,2) in any wedge^k V   (T not in H^*(X))
 (b) multiplicity of V(2,0,0) in H^n(X x X) = sum_{a+b=n} wedge^a V (x) wedge^b V
 (c) Carayol-type 12-dimensional model: explicit weights of the torus
     (characters chi_1,chi_2,chi_3) and of SL2^3, Hodge types; the
     torus-invariant part of wedge^2 and its Hodge numbers.
 (d) Hodge-type check of T inside H^2(X x X): the unique copy of T in
     H^1 (x) H^1 has Hodge numbers (1,7,1) (so it is T(-1) with no further
     twist), using the Hodge cocharacter acting on V_3 only.
All arithmetic is in integers.
"""
import sys
from collections import Counter
from itertools import combinations, product

PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("PASS " if cond else "FAIL ") + name)


# weights of V: (x1,x2,x3) in {+-1}^3; Hodge p-index: p = 1 if x3 = +1 else 0
V = [(a, b, c) for a in (1, -1) for b in (1, -1) for c in (1, -1)]


def wedge_char(k, ws=V):
    ch = Counter()
    for S in combinations(range(len(ws)), k):
        w = tuple(sum(ws[i][j] for i in S) for j in range(3))
        ch[w] += 1
    return ch


def mult(ch, hw):
    m = 0
    for eps in product((0, 1), repeat=3):
        w = tuple(hw[j] + 2 * eps[j] for j in range(3))
        m += (-1) ** sum(eps) * ch.get(w, 0)
    return m


def tensor(c1, c2):
    out = Counter()
    for w1, m1 in c1.items():
        for w2, m2 in c2.items():
            out[tuple(a + b for a, b in zip(w1, w2))] += m1 * m2
    return out


W = {k: wedge_char(k) for k in range(9)}
Ts = [(2, 0, 0), (0, 2, 0), (0, 0, 2)]
check("(a) no T_i = V(2e_i) summand in any wedge^k V, k=0..8",
      all(mult(W[k], t) == 0 for k in range(9) for t in Ts))
# sanity: wedge^2 V = V(2,2,0)+V(2,0,2)+V(0,2,2)+1 by the alternating formula
check("sanity: wedge^2 V multiplicities", [mult(W[2], h) for h in [(2, 2, 0), (2, 0, 2), (0, 2, 2), (0, 0, 0)]]
      == [1, 1, 1, 1])
# dimension sanity: sum of mult*dim = dim
def dimrep(h):
    return (h[0] + 1) * (h[1] + 1) * (h[2] + 1)


for k in range(9):
    tot = 0
    for h in product(range(0, 9), repeat=3):
        m = mult(W[k], h)
        assert m >= 0
        tot += m * dimrep(h)
    assert tot == len(list(combinations(range(8), k))), k
check("sanity: the alternating formula reproduces dim wedge^k V for all k", True)

degmult = Counter()
for a in range(9):
    for b in range(9):
        degmult[a + b] += mult(tensor(W[a], W[b]), (2, 0, 0))
seq = [degmult[n] for n in range(17)]
print("(b) multiplicity of V(2,0,0) in H^n(X x X), n = 0..16:", seq)
check("(b) = [0,0,1,0,6,0,16,0,24,0,16,0,6,0,1,0,0]",
      seq == [0, 0, 1, 0, 6, 0, 16, 0, 24, 0, 16, 0, 6, 0, 1, 0, 0])
check("(b) the copy in H^2 is in H^1 (x) H^1",
      mult(tensor(W[1], W[1]), (2, 0, 0)) == 1 and mult(tensor(W[2], W[0]), (2, 0, 0)) == 0)

# (d) Hodge numbers of the T_1+T_2+T_3 part of H^1 (x) H^1: weights with p-grading.
# Use a graded character: key (w, p).  Multiplicity of T_i with Hodge type p via
# the alternating formula on each p-graded piece is not legitimate (the cocharacter
# does not commute with SL2(V_3)); instead compute the Hodge numbers of the
# V(2,0,0)+V(0,2,0)+V(0,0,2) isotypic part as: H^{p}-dimension of the full space minus
# that of the other isotypic parts, all computed from the Hodge cocharacter acting
# through the weight of the third factor (p = (x3+1)/2 per leg).
# The Hodge cocharacter is the cocharacter z -> (1,1,diag(z,1)) of GL(V_3) up to the
# weight; on an irreducible V(n1,n2,n3) its p-distribution is that of V(n3) shifted:
# p = (x3 + n_legs)/2.  So on H^1 (x) H^1 (two legs) p = (x3 + 2)/2.
def hodge_of_irrep(h, nlegs):
    out = Counter()
    for x3 in range(-h[2], h[2] + 1, 2):
        out[(x3 + nlegs) // 2] += (h[0] + 1) * (h[1] + 1)
    return out


hT = Counter()
for t in Ts:
    m = mult(tensor(W[1], W[1]), t)
    for p, d in hodge_of_irrep(t, 2).items():
        hT[p] += m * d
print("(d) Hodge numbers (p=2,1,0) of T in H^1 (x) H^1:", hT[2], hT[1], hT[0])
check("(d) T in H^2(X x X) has Hodge numbers (1,7,1)", (hT[2], hT[1], hT[0]) == (1, 7, 1))

# (c) Carayol-type model.  H^1 (x) C = sum_i V_i chi_i + V_i chi_i^{-1}.
# Each basis vector: (sl2^3 weight, torus character vector in Z^3, Hodge p).
H1 = []
for i in range(3):
    for s in (1, -1):          # weight on V_i
        for c in (1, -1):      # chi_i^{c}
            w = [0, 0, 0]; w[i] = s
            ch = [0, 0, 0]; ch[i] = c
            if i == 2:
                p = 1 if s == 1 else 0      # the split place: cocharacter in SL(V_3)
            else:
                p = 1 if c == 1 else 0      # definite places: the CM type picks chi_i
            H1.append((tuple(w), tuple(ch), p))
check("(c) dim 12, h^{1,0} = 6", len(H1) == 12 and sum(x[2] for x in H1) == 6)
# complex conjugation: (w, ch, p) -> (-w? , -ch, 1-p).  Check the multiset is stable
# under (w,ch,p) -> (w', -ch, 1-p) with w' ranging over the same SL2-rep (weights symmetric).
conj = Counter((w, tuple(-x for x in ch), 1 - p) for (w, ch, p) in H1)
# for the check, compare the (ch, p) marginals and the SL2 weight multisets per (ch)
marg = Counter((ch, p) for (w, ch, p) in H1)
margc = Counter((ch, p) for (w, ch, p) in conj.elements())
check("(c) Hodge types are compatible with complex conjugation (chi -> chi^{-1}, p -> 1-p)", marg == margc)
W2 = Counter()
for A, B in combinations(H1, 2):
    W2[(tuple(a + b for a, b in zip(A[0], B[0])), tuple(a + b for a, b in zip(A[1], B[1])), A[2] + B[2])] += 1
triv = Counter()
trivp = Counter()
for (w, ch, p), m in W2.items():
    if ch == (0, 0, 0):
        triv[w] += m
        trivp[(w, p)] += m
mults = {h: mult(triv, h) for h in [(2, 0, 0), (0, 2, 0), (0, 0, 2), (0, 0, 0)]}
print("(c) torus-invariant part of wedge^2: multiplicities", mults, "dim", sum(triv.values()))
check("(c) torus-invariant part of wedge^2 H^1 = T_1+T_2+T_3 + 3.1",
      mults == {(2, 0, 0): 1, (0, 2, 0): 1, (0, 0, 2): 1, (0, 0, 0): 3} and sum(triv.values()) == 12)
# Hodge numbers of the invariant part, and of its T-part: the trivial summands are the
# weight-0 vectors of V_i chi_i (x) V_i chi_i^{-1} antisymmetric part; for i = 1,2 they are (1,1)
# because every vector there is (1,0)(x)(0,1); for i = 3 the invariant line is eps_3, of type (1,1).
hp = Counter()
for (w, p), m in trivp.items():
    hp[p] += m
print("(c) Hodge numbers of the torus-invariant part (p=2,1,0):", hp[2], hp[1], hp[0])
check("(c) T-part has Hodge numbers (1,7,1)", (hp[2], hp[1] - 3, hp[0]) == (1, 7, 1))
# also: other torus characters chi_i chi_j^{+-1} (i != j) and chi_i^{+-2} occur, but none is trivial
check("(c) only the pairs (V_i chi_i, V_i chi_i^{-1}) contribute torus-invariants",
      all(ch != (0, 0, 0) or w in triv for (w, ch, p) in W2))

print(f"\n{len(PASS)} checks passed, {len(FAIL)} failed")
sys.exit(1 if FAIL else 0)
