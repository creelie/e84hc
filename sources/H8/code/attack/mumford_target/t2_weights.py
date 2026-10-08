#!/usr/bin/env python3
"""
t2_weights.py  (round 12, track T2)

Weight computations for G = SL(2)^3 (exact integer arithmetic, peeling of
highest weights from the character).

 (1) wedge^k V, V = V(1,1,1), contains no summand V(2,0,0), V(0,2,0), V(0,0,2)
     for any k: the Hodge structure T = Lie G does not occur in the cohomology
     of X itself (in any degree, with any Tate twist).
 (2) Multiplicity of V(2,0,0) in wedge^a V (x) wedge^b V (the Kunneth
     components of H^{a+b}(X x X)): this is the number of copies of T in
     H^*(X x X), i.e. Hom_Hodge(T(S), H^{a+b}(X x X)(j)) = F^{mult}; these
     are the Kuga-Satake-type classes on S x X x X.
 (3) Carayol-type model: H^1(Z) (x) C = sum_i (V_i chi_i + V_i chi_i^{-1}),
     dim 12 (Z an abelian sixfold), with the Hodge cocharacter nontrivial on
     V_3 and on the CM characters at the compact places.  wedge^2 H^1(Z)
     contains T_1 + T_2 + T_3 with trivial character, of Hodge numbers
     (1,7,1): T occurs in H^2 of an abelian sixfold.
"""
import sys
from collections import Counter
from itertools import combinations

PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("PASS " if cond else "FAIL ") + name)


V = [(a, b, c) for a in (1, -1) for b in (1, -1) for c in (1, -1)]


def wedge(ws, k):
    return Counter(tuple(sum(x) for x in zip(*S)) if S else (0, 0, 0) for S in combinations(ws, k))


def irr_char(hw):
    return Counter((x, y, z) for x in range(-hw[0], hw[0] + 1, 2)
                   for y in range(-hw[1], hw[1] + 1, 2) for z in range(-hw[2], hw[2] + 1, 2))


def decompose(ch):
    ch = Counter(ch)
    out = Counter()
    while any(v != 0 for v in ch.values()):
        # highest weight: dominant with maximal sum
        cand = [w for w, m in ch.items() if m != 0]
        hw = max(cand, key=lambda w: (sum(w), w))
        m = ch[hw]
        assert m > 0 and all(x >= 0 for x in hw), (hw, m)
        out[hw] += m
        for w, mm in irr_char(hw).items():
            ch[w] -= m * mm
            if ch[w] == 0:
                del ch[w]
    return out


def tensor(c1, c2):
    out = Counter()
    for w1, m1 in c1.items():
        for w2, m2 in c2.items():
            out[tuple(a + b for a, b in zip(w1, w2))] += m1 * m2
    return out


dec = {k: decompose(wedge(V, k)) for k in range(9)}
for k in range(9):
    print(f"wedge^{k} V =", dict(sorted(dec[k].items())))
check("no V(2,0,0)-type summand in any wedge^k V",
      all(dec[k][w] == 0 for k in range(9) for w in [(2, 0, 0), (0, 2, 0), (0, 0, 2)]))
check("wedge^2 V = V(2,2,0)+V(2,0,2)+V(0,2,2)+1, wedge^4 V as in prop:mumfordproduct",
      dec[2] == Counter({(2, 2, 0): 1, (2, 0, 2): 1, (0, 2, 2): 1, (0, 0, 0): 1}) and
      dec[4] == Counter({(2, 2, 2): 1, (4, 0, 0): 1, (0, 4, 0): 1, (0, 0, 4): 1, (2, 2, 0): 1, (2, 0, 2): 1,
                         (0, 2, 2): 1, (0, 0, 0): 1}))

mult = {}
for a in range(9):
    for b in range(9):
        d = decompose(tensor(wedge(V, a), wedge(V, b)))
        mult[(a, b)] = d[(2, 0, 0)]
tot = Counter()
for (a, b), m in mult.items():
    tot[a + b] += m
print("multiplicity of T_1 = V(2,0,0) in H^n(X x X), n = 0..16:", [tot[n] for n in range(17)])
check("T occurs in H^2(X x X) exactly once (in H^1 (x) H^1)",
      tot[2] == 1 and mult[(1, 1)] == 1 and mult[(0, 2)] == 0 and mult[(2, 0)] == 0)
check("T does not occur in odd degree of X x X", all(tot[n] == 0 for n in range(1, 17, 2)))

# (3) Carayol-type sixfold.  Weights: (sl2^3 weight, character index vector (c1,c2,c3), Hodge type p)
# V_i chi_i : weights +-1 on factor i, character +e_i; V_i chi_i^{-1}: character -e_i.
# Hodge type (p) on H^1: on V_3 chi_3 and its dual the cocharacter lives in SL(V_3): weight +1 -> p=1, -1 -> p=0;
# on V_i chi_i (i=1,2) p=1 throughout, on V_i chi_i^{-1} p=0 (definite places).
H1 = []
for i in range(3):
    for s in (1, -1):
        for sgn in (1, -1):
            w = [0, 0, 0]
            w[i] = s
            ch = [0, 0, 0]
            ch[i] = sgn
            if i == 2:
                p = 1 if s == 1 else 0
            else:
                p = 1 if sgn == 1 else 0
            H1.append((tuple(w), tuple(ch), p))
check("dim H^1(Z) = 12, h^{1,0} = 6", len(H1) == 12 and sum(x[2] for x in H1) == 6)
W2 = Counter()
for A, B in combinations(H1, 2):
    w = tuple(a + b for a, b in zip(A[0], B[0]))
    ch = tuple(a + b for a, b in zip(A[1], B[1]))
    W2[(w, ch, A[2] + B[2])] += 1
# character-trivial part, split by Hodge type
triv = Counter()
for (w, ch, p), m in W2.items():
    if ch == (0, 0, 0):
        triv[(w, p)] += m
# weights of the character-trivial part: should be T_1+T_2+T_3 plus 3 trivial (one per i from wedge^2 V_i ... )
wts = Counter()
for (w, p), m in triv.items():
    wts[w] += m
d = decompose(wts)
print("character-trivial part of wedge^2 H^1(Z):", dict(d))
check("it is T_1 + T_2 + T_3 + 3 copies of the trivial representation",
      d == Counter({(2, 0, 0): 1, (0, 2, 0): 1, (0, 0, 2): 1, (0, 0, 0): 3}))
# Hodge numbers of the T-part: remove the three trivial weights of type (1,1) one per factor
hodge = Counter()
for (w, p), m in triv.items():
    hodge[p] += m
# total char-trivial part has 9 + 3 = 12 dims; trivial summands are of type (1,1) (p=1), so T has
hT = {2: hodge[2], 1: hodge[1] - 3, 0: hodge[0]}
print("Hodge numbers of the character-trivial part (p=2,1,0):", dict(hodge), " -> T:", hT)
check("T inside H^2(Z) has Hodge numbers (1,7,1): K3 type", hT == {2: 1, 1: 7, 0: 1})

print(f"\n{len(PASS)} checks passed, {len(FAIL)} failed")
sys.exit(1 if FAIL else 0)
