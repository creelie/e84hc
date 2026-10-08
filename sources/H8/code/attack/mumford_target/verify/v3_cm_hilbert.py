#!/usr/bin/env python3
"""
v3_cm_hilbert.py  (round 12, adversarial verification of track T2)

Theorem A of the T2 report asserts that (b) of cor:mumfordequiv is
equivalent to the Hodge conjecture for every power X_t^n "for all t", which
includes the CM points c of the Mumford curve.  Theorem A itself only treats
Hodge group G.  At a CM point the Hodge group is a maximal torus of G, with
the eight distinct weights w in {+-1}^3 on V (thm:mumfordcm).  The Hodge
classes of X_c^n (x) C are spanned by monomials e_{w_1}^{(i_1)} ^ ... whose
multiset of weights sums to zero.  If every MINIMAL zero-sum multiset of
weights has pairwise distinct elements, every such monomial is a product of
monomials with distinct weights, each a pull-back f^*(t) of a Hodge class t
of X_c along a homomorphism X_c^n -> X_c (End^0(X_c) (x) C = diagonal
matrices, Zariski density of rational homomorphisms), and Markman's theorem
for abelian fourfolds gives the Hodge conjecture for every X_c^n.

This script computes the Hilbert basis of the monoid
   { n in N^8 : sum_w n_w w = 0 }
by brute force over n in {0..B}^8 and checks that every irreducible element
is a 0/1 vector.  Bound: an irreducible element of this monoid has entries
bounded by ... (not needed: we check up to B = 4 and, separately, prove
the statement by hand below).

Hand proof (checked here numerically for B = 4): let n be a zero-sum multiset
with some n_w >= 2.  If n_{-w} >= 1 then {w,-w} is a zero-sum proper
submultiset.  Otherwise replace coordinates by x -> x*w (coordinatewise sign
change, an automorphism of the weight set), so w = (1,1,1) and n_{(-1,-1,-1)}
= 0.  Every other weight u has exactly one or two coordinates equal to +1.
Sum of all coordinates of all elements = 0: 3 n_w + sum_u (#plus(u) - #minus(u))
n_u = 0, where #plus-#minus is +1 (two plus signs) or -1 (one plus sign).
So the elements with one plus sign, say of total multiplicity m1, satisfy
m1 = 3 n_w + m2 >= 6.  ... (the brute force below is the actual check)
"""
import sys
from itertools import product

PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("PASS " if cond else "FAIL ") + name)


W = [(a, b, c) for a in (1, -1) for b in (1, -1) for c in (1, -1)]
B = 5
zs = []
for n in product(range(B + 1), repeat=8):
    if sum(n) == 0:
        continue
    s = [sum(n[i] * W[i][j] for i in range(8)) for j in range(3)]
    if s == [0, 0, 0]:
        zs.append(n)
zsset = set(zs)
print("nonzero zero-sum vectors with entries <=", B, ":", len(zs))


def reducible(n):
    # exists 0 < m < n (componentwise) with m zero-sum
    for m in product(*[range(x + 1) for x in n]):
        if m == n or sum(m) == 0:
            continue
        if m in zsset:
            return True
    return False


irr = [n for n in zs if not reducible(n)]
print("irreducible elements:", len(irr))
for n in irr:
    print("  ", n, "support", [W[i] for i in range(8) if n[i]])
check("every irreducible zero-sum multiset (entries <= %d) is a set (0/1 vector)" % B,
      all(max(n) <= 1 for n in irr))
# completeness of the bound: an irreducible element with an entry >= B+1 would, by Gordan/Sebo
# bounds, need ... ; instead verify directly that no irreducible element has an entry equal to B
# (if the Hilbert basis had elements with large entries, some would show entries near B).
check("no irreducible element has an entry >= 2 within the box", all(max(n) < 2 for n in irr))

# Exact proof that the six elements found generate the monoid (so the box is irrelevant):
# E = weights with product of coordinates +1: e1..e4; the others are -e1..-e4.
# The only integer relation among e1..e4 is (1,1,1,1) (rank 3, det of any three = +-4).
# A zero-sum n = sum a_i e_i + b_i (-e_i) forces a_i - b_i = k constant; subtracting |k| copies of
# the quadruple {e_i} (k>0) or {-e_i} (k<0) leaves the pairs {e_i,-e_i}.
E = [w for w in W if w[0]*w[1]*w[2] == 1]
def det3(M):
    return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
            + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
import itertools
check("e1+e2+e3+e4 = 0 and any three of e1..e4 are independent (so the relation lattice is Z(1,1,1,1))",
      [sum(e[j] for e in E) for j in range(3)] == [0,0,0] and
      all(det3([list(E[a]),list(E[b]),list(E[c])]) != 0 for a,b,c in itertools.combinations(range(4),3)))
check("the odd weights are exactly -E", sorted(w for w in W if w[0]*w[1]*w[2] == -1) == sorted(tuple(-x for x in e) for e in E))

print(f"\n{len(PASS)} checks passed, {len(FAIL)} failed")
sys.exit(1 if FAIL else 0)
