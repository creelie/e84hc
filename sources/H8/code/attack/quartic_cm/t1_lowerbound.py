"""
t1_lowerbound.py -- a lower bound for r(gamma) valid for EVERY
gamma = omega + p(theta_1, theta_2), omega = sum_sigma a_sigma alpha_sigma, all a_sigma != 0.

The torus (C^x)^16 scaling each basis vector x_{sigma,j}, y_{sigma,j} separately acts on
H^*(A,C) and (contragrediently on T) on HT^2, compatibly with contraction.  Characters:
a monomial is its own character; theta and omega are sums of monomials.
Contraction of a basis operator with a monomial is a multiple of a single monomial.
Let G be the set of monomials m of H^*(A,C) such that m occurs in xi |_ alpha_sigma for some
basis operator xi and embedding sigma, and such that NO basis operator applied to ANY monomial
occurring in ANY theta-monomial theta_1^i theta_2^j can produce the character of m.
Then for every p the G-components of xi |_ gamma equal those of xi |_ omega, so
      r(gamma) >= rank( xi -> proj_G (xi |_ omega) ),
computed here exactly (it does not depend on p at all).
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1_annihilator import *

def char_of_mono(K):
    # finest torus (C^x)^16 scaling each basis vector x_{sigma,j}, y_{sigma,j} separately:
    # the character of a monomial is the monomial itself
    return K

# all monomials occurring in theta-monomials
th = [theta(0), theta(1)]
pmonos = set()
for i in range(5):
    for j in range(5):
        pmonos.update(wedge(powf(th[0], i), powf(th[1], j)).keys())
# characters reachable from p-terms by any operator
bad_chars = set()
for K in pmonos:
    f = {K: Fr(1)}
    for op in OPS:
        for L in op[2](f):
            bad_chars.add(char_of_mono(L))
rng = random.Random(5)
a = [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(4)]
om = gamma_of(a, {})
imgs = [op[2](om) for op in OPS]
good = [{L: c for L, c in f.items() if char_of_mono(L) not in bad_chars} for f in imgs]
lb = rank_forms(good)
print("rank of the p-independent part of the contraction:", lb)
kinds = {}
for kind in ("z", "v", "pi"):
    kinds[kind] = rank_forms([good[c] for c, op in enumerate(OPS) if op[0] == kind])
print("by summand:", kinds)
check("r(gamma) >= %d for every p (p-independent lower bound)" % lb, lb > 0)
summary()
