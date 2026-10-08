import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1_annihilator import *
rng = random.Random(3)
a = [Fr(2), Fr(3), Fr(5), Fr(7)]
seen = {}
mons = [(i, j) for i in range(5) for j in range(5)]
# single monomials and pairs
for m in mons:
    r, k, kinds, _ = annihilator(gamma_of(a, {m: Fr(1)}))
    seen.setdefault(r, []).append(("mono", m))
for m1, m2 in itertools.combinations(mons, 2):
    if rng.random() < 0.25:
        r, k, kinds, _ = annihilator(gamma_of(a, {m1: Fr(1), m2: Fr(rng.randint(1, 5))}))
        seen.setdefault(r, []).append(("pair", m1, m2))
for r in sorted(seen):
    print(r, len(seen[r]), seen[r][:4])
