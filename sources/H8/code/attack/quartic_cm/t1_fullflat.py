"""r(gamma) for gamma a general flat Hodge class of the generic (F,2) member:
gamma = sum_{S subset of embeddings, i, j} c_{S,i,j} alpha_S theta_1^i theta_2^j,
with the Weil part (|S|=1, i=j=0) nonzero.  Exact, random rational coefficients."""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1_annihilator import *
rng = random.Random(17)
th = [theta(0), theta(1)]
thp = {(i, j): wedge(powf(th[0], i), powf(th[1], j)) for i in range(5) for j in range(5)}
subsets = [S for k in range(0, 5) for S in itertools.combinations(range(4), k)]
aS = {}
for S in subsets:
    f = {(): Fr(1)}
    for s in S:
        f = wedge(f, alpha(s))
    aS[S] = f
res = []
for trial in range(3):
    g = {}
    for S in subsets:
        if not aS[S]:
            continue
        for (i, j), tp in thp.items():
            if rng.random() < 0.5 or (len(S) == 1 and i == j == 0):
                c = Fr(rng.randint(1, 9), rng.randint(1, 9))
                g = addf(g, scalf(c, wedge(aS[S], tp)))
    r, k, kinds, ker = annihilator(g)
    res.append((r, k, kinds))
    print("general flat gamma: r = %d, dim Ann = %d, %s" % (r, k, kinds))
check("general flat Hodge gamma with nonzero Weil part: r = 112", all(x[0] == 112 for x in res))
summary()
