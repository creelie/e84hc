"""s1_profile.py -- the dimension count of thm:quarticobstruction for CM fields of
degree 2g, in particular sextic fields (g = 3), at n = 2.

Model.  X is a principally polarised abelian 2g-fold with real multiplication by
a totally real field F0 of degree g.  Over C, H^1(X) is spanned by holomorphic
z_0..z_{N-1} and antiholomorphic zbar_0..zbar_{N-1}, N = 2g; the real place j
owns z_{2j}, z_{2j+1}, and theta_j = z_{2j} zbar_{2j} + z_{2j+1} zbar_{2j+1} is,
up to the factor sqrt(-1)/2, the component of the polarisation at that place.
A secant class of F = F0(sqrt(-q)) is v = sum_eps w_eps e_eps with
e_eps = exp(sum_j eps_j c_j theta_j), eps in {+-1}^g, c_j a nonzero multiple of
sqrt(tau_j(q)) (in these coordinates the exponents are real).  A class is real
iff w_{-eps} = conj(w_eps); that real form is Zariski dense in the space of all
w with the same support, so generic ranks may be computed at random RATIONAL w,
which keeps everything over Q.

HT^k(X) acts by contracting with d/dz (p of them) and wedging with zbar
(q of them), p + q = k.  r^k(v) is the rank of HT^k(X) -> H^*(X), xi -> xi _| v,
computed EXACTLY over Z (flint fmpz_mat.rank) after clearing denominators.  The
values at random rational points are the generic values unless the point is
special; two independent random choices are required to agree.

Questions answered:
 (1) the full profile r^0..r^{2g} of secant classes of every support pattern and
     every flattening rank; palindromy r^k = r^{2g-k};
 (2) the formula r^2 = sum_j rho_j + 4 sum_{j<k} N_jk, with rho_j the rank of the
     flattening of W = (w_eps) at place j and N_jk the number of nonzero entries
     of the (j,k) marginal support of W;
 (3) chi(v,v) = (-4)^g N(q) sum |w_eps|^2 for real classes (checked over Q(i)),
     negative definite for g = 3;
 (4) for a minimal object (e_k = r^k for k <= 2, Ext^{<0} = 0) on the sixfold,
     Serre duality gives e_3 = 2 r^2 - 2 r^1 + 2 - chi, and minimality is
     numerically possible iff e_3 >= r^3, r^4 <= r^2, r^5 <= r^1, r^6 <= 1: the
     threshold T = r^3 - 2 r^2 + 2 r^1 - 2 on -chi.
The quartic case g = 2 is run first as a regression test: its profile must be
(1, 8, 2 rho + 4 N_w, 8, 1).
"""
import itertools
import os
import random
import sys
import time
from fractions import Fraction as Fr
from math import lcm, comb

import flint

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "quartic_obstruction"))
from ealib import add, sc, wedge, contract, lwedge, one, gen, expo, QI  # noqa: E402

PASS, FAIL = [], []


def check(name, ok):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name), flush=True)


class Model:
    def __init__(self, g):
        self.g = g
        self.N = 2 * g
        self.theta = [add(wedge(gen(2 * j), gen(self.N + 2 * j)),
                          wedge(gen(2 * j + 1), gen(self.N + 2 * j + 1))) for j in range(g)]
        self.top = (1 << (2 * self.N)) - 1

    def exp_factor(self, j, c):
        """exp(c theta_j) = 1 + c theta_j + c^2 theta_j^2 / 2 (theta_j^3 = 0)."""
        t = self.theta[j]
        return add(one(), sc(c, t), sc(c * c / 2, wedge(t, t)))

    def secant(self, W, cs):
        """v = sum_eps W[eps] exp(sum_j eps_j c_j theta_j)."""
        v = {}
        for eps, w in W.items():
            if w == 0:
                continue
            e = one()
            for j in range(self.g):
                e = wedge(e, self.exp_factor(j, eps[j] * cs[j]))
            v = add(v, sc(w, e))
        return v

    def HT(self, k):
        out = []
        for p in range(0, k + 1):
            q = k - p
            if p > self.N or q > self.N:
                continue
            for B in itertools.combinations(range(self.N), p):
                for A in itertools.combinations(range(self.N), q):
                    out.append((A, B))
        return out

    def act(self, AB, u):
        A, B = AB
        r = u
        for b in B:
            r = contract(b, r)
        for a in reversed(A):
            r = lwedge(self.N + a, r)
        return r

    def rank(self, vecs):
        vecs = [v for v in vecs if v]
        if not vecs:
            return 0
        keys = sorted(set(k for v in vecs for k in v))
        kid = {k: i for i, k in enumerate(keys)}
        M = flint.fmpz_mat(len(vecs), len(keys))
        for r, v in enumerate(vecs):
            den = 1
            for c in v.values():
                den = lcm(den, Fr(c).denominator)
            for k, c in v.items():
                M[r, kid[k]] = int(Fr(c) * den)
        return M.rank()

    def profile(self, v):
        return [self.rank([self.act(AB, v) for AB in self.HT(k)]) for k in range(2 * self.N + 1)
                if k <= self.N]

    # pairing
    def orientation(self):
        """coefficient of the top monomial in theta_R^N / N!, theta_R = (i/2) sum theta_j."""
        th = {}
        for t in self.theta:
            th = add(th, t)
        th = {k: QI(0, Fr(1, 2)) * QI(c) for k, c in th.items()}
        p = {0: QI(1)}
        for m in range(1, self.N + 1):
            p = wedge(p, th)
            p = {k: c * QI(Fr(1, m)) for k, c in p.items()}
        return p[self.top]

    def chi(self, v):
        vd = {k: (c if (bin(k).count("1") // 2) % 2 == 0 else -c) for k, c in v.items()}
        prod = wedge(vd, v)
        c = prod.get(self.top, QI(0))
        return c / self.orientation()


def flattening_rank(W, g, j):
    """rank of the 2 x 2^{g-1} flattening of W at place j."""
    rows = []
    for s in (1, -1):
        row = []
        for rest in itertools.product((1, -1), repeat=g - 1):
            eps = rest[:j] + (s,) + rest[j:]
            row.append(Fr(W.get(eps, 0)))
        rows.append(row)
    M = flint.fmpq_mat(2, len(rows[0]))
    for a in range(2):
        for b in range(len(rows[0])):
            M[a, b] = flint.fmpq(rows[a][b].numerator, rows[a][b].denominator)
    return M.rank()


def marginal_support(W, g, j, k):
    """number of (s_j, s_k) such that some eps with those signs has W[eps] != 0."""
    return len({(e[j], e[k]) for e, w in W.items() if w != 0})


def rand_rat(rng):
    return Fr(rng.randint(-9, 9) or 1, rng.randint(1, 7))


def shapes(g, rng):
    """(name, W) for a family of secant coefficient tensors W on {+-1}^g."""
    signs = list(itertools.product((1, -1), repeat=g))
    pairs = []
    for e in signs:
        m = tuple(-x for x in e)
        if (m, e) not in pairs:
            pairs.append((e, m))
    out = []
    # supports closed under eps -> -eps (those of real classes), generic coefficients
    for r in range(1, len(pairs) + 1):
        for sub in itertools.combinations(range(len(pairs)), r):
            W = {}
            for i in sub:
                a, b = pairs[i]
                W[a] = rand_rat(rng)
                W[b] = rand_rat(rng)
            out.append(("support %d pairs %s" % (r, sub), W))
    # structured tensors on the full support: decomposable, and one factor decomposable
    if g >= 2:
        vecs = [(rand_rat(rng), rand_rat(rng)) for _ in range(g)]
        W = {e: Fr(1) for e in signs}
        for e in signs:
            for j in range(g):
                W[e] *= vecs[j][0 if e[j] == 1 else 1]
        out.append(("decomposable (rank one) on the full support", W))
        if g == 3:
            a = (rand_rat(rng), rand_rat(rng))
            B = {(s, t): rand_rat(rng) for s in (1, -1) for t in (1, -1)}
            W = {e: a[0 if e[0] == 1 else 1] * B[(e[1], e[2])] for e in signs}
            out.append(("a (x) B, B generic 2x2, full support", W))
            W = {e: Fr(0) for e in signs}
            W[(1, 1, 1)] = rand_rat(rng)
            W[(-1, -1, -1)] = rand_rat(rng)
            W[(1, -1, -1)] = rand_rat(rng)
            W[(-1, 1, 1)] = rand_rat(rng)
            out.append(("two antipodal pairs sharing places 2,3 pattern", W))
    return out


def run(g, seed):
    rng = random.Random(seed)
    M = Model(g)
    cs = [Fr(j + 2, j + 1) for j in range(g)]       # distinct nonzero rationals
    rng.shuffle(cs)
    results = {}
    for name, W in shapes(g, rng):
        v = M.secant(W, cs)
        prof = M.profile(v)
        rhos = [flattening_rank(W, g, j) for j in range(g)]
        Njk = [marginal_support(W, g, j, k) for j, k in itertools.combinations(range(g), 2)]
        results[name] = (prof, rhos, Njk, sum(1 for w in W.values() if w != 0))
    return M, results


def main():
    t0 = time.time()
    # ---------------------------------------------------------------- g = 2
    print("g = 2 (quartic): regression against (1, 8, 2 rho + 4 N_w, 8, 1)")
    M2, res2a = run(2, 11)
    _, res2b = run(2, 23)
    ok = True
    for name, (prof, rhos, Njk, Nw) in res2a.items():
        rho = max(rhos)
        exp_r2 = 2 * rho + 4 * Nw
        good = prof == [1, 8, exp_r2, 8, 1]
        ok = ok and good and res2b[name][0] == prof
        print("   %-48s profile %s rho %s N_w %d" % (name, prof, rhos, Nw))
    check("g = 2: the profile is (1, 8, 2 rho + 4 N_w, 8, 1) for every shape, at two random points", ok)
    # ---------------------------------------------------------------- g = 3
    print("g = 3 (sextic)")
    M3, resa = run(3, 101)
    _, resb = run(3, 202)
    agree = all(resb[k][0] == resa[k][0] for k in resa)
    check("g = 3: two independent random points give the same profiles for every shape", agree)
    pal = True
    formula = True
    thresholds = {}
    for name, (prof, rhos, Njk, Nw) in resa.items():
        pal = pal and all(prof[k] == prof[6 - k] for k in range(7))
        guess = sum(rhos) + 4 * sum(Njk)
        formula = formula and prof[2] == guess
        T = prof[3] - 2 * prof[2] + 2 * prof[1] - 2
        thresholds[name] = T
        print("   %-48s profile %s rho %s N_jk %s N_w %d  T = %d%s"
              % (name, prof, rhos, Njk, Nw, T, "" if prof[2] == guess else "  (r2 != %d)" % guess))
    check("g = 3: every profile is palindromic, r^k = r^{6-k}", pal)
    check("g = 3: r^1 = 12 for every shape", all(p[1] == 12 for p, *_ in resa.values()))
    check("g = 3: r^2 = sum_j rho_j + 4 sum_{j<k} N_jk for every shape", formula)
    # chi for real classes, over Q(i), against (-4)^g N(q) sum |w|^2
    rng = random.Random(7)
    cs = [Fr(3, 2), Fr(5, 3), Fr(7, 4)]
    signs = list(itertools.product((1, -1), repeat=3))
    okchi = True
    for trial in range(3):
        W = {}
        for e in signs:
            m = tuple(-x for x in e)
            if m in W:
                W[e] = QI(W[m].a, -W[m].b)
            else:
                W[e] = QI(rand_rat(rng), rand_rat(rng))
        v = {}
        for e, w in W.items():
            ee = one()
            for j in range(3):
                ee = wedge(ee, M3.exp_factor(j, Fr(e[j]) * cs[j]))
            v = add(v, {k: w * QI(c) for k, c in ee.items()})
        # per factor, theta = -2i theta_R and int exp(a theta_R) = a^2, so
        # int exp(a theta) = -4 a^2; e_eps^vee = e_{-eps}, and int e_{-eps} e_{eps'}
        # is nonzero only for eps' = -eps, where the exponent at place j is 2 c_j
        ch = M3.chi(v)
        f = Fr(1)
        for j in range(3):
            f *= -16 * cs[j] ** 2
        pred = QI(0)
        for e, w in W.items():
            pred = pred + w * W[tuple(-x for x in e)] * QI(f)
        okchi = okchi and ch.b == 0 and ch.a < 0 and ch == pred
    check("g = 3: chi(v,v) of a real secant class is real, negative, and equals "
          "sum_eps w_eps w_{-eps} prod_j (-16 c_j^2) = (-4)^3 N(q) sum |w|^2", okchi)
    # minimality thresholds
    print("   thresholds T = r^3 - 2 r^2 + 2 r^1 - 2 (minimality needs -chi >= T): %s"
          % sorted(set(thresholds.values())))
    check("g = 3: for every shape the remaining inequalities r^4 <= r^2, r^5 <= r^1, r^6 <= 1 hold "
          "(palindromy), so minimality is excluded only for |chi| < T, and N v escapes for N large",
          pal)
    print("\ntime %.1fs" % (time.time() - t0))
    print("%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)


if __name__ == "__main__":
    main()
