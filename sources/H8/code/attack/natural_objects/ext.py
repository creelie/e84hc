"""
ext.py  --  exterior algebra on H^1(A) for A = X x Xhat, dim X = n, by bitmasks.

Generators (bit positions):  x_1..x_{2n}  -> bits 0..2n-1,
                             xi_1..xi_{2n} -> bits 2n..4n-1.
Conventions are those of code/split_locus.py and of thm:splitclosed:
  beta    = sum_{j<=n} x_j ^ x_{n+j}
  betahat = sum_{j<=n} xi_j ^ xi_{n+j}
  ell     = sum_i x_i ^ xi_i
  B x_j = xi_{n+j},  B x_{n+j} = -xi_j   (B induced by beta)
  M acts on H^1(A) by  x -> -B x,  xi -> d B^{-1} xi.
An element is a dict {mask: coeff}; coefficients are ints or Fractions
(or anything supporting + and *).  Everything is exact.
"""
from fractions import Fraction as Fr


def popcount(x):
    return bin(x).count("1")


def merge_sign(m1, m2):
    """sign of sorting the generators of m1 followed by those of m2"""
    s = 0
    x = m2
    while x:
        low = x & -x
        s += popcount(m1 & ~((low << 1) - 1))
        x ^= low
    return -1 if s & 1 else 1


def wedge(u, v):
    out = {}
    for mu, cu in u.items():
        for mv, cv in v.items():
            if mu & mv:
                continue
            k = mu | mv
            c = cu * cv
            if merge_sign(mu, mv) < 0:
                c = -c
            out[k] = out.get(k, 0) + c
    return {k: c for k, c in out.items() if c != 0}


def add(u, v, a=1, b=1):
    out = {}
    for k, c in u.items():
        out[k] = out.get(k, 0) + a * c
    for k, c in v.items():
        out[k] = out.get(k, 0) + b * c
    return {k: c for k, c in out.items() if c != 0}


def scale(u, a):
    return {k: a * c for k, c in u.items() if a * c != 0}


def power(u, k):
    r = {0: 1}
    for _ in range(k):
        r = wedge(r, u)
    return r


def degree_part(u, deg):
    return {k: c for k, c in u.items() if popcount(k) == deg}


def exp_class(D, top):
    """e^D = sum_k D^k/k!, exact (Fractions); top = 4n."""
    out = {0: Fr(1)}
    p = {0: Fr(1)}
    k = 0
    while True:
        k += 1
        p = wedge(p, D)
        if not p:
            break
        out = add(out, scale(p, Fr(1, 1)), 1, Fr(1, _fact(k)))
    return out


def _fact(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


class Split:
    def __init__(self, n, d):
        self.n, self.d = n, d
        self.m = 2 * n
        self.N = 4 * n
        self.full = (1 << self.N) - 1

    def x(self, i):          # i = 1..2n
        return 1 << (i - 1)

    def xi(self, i):         # i = 1..2n
        return 1 << (self.m + i - 1)

    def gen(self, mask, c=1):
        return {mask: c}

    def beta(self):
        n = self.n
        out = {}
        for j in range(1, n + 1):
            out = add(out, wedge({self.x(j): 1}, {self.x(n + j): 1}))
        return out

    def betahat(self):
        n = self.n
        out = {}
        for j in range(1, n + 1):
            out = add(out, wedge({self.xi(j): 1}, {self.xi(n + j): 1}))
        return out

    def ell(self):
        out = {}
        for i in range(1, self.m + 1):
            out = add(out, wedge({self.x(i): 1}, {self.xi(i): 1}))
        return out

    def eta(self):
        return add(self.beta(), self.betahat(), self.d, 1)

    def gamma(self):
        return add(self.beta(), self.betahat(), self.d, -1)

    def integral(self, u):
        """int_A of the top component; int x_1..x_{2n} xi_1..xi_{2n} = 1,
        which gives int beta^n/n! = int betahat^n/n! = 1 on the factors."""
        return u.get(self.full, 0)

    def weil_pair(self):
        """W1 = Re (gamma - delta ell)^n, W2 = Im(...)/delta, integral
        polynomials in gamma, ell (thm:splitclosed), delta^2 = -d."""
        n, d = self.n, self.d
        g, l = self.gamma(), self.ell()
        W1, W2 = {}, {}
        # (gamma - delta ell)^n = sum_k C(n,k) gamma^{n-k} (-delta)^k ell^k
        for k in range(n + 1):
            t = wedge(power(g, n - k), power(l, k))
            c = _binom(n, k) * (-1) ** k
            # delta^k = (-d)^{k//2} * (1 or delta)
            c *= (-d) ** (k // 2)
            if k % 2 == 0:
                W1 = add(W1, t, 1, c)
            else:
                W2 = add(W2, t, 1, c)
        return W1, W2

    def subtorus(self, p, q):
        """class of B_(p,q) = image of x -> (p x, q phi(x)), gcd(p,q)=1,
        as the wedge of the integral basis of the conormal lattice
        { p xi_j - q x_{n+j},  p xi_{n+j} + q x_j }, sign fixed so that
        int [B] eta^n > 0."""
        n = self.n
        r = {0: 1}
        for j in range(1, n + 1):
            v1 = add({self.xi(j): 1}, {self.x(n + j): 1}, p, -q)
            v2 = add({self.xi(n + j): 1}, {self.x(j): 1}, p, q)
            r = wedge(r, v1)
            r = wedge(r, v2)
        s = self.integral(wedge(r, power(self.eta(), n)))
        assert s != 0
        if s < 0:
            r = scale(r, -1)
        return r

    def point(self):
        return {self.full: 1}

    def D(self, a, b, c):
        """a beta + b betahat + c ell"""
        return add(add(scale(self.beta(), a), scale(self.betahat(), b)),
                   scale(self.ell(), c))


def _binom(n, k):
    if k < 0 or k > n:
        return 0
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


# ----------------------------------------------------------- linear algebra
class Echelon:
    """incremental row echelon form over Q for sparse dict vectors"""

    def __init__(self):
        self.rows = []      # list of (pivot, vec) with vec[pivot] == 1
        self.piv = {}

    def reduce(self, v):
        v = {k: Fr(c) for k, c in v.items() if c != 0}
        for pk, row in self.rows:
            c = v.get(pk, 0)
            if c:
                for k, rc in row.items():
                    nv = v.get(k, 0) - c * rc
                    if nv:
                        v[k] = nv
                    else:
                        v.pop(k, None)
        return v

    def add(self, v):
        r = self.reduce(v)
        if not r:
            return False
        pk = min(r)
        c = r[pk]
        r = {k: x / c for k, x in r.items()}
        # keep fully reduced: eliminate pk from existing rows
        newrows = []
        for opk, row in self.rows:
            cc = row.get(pk, 0)
            if cc:
                row = {k: row.get(k, 0) - cc * r.get(k, 0)
                       for k in set(row) | set(r)}
                row = {k: x for k, x in row.items() if x != 0}
            newrows.append((opk, row))
        self.rows = newrows
        self.rows.append((pk, r))
        return True

    def rank(self):
        return len(self.rows)


def rank_of(vecs):
    E = Echelon()
    for v in vecs:
        E.add(v)
    return E.rank()
