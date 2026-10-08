"""
v4lib.py -- independent exterior-algebra toolkit for verifying track T4.
Written from scratch (does not import the track's ext.py / lg.py).

A = X x Xhat, dim X = n.  H^1(A,Q) basis: x_1..x_2n (bits 0..2n-1),
xi_1..xi_2n (bits 2n..4n-1).  Classes: dict {bitmask: coeff}.
Conventions (paper, thm:splitclosed proof): beta = sum_j x_j x_{n+j},
betahat = sum_j xi_j xi_{n+j}, ell = sum_i x_i xi_i, B x_j = xi_{n+j},
B x_{n+j} = -xi_j; M acts on H^1 by x -> -B x, xi -> d B^{-1} xi.
"""
from fractions import Fraction as Fr
from math import comb, factorial


def _sgn(a, b):
    # sign of putting sorted gens of a then b into sorted order
    s = 0
    bb = b
    while bb:
        j = (bb & -bb).bit_length() - 1
        s += bin(a >> (j + 1)).count("1")
        bb &= bb - 1
    return -1 if (s & 1) else 1


def wedge(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if a & b:
                continue
            c = ca * cb
            if _sgn(a, b) < 0:
                c = -c
            k = a | b
            out[k] = out.get(k, 0) + c
    return {k: c for k, c in out.items() if c != 0}


def lin(*pairs):
    out = {}
    for c, u in pairs:
        for k, x in u.items():
            out[k] = out.get(k, 0) + c * x
    return {k: x for k, x in out.items() if x != 0}


def deg(u, k):
    return {m: c for m, c in u.items() if bin(m).count("1") == k}


class Model:
    def __init__(self, n, d):
        self.n, self.d = n, d
        self.N = 4 * n
        self.top = (1 << self.N) - 1

    def x(self, i):
        return 1 << (i - 1)

    def xi(self, i):
        return 1 << (2 * self.n + i - 1)

    def form(self, xs, xis):
        """1-form sum xs[i] x_{i+1} + sum xis[i] xi_{i+1}"""
        out = {}
        for i, c in enumerate(xs):
            if c:
                out[self.x(i + 1)] = c
        for i, c in enumerate(xis):
            if c:
                out[self.xi(i + 1)] = c
        return out

    def beta(self):
        n = self.n
        return lin(*[(1, {self.x(j) | self.x(n + j): _sgn(self.x(j), self.x(n + j))})
                     for j in range(1, n + 1)])

    def betahat(self):
        n = self.n
        return lin(*[(1, {self.xi(j) | self.xi(n + j): _sgn(self.xi(j), self.xi(n + j))})
                     for j in range(1, n + 1)])

    def ell(self):
        return lin(*[(1, {self.x(i) | self.xi(i): _sgn(self.x(i), self.xi(i))})
                     for i in range(1, 2 * self.n + 1)])

    def eta(self):
        return lin((self.d, self.beta()), (1, self.betahat()))

    def integral(self, u):
        return u.get(self.top, 0)

    def expo(self, D):
        out = {0: Fr(1)}
        p = {0: Fr(1)}
        k = 0
        while True:
            k += 1
            p = wedge(p, D)
            if not p:
                break
            out = lin((1, out), (Fr(1, factorial(k)), p))
        return out

    # ---- B and the K-action on H^1
    def Bmap(self, i):
        """B applied to x_i as a 1-form (dict)"""
        n = self.n
        if i <= n:
            return {self.xi(n + i): 1}
        return {self.xi(i - n): -1}

    def subtorus_track(self, p, q):
        """track's convention: conormal {p xi_j - q x_{n+j}, p xi_{n+j} + q x_j}"""
        n = self.n
        r = {0: 1}
        for j in range(1, n + 1):
            r = wedge(r, lin((p, {self.xi(j): 1}), (-q, {self.x(n + j): 1})))
            r = wedge(r, lin((p, {self.xi(n + j): 1}), (q, {self.x(j): 1})))
        s = self.integral(wedge(r, pw(self.eta(), n)))
        assert s != 0
        return r if s > 0 else {k: -c for k, c in r.items()}


def pw(u, k):
    r = {0: 1}
    for _ in range(k):
        r = wedge(r, u)
    return r


# ---------------- Q(delta) arithmetic as pairs (a, b) = a + b delta, delta^2 = -d
class QD:
    __slots__ = ("a", "b", "d")

    def __init__(self, a, b, d):
        self.a, self.b, self.d = Fr(a), Fr(b), d

    def __add__(self, o):
        if not isinstance(o, QD):
            o = QD(o, 0, self.d)
        return QD(self.a + o.a, self.b + o.b, self.d)
    __radd__ = __add__

    def __neg__(self):
        return QD(-self.a, -self.b, self.d)

    def __sub__(self, o):
        return self + (-o if isinstance(o, QD) else QD(-o, 0, self.d))

    def __mul__(self, o):
        if not isinstance(o, QD):
            return QD(self.a * o, self.b * o, self.d)
        return QD(self.a * o.a - self.d * self.b * o.b, self.a * o.b + self.b * o.a, self.d)
    __rmul__ = __mul__

    def __eq__(self, o):
        if not isinstance(o, QD):
            return self.b == 0 and self.a == o
        return self.a == o.a and self.b == o.b

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        return hash((self.a, self.b))

    def __bool__(self):
        return self.a != 0 or self.b != 0

    def __repr__(self):
        return "(%s + %s delta)" % (self.a, self.b)


def re_im(u):
    re = {k: c.a for k, c in u.items() if c.a != 0}
    im = {k: c.b for k, c in u.items() if c.b != 0}
    return re, im


# ---------------- exact linear algebra over Q (sparse)
class RREF:
    def __init__(self):
        self.rows = []  # (pivot, dict) fully reduced, pivot coeff 1

    def reduce(self, v):
        v = {k: Fr(c) for k, c in v.items() if c != 0}
        for pk, row in self.rows:
            c = v.get(pk)
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
        new = []
        for opk, row in self.rows:
            cc = row.get(pk)
            if cc:
                row = dict(row)
                for k, x in r.items():
                    nv = row.get(k, 0) - cc * x
                    if nv:
                        row[k] = nv
                    else:
                        row.pop(k, None)
            new.append((opk, row))
        new.append((pk, r))
        self.rows = new
        return True

    def rank(self):
        return len(self.rows)


def rank(vecs):
    R = RREF()
    for v in vecs:
        R.add(v)
    return R.rank()


def nullspace(vecs):
    """kernel of the map Q^m -> Q^N, e_i -> vecs[i]; returns list of coefficient lists"""
    m = len(vecs)
    # augment with identity tags using large keys
    BIG = 1 << 40
    aug = []
    for i, v in enumerate(vecs):
        w = {k: Fr(c) for k, c in v.items()}
        w[BIG + i] = Fr(1)
        aug.append(w)
    # eliminate on original coordinates only
    rows = []
    kers = []
    for w in aug:
        w = dict(w)
        for pk, row in rows:
            c = w.get(pk)
            if c:
                for k, x in row.items():
                    nv = w.get(k, 0) - c * x
                    if nv:
                        w[k] = nv
                    else:
                        w.pop(k, None)
        orig = [k for k in w if k < BIG]
        if not orig:
            kers.append([w.get(BIG + i, Fr(0)) for i in range(m)])
            continue
        pk = min(orig)
        c = w[pk]
        w = {k: x / c for k, x in w.items()}
        rows.append((pk, w))
    return kers
