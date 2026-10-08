"""qk_ext.py -- exterior algebra toolkit for item (LIX) (quartic_kernels.py).

An element of an exterior algebra on generators g_0, g_1, ... is a dict
{bitmask: coefficient}; the monomial with bitmask m is the product of the g_i
with i in m, in increasing order of i.  Coefficients are Fractions or elements
of the class K below (the field Q(sqrt D, i)); everything is exact.

Linear algebra over Q uses python-flint (fmpq_mat); over K it uses the regular
representation of K on Q^4.
"""
from fractions import Fraction as Fr


def popc(m):
    return bin(m).count("1")


def msign(m1, m2):
    """sign of g_{m1} ^ g_{m2} = +- g_{m1 | m2} for disjoint m1, m2."""
    s = 0
    mm = m2
    while mm:
        j = (mm & -mm).bit_length() - 1
        s += popc(m1 >> (j + 1))
        mm &= mm - 1
    return -1 if s & 1 else 1


def iszero(c):
    return c == 0


def clean(u):
    return {k: v for k, v in u.items() if not iszero(v)}


def add(*us):
    out = {}
    for u in us:
        for k, v in u.items():
            out[k] = out.get(k, 0) + v
    return clean(out)


def sc(c, u):
    return clean({k: c * v for k, v in u.items()})


def sub(u, v):
    return add(u, sc(-1, v))


def wedge(u, v):
    out = {}
    for k1, a in u.items():
        for k2, b in v.items():
            if k1 & k2:
                continue
            k = k1 | k2
            p = a * b
            out[k] = out.get(k, 0) + (p if msign(k1, k2) > 0 else -p)
    return clean(out)


def gen(i, c=1):
    return {1 << i: c}


def one(c=1):
    return {0: c}


def expo(u):
    """exp of an even nilpotent element u with zero constant term."""
    out = one(Fr(1))
    term = one(Fr(1))
    k = 0
    while True:
        k += 1
        term = sc(Fr(1, k), wedge(term, u))
        if not term:
            break
        out = add(out, term)
    return out


def power(u, k):
    out = one(Fr(1))
    for _ in range(k):
        out = wedge(out, u)
    return out


def degpart(u, k):
    return {m: v for m, v in u.items() if popc(m) == k}


def degrees(u):
    return sorted(set(popc(m) for m in u))


def shift(u, s):
    return {m << s: c for m, c in u.items()}


def bits(m):
    out = []
    while m:
        j = (m & -m).bit_length() - 1
        out.append(j)
        m &= m - 1
    return out


def lin_subst(u, images):
    """algebra map sending generator i to images[i] (an element of degree 1)."""
    out = {}
    for m, c in u.items():
        t = one(1)
        for j in bits(m):
            t = wedge(t, images[j])
            if not t:
                break
        for k, v in t.items():
            out[k] = out.get(k, 0) + c * v
    return clean(out)


def derivation(u, lin):
    """the even derivation extending the linear map g_i -> lin[i] (degree 1)."""
    out = {}
    for m, c in u.items():
        idx = bits(m)
        for r, j in enumerate(idx):
            img = lin.get(j)
            if not img:
                continue
            left = one(1)
            for jj in idx[:r]:
                left = wedge(left, gen(jj))
            right = one(1)
            for jj in idx[r + 1:]:
                right = wedge(right, gen(jj))
            for k, v in wedge(wedge(left, img), right).items():
                out[k] = out.get(k, 0) + c * v
    return clean(out)


def interior(u, vec):
    """the odd derivation (contraction) with g_i -> vec[i] (scalars)."""
    out = {}
    for m, c in u.items():
        for r, j in enumerate(bits(m)):
            a = vec.get(j)
            if a is None or iszero(a):
                continue
            k = m & ~(1 << j)
            p = c * a
            out[k] = out.get(k, 0) + (-p if r & 1 else p)
    return clean(out)


# ------------------------------------------------------------------ Q(sqrt D, i)
class K:
    """a + b r + c i + e i r with r = sqrt(D), i = sqrt(-1)."""
    __slots__ = ("v", "D")

    def __init__(self, a=0, b=0, c=0, e=0, D=5):
        self.v = (Fr(a), Fr(b), Fr(c), Fr(e))
        self.D = D

    def lift(self, x):
        return x if isinstance(x, K) else K(x, 0, 0, 0, self.D)

    def __add__(self, o):
        o = self.lift(o)
        return K(*[x + y for x, y in zip(self.v, o.v)], D=self.D)
    __radd__ = __add__

    def __neg__(self):
        return K(*[-x for x in self.v], D=self.D)

    def __sub__(self, o):
        return self + (-self.lift(o))

    def __rsub__(self, o):
        return self.lift(o) - self

    def __mul__(self, o):
        o = self.lift(o)
        a, b, c, e = self.v
        A, B, C, E = o.v
        D = self.D
        return K(a * A + D * b * B - c * C - D * e * E,
                 a * B + b * A - c * E - e * C,
                 a * C + D * b * E + c * A + D * e * B,
                 a * E + b * C + c * B + e * A, D=D)
    __rmul__ = __mul__

    def __eq__(self, o):
        if isinstance(o, K):
            return self.v == o.v
        return self.v == (Fr(o), 0, 0, 0)

    def __hash__(self):
        return hash(self.v)

    def conj_r(self):
        """the automorphism sqrt D -> -sqrt D."""
        a, b, c, e = self.v
        return K(a, -b, c, -e, D=self.D)

    def inv(self):
        a, b, c, e = self.v
        D = self.D
        x = K(a, b, 0, 0, D)
        y = K(c, e, 0, 0, D)
        n = x * x + y * y
        n0, n1 = n.v[0], n.v[1]
        nn = n0 * n0 - D * n1 * n1
        return K(a, b, -c, -e, D) * K(n0 / nn, -n1 / nn, 0, 0, D)

    def regmat(self):
        """4 x 4 rational matrix of multiplication by self, basis (1, r, i, ir)."""
        cols = [(self * K(*u, D=self.D)).v for u in
                ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
        return [[cols[j][i] for j in range(4)] for i in range(4)]

    def __repr__(self):
        return "K%s" % (tuple(str(x) for x in self.v),)


def field(D):
    """constructor of elements of Q(sqrt D, i)."""
    def mk(a=0, b=0, c=0, e=0):
        return K(a, b, c, e, D=D)
    return mk


# ------------------------------------------------------------------ linear algebra
def _fq(x):
    import flint
    x = Fr(x)
    return flint.fmpq(x.numerator, x.denominator)


def rank_Q(rows, ncols):
    import flint
    if not rows:
        return 0
    return flint.fmpq_mat(len(rows), ncols,
                          [_fq(x) for r in rows for x in r]).rank()


def nullspace_Q(rows, ncols):
    """basis of {v : rows . v = 0} over Q (list of lists of Fractions)."""
    import flint
    if not rows:
        return [[Fr(int(i == j)) for i in range(ncols)] for j in range(ncols)]
    A = flint.fmpq_mat(len(rows), ncols, [_fq(x) for r in rows for x in r])
    R, rk = A.rref()
    piv = []
    r = 0
    for c in range(ncols):
        if r < rk and R[r, c] != 0:
            piv.append(c)
            r += 1
    out = []
    for f in [c for c in range(ncols) if c not in piv]:
        v = [Fr(0)] * ncols
        v[f] = Fr(1)
        for i, p in enumerate(piv):
            x = R[i, f]
            v[p] = -Fr(int(x.p), int(x.q))
        out.append(v)
    return out


def dict_rank_Q(vecs):
    keys = sorted(set(k for v in vecs for k in v))
    return rank_Q([[v.get(k, Fr(0)) for k in keys] for v in vecs], len(keys))


def span_basis(vecs):
    """a reduced basis (as dicts) of the Q-span of dict vectors."""
    import flint
    vecs = [v for v in vecs if v]
    if not vecs:
        return []
    keys = sorted(set(k for v in vecs for k in v))
    A = flint.fmpq_mat(len(vecs), len(keys),
                       [_fq(v.get(k, Fr(0))) for v in vecs for k in keys])
    R, rk = A.rref()
    out = []
    for i in range(rk):
        out.append({keys[j]: Fr(int(R[i, j].p), int(R[i, j].q))
                    for j in range(len(keys)) if R[i, j] != 0})
    return out


def intersection(U, V):
    """a basis of span(U) cap span(V) for lists of dict vectors over Q."""
    U = span_basis(U)
    V = span_basis(V)
    allv = U + [sc(-1, w) for w in V]
    keys = sorted(set(k for v in allv for k in v))
    ns = nullspace_Q([[v.get(k, Fr(0)) for v in allv] for k in keys], len(allv))
    out = [add(*[sc(n[i], U[i]) for i in range(len(U)) if n[i] != 0]) for n in ns]
    return span_basis([o for o in out if o])


def rank_K(vecs, mk):
    """rank over Q(sqrt D, i) of dict vectors with K coefficients (via Q^4)."""
    import flint
    keys = sorted(set(k for v in vecs for k in v))
    if not vecs or not keys:
        return 0
    kidx = {k: i for i, k in enumerate(keys)}
    A = flint.fmpq_mat(4 * len(vecs), 4 * len(keys))
    for i, v in enumerate(vecs):
        for k, c in v.items():
            R = mk(0).lift(c).regmat()
            j = kidx[k]
            for a in range(4):
                for b in range(4):
                    if R[a][b] != 0:
                        A[4 * i + b, 4 * j + a] = _fq(R[a][b])
    r = A.rank()
    assert r % 4 == 0, r
    return r // 4
