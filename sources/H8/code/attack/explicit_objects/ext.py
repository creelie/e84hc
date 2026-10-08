"""
ext.py  --  exact exterior-algebra toolkit for track T3.

Elements of an exterior algebra on generators 0..N-1 are dicts
{bitmask: coefficient}; coefficients are Fractions or GQ (Gaussian rationals
a + b i with a, b Fractions).  Everything is exact.
"""
from fractions import Fraction as Fr
from math import factorial


class GQ:
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(self, o):
        o = _gq(o)
        return GQ(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __sub__(self, o):
        o = _gq(o)
        return GQ(self.a - o.a, self.b - o.b)

    def __rsub__(self, o):
        return _gq(o) - self

    def __neg__(self):
        return GQ(-self.a, -self.b)

    def __mul__(self, o):
        o = _gq(o)
        return GQ(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def conj(self):
        return GQ(self.a, -self.b)

    def inv(self):
        n = self.a * self.a + self.b * self.b
        return GQ(self.a / n, -self.b / n)

    def __truediv__(self, o):
        return self * _gq(o).inv()

    def __rtruediv__(self, o):
        return _gq(o) * self.inv()

    def __eq__(self, o):
        o = _gq(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def iszero(self):
        return self.a == 0 and self.b == 0

    def __repr__(self):
        if self.b == 0:
            return str(self.a)
        return "(%s%+si)" % (self.a, self.b) if self.a != 0 else "%si" % self.b


def _gq(x):
    return x if isinstance(x, GQ) else GQ(x)


def iszero(c):
    return c.iszero() if isinstance(c, GQ) else c == 0


def popcount(m):
    return bin(m).count("1")


def wsign(a, b):
    """sign of e_a ^ e_b -> e_{a|b} (a, b disjoint bitmasks)."""
    s = 0
    bb = b
    while bb:
        low = bb & -bb
        # number of bits of a above position of low
        s += popcount(a & ~((low << 1) - 1))
        bb ^= low
    return -1 if s & 1 else 1


def wedge(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if a & b:
                continue
            c = ca * cb
            if wsign(a, b) < 0:
                c = -c
            m = a | b
            out[m] = out.get(m, 0) + c
    return {k: c for k, c in out.items() if not iszero(c)}


def eadd(*us):
    out = {}
    for u in us:
        for k, c in u.items():
            out[k] = out.get(k, 0) + c
    return {k: c for k, c in out.items() if not iszero(c)}


def escale(c, u):
    return {k: c * v for k, v in u.items() if not iszero(c * v)}


def epow(u, k):
    r = {0: Fr(1)}
    for _ in range(k):
        r = wedge(r, u)
    return r


def eexp(u, maxdeg):
    """exp of an even element u with no degree-0 part."""
    out = {0: Fr(1)}
    term = {0: Fr(1)}
    for k in range(1, maxdeg + 1):
        term = escale(Fr(1, k), wedge(term, u))
        if not term:
            break
        out = eadd(out, term)
    return out


def to_gq(u):
    return {k: _gq(c) for k, c in u.items()}


def gen(i, c=1):
    return {1 << i: Fr(c) if not isinstance(c, GQ) else c}


def degree_part(u, k):
    return {m: c for m, c in u.items() if popcount(m) == k}


def substitute(u, images, N):
    """algebra map sending generator i to the degree-1 element images[i]
    (images: dict i -> element); generators not in images are fixed."""
    out = {}
    for m, c in u.items():
        piece = {0: c}
        for i in range(N):
            if m >> i & 1:
                g = images.get(i, {1 << i: Fr(1)})
                piece = wedge(piece, g)
        out = eadd(out, piece)
    return out


def interior(i, u):
    """contraction with the dual of generator i (a left derivation)."""
    out = {}
    for m, c in u.items():
        if m >> i & 1:
            s = popcount(m & ((1 << i) - 1))
            cc = -c if s & 1 else c
            out[m ^ (1 << i)] = out.get(m ^ (1 << i), 0) + cc
    return {k: c for k, c in out.items() if not iszero(c)}


def wedge_left(i, u):
    return wedge({1 << i: Fr(1)}, u)


# ------------------------------------------------------------ linear algebra
def rank_and_kernel(vectors, want_kernel=False):
    """vectors: list of dicts (sparse).  Returns rank (and a kernel basis of
    the map coefficients -> sum, as lists of coefficients)."""
    rows = []   # echelon rows: (pivot_key, dict, combo)
    pivots = {}
    kernel = []
    for idx, v in enumerate(vectors):
        v = dict(v)
        combo = {idx: Fr(1)} if want_kernel else None
        changed = True
        while v:
            # find a key of v that is a pivot
            hit = None
            for k in v:
                if k in pivots:
                    hit = k
                    break
            if hit is None:
                break
            pk, pv, pc = pivots[hit]
            f = v[hit] / pv[hit] if not isinstance(v[hit], GQ) else v[hit] / pv[hit]
            for k, c in pv.items():
                nv = v.get(k, 0) - f * c
                if iszero(nv):
                    v.pop(k, None)
                else:
                    v[k] = nv
            if want_kernel:
                for k, c in pc.items():
                    nc = combo.get(k, 0) - f * c
                    if iszero(nc):
                        combo.pop(k, None)
                    else:
                        combo[k] = nc
        if v:
            key = next(iter(v))
            pivots[key] = (key, v, combo)
        elif want_kernel:
            kernel.append(combo)
    if want_kernel:
        return len(pivots), kernel
    return len(pivots)


def solve_in_span(target, basis):
    """Return coefficients x with sum x_i basis_i = target, or None."""
    vecs = list(basis) + [target]
    r, ker = rank_and_kernel(vecs, want_kernel=True)
    last = len(basis)
    for combo in ker:
        if last in combo and not iszero(combo[last]):
            f = combo[last]
            x = [-(combo.get(i, 0)) / f for i in range(last)]
            return x
    return None
