"""ea.py -- independent exact exterior algebra for verifying track T3.

Elements: dict {frozen sorted tuple of generator indices: coefficient}.
Coefficients: Fraction, or Qm (elements a + b*sqrt(-m) of Q(sqrt(-m)), m>0).
Deliberately written differently from the track's bitmask code.
"""
from fractions import Fraction as F


class Qm:
    """a + b*r with r^2 = -m."""
    __slots__ = ("a", "b", "m")

    def __init__(self, a, b=0, m=1):
        self.a = F(a); self.b = F(b); self.m = m

    def _c(self, o):
        if isinstance(o, Qm):
            assert o.m == self.m
            return o
        return Qm(o, 0, self.m)

    def __add__(self, o):
        o = self._c(o); return Qm(self.a + o.a, self.b + o.b, self.m)
    __radd__ = __add__

    def __sub__(self, o):
        o = self._c(o); return Qm(self.a - o.a, self.b - o.b, self.m)

    def __rsub__(self, o):
        return self._c(o) - self

    def __neg__(self):
        return Qm(-self.a, -self.b, self.m)

    def __mul__(self, o):
        o = self._c(o)
        return Qm(self.a * o.a - self.m * self.b * o.b, self.a * o.b + self.b * o.a, self.m)
    __rmul__ = __mul__

    def conj(self):
        return Qm(self.a, -self.b, self.m)

    def __truediv__(self, o):
        o = self._c(o)
        n = o.a * o.a + o.m * o.b * o.b
        return self * Qm(o.a / n, -o.b / n, self.m)

    def __rtruediv__(self, o):
        return self._c(o) / self

    def __eq__(self, o):
        if not isinstance(o, Qm):
            return self.b == 0 and self.a == o
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def iszero(self):
        return self.a == 0 and self.b == 0

    def __repr__(self):
        return "(%s + %s*sqrt(-%d))" % (self.a, self.b, self.m)


def isz(c):
    return c.iszero() if isinstance(c, Qm) else c == 0


def clean(u):
    return {k: c for k, c in u.items() if not isz(c)}


def merge_sign(a, b):
    """sign and sorted tuple of the wedge of monomials a, b (tuples), or (0,None)."""
    if set(a) & set(b):
        return 0, None
    # count inversions: pairs (x in a, y in b) with x > y
    inv = 0
    for x in a:
        for y in b:
            if x > y:
                inv += 1
    return (-1 if inv % 2 else 1), tuple(sorted(a + b))


def mul(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            s, m = merge_sign(a, b)
            if s == 0:
                continue
            c = ca * cb
            if s < 0:
                c = -c
            out[m] = out.get(m, 0) + c
    return clean(out)


def add(*us):
    out = {}
    for u in us:
        for k, c in u.items():
            out[k] = out.get(k, 0) + c
    return clean(out)


def sc(c, u):
    return clean({k: c * x for k, x in u.items()})


def one():
    return {(): F(1)}


def g(i, c=F(1)):
    return {(i,): c}


def power(u, k):
    r = one()
    for _ in range(k):
        r = mul(r, u)
    return r


def expo(u, maxdeg=64):
    out = one(); t = one()
    for k in range(1, maxdeg + 1):
        t = sc(F(1, k), mul(t, u))
        if not t:
            break
        out = add(out, t)
    return out


def deg(u, k):
    return {m: c for m, c in u.items() if len(m) == k}


def contract(i, u):
    """left contraction with the dual of generator i."""
    out = {}
    for m, c in u.items():
        if i in m:
            p = m.index(i)
            cc = -c if p % 2 else c
            nm = m[:p] + m[p + 1:]
            out[nm] = out.get(nm, 0) + cc
    return clean(out)


def linsub(u, images):
    """algebra map: generator i -> images[i] (degree-1 element); others fixed."""
    out = {}
    for m, c in u.items():
        piece = {(): c}
        for i in m:
            piece = mul(piece, images.get(i, g(i)))
        for k, x in piece.items():
            out[k] = out.get(k, 0) + x
    return clean(out)


# ---------------- linear algebra (dense-ish Gaussian elimination on dict rows)
def rank(vectors):
    piv = []   # list of (key, row)
    pivkeys = {}
    r = 0
    for v in vectors:
        v = dict(v)
        for key, row in piv:
            if key in v and not isz(v[key]):
                f = v[key] / row[key]
                for k, c in row.items():
                    nv = v.get(k, 0) - f * c
                    if isz(nv):
                        v.pop(k, None)
                    else:
                        v[k] = nv
        v = clean(v)
        if v:
            key = min(v.keys(), key=lambda t: (len(t), t) if isinstance(t, tuple) else (0, t))
            # eliminate key from existing pivot rows not needed (we do sequential elimination)
            piv.append((key, v))
            r += 1
    return r


def solve(target, basis):
    """coefficients x with sum x_i basis_i == target, or None.  Exact."""
    # build augmented system: unknowns x_i; equations per key
    keys = set()
    for b in basis:
        keys |= set(b.keys())
    keys |= set(target.keys())
    keys = sorted(keys, key=lambda t: (len(t), t) if isinstance(t, tuple) else (0, t))
    n = len(basis)
    rows = []
    for k in keys:
        row = [b.get(k, 0) for b in basis] + [target.get(k, 0)]
        if any(not isz(c) for c in row):
            rows.append(row)
    # gaussian elimination
    R = [list(r) for r in rows]
    pivcols = []
    ri = 0
    for col in range(n):
        p = None
        for i in range(ri, len(R)):
            if not isz(R[i][col]):
                p = i; break
        if p is None:
            continue
        R[ri], R[p] = R[p], R[ri]
        pv = R[ri][col]
        R[ri] = [c / pv for c in R[ri]]
        for i in range(len(R)):
            if i != ri and not isz(R[i][col]):
                f = R[i][col]
                R[i] = [a - f * b for a, b in zip(R[i], R[ri])]
        pivcols.append(col)
        ri += 1
    for i in range(ri, len(R)):
        if not isz(R[i][n]):
            return None
    x = [F(0)] * n
    for i, col in enumerate(pivcols):
        x[col] = R[i][n]
    return x
