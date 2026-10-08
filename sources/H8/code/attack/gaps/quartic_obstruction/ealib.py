"""ealib.py -- exact exterior algebra on bitmask monomials (track A1).

An element is a dict {mask: coeff}; bit i of mask <-> generator g_i, and a
monomial is g_{i1} ^ ... ^ g_{ik} with i1 < ... < ik.  Coefficients are
fractions.Fraction (or any field type supporting + - * / and == 0).

Linear algebra: exact ranks over Q with python-flint (fmpq_mat), ranks over
Q(i) by realification, ranks mod p with nmod_mat (used only as LOWER bounds
for ranks over number fields, never as upper bounds).
"""
from fractions import Fraction as Fr
import flint

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name), flush=True)
    if detail:
        for line in str(detail).split("\n"):
            print("         " + line, flush=True)


def summary():
    print("\n%d checks passed, %d failed" % (len(PASS), len(FAIL)), flush=True)
    for f in FAIL:
        print("   FAILED:", f)
    return len(FAIL) == 0


def pc(m):
    return bin(m).count("1")


def bits(m):
    out = []
    i = 0
    while m:
        if m & 1:
            out.append(i)
        m >>= 1
        i += 1
    return out


def wsign(a, b):
    """sign of g_A ^ g_B = sign * g_{A|B} (A, B disjoint masks)."""
    s = 0
    bb = b
    j = 0
    while bb:
        if bb & 1:
            s += pc(a >> (j + 1))
        bb >>= 1
        j += 1
    return -1 if s & 1 else 1


def clean(u):
    return {k: c for k, c in u.items() if c != 0}


def add(*us):
    out = {}
    for u in us:
        for k, c in u.items():
            out[k] = out.get(k, 0) + c
    return clean(out)


def sc(c, u):
    return clean({k: c * x for k, x in u.items()})


def sub(u, v):
    return add(u, sc(-1, v))


def one():
    return {0: Fr(1)}


def gen(i, c=Fr(1)):
    return {1 << i: c}


def wedge(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if a & b:
                continue
            s = wsign(a, b)
            m = a | b
            out[m] = out.get(m, 0) + (ca * cb if s > 0 else -(ca * cb))
    return clean(out)


def power(u, k):
    r = one()
    for _ in range(k):
        r = wedge(r, u)
    return r


def expo(u, maxdeg=64):
    out = one()
    t = one()
    for k in range(1, maxdeg + 1):
        t = sc(Fr(1, k), wedge(t, u))
        if not t:
            break
        out = add(out, t)
    return out


def deg(u, k):
    return {m: c for m, c in u.items() if pc(m) == k}


def degrees(u):
    return sorted(set(pc(m) for m in u))


def contract(i, u):
    """iota_i: left contraction with the dual of generator i (odd derivation)."""
    out = {}
    bi = 1 << i
    for m, c in u.items():
        if m & bi:
            s = pc(m & (bi - 1))
            out[m ^ bi] = out.get(m ^ bi, 0) + (-c if s & 1 else c)
    return clean(out)


def lwedge(i, u, c=Fr(1)):
    """left multiplication by c*g_i."""
    out = {}
    bi = 1 << i
    for m, x in u.items():
        if m & bi:
            continue
        s = pc(m & (bi - 1))
        out[m | bi] = out.get(m | bi, 0) + (-(c * x) if s & 1 else c * x)
    return clean(out)


def derivation(A, u):
    """even derivation induced by the endomorphism A of the degree-one part.
    A: dict col -> list of (row, coeff), meaning A(g_col) = sum coeff * g_row."""
    out = {}
    for m, c in u.items():
        mm = m
        i = 0
        while mm:
            if mm & 1:
                rest = m ^ (1 << i)
                p = pc(rest & ((1 << i) - 1))
                for (j, a) in A.get(i, ()):
                    if rest & (1 << j):
                        continue
                    q = pc(rest & ((1 << j) - 1))
                    s = -1 if (p + q) & 1 else 1
                    key = rest | (1 << j)
                    out[key] = out.get(key, 0) + (s * a * c)
            mm >>= 1
            i += 1
    return clean(out)


def substitute(u, images):
    """algebra homomorphism g_i -> images[i] (degree-one elements); u small."""
    out = {}
    cache = {}
    for m, c in u.items():
        if m in cache:
            piece = cache[m]
        else:
            piece = one()
            for i in bits(m):
                piece = wedge(piece, images[i])
            cache[m] = piece
        for k, x in piece.items():
            out[k] = out.get(k, 0) + c * x
    return clean(out)


def mat_to_A(M):
    """square matrix (list of rows, M[row][col]) -> column dict for derivation."""
    n = len(M)
    A = {}
    for col in range(n):
        lst = [(row, Fr(M[row][col])) for row in range(n) if M[row][col] != 0]
        if lst:
            A[col] = lst
    return A


# ---------------------------------------------------------------- ranks
def _fq(x):
    x = Fr(x)
    return flint.fmpq(x.numerator, x.denominator)


def rank_Q(vectors):
    keys = sorted(set(k for v in vectors for k in v))
    if not keys or not vectors:
        return 0
    idx = {k: i for i, k in enumerate(keys)}
    M = flint.fmpq_mat(len(vectors), len(keys))
    for r, v in enumerate(vectors):
        for k, c in v.items():
            M[r, idx[k]] = _fq(c)
    return M.rank()


def nullspace_Q(vectors):
    """rational kernel of the map coefficient-vector -> sum c_i vectors_i.
    Returns list of coefficient lists (Fractions)."""
    keys = sorted(set(k for v in vectors for k in v))
    n = len(vectors)
    if not keys:
        return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    idx = {k: i for i, k in enumerate(keys)}
    M = flint.fmpq_mat(len(keys), n)
    for c_, v in enumerate(vectors):
        for k, c in v.items():
            M[idx[k], c_] = _fq(c)
    return fmpq_nullspace(M)


def fmpq_nullspace(M):
    """basis (list of lists of Fractions) of the right kernel of an fmpq_mat, via rref."""
    R, rk = M.rref()
    nr, nc = M.nrows(), M.ncols()
    piv = []
    r = 0
    for c in range(nc):
        if r < rk and R[r, c] != 0:
            piv.append(c)
            r += 1
    free = [c for c in range(nc) if c not in set(piv)]
    out = []
    for f in free:
        v = [Fr(0)] * nc
        v[f] = Fr(1)
        for i, pcol in enumerate(piv):
            x = R[i, f]
            v[pcol] = -Fr(int(x.p), int(x.q))
        out.append(v)
    return out


class QI:
    """a + b i over Q."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def _c(self, o):
        return o if isinstance(o, QI) else QI(o, 0)

    def __add__(self, o):
        o = self._c(o)
        return QI(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __sub__(self, o):
        o = self._c(o)
        return QI(self.a - o.a, self.b - o.b)

    def __rsub__(self, o):
        return self._c(o) - self

    def __neg__(self):
        return QI(-self.a, -self.b)

    def __mul__(self, o):
        o = self._c(o)
        return QI(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._c(o)
        n = o.a * o.a + o.b * o.b
        return self * QI(o.a / n, -o.b / n)

    def __eq__(self, o):
        if isinstance(o, QI):
            return self.a == o.a and self.b == o.b
        return self.b == 0 and self.a == o

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        return hash((self.a, self.b))

    def __repr__(self):
        return "(%s%+si)" % (self.a, self.b)


def rank_QI(vectors):
    """exact rank over Q(i) of vectors with QI (or Fraction) coefficients:
    rank over C = (rank over R of the realification) / 2."""
    keys = sorted(set(k for v in vectors for k in v))
    if not keys or not vectors:
        return 0
    idx = {k: i for i, k in enumerate(keys)}
    n = len(keys)
    M = flint.fmpq_mat(2 * len(vectors), 2 * n)
    for r, v in enumerate(vectors):
        for k, c in v.items():
            c = c if isinstance(c, QI) else QI(c)
            j = idx[k]
            # row (a+bi) acting: real part row r, imag part row r+len
            M[2 * r, j] = _fq(c.a)
            M[2 * r, n + j] = _fq(c.b)
            M[2 * r + 1, j] = _fq(-c.b)
            M[2 * r + 1, n + j] = _fq(c.a)
    rk = M.rank()
    assert rk % 2 == 0
    return rk // 2


def rank_modp(vectors, p, conv):
    """rank mod p; conv maps a coefficient to an int mod p."""
    keys = sorted(set(k for v in vectors for k in v))
    if not keys or not vectors:
        return 0
    idx = {k: i for i, k in enumerate(keys)}
    M = flint.nmod_mat(len(vectors), len(keys), p)
    for r, v in enumerate(vectors):
        for k, c in v.items():
            M[r, idx[k]] = conv(c) % p
    return M.rank()
