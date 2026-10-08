"""
t1lib.py -- exact helpers for track T1 (Weil classes of a quartic CM field, n = 2).

A quartic CM field is F = F0(r), F0 = Q(s), s^2 = t (t > 1 squarefree),
r^2 = -D with D = a + b s totally positive.  Elements of F are 4-tuples
(p0, q0, p1, q1) of Fractions meaning (p0 + q0 s) + (p1 + q1 s) r, i.e.
coordinates in the Q-basis [1, s, r, s r].

Everything is exact (fractions.Fraction, python-flint fmpq_mat).  Where a
computation is done modulo a prime it is only ever used for an UPPER bound
on a dimension of invariants (kernel mod p contains the reduction of the
kernel over Q, and a kernel over Q of a subset of the equations contains the
kernel of all of them); the matching LOWER bound is always an explicit
exact family of invariants.
"""
from fractions import Fraction as Fr
import itertools
import flint

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in str(detail).split("\n"):
            print("         " + line)


def summary():
    print("\n%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    for f in FAIL:
        print("   FAILED:", f)
    return len(FAIL) == 0


# ----------------------------------------------------------------- field
class QuarticCM:
    def __init__(self, t, a, b, name):
        self.t, self.a, self.b = Fr(t), Fr(a), Fr(b)
        self.name = name
        assert self.a > 0 and self.a ** 2 - self.t * self.b ** 2 > 0, "D not totally positive"
        self.zero = (Fr(0),) * 4
        self.one = (Fr(1), Fr(0), Fr(0), Fr(0))
        self.s = (Fr(0), Fr(1), Fr(0), Fr(0))
        self.r = (Fr(0), Fr(0), Fr(1), Fr(0))
        self.basis = [self.one, self.s, self.r, self.mul(self.s, self.r)]
        G = [[self.tr(self.mul(x, y)) for y in self.basis] for x in self.basis]
        Gi = flint.fmpq_mat([[flint.fmpq(x.numerator, x.denominator) for x in row] for row in G]).inv()
        # dual basis w*_k = sum_j Gi[k][j] basis_j  (Tr(w_i w*_k) = delta_ik)
        self.dual = []
        for k in range(4):
            e = self.zero
            for j in range(4):
                c = Fr(int(Gi[k, j].p), int(Gi[k, j].q))
                e = self.add(e, self.scal(c, self.basis[j]))
            self.dual.append(e)
        for i in range(4):
            for k in range(4):
                assert self.tr(self.mul(self.basis[i], self.dual[k])) == (1 if i == k else 0)

    # F0 arithmetic on pairs
    def m0(self, x, y):
        return (x[0] * y[0] + self.t * x[1] * y[1], x[0] * y[1] + x[1] * y[0])

    def D(self):
        return (self.a, self.b)

    def add(self, x, y):
        return tuple(u + v for u, v in zip(x, y))

    def sub(self, x, y):
        return tuple(u - v for u, v in zip(x, y))

    def neg(self, x):
        return tuple(-u for u in x)

    def scal(self, c, x):
        return tuple(Fr(c) * u for u in x)

    def mul(self, x, y):
        A0, A1 = (x[0], x[1]), (x[2], x[3])
        B0, B1 = (y[0], y[1]), (y[2], y[3])
        c0 = self.m0(A0, B0)
        dd = self.m0(self.D(), self.m0(A1, B1))
        c0 = (c0[0] - dd[0], c0[1] - dd[1])
        c1a, c1b = self.m0(A0, B1), self.m0(A1, B0)
        return (c0[0], c0[1], c1a[0] + c1b[0], c1a[1] + c1b[1])

    def conj(self, x):
        return (x[0], x[1], -x[2], -x[3])

    def tr(self, x):  # Tr_{F/Q}
        return 4 * x[0]

    def f0(self, p, q=0):
        return (Fr(p), Fr(q), Fr(0), Fr(0))

    def inv(self, x):
        A0, A1 = (x[0], x[1]), (x[2], x[3])
        N = self.m0(A0, A0)
        dd = self.m0(self.D(), self.m0(A1, A1))
        N = (N[0] + dd[0], N[1] + dd[1])  # N_{F/F0} = A0^2 + D A1^2
        den = N[0] ** 2 - self.t * N[1] ** 2
        Ni = (N[0] / den, -N[1] / den)
        c = (A0[0], A0[1], -A1[0], -A1[1])
        return self.mul(c, (Ni[0], Ni[1], Fr(0), Fr(0)))

    def is_zero(self, x):
        return all(u == 0 for u in x)

    def in_F0(self, x):
        return x[2] == 0 and x[3] == 0

    def totally_positive_F0(self, x):
        p, q = x[0], x[1]
        return self.in_F0(x) and p > 0 and p * p - self.t * q * q > 0

    def mulmat(self, c):
        """4x4 rational matrix of multiplication by c on the basis [1,s,r,sr]"""
        cols = [self.mul(c, e) for e in self.basis]
        return [[cols[j][i] for j in range(4)] for i in range(4)]


# ------------------------------------------------------------- V = F^n
def vec_to_Q(Fd, v):
    """F^n -> Q^{4n}, index 4*i + k for coordinate i, basis element k"""
    out = []
    for x in v:
        out.extend(x)
    return out


def fmat_to_Q(Fd, X):
    """F-linear map (n x n F-matrix, acting on columns) -> 4n x 4n rational matrix"""
    n = len(X)
    N = 4 * n
    M = [[Fr(0)] * N for _ in range(N)]
    for j in range(n):
        for k in range(4):
            col = []
            for i in range(n):
                col.append(Fd.mul(X[i][j], Fd.basis[k]))
            colQ = vec_to_Q(Fd, col)
            c = 4 * j + k
            for rI in range(N):
                M[rI][c] = colQ[rI]
    return M


# ------------------------------------------------------- exterior algebra
def sort_sign(idx):
    idx = list(idx)
    if len(set(idx)) < len(idx):
        return 0, None
    sign = 1
    for i in range(len(idx)):
        for j in range(len(idx) - 1 - i):
            if idx[j] > idx[j + 1]:
                idx[j], idx[j + 1] = idx[j + 1], idx[j]
                sign = -sign
    return sign, tuple(idx)


def wedge(u, v):
    out = {}
    for I, a in u.items():
        for J, b in v.items():
            sg, K = sort_sign(I + J)
            if sg:
                out[K] = out.get(K, Fr(0)) + sg * a * b
    return {K: c for K, c in out.items() if c != 0}


def vec_form(vQ):
    return {(i,): Fr(c) for i, c in enumerate(vQ) if c != 0}


def wedge_vectors(vs):
    out = {(): Fr(1)}
    for v in vs:
        out = wedge(out, vec_form(v))
    return out


def addf(u, v, c=1):
    out = dict(u)
    for K, x in v.items():
        out[K] = out.get(K, Fr(0)) + c * x
    return {K: x for K, x in out.items() if x != 0}


def scalf(c, u):
    return {K: c * x for K, x in u.items() if c * x != 0}


def derivation(M, form):
    """action of the linear map M (rational matrix, M[row][col]) as a derivation"""
    out = {}
    N = len(M)
    for I, c in form.items():
        for pos, i in enumerate(I):
            for row in range(N):
                m = M[row][i]
                if m == 0:
                    continue
                J = I[:pos] + (row,) + I[pos + 1:]
                sg, K = sort_sign(J)
                if sg:
                    out[K] = out.get(K, Fr(0)) + sg * c * m
    return {K: x for K, x in out.items() if x != 0}


def rank_forms(forms):
    keys = sorted({K for f in forms for K in f})
    if not keys or not forms:
        return 0
    pos = {K: i for i, K in enumerate(keys)}
    M = flint.fmpq_mat(len(forms), len(keys))
    for r, f in enumerate(forms):
        for K, c in f.items():
            M[r, pos[K]] = flint.fmpq(c.numerator, c.denominator)
    return M.rank()


def basis_k(N, k):
    return list(itertools.combinations(range(N), k))


def action_matrix_modp(M, N, k, p, basis=None):
    """matrix of the derivation action of M on wedge^k Q^N, reduced mod p (rows = image coords)"""
    if basis is None:
        basis = basis_k(N, k)
    pos = {K: i for i, K in enumerate(basis)}
    A = flint.nmod_mat(len(basis), len(basis), p)
    for col, I in enumerate(basis):
        img = derivation(M, {I: Fr(1)})
        for K, c in img.items():
            A[pos[K], col] = (c.numerator * pow(c.denominator, -1, p)) % p
    return A, basis


def nullity_modp_stack(mats, p):
    """nullity mod p of the vertical stack of nmod_mats with equal column count"""
    ncols = mats[0].ncols()
    nrows = sum(m.nrows() for m in mats)
    S = flint.nmod_mat(nrows, ncols, p)
    r0 = 0
    for m in mats:
        for i in range(m.nrows()):
            for j in range(ncols):
                v = int(m[i, j])
                if v:
                    S[r0 + i, j] = v
        r0 += m.nrows()
    return ncols - S.rank()


def nullspace_q(rows, ncols):
    """basis of the right kernel of a rational matrix given as list of rows (Fractions)"""
    M = flint.fmpq_mat(len(rows), ncols)
    for i, r in enumerate(rows):
        for j, c in enumerate(r):
            if c != 0:
                M[i, j] = flint.fmpq(c.numerator, c.denominator)
    R, rk = M.rref()
    piv = []
    row = 0
    for j in range(ncols):
        if row < rk and R[row, j] != 0:
            piv.append(j)
            row += 1
    free = [j for j in range(ncols) if j not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * ncols
        v[f] = Fr(1)
        for i, pj in enumerate(piv):
            c = R[i, f]
            v[pj] = -Fr(int(c.p), int(c.q))
        basis.append(v)
    return basis


# ------------------------------------------------ balanced (F-linear) lifts
def balanced_lift(Fd, vecs):
    """F-balanced lift of v_1 ^_F ... ^_F v_k into wedge^k_Q V:
    sum over k_1..k_{m-1} of (w_{k1} v1) ^ (w*_{k1} w_{k2} v2) ^ ... ^ (w*_{k_{m-1}} v_m).
    Its complexification is sum_sigma (v1)_sigma ^ ... ^ (vk)_sigma."""
    m = len(vecs)
    if m == 1:
        return vec_form(vec_to_Q(Fd, vecs[0]))
    total = {}
    for ks in itertools.product(range(4), repeat=m - 1):
        coeffs = []
        for pos in range(m):
            c = Fd.one
            if pos > 0:
                c = Fd.mul(c, Fd.dual[ks[pos - 1]])
            if pos < m - 1:
                c = Fd.mul(c, Fd.basis[ks[pos]])
            coeffs.append(c)
        vs = [vec_to_Q(Fd, [Fd.mul(coeffs[pos], x) for x in vecs[pos]]) for pos in range(m)]
        total = addf(total, wedge_vectors(vs))
    return total


def std_vec(Fd, n, i, c=None):
    v = [Fd.zero] * n
    v[i] = Fd.one if c is None else c
    return v


def weil_lift(Fd, n, c):
    """Tr-type Weil class of V=F^n (n = 2*nn): balanced lift of c e_0 ^_F e_1 ^_F ... ^_F e_{n-1}"""
    vecs = [std_vec(Fd, n, 0, c)] + [std_vec(Fd, n, i) for i in range(1, n)]
    return balanced_lift(Fd, vecs)


def stacked_action_modp(Ms, N, k, p):
    """vertical stack of the derivation actions of the matrices Ms on wedge^k Q^N, mod p"""
    basis = basis_k(N, k)
    pos = {K: i for i, K in enumerate(basis)}
    nb = len(basis)
    S = flint.nmod_mat(nb * len(Ms), nb, p)
    for t_, M in enumerate(Ms):
        off = t_ * nb
        for col, I in enumerate(basis):
            img = derivation(M, {I: Fr(1)})
            for K, c in img.items():
                S[off + pos[K], col] = (c.numerator * pow(c.denominator, -1, p)) % p
    return S


def nullity_modp(Ms, N, k, p=1000003):
    S = stacked_action_modp(Ms, N, k, p)
    return S.ncols() - S.rank()
