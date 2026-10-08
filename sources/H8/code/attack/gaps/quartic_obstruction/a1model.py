"""a1model.py -- exact model of a principally polarised abelian fourfold X with
real multiplication by a real quadratic field F0 (track A1).

Model: X = S (x) O_0 with S a principally polarised abelian surface and O_0 = Z^2
with the unimodular form I_2, on which O_0 acts through a symmetric integral
2x2 matrix Rm with irrational eigenvalues (for F0 = Q(sqrt5): Rm = [[0,1],[1,1]]).
H^1(X,Q) = H^1(S,Q) (x) Q^2 has generators x_j, j = 4h + 2k + a, for
h in {0 (e), 1 (f)}, k in {0,1} (index in Q^2), a in {0,1} (index in S), so that
theta = sum_{j<4} x_j x_{4+j} is the principal polarisation, and f in F0 acts on
the index k.  (Every principally polarised O_0-lattice for Q(sqrt5) is of this
form; the rational cohomology with its F0-action and polarisation is the same
for every principally polarised abelian fourfold with RM by F0.)

Complex structure (used only for Hochschild ranks, which are constant on the
family): z_j = x_j + i x_{4+j}, j < 4.

The F0-Hodge ring R (the Hodge classes of a very general member) is spanned by
theta_1^a theta_2^b, 0 <= a, b <= 2, where theta_f = tau_1(f) theta_1 + tau_2(f) theta_2.
V-coordinates: v = sum V[a][b] theta_1^a theta_2^b / (a! b!).
"""
from fractions import Fraction as Fr
from math import factorial
import itertools
from ealib import *


class QS:
    """a + b sqrt(t) with rational a, b (t > 0 not a square)."""
    __slots__ = ("a", "b", "t")

    def __init__(self, a, b=0, t=5):
        self.a = Fr(a)
        self.b = Fr(b)
        self.t = t

    def _c(self, o):
        return o if isinstance(o, QS) else QS(o, 0, self.t)

    def __add__(self, o):
        o = self._c(o)
        return QS(self.a + o.a, self.b + o.b, self.t)
    __radd__ = __add__

    def __sub__(self, o):
        o = self._c(o)
        return QS(self.a - o.a, self.b - o.b, self.t)

    def __rsub__(self, o):
        return self._c(o) - self

    def __neg__(self):
        return QS(-self.a, -self.b, self.t)

    def __mul__(self, o):
        o = self._c(o)
        return QS(self.a * o.a + self.t * self.b * o.b, self.a * o.b + self.b * o.a, self.t)
    __rmul__ = __mul__

    def conj(self):
        return QS(self.a, -self.b, self.t)

    def norm(self):
        return self.a * self.a - self.t * self.b * self.b

    def __truediv__(self, o):
        o = self._c(o)
        n = o.norm()
        return self * QS(o.a / n, -o.b / n, self.t)

    def __rtruediv__(self, o):
        return self._c(o) / self

    def __eq__(self, o):
        if isinstance(o, QS):
            return self.a == o.a and self.b == o.b
        return self.b == 0 and self.a == o

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        return hash((self.a, self.b))

    def val(self):
        return float(self.a) + float(self.b) * self.t ** 0.5

    def __repr__(self):
        if self.b == 0:
            return str(self.a)
        return "(%s%+s*sqrt%d)" % (self.a, self.b, self.t)


def idx(h, k, a):
    return 4 * h + 2 * k + a


class RMModel:
    def __init__(self, Rm=((0, 1), (1, 1))):
        self.Rm = [[Fr(x) for x in row] for row in Rm]
        tr = self.Rm[0][0] + self.Rm[1][1]
        det = self.Rm[0][0] * self.Rm[1][1] - self.Rm[0][1] * self.Rm[1][0]
        disc = tr * tr - 4 * det
        assert disc > 0 and disc.denominator == 1
        self.tr, self.det, self.disc = tr, det, int(disc)
        # eigenvalues r1 > r2 of R in Q(sqrt disc)
        self.r1 = QS(tr / 2, Fr(1, 2), self.disc)
        self.r2 = QS(tr / 2, Fr(-1, 2), self.disc)
        self.N = 8
        self.theta = self.theta_f((1, 0))
        self.thetaR = self.theta_f((0, 1))
        # theta_1, theta_2 over Q(sqrt disc)
        d12 = self.r1 - self.r2
        self.th1 = add(sc(1 / d12, self.qs(self.thetaR)), sc(-self.r2 / d12, self.qs(self.theta)))
        self.th2 = add(sc(-1 / d12, self.qs(self.thetaR)), sc(self.r1 / d12, self.qs(self.theta)))

    # ---------------------------------------------------------------- F0
    def QSel(self, f):
        """element c0 + c1 R of F0 as its tau_1-value in Q(sqrt disc)."""
        c0, c1 = Fr(f[0]), Fr(f[1])
        return QS(c0, 0, self.disc) + self.r1 * c1

    def tau(self, f):
        c0, c1 = Fr(f[0]), Fr(f[1])
        return (QS(c0, 0, self.disc) + self.r1 * c1, QS(c0, 0, self.disc) + self.r2 * c1)

    def qs(self, u):
        return {k: (c if isinstance(c, QS) else QS(c, 0, self.disc)) for k, c in u.items()}

    def act_R(self):
        """matrix of R on H^1(X,Q) (the x generators), as column dict."""
        A = {}
        for h in range(2):
            for k in range(2):
                for a in range(2):
                    col = idx(h, k, a)
                    A[col] = [(idx(h, l, a), self.Rm[l][k]) for l in range(2) if self.Rm[l][k] != 0]
        return A

    def fvec(self, f, j):
        """f(x_j) as a degree-one element."""
        c0, c1 = Fr(f[0]), Fr(f[1])
        out = {1 << j: c0} if c0 != 0 else {}
        for (row, c) in self.act_R().get(j, ()):
            out = add(out, {1 << row: c1 * c})
        return out

    def theta_f(self, f):
        out = {}
        for j in range(4):
            out = add(out, wedge(self.fvec(f, j), gen(4 + j)))
        return out

    # --------------------------------------------------- V-coordinates of R
    def Rbasis_QS(self):
        """theta_1^a theta_2^b /(a! b!), 0<=a,b<=2, as classes over Q(sqrt disc)."""
        out = {}
        p1 = [self.qs(one()), self.th1, sc(Fr(1, 2), wedge(self.th1, self.th1))]
        p2 = [self.qs(one()), self.th2, sc(Fr(1, 2), wedge(self.th2, self.th2))]
        for a in range(3):
            for b in range(3):
                out[(a, b)] = wedge(p1[a], p2[b])
        return out

    def from_V(self, V):
        """class from a 3x3 matrix of QS (or rationals)."""
        B = self.Rbasis_QS()
        out = {}
        for a in range(3):
            for b in range(3):
                c = V[a][b]
                if c != 0:
                    out = add(out, sc(c if isinstance(c, QS) else QS(c, 0, self.disc), B[(a, b)]))
        return out

    def to_V(self, u):
        """V-matrix of a class in R (over Q(sqrt disc)); raises if not in R.
        Uses the fact that the nine basis classes have disjoint 'signatures':
        solve by extracting coefficients against a dual set of monomials."""
        B = self.Rbasis_QS()
        keys = list(B.keys())
        u = self.qs(u)
        # linear solve over Q(sqrt disc) via splitting into Q-coordinates
        # unknowns: V_ab = p_ab + q_ab sqrt(disc)
        monos = sorted(set(m for b in B.values() for m in b) | set(u))
        rows = []
        rhs = []
        for m in monos:
            for part in (0, 1):
                row = []
                for kk in keys:
                    c = B[kk].get(m, QS(0, 0, self.disc))
                    # (p + q s)(c.a + c.b s) = (p c.a + q c.b t) + (p c.b + q c.a) s
                    if part == 0:
                        row += [c.a, c.b * self.disc]
                    else:
                        row += [c.b, c.a]
                val = u.get(m, QS(0, 0, self.disc))
                rows.append(row)
                rhs.append(val.a if part == 0 else val.b)
        M = flint.fmpq_mat(len(rows), 18)
        bvec = flint.fmpq_mat(len(rows), 1)
        for i, r in enumerate(rows):
            for j, c in enumerate(r):
                M[i, j] = flint.fmpq(c.numerator, c.denominator)
            bvec[i, 0] = flint.fmpq(rhs[i].numerator, rhs[i].denominator)
        # least-squares-free exact solve: use rref of augmented matrix
        aug = flint.fmpq_mat(len(rows), 19)
        for i in range(len(rows)):
            for j in range(18):
                aug[i, j] = M[i, j]
            aug[i, 18] = bvec[i, 0]
        R, rk = aug.rref()
        sol = [Fr(0)] * 18
        for i in range(rk):
            # pivot column
            piv = None
            for j in range(19):
                if R[i, j] != 0:
                    piv = j
                    break
            if piv == 18:
                raise ValueError("class not in R")
            sol[piv] = Fr(int(R[i, 18].p), int(R[i, 18].q))
        V = [[None] * 3 for _ in range(3)]
        for n_, kk in enumerate(keys):
            V[kk[0]][kk[1]] = QS(sol[2 * n_], sol[2 * n_ + 1], self.disc)
        # verify
        assert sub(self.from_V(V), u) == {} or all(c == 0 for c in sub(self.from_V(V), u).values())
        return V

    # ------------------------------------------------------------ Hodge ranks
    def to_complex(self, u):
        """rational class -> complex coordinates z_j (0..3), zbar_j (4..7), QI coeffs."""
        half = Fr(1, 2)
        images = {}
        for j in range(4):
            images[j] = {1 << j: QI(half), 1 << (4 + j): QI(half)}              # x_j
            images[4 + j] = {1 << j: QI(0, -half), 1 << (4 + j): QI(0, half)}  # x_{4+j}
        uu = {k: (c if isinstance(c, QI) else QI(c)) for k, c in u.items()}
        return substitute(uu, images)

    def HT_basis(self, k):
        """list of (A, B): wedge with zbar_A, contract with d/dz_B, |A|+|B| = k."""
        out = []
        for na in range(0, k + 1):
            nb = k - na
            if na > 4 or nb > 4:
                continue
            for A in itertools.combinations(range(4), na):
                for B in itertools.combinations(range(4), nb):
                    out.append((A, B))
        return out

    def HT_act(self, AB, cu):
        A, B = AB
        r = cu
        for b in B:
            r = contract(b, r)
        for a in reversed(A):
            r = lwedge(4 + a, r, QI(1))
        return r

    def profile(self, u, kmax=8):
        cu = self.to_complex(u)
        prof = []
        for k in range(0, kmax + 1):
            vecs = [self.HT_act(AB, cu) for AB in self.HT_basis(k)]
            vecs = [v for v in vecs if v]
            prof.append(rank_QI(vecs) if vecs else 0)
        return prof

    # ------------------------------------------------------------ pairing
    def top(self):
        return (1 << 8) - 1

    def integral(self, u):
        """int_X of a class; int theta^4/4! = 1 fixes the orientation."""
        return u.get(self.top(), 0)

    def dual(self, u):
        """ch(F^vee): degree 2k part times (-1)^k."""
        return {k: (c if (pc(k) // 2) % 2 == 0 else -c) for k, c in u.items()}

    def chi(self, u, w=None):
        w = u if w is None else w
        return self.integral(wedge(self.dual(u), w))
