"""qk_coeff.py -- graph-type kernels on X x X in coordinates, for item (LIX).

F_0 = Q(sqrt D), O = Z[R] with R = (1 + sqrt D)/2 if D = 1 mod 4 and R = sqrt D
otherwise; X a principally polarised abelian fourfold with real multiplication
by O; theta_1, theta_2 the components of the polarisation at the two real
places, theta_j^3 = 0.  Elements of F_0 are pairs (a, b) = a + b sqrt D; the
first real place is sqrt D > 0, and tau_2 is the conjugate.

At a real place a class on X_j x X_j of graph type is a correspondence
y_k -> C_k ^ y_k.  With C_k in R[theta_j] it is a combination of the nine
E_(k, m) : y_k -> theta_j^(m/2) ^ y_k, (k, m) with k + m <= 4, m in {0, 2, 4},
and a class on X x X of graph type at both places is a vector in the 81-
dimensional span of the E_(k1, m1) (x) E_(k2, m2), with coefficients in F_0.
The class (beta, alpha)_*(c) of a sheaf on the graph {(beta x, alpha x)}, for
beta, alpha in O and c = sum c_ab theta_1^a theta_2^b, has at a place the
correspondence y_k -> b^k a^(4 - k - m) (y_k ^ c_m) (qk_place.graph_class), so
its coordinate at (k1, 2a) (x) (k2, 2b) is
    c_ab tau_1(beta)^k1 tau_1(alpha)^(4 - k1 - 2a) tau_2(beta)^k2 tau_2(alpha)^(4 - k2 - 2b).
"""
from fractions import Fraction as Fr
import itertools
from qk_ext import rank_Q, nullspace_Q

Z0 = (Fr(0), Fr(0))


class F0:
    def __init__(self, D):
        self.D = D
        if D % 4 == 1:
            self.R = (Fr(1, 2), Fr(1, 2))
        else:
            self.R = (Fr(0), Fr(1))

    def m(self, x, y):
        return (x[0] * y[0] + self.D * x[1] * y[1], x[0] * y[1] + x[1] * y[0])

    @staticmethod
    def ad(x, y):
        return (x[0] + y[0], x[1] + y[1])

    @staticmethod
    def scl(c, x):
        return (c * x[0], c * x[1])

    @staticmethod
    def conj(x):
        return (x[0], -x[1])

    def pw(self, x, k):
        r = (Fr(1), Fr(0))
        for _ in range(k):
            r = self.m(r, x)
        return r

    def elt(self, o):
        """o = (m, n) -> m + n R."""
        return self.ad((Fr(o[0]), Fr(0)), self.scl(Fr(o[1]), self.R))

    def taus(self, x):
        return [x, self.conj(x)]


BASIS = []
for k1 in range(5):
    for m1 in (0, 2, 4):
        if k1 + m1 > 4:
            continue
        for k2 in range(5):
            for m2 in (0, 2, 4):
                if k2 + m2 > 4:
                    continue
                BASIS.append(((k1, m1), (k2, m2)))
BIDX = {b: i for i, b in enumerate(BASIS)}


def T_vec(Fd, dj):
    """the per-place correspondence T(d) of qk_place.T_class in the E-basis."""
    return {(0, 4): Fd.scl(Fr(-1, 2), Fd.m(dj, dj)), (2, 0): Fd.scl(Fr(1, 2), dj),
            (3, 0): Fd.scl(Fr(3, 2), dj), (4, 0): Fd.scl(Fr(3), dj)}


def G_vec(Fd, q):
    """G'' = U0_1 (x) T_2 + T_1 (x) U0_2, U0 = E_(4, 0)."""
    d = Fd.taus(q)
    G = [Z0] * len(BASIS)
    for key, c in T_vec(Fd, d[1]).items():
        i = BIDX[((4, 0), key)]
        G[i] = Fd.ad(G[i], c)
    for key, c in T_vec(Fd, d[0]).items():
        i = BIDX[(key, (4, 0))]
        G[i] = Fd.ad(G[i], c)
    return G


def c_expand(Fd, i, l):
    """theta^i theta_R^l = sum c_ab theta_1^a theta_2^b (a, b <= 2), theta_R the
    class of the twisted polarisation, tau_1(R) theta_1 + tau_2(R) theta_2."""
    Rt = Fd.taus(Fd.R)
    poly = {(0, 0): (Fr(1), Fr(0))}
    for factors in ([(1, 0, (Fr(1), Fr(0))), (0, 1, (Fr(1), Fr(0)))],) * i + \
            ([(1, 0, Rt[0]), (0, 1, Rt[1])],) * l:
        new = {}
        for (a, b), c in poly.items():
            for (da, db, coef) in factors:
                if a + da <= 2 and b + db <= 2:
                    key = (a + da, b + db)
                    new[key] = Fd.ad(new.get(key, Z0), Fd.m(c, coef))
        poly = new
    return poly


def graph_vec(Fd, beta, alpha, cdict):
    tb, ta = Fd.taus(Fd.elt(beta)), Fd.taus(Fd.elt(alpha))
    v = [Z0] * len(BASIS)
    for (a, b), cc in cdict.items():
        for k1 in range(0, 5 - 2 * a):
            for k2 in range(0, 5 - 2 * b):
                coef = Fd.m(Fd.m(Fd.pw(tb[0], k1), Fd.pw(ta[0], 4 - k1 - 2 * a)),
                            Fd.m(Fd.pw(tb[1], k2), Fd.pw(ta[1], 4 - k2 - 2 * b)))
                i = BIDX[((k1, 2 * a), (k2, 2 * b))]
                v[i] = Fd.ad(v[i], Fd.m(cc, coef))
    return v


def galois(Fd, v):
    """the action of Gal(F_0/Q) on a vector: exchange the places, conjugate."""
    out = [Z0] * len(BASIS)
    for i, (a, b) in enumerate(BASIS):
        out[BIDX[(b, a)]] = Fd.conj(v[i])
    return out


def ratrows(vecs):
    return [[x for c in v for x in c] for v in vecs]


def in_Q_span(target, gens):
    n = 2 * len(BASIS)
    R = ratrows(gens)
    return rank_Q(R + ratrows([target]), n) == rank_Q(R, n), rank_Q(R, n)


def solve_Q(target, gens):
    """rational coefficients a_i with sum a_i gens_i = target, or None."""
    R = ratrows(gens)
    t = ratrows([target])[0]
    cols = len(gens) + 1
    rows = [[R[i][k] for i in range(len(gens))] + [-t[k]] for k in range(len(t))]
    for v in nullspace_Q(rows, cols):
        if v[-1] != 0:
            return [x / v[-1] for x in v[:-1]]
    return None
