#!/usr/bin/env python3
"""
wt_engine.py  (round 11, track E, item 1: engine)

Fast exterior-algebra engine for the Hodge classes of members of the family S
of Weil tori (setup:weiltori), in the EIGENBASIS e_1..e_{2n} of V_+,
f_1..f_{2n} of V_- (f_j = conj e_j), which is the basis u_j^+, u_j^- of
explicit_weil.py.  Bit j (0 <= j < 2n) is e_{j+1}, bit 2n + j is f_{j+1};
a monomial is a bitmask, its generators wedged in increasing bit order.

Scalars are exact elements of K = Q(delta), delta^2 = -d, stored as pairs
(a, b) of Fractions meaning a + b delta; complex conjugation is the Galois
conjugation delta -> -delta.  A reduction modulo a prime q in which -d is a
square (delta -> s) is also provided.

A member T_{X,Y} of S is given by an invertible 2n x 2n matrix C over
Z[delta]: X is spanned by the first n rows (x_i = sum_j C_ij e_j), Y by the
last n.  Then H^{1,0} = X + conj(Y), H^{0,1} = conj(X) + Y.

Two equivalent criteria for a complex class c of degree 2k to be of type
(k,k) at the member:
  (W) the paper's criterion: c ^ h_I = 0 for every product h_I of 2n-k+1
      vectors of a basis of H^{1,0}, AND c ^ hbar_I = 0 for the conjugate
      basis of H^{0,1} (both are needed for a complex class);
  (D) D_Phi c = 0, where Phi is +1 on H^{1,0} and -1 on H^{0,1} and D_Phi
      its extension to wedge^* as a derivation, which acts by p - q on the
      (p,q) part (so over Q, or over F_q with q > 4n, its kernel in degree 2k
      is exactly the (k,k) part).
"""
import random
from fractions import Fraction as F
from itertools import combinations


# ------------------------------------------------------------ K arithmetic
class Kfield:
    def __init__(self, d):
        self.d = d
        self.zero = (F(0), F(0))
        self.one = (F(1), F(0))

    def add(self, x, y):
        return (x[0] + y[0], x[1] + y[1])

    def sub(self, x, y):
        return (x[0] - y[0], x[1] - y[1])

    def neg(self, x):
        return (-x[0], -x[1])

    def mul(self, x, y):
        return (x[0] * y[0] - self.d * x[1] * y[1],
                x[0] * y[1] + x[1] * y[0])

    def inv(self, x):
        nrm = x[0] * x[0] + self.d * x[1] * x[1]
        return (x[0] / nrm, -x[1] / nrm)

    def conj(self, x):
        return (x[0], -x[1])

    def iszero(self, x):
        return x[0] == 0 and x[1] == 0

    def smul(self, c, x):
        return (c * x[0], c * x[1])


class Fq:
    """F_q with delta -> s, s^2 = -d mod q"""

    def __init__(self, d, q=None):
        self.d = d
        if q is None:
            q = choose_prime(d)
        self.q = q
        self.s = sqrt_mod(-d % q, q)
        assert self.s * self.s % q == (-d) % q
        self.zero = 0
        self.one = 1

    def from_K(self, x):
        q = self.q
        a = x[0].numerator * pow(x[0].denominator, q - 2, q)
        b = x[1].numerator * pow(x[1].denominator, q - 2, q)
        return (a + b * self.s) % q

    def add(self, x, y):
        return (x + y) % self.q

    def sub(self, x, y):
        return (x - y) % self.q

    def neg(self, x):
        return (-x) % self.q

    def mul(self, x, y):
        return x * y % self.q

    def inv(self, x):
        return pow(x, self.q - 2, self.q)

    def iszero(self, x):
        return x % self.q == 0

    def smul(self, c, x):
        return c * x % self.q


def is_prime(q):
    if q < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    for b in small:
        if q % b == 0:
            return q == b
    dd, r = q - 1, 0
    while dd % 2 == 0:
        dd //= 2
        r += 1
    for b in small:
        x = pow(b, dd, q)
        if x in (1, q - 1):
            continue
        for _ in range(r - 1):
            x = x * x % q
            if x == q - 1:
                break
        else:
            return False
    return True


def choose_prime(d, top=2 ** 31 - 1):
    q = top
    while not (is_prime(q) and pow((-d) % q, (q - 1) // 2, q) == 1):
        q -= 2
    return q


def sqrt_mod(a, q):
    a %= q
    if a == 0:
        return 0
    assert pow(a, (q - 1) // 2, q) == 1
    Q, S = q - 1, 0
    while Q % 2 == 0:
        Q //= 2
        S += 1
    z = 2
    while pow(z, (q - 1) // 2, q) != q - 1:
        z += 1
    M, c, t, R = S, pow(z, Q, q), pow(a, Q, q), pow(a, (Q + 1) // 2, q)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % q
            i += 1
        b = pow(c, 1 << (M - i - 1), q)
        M, c, t, R = i, b * b % q, t * b * b % q, R * b % q
    return R


# ------------------------------------------------------- exterior algebra
def popc(x):
    return bin(x).count("1")


def merge_sign(a, b):
    """sign of e_a ^ e_b -> e_{a|b} (a, b disjoint masks)"""
    s = 0
    bb = b
    while bb:
        low = bb & -bb
        s += popc(a & ~((low << 1) - 1))     # elements of a above this bit
        bb ^= low
    return -1 if s & 1 else 1


def wedge(Fd, u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if a & b:
                continue
            val = Fd.mul(ca, cb)
            if merge_sign(a, b) < 0:
                val = Fd.neg(val)
            k = a | b
            if k in out:
                out[k] = Fd.add(out[k], val)
            else:
                out[k] = val
    return {k: x for k, x in out.items() if not Fd.iszero(x)}


def vec_to_elem(vec):
    """a degree-one element from {bit: scalar}"""
    return {1 << i: c for i, c in vec.items()}


# --------------------------------------------------------------- members
class Member:
    """T_{X,Y} for the matrix C (list of 2n rows of 2n K-scalars)"""

    def __init__(self, KF, n, C, name=""):
        self.KF, self.n, self.C, self.name = KF, n, C, name
        m = 2 * n
        # holomorphic basis: x_i (e's), conj(y_i) (f's)
        self.hol = []
        self.antihol = []
        for i in range(m):
            row = C[i]
            ev = {j: row[j] for j in range(m) if not KF.iszero(row[j])}
            fv = {m + j: KF.conj(row[j]) for j in range(m)
                  if not KF.iszero(row[j])}
            if i < n:
                self.hol.append(ev)          # x_i in X
                self.antihol.append(fv)      # conj x_i
            else:
                self.hol.append(fv)          # conj y_i
                self.antihol.append(ev)      # y_i in Y
        # Phi on V_+ in the e basis: P = B D B^{-1}, B = C^T
        B = [[C[i][j] for i in range(m)] for j in range(m)]   # columns x,y
        Binv = mat_inv(KF, B)
        Dg = [KF.one if i < n else KF.neg(KF.one) for i in range(m)]
        P = [[KF.zero] * m for _ in range(m)]
        for i in range(m):
            for j in range(m):
                acc = KF.zero
                for t in range(m):
                    if not KF.iszero(B[i][t]) and not KF.iszero(Binv[t][j]):
                        v = KF.mul(B[i][t], Binv[t][j])
                        acc = KF.add(acc, v if t < n else KF.neg(v))
                P[i][j] = acc
        self.P = P
        # Phi as a 4n x 4n matrix: column g = image of generator g
        self.Phi = {}
        for j in range(m):
            self.Phi[j] = {i: P[i][j] for i in range(m)
                           if not KF.iszero(P[i][j])}
            self.Phi[m + j] = {m + i: KF.neg(KF.conj(P[i][j]))
                               for i in range(m) if not KF.iszero(P[i][j])}

    def check_phi(self):
        """Phi(h) = h on H^{1,0}, Phi(hbar) = -hbar on H^{0,1}"""
        KF = self.KF
        for vecs, sgn in ((self.hol, 1), (self.antihol, -1)):
            for v in vecs:
                img = {}
                for g, c in v.items():
                    for i, pc in self.Phi[g].items():
                        img[i] = KF.add(img.get(i, KF.zero), KF.mul(c, pc))
                for i in set(img) | set(v):
                    lhs = img.get(i, KF.zero)
                    rhs = v.get(i, KF.zero)
                    if sgn < 0:
                        rhs = KF.neg(rhs)
                    if not KF.iszero(KF.sub(lhs, rhs)):
                        return False
        return True

    def reduce_mod(self, FQ):
        """the same member with scalars reduced into FQ"""
        M = Member.__new__(Member)
        M.KF, M.n, M.name = FQ, self.n, self.name + " mod q"
        conv = FQ.from_K
        M.hol = [{g: conv(c) for g, c in v.items()} for v in self.hol]
        M.antihol = [{g: conv(c) for g, c in v.items()} for v in self.antihol]
        M.Phi = {g: {i: conv(c) for i, c in col.items()}
                 for g, col in self.Phi.items()}
        return M


def mat_inv(KF, A):
    m = len(A)
    M = [list(A[i]) + [KF.one if i == j else KF.zero for j in range(m)]
         for i in range(m)]
    for c in range(m):
        p = next(i for i in range(c, m) if not KF.iszero(M[i][c]))
        M[c], M[p] = M[p], M[c]
        iv = KF.inv(M[c][c])
        M[c] = [KF.mul(iv, x) for x in M[c]]
        for i in range(m):
            if i != c and not KF.iszero(M[i][c]):
                f = M[i][c]
                M[i] = [KF.sub(x, KF.mul(f, y)) for x, y in zip(M[i], M[c])]
    return [row[m:] for row in M]


def mat_det_nonzero(KF, A):
    m = len(A)
    M = [list(r) for r in A]
    for c in range(m):
        p = next((i for i in range(c, m) if not KF.iszero(M[i][c])), None)
        if p is None:
            return False
        M[c], M[p] = M[p], M[c]
        iv = KF.inv(M[c][c])
        for i in range(c + 1, m):
            if not KF.iszero(M[i][c]):
                f = KF.mul(M[i][c], iv)
                M[i] = [KF.sub(x, KF.mul(f, y)) for x, y in zip(M[i], M[c])]
    return True


def random_member(KF, n, rng, lo=-3, hi=3, name="random"):
    m = 2 * n
    while True:
        C = [[(F(rng.randint(lo, hi)), F(rng.randint(lo, hi)))
              for _ in range(m)] for _ in range(m)]
        if mat_det_nonzero(KF, C):
            return Member(KF, n, C, name)


def diagonal_member(KF, n, S):
    """X = span(e_j : j in S), Y = span(e_j : j not in S)"""
    m = 2 * n
    order = list(S) + [j for j in range(m) if j not in S]
    C = [[KF.one if j == order[i] else KF.zero for j in range(m)]
         for i in range(m)]
    return Member(KF, n, C, "diag%s" % (tuple(S),))


# ------------------------------------------------------- the two criteria
def derivation(Fd, Phi, mask, coeff):
    """D_Phi (coeff * e_mask) as a dict"""
    out = {}
    bits = []
    x = mask
    while x:
        low = x & -x
        bits.append(low.bit_length() - 1)
        x ^= low
    for g in bits:
        rest = mask ^ (1 << g)
        for i, c in Phi[g].items():
            if i != g and (rest >> i) & 1:
                continue
            new = rest | (1 << i)
            lo, hi = (g, i) if g < i else (i, g)
            between = popc(rest & ((1 << hi) - 1) & ~((1 << (lo + 1)) - 1))
            val = Fd.mul(coeff, c)
            if between & 1:
                val = Fd.neg(val)
            out[new] = Fd.add(out[new], val) if new in out else val
    return out


def apply_derivation(Fd, Phi, elem):
    out = {}
    for mask, c in elem.items():
        for k, v in derivation(Fd, Phi, mask, c).items():
            out[k] = Fd.add(out[k], v) if k in out else v
    return {k: v for k, v in out.items() if not Fd.iszero(v)}


def hI_products(Fd, vecs, size):
    """{I: h_I} for all size-subsets I of the list of degree-one vectors"""
    elems = [vec_to_elem(v) for v in vecs]
    out = {}
    for I in combinations(range(len(elems)), size):
        u = {0: Fd.one}
        for i in I:
            u = wedge(Fd, u, elems[i])
            if not u:
                break
        out[I] = u
    return out


# ------------------------------------------------------- the space W_k
def W_basis(Fd, n, k):
    """basis of the joint kernel, over all diagonal members, of the (k,k)
    condition: the products prod_{j in A} e_j ^ f_j, |A| = k, and alpha_+,
    alpha_- when k = n.  Returned as a list of (label, element)."""
    m = 2 * n
    out = []
    for A in combinations(range(m), k):
        u = {0: Fd.one}
        for j in A:
            u = wedge(Fd, u, {(1 << j) | (1 << (m + j)): Fd.one})
        out.append(("w%s" % (tuple(A),), u))
    if k == n:
        out.append(("alpha_+", {(1 << m) - 1: Fd.one}))
        out.append(("alpha_-", {((1 << (2 * m)) - 1) ^ ((1 << m) - 1):
                                Fd.one}))
    return out


def weight_zero_monomials(n, k):
    """monomials of degree 2k with weight zero for every diagonal member
    (all binom(2n,n) of them), i.e. sum_{S} v - sum_{S^c} v = 0 for
    v = 1_A - 1_B, for every n-subset S; counted directly"""
    m = 2 * n
    subsets = list(combinations(range(m), n))
    cnt = 0
    good = []
    for mu in combinations(range(2 * m), 2 * k):
        v = [0] * m
        for g in mu:
            if g < m:
                v[g] += 1
            else:
                v[g - m] -= 1
        tot = sum(v)
        ok = True
        for S in subsets:
            s = 0
            for j in S:
                s += v[j]
            if 2 * s - tot != 0:       # sum_S v - sum_{S^c} v
                ok = False
                break
        if ok:
            cnt += 1
            good.append(sum(1 << g for g in mu))
    return cnt, good


# ------------------------------------------------------- exact sparse rank
def sparse_rank(Fd, vectors):
    """rank of a list of sparse vectors {key: scalar} (keys comparable);
    returns (rank, list of indices of vectors that were independent)"""
    piv = {}
    indep = []
    for idx, v in enumerate(vectors):
        v = {k: c for k, c in v.items() if not Fd.iszero(c)}
        while v:
            k = min(v)
            if k in piv:
                p = piv[k]
                f = Fd.mul(v[k], Fd.inv(p[k]))
                for kk, c in p.items():
                    x = Fd.sub(v[kk], Fd.mul(f, c)) if kk in v else \
                        Fd.neg(Fd.mul(f, c))
                    if Fd.iszero(x):
                        v.pop(kk, None)
                    else:
                        v[kk] = x
            else:
                piv[k] = v
                indep.append(idx)
                break
    return len(piv), indep


def kernel_dim_on_basis(Fd, basis_elems, conditions):
    """basis_elems: list of elements (dicts); conditions: list of functions
    elem -> dict keyed by hashable keys.  Returns dim of the space of
    combinations of basis_elems killed by every condition (the columns are
    the basis elements, rows the condition coordinates)."""
    cols = []
    for el in basis_elems:
        vec = {}
        for ci, cond in enumerate(conditions):
            for key, val in cond(el).items():
                vec[(ci, key)] = val
        cols.append(vec)
    r, _ = sparse_rank(Fd, cols)
    return len(basis_elems) - r
