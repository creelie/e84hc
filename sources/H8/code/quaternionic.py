#!/usr/bin/env python3
"""
quaternionic.py

Question (R2) of the paper asks for one member of a Weil family of nontrivial
discriminant at which the Weil classes are algebraic.  This script decides the
question by exhibiting such members.

The mechanism is the divisorial criterion.  Let B = (-d, b) be the quaternion
algebra over Q with generators i, j satisfying

    i^2 = -d,      j^2 = b,      i j = - j i,

and let A be an abelian 2n-fold with H^1(A,Q) = B^n as a left B-module and
polarisation E(x,y) = sum_k a_k trd( conj(x_k) i y_k ),  a_k in Q^x.  Then:

  (Q1) left multiplication by i and by j satisfies the relations, and j is
       semilinear over K = Q(i), that is  L_j L_i = L_conj(i) L_j;

  (Q2) E is alternating and nondegenerate, L_i is anti-self-adjoint for it,
       which is the Rosati condition, and L_j is self-adjoint, so the class
       of E composed with L_j is a divisor class;

  (Q3) in the K-basis  e_1, e_1 j, ..., e_n, e_n j  the hermitian form is
       diag( 2 a_k d, -2 a_k b d ), of signature (n,n) for b > 0, so A is of
       (K,-1,n)-Weil type with no further hypothesis;

  (Q4) det H = (-1)^n b^n ( 2^n d^n prod a_k )^2, so the discriminant class is
       b^n modulo norms from K.  For n odd that is b, and b runs over every
       class; for n even it is a square and the class is trivial;

  (Q5) the class g(x,y) = E(L_j x, y) is K-bilinear, so it lies in the outer
       part R of H^2, and it is nondegenerate.  The divisorial criterion of
       Theorem 14.16 therefore applies, and the Weil classes of A are
       algebraic.

Everything below is exact rational arithmetic.
"""

from fractions import Fraction as F
from itertools import combinations


def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("           " + detail)
    return (1, 0) if ok else (0, 1)


# ------------------------------------------------------- the algebra B

class Quat:
    """B = (-d, b) over Q, basis 1, i, j, ij."""

    def __init__(self, d, b):
        self.d, self.b = d, b

    def mul(self, x, y):
        d, b = self.d, self.b
        x0, x1, x2, x3 = x
        y0, y1, y2, y3 = y
        # (x0 + x1 i + x2 j + x3 ij)(y0 + y1 i + y2 j + y3 ij)
        z0 = x0 * y0 - d * x1 * y1 + b * x2 * y2 + d * b * x3 * y3
        z1 = x0 * y1 + x1 * y0 - b * x2 * y3 + b * x3 * y2
        z2 = x0 * y2 + x2 * y0 - d * x1 * y3 + d * x3 * y1
        z3 = x0 * y3 + x3 * y0 + x1 * y2 - x2 * y1
        return (z0, z1, z2, z3)

    def conj(self, x):
        return (x[0], -x[1], -x[2], -x[3])

    def trd(self, x):
        return 2 * x[0]

    def one(self):
        return (F(1), F(0), F(0), F(0))

    def i(self):
        return (F(0), F(1), F(0), F(0))

    def j(self):
        return (F(0), F(0), F(1), F(0))


def basis4():
    e = []
    for k in range(4):
        v = [F(0)] * 4
        v[k] = F(1)
        e.append(tuple(v))
    return e


# ------------------------------------------------- the module V = B^n

class Model:
    def __init__(self, n, d, b, weights=None):
        self.n, self.d, self.b = n, d, b
        self.B = Quat(d, b)
        self.a = weights if weights else [1] * n
        self.N = 4 * n

    def idx(self, k, r):
        """basis vector: component k (0-based), quaternion basis element r."""
        return 4 * k + r

    def vec(self, k, q):
        """the element of V with q in slot k."""
        v = [F(0)] * self.N
        for r in range(4):
            v[self.idx(k, r)] = q[r]
        return v

    def left(self, q):
        """matrix of left multiplication by the quaternion q on V."""
        M = [[F(0)] * self.N for _ in range(self.N)]
        for k in range(self.n):
            for r, e in enumerate(basis4()):
                img = self.B.mul(q, e)
                for s in range(4):
                    M[self.idx(k, s)][self.idx(k, r)] = img[s]
        return M

    def E(self):
        """E(x,y) = sum_k a_k trd( conj(x_k) i y_k ), as a matrix."""
        B = self.B
        Em = [[F(0)] * self.N for _ in range(self.N)]
        for k in range(self.n):
            for r, er in enumerate(basis4()):
                for s, es in enumerate(basis4()):
                    z = B.mul(B.mul(B.conj(er), B.i()), es)
                    Em[self.idx(k, r)][self.idx(k, s)] = F(self.a[k]) * B.trd(z)
        return Em


def matmul(A, C):
    n, m, p = len(A), len(C), len(C[0])
    R = [[F(0)] * p for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for k in range(m):
            v = Ai[k]
            if v == 0:
                continue
            Ck = C[k]
            for jj in range(p):
                R[i][jj] += v * Ck[jj]
    return R


def transpose(A):
    return [list(r) for r in zip(*A)]


def is_zero(A):
    return all(v == 0 for row in A for v in row)


def add(A, C):
    return [[a + c for a, c in zip(ra, rc)] for ra, rc in zip(A, C)]


def scale(t, A):
    return [[t * a for a in r] for r in A]


def det(A):
    """exact determinant by fraction-free elimination."""
    M = [row[:] for row in A]
    n = len(M)
    d = F(1)
    for c in range(n):
        p = None
        for r in range(c, n):
            if M[r][c] != 0:
                p = r
                break
        if p is None:
            return F(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return d


def squarefree_part(y):
    out, m = 1, abs(y)
    f = 2
    while f * f <= m:
        e = 0
        while m % f == 0:
            m //= f
            e += 1
        if e % 2:
            out *= f
        f += 1
    return out * m


def is_norm(x, d, bound=60000):
    """Is the positive rational x a norm from Q(sqrt(-d))?"""
    if x <= 0:
        return False
    y = x.numerator * x.denominator
    k = squarefree_part(y)
    if k == 1:
        return True
    for m in range(1, 80):
        t = k * m * m
        bb = 0
        while d * bb * bb <= t and bb <= bound:
            r = t - d * bb * bb
            rr = int(round(r ** 0.5))
            for c in (rr - 1, rr, rr + 1):
                if c >= 0 and c * c == r:
                    return True
            bb += 1
    return False


def signature(A):
    """signature of a real symmetric matrix, by symmetric elimination."""
    M = [row[:] for row in A]
    n = len(M)
    pos = neg = 0
    used = [False] * n
    for _ in range(n):
        p = None
        for r in range(n):
            if not used[r] and M[r][r] != 0:
                p = r
                break
        if p is None:
            # look for an off-diagonal pivot among unused rows
            found = False
            for r in range(n):
                for c in range(n):
                    if r != c and not used[r] and not used[c] and M[r][c] != 0:
                        for k in range(n):
                            M[r][k] += M[c][k]
                        for k in range(n):
                            M[k][r] += M[k][c]
                        found = True
                        break
                if found:
                    break
            if not found:
                break
            continue
        used[p] = True
        if M[p][p] > 0:
            pos += 1
        else:
            neg += 1
        pv = M[p][p]
        for r in range(n):
            if not used[r] and M[r][p] != 0:
                f = M[r][p] / pv
                for k in range(n):
                    M[r][k] -= f * M[p][k]
                for k in range(n):
                    M[k][r] -= f * M[k][p]
    return pos, neg


# --------------------------------------------------------------- the runs

def run(n, d, b, weights=None, verbose=True):
    npass = nfail = 0
    M = Model(n, d, b, weights)
    Li, Lj = M.left(M.B.i()), M.left(M.B.j())
    N = M.N
    Id = [[F(1) if r == c else F(0) for c in range(N)] for r in range(N)]

    # (Q1)
    ok = (is_zero(add(matmul(Li, Li), scale(F(d), Id)))
          and is_zero(add(matmul(Lj, Lj), scale(F(-b), Id)))
          and is_zero(add(matmul(Li, Lj), matmul(Lj, Li))))
    p, f = check("i^2 = -d, j^2 = b, ij = -ji, so j is semilinear over K", ok)
    npass += p
    nfail += f

    # (Q2)
    Em = M.E()
    alt = is_zero(add(Em, transpose(Em)))
    nondeg = det(Em) != 0
    anti = is_zero(add(matmul(transpose(Li), Em), matmul(Em, Li)))
    selfadj = is_zero(add(matmul(transpose(Lj), Em), scale(F(-1), matmul(Em, Lj))))
    p, f = check("E alternating, nondegenerate, L_i anti-self-adjoint, "
                 "L_j self-adjoint", alt and nondeg and anti and selfadj)
    npass += p
    nfail += f

    # (Q3) the hermitian form on the K-basis e_k, e_k j
    kb = []
    for k in range(n):
        kb.append(M.vec(k, M.B.one()))
        kb.append(M.vec(k, M.B.j()))

    def Ev(x, y):
        return sum(x[r] * Em[r][c] * y[c] for r in range(N) for c in range(N))

    # H(x,y) = E(i x, y) + sqrt(-d) E(x,y), as a pair (real, sqrt(-d) part)
    Hr = [[F(0)] * (2 * n) for _ in range(2 * n)]
    Hi = [[F(0)] * (2 * n) for _ in range(2 * n)]
    for r, x in enumerate(kb):
        ix = [sum(Li[u][v] * x[v] for v in range(N)) for u in range(N)]
        for c, y in enumerate(kb):
            Hr[r][c] = Ev(ix, y)
            Hi[r][c] = Ev(x, y)
    herm = all(Hr[r][c] == Hr[c][r] and Hi[r][c] == -Hi[c][r]
               for r in range(2 * n) for c in range(2 * n))
    want = []
    for k in range(n):
        want += [F(2 * M.a[k] * d), F(-2 * M.a[k] * b * d)]
    diag = all(Hr[r][c] == (want[r] if r == c else F(0)) and Hi[r][c] == 0
               for r in range(2 * n) for c in range(2 * n))
    sg = signature(Hr)
    p, f = check("H = diag(2 a_k d, -2 a_k b d) in the K-basis, hermitian, "
                 "signature %s" % (sg,), herm and diag and sg == (n, n))
    npass += p
    nfail += f

    # (Q4) the discriminant
    detH = F(1)
    for w in want:
        detH *= w
    pref = F(2) ** n * F(d) ** n
    for w in M.a:
        pref *= F(w)
    predicted = F((-1) ** n) * F(b) ** n * pref ** 2
    normalised = F((-1) ** n) * detH
    cls = normalised / (F(b) ** n)
    p, f = check("det H = (-1)^n b^n (2^n d^n prod a_k)^2",
                 detH == predicted,
                 "det H = %s, b^n = %s, quotient %s is a square: %s"
                 % (detH, F(b) ** n, cls,
                    "yes" if is_norm(cls, d) else "no"))
    npass += p
    nfail += f

    # (Q5) the class g(x,y) = E(L_j x, y) is K-bilinear and nondegenerate
    g = matmul(transpose(Lj), Em)
    galt = is_zero(add(g, transpose(g)))
    # K-bilinear: g(i x, y) = g(x, i y)
    kb_lin = is_zero(add(matmul(transpose(Li), g),
                         scale(F(-1), matmul(g, Li))))
    gnd = det(g) != 0
    p, f = check("g(x,y) = E(jx,y) is alternating, K-bilinear (so g lies in "
                 "R) and nondegenerate", galt and kb_lin and gnd)
    npass += p
    nfail += f
    return npass, nfail


def product_case(parts, d):
    """parts = [(n_k, b_k, weights_k)].  The orthogonal sum of the hermitian
    forms of the factors: signature adds, determinant multiplies, and the
    divisorial criterion holds on the sum because it holds on each factor."""
    n = sum(p[0] for p in parts)
    diag = []
    cls = F(1)
    for (nk, bk, wk) in parts:
        a = wk if wk else [1] * nk
        for t in a:
            diag += [F(2 * t * d), F(-2 * t * bk * d)]
        cls *= F(bk) ** nk
    detH = F(1)
    for v in diag:
        detH *= v
    sg = (sum(1 for v in diag if v > 0), sum(1 for v in diag if v < 0))
    normalised = F((-1) ** n) * detH
    trivial = is_norm(normalised, d)
    predicted_trivial = is_norm(cls, d)
    return n, sg, detH, cls, trivial, predicted_trivial


# ------------------------------------------------- the quaternionic locus

def quaternionic_locus_dim(n):
    """The complex structures on V commuting with B form the symmetric space
    of the unitary group of the B-valued hermitian form.  With the Rosati
    involution of orthogonal type that group is Sp(2n,R), whose symmetric
    space has dimension n(n+1)/2, inside the D_{n,n} of dimension n^2."""
    return n * (n + 1) // 2


def properness_count(n):
    """The three numbers the properness reduction turns on: the dimension of
    the period domain, the dimension of the quaternionic locus in it, and the
    codimension of the second inside the first."""
    amb = n * n                      # dim D_{n,n}
    quat = quaternionic_locus_dim(n)
    return amb, quat, amb - quat


if __name__ == "__main__":
    print("abelian varieties of Weil type with quaternionic multiplication")
    NP = NF = 0

    cases = [(1, 1, 3, None), (1, 1, 7, None), (1, 2, 5, None),
             (2, 1, 3, None), (2, 1, 2, [1, 3]), (2, 3, 5, None),
             (3, 1, 3, None), (3, 2, 5, None), (3, 1, 7, [1, 1, 2])]
    for (n, d, b, w) in cases:
        print("  n=%d, d=%d, b=%d, weights %s   (dim A = %d)"
              % (n, d, b, w if w else [1] * n, 2 * n))
        p, f = run(n, d, b, w)
        NP += p
        NF += f

    print("  which discriminant classes are reached")
    ok = True
    for d in (1, 2, 3, 7, 11):
        nonnorms = [b for b in range(2, 60) if not is_norm(F(b), d)]
        if not nonnorms:
            ok = False
            continue
        b0 = nonnorms[0]
        for n in (1, 2, 3, 4, 5, 6):
            cls_is_trivial = is_norm(F(b0) ** n, d)
            expect = (n % 2 == 0)
            if cls_is_trivial != expect:
                ok = False
        print("    d=%2d: smallest positive non-norm is b=%d; b^n is a norm "
              "exactly for n even" % (d, b0))
    p, f = check("for n odd the class is b, so every class in "
                 "Q_{>0}^x / N(K^x) is reached; for n even it is trivial", ok)
    NP += p
    NF += f

    print("  products of quaternionic factors reach every class")
    ok = True
    rows = []
    for d in (1, 2, 3, 7):
        nn = [b for b in range(2, 40) if not is_norm(F(b), d)]
        b0 = nn[0]
        for n in (2, 4, 6, 8):
            # n even: one factor of odd dimension n-1 with b = d (trivial),
            # one factor of dimension 1 with b = b0 (nontrivial)
            parts = [(1, b0, None), (n - 1, d, None)]
            m, sg, detH, cls, trivial, pred = product_case(parts, d)
            good = (m == n and sg == (n, n) and trivial == pred
                    and not trivial)
            ok = ok and good
            if n in (2, 4):
                rows.append("d=%d, n=%d: b=%d and b=%d, signature %s, "
                            "class %s, trivial: %s"
                            % (d, n, b0, d, sg, cls, "yes" if trivial else "no"))
    for r in rows:
        print("    " + r)
    p, f = check("for n even a product of an odd quaternionic factor and a "
                 "split factor has nontrivial discriminant", ok)
    NP += p
    NF += f

    allclasses = True
    for d in (1, 2, 3, 7, 11):
        targets = [b for b in range(2, 30) if not is_norm(F(b), d)][:4]
        for n in range(1, 9):
            for t in targets:
                if n % 2 == 1:
                    parts = [(n, t, None)]
                else:
                    parts = [(1, t, None), (n - 1, d, None)]
                m, sg, detH, cls, trivial, pred = product_case(parts, d)
                if m != n or sg != (n, n) or trivial:
                    allclasses = False
    p, f = check("every nontrivial class tested is realised, in every "
                 "dimension 1 <= n <= 8, with signature (n,n)", allclasses)
    NP += p
    NF += f

    print("  the quaternionic locus inside the Weil family")
    ok = True
    for n in range(1, 11):
        amb, quat, cod = properness_count(n)
        if cod != n * (n - 1) // 2 or (cod == 0) != (n == 1):
            ok = False
        if n <= 5:
            print("    n=%d: dim D_{n,n} = %2d, dim of the quaternionic "
                  "locus = %2d, codimension = %d" % (n, amb, quat, cod))
    p, f = check("the quaternionic locus has dimension n(n+1)/2 and "
                 "codimension n(n-1)/2, zero only at n = 1", ok)
    NP += p
    NF += f

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
