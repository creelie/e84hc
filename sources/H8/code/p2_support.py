#!/usr/bin/env python3
"""
p2_support.py

The finite linear algebra behind the two theorems that sharpen (P2): that
the semiregularity criterion holds as soon as Ext^2(E,E) has its smallest
possible dimension, and that an object meeting the criterion cannot be
supported in codimension n.  Item (XXXIX).

Notation.  A is an abelian 2n-fold of Weil type, H^1(A,C) has the four
pieces V_+^{1,0}, V_-^{1,0}, V_+^{0,1}, V_-^{0,1}, each of dimension n, with
bases x, y, xb, yb, and the Weil line is spanned by alpha_+ = x_[n] xb_[n]
and alpha_- = y_[n] yb_[n].  The tangent space is T_+ (+) T_-, dual to the
x and the y.  Hochschild cohomology HH^1 = H^{0,1} (+) H^0(T_A) acts on
H^*(A,C) by wedging with xb, yb and contracting x, y.

What is checked, in exact rational arithmetic:

  (A) The count behind the numerical form of the criterion: the map
      HH^2 -> H^{2n+2}, xi |-> xi _| omega, has rank 2n(2n-1) for
      n = 2, 3, and it is injective on wedge^2 P (+) wedge^2 Q, where
      P = V_+^{0,1} (+) T_- and Q = V_-^{0,1} (+) T_+.  Also
      binom(4n,2) - 4n^2 = 2 binom(2n,2) = 2n(2n-1) for every n <= 60.
      With the square sigma_E ev_E = ( ) _| ch(E), this is all the
      theorem uses: if dim Ext^2(E,E) = 2n(2n-1) then ev_E is onto,
      its kernel is exactly P ^ Q, and sigma_E is injective.

  (B) The key nonvanishing of the local product lemma: on a torus of
      dimension c, 2 <= c <= 6, the class of a point contracted with a ^ b
      is nonzero for every pair of independent constant vector fields a, b,
      checked on all coordinate pairs and on random rational pairs, and is
      zero when a, b are dependent.

  (C) The dichotomy: for a subspace W of T_+ (+) T_- of codimension
      c >= 2, the images of T_+ and T_- in the quotient have all their
      mixed wedges zero if and only if W contains T_+ or W contains T_-.
      Checked on random subspaces over Q for n = 2, 3, 4 and on the
      boundary cases where W contains one of the two.

  (D) The eigenspace bookkeeping in an explicit real model.  For n = 1, 2
      and K = Q(i), with an explicit rational complex structure J and
      K-action M on R^{4n} of signature (n,n), the annihilator in
      H^1(A,C) of the real subspace ker(J - M), which is the real form of
      T_+, is exactly V_-^{1,0} (+) V_+^{0,1}; so the cohomology pulled
      back from A/B, for any abelian subvariety B with T_0 B containing
      T_+, lies in the exterior algebra on V_-^{1,0} (+) V_+^{0,1}.
      Computed with Gaussian rationals.

  (E) The monomial separation: for 2 <= n <= 6 the Weil line meets the
      sum of the degree 2n parts of wedge^*(V_-^{1,0} (+) V_+^{0,1}) and
      wedge^*(V_+^{1,0} (+) V_-^{0,1}) only in zero.

Nothing here constructs an object satisfying the criterion.
"""

import random
from fractions import Fraction as Fr
from math import comb

PASS, FAIL = [], []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % (tag, name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


# -------------------------------------------------- exterior algebra by masks
def sign_insert(i, mask):
    """sign of moving generator i to its place in the ordered monomial mask"""
    return -1 if bin(mask & ((1 << i) - 1)).count("1") % 2 else 1


def wedge_gen(i, u):
    out = {}
    for a, c in u.items():
        if (a >> i) & 1:
            continue
        k = a | (1 << i)
        out[k] = out.get(k, 0) + sign_insert(i, a) * c
    return {k: v for k, v in out.items() if v != 0}


def contract_gen(i, u):
    out = {}
    for a, c in u.items():
        if not (a >> i) & 1:
            continue
        k = a ^ (1 << i)
        out[k] = out.get(k, 0) + sign_insert(i, a) * c
    return {k: v for k, v in out.items() if v != 0}


def rank(rows):
    """rank of a list of dict-vectors over Q"""
    rows = [dict(r) for r in rows if r]
    piv = []
    for r in rows:
        r = dict(r)
        for (p, pr) in piv:
            if p in r:
                f = r[p] / pr[p]
                for k, v in pr.items():
                    r[k] = r.get(k, 0) - f * v
                    if r[k] == 0:
                        del r[k]
        if r:
            p = min(r)
            piv.append((p, r))
    return len(piv)


# ------------------------------------------------------- (A) the count
def item_A():
    for n in (2, 3):
        X = list(range(0, n))            # V_+^{1,0}
        Y = list(range(n, 2 * n))        # V_-^{1,0}
        XB = list(range(2 * n, 3 * n))   # V_+^{0,1}
        YB = list(range(3 * n, 4 * n))   # V_-^{0,1}
        mask = lambda idx: sum(1 << i for i in idx)
        a, b = Fr(2), Fr(-3)
        omega = {mask(X + XB): a, mask(Y + YB): b}
        # HH^1 generators: ('w', i) wedge with a (0,1) class, ('c', i)
        # contract a (1,0) class
        gens = [('w', i) for i in XB + YB] + [('c', i) for i in X + Y]

        def act(g, u):
            return wedge_gen(g[1], u) if g[0] == 'w' else contract_gen(g[1], u)

        pairs = [(g, h) for i, g in enumerate(gens) for h in gens[i + 1:]]
        images = [act(g, act(h, omega)) for (g, h) in pairs]
        r = rank(images)
        check("n=%d: xi |-> xi _| omega has rank 2n(2n-1) on HH^2" % n,
              r == 2 * n * (2 * n - 1),
              "rank %d = %d, out of dim HH^2 = %d" % (r, 2 * n * (2 * n - 1),
                                                    len(pairs)))
        Pset = [('w', i) for i in XB] + [('c', i) for i in Y]
        Qset = [('w', i) for i in YB] + [('c', i) for i in X]
        sub = [(g, h) for (g, h) in pairs
               if (g in Pset and h in Pset) or (g in Qset and h in Qset)]
        rs = rank([act(g, act(h, omega)) for (g, h) in sub])
        check("n=%d: it is injective on wedge^2 P (+) wedge^2 Q" % n,
              rs == len(sub) == 2 * comb(2 * n, 2),
              "%d independent images from %d classes" % (rs, len(sub)))
    ok = all(comb(4 * n, 2) - 4 * n * n == 2 * comb(2 * n, 2)
             == 2 * n * (2 * n - 1) for n in range(1, 61))
    check("binom(4n,2) - 4n^2 = 2 binom(2n,2) = 2n(2n-1) for n <= 60", ok)


# --------------------------------------- (B) the point class on a c-torus
def item_B():
    rnd = random.Random(20260923)
    for c in range(2, 7):
        # generators dz_1..dz_c (holomorphic), dzb_1..dzb_c
        point = {(1 << (2 * c)) - 1: 1}

        def contract_field(v, u):
            out = {}
            for i, vi in enumerate(v):
                if vi == 0:
                    continue
                for k, x in contract_gen(i, u).items():
                    out[k] = out.get(k, 0) + vi * x
            return {k: x for k, x in out.items() if x != 0}

        ok_coord = True
        for i in range(c):
            for j in range(i + 1, c):
                a = [1 if t == i else 0 for t in range(c)]
                b = [1 if t == j else 0 for t in range(c)]
                if not contract_field(a, contract_field(b, point)):
                    ok_coord = False
        ok_rand, ok_dep = True, True
        for _ in range(25):
            a = [Fr(rnd.randint(-9, 9)) for _ in range(c)]
            b = [Fr(rnd.randint(-9, 9)) for _ in range(c)]
            indep = rank([{i: x for i, x in enumerate(a) if x},
                          {i: x for i, x in enumerate(b) if x}]) == 2
            val = contract_field(a, contract_field(b, point))
            if indep and not val:
                ok_rand = False
            lam = Fr(rnd.randint(-5, 5))
            dep = contract_field([lam * x for x in a],
                                 contract_field(a, point))
            if dep:
                ok_dep = False
        check("c=%d: (a ^ b) _| [pt] != 0 exactly when a, b are independent"
              % c, ok_coord and ok_rand and ok_dep,
              "all %d coordinate pairs, 25 random pairs, 25 dependent pairs"
              % comb(c, 2))


# ------------------------------------------------------- (C) the dichotomy
def nullspace_Q(rows, ncols):
    """basis of {v : r.v = 0 for all rows} over Q"""
    m = [list(r) for r in rows]
    pivots, R = [], []
    for r in m:
        r = r[:]
        for (p, pr) in zip(pivots, R):
            if r[p] != 0:
                f = r[p] / pr[p]
                r = [x - f * y for x, y in zip(r, pr)]
        nz = [i for i, x in enumerate(r) if x != 0]
        if nz:
            pivots.append(nz[0])
            R.append(r)
    # reduce to row echelon with pivots, then solve
    free = [j for j in range(ncols) if j not in pivots]
    basis = []
    for f in free:
        v = [Fr(0)] * ncols
        v[f] = Fr(1)
        for (p, pr) in reversed(list(zip(pivots, R))):
            s = sum(pr[j] * v[j] for j in range(ncols) if j != p)
            v[p] = -s / pr[p]
        basis.append(v)
    return basis


def mixed_wedges_vanish(W, n):
    """W: list of spanning vectors of a subspace of Q^{2n} = T_+ (+) T_-.
    Decide whether (t + W) ^ (t' + W) = 0 in wedge^2 (Q^{2n}/W) for all
    t in T_+, t' in T_-."""
    N = 2 * n
    # quotient map: choose a complement via the annihilator of W
    ann = nullspace_Q(W, N) if W else [[Fr(int(i == j)) for j in range(N)]
                                        for i in range(N)]
    # coordinates on the quotient are the functionals in ann
    def q(v):
        return [sum(f[i] * v[i] for i in range(N)) for f in ann]
    Tp = [q([Fr(int(i == j)) for j in range(N)]) for i in range(n)]
    Tm = [q([Fr(int(i == j)) for j in range(N)]) for i in range(n, N)]
    for u in Tp:
        for v in Tm:
            for i in range(len(ann)):
                for j in range(i + 1, len(ann)):
                    if u[i] * v[j] - u[j] * v[i] != 0:
                        return False
    return True


def contains(W, vecs, N):
    r0 = rank([{i: x for i, x in enumerate(w) if x} for w in W])
    r1 = rank([{i: x for i, x in enumerate(w) if x} for w in W + vecs])
    return r0 == r1


def item_C():
    rnd = random.Random(7)
    for n in (2, 3, 4):
        N = 2 * n
        e = [[Fr(int(i == j)) for j in range(N)] for i in range(N)]
        agree, trials = True, 0
        for c in range(2, N):
            for _ in range(12):
                dimW = N - c
                W = [[Fr(rnd.randint(-4, 4)) for _ in range(N)]
                     for _ in range(dimW)]
                if rank([{i: x for i, x in enumerate(w) if x} for w in W]) \
                        != dimW:
                    continue
                trials += 1
                lhs = mixed_wedges_vanish(W, n)
                rhs = contains(W, e[:n], N) or contains(W, e[n:], N)
                if lhs != rhs:
                    agree = False
            # boundary cases: W contains T_+ (or T_-) and has codim c
            for half in (e[:n], e[n:]):
                if N - c >= n:
                    extra = [[Fr(rnd.randint(-4, 4)) for _ in range(N)]
                             for _ in range(N - c - n)]
                    W = half + extra
                    if rank([{i: x for i, x in enumerate(w) if x}
                             for w in W]) == N - c:
                        trials += 1
                        if not mixed_wedges_vanish(W, n):
                            agree = False
        check("n=%d: mixed wedges vanish in the normal space iff it is "
              "cut out by a subspace containing T_+ or T_-" % n, agree,
              "%d subspaces of codimension >= 2" % trials)


# ------------------------------------------ (D) Gaussian rational model
class G:
    """a + b i with a, b rational"""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.a - o.a, s.b - o.b)

    def __neg__(s):
        return G(-s.a, -s.b)

    def __mul__(s, o):
        o = o if isinstance(o, G) else G(o)
        return G(s.a * o.a - s.b * o.b, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__

    def inv(s):
        n = s.a * s.a + s.b * s.b
        return G(s.a / n, -s.b / n)

    def __truediv__(s, o):
        o = o if isinstance(o, G) else G(o)
        return s * o.inv()

    def iszero(s):
        return s.a == 0 and s.b == 0


def g_nullspace(rows, ncols):
    R, piv = [], []
    for r in rows:
        r = list(r)
        for (p, pr) in zip(piv, R):
            if not r[p].iszero():
                f = r[p] / pr[p]
                r = [x - f * y for x, y in zip(r, pr)]
        nz = [i for i, x in enumerate(r) if not x.iszero()]
        if nz:
            piv.append(nz[0])
            R.append(r)
    free = [j for j in range(ncols) if j not in piv]
    basis = []
    for f in free:
        v = [G(0)] * ncols
        v[f] = G(1)
        for (p, pr) in reversed(list(zip(piv, R))):
            s = G(0)
            for j in range(ncols):
                if j != p:
                    s = s + pr[j] * v[j]
            v[p] = -(s / pr[p])
        basis.append(v)
    return basis


def g_rank(vecs):
    R, piv = [], []
    for r in vecs:
        r = list(r)
        for (p, pr) in zip(piv, R):
            if not r[p].iszero():
                f = r[p] / pr[p]
                r = [x - f * y for x, y in zip(r, pr)]
        nz = [i for i, x in enumerate(r) if not x.iszero()]
        if nz:
            piv.append(nz[0])
            R.append(r)
    return len(R)


def item_D():
    # R^{4n} = (R^2)^{2n}; on each R^2 the rotation j = [[0,-1],[1,0]].
    # J acts by j on every block; M acts by j on the first n blocks and by
    # -j on the last n, so M commutes with J, M^2 = -1, and on T^{1,0}
    # (the +i eigenspace of J) M has eigenvalue +i on n dimensions and -i on
    # n: signature (n,n).  A rational change of basis scrambles the blocks so
    # that nothing is diagonal in the coordinates used.
    for n in (1, 2):
        N = 4 * n
        J = [[G(0)] * N for _ in range(N)]
        M = [[G(0)] * N for _ in range(N)]
        for blk in range(2 * n):
            i = 2 * blk
            J[i][i + 1], J[i + 1][i] = G(-1), G(1)
            s = 1 if blk < n else -1
            M[i][i + 1], M[i + 1][i] = G(-s), G(s)
        rnd = random.Random(11 + n)
        while True:
            S = [[G(rnd.randint(-2, 2)) for _ in range(N)] for _ in range(N)]
            if g_rank(S) == N:
                break
        # S^{-1}
        aug = [S[i] + [G(int(i == j)) for j in range(N)] for i in range(N)]
        for c in range(N):
            p = next(r for r in range(c, N) if not aug[r][c].iszero())
            aug[c], aug[p] = aug[p], aug[c]
            f = aug[c][c].inv()
            aug[c] = [x * f for x in aug[c]]
            for r in range(N):
                if r != c and not aug[r][c].iszero():
                    g = aug[r][c]
                    aug[r] = [x - g * y for x, y in zip(aug[r], aug[c])]
        Si = [row[N:] for row in aug]

        def mm(A, B):
            return [[sum((A[i][k] * B[k][j] for k in range(N)), G(0))
                     for j in range(N)] for i in range(N)]

        J2, M2 = mm(mm(Si, J), S), mm(mm(Si, M), S)

        def eig(A, lam):
            rows = [[A[i][j] - (lam if i == j else G(0)) for j in range(N)]
                    for i in range(N)]
            return g_nullspace(rows, N)

        def inter(U, V):
            # U, V lists of vectors; intersection via nullspace of [U | -V]
            if not U or not V:
                return []
            cols = [[U[k][i] for k in range(len(U))] +
                    [-V[k][i] for k in range(len(V))] for i in range(N)]
            ns = g_nullspace(cols, len(U) + len(V))
            return [[sum((c[k] * U[k][i] for k in range(len(U))), G(0))
                     for i in range(N)] for c in ns]

        # tangent vectors: T^{1,0} = +i eigenspace of J; T_+ = M-eigenvalue +i
        I = G(0, 1)
        T10 = eig(J2, I)
        Tplus = inter(T10, eig(M2, I))
        # cotangent side: forms are row vectors, the action is the transpose
        JT = [[J2[j][i] for j in range(N)] for i in range(N)]
        MT = [[M2[j][i] for j in range(N)] for i in range(N)]
        H10 = eig(JT, I)
        H01 = eig(JT, -I)
        Vp10 = inter(H10, eig(MT, I))
        Vm10 = inter(H10, eig(MT, -I))
        Vp01 = inter(H01, eig(MT, I))
        Vm01 = inter(H01, eig(MT, -I))
        dims_ok = all(len(x) == n for x in (Tplus, Vp10, Vm10, Vp01, Vm01))
        # the real form of T_+ is ker(J - M) over R; its complexification is
        # spanned by T_+ and its complex conjugate
        Treal = g_nullspace([[J2[i][j] - M2[i][j] for j in range(N)]
                             for i in range(N)], N)
        ann = g_nullspace(Treal, N)       # forms vanishing on ker(J - M)
        target = Vm10 + Vp01
        same = (len(ann) == 2 * n and g_rank(target) == 2 * n and
                g_rank(ann + target) == 2 * n)
        check("n=%d: the forms vanishing on the real form of T_+ are exactly "
              "V_-^{1,0} (+) V_+^{0,1}" % n, dims_ok and same,
              "real dimension of T_+ is %d; annihilator of dimension %d"
              % (len(Treal), len(ann)))


# ------------------------------------------------- (E) monomial separation
def item_E():
    for n in range(2, 7):
        X = set(range(0, n))
        Y = set(range(n, 2 * n))
        XB = set(range(2 * n, 3 * n))
        YB = set(range(3 * n, 4 * n))
        mask = lambda s: sum(1 << i for i in s)
        allowed_p = mask(Y | XB)     # pulled back along A -> A/B, T_0B > T_+
        allowed_m = mask(X | YB)     # T_0B > T_-
        ap, am = mask(X | XB), mask(Y | YB)
        in_p = lambda m: (m & ~allowed_p) == 0
        in_m = lambda m: (m & ~allowed_m) == 0
        # the two subspaces are spanned by monomials, so the Weil line
        # a alpha_+ + b alpha_- (ab != 0) lies in their sum iff both
        # monomials alpha_+ and alpha_- do
        sep = not (in_p(ap) or in_m(ap)) and not (in_p(am) or in_m(am))
        # degree 2n parts: all 2n generators of each 2n-dim piece
        check("n=%d: the Weil line meets the classes pulled back from A/B_+ "
              "and A/B_- only in zero" % n, sep,
              "each subring has a one-dimensional degree 2n part, spanned by "
              "the class of a coset, and\nneither alpha_+ nor alpha_- is "
              "among the monomials either subring contains")


if __name__ == "__main__":
    print("(XXXIX) the numerical criterion and the support of a "
          "semiregular Weil object")
    print()
    print("  (A) the count")
    item_A()
    print("  (B) the class of a point on a c-dimensional torus")
    item_B()
    print("  (C) the dichotomy in the normal space")
    item_C()
    print("  (D) the eigenspace bookkeeping, in a real model")
    item_D()
    print("  (E) the monomial separation")
    item_E()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
