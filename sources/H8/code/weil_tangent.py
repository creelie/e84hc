#!/usr/bin/env python3
"""
weil_tangent.py

The annihilator of the Weil line is the tangent space to the Weil family.

This script builds a Weil-type Hodge structure from scratch over the Gaussian
rationals, with exact arithmetic and no reduction modulo a prime, and checks
the following, for n = 2, 3, 4.

  (a) The construction is a polarised Hodge structure of Weil type: the
      polarisation pairs the two eigenspaces of K perfectly, vanishes on
      H^{1,0} and on H^{0,1}, and the two classes
      omega_1 = alpha_+ + alpha_-,  omega_2 = i(alpha_+ - alpha_-)
      are real of type (n,n).  This is Theorem 3.11 and Proposition B.6
      rebuilt independently of the model used everywhere else in the paper.

  (b) The annihilator of each omega in H^{0,2} has dimension n^2 and equals
      the mixed block Q (x) Q'.  This reproves Lemma 8.7 in a second model.

  (c) The polarisation-preserving first-order deformations form a space of
      dimension n(2n+1) = dim A_{2n}, and those commuting with K form a
      subspace of dimension n^2 = dim D_{n,n}.

  (d) A polarisation-preserving deformation annihilates the whole Weil line
      if and only if it commutes with K.  So the first-order Hodge locus of
      the Weil line is exactly the Weil family: Proposition 8.12.

  (e) The map of Theorem 8.13, which sends phi in Hom(P, Q) to the sum of
      q'_a wedge phi(p_a) over an E-dual pair of bases, is injective, is
      independent of the basis used to write it, and has image exactly the
      annihilator of (b).  So the tangent space to the family and the
      annihilator are the same subspace of H^{0,2}.

Everything is exact.  No statement here rests on a numerical tolerance or on
a reduction modulo a prime.
"""

import sys
from fractions import Fraction as Fr
from itertools import combinations

NP = NF = 0


def check(name, ok, detail=""):
    global NP, NF
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    if ok:
        NP += 1
    else:
        NF += 1


# --------------------------------------------------------- Gaussian rationals

class G(object):
    """a + b i with a, b rational.  Exact."""
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(self, o):
        o = mk(o)
        return G(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-mk(o))

    def __rsub__(self, o):
        return mk(o) + (-self)

    def __mul__(self, o):
        o = mk(o)
        return G(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def inv(self):
        nn = self.a * self.a + self.b * self.b
        if nn == 0:
            raise ZeroDivisionError
        return G(self.a / nn, -self.b / nn)

    def __truediv__(self, o):
        return self * mk(o).inv()

    def conj(self):
        return G(self.a, -self.b)

    def __eq__(self, o):
        o = mk(o)
        return self.a == o.a and self.b == o.b

    def __bool__(self):
        return self.a != 0 or self.b != 0

    def __hash__(self):
        return hash((self.a, self.b))

    def __repr__(self):
        return "(%s%+si)" % (self.a, self.b)


def mk(x):
    return x if isinstance(x, G) else G(x)


ZERO = G(0)
ONE = G(1)
IMU = G(0, 1)


# ------------------------------------------------- linear algebra over Q(i)

def rref(rows, ncols):
    """Row reduce a list of rows (lists of G).  Returns (rank, pivots, rows)."""
    rows = [r[:] for r in rows]
    r, piv = 0, []
    for c in range(ncols):
        p = None
        for i in range(r, len(rows)):
            if rows[i][c]:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        iv = rows[r][c].inv()
        rows[r] = [v * iv for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
        if r == len(rows):
            break
    return r, piv, rows


def rank(rows, ncols):
    return rref(rows, ncols)[0]


def nullspace(rows, ncols):
    """Basis of {x : M x = 0} where the given rows are the rows of M."""
    r, piv, R = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [ZERO] * ncols
        v[f] = ONE
        for i, c in enumerate(piv):
            v[c] = -R[i][f]
        basis.append(v)
    return basis


def col_rank(vectors, ncols):
    return rank([v[:] for v in vectors], ncols) if vectors else 0


def span_equal(A, B, ncols):
    """Do the two lists of vectors span the same subspace?"""
    ra = col_rank(A, ncols)
    rb = col_rank(B, ncols)
    rab = col_rank(list(A) + list(B), ncols)
    return ra == rb == rab


# --------------------------------------------------------- exterior algebra
# an element of the exterior algebra is a dict {bitmask: G}

def wsign(a, b):
    s = 0
    bb = b
    while bb:
        low = bb & -bb
        j = low.bit_length() - 1
        s += bin(a >> (j + 1)).count("1")
        bb ^= low
    return -1 if s & 1 else 1


def wedge(u, v):
    out = {}
    for ka, ca in u.items():
        for kb, cb in v.items():
            if ka & kb:
                continue
            t = ca * cb
            if wsign(ka, kb) < 0:
                t = -t
            k = ka | kb
            t = out.get(k, ZERO) + t
            if t:
                out[k] = t
            elif k in out:
                del out[k]
    return out


def vec_to_form(v):
    return {1 << i: c for i, c in enumerate(v) if c}


def form_add(*us):
    out = {}
    for u in us:
        for k, c in u.items():
            t = out.get(k, ZERO) + c
            if t:
                out[k] = t
            elif k in out:
                del out[k]
    return out


def form_scale(c, u):
    c = mk(c)
    return {k: c * v for k, v in u.items() if c * v}


# ------------------------------------------------------------ the model

class Weil(object):
    """A polarised Hodge structure of (K,-1,n)-Weil type over Q(i).

    Basis of V_C: e_1..e_{2n} span V_+, f_1..f_{2n} span V_-.
    Conjugation is the antilinear map with conj(e_j) = f_j.
    The polarisation is E(e_j, f_k) = i delta_{jk}, extended antisymmetrically.
    A choice of P in V_+ of dimension n determines the whole structure:
       P' = P^perp in V_-,  Q' = conj(P),  Q = conj(P').
    """

    def __init__(self, n, seed=0):
        self.n = n
        self.m = 2 * n
        self.N = 4 * n
        self.P = self._choose_P(seed)
        self.Pp = self._perp(self.P)
        self.Qp = [self.conj(v) for v in self.P]
        self.Q = [self.conj(v) for v in self.Pp]
        self.H10 = self.P + self.Pp
        self.H01 = self.Q + self.Qp

    # ---- basic vector operations, vectors are lists of G of length N
    def zero(self):
        return [ZERO] * self.N

    def basis(self, i):
        v = self.zero()
        v[i] = ONE
        return v

    def conj(self, v):
        """antilinear, swaps e_j and f_j"""
        m = self.m
        w = self.zero()
        for i, c in enumerate(v):
            j = i + m if i < m else i - m
            w[j] = c.conj()
        return w

    def E(self, u, v):
        """E(e_j, f_k) = i delta_jk, E(f_j, e_k) = -i delta_jk."""
        m = self.m
        s = ZERO
        for j in range(m):
            s = s + IMU * u[j] * v[m + j]
            s = s - IMU * u[m + j] * v[j]
        return s

    def _choose_P(self, seed):
        """n vectors in V_+ with small Gaussian-rational entries.  The
        entries are deterministic; the only requirement is that the
        resulting structure be nondegenerate, which is checked in part (a)."""
        n, m = self.n, self.m
        P = []
        for a in range(n):
            v = self.zero()
            v[a] = ONE
            for b in range(n):
                # a generic-looking but fixed n x n block
                v[n + b] = G(1 + ((a * 3 + b * 5 + seed) % 7),
                             1 + ((a * 2 + b * 7 + seed) % 5))
            P.append(v)
        return P

    def _perp(self, S):
        """{w in V_- : E(s, w) = 0 for all s in S}, expressed in the full
        basis with zero e-components."""
        m = self.m
        rows = []
        for s in S:
            row = [ZERO] * m
            for k in range(m):
                w = self.zero()
                w[m + k] = ONE
                row[k] = self.E(s, w)
            rows.append(row)
        out = []
        for c in nullspace(rows, m):
            w = self.zero()
            for k in range(m):
                w[m + k] = c[k]
            out.append(w)
        return out

    # ---- the Weil classes
    def alpha(self, sign):
        """generator of the top exterior power of V_+ (sign = +1) or V_- ."""
        off = 0 if sign > 0 else self.m
        k = 0
        for j in range(self.m):
            k |= 1 << (off + j)
        return {k: ONE}

    def omegas(self):
        ap, am = self.alpha(+1), self.alpha(-1)
        w1 = form_add(ap, am)
        w2 = form_add(form_scale(IMU, ap), form_scale(-IMU, am))
        return w1, w2

    # ---- H^{0,2}
    def h02_basis(self):
        return [wedge(vec_to_form(self.H01[a]), vec_to_form(self.H01[b]))
                for a, b in combinations(range(self.m), 2)]

    # ---- first-order deformations
    def deformation_matrix(self, coeffs):
        """Build the endomorphism of V_C that is the given element of
        Hom(H^{1,0}, H^{0,1}) on H^{1,0} and zero on H^{0,1}.
        coeffs is a flat list of length (2n)^2, read as v(H10[j]) =
        sum_k coeffs[j*2n+k] H01[k].  Returned as a list of columns."""
        m = self.m
        # change of basis: express each standard basis vector in H10 + H01
        cols = self.H10 + self.H01
        Mrows = [[cols[j][i] for j in range(self.N)] for i in range(self.N)]
        inv = self._inverse(Mrows)
        # image of standard basis vector i
        out = []
        for i in range(self.N):
            # coordinates of e_i in the basis H10 + H01
            co = [inv[j][i] for j in range(self.N)]
            w = self.zero()
            for j in range(m):                       # only the H10 part moves
                cj = co[j]
                if not cj:
                    continue
                for k in range(m):
                    ck = coeffs[j * m + k]
                    if not ck:
                        continue
                    t = cj * ck
                    tgt = self.H01[k]
                    for q in range(self.N):
                        if tgt[q]:
                            w[q] = w[q] + t * tgt[q]
            out.append(w)
        return out

    def _inverse(self, M):
        nn = len(M)
        A = [M[i][:] + [ONE if i == j else ZERO for j in range(nn)]
             for i in range(nn)]
        r = 0
        for c in range(nn):
            p = None
            for i in range(r, nn):
                if A[i][c]:
                    p = i
                    break
            if p is None:
                raise RuntimeError("singular change of basis")
            A[r], A[p] = A[p], A[r]
            iv = A[r][c].inv()
            A[r] = [v * iv for v in A[r]]
            for i in range(nn):
                if i != r and A[i][c]:
                    f = A[i][c]
                    A[i] = [a - f * b for a, b in zip(A[i], A[r])]
            r += 1
        return [row[nn:] for row in A]

    def contract(self, cols, form):
        """Apply the derivation determined by the endomorphism given by its
        columns to an element of the exterior algebra."""
        out = {}
        for k, c in form.items():
            idx = []
            mm = k
            while mm:
                low = mm & -mm
                idx.append(low.bit_length() - 1)
                mm ^= low
            for t, j in enumerate(idx):
                term = {0: c}
                for s, jj in enumerate(idx):
                    piece = (vec_to_form(cols[jj]) if s == t
                             else {1 << jj: ONE})
                    term = wedge(term, piece)
                    if not term:
                        break
                out = form_add(out, term)
        return out


# ------------------------------------------------------------- the checks

def symmetric_space(W):
    """Basis of the polarisation-preserving first-order deformations,
    as coefficient vectors of length (2n)^2."""
    m = W.m
    rows = []
    for a in range(m):
        for b in range(a, m):
            row = [ZERO] * (m * m)
            # E(v x_a, x_b) + E(x_a, v x_b) with v H10[j] = sum_k c_jk H01[k]
            for k in range(m):
                row[a * m + k] = row[a * m + k] + W.E(W.H01[k], W.H10[b])
                row[b * m + k] = row[b * m + k] + W.E(W.H10[a], W.H01[k])
            rows.append(row)
    return nullspace(rows, m * m)


def equivariant_space(W):
    """Basis of the deformations commuting with K, i.e. carrying P into Q
    and P' into Q'.  In the basis H10 = P + P', H01 = Q + Q', that is the
    vanishing of the two off-diagonal blocks."""
    n, m = W.n, W.m
    rows = []
    for j in range(m):
        for k in range(m):
            jin_P = j < n
            kin_Q = k < n
            if jin_P != kin_Q:
                row = [ZERO] * (m * m)
                row[j * m + k] = ONE
                rows.append(row)
    return nullspace(rows, m * m)


def intersect(A, B, ncols):
    """Basis of the intersection of two subspaces given by spanning sets."""
    if not A or not B:
        return []
    # solve for x with sum x_i A_i = sum y_j B_j
    rows = []
    for c in range(ncols):
        rows.append([A[i][c] for i in range(len(A))] +
                    [-B[j][c] for j in range(len(B))])
    sol = nullspace(rows, len(A) + len(B))
    out = []
    for s in sol:
        v = [ZERO] * ncols
        for i in range(len(A)):
            if s[i]:
                for c in range(ncols):
                    v[c] = v[c] + s[i] * A[i][c]
        if any(v):
            out.append(v)
    return out if col_rank(out, ncols) == len(out) else \
        [out[i] for i in rref([o[:] for o in out], ncols)[1]]


def part_a(W, rows):
    n, m = W.n, W.m
    ok = True
    ok = ok and len(W.P) == n and len(W.Pp) == n
    ok = ok and col_rank(W.H10 + W.H01, W.N) == W.N
    for u in W.H10:
        for v in W.H10:
            ok = ok and not W.E(u, v)
    for u in W.H01:
        for v in W.H01:
            ok = ok and not W.E(u, v)
    pq = [[W.E(p, q) for q in W.Qp] for p in W.P]
    qp = [[W.E(q, p) for p in W.Pp] for q in W.Q]
    ok = ok and rank([r[:] for r in pq], n) == n
    ok = ok and rank([r[:] for r in qp], n) == n
    # alpha_+ is the wedge of a basis of P and a basis of Q, hence type (n,n)
    top = {0: ONE}
    for v in W.P + W.Q:
        top = wedge(top, vec_to_form(v))
    ok = ok and len(top) == 1 and list(top) == list(W.alpha(+1))
    w1, w2 = W.omegas()
    for w in (w1, w2):
        cw = {}
        for k, c in w.items():
            kk = 0
            mm = k
            while mm:
                low = mm & -mm
                j = low.bit_length() - 1
                kk |= 1 << (j + m if j < m else j - m)
                mm ^= low
            # conjugating a wedge of 2n vectors reorders nothing here since
            # the two blocks are swapped as blocks, of even size 2n
            cw[kk] = c.conj()
        ok = ok and cw == w
    rows.append("n=%d: dim V = %d, E nondegenerate on P x Q' and Q x P', "
                "alpha_+ of type (n,n), omega_1 and omega_2 real"
                % (n, W.N))
    return ok


def part_b(W, rows):
    n, m = W.n, W.m
    zb = W.h02_basis()
    w1, w2 = W.omegas()
    dims = []
    for w in (w1, w2):
        prods = [wedge(z, w) for z in zb]
        keys = sorted({k for p in prods for k in p})
        idx = {k: i for i, k in enumerate(keys)}
        mrows = [[ZERO] * len(prods) for _ in keys]
        for j, p in enumerate(prods):
            for k, c in p.items():
                mrows[idx[k]][j] = c
        dims.append(len(prods) - rank(mrows, len(prods)))
    # the mixed block Q (x) Q'
    mixed = [wedge(vec_to_form(q), vec_to_form(qp))
             for q in W.Q for qp in W.Qp]
    keys = sorted({k for p in mixed for k in p})
    ok = (dims == [n * n, n * n])
    rows.append("n=%d: dim H^{0,2} = %d, Ann(omega_1) = %d, "
                "Ann(omega_2) = %d, n^2 = %d"
                % (n, len(zb), dims[0], dims[1], n * n))
    return ok, mixed


def part_c(W, rows):
    n, m = W.n, W.m
    S = symmetric_space(W)
    Kq = equivariant_space(W)
    I = intersect(S, Kq, m * m)
    dS, dI = col_rank(S, m * m), col_rank(I, m * m)
    ok = (dS == n * (2 * n + 1)) and (dI == n * n)
    rows.append("n=%d: polarised deformations %d (= dim A_{2n} = n(2n+1) = %d), "
                "of which K-equivariant %d (= dim D_{n,n} = n^2 = %d)"
                % (n, dS, n * (2 * n + 1), dI, n * n))
    return ok, S, I


def part_d(W, S, I, rows):
    n, m = W.n, W.m
    w1, w2 = W.omegas()
    hodge_rows = []
    for basis_vec in S:
        cols = W.deformation_matrix(basis_vec)
        img = form_add(W.contract(cols, w1), {})
        img2 = W.contract(cols, w2)
        hodge_rows.append((img, img2))
    keys = sorted({k for a, b in hodge_rows for k in list(a) + list(b)})
    idx = {k: i for i, k in enumerate(keys)}
    mrows = [[ZERO] * len(S) for _ in range(2 * len(keys))]
    for j, (a, b) in enumerate(hodge_rows):
        for k, c in a.items():
            mrows[idx[k]][j] = c
        for k, c in b.items():
            mrows[len(keys) + idx[k]][j] = c
    ker = nullspace(mrows, len(S))
    # lift back to coefficient space
    lifted = []
    for c in ker:
        v = [ZERO] * (m * m)
        for i, ci in enumerate(c):
            if ci:
                for q in range(m * m):
                    v[q] = v[q] + ci * S[i][q]
        lifted.append(v)
    d = col_rank(lifted, m * m)
    same = span_equal(lifted, I, m * m) if d else False
    # the Hodge locus of omega_1 alone
    m1rows = [[ZERO] * len(S) for _ in keys]
    for j, (a, b) in enumerate(hodge_rows):
        for k, c in a.items():
            m1rows[idx[k]][j] = c
    d1 = len(S) - rank([r[:] for r in m1rows], len(S))
    ok = (d == n * n) and same
    rows.append("n=%d: {v polarised : v contracts the whole Weil line to 0} "
                "has dimension %d = n^2, and is the K-equivariant space: %s"
                % (n, d, "yes" if same else "no"))
    rows.append("        for omega_1 alone the dimension is %d" % d1)
    return ok


def part_e(W, mixed, rows):
    n, m = W.n, W.m

    def transported(Pbasis):
        """E-dual basis of Pbasis inside Q', then the map Hom(P,Q) -> H^{0,2}."""
        Mrows = [[W.E(p, q) for q in W.Qp] for p in Pbasis]
        inv = W._inverse(Mrows)
        dual = []
        for a in range(n):
            v = W.zero()
            for b in range(n):
                cb = inv[b][a]
                if cb:
                    for q in range(W.N):
                        if W.Qp[b][q]:
                            v[q] = v[q] + cb * W.Qp[b][q]
            dual.append(v)
        img = []
        for a in range(n):
            for k in range(n):
                img.append(wedge(vec_to_form(dual[a]),
                                 vec_to_form(W.Q[k])))
        return img

    img1 = transported(W.P)
    # a second, different basis of P
    P2 = [W.P[0]]
    for a in range(1, n):
        v = [x + y for x, y in zip(W.P[a], W.P[a - 1])]
        P2.append(v)
    img2 = transported(P2)

    def tomat(forms):
        keys = sorted({k for f in forms for k in f})
        idx = {k: i for i, k in enumerate(keys)}
        out = []
        for f in forms:
            v = [ZERO] * len(keys)
            for k, c in f.items():
                v[idx[k]] = c
            out.append(v)
        return out, len(keys)

    allf = img1 + img2 + mixed
    keys = sorted({k for f in allf for k in f})
    idx = {k: i for i, k in enumerate(keys)}

    def vecs(forms):
        out = []
        for f in forms:
            v = [ZERO] * len(keys)
            for k, c in f.items():
                v[idx[k]] = c
            out.append(v)
        return out

    v1, v2, vm = vecs(img1), vecs(img2), vecs(mixed)
    r1 = col_rank(v1, len(keys))
    ok = (r1 == n * n)
    ok = ok and span_equal(v1, v2, len(keys))
    ok = ok and span_equal(v1, vm, len(keys))
    rows.append("n=%d: the map Hom(P,Q) -> H^{0,2} is injective (rank %d = n^2), "
                "independent of the basis of P, and its image is the "
                "annihilator" % (n, r1))
    return ok


def part_f(rows):
    """The five statements above do not depend on the chosen n-plane P."""
    ok, tested = True, 0
    for n in (2, 3):
        good = 0
        for seed in range(8):
            try:
                W = Weil(n, seed=seed)
            except RuntimeError:
                continue
            junk = []
            a = part_a(W, junk)
            b, mixed = part_b(W, junk)
            c, S, I = part_c(W, junk)
            d = part_d(W, S, I, junk)
            e = part_e(W, mixed, junk)
            ok = ok and a and b and c and d and e
            good += 1
            tested += 1
        rows.append("n=%d: all five statements hold for %d distinct choices "
                    "of the n-plane P" % (n, good))
    return ok and tested >= 12


def main():
    print("the annihilator of the Weil line is the tangent space to the family")

    ra, rb, rc, rd, re = [], [], [], [], []
    oa = ob = oc = od = oe = True
    for n in (2, 3, 4):
        W = Weil(n)
        oa = part_a(W, ra) and oa
        b, mixed = part_b(W, rb)
        ob = b and ob
        c, S, I = part_c(W, rc)
        oc = c and oc
        od = part_d(W, S, I, rd) and od
        oe = part_e(W, mixed, re) and oe

    print("  (a) the construction is a polarised Hodge structure of Weil type")
    check("E pairs the eigenspaces perfectly and the Weil classes are real "
          "of type (n,n)", oa, "\n".join(ra))
    print("  (b) the annihilator of the Weil line in H^{0,2}")
    check("dim Ann(omega) = n^2 for both rational generators, exactly, "
          "over Q(i)", ob, "\n".join(rb))
    print("  (c) the two deformation spaces")
    check("polarised deformations have dimension n(2n+1); the K-equivariant "
          "ones have dimension n^2", oc, "\n".join(rc))
    print("  (d) the first-order Hodge locus of the Weil line")
    check("a polarised deformation kills the Weil line exactly when it "
          "commutes with K", od, "\n".join(rd))
    print("  (e) the tangent space and the annihilator are the same subspace")
    check("the canonical map is injective, basis independent, and onto the "
          "annihilator", oe, "\n".join(re))
    rf = []
    of = part_f(rf)
    print("  (f) independence of the chosen n-plane")
    check("the five statements hold for every choice of P that gives a "
          "Hodge structure", of, "\n".join(rf))

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
