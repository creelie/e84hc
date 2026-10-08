#!/usr/bin/env python3
"""
cm_fields.py

Weil classes of a CM field of degree four: the base point, the explicit
representative, and the composite-field identity.  Item (XXXVI).

Everything is exact, in the number fields Q(zeta_5) and Q(zeta_8), with
elements stored as rational coordinate vectors and linear algebra done by
Gaussian elimination over the field.

  (A) F = Q(zeta_5), a cyclic quartic CM field with no imaginary quadratic
      subfield, n = 2, so g = 8.  V = F^4 with the hermitian form
      H = diag(1, 1, -1, -1) and the totally imaginary xi = zeta - zeta^{-1}.
      The CM point of the theorem "A base point in every family, for every
      CM field" has Hodge decomposition defined over F itself: V^{1,0} is the
      sum of the sigma-eigenspaces of F e_i for sigma in the CM type Phi_i,
      with Phi_1 = Phi_2 = {sigma_1, sigma_2} and Phi_3 = Phi_4 the conjugate
      type.  The script checks that V^{1,0} is eight-dimensional and isotropic
      for the polarisation E = Tr(xi H), that each eigenspace V_sigma meets it
      in dimension two, so the four Weil classes alpha_sigma = det V_sigma are
      of type (2,2); computes the Weil space W_F = wedge^4_F V as the rational
      points of the span of the alpha_sigma and finds it four-dimensional;
      computes the Neron-Severi space as the rational classes of type (1,1)
      and finds it of dimension 32; forms the balanced divisor classes
      delta_i(f) = sum_k (omega_k f e_i) ^ (omega_k^* e_{i'}) for dual bases
      of F with respect to the trace, checks they are of type (1,1); and
      verifies the representative

          w(f) = sum_k  delta_1(omega_k f) . delta_2(omega_k^*)

      lies in W_F for every f, is nonzero, and spans W_F as f runs over a
      basis of F: the Weil classes are polynomials in divisor classes at this
      point.  As a control it checks that the plain product delta_1 . delta_2
      is not in W_F, so the balanced sum is needed.

  (B) F = Q(zeta_8) = Q(i, sqrt 2), which contains K = Q(i), n = 1, g = 4.
      The Weil classes of F lie in H^2 and those of K in H^4.  The script
      checks that W_K = wedge^4_K V is contained in the span of the products
      of pairs of elements of W_F, which is the identity behind the
      proposition that the Weil classes of a composite field generate those
      of its imaginary quadratic subfield.

  (C) The same construction for six pairs (F, n), with F cyclotomic of degree
      four and six, so m = 2 and m = 3, and n = 1, 2, 3.  For each it checks
      that the CM type and its conjugate partition the embeddings, that
      zeta - zeta^{-1} is totally imaginary, that the trace-dual bases satisfy
      sum_k sigma(w_k) sigma'(w*_k) = delta over every pair of embeddings,
      that V^{1,0} is half-dimensional and isotropic for E = Tr(xi H) with
      H = diag(1,...,1,-1,...,-1), so the point lies in the period domain,
      that every eigenspace meets V^{1,0} in dimension n, that the balanced
      class delta_i(f) equals sum_sigma sigma(f) u_{i,sigma} ^ u_{i',sigma}
      and is therefore of type (1,1), that every alpha_sigma is nonzero, and
      that the balanced n-fold product of the delta_i is
      w(f) = sum_sigma sigma(f) alpha_sigma, rational, spanning W_F.
"""

import itertools
import sys
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


# ---------------------------------------------------------------- fields
class NumberField:
    """Q[x]/(p), p monic with rational coefficients, elements as tuples"""

    def __init__(self, coeffs):
        # p = x^d + coeffs[d-1] x^{d-1} + ... + coeffs[0]
        self.d = len(coeffs)
        self.p = [Fr(c) for c in coeffs]
        self.zero = tuple(Fr(0) for _ in range(self.d))
        self.one = tuple([Fr(1)] + [Fr(0)] * (self.d - 1))
        self.x = tuple([Fr(0), Fr(1)] + [Fr(0)] * (self.d - 2))

    def el(self, *cs):
        cs = [Fr(c) for c in cs] + [Fr(0)] * (self.d - len(cs))
        return tuple(cs[:self.d])

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def neg(self, a):
        return tuple(-x for x in a)

    def scal(self, c, a):
        return tuple(c * x for x in a)

    def mul(self, a, b):
        d = self.d
        prod = [Fr(0)] * (2 * d - 1)
        for i, x in enumerate(a):
            if x == 0:
                continue
            for j, y in enumerate(b):
                if y == 0:
                    continue
                prod[i + j] += x * y
        # reduce x^k for k >= d using x^d = -sum p_j x^j
        for k in range(2 * d - 2, d - 1, -1):
            c = prod[k]
            if c == 0:
                continue
            prod[k] = Fr(0)
            for j in range(d):
                prod[k - d + j] -= c * self.p[j]
        return tuple(prod[:d])

    def power(self, a, n):
        r = self.one
        for _ in range(n):
            r = self.mul(r, a)
        return r

    def is_zero(self, a):
        return all(x == 0 for x in a)

    def matrix_of_mult(self, a):
        """the d x d rational matrix of multiplication by a"""
        cols = []
        for j in range(self.d):
            e = tuple(Fr(1) if i == j else Fr(0) for i in range(self.d))
            cols.append(self.mul(a, e))
        return [[cols[j][i] for j in range(self.d)] for i in range(self.d)]

    def inv(self, a):
        M = self.matrix_of_mult(a)
        # solve M y = e_0
        n = self.d
        A = [row[:] + [Fr(1) if i == 0 else Fr(0)] for i, row in enumerate(M)]
        for c in range(n):
            piv = next(i for i in range(c, n) if A[i][c] != 0)
            A[c], A[piv] = A[piv], A[c]
            pv = A[c][c]
            A[c] = [x / pv for x in A[c]]
            for i in range(n):
                if i != c and A[i][c] != 0:
                    f = A[i][c]
                    A[i] = [x - f * y for x, y in zip(A[i], A[c])]
        return tuple(A[i][n] for i in range(n))

    def trace(self, a):
        M = self.matrix_of_mult(a)
        return sum(M[i][i] for i in range(self.d))

    def embed_poly(self, a, k):
        """the image of a under x -> x^k (an automorphism when it is one)"""
        r = self.zero
        xk = self.power(self.x, k)
        for i, c in enumerate(a):
            if c != 0:
                r = self.add(r, self.scal(c, self.power(xk, i)))
        return r


def rank_over(Fld, rows):
    """rank of a matrix with entries in Fld"""
    M = [list(r) for r in rows]
    if not M:
        return 0
    nr, nc = len(M), len(M[0])
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if not Fld.is_zero(M[i][c]):
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = Fld.inv(M[r][c])
        M[r] = [Fld.mul(inv, x) for x in M[r]]
        for i in range(nr):
            if i != r and not Fld.is_zero(M[i][c]):
                f = M[i][c]
                M[i] = [Fld.sub(x, Fld.mul(f, y)) for x, y in zip(M[i], M[r])]
        r += 1
        if r == nr:
            break
    return r


def rank_q(rows):
    M = [list(r) for r in rows]
    if not M:
        return 0
    nr, nc = len(M), len(M[0])
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
        if r == nr:
            break
    return r


def kernel_q(rows, ncols):
    """a basis of {v : rows . v = 0} over Q"""
    M = [list(r) for r in rows]
    nr = len(M)
    pivots = []
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, nr):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == nr:
            break
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fcol in free:
        v = [Fr(0)] * ncols
        v[fcol] = Fr(1)
        for i, pc in enumerate(pivots):
            v[pc] = -M[i][fcol]
        basis.append(v)
    return basis


# ------------------------------------------------------- exterior algebra
def wedge_basis(N, k):
    return list(itertools.combinations(range(N), k))


def sort_sign(idx):
    """sort a tuple of distinct indices, returning (sorted, sign)"""
    arr = list(idx)
    sgn = 1
    for i in range(len(arr)):
        for j in range(len(arr) - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                sgn = -sgn
    return tuple(arr), sgn


def wedge_mul(Fld, u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if set(a) & set(b):
                continue
            key, sgn = sort_sign(a + b)
            val = Fld.scal(Fr(sgn), Fld.mul(ca, cb))
            out[key] = Fld.add(out.get(key, Fld.zero), val)
            if Fld.is_zero(out[key]):
                del out[key]
    return out


def wedge_of_vectors(Fld, vecs):
    """the k-vector v_1 ^ ... ^ v_k as a dict {sorted index tuple: coeff},
    built by iterated sparse multiplication"""
    out = {(): Fld.one}
    for v in vecs:
        one = {(i,): c for i, c in enumerate(v) if not Fld.is_zero(c)}
        out = wedge_mul(Fld, out, one)
        if not out:
            return {}
    return out


def to_row(Fld, form, basis_index):
    row = [Fld.zero] * len(basis_index)
    for key, val in form.items():
        row[basis_index[key]] = val
    return row


# ------------------------------------------------------------------ (A)
def part_A():
    print("  (A) F = Q(zeta_5), n = 2: the CM base point and the representative")
    F = NumberField([1, 1, 1, 1])          # x^4 + x^3 + x^2 + x + 1
    d = 4
    z = F.x
    auts = {k: (lambda a, k=k: F.embed_poly(a, k)) for k in (1, 2, 3, 4)}
    # complex conjugation is k -> 5 - k
    conj = {1: 4, 2: 3, 3: 2, 4: 1}
    xi = F.sub(z, F.power(z, 4))             # zeta - zeta^{-1}, totally imaginary
    check("xi = zeta - zeta^{-1} is totally imaginary",
          F.is_zero(F.add(xi, auts[4](xi))))
    # V = F^4 over F, with Q-basis  omega_j e_i  (omega_j = zeta^j)
    twon = 4
    N = d * twon                              # 16
    omega = [F.power(z, j) for j in range(d)]
    # trace-dual basis omega^*: solve Tr(omega_j omega*_l) = delta_jl
    T = [[F.trace(F.mul(omega[j], omega[l])) for l in range(d)]
         for j in range(d)]
    # invert T over Q
    n_ = d
    A = [T[i][:] + [Fr(1) if i == j else Fr(0) for j in range(n_)]
         for i in range(n_)]
    for c in range(n_):
        piv = next(i for i in range(c, n_) if A[i][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for i in range(n_):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    Tinv = [row[n_:] for row in A]
    omega_star = []
    for l in range(d):
        s = F.zero
        for j in range(d):
            s = F.add(s, F.scal(Tinv[j][l], omega[j]))
        omega_star.append(s)
    check("the trace-dual basis satisfies Tr(omega_j omega*_l) = delta_jl",
          all(F.trace(F.mul(omega[j], omega_star[l])) == (1 if j == l else 0)
              for j in range(d) for l in range(d)))

    # coordinates: a vector of V (x) F is a list of 16 field elements, the
    # coefficient of omega_j e_i sitting at index 4 i + j.  The element
    # alpha in F acts on V by multiplication on each F e_i.
    def vec_F(i, a):
        """the vector a e_i, a in F, written in the Q-basis (over F)"""
        v = [F.zero] * N
        # a = sum_j a_j omega_j
        for j in range(d):
            v[d * i + j] = F.el(a[j])
        return v

    def act(alpha, v):
        """multiplication by alpha in F on V (x) F, F acting on the first
        factor: on coordinates, alpha . omega_j e_i = sum_l c_jl omega_l e_i
        where alpha omega_j = sum_l c_jl omega_l (rational c)"""
        out = [F.zero] * N
        for i in range(twon):
            for j in range(d):
                if F.is_zero(v[d * i + j]):
                    continue
                prod = F.mul(alpha, omega[j])       # rational coordinates
                for l in range(d):
                    if prod[l] != 0:
                        out[d * i + l] = F.add(out[d * i + l],
                                               F.scal(prod[l], v[d * i + j]))
        return out

    # the sigma_k eigenspace of F e_i inside (F e_i) (x) F: spanned by
    # u_{i,k} = sum_j omega*_j (x) sigma_k(omega_j) e_i ... we take the
    # vector with coordinates sigma_k(omega_j^*) at omega_j e_i
    def eigvec(i, k):
        v = [F.zero] * N
        for j in range(d):
            v[d * i + j] = auts[k](omega_star[j])
        return v

    ok = True
    for i in range(twon):
        for k in (1, 2, 3, 4):
            v = eigvec(i, k)
            w = act(z, v)
            w2 = [F.mul(auts[k](z), x) for x in v]
            ok = ok and all(F.is_zero(F.sub(a, b)) for a, b in zip(w, w2))
    check("the vectors u_{i,sigma} are eigenvectors of F for the embeddings",
          ok)

    # CM types: Phi_1 = Phi_2 = {sigma_1, sigma_2}, Phi_3 = Phi_4 = {3, 4}
    Phi = {0: (1, 2), 1: (1, 2), 2: (3, 4), 3: (3, 4)}
    V10 = [eigvec(i, k) for i in range(twon) for k in Phi[i]]
    V01 = [eigvec(i, k) for i in range(twon) for k in (1, 2, 3, 4)
           if k not in Phi[i]]
    check("V^{1,0} has dimension 8 over F", rank_over(F, V10) == 8)

    # the polarisation E(x,y) = Tr(xi H(x,y)), H = diag(1,1,-1,-1), computed
    # on V (x) F by F-bilinear extension of the rational form
    a_diag = [1, 1, -1, -1]

    def E_pair(v, w):
        # E(omega_j e_i, omega_l e_i') = delta_{ii'} a_i Tr(xi omega_j conj(omega_l))
        tot = F.zero
        for i in range(twon):
            for j in range(d):
                if F.is_zero(v[d * i + j]):
                    continue
                for l in range(d):
                    if F.is_zero(w[d * i + l]):
                        continue
                    c = a_diag[i] * F.trace(F.mul(F.mul(xi, omega[j]),
                                                  auts[4](omega[l])))
                    if c != 0:
                        tot = F.add(tot, F.scal(c, F.mul(v[d * i + j],
                                                         w[d * i + l])))
        return tot

    check("V^{1,0} is isotropic for E = Tr(xi H)",
          all(F.is_zero(E_pair(v, w)) for v in V10 for w in V10))
    check("E is alternating on a spanning set",
          all(F.is_zero(F.add(E_pair(v, w), E_pair(w, v)))
              for v in V10 + V01 for w in V10 + V01))

    # the eigenspaces V_sigma and the Weil classes alpha_sigma
    B4 = wedge_basis(N, 4)
    idx4 = {S: t for t, S in enumerate(B4)}
    alpha = {}
    for k in (1, 2, 3, 4):
        vecs = [eigvec(i, k) for i in range(twon)]
        alpha[k] = wedge_of_vectors(F, vecs)
        inter = rank_over(F, vecs + V10) - 8
        # dim(V_sigma cap V^{1,0}) = dim V_sigma + dim V10 - dim(sum)
        # = 4 + 8 - rank
        if inter != 4 - 2:
            check("V_sigma_%d meets V^{1,0} in dimension 2" % k, False,
                  "rank of the sum is %d" % (inter + 8))
        else:
            check("V_sigma_%d meets V^{1,0} in dimension 2, so alpha_sigma "
                  "has type (2,2)" % k, True)
    # W_F: rational points of span_F(alpha_k).  Galois compatibility: the
    # coordinates of alpha_k are sigma_k applied to those of alpha_1 up to
    # the ordering of the wedge, so w_f = sum_k sigma_k(f) alpha_k is
    # rational.  We build W_F as these four vectors for f a basis of F and
    # check rationality.
    W_rows = []
    for f in omega:
        row = [F.zero] * len(B4)
        for k in (1, 2, 3, 4):
            cf = auts[k](f)
            for key, val in alpha[k].items():
                row[idx4[key]] = F.add(row[idx4[key]], F.mul(cf, val))
        W_rows.append(row)
    rational = all(all(x[1:] == (Fr(0),) * (d - 1) for x in row)
                   for row in W_rows)
    check("w_f = sum_sigma sigma(f) alpha_sigma is rational for f in a basis",
          rational)
    W_q = [[x[0] for x in row] for row in W_rows]
    check("W_F = wedge^4_F V has dimension 4 over Q", rank_q(W_q) == 4)

    # Neron-Severi: rational 2-forms of type (1,1).  T = V10 ^ V01 in
    # wedge^2 (V (x) F); a rational 2-form x lies in T iff x is in the span
    # over F; we compute the rational kernel of the projection to the
    # quotient by T, via a complement basis.
    B2 = wedge_basis(N, 2)
    idx2 = {S: t for t, S in enumerate(B2)}
    T_rows = []
    for v in V10:
        for w in V01:
            T_rows.append(to_row(F, wedge_of_vectors(F, [v, w]), idx2))
    check("V^{1,0} ^ V^{0,1} has dimension 64 over F",
          rank_over(F, T_rows) == 64)
    # reduce T_rows to echelon form to get pivot columns, then a rational
    # 2-form x is in T iff reducing x against the echelon rows leaves zero
    M = [list(r) for r in T_rows]
    nr, nc = len(M), len(M[0])
    r = 0
    pivots = []
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if not F.is_zero(M[i][c]):
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = F.inv(M[r][c])
        M[r] = [F.mul(inv, x) for x in M[r]]
        for i in range(nr):
            if i != r and not F.is_zero(M[i][c]):
                fct = M[i][c]
                M[i] = [F.sub(x, F.mul(fct, y)) for x, y in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
        if r == nr:
            break
    ech = M[:r]

    def residue(row):
        row = list(row)
        for i, pc in enumerate(pivots):
            if not F.is_zero(row[pc]):
                fct = row[pc]
                row = [F.sub(x, F.mul(fct, y)) for x, y in zip(row, ech[i])]
        return row

    # the condition "residue(x) = 0" is F-linear in x; for rational x it is a
    # system of rational linear equations: residue of the basis 2-forms
    res_basis = [residue(to_row(F, {S: F.one}, idx2)) for S in B2]
    # each residue is a vector of field elements; flatten to rational rows
    eqs = []
    for col in range(len(B2)):
        for comp in range(d):
            eqs.append([res_basis[t][col][comp] for t in range(len(B2))])
    NS = kernel_q(eqs, len(B2))
    check("the Neron-Severi space at the CM point has dimension 32",
          len(NS) == 32)

    # the balanced divisor classes delta_i(f)
    def delta(i, ip, f):
        form = {}
        for k in range(d):
            u = vec_F(i, F.mul(omega[k], f))
            v = vec_F(ip, omega_star[k])
            w2 = wedge_of_vectors(F, [u, v])
            for key, val in w2.items():
                form[key] = F.add(form.get(key, F.zero), val)
                if F.is_zero(form[key]):
                    del form[key]
        return form

    def in_span_q(form, span_rows):
        row = [x[0] for x in to_row(F, form, idx2)]
        assert all(all(c == 0 for c in x[1:]) for x in to_row(F, form, idx2))
        return rank_q(span_rows + [row]) == rank_q(span_rows)

    d1 = delta(0, 2, F.one)
    d2 = delta(1, 3, F.one)
    check("delta_1(1) and delta_2(1) are rational classes of type (1,1)",
          in_span_q(d1, NS) and in_span_q(d2, NS))
    # F acts on D_{11'} through the first factor: check z . delta_1(1) =
    # delta_1(z), multiplication by z on the e_1 coordinates of delta_1(1)
    # we verify delta(0,2,z) equals the form obtained by acting with z on
    # the e_1 coordinates of delta(0,2,1)
    act_form = {}
    for k in range(d):
        u = act(z, vec_F(0, omega[k]))
        v = vec_F(2, omega_star[k])
        for key, val in wedge_of_vectors(F, [u, v]).items():
            act_form[key] = F.add(act_form.get(key, F.zero), val)
            if F.is_zero(act_form[key]):
                del act_form[key]
    same = set(act_form) == set(delta(0, 2, z)) and all(
        F.is_zero(F.sub(act_form[k], delta(0, 2, z)[k])) for k in act_form)
    check("F acts on the balanced classes: zeta . delta_1(1) = delta_1(zeta)",
          same)

    # the representative w(f) = sum_k delta_1(omega_k f) . delta_2(omega*_k)
    def wrep(f):
        form = {}
        for k in range(d):
            p = wedge_mul(F, delta(0, 2, F.mul(omega[k], f)),
                          delta(1, 3, omega_star[k]))
            for key, val in p.items():
                form[key] = F.add(form.get(key, F.zero), val)
                if F.is_zero(form[key]):
                    del form[key]
        return form

    w_rows = []
    for f in omega:
        w = wrep(f)
        row = to_row(F, w, idx4)
        assert all(all(c == 0 for c in x[1:]) for x in row)
        w_rows.append([x[0] for x in row])
    in_W = all(rank_q(W_q + [row]) == 4 for row in w_rows)
    check("w(f) lies in W_F for f in a basis of F", in_W)
    check("w(1) is nonzero and the w(f) span W_F",
          any(x != 0 for x in w_rows[0]) and rank_q(w_rows) == 4)
    plain = wedge_mul(F, d1, d2)
    prow = [x[0] for x in to_row(F, plain, idx4)]
    check("control: the plain product delta_1 . delta_2 is not in W_F",
          rank_q(W_q + [prow]) == 5)


# ------------------------------------------------------------------ (B)
def part_B():
    print("  (B) F = Q(zeta_8) containing K = Q(i), n = 1: products of Weil "
          "classes")
    F = NumberField([1, 0, 0, 0])            # x^4 + 1
    d = 4
    z = F.x
    auts = {k: (lambda a, k=k: F.embed_poly(a, k)) for k in (1, 3, 5, 7)}
    i_el = F.power(z, 2)                     # zeta_8^2 = i
    check("zeta_8^2 squares to -1", F.is_zero(F.add(F.mul(i_el, i_el), F.one)))
    twon = 2
    N = d * twon                             # 8
    omega = [F.power(z, j) for j in range(d)]

    def eigvec(i, k):
        # sigma_k eigenvector of F e_i: coordinates sigma_k(omega*_j); for the
        # power basis of Q(zeta_8), a dual basis is (1, z^{-1}, z^{-2}, z^{-3})/4
        v = [F.zero] * N
        for j in range(d):
            v[d * i + j] = F.scal(Fr(1, 4), auts[k](F.power(z, (8 - j) % 8)))
        return v

    # K = Q(i) embeddings: i -> i is {sigma_1, sigma_5} (zeta^2 -> zeta^2 or
    # zeta^{10} = zeta^2), i -> -i is {sigma_3, sigma_7}
    B2 = wedge_basis(N, 2)
    B4 = wedge_basis(N, 4)
    idx2 = {S: t for t, S in enumerate(B2)}
    idx4 = {S: t for t, S in enumerate(B4)}
    alphaF = {k: wedge_of_vectors(F, [eigvec(0, k), eigvec(1, k)])
              for k in (1, 3, 5, 7)}
    # K-eigenspaces: V_{tau} = V_{sigma_1} + V_{sigma_5}, four-dimensional
    alphaK = {}
    for tau, ks in (("+", (1, 5)), ("-", (3, 7))):
        vecs = [eigvec(i, k) for k in ks for i in range(twon)]
        alphaK[tau] = wedge_of_vectors(F, vecs)
    prod15 = wedge_mul(F, alphaF[1], alphaF[5])
    # alphaK["+"] should be proportional to alphaF[1] ^ alphaF[5]
    rows = [to_row(F, alphaK["+"], idx4), to_row(F, prod15, idx4)]
    check("the K-Weil class of the place i -> i is the product of the two "
          "F-Weil classes above it", rank_over(F, rows) == 1)
    prod37 = wedge_mul(F, alphaF[3], alphaF[7])
    rows = [to_row(F, alphaK["-"], idx4), to_row(F, prod37, idx4)]
    check("and likewise for the place i -> -i", rank_over(F, rows) == 1)
    # rational statement: W_K (2-dim over Q) lies in the span of products of
    # pairs from W_F (4-dim over Q)
    WF_rows = []
    for f in omega:
        row = [F.zero] * len(B2)
        for k in (1, 3, 5, 7):
            cf = auts[k](f)
            for key, val in alphaF[k].items():
                row[idx2[key]] = F.add(row[idx2[key]], F.mul(cf, val))
        assert all(all(c == 0 for c in x[1:]) for x in row)
        WF_rows.append([x[0] for x in row])
    check("W_F has dimension 4 over Q", rank_q(WF_rows) == 4)
    WK_rows = []
    for f in (F.one, i_el):
        row = [F.zero] * len(B4)
        for tau, ks in (("+", (1, 5)), ("-", (3, 7))):
            # sigma(f) for f in K is constant on the pair
            cf = auts[ks[0]](f)
            for key, val in alphaK[tau].items():
                row[idx4[key]] = F.add(row[idx4[key]], F.mul(cf, val))
        assert all(all(c == 0 for c in x[1:]) for x in row)
        WK_rows.append([x[0] for x in row])
    check("W_K has dimension 2 over Q", rank_q(WK_rows) == 2)
    # products of pairs of the rational basis of W_F
    forms = []
    for row in WF_rows:
        forms.append({B2[t]: F.el(row[t]) for t in range(len(B2)) if row[t] != 0})
    prods = []
    for a in range(4):
        for b in range(a, 4):
            p = wedge_mul(F, forms[a], forms[b])
            prods.append([x[0] for x in to_row(F, p, idx4)])
    rk = rank_q(prods)
    check("W_K lies in the span of the products of pairs of W_F",
          rank_q(prods + WK_rows) == rk,
          "the products span a space of dimension %d containing W_K" % rk)


# ------------------------------------------------------------------ (C)
def part_C():
    print("  (C) the base point for a general CM field: the closed forms")
    # (cyclotomic index, degree, the CM type as exponents, n, label)
    CASES = [
        (5, 4, (1, 2), 2, "Q(zeta_5), m=2, n=2"),
        (5, 4, (1, 2), 3, "Q(zeta_5), m=2, n=3"),
        (8, 4, (1, 3), 2, "Q(zeta_8), m=2, n=2"),
        (7, 6, (1, 2, 3), 2, "Q(zeta_7), m=3, n=2"),
        (7, 6, (1, 2, 3), 1, "Q(zeta_7), m=3, n=1"),
        (9, 6, (1, 2, 4), 2, "Q(zeta_9), m=3, n=2"),
    ]
    for r, d, PhiExp, n, label in CASES:
        # the r-th cyclotomic polynomial, for r = 5, 7, 8, 9
        if r in (5, 7):
            poly = [1] * r if False else [1] * (r - 1)
        elif r == 8:
            poly = [1, 0, 0, 0]
        elif r == 9:
            poly = [1, 0, 0, 1, 0, 0]
        F = NumberField(poly)
        z = F.x
        assert F.d == d
        # the automorphisms x -> x^k, k prime to r
        units = [k for k in range(1, r) if gcd(k, r) == 1]
        auts = {k: (lambda a, k=k: F.embed_poly(a, k)) for k in units}
        conj = {k: (r - k) % r for k in units}
        Phi = list(PhiExp)
        Phibar = [conj[k] for k in Phi]
        check("%s: the CM type and its conjugate partition the embeddings"
              % label,
              sorted(Phi + Phibar) == sorted(units) and len(Phi) == d // 2)
        # xi = zeta - zeta^{-1} is totally imaginary
        xi = F.sub(z, F.power(z, r - 1))
        check("%s: xi = zeta - zeta^{-1} is totally imaginary" % label,
              F.is_zero(F.add(xi, auts[conj[1]](xi))))
        omega = [F.power(z, j) for j in range(d)]
        T = [[F.trace(F.mul(omega[j], omega[l])) for l in range(d)]
             for j in range(d)]
        Tinv = inverse_q(T)
        omega_star = []
        for l in range(d):
            e = F.zero
            for j in range(d):
                e = F.add(e, F.scal(Tinv[j][l], omega[j]))
            omega_star.append(e)
        check("%s: the trace-dual basis is dual" % label,
              all(F.trace(F.mul(omega[j], omega_star[l]))
                  == (1 if j == l else 0)
                  for j in range(d) for l in range(d)))
        # trace duality across the embeddings: sum_k sigma(w_k) sigma'(w*_k)
        # = delta_{sigma sigma'}
        ok = True
        for a in units:
            for b in units:
                tot = F.zero
                for k in range(d):
                    tot = F.add(tot, F.mul(auts[a](omega[k]),
                                           auts[b](omega_star[k])))
                want = F.one if a == b else F.zero
                ok = ok and F.is_zero(F.sub(tot, want))
        check("%s: sum_k sigma(w_k) sigma'(w*_k) = delta, over all pairs of "
              "embeddings" % label, ok)

        twon = 2 * n
        N = d * twon

        def vec_F(i, a):
            v = [F.zero] * N
            for j in range(d):
                v[d * i + j] = F.el(a[j])
            return v

        def eigvec(i, k):
            v = [F.zero] * N
            for j in range(d):
                v[d * i + j] = auts[k](omega_star[j])
            return v

        PhiI = {i: (Phi if i < n else Phibar) for i in range(twon)}
        V10 = [eigvec(i, k) for i in range(twon) for k in PhiI[i]]
        V01 = [eigvec(i, k) for i in range(twon) for k in units
               if k not in PhiI[i]]
        check("%s: V^{1,0} has dimension %d, half of %d"
              % (label, N // 2, N),
              rank_over(F, V10) == N // 2 and len(V10) == N // 2)
        # the polarisation E = Tr(xi H) with H = diag(1,..,1,-1,..,-1)
        a_diag = [1] * n + [-1] * n

        def E_pair(v, w):
            tot = F.zero
            for i in range(twon):
                for j in range(d):
                    if F.is_zero(v[d * i + j]):
                        continue
                    for l in range(d):
                        if F.is_zero(w[d * i + l]):
                            continue
                        c = a_diag[i] * F.trace(
                            F.mul(F.mul(xi, omega[j]),
                                  auts[conj[1]](omega[l])))
                        if c != 0:
                            tot = F.add(tot, F.scal(c, F.mul(v[d * i + j],
                                                             w[d * i + l])))
            return tot
        check("%s: V^{1,0} is isotropic for E = Tr(xi H), so the point lies "
              "in the period domain" % label,
              all(F.is_zero(E_pair(v, w)) for v in V10 for w in V10))
        # each eigenspace meets V^{1,0} in dimension n: signature (n,n)
        okdim = True
        for k in units:
            vecs = [eigvec(i, k) for i in range(twon)]
            rk = rank_over(F, vecs + V10)
            okdim = okdim and (twon + N // 2 - rk == n)
        check("%s: every eigenspace meets V^{1,0} in dimension n = %d, so the "
              "Weil classes have type (n,n)" % (label, n), okdim)

        # the balanced divisor classes and the closed form
        def delta(i, ip, f):
            form = {}
            for k in range(d):
                u = vec_F(i, F.mul(omega[k], f))
                v = vec_F(ip, omega_star[k])
                for key, val in wedge_of_vectors(F, [u, v]).items():
                    form[key] = F.add(form.get(key, F.zero), val)
                    if F.is_zero(form[key]):
                        del form[key]
            return form

        def closed(i, ip, f):
            form = {}
            for k in units:
                cf = auts[k](f)
                for key, val in wedge_of_vectors(
                        F, [eigvec(i, k), eigvec(ip, k)]).items():
                    form[key] = F.add(form.get(key, F.zero),
                                      F.mul(cf, val))
                    if F.is_zero(form[key]):
                        del form[key]
            return form

        okd = True
        for f in (F.one, z):
            for i in range(n):
                A1, B1 = delta(i, i + n, f), closed(i, i + n, f)
                okd = okd and set(A1) == set(B1) and all(
                    F.is_zero(F.sub(A1[k], B1[k])) for k in A1)
        check("%s: delta_i(f) = sum_sigma sigma(f) u_{i,sigma} ^ u_{i',sigma}, "
              "so it is of type (1,1)" % label, okd)

        # the Weil classes: w(f) = the balanced n-fold product
        def wrep(f):
            form = {}
            for ks in itertools.product(range(d), repeat=n - 1):
                term = delta(0, n, F.mul(omega[ks[0]], f)) if n > 1 \
                    else delta(0, n, f)
                for j in range(1, n):
                    left = omega_star[ks[j - 1]]
                    right = omega[ks[j]] if j < n - 1 else F.one
                    term = wedge_mul(F, term,
                                     delta(j, j + n, F.mul(left, right)))
                    if not term:
                        break
                for key, val in term.items():
                    form[key] = F.add(form.get(key, F.zero), val)
                    if F.is_zero(form[key]):
                        del form[key]
            return form

        alpha = {k: wedge_of_vectors(
            F, [eigvec(i, k) for i in range(twon)]) for k in units}
        check("%s: every alpha_sigma is nonzero" % label,
              all(alpha[k] for k in units))

        def weil(f):
            form = {}
            for k in units:
                cf = auts[k](f)
                for key, val in alpha[k].items():
                    form[key] = F.add(form.get(key, F.zero), F.mul(cf, val))
                    if F.is_zero(form[key]):
                        del form[key]
            return form

        okw, okrat, rows = True, True, []
        for f in omega:
            W1, W2 = wrep(f), weil(f)
            # they agree up to a sign coming from the reordering, one sign
            # for the whole family
            sgn = None
            if set(W1) == set(W2) and W1:
                key = next(iter(W1))
                if not F.is_zero(W2[key]):
                    q = F.mul(W1[key], F.inv(W2[key]))
                    if q == F.one or F.is_zero(F.add(q, F.one)):
                        sgn = q
            okw = okw and sgn is not None and all(
                F.is_zero(F.sub(W1[k], F.mul(sgn, W2[k]))) for k in W1)
            row = []
            keys = sorted(set(W1) | set(W2))
            for k in keys:
                c = W1.get(k, F.zero)
                okrat = okrat and all(x == 0 for x in c[1:])
                row.append(c[0])
            rows.append(row)
        check("%s: the product of the n balanced classes is the Weil class, "
              "w(f) = sum_sigma sigma(f) alpha_sigma" % label, okw)
        check("%s: w(f) is rational and the w(f) span W_F, of dimension "
              "2m = %d" % (label, d),
              okrat and rank_q(rows) == d)


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def inverse_q(M):
    n = len(M)
    A = [list(M[i]) + [Fr(1) if i == j else Fr(0) for j in range(n)]
         for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [row[n:] for row in A]


def main():
    part_A()
    part_B()
    part_C()
    print("  cm_fields: %d passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
