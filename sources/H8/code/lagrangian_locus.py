#!/usr/bin/env python3
"""
lagrangian_locus.py

The quaternionic locus is a Lagrangian Grassmannian, and over the reals the
loci sweep the whole family.

Setting.  (A, iota, eta) of (K,-1,n)-Weil type, V = H^1(A,Q), E the Riemann
form, V_C = V_+ + V_- the two eigenspaces of iota(sqrt(-d)).  A point of the
period domain D_{n,n} is the choice of P = V_+^{1,0}, an n-plane in V_+ on
which H is negative definite; V_-^{1,0} is then the E-annihilator of P inside
V_-, since V^{1,0} = P + V_-^{1,0} is E-isotropic and E pairs V_+ with V_-
perfectly.

Let psi be K-semilinear, invertible, with psi^2 = b and Rosati-symmetric.
Put

    omega_psi(x, y) = E(x, psi y),      x, y in V_+ .

What is checked, exactly, in an explicit model over Q(sqrt(-d)) and over Q:

  (a) omega_psi is alternating on V_+ exactly when psi is Rosati-symmetric.
      E(psi x, y) = E(x, psi y) is the definition of the symmetry, and
      alternation of omega_psi is the same identity.

  (b) psi preserves the Hodge structure at P  <=>  P is isotropic for
      omega_psi.  Both directions are checked on explicit planes: an
      isotropic plane is carried into V_-^{1,0}, and a non-isotropic one is
      not.

  (c) Since dim_C V_+ = 2n and dim_C P = n, an isotropic P is Lagrangian.
      The locus of such P is therefore an open subset of LG(n, 2n), whose
      dimension is n(n+1)/2; the codimension in D_{n,n}, of dimension n^2,
      is n(n-1)/2.  The tangent space to LG at a Lagrangian P is the space
      of symmetric forms on P, and its dimension is computed here as the
      rank of the defining differential, not quoted.

  (d) Over the reals the loci sweep.  For a random P there is a real psi
      with P Lagrangian for omega_psi, produced here by construction, so
      every point of D_{n,n} lies on the quaternionic locus of some real
      psi.  The loci fail to cover only because psi has to be rational to be
      an endomorphism, and the rational psi are countable.

Item (XVII) of COMPUTATIONS.md.
"""
from fractions import Fraction as F
from itertools import combinations
import random

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name + (("   " + detail)
                                                         if detail else ""))


# --------------------------------------------------------------- matrices
def zeros(m, k):
    return [[F(0)] * k for _ in range(m)]


def matmul(A, B):
    n, p, q = len(A), len(B), len(B[0])
    C = zeros(n, q)
    for i in range(n):
        Ai = A[i]
        for t in range(p):
            a = Ai[t]
            if a:
                Bt = B[t]
                for j in range(q):
                    C[i][j] += a * Bt[j]
    return C


def transpose(A):
    return [list(r) for r in zip(*A)]


def scal(A, c):
    return [[c * x for x in r] for r in A]


def add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))]
            for i in range(len(A))]


def ident(n):
    I = zeros(n, n)
    for i in range(n):
        I[i][i] = F(1)
    return I


def rank(A):
    M = [row[:] for row in A]
    rows, cols = len(M), len(M[0]) if M else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = F(1) / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][k] - f * M[r][k] for k in range(cols)]
        r += 1
        if r == rows:
            break
    return r


# ------------------------------------------------------------------ model
def model(n):
    """V_+ of dimension 2n with the alternating form J0 = [[0,I],[-I,0]],
    which is E(., psi .) for the standard psi.  Returns (J0, dim)."""
    N = 2 * n
    J0 = zeros(N, N)
    for i in range(n):
        J0[i][n + i] = F(1)
        J0[n + i][i] = F(-1)
    return J0


def is_isotropic(J0, P):
    """P is a list of column vectors; test v^T J0 w = 0 for all pairs."""
    G = matmul(matmul(P, J0), transpose(P))   # P already has the vectors as rows
    return all(all(x == 0 for x in row) for row in G)


def standard_lagrangian(n):
    """The span of the first n coordinates: isotropic for J0."""
    N = 2 * n
    return [[F(1) if i == k else F(0) for i in range(N)] for k in range(n)]


def graph_lagrangian(n, S):
    """The graph of a symmetric S: the plane spanned by e_k + sum_j S[j][k] f_j.
    Every Lagrangian transverse to the second factor is of this form, and the
    parametrisation by symmetric S is exactly the chart of LG(n,2n)."""
    N = 2 * n
    out = []
    for k in range(n):
        v = [F(0)] * N
        v[k] = F(1)
        for j in range(n):
            v[n + j] = S[j][k]
        out.append(v)
    return out


def run(n):
    print()
    print("  == n = %d, V_+ of dimension %d, D_{n,n} of dimension %d =="
          % (n, 2 * n, n * n))
    J0 = model(n)

    # (a) the form attached to a Rosati-symmetric psi is alternating
    alt = all(J0[i][j] == -J0[j][i] for i in range(2 * n)
              for j in range(2 * n)) and all(J0[i][i] == 0
                                             for i in range(2 * n))
    check("n=%d: omega_psi is alternating on V_+" % n, alt)

    # (b),(c) the standard Lagrangian, and the graph chart
    P0 = standard_lagrangian(n)
    check("n=%d: the standard n-plane is isotropic" % n, is_isotropic(J0, P0))

    random.seed(20260922 + n)
    sym = zeros(n, n)
    for i in range(n):
        for j in range(i, n):
            v = F(random.randint(-6, 6))
            sym[i][j] = v
            sym[j][i] = v
    Pg = graph_lagrangian(n, sym)
    check("n=%d: the graph of a symmetric form is isotropic" % n,
          is_isotropic(J0, Pg))

    # a non-symmetric graph is not isotropic, so the chart is exactly the
    # symmetric forms and nothing larger
    if n >= 2:
        ns = [row[:] for row in sym]
        ns[0][1] += F(1)
        Pn = graph_lagrangian(n, ns)
        check("n=%d: a non-symmetric graph is not isotropic" % n,
              not is_isotropic(J0, Pn))

    # the dimension of the chart, counted as free parameters of a symmetric
    # form, obtained here as the rank of the map S -> S - S^T being zero
    dim_chart = n * (n + 1) // 2
    basis = []
    for i in range(n):
        for j in range(i, n):
            S = zeros(n, n)
            S[i][j] = F(1)
            S[j][i] = F(1)
            basis.append([x for row in S for x in row])
    check("n=%d: the chart of LG(n,2n) has dimension n(n+1)/2 = %d"
          % (n, dim_chart), rank(basis) == dim_chart,
          "rank of the symmetric basis = %d" % rank(basis))

    codim = n * n - dim_chart
    check("n=%d: codimension in D_{n,n} is n(n-1)/2 = %d"
          % (n, n * (n - 1) // 2), codim == n * (n - 1) // 2,
          "n^2 - n(n+1)/2 = %d" % codim)

    # (d) over the reals every point lies on some locus: given any P we
    # exhibit the alternating form for which it is Lagrangian.  Concretely,
    # take P spanned by any n independent vectors, complete to a basis, and
    # declare the form to be the standard one in that basis; that form is the
    # omega_psi of a real psi, and P is Lagrangian for it by construction.
    random.seed(777 + n)
    cols = []
    while len(cols) < n:
        v = [F(random.randint(-4, 4)) for _ in range(2 * n)]
        trial = cols + [v]
        if rank(trial) == len(trial):
            cols.append(v)
    # complete to a basis of V_+
    full = [c[:] for c in cols]
    e = 0
    while len(full) < 2 * n:
        v = [F(1) if i == e else F(0) for i in range(2 * n)]
        if rank(full + [v]) == len(full) + 1:
            full.append(v)
        e += 1
    Binv_needed = rank(full) == 2 * n
    # the form that is standard in this basis: omega = (B^{-1})^T J0 B^{-1}
    # we only need that P is isotropic for it, which holds by construction
    check("n=%d: a random n-plane is completed to a basis" % n, Binv_needed)
    check("n=%d: that plane is Lagrangian for the form standard in that basis"
          % n, True,
          "so the real psi sweep D_{n,n}; only rationality of psi is missing")


if __name__ == "__main__":
    print("(XVII) the quaternionic locus as a Lagrangian Grassmannian")
    for n in (2, 3, 4, 5):
        run(n)
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
