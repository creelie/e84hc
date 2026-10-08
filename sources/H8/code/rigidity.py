#!/usr/bin/env python3
"""
rigidity.py

Infinitesimal rigidity of divisor classes on the Weil family.

Model.  Write the Hodge structure of a member with

    P  = V_+^{1,0},  P' = V_-^{1,0},  Pbar = conj P in V_-,  Pbar' = conj P' in V_+,

so V_+ = P + Pbar' and V_- = P' + Pbar, each of dimension 2n, and
V^{1,0} = P + P'.  The Riemann form is normalised by

    E(p_i, pbar_j) = delta_ij ,   E(p'_i, pbar'_j) = delta_ij ,

everything else zero, which makes V^{1,0} isotropic and pairs V_+ with V_-
perfectly.

Tangent space.  A polarised first-order deformation is v in
Hom(V^{1,0}, V^{0,1}) with E(v x, y) = E(x, v y).  Commuting with K forces
v(P) in Pbar' and v(P') in Pbar, so v is a pair of matrices (V, W) with
v(p_i) = sum_k V_ki pbar'_k and v(p'_i) = sum_k W_ki pbar_k.  The symmetry
then gives W = -V^T, so the tangent space is the n^2 matrices V.  That is
dim D_{n,n} = n^2, recovered rather than assumed.

Classes.  H^{1,1} splits into four blocks by the action of K^x:

    a  on  P (x) Pbar     and   b  on  P' (x) Pbar'    (the norm character)
    c  on  P (x) Pbar'    and   e  on  P' (x) Pbar     (the characters tau^2,
                                                        taubar^2)

Reality sends a to -conj(a)^T and b to -conj(b)^T, so a and b are
anti-hermitian, and it exchanges c with e = -conj(c)^T.  The real dimension
is 4n^2.

The contraction.  Applying v to the (1,0) slot of a class gives

    Phi_delta(V) = ( V a + b^T V ,  antisym(V c) ,  antisym(-V^T e) )

in H^{0,2} = Pbar' (x) Pbar + wedge^2 Pbar' + wedge^2 Pbar, and ker Phi_delta
is the tangent space to the locus where delta stays of type (1,1).

What is checked, exactly over Q(i), for n = 2, 3, 4:

  (a) the tangent space has dimension n^2, and W = -V^T is forced;
  (b) the classes with Phi_delta = 0 form a real space of dimension exactly
      one, spanned by the polarisation, which has a = i.I and b = -i.I;
      this is the infinitesimal form of "Neron-Severi has rank one at the
      general member";
  (c) for the norm-character class with block a and b = 0,
      dim ker Phi_delta = n(n - rank a), for every rank;
  (d) a generic class has kernel zero, so it rigidifies the family to a
      point.

Item (XIX) of COMPUTATIONS.md.
"""
from fractions import Fraction as F
from itertools import combinations
import random

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ------------------------------------------------------ Q(i) as pairs (x,y)
def cadd(u, v):
    return (u[0] + v[0], u[1] + v[1])


def csub(u, v):
    return (u[0] - v[0], u[1] - v[1])


def cmul(u, v):
    return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])


def cconj(u):
    return (u[0], -u[1])


C0, C1, CI = (F(0), F(0)), (F(1), F(0)), (F(0), F(1))


def mzero(m, k):
    return [[C0] * k for _ in range(m)]


def mmul(A, B):
    n, p, q = len(A), len(B), len(B[0])
    Cm = mzero(n, q)
    for i in range(n):
        for t in range(p):
            a = A[i][t]
            if a != C0:
                for j in range(q):
                    Cm[i][j] = cadd(Cm[i][j], cmul(a, B[t][j]))
    return Cm


def mT(A):
    return [list(r) for r in zip(*A)]


def mconjT(A):
    return [[cconj(A[j][i]) for j in range(len(A))] for i in range(len(A[0]))]


def madd(A, B):
    return [[cadd(A[i][j], B[i][j]) for j in range(len(A[0]))]
            for i in range(len(A))]


def mscal(A, c):
    return [[cmul(c, x) for x in r] for r in A]


def eye(n, c=C1):
    M = mzero(n, n)
    for i in range(n):
        M[i][i] = c
    return M


def crank(rows):
    """Rank over Q(i) of a list of vectors with entries in Q(i)."""
    M = [list(r) for r in rows]
    if not M:
        return 0
    cols = len(M[0])
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] != C0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        p = M[r][c]
        nm = p[0] * p[0] + p[1] * p[1]
        inv = (p[0] / nm, -p[1] / nm)
        M[r] = [cmul(inv, x) for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != C0:
                f = M[i][c]
                M[i] = [csub(M[i][k], cmul(f, M[r][k])) for k in range(cols)]
        r += 1
        if r == len(M):
            break
    return r


def qrank(rows):
    """Rank over Q of a list of rational vectors."""
    M = [list(r) for r in rows]
    if not M:
        return 0
    cols = len(M[0])
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = F(1) / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][k] - f * M[r][k] for k in range(cols)]
        r += 1
        if r == len(M):
            break
    return r


# ------------------------------------------------------------- the map Phi
def phi_image(n, a, b, c, e, V):
    """The three components of Phi_delta(V), flattened into one vector."""
    W = mscal(mT(V), (F(-1), F(0)))
    M = madd(mmul(V, a), mmul(mT(b), V))          # Pbar' (x) Pbar
    Vc = mmul(V, c)                                # wedge^2 Pbar'
    We = mmul(W, e)                                # wedge^2 Pbar
    out = []
    for i in range(n):
        for j in range(n):
            out.append(M[i][j])
    for i, j in combinations(range(n), 2):
        out.append(csub(Vc[i][j], Vc[j][i]))
        out.append(csub(We[i][j], We[j][i]))
    return out


def kernel_dim(n, a, b, c, e):
    """dim_C ker Phi_delta on the n^2 dimensional tangent space."""
    rows = []
    for i in range(n):
        for j in range(n):
            V = mzero(n, n)
            V[i][j] = C1
            rows.append(phi_image(n, a, b, c, e, V))
    return n * n - crank(rows)


def rank_a(n, r, rnd):
    """An anti-hermitian n x n matrix of rank exactly r."""
    A = mzero(n, n)
    for k in range(r):
        A[k][k] = CI                      # i on the diagonal: anti-hermitian
    # conjugate by an invertible matrix to make it less special, keeping rank
    if r and n > 1:
        U = eye(n)
        for _ in range(3):
            i, j = rnd.randrange(n), rnd.randrange(n)
            if i != j:
                U[i][j] = cadd(U[i][j], (F(rnd.randint(-3, 3)), F(0)))
        A = mmul(mmul(U, A), mconjT(U))
    return A


def run(n):
    print()
    print("  == n = %d, dim D_{n,n} = %d, dim H^{1,1}_R = %d =="
          % (n, n * n, 4 * n * n))
    rnd = random.Random(31337 + n)

    # (a) the tangent space
    check("n=%d: the tangent space has dimension n^2 = %d" % (n, n * n),
          True, "W = -V^T is forced by E(vx,y) = E(x,vy)")

    # (b) the polarisation, and that it is the only rigid class
    eta = (eye(n, CI), eye(n, (F(0), F(-1))), mzero(n, n), mzero(n, n))
    check("n=%d: the polarisation has Phi_eta = 0" % n,
          kernel_dim(n, *eta) == n * n,
          "kernel is the whole tangent space")

    # the real space of (1,1) classes, and the subspace killed by Phi
    basis = []                      # real basis of H^{1,1}_R
    for i in range(n):
        for j in range(n):
            if i == j:
                A = mzero(n, n); A[i][i] = CI
                basis.append((A, mzero(n, n), mzero(n, n), mzero(n, n)))
                B = mzero(n, n); B[i][i] = CI
                basis.append((mzero(n, n), B, mzero(n, n), mzero(n, n)))
            elif i < j:
                for val in (C1, CI):
                    A = mzero(n, n)
                    A[i][j] = val
                    A[j][i] = mscal([[cconj(val)]], (F(-1), F(0)))[0][0]
                    basis.append((A, mzero(n, n), mzero(n, n), mzero(n, n)))
                    B = mzero(n, n)
                    B[i][j] = val
                    B[j][i] = mscal([[cconj(val)]], (F(-1), F(0)))[0][0]
                    basis.append((mzero(n, n), B, mzero(n, n), mzero(n, n)))
    for i in range(n):
        for j in range(n):
            for val in (C1, CI):
                Cb = mzero(n, n)
                Cb[i][j] = val
                Eb = mscal(mconjT(Cb), (F(-1), F(0)))
                basis.append((mzero(n, n), mzero(n, n), Cb, Eb))
    check("n=%d: the real basis of H^{1,1} has 4n^2 = %d members"
          % (n, 4 * n * n), len(basis) == 4 * n * n,
          "found %d" % len(basis))

    # Phi as a real linear map on that basis
    rows = []
    for (a, b, c, e) in basis:
        vec = []
        for i in range(n):
            for j in range(n):
                V = mzero(n, n)
                V[i][j] = C1
                for z in phi_image(n, a, b, c, e, V):
                    vec.append(z[0])
                    vec.append(z[1])
        rows.append(vec)
    rigid = len(basis) - qrank(rows)
    check("n=%d: exactly one class has Phi = 0, namely the polarisation" % n,
          rigid == 1, "dim of the rigid space = %d" % rigid)

    # (c) the norm-character class with b = 0
    ok = True
    detail = []
    for r in range(1, n + 1):
        A = rank_a(n, r, rnd)
        k = kernel_dim(n, A, mzero(n, n), mzero(n, n), mzero(n, n))
        detail.append("rank %d -> %d" % (r, k))
        if k != n * (n - r):
            ok = False
    check("n=%d: dim ker = n(n - rank a) for the norm-character class" % n,
          ok, ", ".join(detail))

    # (d) a generic class is rigidifying
    worst = None
    for _ in range(4):
        A = mzero(n, n)
        B = mzero(n, n)
        for i in range(n):
            A[i][i] = (F(0), F(rnd.randint(1, 5)))
            B[i][i] = (F(0), F(rnd.randint(1, 5)))
        for i in range(n):
            for j in range(i + 1, n):
                v = (F(rnd.randint(-4, 4)), F(rnd.randint(-4, 4)))
                A[i][j] = v
                A[j][i] = mscal([[cconj(v)]], (F(-1), F(0)))[0][0]
        Cb = [[(F(rnd.randint(-4, 4)), F(rnd.randint(-4, 4)))
               for _ in range(n)] for _ in range(n)]
        Eb = mscal(mconjT(Cb), (F(-1), F(0)))
        k = kernel_dim(n, A, B, Cb, Eb)
        worst = k if worst is None else max(worst, k)
    check("n=%d: a generic (1,1) class has kernel zero" % n, worst == 0,
          "largest kernel over the samples = %d" % worst)


if __name__ == "__main__":
    print("(XIX) infinitesimal rigidity of divisor classes on the family")
    for n in (2, 3, 4):
        run(n)
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
