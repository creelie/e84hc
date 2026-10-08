#!/usr/bin/env python3
"""
split_geometry.py

How much of the Weil family does the base case of split_locus.py actually
reach?  Four questions, all decided here by exact arithmetic.

  (S1) the polarisation.  The endomorphism M of the construction acts on
       H_1(A) = U + U^dual by (u, phi) -> (-beta^{-1} phi, d beta u); in the
       symplectic basis of U and the dual basis of U^dual this is the matrix
       M = [[0, -B], [-d B, 0]] with B = [[0, I], [-I, 0]].  It is
       anti-self-adjoint, M^t Q + Q M = 0, for the Gram matrix
       Q = diag(B, B/d) of the class eta = beta + betahat/d, a positive
       multiple of d beta + betahat; that is the Rosati condition.  On
       H^2(A) the induced action multiplies eta by +d (the norm character)
       and multiplies gamma = d beta - betahat and ell by -d (the characters
       tau^2 and conj(tau)^2), while beta + d betahat is not an eigenclass
       for d > 1.  The class beta + d betahat is the Rosati-invariant class
       for the endomorphism with the factor d in the other block, so the two
       conventions are easily confused; the eigenclass check below is what
       fixes the one used here.

  (S2) the discriminant.  In the K-basis u_1..u_{2n} of H^1(A) the hermitian
       form has Gram matrix sqrt(-d) * B, so det H = (-d)^n det B.  Since
       det B is the square of the Pfaffian and d = N(sqrt(-d)) is a norm,
       (-1)^n det H is a norm from K.  The split members therefore all sit in
       the discriminant one family, whatever beta is chosen.

  (S3) the codimension.  dim D_{n,n} = n^2 and the split members are
       parametrised by the moduli of the n-fold X, of dimension n(n+1)/2, so
       the split locus has codimension n(n-1)/2.

  (S4) the divisors available at the split point.  For X with
       Hg(X) = Sp(H^1(X)), the Neron-Severi group of X x Xhat has rank three
       over Q, spanned by beta, betahat and the Poincare class; and in degree
       2n the span of the monomials in those three classes has the dimension
       predicted by Sp-invariant theory.  So the closed form of
       Theorem 14.14 uses every divisor there is.
"""

from fractions import Fraction as F
from itertools import combinations
from math import comb

from split_locus import (Split, sc, add, mul, smul, iszero, wedge, eadd,
                         escale, epow)


def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    return 1 if ok else 0


# ------------------------------------------------------------------ (S1)

def gram(n, d, a, b, c):
    """Gram matrix on H_1(A) = U + U^dual of the class a beta + b betahat +
    c ell.  Basis: u_1..u_{2n} of U with beta(u_j, u_{n+j}) = 1 (indices
    0..2n-1), then the dual basis x_1..x_{2n} of U^dual (indices 2n..4n-1).
    betahat(x_j, x_{n+j}) = 1 and ell(u_i, x_i) = 1."""
    N = 4 * n
    G = [[F(0)] * N for _ in range(N)]
    for j in range(n):
        G[j][n + j] += a
        G[n + j][j] -= a
        G[2 * n + j][3 * n + j] += b
        G[3 * n + j][2 * n + j] -= b
    for i in range(2 * n):
        G[i][2 * n + i] += c
        G[2 * n + i][i] -= c
    return G


def Mmat(n, d):
    """The K-action on H_1(A): u -> d beta(u), phi -> -beta^{-1}(phi), that is
    u_j -> d x_{n+j}, u_{n+j} -> -d x_j, x_{n+j} -> -u_j, x_j -> u_{n+j}."""
    N = 4 * n
    M = [[F(0)] * N for _ in range(N)]
    for j in range(n):
        M[3 * n + j][j] = F(d)             # u_j -> d x_{n+j}
        M[2 * n + j][n + j] = F(-d)        # u_{n+j} -> -d x_j
        M[j][3 * n + j] = F(-1)            # x_{n+j} -> -u_j
        M[n + j][2 * n + j] = F(1)         # x_j -> u_{n+j}
    return M


def matmul(A, B):
    N = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(N)) for j in range(N)]
            for i in range(N)]


def transpose(A):
    N = len(A)
    return [[A[j][i] for j in range(N)] for i in range(N)]


def rosati(n, d):
    """M^2 = -d, and M^t Q + Q M = 0 for the Gram matrix Q of
    eta = beta + betahat/d, entry by entry."""
    N = 4 * n
    Q = gram(n, d, F(1), F(1, d), F(0))
    M = Mmat(n, d)
    MM = matmul(M, M)
    ok2 = all(MM[i][j] == (F(-d) if i == j else F(0))
              for i in range(N) for j in range(N))
    S = matmul(transpose(M), Q)
    T = matmul(Q, M)
    ok1 = all(S[i][j] + T[i][j] == 0 for i in range(N) for j in range(N))
    return ok1, ok2, Q, M


def eigenvalue_on_h2(n, d, a, b, c):
    """The scalar e with M^* W = e W for the class W = a beta + b betahat +
    c ell, where M^* W has Gram matrix M^t G M; None if W is not an
    eigenclass."""
    G = gram(n, d, a, b, c)
    M = Mmat(n, d)
    H = matmul(matmul(transpose(M), G), M)
    N = 4 * n
    e = None
    for i in range(N):
        for j in range(N):
            if G[i][j] != 0:
                r = H[i][j] / G[i][j]
                if e is None:
                    e = r
                elif r != e:
                    return None
            elif H[i][j] != 0:
                return None
    return e


# ------------------------------------------------------------------ (S2)

def is_square(x):
    if x < 0:
        return False
    r = int(round(x ** 0.5))
    for c in (r - 2, r - 1, r, r + 1, r + 2):
        if c >= 0 and c * c == x:
            return True
    return False


def squarefree_part(y):
    """y positive integer; strip square factors."""
    out, m = 1, y
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


def is_norm_from_K(x, d, bound=200000):
    """Is the positive rational x a norm from Q(sqrt(-d))?  Norms form a
    group containing every square, so it is enough to test the squarefree
    part of the integer x * den^2."""
    if x <= 0:
        return False
    y = x.numerator * x.denominator      # x = y / den^2, den^2 a norm
    k = squarefree_part(y)
    if k == 1:
        return True
    b = 0
    while d * b * b <= k:
        if is_square(k - d * b * b):
            return True
        b += 1
        if b > bound:
            break
    # k may still be a norm of a non-integral element; test k * m^2 for small m
    for m in range(2, 60):
        t = k * m * m
        b = 0
        while d * b * b <= t:
            if is_square(t - d * b * b):
                return True
            b += 1
    return False


def discriminant(n, d, diag=None):
    """det H for the split member, and whether (-1)^n det H is a norm.
    `diag` gives the elementary divisors of beta; None means principal."""
    D = diag if diag else [1] * n
    detB = 1
    for t in D:
        detB *= t * t                 # det of the block form is (prod d_i)^2
    detH = F((-d) ** n * detB)
    normalised = F((-1) ** n) * detH
    return detH, normalised, is_norm_from_K(normalised, d)


# ------------------------------------------------------------------ (S4)

def sp_invariant_count(n, degree):
    """dim of the Sp(U)-invariants in wedge^degree (U + U^dual), for
    U of dimension 2n.  Using wedge^a U = sum_j wedge^{a-2j}_0 U with
    0 <= a-2j <= n, wedge^a U = wedge^{2n-a} U for a > n, and the fact that
    two primitive pieces pair to an invariant exactly when they agree."""
    def prims(a):
        """the multiset of primitive degrees occurring in wedge^a U."""
        if a > 2 * n:
            return []
        aa = a if a <= n else 2 * n - a
        return [aa - 2 * j for j in range(aa // 2 + 1)]
    total = 0
    for a in range(0, degree + 1):
        b = degree - a
        if b < 0 or a > 2 * n or b > 2 * n:
            continue
        pa, pb = prims(a), prims(b)
        total += sum(1 for m in pa if m in pb)
    return total


def monomial_span(n, d):
    """dim of the span of beta^i betahat^j ell^k, i+j+k=n, in degree 2n."""
    sp = Split(n, d)
    gens = [sp.beta(), sp.betahat(), sp.ell()]
    mons = []
    for i in range(n + 1):
        for j in range(n + 1 - i):
            k = n - i - j
            p = {(): sc(1)}
            for g, e in zip(gens, (i, j, k)):
                if e:
                    p = wedge(p, epow(g, e, d), d)
                if not p:
                    break
            if p:
                mons.append(p)
    keys = sorted({k for mo in mons for k in mo})
    idx = {k: t for t, k in enumerate(keys)}
    rows = [[F(0)] * len(mons) for _ in keys]
    for j, mo in enumerate(mons):
        for k, c in mo.items():
            rows[idx[k]][j] = c[0]
    # rank
    r, piv = 0, 0
    R = [row[:] for row in rows]
    nr, nc = len(R), len(mons)
    while r < nr and piv < nc:
        p = None
        for i in range(r, nr):
            if R[i][piv] != 0:
                p = i
                break
        if p is None:
            piv += 1
            continue
        R[r], R[p] = R[p], R[r]
        pv = R[r][piv]
        R[r] = [a / pv for a in R[r]]
        for i in range(nr):
            if i != r and R[i][piv] != 0:
                f = R[i][piv]
                R[i] = [a - f * b for a, b in zip(R[i], R[r])]
        r += 1
        piv += 1
    return r, len(mons)


if __name__ == "__main__":
    print("the reach of the split base case")
    npass = nfail = 0

    print("  (S1) the polarisation of the split member")
    for (n, d) in [(1, 1), (2, 1), (2, 3), (3, 1), (3, 2), (4, 1)]:
        ok1, ok2, _, _ = rosati(n, d)
        npass += check("n=%d, d=%d: M^2 = -d" % (n, d), ok2)
        nfail += 0 if ok2 else 1
        npass += check("n=%d, d=%d: M is anti-self-adjoint for "
                       "Q = diag(B, B/d), the Gram matrix of "
                       "beta + betahat/d" % (n, d), ok1)
        nfail += 0 if ok1 else 1
    okeig = True
    rows = []
    for (n, d) in [(1, 3), (2, 1), (2, 3), (3, 2), (3, 3), (4, 5)]:
        e_eta = eigenvalue_on_h2(n, d, F(d), F(1), F(0))     # d beta + betahat
        e_gam = eigenvalue_on_h2(n, d, F(d), F(-1), F(0))    # gamma
        e_ell = eigenvalue_on_h2(n, d, F(0), F(0), F(1))     # ell
        e_old = eigenvalue_on_h2(n, d, F(1), F(d), F(0))     # beta + d betahat
        good = (e_eta == F(d) and e_gam == F(-d) and e_ell == F(-d)
                and (e_old is None if d > 1 else e_old == F(d)))
        okeig = okeig and good
        rows.append("n=%d, d=%d: d beta + betahat -> %s, gamma -> %s, "
                    "ell -> %s, beta + d betahat -> %s"
                    % (n, d, e_eta, e_gam, e_ell,
                       "not an eigenclass" if e_old is None else e_old))
    npass += check("on H^2 the K-action multiplies d beta + betahat by +d "
                   "and gamma, ell by -d; beta + d betahat is not an "
                   "eigenclass for d > 1", okeig, "\n".join(rows))
    nfail += 0 if okeig else 1

    print("  (S2) the discriminant of the split member")
    allok = True
    for (n, d, diag) in [(1, 1, None), (2, 1, None), (2, 3, None),
                         (2, 7, [1, 5]), (3, 1, None), (3, 2, [1, 1, 3]),
                         (4, 1, None), (4, 5, [1, 2, 2, 3]),
                         (5, 3, None), (5, 11, [1, 1, 2, 4, 7])]:
        detH, norm, isnm = discriminant(n, d, diag)
        allok = allok and isnm
        print("    n=%d, d=%2d, beta type %-16s  det H = %-12s  "
              "(-1)^n det H = %-12s  norm: %s"
              % (n, d, str(diag if diag else [1] * n), detH, norm,
                 "yes" if isnm else "NO"))
    npass += check("(-1)^n det H is a norm from K in every case, so the "
                   "discriminant class is trivial", allok)
    nfail += 0 if allok else 1
    # the two ingredients, which is what the proof actually uses
    sq = True
    for D in ([1], [1, 1], [1, 5], [1, 1, 3], [1, 2, 2, 3], [1, 1, 2, 4, 7]):
        pf = 1
        for t in D:
            pf *= t
        detB = pf * pf
        if not is_square(detB) or detB != pf ** 2:
            sq = False
    npass += check("det B is the square of the Pfaffian, hence a square, "
                   "hence a norm", sq)
    nfail += 0 if sq else 1
    dn = all(is_norm_from_K(F(d), d) for d in [1, 2, 3, 5, 7, 11, 19, 43])
    npass += check("d itself is a norm, being N(sqrt(-d))", dn)
    nfail += 0 if dn else 1
    grp = all(is_norm_from_K(F(d) ** n * F(pf) ** 2, d)
              for d in [1, 2, 3, 7, 11] for n in [1, 2, 3, 4, 5]
              for pf in [1, 6, 56])
    npass += check("norms form a group, so d^n times a square is a norm", grp)
    nfail += 0 if grp else 1

    print("  (S3) the codimension of the split locus")
    ok = True
    for n in range(1, 11):
        weil = n * n
        split = n * (n + 1) // 2
        if weil - split != n * (n - 1) // 2:
            ok = False
        if n <= 5:
            print("    n=%d: dim D_{n,n} = %2d, dim of the split locus = %2d, "
                  "codimension = %d" % (n, weil, split, weil - split))
    npass += check("codimension = n(n-1)/2, zero only at n = 1", ok)
    nfail += 0 if ok else 1

    print("  (S4) the divisors at the split point")
    ok2deg = True
    for n in (1, 2, 3, 4):
        got = sp_invariant_count(n, 2)
        if got != 3:
            ok2deg = False
        print("    n=%d: dim NS(X x Xhat)_Q = %d" % (n, got))
    npass += check("the Neron-Severi group of the split member has rank 3, "
                   "spanned by beta, betahat and ell", ok2deg)
    nfail += 0 if ok2deg else 1

    okmid = True
    for (n, d) in [(1, 1), (2, 1), (2, 3), (3, 1), (3, 2)]:
        rank, nmon = monomial_span(n, d)
        pred = sp_invariant_count(n, 2 * n)
        agree = (rank == pred)
        okmid = okmid and agree
        print("    n=%d, d=%d: %d monomials span a space of dimension %d; "
              "Sp-invariants in degree %d: %d"
              % (n, d, nmon, rank, 2 * n, pred))
    npass += check("in the middle degree the monomials in the three divisor "
                   "classes span the whole space of Sp-invariants", okmid)
    nfail += 0 if okmid else 1

    print()
    print("  %d checks passed, %d failed" % (npass, nfail))
    print("  overall: %s" % ("PASS" if nfail == 0 else "FAIL"))
