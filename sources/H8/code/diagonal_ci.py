"""Item (LXXIII): diagonal complete intersections of Vandermonde type.

Setting.  Fix d >= 2, N >= 2, 1 <= c <= N - 1, m = N - c, distinct
lambda_0, ..., lambda_N and w_i = prod_{l != i} (lambda_i - lambda_l)^{-1}.
The variety

    X = X_{d,m}(lambda) = { x in P^N : sum_i w_i lambda_i^k x_i^d = 0,
                            k = 0, ..., c - 1 }

is a complete intersection of c diagonal hypersurfaces of degree d, and
C = X_{d,1}(lambda) is the generalised Fermat curve of type (d, N): the
cover of P^1 with group H = mu_d^{N+1}/mu_d branched over the lambda_i.
The map

    Phi : C^m -> X,   Phi(u^(1), ..., u^(m))_i = prod_j u^(j)_i,

is well defined and surjective, by the Lagrange identity
sum_i w_i f(lambda_i) = 0 for deg f <= N - 1, and identifies X with the
quotient of C^m by G = {(h_j) in H^m : prod h_j = 1} x| S_m, of order
m! d^{N(m-1)}.

Paper: the closure computation of Part "Beyond the Weil classes"
(tex/sections/11b_closuregraph.tex): thm:vandermonde, cor:twodiagonal,
rem:vandermonde.  The dimension m of this program is the r of the paper.

Parts (C) and (D) work in double precision (random points, roots of F);
they test the map of thm:vandermonde, which is proved by hand, and no
statement of the paper rests on them.  The other parts are exact.

  (A) the Lagrange identity in exact arithmetic, and the linear spaces
      Lambda_m = {(F(lambda_i))_i : deg F <= m};
  (B) smoothness: every c x c minor of a matrix of Vandermonde type is
      nonzero, and every pair of diagonal equations with nonzero 2 x 2
      minors is of Vandermonde type;
  (C) the map: random points of C^m map to X, which is smooth there;
  (D) surjectivity: a random point of X is reconstructed from the roots of
      F, and the fibre of Phi has m! d^{N(m-1)} = |G| points;
  (E) the genus of C from Riemann-Hurwitz, from adjunction and from the
      characters of the holomorphic forms;
  (F) the Euler number of X from the complete intersection formula and from
      the orbifold formula for C^m/G;
  (G) the Hodge numbers of X from Hirzebruch's formula and from the
      G-invariants of H^*(C^m), sum over characters of the exterior powers;
  (H) the middle Hodge numbers h^{p,p} for some fourfolds and sixfolds, the
      first degrees not covered by the paper's earlier results;
  (I) the bound dim B_[a] <= 5 behind cor:twodiagonal (ii), and the orbits of
      Weil type of cor:twodiagonal (iii) with h^{2,2} of the fourfolds.
"""
import itertools
import math
import random
import sys
from fractions import Fraction as Fr

import numpy as np

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


def weights(lam):
    N1 = len(lam)
    w = []
    for i in range(N1):
        p = Fr(1) if isinstance(lam[0], Fr) else 1.0
        for l in range(N1):
            if l != i:
                p *= (lam[i] - lam[l])
        w.append(1 / p)
    return w


def rank_exact(rows):
    """rank of a matrix of Fractions by Gaussian elimination"""
    M = [list(r) for r in rows]
    r = 0
    ncol = len(M[0]) if M else 0
    for col in range(ncol):
        piv = next((i for i in range(r, len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col] / M[r][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r


def det_exact(M):
    M = [list(r) for r in M]
    n = len(M)
    det = Fr(1)
    for col in range(n):
        piv = next((i for i in range(col, n) if M[i][col] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = -det
        det *= M[col][col]
        for i in range(col + 1, n):
            f = M[i][col] / M[col][col]
            M[i] = [a - f * b for a, b in zip(M[i], M[col])]
    return det


def distinct_rationals(rng, n):
    s = set()
    while len(s) < n:
        s.add(Fr(rng.randint(-40, 40), rng.randint(1, 9)))
    return sorted(s)


# ----------------------------------------------------------------------
def part_A():
    rng = random.Random(1)
    ok = True
    for N in range(2, 10):
        for _ in range(3):
            lam = distinct_rationals(rng, N + 1)
            w = weights(lam)
            for k in range(N + 1):
                s = sum(wi * li ** k for wi, li in zip(w, lam))
                ok &= (s == 0) if k < N else (s == 1)
    check("(A) Lagrange identity: sum_i w_i lambda_i^k = 0 for k <= N - 1 "
          "and 1 for k = N, N = 2..9, exact", ok)
    ok = True
    cases = 0
    for N in range(3, 9):
        lam = distinct_rationals(rng, N + 1)
        w = weights(lam)
        for m in range(1, N):
            c = N - m
            eqs = [[w[i] * lam[i] ** k for i in range(N + 1)] for k in range(c)]
            polys = [[lam[i] ** j for i in range(N + 1)] for j in range(m + 1)]
            inker = all(sum(e[i] * v[i] for i in range(N + 1)) == 0
                        for e in eqs for v in polys)
            ok &= rank_exact(eqs) == c and rank_exact(polys) == m + 1 and inker
            cases += 1
    check("(A) Lambda_m = {(F(lambda_i))_i : deg F <= m}: the c equations "
          "have rank c and the m + 1 vectors (lambda_i^j) span their kernel",
          ok, "%d pairs (N, m)" % cases)


# ----------------------------------------------------------------------
def part_B():
    rng = random.Random(2)
    ok = True
    nmin = 0
    for N in range(3, 9):
        for c in range(1, N):
            lam = distinct_rationals(rng, N + 1)
            mu = [Fr(rng.randint(1, 9)) * rng.choice([1, -1]) for _ in range(N + 1)]
            while True:
                g = [[Fr(rng.randint(-5, 5)) for _ in range(c)] for _ in range(c)]
                if det_exact(g) != 0:
                    break
            a = [[mu[i] * sum(g[k][l] * lam[i] ** l for l in range(c))
                  for i in range(N + 1)] for k in range(c)]
            for cols in itertools.combinations(range(N + 1), c):
                nmin += 1
                ok &= det_exact([[a[k][i] for i in cols] for k in range(c)]) != 0
    check("(B) every c x c minor of a matrix of Vandermonde type is nonzero, "
          "so X is smooth", ok, "%d minors" % nmin)
    # c = 2: diagonal pairs with nonzero minors are of Vandermonde type
    ok = True
    for trial in range(40):
        N = rng.randint(3, 8)
        while True:
            a = [[Fr(rng.randint(-6, 6)) for _ in range(N + 1)] for _ in range(2)]
            if all(a[0][i] * a[1][j] - a[0][j] * a[1][i] != 0
                   for i, j in itertools.combinations(range(N + 1), 2)):
                break
        # a point of P^1 off the columns: (1, s) with a_0i s - a_1i != 0
        s = 0
        while any(a[0][i] * s - a[1][i] == 0 for i in range(N + 1)):
            s += 1
        # new first row r_i = s a_0i - a_1i (nonzero), lambda_i = a_0i / r_i
        r = [s * a[0][i] - a[1][i] for i in range(N + 1)]
        lam = [a[0][i] / r[i] for i in range(N + 1)]
        mu = r
        # a_0i = mu_i lambda_i, a_1i = s a_0i - r_i = mu_i (s lambda_i - 1)
        g = [[Fr(0), Fr(1)], [Fr(-1), Fr(s)]]
        rec = [[mu[i] * (g[k][0] + g[k][1] * lam[i]) for i in range(N + 1)]
               for k in range(2)]
        ok &= rec == a and len(set(lam)) == N + 1 and det_exact(g) != 0
    check("(B) c = 2: 40 random pairs of diagonal equations with nonzero 2 x 2 "
          "minors are of Vandermonde type, a = g V diag(mu), exact", ok)


# ----------------------------------------------------------------------
def curve_point(lam, s, t, d, rng=None):
    """a point of C over (s : t): u_i^d = t - lambda_i s"""
    v = np.array([t - li * s for li in lam], dtype=complex)
    u = v ** (1.0 / d)
    if rng is not None:
        u = u * np.exp(2j * np.pi * rng.integers(0, d, len(lam)) / d)
    return u


def equations(lam, w, c, d, x):
    return np.array([sum(w[i] * lam[i] ** k * x[i] ** d for i in range(len(lam)))
                     for k in range(c)])


def jacobian_rank(lam, w, c, d, x):
    J = np.array([[w[i] * lam[i] ** k * d * x[i] ** (d - 1) for i in range(len(lam))]
                  for k in range(c)])
    sv = np.linalg.svd(J, compute_uv=False)
    return int(np.sum(sv > 1e-9 * sv[0]))


def part_C():
    rng = np.random.default_rng(3)
    ok = True
    worst = 0.0
    cases = 0
    for (d, N) in [(2, 3), (2, 5), (3, 3), (3, 4), (3, 6), (4, 4), (5, 5), (6, 5)]:
        lam = list(rng.normal(size=N + 1) + 1j * rng.normal(size=N + 1))
        w = weights(lam)
        # C lies in its equations
        for _ in range(3):
            u = curve_point(lam, *rng.normal(size=2), d, rng)
            res = equations(lam, w, N - 1, d, u)
            worst = max(worst, np.max(np.abs(res)) / np.max(np.abs(u)) ** d)
        for m in range(1, N):
            c = N - m
            for _ in range(3):
                us = [curve_point(lam, *(rng.normal(size=2) + 1j * rng.normal(size=2)), d, rng)
                      for _ in range(m)]
                x = np.prod(us, axis=0)
                x = x / np.max(np.abs(x))
                res = equations(lam, w, c, d, x)
                worst = max(worst, np.max(np.abs(res)))
                ok &= jacobian_rank(lam, w, c, d, x) == c
                cases += 1
    check("(C) Phi maps C^m into X: residuals of the c equations at Phi(u), "
          "and the Jacobian has rank c there", ok and worst < 1e-10,
          "%d points, largest residual %.1e" % (cases, worst))


def phi(us):
    return np.prod(us, axis=0)


def proj_equal(x, y, tol=1e-8):
    k = np.argmax(np.abs(y))
    if abs(y[k]) < 1e-14:
        return False
    r = x[k] / y[k]
    return np.max(np.abs(x - r * y)) < tol * np.max(np.abs(x))


def reconstruct(lam, d, m, x, rng):
    """a preimage of x under Phi, from the roots of F"""
    N1 = len(lam)
    y = x ** d
    # F of degree <= m with F(lambda_i) = y_i: solve on m + 1 nodes, check rest
    V = np.array([[lam[i] ** j for j in range(m + 1)] for i in range(N1)])
    coef, *_ = np.linalg.lstsq(V, y, rcond=None)
    roots = np.roots(coef[::-1])
    lead = coef[-1]
    # F(l) = lead prod (l - r_j) = prod_j (t_j - l s_j) with s_j = -1,
    # t_j = -r_j, the leading coefficient absorbed in the first factor
    fac = [(-1.0 + 0j, -r) for r in roots]
    fac[0] = (fac[0][0] * lead, fac[0][1] * lead)
    us = [curve_point(lam, s, t, d) for (s, t) in fac]
    z = phi(us)
    # fix the overall constant and the d-th roots of unity coordinatewise
    eps = x / z
    us[0] = us[0] * eps
    return us, np.allclose(phi(us), x, rtol=1e-8, atol=1e-10 * np.max(np.abs(x)))


def part_D():
    rng = np.random.default_rng(4)
    ok = True
    cases = 0
    for (d, N) in [(2, 4), (3, 4), (3, 5), (4, 5), (5, 6)]:
        lam = list(rng.normal(size=N + 1) + 1j * rng.normal(size=N + 1))
        w = weights(lam)
        for m in range(1, N):
            c = N - m
            for _ in range(2):
                F = rng.normal(size=m + 1) + 1j * rng.normal(size=m + 1)
                y = np.array([np.polyval(F[::-1], li) for li in lam])
                x = y ** (1.0 / d) * np.exp(2j * np.pi * rng.integers(0, d, N + 1) / d)
                assert np.max(np.abs(equations(lam, w, c, d, x))) < 1e-9 * np.max(np.abs(x)) ** d
                us, good = reconstruct(lam, d, m, x, rng)
                # each factor lies on C (ratio of eps is a root of unity)
                onC = all(np.max(np.abs(equations(lam, w, N - 1, d, u))) <
                          1e-8 * np.max(np.abs(u)) ** d for u in us)
                ok &= good and onC
                cases += 1
    check("(D) surjectivity: random points of X are Phi of points of C^m "
          "built from the roots of F", ok, "%d points" % cases)
    # the fibre has |G| = m! d^{N(m-1)} points
    ok = True
    rows = []
    for (d, N, m) in [(2, 3, 2), (2, 4, 2), (3, 3, 2), (2, 4, 3), (3, 4, 2)]:
        lam = list(rng.normal(size=N + 1) + 1j * rng.normal(size=N + 1))
        pts = [(rng.normal() + 1j * rng.normal(), rng.normal() + 1j * rng.normal())
               for _ in range(m)]
        base = [curve_point(lam, s, t, d) for s, t in pts]
        x = phi(base)
        # the fibre of C -> P^1 over (s : t): d^N points (roots of unity mod scalar)
        fib = []
        for e in itertools.product(range(d), repeat=N):
            z = np.exp(2j * np.pi * np.array((0,) + e) / d)
            fib.append(z)
        cnt = 0
        for perm in itertools.permutations(range(m)):
            for choice in itertools.product(range(len(fib)), repeat=m):
                us = [base[perm[j]] * fib[choice[j]] for j in range(m)]
                if proj_equal(phi(us), x):
                    cnt += 1
        G = math.factorial(m) * d ** (N * (m - 1))
        ok &= cnt == G
        rows.append("(%d,%d,%d): %d" % (d, N, m, cnt))
    check("(D) the fibre of Phi over a general point has m! d^{N(m-1)} = |G| "
          "points", ok, ", ".join(rows))


# ----------------------------------------------------------------------
def genus_rh(d, N):
    # 2g - 2 = d^N (-2) + (N + 1) d^{N-1} (d - 1)
    return (d ** N * (-2) + (N + 1) * d ** (N - 1) * (d - 1)) // 2 + 1


def genus_adj(d, N):
    # complete intersection of N - 1 hypersurfaces of degree d in P^N:
    # 2g - 2 = d^{N-1} ((N - 1) d - N - 1)
    return (d ** (N - 1) * ((N - 1) * d - N - 1)) // 2 + 1


def characters(d, N):
    """characters of H = mu_d^{N+1}/mu_d: a in (Z/d)^{N+1}, sum a = 0"""
    for a in itertools.product(range(d), repeat=N + 1):
        if sum(a) % d == 0:
            yield a


def h10(a, d):
    """dim of the a-eigenspace of H^{1,0}(C): the forms
    t^j prod (t - lambda_i)^{-b_i/d} dt, b_i = -a_i mod d,
    0 <= j <= sum b_i / d - 2"""
    if not any(a):
        return 0
    return max(0, sum((-x) % d for x in a) // d - 1)


def part_E():
    ok1 = ok2 = True
    for d in range(2, 8):
        for N in range(2, 9):
            g1, g2 = genus_rh(d, N), genus_adj(d, N)
            ok1 &= g1 == g2
            if d ** (N + 1) <= 60000:
                g3 = sum(h10(a, d) for a in characters(d, N))
                ok2 &= g3 == g1
    check("(E) genus of C: Riemann-Hurwitz = adjunction, "
          "1 + d^{N-1}((N-1)(d-1)-2)/2, d = 2..7, N = 2..8", ok1)
    check("(E) the holomorphic forms t^j prod (t - lambda_i)^{-b_i/d} dt, one "
          "family for each character, add up to the genus", ok2)


# ----------------------------------------------------------------------
def poly_mul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def ci_euler(d, N, c):
    """Euler number of a smooth complete intersection of c hypersurfaces of
    degree d in P^N: d^c [h^m] (1 + h)^{N+1} / (1 + d h)^c"""
    m = N - c
    num = [Fr(math.comb(N + 1, k)) for k in range(N + 2)]
    inv = [Fr((-d) ** k) for k in range(m + 1)]   # 1/(1 + d h)
    p = num
    for _ in range(c):
        p = poly_mul(p, inv)
    return d ** c * p[m]


def orbifold_euler(d, N, m):
    """(1/|G|) sum_{g in G} e((C^m)^g) for G = K x| S_m"""
    H = list(itertools.product(range(d), repeat=N))   # H = mu_d^{N+1}/mu_d, u_0 fixed
    idx = {h: k for k, h in enumerate(H)}
    g = genus_rh(d, N)

    def eps(h):
        if not any(h):
            return 2 - 2 * g
        # h = (0, h_1, ..., h_N) mod scalars: a power of a single generator e_i
        full = (0,) + h
        for kappa in range(d):
            diff = [i for i, x in enumerate(full) if (x - kappa) % d]
            if len(diff) == 1:
                return d ** (N - 1)
        return 0
    e = np.array([eps(h) for h in H], dtype=object)

    def conv(f1, f2):
        out = np.zeros(len(H), dtype=object)
        for i, a in enumerate(H):
            if f1[i] == 0:
                continue
            for j, b in enumerate(H):
                if f2[j] == 0:
                    continue
                k = idx[tuple((x + y) % d for x, y in zip(a, b))]
                out[k] += f1[i] * f2[j]
        return out
    S = {1: e[idx[(0,) * N]]}
    f = e.copy()
    for l in range(2, m + 1):
        f = conv(f, e)
        S[l] = f[idx[(0,) * N]]
    # unsigned Stirling numbers of the first kind
    st = [[0] * (m + 1) for _ in range(m + 1)]
    st[0][0] = 1
    for n in range(1, m + 1):
        for k in range(1, n + 1):
            st[n][k] = st[n - 1][k - 1] + (n - 1) * st[n - 1][k]
    hH = d ** N
    tot = sum(st[m][l] * hH ** (m - l) * S[l] for l in range(1, m + 1))
    G = math.factorial(m) * hH ** (m - 1)
    return Fr(int(tot), G)


def part_F():
    ok = True
    rows = []
    for (d, N) in [(2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (4, 3), (4, 4), (5, 3), (3, 5)]:
        for m in range(1, min(N, 4)):
            c = N - m
            e1 = ci_euler(d, N, c)
            e2 = orbifold_euler(d, N, m)
            ok &= e1 == e2
            rows.append(int(e1))
    check("(F) Euler number of X: complete intersection formula = orbifold "
          "formula for C^m/G", ok, "%d cases, e.g. %s" % (len(rows), rows[:6]))


# ----------------------------------------------------------------------
def chi_y_numeric(d, N, c, yval):
    """chi_y(X) at a rational y, from Hirzebruch's formula with exact
    rational power series in z"""
    Z = N + 2

    def mul(A, B):
        C = [Fr(0)] * Z
        for i, a in enumerate(A):
            if a:
                for j in range(Z - i):
                    C[i + j] += a * B[j]
        return C

    def power(A, k):
        R = [Fr(1)] + [Fr(0)] * (Z - 1)
        for _ in range(k):
            R = mul(R, A)
        return R

    def inv(A):
        R = [Fr(0)] * Z
        R[0] = 1 / A[0]
        for n in range(1, Z):
            R[n] = -sum(A[k] * R[n - k] for k in range(1, n + 1)) / A[0]
        return R
    y = Fr(yval)
    a = [Fr(1), y] + [Fr(0)] * (Z - 2)
    b = [Fr(1), Fr(-1)] + [Fr(0)] * (Z - 2)
    P, Q = power(a, d), power(b, d)
    num = [p - q for p, q in zip(P, Q)]
    den = [p + y * q for p, q in zip(P, Q)]
    ratio = mul(num, inv(den))
    pre = inv(mul(a, b))
    S = pre
    for _ in range(c):
        S = mul(S, ratio)
    return S[N]       # coefficient of z^{n + c} with n = N - c


def chi_y_poly(d, N, c):
    """recover chi_y as a polynomial of degree m by interpolation at m + 1
    rational points"""
    m = N - c
    xs = [Fr(k + 2) for k in range(m + 1)]
    ys = [chi_y_numeric(d, N, c, x) for x in xs]
    # Lagrange interpolation to coefficients
    coef = [Fr(0)] * (m + 1)
    for i, xi in enumerate(xs):
        basis = [Fr(1)]
        denom = Fr(1)
        for j, xj in enumerate(xs):
            if j != i:
                basis = poly_mul(basis, [-xj, Fr(1)])
                denom *= (xi - xj)
        for k in range(m + 1):
            coef[k] += ys[i] * basis[k] / denom
    return coef


def hodge_middle_ci(d, N, c):
    """h^{p, m-p}, p = 0..m, from chi(Omega^p) and the Lefschetz theorem"""
    m = N - c
    chi = chi_y_poly(d, N, c)
    h = []
    for p in range(m + 1):
        if 2 * p == m:
            h.append((-1) ** p * chi[p])
        else:
            h.append((-1) ** (m - p) * (chi[p] - (-1) ** p))
    return h


def hodge_middle_quotient(d, N, m):
    """h^{p, m-p} of C^m/G: delta + sum over characters of C(a, p) C(b, m-p)"""
    h = [0] * (m + 1)
    if m % 2 == 0:
        h[m // 2] += 1
    for a in characters(d, N):
        if not any(a):
            continue
        A = h10(a, d)
        B = h10(tuple((-x) % d for x in a), d)
        for p in range(m + 1):
            h[p] += math.comb(A, p) * math.comb(B, m - p)
    return h


def part_G():
    # sanity of the formula: a plane cubic, a quartic surface, P^n
    ok = chi_y_poly(3, 2, 1) == [0, 0] and chi_y_poly(4, 3, 1) == [2, -20, 2] \
        and chi_y_poly(1, 4, 1) == [1, -1, 1, -1]
    check("(G) Hirzebruch's formula: chi_y of a plane cubic 0, of a quartic "
          "surface 2 - 20y + 2y^2, of P^3 1 - y + y^2 - y^3", ok)
    ok = True
    rows = 0
    for (d, N) in [(2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5),
                   (4, 3), (4, 4), (5, 3), (5, 4), (6, 3), (6, 4), (3, 6)]:
        for m in range(1, N):
            c = N - m
            h1 = hodge_middle_ci(d, N, c)
            h2 = hodge_middle_quotient(d, N, m)
            ok &= [int(x) for x in h1] == h2 and all(x.denominator == 1 for x in h1)
            rows += 1
    check("(G) middle Hodge numbers of X from Hirzebruch's formula = those of "
          "C^m/G, sum over characters of C(a_chi, p) C(a_conj chi, m - p)",
          ok, "%d triples (d, N, m)" % rows)


def part_H():
    rows = []
    ok = True
    for (d, N, m) in [(3, 6, 4), (4, 6, 4), (3, 7, 4), (3, 8, 6), (5, 6, 4)]:
        h = hodge_middle_quotient(d, N, m)
        hc = hodge_middle_ci(d, N, N - m)
        ok &= [int(x) for x in hc] == h
        rows.append("d=%d N=%d m=%d: h^{%d,%d} = %d" % (d, N, m, m // 2, m // 2, h[m // 2]))
    check("(H) middle Hodge numbers of some fourfolds and a sixfold "
          "(c = 2 or 3 diagonal hypersurfaces), both ways",
          ok, "; ".join(rows))
    # the two-diagonal fourfolds: their h^{2,2} grows without bound in d
    seq = [hodge_middle_quotient(d, 6, 4)[2] for d in (3, 4, 5)]
    check("(H) for c = 2, m = 4 (fourfolds in P^6) h^{2,2} increases with d",
          seq[0] < seq[1] < seq[2], str(seq))


# ----------------------------------------------------------------------
def orbit_rep(a, d):
    units = [u for u in range(1, d) if math.gcd(u, d) == 1]
    return min(tuple(u * x % d for x in a) for u in units)


def part_I():
    # cor:twodiagonal (ii): for d in {2,3,4,6} every B_[a] has dimension
    # |[a]| dim V_a / 2 <= 5 when N <= 6 (d = 3, 4, 6) or N <= 12 (d = 2),
    # and the bounds are sharp: 6 at N = 7 and N = 13
    ok = True
    worst = {}
    for d, Nmax in ((2, 12), (3, 6), (4, 6), (6, 6)):
        for N in range(2, Nmax + 1):
            dimB = 0
            for a in characters(d, N):
                if not any(a):
                    continue
                orb = {tuple(u * x % d for x in a)
                       for u in range(1, d) if math.gcd(u, d) == 1}
                nz = sum(1 for x in a if x)
                # dim V_a = h10(a) + h10(-a) = #nonzero - 2
                va = h10(a, d) + h10(tuple((-x) % d for x in a), d)
                ok &= va == max(0, nz - 2)
                dimB = max(dimB, Fr(len(orb) * va, 2))
            worst[(d, N)] = dimB
            ok &= dimB <= 5
    # sharpness: dimension six appears at N = 7 for d = 3 and N = 13 for d = 2
    for d, N in ((3, 7), (2, 13)):
        worst[(d, N)] = max(
            v for v in (
                Fr(len({tuple(u * x % d for x in a) for u in range(1, d)
                        if math.gcd(u, d) == 1})
                   * (h10(a, d) + h10(tuple((-x) % d for x in a), d)), 2)
                for a in characters(d, N) if any(a)))
        ok &= worst[(d, N)] == 6
    check("(I) cor:twodiagonal (ii): dim V_a = #nonzero - 2 and every "
          "B_[a] has dimension <= 5 for d = 3, 4, 6, N <= 6 and d = 2, N <= 12, "
          "and the bounds are sharp",
          ok, "largest: d=3,4,6 at N=6: %s; d=2 at N=12: %s; six at d=3, N=7 "
          "and d=2, N=13: %s, %s" % (
              ", ".join(str(worst[(d, 6)]) for d in (3, 4, 6)), worst[(2, 12)],
              worst[(3, 7)], worst[(2, 13)]))
    # cor:twodiagonal (iii): the orbits of Weil type in P^6
    counts, hdg, h22 = [], [], []
    for d in (3, 4, 6):
        orbs = set()
        for a in characters(d, 6):
            if sum(1 for x in a if x) != 6:
                continue
            if d // math.gcd(d, *a) < 3:
                continue
            if sum(Fr(x, d) for x in a) != 3:
                continue
            # balanced: V_a^{1,0} and V_{-a}^{1,0} both of dimension two
            ok &= h10(a, d) == 2 and h10(tuple((-x) % d for x in a), d) == 2
            orbs.add(orbit_rep(a, d))
        counts.append(len(orbs))
        hdg.append(1 + 2 * len(orbs))
        h22.append(hodge_middle_quotient(d, 6, 4)[2])
    ok = counts == [70, 490, 6125] and hdg == [141, 981, 12251] and \
        h22 == [267, 2584, 48588] and all(a <= b for a, b in zip(hdg, h22))
    check("(I) cor:twodiagonal (iii): orbits of Weil type 70, 490, 6125 for "
          "d = 3, 4, 6 in P^6, balanced (2,2); Hodge classes >= 141, 981, 12251 "
          "<= h^{2,2} = 267, 2584, 48588", ok,
          "orbits %s, h22 %s" % (counts, h22))


def main():
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    part_H()
    part_I()
    print()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
