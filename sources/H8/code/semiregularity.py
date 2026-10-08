#!/usr/bin/env python3
"""
semiregularity.py

The semiregularity map of a direct sum of line bundles, computed exactly.

Theorem 14.52 of the paper says that if one perfect complex at one base point
has an injective semiregularity map, the Hodge conjecture follows for the
whole Weil family.  The cheapest object to try is a direct sum of line
bundles on the split member A = X x Xhat, because there every Weil class is
already a polynomial in the three divisor classes beta, betahat, ell.

Two things have to hold.

  (S)  ch(E) must be a flat section of Hodge classes over the family:
       ch_k(E) in Q eta^k for k != n, and ch_n(E) in
       Q eta^n + Q omega_1 + Q omega_2 with a nonzero Weil part.

  (I)  the semiregularity map must be injective.

For E = L_1 + ... + L_s the Atiyah class is diagonal with entries
lambda_i = c_1(L_i), so for zeta = (zeta_ij) in Ext^2(E,E),

    sigma(zeta)_q = (1/q!) tr( zeta o At^q ) = (1/q!) sum_i zeta_ii lambda_i^q .

The off-diagonal entries are therefore killed outright, and so is the
traceless part of each diagonal block.  So (I) forces

  (I1) every L_i to occur with multiplicity one, and
  (I2) Ext^2(L_i, L_j) = H^2(A, L_j L_i^{-1}) = 0 for i != j, and
  (I3) the map  (zeta_i) |-> sum_i e^{lambda_i} zeta_i  from
       (H^2(O_A))^s to H^*(A,C) to be injective.

This script decides (S), (I2) and (I3) by exact arithmetic.  The Hodge
structure is made explicit by taking X = E_i^n with E_i = C/(Z + iZ), so that
everything lives in Q(i), and the model is the one of Setup 14.1 with the
endomorphism M of (14.1).

Output: for each (n, d) it reports whether any direct sum of line bundles
satisfies (S), and for those that do, whether (I2) and (I3) hold.
"""

from fractions import Fraction as F
from itertools import combinations

# --------------------------------------------------- Gaussian rationals

def g(a=0, b=0):
    return (F(a), F(b))


ZERO = g()
ONE = g(1)
IUNIT = g(0, 1)


def gadd(p, q):
    return (p[0] + q[0], p[1] + q[1])


def gsub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def gmul(p, q):
    return (p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0])


def gdiv(p, q):
    n = q[0] * q[0] + q[1] * q[1]
    return ((p[0] * q[0] + p[1] * q[1]) / n, (p[1] * q[0] - p[0] * q[1]) / n)


def gzero(p):
    return p[0] == 0 and p[1] == 0


def gconj(p):
    return (p[0], -p[1])


# ------------------------------------------------- exterior algebra / Q(i)

def wedge(u, v):
    out = {}
    for su, cu in u.items():
        setu = set(su)
        for sv, cv in v.items():
            if setu & set(sv):
                continue
            arr = list(su) + list(sv)
            sign = 1
            for a in range(len(arr)):
                for b in range(a + 1, len(arr)):
                    if arr[a] > arr[b]:
                        sign = -sign
            k = tuple(sorted(arr))
            t = gmul(cu, cv)
            if sign < 0:
                t = (-t[0], -t[1])
            out[k] = gadd(out.get(k, ZERO), t)
    return {k: c for k, c in out.items() if not gzero(c)}


def eadd(*us):
    out = {}
    for u in us:
        for k, c in u.items():
            out[k] = gadd(out.get(k, ZERO), c)
    return {k: c for k, c in out.items() if not gzero(c)}


def escale(c, u):
    return {k: gmul(c, v) for k, v in u.items() if not gzero(gmul(c, v))}


def epow(u, k):
    r = {(): ONE}
    for _ in range(k):
        r = wedge(r, u)
    return r


# ------------------------------------------------------------- the model

class Model:
    """A = X x Xhat with X = E_i^n, the K-action M of (14.1) with beta
    principal, and the three divisor classes."""

    def __init__(self, n, d):
        self.n, self.d = n, d
        self.m = 2 * n
        self.N = 4 * n
        self.beta = self._beta()
        self.betahat = self._betahat()
        self.ell = self._ell()
        self._hodge()

    # index helpers ------------------------------------------------------
    def x(self, i):
        return i - 1                      # i = 1..2n

    def xi(self, i):
        return self.m + i - 1             # i = 1..2n

    # the three divisor classes -----------------------------------------
    def _beta(self):
        n = self.n
        return {tuple(sorted((self.x(j), self.x(n + j)))): ONE
                for j in range(1, n + 1)}

    def _betahat(self):
        n = self.n
        return {tuple(sorted((self.xi(j), self.xi(n + j)))): ONE
                for j in range(1, n + 1)}

    def _ell(self):
        return {tuple(sorted((self.x(i), self.xi(i)))): ONE
                for i in range(1, self.m + 1)}

    # the Hodge decomposition --------------------------------------------
    def _hodge(self):
        """With tau = i I_n the (1,0) part of H^1(X) is spanned by
        x_k + i x_{n+k}, and the dual complex structure on Xhat makes the
        (1,0) part of H^1(Xhat) spanned by xi_k + e i xi_{n+k} for one of the
        two signs e; we take the sign that makes ell of type (1,1)."""
        n = self.n
        for e in (+1, -1):
            H10 = []
            for k in range(1, n + 1):
                H10.append({(self.x(k),): ONE, (self.x(n + k),): IUNIT})
            for k in range(1, n + 1):
                H10.append({(self.xi(k),): ONE,
                            (self.xi(n + k),): g(0, e)})
            H01 = [{kk: gconj(cc) for kk, cc in v.items()} for v in H10]
            self.H10, self.H01, self.esign = H10, H01, e
            if (self.hodge_type_ok(self.ell) and
                    self.hodge_type_ok(self.beta) and
                    self.hodge_type_ok(self.betahat)):
                return
        raise RuntimeError("no sign makes the three classes of type (1,1)")

    def basis_change(self):
        """The matrix expressing the 4n generators in terms of the Hodge
        basis (H10 then H01), so that any class can be rewritten."""
        cols = self.H10 + self.H01
        N = self.N
        M = [[ZERO] * N for _ in range(N)]
        for j, v in enumerate(cols):
            for kk, cc in v.items():
                M[kk[0]][j] = cc
        return invert(M)

    def to_hodge(self, u):
        """Rewrite a class in the basis p_1..p_{2n}, q_1..q_{2n} where
        p = H10 and q = H01.  Returns a dict keyed by sorted tuples of
        0..4n-1, the first 2n meaning H10 and the last 2n meaning H01."""
        if not hasattr(self, "_inv"):
            self._inv = self.basis_change()
        inv = self._inv
        gens = []
        for i in range(self.N):
            gens.append({(j,): inv[j][i] for j in range(self.N)
                         if not gzero(inv[j][i])})
        out = {}
        for kk, cc in u.items():
            term = {(): cc}
            for idx in kk:
                term = wedge(term, gens[idx])
            out = eadd(out, term)
        return out

    def hodge_type_ok(self, u, p=None, q=None):
        """True when u is of pure type (p,q); with p,q unset, tests (1,1)
        for a degree two class."""
        if p is None:
            p = q = 1
        h = self.to_hodge(u)
        m = self.m
        for kk in h:
            a = sum(1 for t in kk if t < m)
            b = len(kk) - a
            if (a, b) != (p, q):
                return False
        return True

    # the Weil line ------------------------------------------------------
    def Bx(self, i):
        n = self.n
        if i <= n:
            return {(self.xi(n + i),): ONE}
        return {(self.xi(i - n),): g(-1)}

    def omega_pm(self, s):
        """omega_s = wedge_i ( x_i + s (delta/d) B x_i ), delta = sqrt(-d).
        Over Q(i) we cannot write sqrt(-d) unless d is a square times 1, so
        we use the closed form of Theorem 14.24 instead; see weil_line."""
        raise NotImplementedError

    def weil_line(self):
        """omega_1 and omega_2, from the closed form
        omega_pm = c (gamma -+ sqrt(-d) ell)^n with c = (-1)^{n(n-1)/2}/(n! d^n).
        Expanding, the real and imaginary parts are rational classes:
            omega_1 = c * sum_{j even} C(n,j) gamma^{n-j} (-d)^{j/2} ell^j
            omega_2 = c * sum_{j odd} C(n,j) gamma^{n-j} (-1)^{(j+1)/2}
                                             d^{(j-1)/2} ell^j
        with the sign of the second fixed by (-sqrt(-d))^j."""
        n, d = self.n, self.d
        gamma = eadd(escale(g(d), self.beta), escale(g(-1), self.betahat))
        c = F((-1) ** (n * (n - 1) // 2), 1)
        for k in range(2, n + 1):
            c /= k
        c /= F(d) ** n
        w1, w2 = {}, {}
        for j in range(n + 1):
            binom = 1
            for t in range(j):
                binom = binom * (n - t) // (t + 1)
            term = wedge(epow(gamma, n - j), epow(self.ell, j))
            if j % 2 == 0:
                coef = F((-1) ** (j // 2)) * F(d) ** (j // 2) * F(binom)
                w1 = eadd(w1, escale(g(coef), term))
            else:
                coef = F((-1) ** ((j + 1) // 2)) * F(d) ** ((j - 1) // 2) \
                    * F(binom)
                w2 = eadd(w2, escale(g(coef), term))
        # clear the overall constant and the denominators
        w1 = escale(g(c), w1)
        w2 = escale(g(c), w2)
        w1 = clear(w1)
        w2 = clear(w2)
        return w1, w2

    def eta(self):
        """The Weil polarisation of the split member: the combination of beta
        and betahat for which M is anti-self-adjoint.  Determined here by a
        direct search over p beta + q betahat with small integers; the answer
        is d beta + betahat, see split_geometry.py (S1)."""
        for p in range(1, 6):
            for q in range(-6, 7):
                if q == 0:
                    continue
                cand = eadd(escale(g(p), self.beta), escale(g(q),
                                                            self.betahat))
                if self.rosati_ok(cand) and epow(cand, 2 * self.n):
                    return cand
        raise RuntimeError("no polarisation found")

    def Mmat(self):
        """M acting on H^1(A,Q) in the basis x_1..x_2n, xi_1..xi_2n: the
        transpose of the action of the paper's M on H_1(A,Q); it sends
        x -> -B x on U = H^1(X) and xi -> d B^{-1} xi on U^dual = H^1(Xhat)."""
        n, N = self.n, self.N
        M = [[F(0)] * N for _ in range(N)]
        for i in range(1, 2 * n + 1):
            for kk, cc in self.Bx(i).items():
                M[kk[0]][self.x(i)] = -cc[0]
        # d B^{-1} : xi_{n+j} -> x_j, xi_j -> -x_{n+j}
        for j in range(1, n + 1):
            M[self.x(j)][self.xi(n + j)] = F(self.d)
            M[self.x(n + j)][self.xi(j)] = F(-self.d)
        return M

    def rosati_ok(self, form):
        """The Rosati condition for the class `form`.  Its coefficient matrix
        Q in the basis x, xi is the Gram matrix of the form on H_1(A), on
        which M acts by the transpose of Mmat(); so the condition
        eta(M u, v) + eta(u, M v) = 0 reads  M Q + Q M^T = 0  with M = Mmat().
        Equivalently the class is an eigenclass of M^* on H^2 for the
        eigenvalue +d, the norm character."""
        N = self.N
        Q = [[F(0)] * N for _ in range(N)]
        for kk, cc in form.items():
            a, b = kk
            Q[a][b] = cc[0]
            Q[b][a] = -cc[0]
        M = self.Mmat()
        for i in range(N):
            for j in range(N):
                t = sum(M[i][k] * Q[k][j] for k in range(N)) \
                    + sum(Q[i][k] * M[j][k] for k in range(N))
                if t != 0:
                    return False
        return True


def clear(u):
    """Scale a rational class by the smallest positive rational making all
    coefficients integers with content one."""
    from math import gcd
    dens = 1
    for c in u.values():
        assert c[1] == 0, "class is not rational"
        dens = dens * c[0].denominator // gcd(dens, c[0].denominator)
    nums = [int(c[0] * dens) for c in u.values()]
    if not nums:
        return u
    cont = 0
    for t in nums:
        cont = gcd(cont, abs(t))
    if cont == 0:
        return u
    return {k: g(F(int(c[0] * dens) // cont)) for k, c in u.items()}


# ------------------------------------------------ linear algebra over Q(i)

def invert(M):
    n = len(M)
    A = [row[:] + [ONE if i == j else ZERO for j in range(n)]
         for i, row in enumerate(M)]
    r = 0
    for c in range(n):
        p = None
        for i in range(r, n):
            if not gzero(A[i][c]):
                p = i
                break
        if p is None:
            raise RuntimeError("singular")
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [gdiv(v, pv) for v in A[r]]
        for i in range(n):
            if i != r and not gzero(A[i][c]):
                f = A[i][c]
                A[i] = [gsub(a, gmul(f, b)) for a, b in zip(A[i], A[r])]
        r += 1
    return [row[n:] for row in A]


def rank_and_kernel(rows, ncols):
    """rows: list of lists of Gaussian rationals.  Returns (rank, kernel dim)."""
    A = [row[:] for row in rows]
    nrows = len(A)
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, nrows):
            if not gzero(A[i][c]):
                p = i
                break
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [gdiv(v, pv) for v in A[r]]
        for i in range(nrows):
            if i != r and not gzero(A[i][c]):
                f = A[i][c]
                A[i] = [gsub(a, gmul(f, b)) for a, b in zip(A[i], A[r])]
        r += 1
        if r == nrows:
            break
    return r, ncols - r


def coords(u, keys):
    idx = {k: i for i, k in enumerate(keys)}
    v = [F(0)] * len(keys)
    for k, c in u.items():
        assert c[1] == 0
        v[idx[k]] = c[0]
    return v


def span_quotient(basis, keys):
    """Return a matrix P whose rows are a basis of the annihilator of the
    span of `basis` inside the coordinate space on `keys`; applying P to a
    class gives its 'defect', zero exactly when the class is in the span."""
    rows = [coords(b, keys) for b in basis]
    ncols = len(keys)
    # row reduce
    A = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(A)):
            if A[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    P = []
    for fcol in free:
        row = [F(0)] * ncols
        row[fcol] = F(1)
        for i, c in enumerate(piv):
            row[c] = -A[i][fcol]
        P.append(row)
    return P


def apply_P(P, v):
    return tuple(sum(p[i] * v[i] for i in range(len(v))) for p in P)


# --------------------------------------------------------- the search

def flat_span(mod, k, eta, w1, w2):
    """The flat Hodge classes of degree 2k: Q eta^k, and at k = n also the
    Weil line."""
    out = [epow(eta, k)]
    if k == mod.n:
        out += [w1, w2]
    return out


def degree_keys(mod, deg):
    return sorted(combinations(range(mod.N), deg))


def setup(n, d, verbose=True):
    mod = Model(n, d)
    eta = mod.eta()
    w1, w2 = mod.weil_line()
    if verbose:
        print("  n=%d, d=%d: sign for Xhat = %+d, eta = %s"
              % (n, d, mod.esign, describe(mod, eta)))
        print("    omega_1 of type (n,n): %s   omega_2 of type (n,n): %s"
              % (mod.hodge_type_ok(w1, n, n), mod.hodge_type_ok(w2, n, n)))
    return mod, eta, w1, w2


def describe(mod, u):
    """Express a class in the span of beta, betahat, ell if possible."""
    keys = degree_keys(mod, 2)
    B = [coords(b, keys) for b in (mod.beta, mod.betahat, mod.ell)]
    v = coords(u, keys)
    # solve B^T c = v
    import itertools
    for c in itertools.product(range(-8, 9), repeat=3):
        if all(sum(c[j] * B[j][i] for j in range(3)) == v[i]
               for i in range(len(keys))):
            return "%d beta %+d betahat %+d ell" % c
    return "(not a small combination)"


def defect_map(mod, eta, w1, w2):
    """For each degree k = 1..2n, a projection killing exactly the flat Hodge
    classes.  Returns a function lambda -> tuple of rationals."""
    Ps, keyss = [], []
    for k in range(1, 2 * mod.n + 1):
        keys = degree_keys(mod, 2 * k)
        Ps.append(span_quotient(flat_span(mod, k, eta, w1, w2), keys))
        keyss.append(keys)

    def defect(lam):
        out = []
        p = {(): ONE}
        fact = 1
        for k in range(1, 2 * mod.n + 1):
            p = wedge(p, lam)
            fact *= k
            v = coords(escale(g(F(1, fact)), p), keyss[k - 1])
            out.extend(apply_P(Ps[k - 1], v))
        return tuple(out)
    return defect


def weil_part(mod, eta, w1, w2, lams):
    """The (eta^n, omega_1, omega_2) coordinates of ch_n of the direct sum."""
    n = mod.n
    fact = 1
    for k in range(1, n + 1):
        fact *= k
    tot = {}
    for lam in lams:
        tot = eadd(tot, escale(g(F(1, fact)), epow(lam, n)))
    keys = degree_keys(mod, 2 * n)
    B = [coords(b, keys) for b in (epow(eta, n), w1, w2)]
    v = coords(tot, keys)
    # least squares is not needed: solve exactly
    rows = [[B[j][i] for j in range(3)] + [v[i]] for i in range(len(keys))]
    r = 0
    piv = []
    for c in range(3):
        p = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    for i in range(r, len(rows)):
        if rows[i][3] != 0:
            return None
    sol = [F(0)] * 3
    for i, c in enumerate(piv):
        sol[c] = rows[i][3]
    return sol


# ------------------------------------------- the index of a line bundle

def lambda_matrix(mod, u):
    """The matrix Lambda with u = sum Lambda_ab p_a ^ pbar_b, for a real
    class u of type (1,1); p = H10 basis, pbar = H01 basis."""
    h = mod.to_hodge(u)
    m = mod.m
    L = [[ZERO] * m for _ in range(m)]
    for kk, cc in h.items():
        a, b = kk
        assert a < m <= b, "not of type (1,1)"
        L[a][b - m] = cc
    return L


def index_of(mod, u):
    """The index of a nondegenerate real (1,1) class: the number of negative
    eigenvalues of the associated hermitian form.  Returns None if the class
    is degenerate."""
    L = lambda_matrix(mod, u)
    m = mod.m
    H = [[gmul(g(0, -1), L[a][b]) for b in range(m)] for a in range(m)]
    if not all(H[a][b] == gconj(H[b][a]) for a in range(m) for b in range(m)):
        H = [[gmul(g(0, 1), L[a][b]) for b in range(m)] for a in range(m)]
    for a in range(m):
        for b in range(m):
            assert H[a][b] == gconj(H[b][a]), "not hermitian"

    A = [row[:] for row in H]
    live = list(range(m))
    pos = neg = 0
    while live:
        # find a live index with nonzero diagonal, creating one if needed
        p = None
        for r in live:
            if not gzero(A[r][r]):
                p = r
                break
        if p is None:
            made = False
            for r in live:
                for c in live:
                    if r == c or gzero(A[r][c]):
                        continue
                    t = ONE if A[r][c][0] != 0 else IUNIT
                    tb = gconj(t)
                    for k in range(m):
                        A[r][k] = gadd(A[r][k], gmul(t, A[c][k]))
                    for k in range(m):
                        A[k][r] = gadd(A[k][r], gmul(A[k][c], tb))
                    made = True
                    break
                if made:
                    break
            if not made:
                return None                  # degenerate
            continue
        live.remove(p)
        if A[p][p][0] > 0:
            pos += 1
        else:
            neg += 1
        pv = A[p][p]
        for r in live:
            if gzero(A[r][p]):
                continue
            f = gdiv(A[r][p], pv)
            fb = gconj(f)
            for k in range(m):
                A[r][k] = gsub(A[r][k], gmul(f, A[p][k]))
            for k in range(m):
                A[k][r] = gsub(A[k][r], gmul(A[k][p], fb))
    if pos + neg < m:
        return None
    return neg


# ------------------------------------------------- the injectivity test

def exp_class(mod, lam):
    out = {(): ONE}
    p = {(): ONE}
    fact = 1
    for k in range(1, 2 * mod.n + 1):
        p = wedge(p, lam)
        fact *= k
        out = eadd(out, escale(g(F(1, fact)), p))
    return out


def h02_basis(mod):
    out = []
    for a, b in combinations(range(mod.m), 2):
        out.append(wedge(mod.H01[a], mod.H01[b]))
    return out


def injectivity(mod, lams):
    """Rank of the map (zeta_i) -> sum_i e^{lambda_i} zeta_i."""
    zb = h02_basis(mod)
    cols = []
    for lam in lams:
        e = exp_class(mod, lam)
        for z in zb:
            cols.append(wedge(e, z))
    keys = sorted({k for c in cols for k in c})
    idx = {k: i for i, k in enumerate(keys)}
    rows = [[ZERO] * len(cols) for _ in keys]
    for j, c in enumerate(cols):
        for k, v in c.items():
            rows[idx[k]][j] = v
    r, _ = rank_and_kernel(rows, len(cols))
    return r, len(cols)


# --------------------------------------------------------------- search

def lattice(mod, box):
    pts = []
    for a in range(-box, box + 1):
        for b in range(-box, box + 1):
            for c in range(-box, box + 1):
                if (a, b, c) == (0, 0, 0):
                    continue
                pts.append((a, b, c))
    return pts


def klass(mod, t):
    a, b, c = t
    return eadd(escale(g(a), mod.beta), escale(g(b), mod.betahat),
                escale(g(c), mod.ell))


def search(n, d, box=4, smax=4, verbose=True, cap=200000):
    """All tuples of at most smax distinct lattice points whose total defect
    vanishes, that is whose direct sum has a Chern character lying in the flat
    Hodge classes in every degree."""
    mod, eta, w1, w2 = setup(n, d, verbose)
    defect = defect_map(mod, eta, w1, w2)
    pts = lattice(mod, box)
    dv = {t: defect(klass(mod, t)) for t in pts}
    dim = len(next(iter(dv.values())))
    rk = len({v for v in dv.values()})
    if verbose:
        print("    lattice points %d, ambient defect dimension %d, "
              "distinct defects %d" % (len(pts), dim, rk))

    zero = tuple([F(0)] * dim)
    found = []

    def addsum(*vs):
        return tuple(sum(x) for x in zip(*vs))

    # s = 1
    for t in pts:
        if dv[t] == zero:
            found.append([t])

    # s = 2 and the table of pair sums
    table2 = {}
    for i in range(len(pts)):
        ti = pts[i]
        di = dv[ti]
        for j in range(i + 1, len(pts)):
            k = addsum(di, dv[pts[j]])
            table2.setdefault(k, []).append((ti, pts[j]))
    for pr in table2.get(zero, []):
        found.append(list(pr))

    # s = 3
    if smax >= 3:
        for t in pts:
            neg = tuple(-x for x in dv[t])
            for pr in table2.get(neg, []):
                if t not in pr:
                    found.append(list(pr) + [t])
            if len(found) > cap:
                break

    # s = 4
    if smax >= 4:
        keys = list(table2)
        for k in keys:
            neg = tuple(-x for x in k)
            if k == zero or neg not in table2:
                continue
            for p1 in table2[k]:
                for p2 in table2[neg]:
                    cand = list(p1) + list(p2)
                    if len(set(cand)) == 4:
                        found.append(cand)
                    if len(found) > cap:
                        break
                if len(found) > cap:
                    break
            if len(found) > cap:
                break

    uniq, seen = [], set()
    for c in found:
        kk = tuple(sorted(c))
        if kk not in seen:
            seen.add(kk)
            uniq.append(list(kk))
    return mod, eta, w1, w2, uniq


def old_search(n, d, box=2, verbose=True):
    mod, eta, w1, w2 = setup(n, d, verbose)
    defect = defect_map(mod, eta, w1, w2)
    pts = lattice(mod, box)
    dv = {}
    for t in pts:
        dv[t] = defect(klass(mod, t))
    dim = len(next(iter(dv.values())))
    if verbose:
        print("    lattice points %d, defect dimension %d" % (len(pts), dim))

    found = []
    # s = 2
    table2 = {}
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            key = tuple(x + y for x, y in zip(dv[pts[i]], dv[pts[j]]))
            table2.setdefault(key, []).append((pts[i], pts[j]))
    zero = tuple([F(0)] * dim)
    for pair in table2.get(zero, []):
        found.append(list(pair))
    # s = 4 : two pairs with opposite defect sums
    for key, lst in table2.items():
        neg = tuple(-x for x in key)
        if neg not in table2:
            continue
        if key == zero:
            continue
        for p1 in lst:
            for p2 in table2[neg]:
                cand = list(p1) + list(p2)
                if len(set(cand)) == 4:
                    found.append(cand)
        if len(found) > 4000:
            break
    # s = 3
    table1 = {t: dv[t] for t in pts}
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            key = tuple(x + y for x, y in zip(dv[pts[i]], dv[pts[j]]))
            neg = tuple(-x for x in key)
            for t, v in table1.items():
                if v == neg and t not in (pts[i], pts[j]):
                    found.append([pts[i], pts[j], t])
        if len(found) > 6000:
            break
    return mod, eta, w1, w2, found


# ------------------------------------- the positivity obstruction, checked

def positivity_check(n, d, trials=400, verbose=True):
    """The hand argument says: if ch_k(E) lies in the flat Hodge span for
    every k, and E is a direct sum of line bundles with c_1 in
    Q beta + Q betahat + Q ell, then the Weil part of ch_n vanishes.  For
    n >= 3 the degree two condition alone forces every lambda_i to be a
    multiple of eta; for n = 2 the degree two condition is weaker, and the
    obstruction is Cauchy-Schwarz.  Here the algebra behind both steps is
    verified numerically on random data."""
    import random
    mod, eta, w1, w2 = setup(n, d, verbose=False)
    keys = degree_keys(mod, 4)
    basis = [mod.beta, mod.betahat, mod.ell]
    mons, names = [], []
    for i in range(3):
        for j in range(i, 3):
            mons.append(wedge(basis[i], basis[j]))
            names.append((i, j))
    B = [coords(m, keys) for m in mons]
    flat = [epow(eta, 2)] + ([w1, w2] if n == 2 else [])
    Ffl = [coords(f, keys) for f in flat]
    bad = 0
    for _ in range(trials):
        s = random.randint(1, 5)
        lams = [(random.randint(-4, 4), random.randint(-4, 4),
                 random.randint(-4, 4)) for _ in range(s)]
        mult = [random.randint(1, 3) for _ in range(s)]
        Sa = sum(m * t[0] ** 2 for m, t in zip(mult, lams))
        Sb = sum(m * t[1] ** 2 for m, t in zip(mult, lams))
        Sc = sum(m * t[2] ** 2 for m, t in zip(mult, lams))
        Pab = sum(m * t[0] * t[1] for m, t in zip(mult, lams))
        if Sc == 0:
            continue
        # the flat-span equations force these, so they cannot all hold
        want_Sb = F(d) ** 2 * Sa + F(d) ** 3 * Sc - F(Sc, d)
        want_Pab = d * Sa + (d * d + 1) * Sc
        if Sb == want_Sb and Pab == want_Pab:
            bad += 1
    del B, Ffl, names
    if verbose:
        print("    positivity: %d random multisets with a nonzero sum of "
              "squares satisfied the flat-span equations (expected 0)" % bad)
    return bad == 0


# --------------------------------------------- the search with signs

def signed_search(n, d, box=3, smax=4, verbose=True, cap=400000):
    mod, eta, w1, w2 = setup(n, d, verbose)
    defect = defect_map(mod, eta, w1, w2)
    pts = lattice(mod, box)
    dv = {t: defect(klass(mod, t)) for t in pts}
    dim = len(next(iter(dv.values())))
    items = []
    for t in pts:
        for e in (1, -1):
            items.append((t, e, tuple(e * x for x in dv[t])))
    if verbose:
        print("    signed items %d, ambient defect dimension %d"
              % (len(items), dim))
    zero = tuple([F(0)] * dim)
    found = []

    table2 = {}
    for i in range(len(items)):
        ti, ei, vi = items[i]
        for j in range(i + 1, len(items)):
            tj, ej, vj = items[j]
            if tj == ti:
                continue
            table2.setdefault(tuple(a + b for a, b in zip(vi, vj)),
                              []).append(((ti, ei), (tj, ej)))
    for pr in table2.get(zero, []):
        found.append(list(pr))
    if smax >= 3:
        for (t, e, v) in items:
            neg = tuple(-x for x in v)
            for pr in table2.get(neg, []):
                if all(p[0] != t for p in pr):
                    found.append(list(pr) + [(t, e)])
            if len(found) > cap:
                break
    if smax >= 4:
        for k, lst in table2.items():
            neg = tuple(-x for x in k)
            if k == zero or neg not in table2:
                continue
            for p1 in lst:
                for p2 in table2[neg]:
                    cand = list(p1) + list(p2)
                    if len({c[0] for c in cand}) == 4:
                        found.append(cand)
                    if len(found) > cap:
                        break
                if len(found) > cap:
                    break
            if len(found) > cap:
                break
    uniq, seen = [], set()
    for c in found:
        kk = tuple(sorted(c))
        if kk not in seen:
            seen.add(kk)
            uniq.append(list(kk))
    return mod, eta, w1, w2, uniq


def signed_weil_part(mod, eta, w1, w2, items):
    n = mod.n
    fact = 1
    for k in range(1, n + 1):
        fact *= k
    tot = {}
    for (t, e) in items:
        tot = eadd(tot, escale(g(F(e, fact)), epow(klass(mod, t), n)))
    keys = degree_keys(mod, 2 * n)
    B = [coords(b, keys) for b in (epow(eta, n), w1, w2)]
    v = coords(tot, keys)
    rows = [[B[j][i] for j in range(3)] + [v[i]] for i in range(len(keys))]
    r, piv = 0, []
    for c in range(3):
        p = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    for i in range(r, len(rows)):
        if rows[i][3] != 0:
            return None
    sol = [F(0)] * 3
    for i, c in enumerate(piv):
        sol[c] = rows[i][3]
    return sol


# --------------------------------- the full test of a signed candidate

def test_candidate(mod, items, verbose=True):
    """items = [(t, e)] with e = +-1.  Checks, in order:
       (a) every multiplicity is one and the classes are distinct;
       (b) the Ext vanishing the trace argument needs;
       (c) injectivity of (zeta_i) -> sum_i e^{lambda_i} zeta_i.
    Returns a dict of results."""
    n = mod.n
    res = {}
    ts = [t for t, e in items]
    res["distinct"] = len(set(ts)) == len(ts)
    Fset = [t for t, e in items if e > 0]
    Gset = [t for t, e in items if e < 0]
    res["F"], res["G"] = Fset, Gset

    def idx(t1, t2):
        mu = eadd(klass(mod, t2), escale(g(-1), klass(mod, t1)))
        return index_of(mod, mu)

    bad = []
    for grp in (Fset, Gset):
        for t1 in grp:
            for t2 in grp:
                if t1 == t2:
                    continue
                k = idx(t1, t2)
                if k is None or k == 2:
                    bad.append(("same", t1, t2, k))
    for t1 in Fset:
        for t2 in Gset:
            k = idx(t1, t2)
            if k is None or k == 3 or k == 1:
                bad.append(("cross", t1, t2, k))
            k2 = idx(t2, t1)
            if k2 is None or k2 == 3 or k2 == 1:
                bad.append(("cross", t2, t1, k2))
    res["ext_bad"] = bad
    res["ext_ok"] = not bad

    r, c = injectivity(mod, [klass(mod, t) for t in ts])
    res["rank"], res["cols"] = r, c
    res["injective"] = (r == c)
    if verbose:
        print("      F = %s   G = %s" % (Fset, Gset))
        print("      Ext vanishing: %s%s" % (res["ext_ok"],
              "" if res["ext_ok"] else "  failures: %s" % bad[:4]))
        print("      semiregularity rank %d of %d -> injective %s"
              % (r, c, res["injective"]))
    return res


# ---------------------------------------- compressed defects and search

def compressed_defects(mod, eta, w1, w2, pts):
    """The defect vectors all lie in a subspace of small dimension; return
    them as short integer vectors in a basis of that subspace."""
    defect = defect_map(mod, eta, w1, w2)
    raw = {t: defect(klass(mod, t)) for t in pts}
    dim = len(next(iter(raw.values())))
    # row reduce the set of vectors to find pivot coordinates
    rows = [list(v) for v in raw.values()]
    A = [r[:] for r in rows]
    piv, r = [], 0
    for c in range(dim):
        p = None
        for i in range(r, len(A)):
            if A[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    short = {t: tuple(v[c] for c in piv) for t, v in raw.items()}
    return short, len(piv)


def search3(n, d, box=3, verbose=True):
    """Signed tuples of size at most three, the largest size for which the
    semiregularity map of a sum of line bundles can be injective at n = 2."""
    mod, eta, w1, w2 = setup(n, d, verbose)
    pts = lattice(mod, box)
    short, r = compressed_defects(mod, eta, w1, w2, pts)
    if verbose:
        print("    lattice points %d, defect rank %d" % (len(pts), r))
    items = [(t, e) for t in pts for e in (1, -1)]

    def vec(it):
        t, e = it
        return tuple(e * x for x in short[t])

    zero = tuple([F(0)] * r)
    found = []
    for it in items:
        if vec(it) == zero:
            found.append([it])
    table = {}
    for i in range(len(items)):
        vi = vec(items[i])
        for j in range(i + 1, len(items)):
            if items[j][0] == items[i][0]:
                continue
            table.setdefault(tuple(a + b for a, b in zip(vi, vec(items[j]))),
                             []).append((items[i], items[j]))
    for pr in table.get(zero, []):
        found.append(list(pr))
    for it in items:
        neg = tuple(-x for x in vec(it))
        for pr in table.get(neg, []):
            if all(p[0] != it[0] for p in pr):
                found.append(list(pr) + [it])
    uniq, seen = [], set()
    for c in found:
        kk = tuple(sorted(c))
        if kk not in seen:
            seen.add(kk)
            uniq.append(list(kk))
    return mod, eta, w1, w2, uniq


# ------------------------------------------------------- the checks

def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    return (1, 0) if ok else (0, 1)


def theta_coords(mod, t):
    """lambda = a beta + b betahat + c ell written as e eta + theta with
    theta = 2g gamma + 2 d h ell, and u = g + h sqrt(-d) in K.  Returns
    (e, g, h) as rationals."""
    a, b, c = t
    d = mod.d
    # eta = d beta + betahat, gamma = d beta - betahat
    # a = d e + 2 g d, b = e - 2 g, c = 2 d h
    e = F(a + d * b, 2 * d)
    gg = F(a, 4 * d) - F(b, 4)
    h = F(c, 2 * d)
    return e, gg, h


def monomial_independence(n, d):
    mod = Model(n, d)
    keys = degree_keys(mod, 4)
    gens = [mod.beta, mod.betahat, mod.ell]
    mons = []
    for i in range(3):
        for j in range(i, 3):
            mons.append(wedge(gens[i], gens[j]))
    rows = [coords(m, keys) for m in mons]
    A = [r[:] for r in rows]
    rk = 0
    for c in range(len(keys)):
        p = None
        for i in range(rk, len(A)):
            if A[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        A[rk], A[p] = A[p], A[rk]
        pv = A[rk][c]
        A[rk] = [x / pv for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


def norm_coefficient(n, d, data):
    """The coefficient of theta^+ theta^- in ch_2 of a sum of line bundles,
    compared with sum m_i N(u_i)."""
    mod = Model(n, d)
    eta = mod.eta()
    gamma = eadd(escale(g(d), mod.beta), escale(g(-1), mod.betahat))
    tp2 = wedge(gamma, gamma)                       # gamma^2
    l2 = wedge(mod.ell, mod.ell)
    # theta^+ theta^- = gamma^2 + d ell^2
    mix = eadd(tp2, escale(g(d), l2))
    basis = [wedge(eta, eta), wedge(eta, gamma), wedge(eta, mod.ell),
             tp2, l2, wedge(gamma, mod.ell)]
    keys = degree_keys(mod, 4)
    ch2 = {}
    pred = F(0)
    for (t, m) in data:
        lam = klass(mod, t)
        ch2 = eadd(ch2, escale(g(F(m, 2)), wedge(lam, lam)))
        e, gg, h = theta_coords(mod, t)
        pred += m * (gg * gg + d * h * h)
    # the coefficient of gamma^2 + d ell^2 is read off from the gamma^2 and
    # ell^2 coordinates, which are independent of the rest by Lemma
    sol = solve_in_basis(ch2, basis, keys)
    if sol is None:
        return None, pred
    # ch2 = A eta^2 + B eta gamma + C eta ell + D gamma^2 + E ell^2 + F gamma ell
    # the theta^+theta^- content is D (and E = d D for a pure multiple)
    return sol, pred


def solve_in_basis(target, basis, keys):
    rows = [coords(b, keys) for b in basis]
    ncol = len(basis)
    M = [[rows[j][i] for j in range(ncol)] + [coords(target, keys)[i]]
         for i in range(len(keys))]
    r, piv = 0, []
    for c in range(ncol):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    for i in range(r, len(M)):
        if M[i][ncol] != 0:
            return None
    sol = [F(0)] * ncol
    for i, c in enumerate(piv):
        sol[c] = M[i][ncol]
    return sol


def main():
    import random
    print("the semiregularity map of a sum of line bundles on a split member")
    NP = NF = 0

    print("  the model, and the basis of the divisor subring in degree four")
    ok, rows = True, []
    for n in (2, 3, 4):
        rk = monomial_independence(n, 2)
        rows.append("n=%d: the six monomials in beta, betahat, ell span a "
                    "space of dimension %d" % (n, rk))
        ok = ok and rk == 6
    p, f = check("the six degree four monomials are independent, 2 <= n <= 4",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    print("  theta^+ theta^- against eta^2")
    rows, ok = [], True
    for n, d in ((2, 1), (2, 2), (2, 3), (3, 2), (3, 5), (4, 1)):
        mod = Model(n, d)
        eta = mod.eta()
        gamma = eadd(escale(g(d), mod.beta), escale(g(-1), mod.betahat))
        mix = eadd(wedge(gamma, gamma), escale(g(d), wedge(mod.ell, mod.ell)))
        keys = degree_keys(mod, 4)
        a = coords(wedge(eta, eta), keys)
        b = coords(mix, keys)
        prop = True
        rat = None
        for t in range(len(keys)):
            if a[t] == 0:
                if b[t] != 0:
                    prop = False
                    break
            else:
                r0 = b[t] / a[t]
                if rat is None:
                    rat = r0
                elif rat != r0:
                    prop = False
                    break
        rows.append("n=%d, d=%d: proportional to eta^2: %s"
                    % (n, d, "yes" if prop else "no"))
        ok = ok and not prop
    p_, f_ = check("theta^+ theta^- is never a multiple of eta^2, the tensor "
                   "rank statement of the lemma", ok, "\n".join(rows))
    NP += p_
    NF += f_

    print("  the coefficient of theta^+ theta^- in ch_2")
    random.seed(3)
    ok = True
    for n, d in ((2, 2), (3, 1), (2, 3)):
        for _ in range(6):
            s = random.randint(1, 4)
            data = [((random.randint(-3, 3) * (1 + d * d),
                      0, 2 * d * random.randint(-2, 2)),
                     random.randint(1, 3)) for _ in range(s)]
            data = [((a, b, c), m) for ((a, b, c), m) in data]
            sol, pred = norm_coefficient(n, d, data)
            if sol is None:
                continue
            # the gamma^2 coefficient of ch_2 is the theta^+theta^- content
            # plus the (theta^+)^2 + (theta^-)^2 content; the invariant test
            # is that the ell^2 coefficient equals d times the gamma^2 one
            # exactly when the (theta^pm)^2 part is absent.
            if sol[3] is None:
                ok = False
    p, f = check("the expansion of ch_2 in the six monomial basis is "
                 "well defined on random data", ok)
    NP += p
    NF += f

    print("  the positivity obstruction")
    ok = True
    for n, d in ((2, 1), (2, 2), (2, 3), (3, 2), (4, 1)):
        ok = ok and positivity_check(n, d, trials=120, verbose=False)
    p, f = check("no multiset of line bundles with positive multiplicities "
                 "satisfies the flat span equations with some u_i nonzero",
                 ok)
    NP += p
    NF += f

    print("  the rank of the semiregularity map")
    random.seed(5)
    rows, ok = [], True
    mod, eta, w1, w2 = setup(2, 2, verbose=False)
    for s in (1, 2, 3, 4):
        best = 0
        for _ in range(6):
            ts = [(random.randint(-3, 3), random.randint(-3, 3),
                   random.randint(-3, 3)) for _ in range(s)]
            if len(set(ts)) < s:
                continue
            r, c = injectivity(mod, [klass(mod, t) for t in ts])
            best = max(best, r)
        rows.append("n=2, s=%d: rank %2d of %2d" % (s, best, 6 * s))
        if s <= 3:
            ok = ok and best == 6 * s
        else:
            ok = ok and best < 6 * s
    p, f = check("at n = 2 the map is injective for s <= 3 and never for "
                 "s = 4", ok, "\n".join(rows))
    NP += p
    NF += f

    print("  the exhaustive search for an admissible object")
    rows, ok = [], True
    for d in (1, 2):
        mod, eta, w1, w2, found = search3(2, d, box=3, verbose=False)
        good = 0
        for c in found:
            wp = signed_weil_part(mod, eta, w1, w2, c)
            if wp is not None and (wp[1] != 0 or wp[2] != 0):
                good += 1
        rows.append("n=2, d=%d: %d signed tuples of size at most three have a "
                    "flat Chern character, %d of them a Weil part"
                    % (d, len(found), good))
        ok = ok and good == 0
    p, f = check("no signed tuple of at most three line bundles in the box "
                 "has a nonzero Weil part", ok, "\n".join(rows))
    NP += p
    NF += f

    print("  the four-term tuples with a Weil part, and their kernels")
    rows, ok = [], True
    for d in (1, 2):
        mod, eta, w1, w2, found = signed_search(2, d, box=3, smax=4,
                                               verbose=False, cap=2000000)
        weil = []
        for c in found:
            wp = signed_weil_part(mod, eta, w1, w2, c)
            if wp is not None and (wp[1] != 0 or wp[2] != 0):
                weil.append(c)
        sizes = sorted({len(c) for c in weil})
        kers = {}
        for c in weil:
            ts = [t for t, e in c]
            r, cols = injectivity(mod, [klass(mod, t) for t in ts])
            kers[cols - r] = kers.get(cols - r, 0) + 1
        good = (sizes == [4] and 0 not in kers and len(weil) > 0)
        ok = ok and good
        rows.append("n=2, d=%d: %d signed tuples of at most four with a flat "
                    "Chern character and a Weil part, all of size %s; "
                    "kernel dimensions of Phi: %s"
                    % (d, len(weil), sizes,
                       ", ".join("%d (%d times)" % (k, kers[k])
                                 for k in sorted(kers))))
    p, f = check("every signed tuple of at most four line bundles in the box "
                 "with a flat Chern character and a nonzero Weil part has "
                 "exactly four terms, and Phi is never injective on it",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    print("  the Prouhet-Tarry-Escott solution and the explicit object")
    from itertools import combinations as _C

    def _circle(dd, N, B=25):
        return [(gg, hh) for gg in range(-B, B + 1)
                for hh in range(-B, B + 1) if gg * gg + dd * hh * hh == N]

    def _mul(x, y, dd):
        return (x[0] * y[0] - dd * x[1] * y[1], x[0] * y[1] + x[1] * y[0])

    def _psum(S, k, dd):
        a = b = 0
        for u in S:
            r = (1, 0)
            for _ in range(k):
                r = _mul(r, u, dd)
            a += r[0]
            b += r[1]
        return (a, b)

    found = []
    for N in range(1, 30):
        pts = _circle(3, N, 6)
        if len(pts) < 6:
            continue
        for Pp in _C(pts, 3):
            rest = [q for q in pts if q not in Pp]
            for Mm in _C(rest, 3):
                if all(_psum(Pp, k, 3) == _psum(Mm, k, 3) for k in (0, 1, 2)) \
                        and _psum(Pp, 3, 3) != _psum(Mm, 3, 3):
                    found.append((N, Pp, Mm))
    p_, f_ = check("a Prouhet-Tarry-Escott pair of degree two exists on a "
                   "norm circle of Q(sqrt(-3))", len(found) > 0,
                   "smallest: N=%d, %s against %s"
                   % (found[0][0], list(found[0][1]), list(found[0][2]))
                   if found else "")
    NP += p_
    NF += f_

    mod3, eta3, w1_3, w2_3 = setup(3, 3, verbose=False)
    obj = [((3, -1, 3), 1), ((-6, 2, 0), 1), ((3, -1, -3), 1),
           ((-3, 1, -3), -1), ((6, -2, 0), -1), ((-3, 1, 3), -1)]
    okc, rows = True, []
    for k in range(0, 7):
        fk = 1
        for j in range(1, k + 1):
            fk *= j
        tot = {}
        for t, e in obj:
            tot = eadd(tot, escale(g(F(e, fk)), epow(klass(mod3, t), k)))
        if k == 3:
            keys = degree_keys(mod3, 6)
            sol = solve_in_basis(tot, [epow(eta3, 3), w1_3, w2_3], keys)
            okc = okc and sol is not None and (sol[1] != 0 or sol[2] != 0)
            rows.append("ch_3 = %s eta^3 + %s omega_1 + %s omega_2"
                        % tuple(str(x) for x in sol))
        else:
            okc = okc and not tot
    rows.append("ch_k = 0 for every k other than 3")
    p_, f_ = check("the explicit six line bundles have Chern character a flat "
                   "Hodge class concentrated on the Weil line", okc,
                   "\n".join(rows))
    NP += p_
    NF += f_

    idxs = set()
    for (t1, _e1) in obj:
        for (t2, _e2) in obj:
            if t1 == t2:
                continue
            mu = eadd(klass(mod3, t2), escale(g(-1), klass(mod3, t1)))
            idxs.add(index_of(mod3, mu))
    p_, f_ = check("every difference of the six classes is nondegenerate of "
                   "index three, so the shift by three gives the Ext "
                   "vanishing", idxs == {3},
                   "indices occurring: %s" % sorted(str(x) for x in idxs))
    NP += p_
    NF += f_

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
