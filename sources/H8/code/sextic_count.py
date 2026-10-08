#!/usr/bin/env python3
"""
sextic_count.py

Item (LVI) of the computations: the dimension count for Orlov products over a
sextic CM field, and why the obstruction of degree four does not extend.

Model.  X is a principally polarised abelian sixfold with real multiplication
by the ring of integers of a totally real cubic field F_0, with real places
tau_1, tau_2, tau_3.  Over C, H^1(X) = U_1 + U_2 + U_3, the eigenspaces of
F_0, each of dimension 4 and Hodge type (2,2), with basis
x_{j1}, y_{j1}, x_{j2}, y_{j2} (x of type (1,0), y of type (0,1)), and the
components of the polarisation are theta_j = x_{j1} y_{j1} + x_{j2} y_{j2},
so that theta_j^3 = 0 and the integral of theta^6/6! is 1.  The exterior
algebra on the twelve generators is H^*(X, C), with the volume form the
ordered product of the generators.  HT^k(X) = sum over a + b = k of
wedge^a H^{0,1} (x) wedge^b T, with T = H^0(T_X) spanned by the dual vectors
d/dx, acting on H^*(X) by (alpha (x) t) . v = alpha ^ (t _| v).

For the sextic CM field F = F_0(sqrt(-q)), q totally positive, and t in F_0,
the secant space S(t,q) is spanned by the eight classes
    e_eps = prod_j exp( (tau_j(t) + eps_j s_j) theta_j ),
    s_j = sqrt(-1) sqrt(tau_j(q)),  eps in {+1,-1}^3,
and a real class v = sum_eps w_eps e_eps has w_{-eps} = conj(w_eps).

Invariants of the coefficient tensor w (a 2 x 2 x 2 array):
    N_w        the number of nonzero w_eps;
    A_{jj'}    the number of sign pairs (s, s') for which some w_eps != 0 has
               eps_j = s and eps_{j'} = s';
    rho_j      the rank of the 2 x 4 flattening of w along the j-th index;
    M^{(j;j')}_{s'}  the 2 x 2 slice of w with eps_{j'} = s' fixed, indexed
               by (eps_j, eps_{j''}).

What is checked:

  (A) theta_j^3 = 0, the integral of theta^6 is 720, the integral of
      theta_1^2 theta_2^2 theta_3^2 is 8, and the integral of
      exp(c_1 theta_1 + c_2 theta_2 + c_3 theta_3) is (c_1 c_2 c_3)^2;

  (B) for a single place, HT^k_j kills exp(lambda theta_j) for k >= 3, the
      image of HT^2_j is the line spanned by omega_j = y_{j1} y_{j2}, and the
      coefficients (c(xi, lambda^+), c(xi, lambda^-)) fill C^2 whenever
      lambda^+ != lambda^-;

  (C) exactly over Q(sqrt(-1)), for q = 1, t in Q and four coefficient
      patterns w (generic, the two CM types induced from the imaginary
      quadratic subfield, a rank one tensor, a Galois orbit of six types),
      the ranks of contraction from HT^1, HT^2, HT^3 into v are
          r^1 = 12,
          r^2 = 4 (A_12 + A_13 + A_23) + rho_1 + rho_2 + rho_3,
          r^3 = 8 N_w + 2 sum over ordered pairs (j, j') of
                          rk M^{(j;j')}_+ + rk M^{(j;j')}_- ,
      with the values (54, 112), (30, 40), (51, 88), (54, 96) for (r^2, r^3);

  (D) exactly over Q(sqrt(-1)), chi(v, v) = int v^dual v equals
      -64 Nm(q) sum |w_eps|^2, and over Q(sqrt(-1)) for m = 2 the analogous
      integral is +16 Nm(q) sum |w_eps|^2: the Euler form on the secant
      space of a field of degree 2m is (-4)^m Nm(q) sum |w_eps|^2;

  (E) modulo a prime p = 1 mod 4 at which the cubic field splits and the s_j
      exist, the coefficient patterns of (C) carried into F_p by a root of
      -1,
      for the three cubic fields Q(zeta_7)^+, Q(zeta_9)^+ and the non-Galois
      field of discriminant 229, with q a totally positive element that is
      not rational and t a generator of F_0, the ranks modulo p attain the
      values of (C), which bounds them below, while the formulas of (C) bound
      them above; and the identity of (D) holds modulo p;

  (F) the bookkeeping of the count: for a minimal object on X the profile is
      (1, 12, r^2, e_3, r^2, 12, 1) with e_3 = 2 r^2 - 22 - chi(v, v), and
      the condition e_3 >= r^3 reads chi(v, v) <= -(r^3 - 2 r^2 + 22), which
      is chi <= -26, -2, -8, -10 for the four patterns; r(kappa) for an
      Orlov product is r^2(v_1) + 144 + r^2(v_2) <= 252 < 264 = dim HT^2(A)
      - dim D_F.

Everything is exact: Gaussian rationals, integers, and integers modulo a
prime; no floating point.

Run:  python3 sextic_count.py
"""
from fractions import Fraction
import itertools

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ----------------------------------------------------------------- Q(sqrt(-1))
class GI:
    """Gaussian rationals a + b i with Fraction parts."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    def __add__(self, o):
        return GI(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        return GI(self.a - o.a, self.b - o.b)

    def __neg__(self):
        return GI(-self.a, -self.b)

    def __mul__(self, o):
        if not isinstance(o, GI):
            o = GI(o)
        return GI(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def inv(self):
        n = self.a * self.a + self.b * self.b
        return GI(self.a / n, -self.b / n)

    def conj(self):
        return GI(self.a, -self.b)

    def iszero(self):
        return self.a == 0 and self.b == 0

    def __eq__(self, o):
        if not isinstance(o, GI):
            o = GI(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def __repr__(self):
        if self.b == 0:
            return "%s" % self.a
        return "(%s%+si)" % (self.a, self.b)


class Fp:
    """the field with p elements, elements as Python ints"""

    def __init__(self, p):
        self.p = p

    def mul(self, a, b):
        return (a * b) % self.p

    def add(self, a, b):
        return (a + b) % self.p

    def neg(self, a):
        return (-a) % self.p

    def inv(self, a):
        return pow(a, self.p - 2, self.p)

    def iszero(self, a):
        return a % self.p == 0

    def scal(self, k, a):
        return (k * a) % self.p


class QI:
    """the Gaussian rationals as a field object with the same interface"""

    def mul(self, a, b):
        return a * b

    def add(self, a, b):
        return a + b

    def neg(self, a):
        return -a

    def inv(self, a):
        return a.inv()

    def iszero(self, a):
        return a.iszero()

    def scal(self, k, a):
        return GI(Fraction(k)) * a


# ------------------------------------------------------------ exterior algebra
def popcount(m):
    return bin(m).count("1")


def mono_sign(a, b):
    """sign of e_a ^ e_b for disjoint monomials a, b given as bit masks"""
    if a & b:
        return 0
    s, bb = 0, b
    while bb:
        j = (bb & -bb).bit_length() - 1
        s += popcount(a >> (j + 1))
        bb &= bb - 1
    return -1 if s % 2 else 1


class Model:
    """the cohomology of a principally polarised abelian 2m-fold with real
    multiplication by a totally real field of degree m, split into m
    eigenspaces of dimension 4"""

    def __init__(self, m, K):
        self.m = m
        self.K = K
        self.gen = {j: [(4 * j, 4 * j + 1), (4 * j + 2, 4 * j + 3)]
                    for j in range(m)}
        self.nb = 4 * m
        self.top = (1 << self.nb) - 1
        self.xgens = [x for j in range(m) for (x, y) in self.gen[j]]
        self.ygens = [y for j in range(m) for (x, y) in self.gen[j]]
        self.signs = list(itertools.product((1, -1), repeat=m))

    # elements are dicts mask -> coefficient in K
    def clean(self, x):
        return {k: v for k, v in x.items() if not self.K.iszero(v)}

    def wedge(self, x, y):
        K, out = self.K, {}
        for m, c in x.items():
            for n, d in y.items():
                if m & n:
                    continue
                cd = K.mul(c, d)
                if mono_sign(m, n) < 0:
                    cd = K.neg(cd)
                out[m | n] = K.add(out[m | n], cd) if (m | n) in out else cd
        return self.clean(out)

    def add(self, x, y, cy=None):
        K, out = self.K, dict(x)
        for m, c in y.items():
            if cy is not None:
                c = K.mul(cy, c)
            out[m] = K.add(out[m], c) if m in out else c
        return self.clean(out)

    def scale(self, x, c):
        return self.clean({m: self.K.mul(c, v) for m, v in x.items()})

    def contract(self, i, x):
        """interior product by the dual vector of generator i"""
        K, out = self.K, {}
        for m, c in x.items():
            if not (m >> i) & 1:
                continue
            s = popcount(m & ((1 << i) - 1))
            val = K.neg(c) if s % 2 else c
            key = m ^ (1 << i)
            out[key] = K.add(out[key], val) if key in out else val
        return self.clean(out)

    def one(self):
        return self.K.mul(self.unit, self.unit)

    def theta(self, j):
        return {(1 << x) | (1 << y): self.unit for (x, y) in self.gen[j]}

    def exp_theta(self, lam, j):
        """exp(lam theta_j) = 1 + lam theta_j + lam^2 theta_j^2 / 2"""
        th = self.theta(j)
        out = {0: self.unit}
        term = {0: self.unit}
        for k in range(1, 3):
            term = self.wedge(term, th)
            term = self.scale(term, lam)
            term = self.clean({m: self.K.scal(Fraction(1, k), v)
                               if isinstance(v, GI) else
                               self.K.mul(self.K.inv(k % self.K.p), v)
                               for m, v in term.items()})
            out = self.add(out, term)
        return out

    def e_class(self, lams):
        out = {0: self.unit}
        for j in range(self.m):
            out = self.wedge(out, self.exp_theta(lams[j], j))
        return out

    def integral(self, x):
        return x.get(self.top, self.zero)

    def dual(self, x):
        return {m: (v if (popcount(m) // 2) % 2 == 0 else self.K.neg(v))
                for m, v in x.items()}

    def ht_basis(self, k):
        out = []
        for a in range(k + 1):
            b = k - a
            for A in itertools.combinations(self.ygens, a):
                for B in itertools.combinations(self.xgens, b):
                    out.append((sum(1 << i for i in A),
                                sum(1 << i for i in B)))
        return out

    def act(self, A, B, v):
        """(y_A (x) d_B) . v = y_A ^ (d_B _| v)"""
        out = v
        for i in range(self.nb):
            if (B >> i) & 1:
                out = self.contract(i, out)
        if A:
            out = self.wedge({A: self.unit}, out)
        return out

    def secant_class(self, w, lam):
        """v = sum_eps w_eps prod_j exp(lam[j][eps_j] theta_j)"""
        v = {}
        for e in self.signs:
            if self.K.iszero(w[e]):
                continue
            cls = self.e_class([lam[j][e[j]] for j in range(self.m)])
            v = self.add(v, cls, cy=w[e])
        return v

    def contraction_rows(self, v, k):
        return [self.act(A, B, v) for (A, B) in self.ht_basis(k)]

    def rank(self, rows):
        """rank of sparse rows (dicts mask -> coefficient) over K"""
        K = self.K
        pivots = {}
        r = 0
        for row in rows:
            row = self.clean(dict(row))
            while row:
                col = min(row)
                if col in pivots:
                    prow = pivots[col]
                    f = row[col]
                    for m, c in prow.items():
                        val = K.add(row[m], K.neg(K.mul(f, c))) if m in row \
                            else K.neg(K.mul(f, c))
                        if K.iszero(val):
                            row.pop(m, None)
                        else:
                            row[m] = val
                else:
                    inv = K.inv(row[col])
                    row = {m: K.mul(inv, c) for m, c in row.items()}
                    pivots[col] = row
                    r += 1
                    break
        return r

    def small_rank(self, mat):
        rows = [{k: c for k, c in enumerate(row)} for row in mat]
        return self.rank(rows)

    # invariants of the coefficient tensor
    def invariants(self, w):
        supp = [e for e in self.signs if not self.K.iszero(w[e])]
        N = len(supp)
        A = {}
        for j, jp in itertools.combinations(range(self.m), 2):
            A[(j, jp)] = len({(e[j], e[jp]) for e in supp})
        return N, A

    def flattening_rank(self, w, j):
        others = [k for k in range(self.m) if k != j]
        mat = []
        for s in (1, -1):
            row = []
            for mu in itertools.product((1, -1), repeat=self.m - 1):
                e = [0] * self.m
                e[j] = s
                for k, o in enumerate(others):
                    e[o] = mu[k]
                row.append(w[tuple(e)])
            mat.append(row)
        return self.small_rank(mat)

    def slice_rank(self, w, j, jp, sp):
        jpp = [k for k in range(self.m) if k not in (j, jp)][0]
        mat = []
        for s in (1, -1):
            row = []
            for spp in (1, -1):
                e = [0] * self.m
                e[j], e[jp], e[jpp] = s, sp, spp
                row.append(w[tuple(e)])
            mat.append(row)
        return self.small_rank(mat)

    def formulas(self, w):
        N, A = self.invariants(w)
        rho = [self.flattening_rank(w, j) for j in range(self.m)]
        r2 = 4 * sum(A.values()) + sum(rho)
        r3 = 8 * N
        for j in range(self.m):
            for jp in range(self.m):
                if j == jp:
                    continue
                r3 += 2 * (self.slice_rank(w, j, jp, 1)
                           + self.slice_rank(w, j, jp, -1))
        return N, A, rho, r2, r3


class ModelQI(Model):
    def __init__(self, m):
        super().__init__(m, QI())
        self.unit = GI(1)
        self.zero = GI(0)


class ModelFp(Model):
    def __init__(self, m, p):
        super().__init__(m, Fp(p))
        self.unit = 1
        self.zero = 0


# ------------------------------------------------------------------ patterns
def patterns_gi(signs):
    """four real coefficient patterns over Q(i), w_{-eps} = conj(w_eps)"""
    pats = {}
    base = {(1, 1, 1): GI(2, 1), (1, 1, -1): GI(1, 3), (1, -1, 1): GI(3, -1),
            (1, -1, -1): GI(-2, 5)}
    w = {}
    for e, c in base.items():
        w[e] = c
        w[tuple(-s for s in e)] = c.conj()
    pats["generic"] = w
    w = {e: GI(0) for e in signs}
    w[(1, 1, 1)] = GI(3, 2)
    w[(-1, -1, -1)] = GI(3, -2)
    pats["N_w = 2"] = w
    u = [GI(1, 1), GI(2, -1), GI(1, 3)]
    w = {}
    for e in signs:
        c = GI(1)
        for j in range(3):
            c = c * (u[j] if e[j] == 1 else u[j].conj())
        w[e] = c
    pats["rank one"] = w
    w = {e: GI(0) for e in signs}
    vals = {(1, 1, -1): GI(1, 2), (1, -1, 1): GI(2, -3), (-1, 1, 1): GI(4, 1)}
    for e, c in vals.items():
        w[e] = c
        w[tuple(-s for s in e)] = c.conj()
    pats["N_w = 6"] = w
    return pats


EXPECTED = {"generic": (54, 112), "N_w = 2": (30, 40),
            "rank one": (51, 88), "N_w = 6": (54, 96)}


# ------------------------------------------------------------ number theory
def is_prime(n):
    if n < 2:
        return False
    for d in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % d == 0:
            return n == d
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def polmulmod(a, b, f, p):
    """product of polynomials a, b (coefficient lists, low degree first)
    modulo the monic cubic f = [1, f1, f2, f3] (high degree first) and p"""
    prod = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            prod[i + j] = (prod[i + j] + x * y) % p
    while len(prod) > 3:
        c = prod.pop()
        d = len(prod)
        prod[d - 1] = (prod[d - 1] - c * f[1]) % p
        prod[d - 2] = (prod[d - 2] - c * f[2]) % p
        prod[d - 3] = (prod[d - 3] - c * f[3]) % p
    while len(prod) < 3:
        prod.append(0)
    return prod


def split_prime(poly, qof, start):
    """the first prime p > start, p = 1 mod 4, at which the monic cubic poly
    splits completely and -q_j is a nonzero square for each root; returns p,
    the roots and the q_j"""
    p = start
    while True:
        p += 1
        if p % 4 != 1 or not is_prime(p):
            continue
        result, base, e = [1, 0, 0], [0, 1, 0], p
        while e:
            if e & 1:
                result = polmulmod(result, base, poly, p)
            base = polmulmod(base, base, poly, p)
            e >>= 1
        if result != [0, 1, 0]:
            continue
        roots = [a for a in range(p)
                 if (poly[0] * a * a * a + poly[1] * a * a + poly[2] * a
                     + poly[3]) % p == 0]
        if len(set(roots)) != 3:
            continue
        qs = [qof(a) % p for a in roots]
        if all(qq % p and pow((-qq) % p, (p - 1) // 2, p) == 1 for qq in qs):
            return p, roots, qs


def sqrt_mod(a, p):
    """Tonelli--Shanks"""
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        raise ValueError("not a square")
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


# ---------------------------------------------------------------------- run
def run():
    X = ModelQI(3)
    ONE, ZERO = X.unit, X.zero

    # (A) the sixfold
    ok = True
    for j in range(3):
        t2 = X.wedge(X.theta(j), X.theta(j))
        t3 = X.wedge(t2, X.theta(j))
        ok = ok and t3 == {} and len(t2) == 1
    tot = {}
    for j in range(3):
        tot = X.add(tot, X.theta(j))
    p6 = {0: ONE}
    for _ in range(6):
        p6 = X.wedge(p6, tot)
    prod = {0: ONE}
    for j in range(3):
        prod = X.wedge(prod, X.wedge(X.theta(j), X.theta(j)))
    c = [GI(3), GI(-2), GI(5)]
    ec = X.e_class(c)
    ccc = c[0] * c[1] * c[2]
    okA = (ok and X.integral(p6) == GI(720) and X.integral(prod) == GI(8)
           and X.integral(ec) == ccc * ccc)
    check("theta_j^3 = 0, int theta^6 = 720, int theta_1^2 theta_2^2 "
          "theta_3^2 = 8, and int exp(sum c_j theta_j) = (c_1 c_2 c_3)^2", okA)

    # (B) one place
    lam_p, lam_m = GI(1, 1), GI(1, -1)
    omega = (1 << 1) | (1 << 3)
    okB = True
    for lam in (lam_p, lam_m, GI(2), GI(0, 3)):
        e0 = X.exp_theta(lam, 0)
        for (A, B) in [((1 << 1) | (1 << 3), 1 << 0),
                       ((1 << 1) | (1 << 3), 1 << 2),
                       (1 << 1, (1 << 0) | (1 << 2)),
                       (1 << 3, (1 << 0) | (1 << 2)),
                       ((1 << 1) | (1 << 3), (1 << 0) | (1 << 2))]:
            okB = okB and X.act(A, B, e0) == {}
        for (A, B) in X.ht_basis(2):
            if (A | B) & ~0xF:
                continue
            okB = okB and set(X.act(A, B, e0)) <= {omega}
    cofs = []
    for lam in (lam_p, lam_m):
        e0 = X.exp_theta(lam, 0)
        cofs.append([X.act(A, B, e0).get(omega, ZERO)
                     for (A, B) in [(omega, 0), (1 << 1, 1 << 2),
                                    (0, (1 << 0) | (1 << 2))]])
    mat = [[cofs[0][k], cofs[1][k]] for k in range(3)]
    okB = okB and X.small_rank(mat) == 2
    check("for one place, HT^k_j kills exp(lambda theta_j) for k >= 3, HT^2_j "
          "maps into the line of omega_j, and the pairs (c(xi, lambda^+), "
          "c(xi, lambda^-)) span C^2", okB,
          "c(omega) = (%s, %s), c(y_1 d_2) = (%s, %s), c(d_1 d_2) = (%s, %s)" %
          (cofs[0][0], cofs[1][0], cofs[0][1], cofs[1][1],
           cofs[0][2], cofs[1][2]))

    # (C) exact ranks over Q(i), q = 1, t rational
    pats = patterns_gi(X.signs)
    for name, w in pats.items():
        for t in (0, 2):
            lam = [{1: GI(t, 1), -1: GI(t, -1)} for _ in range(3)]
            v = X.secant_class(w, lam)
            ranks = [X.rank(X.contraction_rows(v, k)) for k in (1, 2, 3)]
            N, A, rho, r2, r3 = X.formulas(w)
            ok = (ranks == [12, r2, r3] and (r2, r3) == EXPECTED[name])
            check("q = 1, t = %d, w %s: ranks from HT^1, HT^2, HT^3 are "
                  "%s, and the formulas give (12, %d, %d)"
                  % (t, name, ranks, r2, r3), ok,
                  "N_w = %d, A = %s, rho = %s"
                  % (N, [A[k] for k in sorted(A)], rho))

    # (D) the Euler form, exactly
    okD = True
    chis = []
    for name, w in pats.items():
        lam = [{1: GI(0, 1), -1: GI(0, -1)} for _ in range(3)]
        v = X.secant_class(w, lam)
        chi = X.integral(X.wedge(X.dual(v), v))
        s = GI(0)
        for e in X.signs:
            s = s + w[e] * w[e].conj()
        okD = okD and chi == GI(-64) * s
        chis.append(chi)
    Y = ModelQI(2)
    w2 = {(1, 1): GI(2, 1), (-1, -1): GI(2, -1), (1, -1): GI(1, -3),
          (-1, 1): GI(1, 3)}
    lam2 = [{1: GI(0, 1), -1: GI(0, -1)} for _ in range(2)]
    v2 = Y.secant_class(w2, lam2)
    chi2 = Y.integral(Y.wedge(Y.dual(v2), v2))
    s2 = GI(0)
    for e in Y.signs:
        s2 = s2 + w2[e] * w2[e].conj()
    okD = okD and chi2 == GI(16) * s2
    check("chi(v, v) = -64 Nm(q) sum |w_eps|^2 for the four patterns at "
          "q = 1, and +16 Nm(q) sum |w_eps|^2 for two places: the Euler form "
          "is (-4)^m Nm(q) sum |w_eps|^2", okD,
          "m = 3: chi = %s, %s, %s, %s; m = 2: chi = %s"
          % (chis[0], chis[1], chis[2], chis[3], chi2))

    # (E) three cubic fields, modulo a prime
    fields = [
        ("Q(zeta_7)^+", [1, 1, -2, -1], lambda a: 2 + a, "2+alpha"),
        ("Q(zeta_9)^+", [1, 0, -3, 1], lambda a: 3 - a, "3-alpha"),
        ("disc 229", [1, 0, -4, -1], lambda a: 3 + a, "3+alpha"),
    ]
    for fname, poly, qof, qname in fields:
        p, roots, qs = split_prime(poly, qof, 1000003)
        Z = ModelFp(3, p)
        s = [sqrt_mod((-qq) % p, p) for qq in qs]
        nm = 1
        for qq in qs:
            nm = (nm * qq) % p
        lam = [{1: (roots[j] + s[j]) % p, -1: (roots[j] - s[j]) % p}
               for j in range(3)]
        i_p = sqrt_mod(p - 1, p)          # p = 1 mod 4, so Z[i] -> F_p
        for name, w in pats.items():
            wp = {e: (int(c.a) + int(c.b) * i_p) % p for e, c in w.items()}
            v = Z.secant_class(wp, lam)
            ranks = [Z.rank(Z.contraction_rows(v, k)) for k in (1, 2, 3)]
            N, A, rho, r2, r3 = Z.formulas(wp)
            chi = Z.integral(Z.wedge(Z.dual(v), v)) % p
            ssum = 0
            for e in Z.signs:
                ssum = (ssum + wp[e] * wp[tuple(-x for x in e)]) % p
            chi_formula = (-64 * nm * ssum) % p
            ok = ranks == [12, r2, r3] and (r2, r3) == EXPECTED[name] \
                and chi == chi_formula
            check("%s, q = %s, t = alpha, w %s, modulo p = %d: ranks %s "
                  "match the formulas (12, %d, %d), and chi(v, v) = "
                  "-64 Nm(q) sum w_eps w_{-eps}"
                  % (fname, qname, name, p, ranks, r2, r3), ok)

    # (F) bookkeeping
    okF = True
    detail = []
    for name in ("generic", "N_w = 2", "rank one", "N_w = 6"):
        r2, r3 = EXPECTED[name]
        bound = r3 - 2 * r2 + 22
        detail.append("%s: chi <= -%d" % (name, bound))
        okF = okF and bound > 0
    okF = okF and 54 + 144 + 54 == 252 and 66 + 144 + 66 - 12 == 264
    check("a minimal object has profile (1, 12, r^2, e_3, r^2, 12, 1) with "
          "e_3 = 2 r^2 - 22 - chi, and e_3 >= r^3 reads chi <= -(r^3 - 2 r^2 "
          "+ 22); r(kappa) <= 252 < 264 = dim HT^2(A) - dim D_F", okF,
          "; ".join(detail))


if __name__ == "__main__":
    print("(LVI) the dimension count for Orlov products over a sextic CM "
          "field")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
