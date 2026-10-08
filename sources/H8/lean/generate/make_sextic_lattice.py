#!/usr/bin/env python3
"""
make_sextic_lattice.py

Writes the certificates of item (LVII), the integral classes of the flat
secant space S(0,q) of a sextic CM field, for HodgeObstruction.lean.

Model (that of code/attack/gaps/sextic/s2_lattice.py).  O = Z[a] is the ring
of integers of a totally real cubic field, H^1(X, Z) has the basis
u_{b i}, w_{b k} (b = 0, 1 the two blocks, i, k = 0, 1, 2), and for x in O
the rational 2-form

    Theta(x) = sum_j tau_j(x) theta_j = sum_b sum_{i,k} [x a^i]_k u_{bi} w_{bk}

has integer coefficients ([y]_k the k-th coordinate in the power basis).
With e_i in O and Delta in Z such that Tr(a^k e_i) = Delta delta_ki (computed
from the minimal polynomial), theta_j = Delta^{-1} sum_i tau_j(e_i) Theta_i,
Theta_i = Theta(a^i).  Every class of S(0,q) is then a polynomial in the
commuting forms Theta_0, Theta_1, Theta_2 whose coefficients are mixed traces

    MT(y_1, y_2, y_3) = sum over distinct j_1, j_2, j_3 of
                        tau_{j_1}(y_1) tau_{j_2}(y_2) tau_{j_3}(y_3)
                      = T1 T2 T3 - T12 T3 - T13 T2 - T23 T1 + 2 T123,

so no real embedding is needed: 48 Delta^6 v is an integral combination of
the monomials Theta^alpha, expanded on the two blocks by the binomial rule.

For each of the 32 cases (16 cubic fields, q = 1 and q = k + a) the script
records a basis Lb of the lattice L of parameters (c_0, f, g, c_3) at which
v is integral, as integers over a common denominator, and an integer matrix
R, supported on a few monomials, with R (A Lb) = I, A the coefficient
matrix; together these show that L is exactly the span of Lb.  The kernel
recomputes A, checks A Lb integral and R (A Lb) = I, computes the Euler form
on Lb from the Mukai pairing, checks that it is divisible by 8, and
enumerates the vectors of -chi/8 <= 3 (none) and, for q = 1, <= 4 (exactly
the classes Re exp(i theta), Im exp(i theta) and their negatives, whose
coordinates are recorded).

Run from the repository root:  python3 lean/generate/make_sextic_lattice.py > out
"""
import os
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import comb, factorial, gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code", "attack", "gaps", "sextic"))
import sextic_lattice as SL   # noqa: E402
import s2_lattice as S        # noqa: E402


# ---------------------------------------------------------------- O = Z[a]
class Ring:
    def __init__(self, poly):
        _, self.c2, self.c1, self.c0 = poly

    def mul(self, x, y):
        r = [0] * 5
        for i in range(3):
            for j in range(3):
                r[i + j] += x[i] * y[j]
        for k in (4, 3):
            c = r[k]
            r[k] = 0
            r[k - 1] -= self.c2 * c
            r[k - 2] -= self.c1 * c
            r[k - 3] -= self.c0 * c
        return r[:3]

    def tr(self, x):
        e1, e2, e3 = -self.c2, self.c1, -self.c0
        p1 = e1
        p2 = e1 * e1 - 2 * e2
        return 3 * x[0] + p1 * x[1] + p2 * x[2]

    def apow(self, i):
        r = [1, 0, 0]
        for _ in range(i):
            r = self.mul(r, [0, 1, 0])
        return r

    def dual(self):
        """e_i, Delta with Tr(a^k e_i) = Delta delta_ki"""
        c2, c1 = self.c2, self.c1
        fp = [c1, 2 * c2, 3]                       # f'(a)
        t = self.tr(fp)
        f2 = self.mul(fp, fp)
        e2 = (t * t - self.tr(f2)) // 2
        adj = [f2[0] - t * fp[0] + e2, f2[1] - t * fp[1], f2[2] - t * fp[2]]
        nrm = self.mul(fp, adj)
        assert nrm[1] == nrm[2] == 0
        delta = nrm[0]
        b = [[c1, c2, 1], [c2, 1, 0], [1, 0, 0]]   # b_0 = a^2 + c2 a + c1, ...
        e = [self.mul(bi, adj) for bi in b]
        for k in range(3):
            for i in range(3):
                assert self.tr(self.mul(self.apow(k), e[i])) == (delta if i == k else 0)
        return e, delta


# ------------------------------------------------- polynomials in Theta_i
def akey(al):
    return al[0] + 7 * al[1] + 49 * al[2]


MULTIS = {d: [al for al in ((x, y, d - x - y) for x in range(d + 1) for y in range(d + 1 - x))]
          for d in range(7)}


def pmul(R, P, Q):
    out = {}
    for a, x in P.items():
        for b, y in Q.items():
            k = (a[0] + b[0], a[1] + b[1], a[2] + b[2])
            z = R.mul(x, y)
            out[k] = [s + t for s, t in zip(out.get(k, [0, 0, 0]), z)]
    return out


def ptr(R, P):
    return {k: R.tr(x) for k, x in P.items()}


def padd(*terms):
    out = {}
    for c, P in terms:
        for k, x in P.items():
            out[k] = out.get(k, 0) + c * x
    return out


def pprod(*Ps):
    out = {(0, 0, 0): 1}
    for P in Ps:
        new = {}
        for a, x in out.items():
            for b, y in P.items():
                k = (a[0] + b[0], a[1] + b[1], a[2] + b[2])
                new[k] = new.get(k, 0) + x * y
        out = new
    return out


def mixed_trace(R, P1, P2, P3):
    t1, t2, t3 = ptr(R, P1), ptr(R, P2), ptr(R, P3)
    p12, p13, p23 = pmul(R, P1, P2), pmul(R, P1, P3), pmul(R, P2, P3)
    p123 = pmul(R, p12, P3)
    return padd((1, pprod(t1, t2, t3)), (-1, pprod(ptr(R, p12), t3)),
                (-1, pprod(ptr(R, p13), t2)), (-1, pprod(ptr(R, p23), t1)),
                (2, ptr(R, p123)))


def theta_poly(R, e, delta, h):
    """Delta^2 h(theta_j) as a polynomial in Theta: h = [h_0, h_1, h_2], h_d in O"""
    out = {}
    for d, hd in enumerate(h):
        if not any(hd):
            continue
        for al in MULTIS[d]:
            m = factorial(d) // (factorial(al[0]) * factorial(al[1]) * factorial(al[2]))
            y = hd
            for i in range(3):
                for _ in range(al[i]):
                    y = R.mul(y, e[i])
            s = m * delta ** (2 - d)
            out[al] = [s * t for t in y]
    return out


def param_polys(R, e, delta, q):
    """48 Delta^6 v for the eight basis parameters, as dicts alpha -> int"""
    one, zero = [1, 0, 0], [0, 0, 0]
    psi2 = theta_poly(R, e, delta, [[2, 0, 0], zero, [-t for t in q]])     # 2 psi
    xx = theta_poly(R, e, delta, [zero, one, zero])                        # x
    out = [padd((1, mixed_trace(R, psi2, psi2, psi2)))]
    for l in range(3):
        al = R.apow(l)
        fx = theta_poly(R, e, delta, [zero, al, zero])
        out.append(padd((6, mixed_trace(R, fx, psi2, psi2))))
    for l in range(3):
        al = R.apow(l)
        g2psi = theta_poly(R, e, delta, [[2 * t for t in al], zero,
                                         [-t for t in R.mul(al, q)]])
        out.append(padd((12, mixed_trace(R, g2psi, xx, xx))))
    out.append(padd((8, mixed_trace(R, xx, xx, xx))))
    return out


# ------------------------------------------------------- the two blocks
def popc(x):
    return bin(x).count("1")


def wsign(a, b):
    s, m = 0, b
    while m:
        low = m & -m
        y = low.bit_length() - 1
        s += popc(a >> (y + 1))
        m ^= low
    return -1 if s & 1 else 1


def ext_mul(A, B):
    out = {}
    for a, x in A.items():
        for b, y in B.items():
            if a & b:
                continue
            out[a | b] = out.get(a | b, 0) + wsign(a, b) * x * y
    return {k: v for k, v in out.items() if v}


def block_monos(d):
    return [sum(1 << i for i in I) | sum(1 << (3 + k) for k in K)
            for I in combinations(range(3), d) for K in combinations(range(3), d)]


def block_table(R):
    """cb[beta] = prod_i Theta_i^beta_i on one block, |beta| <= 3"""
    Th = []
    for i in range(3):
        f = {}
        for ip in range(3):
            y = R.mul(R.apow(i), R.apow(ip))
            for k in range(3):
                if y[k]:
                    f[(1 << ip) | (1 << (3 + k))] = y[k]
        Th.append(f)
    cb = {}
    for d in range(4):
        for al in MULTIS[d]:
            P = {0: 1}
            for i in range(3):
                for _ in range(al[i]):
                    P = ext_mul(P, Th[i])
            cb[al] = P
    return cb


GLOBAL = [(d1, d2, m1, m2) for d1 in range(4) for d2 in range(4)
          for m1 in block_monos(d1) for m2 in block_monos(d2)]


def expand(cb, V):
    """coefficients of sum_alpha V[alpha] Theta^alpha on the global monomials"""
    out = []
    for d1, d2, m1, m2 in GLOBAL:
        s = 0
        for b in MULTIS[d1]:
            x = cb[b].get(m1, 0)
            if not x:
                continue
            for bp in MULTIS[d2]:
                y = cb[bp].get(m2, 0)
                if not y:
                    continue
                al = (b[0] + bp[0], b[1] + bp[1], b[2] + bp[2])
                c = V.get(al, 0)
                if c:
                    s += c * comb(al[0], b[0]) * comb(al[1], b[1]) * comb(al[2], b[2]) * x * y
        out.append(s)
    return out


def pairing_sign(d1, d2, m1, m2):
    top = 63
    s = wsign(m1, top ^ m1) * wsign(m2, top ^ m2)
    return s * (-1) ** (d1 + d2)


GIDX = {(m1, m2): i for i, (d1, d2, m1, m2) in enumerate(GLOBAL)}
COMP = [GIDX[(63 ^ m1, 63 ^ m2)] for d1, d2, m1, m2 in GLOBAL]
PSIGN = [pairing_sign(*g) for g in GLOBAL]


# -------------------------------------------------------------- lattices
def lcm(a, b):
    return a * b // gcd(a, b)


def left_inverse(B):
    """integer R (as sparse rows) with R B = I for an integer matrix B whose
    rows span Z^n; rows are processed in order of their size"""
    n = len(B[0])
    order = sorted(range(len(B)), key=lambda i: (sum(abs(x) for x in B[i]), i))
    piv = {}
    for i in order:
        r, comb_ = B[i][:], {i: 1}
        if not any(r):
            continue
        for c in range(n):
            if r[c] == 0:
                continue
            if c not in piv:
                if r[c] < 0:
                    r = [-x for x in r]
                    comb_ = {k: -v for k, v in comb_.items()}
                piv[c] = (r, comb_)
                break
            b, bc = piv[c]
            g, x, y = S.egcd(b[c], r[c])
            nb = [x * s + y * t for s, t in zip(b, r)]
            nbc = {}
            for k in set(bc) | set(comb_):
                nbc[k] = x * bc.get(k, 0) + y * comb_.get(k, 0)
            nr = [(r[c] // g) * s - (b[c] // g) * t for s, t in zip(b, r)]
            nrc = {}
            for k in set(bc) | set(comb_):
                nrc[k] = (r[c] // g) * bc.get(k, 0) - (b[c] // g) * comb_.get(k, 0)
            if nb[c] < 0:
                nb = [-t for t in nb]
                nbc = {k: -v for k, v in nbc.items()}
            piv[c] = (nb, {k: v for k, v in nbc.items() if v})
            r, comb_ = nr, {k: v for k, v in nrc.items() if v}
        if len(piv) == n and all(piv[c][0][c] == 1 for c in range(n)):
            break
    assert len(piv) == n and all(piv[c][0][c] == 1 for c in range(n))
    # back substitution to the identity
    rows = {c: list(piv[c]) for c in range(n)}
    for c in reversed(range(n)):
        for c2 in range(c):
            f = rows[c2][0][c]
            if f:
                rows[c2][0] = [s - f * t for s, t in zip(rows[c2][0], rows[c][0])]
                cc = dict(rows[c2][1])
                for k, v in rows[c][1].items():
                    cc[k] = cc.get(k, 0) - f * v
                rows[c2][1] = {k: v for k, v in cc.items() if v}
    for c in range(n):
        assert rows[c][0] == [int(i == c) for i in range(n)]
        chk = [sum(v * B[k][j] for k, v in rows[c][1].items()) for j in range(n)]
        assert chk == rows[c][0]
    return [sorted(rows[c][1].items()) for c in range(n)]


def enumerate_short(G, bound):
    """the Lean enumerator: fraction-free Schur complements (Bareiss), then
    x_n, ..., x_1 by convex scanning; returns all x with x^T G x <= bound"""
    n = len(G)
    Ms, ds = [G], [1]
    M = [row[:] for row in G]
    d = 1
    for k in range(n - 1):
        piv = M[k][k]
        N = [[0] * n for _ in range(n)]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = piv * M[i][j] - M[i][k] * M[k][j]
                assert num % d == 0
                N[i][j] = num // d
        d = piv
        M = N
        Ms.append(M)
        ds.append(d)
    assert all(Ms[k][k][k] > 0 for k in range(n))
    out = []

    def rec(k, x):
        # S^(k) = Ms[k] / ds[k] on variables k..n-1 ; x holds x_{k+1..n-1}
        Mk, dk = Ms[k], ds[k]
        a = Mk[k][k]
        b = sum(Mk[k][j] * x[j] for j in range(k + 1, n))
        c = sum(Mk[i][j] * x[i] * x[j] for i in range(k + 1, n) for j in range(k + 1, n))
        lim = bound * dk

        def ok(t):
            return a * t * t + 2 * b * t + c <= lim
        t0 = (a - 2 * b) // (2 * a)          # the integer nearest to -b/a
        vals = []
        t = t0
        while ok(t):
            vals.append(t)
            t += 1
        t = t0 - 1
        while ok(t):
            vals.append(t)
            t -= 1
        for t in sorted(vals):
            x[k] = t
            if k == 0:
                if any(x):
                    out.append(x[:])
            else:
                rec(k - 1, x)
        x[k] = 0

    # the scan from the integer t0 nearest to the vertex -b/a is complete:
    # the admissible t form an interval symmetric about -b/a, which contains
    # t0 as soon as it contains any integer
    rec(n - 1, [0] * n)
    return out


# ------------------------------------------------------------------ main
def case_data(name, poly, qvec):
    R = Ring(poly)
    e, delta = R.dual()
    cb = block_table(R)
    Vs = param_polys(R, e, delta, qvec)
    cols = [expand(cb, V) for V in Vs]
    K = 48 * delta ** 6
    A = [[Fr(cols[c][m], K) for c in range(8)] for m in range(len(GLOBAL))]
    Lb = S.integral_lattice(A)
    # an LLL-reduced basis of the same lattice keeps the enumerations small
    G0 = SL.gram(poly, qvec, Lb)
    assert all(x.denominator == 1 for row in G0 for x in row)
    import flint
    _, T = flint.fmpz_mat([[int(x) for x in row] for row in G0]).lll(
        transform=True, rep="gram", gram="exact")
    Tm = [[int(T[i, j]) for j in range(8)] for i in range(8)]
    Lb = [[sum(Tm[i][a] * Lb[a][k] for a in range(8)) for k in range(8)] for i in range(8)]
    den = 1
    for v in Lb:
        for x in v:
            den = lcm(den, x.denominator)
    Ln = [[int(x * den) for x in v] for v in Lb]
    # integral images
    B = [[sum(cols[c][m] * Ln[b][c] for c in range(8)) for b in range(8)]
         for m in range(len(GLOBAL))]
    for row in B:
        for x in row:
            assert x % (K * den) == 0
    B = [[x // (K * den) for x in row] for row in B]
    Rinv = left_inverse(B)
    # Euler form from the pairing
    chi = [[sum(PSIGN[m] * B[m][a] * B[COMP[m]][b] for m in range(len(GLOBAL)))
            for b in range(8)] for a in range(8)]
    for a in range(8):
        for b in range(8):
            assert chi[a][b] == chi[b][a] and chi[a][b] % 8 == 0
    G = [[-chi[a][b] // 8 for b in range(8)] for a in range(8)]
    # against the closed formula
    Gc = SL.gram(poly, qvec, Lb)
    assert all(Fr(G[i][j]) == Gc[i][j] for i in range(8) for j in range(8)), name
    small = enumerate_short(G, 3)
    assert small == [] and S.short_vectors(G, 3) == []
    extra = None
    if qvec == [1, 0, 0]:
        four = enumerate_short(G, 4)
        assert sorted(map(tuple, four)) == sorted(map(tuple, S.short_vectors(G, 4)))
        re = [1, 0, 0, 0, -1, 0, 0, 0]
        im = [0, 1, 0, 0, 0, 0, 0, -1]
        Mt = [[Lb[b][i] for b in range(8)] for i in range(8)]
        inv = S.matinv(Mt)
        xs = []
        for cl in (re, im):
            x = [sum(inv[i][j] * cl[j] for j in range(8)) for i in range(8)]
            assert all(t.denominator == 1 for t in x)
            xs.append([int(t) for t in x])
        want = sorted(tuple(s * t for t in x) for x in xs for s in (1, -1))
        assert sorted(map(tuple, four)) == want
        extra = xs
    return dict(poly=poly, q=qvec, den=den, Ln=Ln, R=Rinv, delta=delta, extra=extra,
                nR=sum(len(r) for r in Rinv), G=G)


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


# ------------------------------------------------------ item (LVIII)
def ring_ops(poly):
    R = Ring(poly)

    def adj(x):
        t = R.tr(x)
        x2 = R.mul(x, x)
        e2 = (t * t - R.tr(x2)) // 2
        return [x2[0] - t * x[0] + e2, x2[1] - t * x[1], x2[2] - t * x[2]]

    def norm(x):
        n = R.mul(x, adj(x))
        assert n[1] == n[2] == 0
        return n[0]

    def star(x, y):
        xy = R.mul(x, y)
        tx = [R.tr(x) - x[0], -x[1], -x[2]]
        ty = [R.tr(y) - y[0], -y[1], -y[2]]
        a = R.mul(tx, ty)
        return [a[0] - (R.tr(xy) - xy[0]), a[1] + xy[1], a[2] + xy[2]]
    return R, adj, norm, star


def omega(poly, q, p):
    """(Nm(q) R, (Nm(q)/q) I) of lem:sexticweil(ii) at the integral parameters p"""
    R, adj, norm, star = ring_ops(poly)
    c0, f, g, c3 = p[0], p[1:4], p[4:7], p[7]
    Nq, Aq = norm(q), adj(q)
    f2, g2 = R.mul(f, f), R.mul(g, g)
    qg2 = R.mul(q, g2)
    a1 = R.mul(Aq, f2)
    a2 = R.mul(q, star(q, f2))
    NR = [-a1[i] + a2[i] + 2 * qg2[i] for i in range(3)]
    NR[0] += Nq * c0 * c0 - R.tr(qg2) - c3 * c3
    b1 = R.mul(Aq, f)
    b2 = star(f, R.mul(q, g))
    NI = [c0 * b1[i] + b2[i] + c3 * g[i] for i in range(3)]
    return NR, NI


def params_of(Ln, x):
    return [sum(x[b] * Ln[b][i] for b in range(8)) for i in range(8)]


def least_k(poly):
    import s3_weil as W
    return W.least_k(poly)


def squarefree_part(n):
    D, d = 1, 2
    while d * d <= n:
        while n % (d * d) == 0:
            n //= d * d
        if n % d == 0:
            D *= d
            n //= d
        d += 1
    return D * n


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def roots_mod(poly, p):
    return [r for r in range(p) if (r ** 3 + poly[1] * r * r + poly[2] * r + poly[3]) % p == 0]


def imag_cert(poly, q):
    R, adj, norm, star = ring_ops(poly)
    D = squarefree_part(norm(q))
    Dq = [D * t for t in q]
    # a square root in O, by search over small coordinates
    for y0 in range(-60, 61):
        for y1 in range(-60, 61):
            for y2 in range(-60, 61):
                if R.mul([y0, y1, y2], [y0, y1, y2]) == Dq:
                    return D, True, [y0, y1, y2], 0, 0
    for p in range(3, 2000):
        if not is_prime(p):
            continue
        for r in roots_mod(poly, p):
            v = (Dq[0] + Dq[1] * r + Dq[2] * r * r) % p
            if v and pow(v, (p - 1) // 2, p) == p - 1:
                return D, False, [0, 0, 0], p, r
    raise AssertionError


def shape_prime(poly, q):
    for p in range(1000, 100000):
        if not is_prime(p):
            continue
        rts = roots_mod(poly, p)
        if len(rts) != 3:
            continue
        ss = []
        for r in rts:
            v = (-(q[0] + q[1] * r + q[2] * r * r)) % p
            s = next((t for t in range(1, p) if t * t % p == v), None)
            if s is None:
                break
            ss.append(s)
        if len(ss) == 3:
            return p, rts, ss


def main():
    import s3_weil as W
    fl = SL.cubic_fields()
    assert len(fl) == 16
    out, rows, imag, summary, grams = [], [], [], [], []
    shapes = []
    for idx, (name, poly) in enumerate(fl):
        k = least_k(poly)
        for qi, qvec in enumerate(([1, 0, 0], [k, 1, 0], [k + 1, 1, 0])):
            D = case_data(name, poly, qvec)
            Ln, den = D["Ln"], D["den"]
            G = D["G"]
            # LVIII: the least norm with Omega != 0, by enumeration with a doubling bound
            b = 24
            while True:
                vecs = enumerate_short(G, b)
                nz = [x for x in vecs if any(sum(omega(poly, qvec, params_of(Ln, x)), []))]
                if nz:
                    break
                b *= 2
            nrm = lambda x: sum(x[i] * G[i][j] * x[j] for i in range(8) for j in range(8))
            m = min(nrm(x) for x in nz)
            at = [x for x in nz if nrm(x) == m]
            below = [x for x in vecs if nrm(x) < m]
            mn = min(nrm(x) for x in vecs)
            assert all(not any(sum(omega(poly, qvec, params_of(Ln, x)), [])) for x in below)
            wit = min(at)
            # the plane Z Re + Z Im
            inplane = qvec == [1, 0, 0] and all(
                (lambda pp: pp[0] % den == 0 and pp[1] % den == 0 and pp[2] == pp[3] == pp[5] == pp[6] == 0
                 and pp[4] == -pp[0] and pp[7] == -pp[1])(params_of(Ln, x)) for x in below)
            # the classes with norm <= 4 for q = 1, and for q = 2 + a over the cyclic fields
            pair = None
            if qvec == [1, 0, 0]:
                pair = ([den, 0, 0, 0, -den, 0, 0, 0], [0, den, 0, 0, 0, 0, 0, -den])
            beta = {"Q(zeta_7)^+": [-1, 1, 1], "Q(zeta_9)^+": [-2, 1, 1]}.get(name)
            if beta is not None and qvec == [2, 1, 0]:
                Rr, adj, norm, star = ring_ops(poly)
                nb = norm(beta)
                pair = ([den] + [0, 0, 0] + [-den * t for t in adj(beta)] + [0],
                        [0] + [den * t for t in beta] + [0, 0, 0] + [-den * nb])
            if pair is not None:
                four = [x for x in vecs if nrm(x) <= 4]
                got = sorted(tuple(params_of(Ln, x)) for x in four)
                want = sorted(tuple(s * t for t in pp) for pp in pair for s in (1, -1))
                assert got == want, (name, qvec)
            tag = "sl%d_%d" % (idx, qi)
            out.append("def %sR : List (List (Nat × Int)) := [%s]" % (
                tag, ", ".join("[" + ", ".join("(%d, %d)" % kv for kv in r) + "]" for r in D["R"])))
            pr = "none" if pair is None else "some (%s, %s)" % (lean_list(pair[0]), lean_list(pair[1]))
            rows.append("  (%s, %s, %d, [%s], %sR, %d, %d, %d, %s, %s, %s)" % (
                lean_list(poly[1:]), lean_list(qvec), den, ", ".join(lean_list(v) for v in Ln), tag,
                mn, m, len(at), lean_list(wit), pr, "true" if inplane else "false"))
            grams.append("[" + ", ".join(lean_list(r) for r in G) + "]")
            Dd, has, y, pp, rr = imag_cert(poly, qvec)
            imag.append("  (%s, %s, %d, %s, %s, %d, %d)" % (
                lean_list(poly[1:]), lean_list(qvec), Dd, "true" if has else "false", lean_list(y), pp, rr))
            summary.append((idx, qi, mn, m, len(below), len(at), inplane, has, Dd))
            print("-- %s q=%s den=%d |R|=%d min=%d least=%d below=%d at=%d plane=%s imag=%s"
                  % (name, qvec, den, D["nR"], 8 * mn, 8 * m, len(below), len(at), inplane,
                     Dd if has else None), file=sys.stderr)
            if (name in ("Q(zeta_7)^+", "Q(zeta_9)^+") and qvec == [1, 0, 0]) or qvec == [3, 1, 0] and \
                    name in ("Q(zeta_7)^+", "Q(zeta_9)^+"):
                p, rts, ss = shape_prime(poly, qvec)
                shapes.append("  (%s, %s, %d, %s, %s, [%s])" % (
                    lean_list(poly[1:]), lean_list(qvec), p, lean_list(rts), lean_list(ss),
                    ", ".join(lean_list(params_of(Ln, x)) for x in at)))
    out.append("")
    for k in range(6):
        out.append("def slCases%d : List SlCase := [\n%s]" % (k, ",\n".join(rows[8 * k:8 * k + 8])))
        out.append("")
    out.append("/-- the 48 cases `((c2, c1, c0), q, den, den * Lb, R, least norm, least norm with")
    out.append("Omega != 0, number of such vectors at that norm, one of them, the classes of norm")
    out.append("at most 4 (times den) when recorded, all classes below in Z Re + Z Im)`; norms")
    out.append("are `-chi/8`. -/")
    out.append("def slCases : List SlCase := " + " ++ ".join("slCases%d" % k for k in range(6)))
    out.append("")
    for k in range(6):
        out.append("def slGrams%d : List (List (List Int)) := [\n  %s]" % (
            k, ",\n  ".join(grams[8 * k:8 * k + 8])))
        out.append("")
    out.append("/-- the Gram matrices of `-chi/8` on the recorded bases, certified by")
    out.append("`slLatticeOk`. -/")
    out.append("def slGrams : List (List (List Int)) := " + " ++ ".join("slGrams%d" % k for k in range(6)))
    out.append("")
    out.append("/-- `((c2, c1, c0), q, D, contains, y, p, r)`: `D` the squarefree part of `Nm(q)`;")
    out.append("either `y^2 = D q`, or `r` is a root of the minimal polynomial modulo the prime")
    out.append("`p` at which `D q` is not a square. -/")
    out.append("def slImag : List (List Int × List Int × Nat × Bool × List Int × Nat × Int) := [")
    out.append(",\n".join(imag) + "]")
    out.append("")
    out.append("/-- `((c2, c1, c0), q, p, roots, square roots of -tau_j(q), classes)` for the")
    out.append("shapes of the least classes with Omega != 0. -/")
    out.append("def slShapeData : List (List Int × List Int × Nat × List Int × List Int"
               " × List (List Int)) := [")
    out.append(",\n".join(shapes) + "]")
    print("\n".join(out))


if __name__ == "__main__":
    main()
