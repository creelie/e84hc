#!/usr/bin/env python3
"""
s3_weil.py

The F-Weil part of the twisted character of an Orlov product over a sextic CM
field F = F_0(sqrt(-q)), and the integral characters of the flat secant space
S(0,q) for which it is nonzero (lem:sexticweil, prop:sexticweilmin; item
(LVIII), driven by code/sextic_weil.py).

Model of A = X x Xhat (the per-factor model of prop:sexticcount(iv)).  Over R,
H^1(X) = U_1 + U_2 + U_3 with U_j the eigenspace of the real place tau_j of
F_0; the U_j are orthogonal for theta and each has a symplectic basis.  So
H^*(A) is the exterior algebra on
    x_0 .. x_11   (bits 0..11, H^1(X)),   xi_0 .. xi_11  (bits 12..23, H^1(Xhat)),
xi_i dual to x_i, with theta = sum_{i<6} x_i x_{6+i}.  Factor j in {0,1,2}
owns x_a, x_b, x_c, x_d = x_{2j}, x_{2j+1}, x_{6+2j}, x_{7+2j}, in this order
the basis x_1, .., x_4 of the proof of thm:splitclosed (theta_j = x_1 x_3 +
x_2 x_4).  B = phi_theta: x_i -> xi_{6+i}, x_{6+i} -> -xi_i; the element
sqrt(-q) acts on H^1 of factor j by u -> -B u, phi -> d_j B^{-1} phi, with
d_j = tau_j(q), as in eq:Mdef with d = d_j; F_0 acts on factor j through tau_j.
    thetahat_j = xi_a xi_c + xi_b xi_d,  ell_j = sum_{i in factor j} x_i xi_i,
    gamma_j = d_j theta_j - thetahat_j,   eta_j = d_j theta_j + thetahat_j,
    omega_(j,sigma) = wedge_{i = 1..4} (x_i + sigma (s_j/d_j) B x_i),
                     s_j = sqrt(-1) sqrt(d_j),
the generator of eq:splitclosed with n = 2, d = d_j (checked below to equal
-(gamma_j - sigma s_j ell_j)^2 / (2 d_j^2)).  The Orlov transform is that of
attack/gaps/quartic_obstruction/orlov.py (same conventions; orlov_low below
is the same sum pruned by output degree and is checked against it).

Coefficients: Fractions, ealib.QI (Gaussian rationals, for models in which
every d_j is a rational square) or QA (the cubic field Q(alpha) itself, for
the cyclic fields Q(zeta_7)^+ and Q(zeta_9)^+, whose real places are the
automorphisms alpha -> alpha, alpha^2 - 2, (alpha^2 - 2)^2 - 2).

Everything is exact.  Run standalone for the tables of the transcript:
    python3 s3_weil.py
"""
import os
import sys
import math
import itertools
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "quartic_obstruction"))
sys.path.insert(0, os.path.join(HERE, "..", "..", ".."))

import flint                                                  # noqa: E402
from ealib import (QI, add, sc, wedge, clean, pc, wsign, one,  # noqa: E402
                   expo, power)
import orlov as ORL                                            # noqa: E402
import s2_lattice as S                                         # noqa: E402

NX = 12
FACT = {j: (2 * j, 2 * j + 1, 6 + 2 * j, 7 + 2 * j) for j in range(3)}
EPS = list(itertools.product((1, -1), repeat=3))
SUBSETS = list(itertools.product((0, 1), repeat=3))


# ------------------------------------------------------------------ classes
def theta(j):
    a, b, c, d = FACT[j]
    return {(1 << a) | (1 << c): Fr(1), (1 << b) | (1 << d): Fr(1)}


def thetahat(j):
    a, b, c, d = FACT[j]
    return {(1 << (12 + a)) | (1 << (12 + c)): Fr(1),
            (1 << (12 + b)) | (1 << (12 + d)): Fr(1)}


def ell_j(j):
    return add(*[{(1 << i) | (1 << (12 + i)): Fr(1)} for i in FACT[j]])


def ell():
    return add(*[ell_j(j) for j in range(3)])


def Bx(i):
    """B x_i as (index of xi, sign)"""
    return (6 + i, 1) if i < 6 else (i - 6, -1)


def B_class(j, d):
    t = theta(j)
    return add(one(), sc(d * Fr(-1, 2), wedge(t, t)))


def secant_class(C, dvec):
    """v = sum_a C[a] prod_j (theta_j if a_j else B_j), B_j = 1 - d_j theta_j^2/2"""
    out = {}
    for a, c in C.items():
        if c == 0:
            continue
        term = one()
        for j in range(3):
            term = wedge(term, theta(j) if a[j] else B_class(j, dvec[j]))
        out = add(out, sc(c, term))
    return out


def C_of(c0, f, g, c3):
    """C_a of v(c0, f, g, c3), f, g given by their three conjugates"""
    C = {}
    for a in SUBSETS:
        k = sum(a)
        if k == 0:
            C[a] = c0
        elif k == 3:
            C[a] = c3
        elif k == 1:
            C[a] = f[a.index(1)]
        else:
            C[a] = g[a.index(0)]
    return C


def dual(u):
    return {m: (c if (pc(m) // 2) % 2 == 0 else -c) for m, c in u.items()}


_VOL = None


def integral_X(u):
    """int_X, normalised by int theta^6/6! = 1"""
    global _VOL
    top = (1 << NX) - 1
    if _VOL is None:
        th = add(*[theta(j) for j in range(3)])
        _VOL = power(th, 6)[top] / 720
    return u.get(top, 0) / _VOL


# ------------------------------------------------------------ Orlov transform
def orlov_low(c1, c2, maxdeg=4):
    """ch(Phi K)(x, xi) = int_y c1(x+y) c2(y) exp(sum_i y_i xi_i) for
    K = c1 [x] c2 on X x X, only the output monomials of degree <= maxdeg;
    the sum of orlov.orlov(6, c1, c2) pruned by output degree (c2 is the
    character of the second factor, already dualised)."""
    m = NX
    full = (1 << m) - 1
    out = {}
    c2items = list(c2.items())
    for I, a in c1.items():
        nI = pc(I)
        for K, b in c2items:
            nK = pc(K)
            avail = I & ~K
            abits = [i for i in range(m) if avail >> i & 1]
            need = nI + m - nK - maxdeg
            nJmin = max(0, (need + 1) // 2)
            for nJ in range(nJmin, len(abits) + 1):
                for Jt in itertools.combinations(abits, nJ):
                    J = 0
                    for i in Jt:
                        J |= 1 << i
                    s = 0
                    for i in Jt:
                        s += pc((I & ~J) >> (i + 1))
                    P = I & ~J
                    L = full & ~(J | K)
                    s += 0 if wsign(J, K) > 0 else 1
                    s += 0 if wsign(J | K, L) > 0 else 1
                    l = pc(L)
                    s += l * (l - 1) // 2 + m * l
                    key = P | (L << m)
                    val = a * b
                    if s & 1:
                        val = -val
                    val = -val            # (-1)^{g(g-1)/2}, g = 6
                    out[key] = out.get(key, 0) + val
    return clean(out)


def truncate(u, maxdeg):
    return {m: c for m, c in u.items() if pc(m) <= maxdeg}


def kappa_low(v1, v2, maxdeg=4, full=False):
    """(ch Phi(F_1 [x] F_2^vee) e^{ell/2}) in degrees <= maxdeg, with
    v1 = ch F_1 and v2 = ch F_2; full=True uses orlov.orlov itself."""
    if full:
        ch = truncate(ORL.orlov(6, v1, dual(v2)), maxdeg)
    else:
        ch = orlov_low(v1, dual(v2), maxdeg)
    E = expo(sc(Fr(1, 2), ell()), maxdeg=maxdeg // 2)
    return truncate(wedge(ch, E), maxdeg)


def degree(u, k):
    return {m: c for m, c in u.items() if pc(m) == k}


# ------------------------------------------------------------ Weil basis
def eta_j(j, d):
    """d theta_j + thetahat_j, a positive multiple of the polarisation of the
    j-th factor; with it prop:flatall reads Psi(e^{s theta} [x] e^{s theta})
    = c exp((s/2d) eta)"""
    return add(sc(d, theta(j)), thetahat(j))


def omega_wedge(j, lam_over_d, unit):
    """wedge over the paper's basis x_1..x_4 of factor j of x_i + (lam/d) B x_i"""
    w = {0: unit}
    for i in FACT[j]:
        k, s = Bx(i)
        v = {1 << i: unit, 1 << (12 + k): lam_over_d * s}
        w = wedge(w, v)
    return w


def omega_closed(j, d, lam, unit):
    """-(gamma_j - lam ell_j)^2 / (2 d^2), the generator of eq:splitclosed"""
    gam = add(sc(d * unit, theta(j)), sc(-unit, thetahat(j)))
    t = add(gam, sc(-lam, ell_j(j)))
    return sc(-(unit / (2 * d * d)), wedge(t, t))


def solve(basis, target, zero):
    """exact coefficients c with sum_k c_k basis_k = target, or None.
    Elimination on as many rows as needed for full column rank, then an
    exact check of the residual on every monomial."""
    n = len(basis)
    keys = sorted(set(k for b in basis for k in b) | set(target))
    rows, pivots = [], []
    for m in keys:
        r = [b.get(m, zero) for b in basis] + [target.get(m, zero)]
        for (pc_, pr) in zip(pivots, rows):
            if r[pc_] != 0:
                f = r[pc_]
                r = [x - f * y for x, y in zip(r, pr)]
        piv = next((c for c in range(n) if r[c] != 0), None)
        if piv is None:
            continue
        inv = (zero + 1) / r[piv]
        r = [x * inv for x in r]
        for idx in range(len(rows)):
            if rows[idx][piv] != 0:
                f = rows[idx][piv]
                rows[idx] = [x - f * y for x, y in zip(rows[idx], r)]
        rows.append(r)
        pivots.append(piv)
        if len(rows) == n:
            break
    assert len(rows) == n, "basis not independent"
    sol = [zero] * n
    for pcol, r in zip(pivots, rows):
        sol[pcol] = r[n]
    for m in keys:
        acc = target.get(m, zero)
        for c, b in zip(sol, basis):
            x = b.get(m)
            if x is not None:
                acc = acc - c * x
        if acc != 0:
            return None
    return sol


# ------------------------------------------------------------ pair formula
def w_of(C, svec):
    """w_eps = (1/8) sum_a C_a prod_{j in a} eps_j / s_j  (v = sum w_eps e_eps)"""
    w = {}
    for e in EPS:
        tot = QI(0)
        for a, c in C.items():
            t = QI(Fr(c))
            for j in range(3):
                if a[j]:
                    t = t * QI(e[j]) / svec[j]
            tot = tot + t
        w[e] = tot * QI(Fr(1, 8))
    return w


def flip(e, j):
    """eps^(j): agrees with eps at j, opposite at the two other places"""
    return tuple(e[k] if k == j else -e[k] for k in range(3))


def pair_W(C1, C2, dvec, svec):
    """the pair formula of lem:sexticweil(i), in the normalisation of
    eq:splitclosed: W_(j,sigma) = -16 Nm(q) d_j sum_{eps_j = sigma}
    w1_eps w2_{eps^(j)}; order (0,+),(0,-),(1,+),(1,-),(2,+),(2,-)"""
    w1, w2 = w_of(C1, svec), w_of(C2, svec)
    Nm = dvec[0] * dvec[1] * dvec[2]
    out = []
    for j in range(3):
        for sg in (1, -1):
            tot = QI(0)
            for e in EPS:
                if e[j] == sg:
                    tot = tot + w1[e] * w2[flip(e, j)]
            out.append(tot * QI(-16 * Nm * dvec[j]))
    return out


def diag_form(C, dvec, svec):
    """(1/16) sum_b (C_0b + sigma C_1b / s_j)^2 / prod_{k in b} d_k"""
    out = []
    for j in range(3):
        oth = [k for k in range(3) if k != j]
        for sg in (1, -1):
            tot = QI(0)
            for b in itertools.product((0, 1), repeat=2):
                a0, a1 = [0, 0, 0], [0, 0, 0]
                a1[j] = 1
                den = Fr(1)
                for kk, k in enumerate(oth):
                    a0[k] = a1[k] = b[kk]
                    if b[kk]:
                        den *= dvec[k]
                Y = QI(Fr(C[tuple(a0)])) + QI(sg) * QI(Fr(C[tuple(a1)])) / svec[j]
                tot = tot + Y * Y * QI(1 / den)
            out.append(tot * QI(Fr(1, 16)))
    return out


def weil_basis_QI(dvec, svec):
    basis = [wedge(eta_j(j, dvec[j]), eta_j(k, dvec[k]))
             for j in range(3) for k in range(j, 3)]
    basis = [{m: QI(c) for m, c in b.items()} for b in basis]
    for j in range(3):
        for sg in (1, -1):
            basis.append(omega_wedge(j, QI(sg) * svec[j] / QI(dvec[j]), QI(1)))
    return basis


def weil_coordinates_QI(k4, dvec, svec):
    """(eta part, W_(j,sigma)) of a degree-four class over Q(i), or None"""
    basis = weil_basis_QI(dvec, svec)
    tgt = {m: (c if isinstance(c, QI) else QI(c)) for m, c in k4.items()}
    sol = solve(basis, tgt, QI(0))
    if sol is None:
        return None
    return sol[:6], sol[6:]


# ------------------------------------------------------------ cubic fields
class QA:
    """an element of Q(alpha), alpha^3 = -c2 alpha^2 - c1 alpha - c0, for the
    polynomial QA.P = [1, c2, c1, c0] set by the caller"""
    __slots__ = ("c",)
    P = None

    def __init__(self, c0=0, c1=0, c2=0):
        self.c = (Fr(c0), Fr(c1), Fr(c2))

    @staticmethod
    def _c(o):
        return o if isinstance(o, QA) else QA(o)

    def __add__(self, o):
        o = QA._c(o)
        return QA(*(a + b for a, b in zip(self.c, o.c)))
    __radd__ = __add__

    def __sub__(self, o):
        o = QA._c(o)
        return QA(*(a - b for a, b in zip(self.c, o.c)))

    def __rsub__(self, o):
        return QA._c(o) - self

    def __neg__(self):
        return QA(*(-a for a in self.c))

    def __mul__(self, o):
        if not isinstance(o, QA):
            o = Fr(o)
            return QA(*(a * o for a in self.c))
        a, b = self.c, o.c
        r = [Fr(0)] * 5
        for i in range(3):
            if a[i]:
                for j in range(3):
                    if b[j]:
                        r[i + j] += a[i] * b[j]
        _, c2, c1, c0 = QA.P
        for k in (4, 3):
            t = r[k]
            if t:
                r[k] = Fr(0)
                r[k - 1] -= c2 * t
                r[k - 2] -= c1 * t
                r[k - 3] -= c0 * t
        return QA(r[0], r[1], r[2])
    __rmul__ = __mul__

    def inv(self):
        cols = [self * QA(1), self * QA(0, 1), self * QA(0, 0, 1)]
        M = [[cols[j].c[i] for j in range(3)] + [Fr(int(i == 0))]
             for i in range(3)]
        for i in range(3):
            p = next(r for r in range(i, 3) if M[r][i] != 0)
            M[i], M[p] = M[p], M[i]
            piv = M[i][i]
            M[i] = [x / piv for x in M[i]]
            for r in range(3):
                if r != i and M[r][i] != 0:
                    f = M[r][i]
                    M[r] = [x - f * y for x, y in zip(M[r], M[i])]
        return QA(M[0][3], M[1][3], M[2][3])

    def __truediv__(self, o):
        if not isinstance(o, QA):
            return QA(*(a / Fr(o) for a in self.c))
        return self * o.inv()

    def __rtruediv__(self, o):
        return QA._c(o) * self.inv()

    def __eq__(self, o):
        return self.c == QA._c(o).c

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        return hash(self.c)

    def norm(self):
        cols = [self * QA(1), self * QA(0, 1), self * QA(0, 0, 1)]
        M = [[cols[j].c[i] for j in range(3)] for i in range(3)]
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

    def __repr__(self):
        return "(%s + %s a + %s a^2)" % self.c


def cyc_sigma(x, k):
    """tau_k(x) for the cyclic fields: sigma(alpha) = alpha^2 - 2"""
    s = QA(-2, 0, 1)
    for _ in range(k):
        x = x.c[0] * QA(1) + x.c[1] * s + x.c[2] * s * s
    return x


class QL:
    """a + lam b over Q(alpha), lam^2 = -d"""
    __slots__ = ("a", "b", "d")

    def __init__(self, a, b, d):
        self.a, self.b, self.d = QA._c(a), QA._c(b), d

    def _c(self, o):
        return o if isinstance(o, QL) else QL(o, 0, self.d)

    def __add__(self, o):
        o = self._c(o)
        return QL(self.a + o.a, self.b + o.b, self.d)
    __radd__ = __add__

    def __neg__(self):
        return QL(-self.a, -self.b, self.d)

    def __sub__(self, o):
        return self + (-self._c(o))

    def __mul__(self, o):
        o = self._c(o)
        return QL(self.a * o.a - self.d * self.b * o.b,
                  self.a * o.b + self.b * o.a, self.d)
    __rmul__ = __mul__

    def __eq__(self, o):
        o = self._c(o)
        return self.a == o.a and self.b == o.b

    def __ne__(self, o):
        return not self.__eq__(o)


def omega_PQ(j, d):
    """omega_(j,sigma) = P_j + sigma s_j Q_j with P_j, Q_j over Q(alpha):
    the wedge of omega_wedge with lam = s_j, expanded in lam (lam^2 = -d)"""
    lam_over_d = QL(0, QA(1) / d, d)
    w = omega_wedge(j, lam_over_d, QL(1, 0, d))
    P = {m: c.a for m, c in w.items() if c.a != 0}
    Q = {m: c.b for m, c in w.items() if c.b != 0}
    return P, Q


def omega_closed_PQ(j, d):
    """-(gamma_j - lam ell_j)^2/(2 d^2) expanded in lam = s_j"""
    unit = QL(1, 0, d)
    lam = QL(0, 1, d)
    gam = add(sc(unit * d, theta(j)), sc(-unit, thetahat(j)))
    t = add(gam, sc(-lam, ell_j(j)))
    w = sc(-(unit * (QA(1) / (2 * d * d))), wedge(t, t))
    P = {m: c.a for m, c in w.items() if c.a != 0}
    Q = {m: c.b for m, c in w.items() if c.b != 0}
    return P, Q


# ------------------------------------------------ Omega = R + 2 I / sqrt(-q)
def F0ops(poly):
    mulv, tr, T, basis = S.field_data(poly)

    def mul(x, y):
        return mulv([Fr(t) for t in x], [Fr(t) for t in y])

    def addv(*xs):
        out = [Fr(0)] * 3
        for x in xs:
            out = [a + Fr(b) for a, b in zip(out, x)]
        return out

    def scal(c, x):
        return [Fr(c) * Fr(t) for t in x]

    def const(c):
        return [Fr(c), Fr(0), Fr(0)]

    def norm(x):
        Mx = [mulv([Fr(t) for t in x], b) for b in basis]
        return (Mx[0][0] * (Mx[1][1] * Mx[2][2] - Mx[1][2] * Mx[2][1])
                - Mx[0][1] * (Mx[1][0] * Mx[2][2] - Mx[1][2] * Mx[2][0])
                + Mx[0][2] * (Mx[1][0] * Mx[2][1] - Mx[1][1] * Mx[2][0]))

    def adj(x):
        """Nm(x)/x = x^2 - Tr(x) x + e_2(x)"""
        x = [Fr(t) for t in x]
        trx = tr(x)
        x2 = mul(x, x)
        e2 = (trx * trx - tr(x2)) / 2
        return [x2[i] - trx * x[i] + (e2 if i == 0 else 0) for i in range(3)]

    return mul, addv, scal, const, norm, adj, tr


def omega_RI(poly, qvec, x):
    """(Nm(q) R, (Nm(q)/q) I, Nm(q)) in F_0 (power basis) for the class
    v(c0, f, g, c3) with parameters x = (c0, f0, f1, f2, g0, g1, g2, c3):
      Nm(q) R = Nm(q) c0^2 - (Nm(q)/q) f^2 + q (q * f^2) + 2 q g^2
                - Tr(q g^2) - c3^2,
      (Nm(q)/q) I = (Nm(q)/q) c0 f + f * (q g) + c3 g,
    with x * y = (Tr x - x)(Tr y - y) - (Tr(xy) - xy), so that
    tau_j(x * y) = tau_k(x) tau_l(y) + tau_l(x) tau_k(y)."""
    mul, addv, scal, const, norm, adj, tr = F0ops(poly)
    c0, c3 = Fr(x[0]), Fr(x[7])
    f = [Fr(t) for t in x[1:4]]
    g = [Fr(t) for t in x[4:7]]
    q = [Fr(t) for t in qvec]
    Nq = norm(q)
    Aq = adj(q)

    def star(a, b):
        ab = mul(a, b)
        return addv(mul(addv(const(tr(a)), scal(-1, a)),
                        addv(const(tr(b)), scal(-1, b))),
                    scal(-1, addv(const(tr(ab)), scal(-1, ab))))
    f2, g2 = mul(f, f), mul(g, g)
    qg2 = mul(q, g2)
    NR = addv(const(Nq * c0 * c0), scal(-1, mul(Aq, f2)), mul(q, star(q, f2)),
              scal(2, qg2), const(-tr(qg2) - c3 * c3))
    NI = addv(scal(c0, mul(Aq, f)), star(f, mul(q, g)), scal(c3, g))
    return NR, NI, Nq


def omega_nonzero(poly, qvec, x):
    NR, NI, _ = omega_RI(poly, qvec, x)
    return any(NR) or any(NI)


# ------------------------------------------------ lattices and enumeration
def cubic_fields():
    import sextic_lattice as SL
    return SL.cubic_fields()


def least_k(poly):
    """least integer k with k + alpha totally positive, exactly: all roots
    of P(x - k) are real, so they are all positive iff its coefficients
    alternate in sign (Descartes' rule is exact for real-rooted polynomials)"""
    def shifted(k):
        # coefficients (high to low) of P(x - k)
        a = [Fr(c) for c in poly]
        res = [Fr(0)] * 4
        for i, c in enumerate(a):
            e = 3 - i
            for r in range(e + 1):
                res[3 - r] += c * math.comb(e, r) * (-k) ** (e - r)
        return res

    def totally_positive(k):
        cs = shifted(k)
        return all(cs[i] * cs[i + 1] < 0 for i in range(3))
    k = -10
    while not totally_positive(k):
        k += 1
    assert not totally_positive(k - 1)
    return k


def q_values(poly):
    k = least_k(poly)
    return [[1, 0, 0], [k, 1, 0], [k + 1, 1, 0]], k


def lattice(poly, qvec):
    import sextic_lattice as SL
    monos, A = S.coefficient_matrix(poly, qvec)
    Lb = S.integral_lattice(A)
    G = SL.gram(poly, qvec, Lb)
    assert all(x.denominator == 1 for row in G for x in row)
    return Lb, [[int(x) for x in row] for row in G]


def enum(G, bound):
    """all nonzero x in Z^8 with x^T G x <= bound (G integral positive
    definite): LLL on the Gram matrix (python-flint), then Fincke-Pohst in
    exact rational arithmetic; returns (norm, x) in the original basis."""
    n = len(G)
    Gm = flint.fmpz_mat(G)
    _, T = Gm.lll(transform=True, rep="gram", gram="exact")
    Tm = [[int(T[i, j]) for j in range(n)] for i in range(n)]
    G2 = [[sum(Tm[i][a] * G[a][b] * Tm[j][b] for a in range(n)
               for b in range(n)) for j in range(n)] for i in range(n)]
    A = [[Fr(G2[i][j]) for j in range(n)] for i in range(n)]
    q = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        q[i][i] = A[i][i]
        for j in range(i + 1, n):
            q[i][j] = A[i][j] / A[i][i]
        for k in range(i + 1, n):
            for l in range(k, n):
                A[k][l] -= q[i][k] * q[i][l] * q[i][i]
                A[l][k] = A[k][l]
    out = []
    y = [0] * n

    def rec(i, rem):
        c = -sum(q[i][j] * y[j] for j in range(i + 1, n))
        r = math.isqrt(int(rem / q[i][i]) + 1) + 1
        for yi in range(math.floor(c) - r, math.ceil(c) + r + 1):
            dd = q[i][i] * (yi - c) ** 2
            if dd <= rem:
                y[i] = yi
                if i == 0:
                    if any(y):
                        out.append(y[:])
                else:
                    rec(i - 1, rem - dd)
        y[i] = 0
    rec(n - 1, Fr(bound))
    res = []
    for yy in out:
        xx = [sum(yy[i] * Tm[i][j] for i in range(n)) for j in range(n)]
        nv = sum(xx[a] * G[a][b] * xx[b] for a in range(n) for b in range(n))
        assert nv <= bound
        res.append((nv, xx))
    return res


def params(Lb, x):
    return [sum(Fr(x[b]) * Lb[b][i] for b in range(8)) for i in range(8)]


def least_weil(poly, qvec, Lb, G, start=24):
    """least norm -chi/8 of an integral class v of S(0,q) with Omega(v) != 0,
    by enumeration with a doubling bound; returns (norm, classes with Omega
    != 0 of that norm, all vectors of smaller norm, lattice minimum)"""
    b = start
    while True:
        vecs = [(nv, params(Lb, x)) for nv, x in enum(G, b)]
        nz = [(nv, c) for nv, c in vecs if omega_nonzero(poly, qvec, c)]
        if nz:
            m = min(nv for nv, _ in nz)
            at = [c for nv, c in nz if nv == m]
            below = [(nv, c) for nv, c in vecs if nv < m]
            return m, at, below, min(nv for nv, _ in vecs)
        b *= 2


# ------------------------------------------------ imaginary quadratic fields
def imag_quadratic(poly, qvec):
    """the imaginary quadratic subfield of F_0(sqrt(-q)), as its D (K =
    Q(sqrt(-D))), or None.  If Q(sqrt(-D)) lies in F, D squarefree, then
    D q is a square in F_0 and D is the squarefree part of Nm(q); conversely.
    D q is a square in F_0 iff prod_j (x^2 - D tau_j(q)) is reducible over Q."""
    import sympy
    x, y = sympy.symbols("x y")
    P = sum(c * y ** (3 - i) for i, c in enumerate(poly))
    q = qvec[0] + qvec[1] * y + qvec[2] * y ** 2
    Nm = int(sympy.resultant(P, q, y))
    assert Nm > 0
    D = 1
    for p, e in sympy.factorint(Nm).items():
        if e % 2:
            D *= p
    R = sympy.Poly(sympy.resultant(P, x ** 2 - D * q, y), x)
    fl = sympy.factor_list(R.as_expr())
    irreducible = len(fl[1]) == 1 and fl[1][0][1] == 1
    return (None if irreducible else D), Nm


if __name__ == "__main__":
    import time
    t0 = time.time()
    print("Least -chi of an integral class of S(0,q) whose Orlov product "
          "kappa(v,v) has a nonzero F-Weil part (Omega(v) != 0), for the "
          "sixteen cubic fields of item (LVII) and q in {1, k+alpha, "
          "k+1+alpha}; lattice minimum; imaginary quadratic subfield of F.")
    for name, poly in cubic_fields():
        qs, k = q_values(poly)
        for qvec in qs:
            Lb, G = lattice(poly, qvec)
            m, at, below, mn = least_weil(poly, qvec, Lb, G)
            D, Nm = imag_quadratic(poly, qvec)
            ex = min(at, key=lambda c: [abs(t) for t in c])
            print("  %-12s q = %-11s Nm(q) = %-3d  min -chi = %-5d  least "
                  "-chi with Omega != 0: %-5d (%d classes up to sign)  "
                  "e.g. (c0,f,g,c3) = %s  K = %s" % (
                      name, "%d%+d a" % (qvec[0], qvec[1]) if qvec[1]
                      else "1", Nm, 8 * mn, 8 * m, len(at) // 2,
                      [str(t) for t in ex],
                      "Q(sqrt(-%d))" % D if D else "none"))
    print("  [%.1fs]" % (time.time() - t0))
