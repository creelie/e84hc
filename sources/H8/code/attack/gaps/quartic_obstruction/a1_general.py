"""a1_general.py -- the admissibility scan (a1_cmscan) for other real quadratic fields F0
(track A1).  F0 = Q(omega) with omega the eigenvalue r1 of a symmetric unimodular-compatible
matrix Rm (O_0 = Z[omega]):  Q(sqrt5): [[0,1],[1,1]];  Q(sqrt2): [[1,1],[1,-1]];
Q(sqrt13): [[2,1],[1,-1]].  For each positive definite binary form (A,B,C) over Z[omega] with
coefficients in a box, the secant lattice e^{theta_t} S_{F'}(q) cap R_Z is computed exactly,
all vectors with chi <= BOUND are listed with their exact Hochschild profile, and the
admissible ones ((chi, rank V, r^2) = (4,1,18) or (6,2,20)) are reported.
Usage: python3 a1_general.py NAME OB BOUND"""
import sys, time, itertools, pickle, random
from fractions import Fraction as Fr
from math import isqrt, lcm
import flint
from ealib import *
from a1model import RMModel, QS
import a1_secant as SEC

FIELDS = {"sqrt5": ((0, 1), (1, 1)), "sqrt2": ((1, 1), (1, -1)), "sqrt13": ((2, 1), (1, -1)), "sqrt17": ((0, 2), (2, 1)), "sqrt10": ((1, 3), (3, -1))}
name = sys.argv[1] if len(sys.argv) > 1 else "sqrt2"
OB = int(sys.argv[2]) if len(sys.argv) > 2 else 1
BOUND = int(sys.argv[3]) if len(sys.argv) > 3 else 8
M = RMModel(FIELDS[name])
SEC.M = M
SEC.S = M.disc
S = M.disc
OMEGA = M.r1


def oelt(a, b):
    return QS(a, 0, S) + OMEGA * b


def to_ab(x):
    """x = a + b omega with omega = tr/2 + sqrt(disc)/2: b = 2 x.b, a = x.a - b tr/2."""
    b = 2 * x.b
    a = x.a - b * M.tr / 2
    return a, b


def Vmat_of(a, f, c, q):
    q1, q2 = M.tau(q)
    f1, f2 = M.tau(f)
    Z = QS(0, 0, S)
    c1 = [QS(1, 0, S), Z, -q1]
    c2 = [QS(1, 0, S), Z, -q2]
    e = [Z, QS(1, 0, S), Z]
    return [[Fr(a) * c1[i] * c2[j] + f1 * e[i] * c2[j] + f2 * c1[i] * e[j] + Fr(c) * e[i] * e[j]
             for j in range(3)] for i in range(3)]


def rational(u):
    out = {}
    for k, c in u.items():
        assert c.b == 0
        if c.a != 0:
            out[k] = c.a
    return out


def saturate_classes(vecs):
    keys = sorted(set(k for v in vecs for k in v))
    kid = {k: i for i, k in enumerate(keys)}
    Mq = flint.fmpq_mat(len(vecs), len(keys))
    for r, v in enumerate(vecs):
        for k, c in v.items():
            c = Fr(c)
            Mq[r, kid[k]] = flint.fmpq(c.numerator, c.denominator)
    Rr, rk = Mq.rref()
    B = [[Fr(int(Rr[i, j].p), int(Rr[i, j].q)) for j in range(len(keys))] for i in range(rk)]
    den = 1
    for row in B:
        for x in row:
            den = lcm(den, x.denominator)
    cols = flint.fmpz_mat(len(keys), rk)
    for j in range(len(keys)):
        for i in range(rk):
            cols[j, i] = int(B[i][j] * den)
    H = cols.hnf()
    Lrows = [[Fr(int(H[i, j]), den) for j in range(rk)] for i in range(H.nrows()) if any(H[i, j] != 0 for j in range(rk))]
    Lm = flint.fmpq_mat(rk, rk)
    for i in range(rk):
        for j in range(rk):
            Lm[i, j] = flint.fmpq(Lrows[i][j].numerator, Lrows[i][j].denominator)
    Dual = Lm.inv().transpose()
    out = []
    for i in range(rk):
        cc = [Fr(int(Dual[i, j].p), int(Dual[i, j].q)) for j in range(rk)]
        v = {}
        for j in range(len(keys)):
            s = sum(cc[a] * B[a][j] for a in range(rk))
            if s != 0:
                v[keys[j]] = s
        assert all(x.denominator == 1 for x in v.values())
        out.append(v)
    return out


def short_vectors(basis, bound):
    G = [[M.chi(a, b) for b in basis] for a in basis]
    n = len(basis)
    Gq = flint.fmpq_mat(n, n)
    for i in range(n):
        for j in range(n):
            Gq[i, j] = flint.fmpq(int(G[i][j]), 1)
    try:
        U = flint.fmpz_mat([[int(x) for x in r] for r in G]).lll(transform=True, rep="gram")[1]
        red = []
        for i in range(n):
            v = {}
            for k in range(n):
                if int(U[i, k]):
                    v = add(v, sc(Fr(int(U[i, k])), basis[k]))
            red.append(v)
    except Exception:
        red = basis
    G = [[M.chi(a, b) for b in red] for a in red]
    for i in range(n):
        for j in range(n):
            Gq[i, j] = flint.fmpq(int(G[i][j]), 1)
    Gi = Gq.inv()
    lims = []
    for i in range(n):
        x = Gi[i, i]
        val = Fr(int(x.p), int(x.q)) * bound
        lims.append(isqrt(int(val) + 1) + 1)
    out = []
    for cs in itertools.product(*[range(-L, L + 1) for L in lims]):
        if not any(cs):
            continue
        if next(x for x in cs if x != 0) < 0:
            continue
        cv = sum(cs[i] * cs[j] * G[i][j] for i in range(n) for j in range(n))
        if cv <= bound:
            v = {}
            for i in range(n):
                if cs[i]:
                    v = add(v, sc(Fr(cs[i]), red[i]))
            out.append((v, int(cv)))
    return out


if __name__ == "__main__":
    t0 = time.time()
    th, thR = M.theta, M.thetaR
    gens = [wedge(power(th, i), power(thR, j)) for i in range(5) for j in range(5 - i)]
    RZ = saturate_classes(gens)
    check("%s: R_Z has rank 9" % name, len(RZ) == 9)
    # index of R_Z over the naive lattice spanned by monomials theta^i thetaR^j / (i! j!)?  report Gram det
    G = [[M.chi(a, b) for b in RZ] for a in RZ]
    print("  det(chi on R_Z) =", flint.fmpz_mat([[int(x) for x in r] for r in G]).det())
    rng = range(-OB, OB + 1)
    seen = set()
    stats = {}
    adm = []
    nforms = 0
    for (a0, a1, b0, b1, c0, c1) in itertools.product(rng, repeat=6):
        A = oelt(a0, a1); B = oelt(b0, b1); C = oelt(c0, c1)
        if C == 0:
            continue
        Dl = B * B - 4 * A * C
        if not (Dl.val() < 0 and Dl.conj().val() < 0):
            continue
        t = -B / (2 * C)
        q = A / C - t * t
        tt = to_ab(t); qq = to_ab(q)
        if (tt, qq) in seen:
            continue
        seen.add((tt, qq))
        nforms += 1
        et = expo(M.theta_f(tt), 8)
        span = [wedge(et, rational(M.from_V(Vmat_of(a, f, c, qq))))
                for (a, f, c) in [(1, (0, 0), 0), (0, (1, 0), 0), (0, (0, 1), 0), (0, (0, 0), 1)]]
        # lattice: span_Q(span) cap R_Z  = saturation of span inside Z-span(RZ) ... compute as
        # saturation in the monomial lattice (R_Z = R cap Z^256, and span subset R)
        L = saturate_classes(span)
        for v, cv in short_vectors(L, BOUND):
            prof = M.profile(v, 2)
            rkV = SEC.rankV(M.to_V(v))
            kk = (cv, rkV, tuple(prof))
            stats[kk] = stats.get(kk, 0) + 1
            if (cv, rkV, prof[2]) in [(4, 1, 18), (6, 2, 20)] and prof[1] == 8:
                adm.append(((tt, qq), cv, rkV, prof, v.get(0, 0)))
    print("%s: scanned %d complex-secant planes (forms with coefficients in [-%d,%d])  (%.1fs)"
          % (name, nforms, OB, OB, time.time() - t0))
    for kk in sorted(stats):
        print("   chi=%d rankV=%d profile=%s : %d" % (kk[0], kk[1], list(kk[2]), stats[kk]))
    print("ADMISSIBLE: %d" % len(adm))
    for a in adm[:30]:
        print("   ", a)
    pickle.dump((stats, adm), open("a1_general_%s_%d_%d.pkl" % (name, OB, BOUND), "wb"))
    print("time %.1fs" % (time.time() - t0))
