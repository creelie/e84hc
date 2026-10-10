"""Finite checks for the Fermat varieties of degree 114 (Section "sec:fermat114").

Prints, line for line as c/fermat114.c and julia/fermat114.jl:
  * the two threefold characters alpha1, alpha2 of level 114 and their join beta:
    every entry nonzero, no two entries adding up to 0, |t alpha| in {2, 3} and
    |t alpha1| + |t alpha2| = 5 for every unit t, so that beta is a Hodge character of
    the Fermat eightfold;
  * the order parity nu_19: beta has exactly one entry of order 19, and every generator
    of Aoki's group S_114 (the pairs and the standard characters) has an even number;
  * the exponent conditions of the two block families of curves: for every block of
    zeros the weighted sum of the exponents is a multiple of 114, and the degrees.
Then, here and in Julia only, family I (cubic forms) is checked in exact rational
arithmetic at three values of lambda: the five forms add up to zero, the family is
nondegenerate, and the residue I(lambda) agrees with the closed formula of the paper.
With --lattice (needs python-flint) the index computations [B_m : S_m] = 2 and
B_m = S_m + Z u(beta) are also run, at the levels 57 and 114.
"""
import sys
from fractions import Fraction as Fr
from math import gcd

M = 114
ALPHA1 = (1, 25, 43, 57, 102)
ALPHA2 = (39, 63, 68, 80, 92)
BETA = ALPHA1 + ALPHA2
ALPHA2T = tuple(13 * x % M for x in ALPHA2)          # (51, 21, 86, 14, 56), |.| = 2

# Family I (cubic forms), character ALPHA2T: blocks at s = 0, 1, lambda, infinity.
FAM1 = {"0": (0, 0, 1, 2, 0), "1": (0, 0, 2, 0, 1), "lambda": (1, 3, 0, 0, 0), "inf": (2, 0, 0, 1, 2)}
# Family II (degree 24), character ALPHA1: u0 = F^3 K, u1 = a H F K^5, u2 = b H^5 F^2,
# u3 = -(1+a+b) G^2, u4 = c H K t^19, with deg F = 7, deg H = 2, deg G = 12, K = s(s-1)(s-kappa).
FAM2 = {"F": ((3, 1, 2, 0, 0), 7), "H": ((0, 1, 5, 0, 1), 2), "G": ((0, 0, 0, 2, 0), 12),
        "K": ((1, 5, 0, 0, 1), 3), "t": ((0, 0, 0, 0, 19), 1)}


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


def norm(a, t, m=M):
    return sum(t * x % m for x in a) // m


def order(y, m=M):
    return m // gcd(y, m)


def standard(m):
    out = []
    for p in [q for q in range(2, m + 1) if m % q == 0 and all(q % r for r in range(2, q))]:
        if m == p:
            continue
        d = m // p
        for i in range(1, d):
            if p == 2:
                out.append((i, i + d, (-2 * i) % m, d))
            else:
                out.append(tuple(i + j * d for j in range(p)) + ((-p * i) % m,))
    return out


def characters():
    lines = []
    for name, a in (("alpha1", ALPHA1), ("alpha2", ALPHA2), ("13*alpha2", ALPHA2T)):
        assert all(x % M for x in a) and sum(a) % M == 0
        assert not any((a[i] + a[j]) % M == 0 for i in range(5) for j in range(i + 1, 5))
        ns = [norm(a, t) for t in units(M)]
        assert set(ns) <= {2, 3}
        lines.append("%s %s |a| = %d, |ta| in {2,3} for all %d units, %d of them 2"
                     % (name, a, norm(a, 1), len(ns), ns.count(2)))
    assert norm(ALPHA1, 1) == 2 and norm(ALPHA2T, 1) == 2
    assert all(norm(ALPHA1, t) + norm(ALPHA2, t) == 5 for t in units(M))
    assert not any((BETA[i] + BETA[j]) % M == 0 for i in range(10) for j in range(i + 1, 10))
    lines.append("beta = alpha1 * alpha2: |t beta| = 5 for all units t, no pair: Hodge character of X^8_114")
    return lines


def parity():
    lines = []
    o19 = [y for y in BETA if order(y) == 19]
    assert o19 == [102]
    lines.append("nu_19(beta) = 1: the only entry of order 19 is %d" % o19[0])
    gens = [(y, M - y) for y in range(1, M)] + standard(M)
    odd = [g for g in gens if sum(1 for y in g if order(y) == 19) % 2]
    assert not odd
    st = standard(M)
    lines.append("nu_19 vanishes on S_114: %d pairs and %d standard characters checked" % (M - 1, len(st)))
    return lines


def families():
    lines = []
    for blk, e in FAM1.items():
        w = sum(a * x for a, x in zip(ALPHA2T, e))
        assert w % M == 0
        lines.append("family I block %s exponents %s weight %d = %d*114" % (blk, e, w, w // M))
    assert all(sum(e[k] for e in FAM1.values()) == 3 for k in range(5))
    lines.append("family I: every u_k has degree 3, A has degree 6")
    degs = [0] * 5
    for blk, (e, d) in FAM2.items():
        w = sum(a * x for a, x in zip(ALPHA1, e))
        assert w % M == 0
        lines.append("family II block %s (degree %d) exponents %s weight %d = %d*114" % (blk, d, e, w, w // M))
        for k in range(5):
            degs[k] += e[k] * d
    assert degs == [24] * 5
    adeg = sum(sum(a * x for a, x in zip(ALPHA1, e)) // M * d for e, d in FAM2.values())
    assert adeg == 48
    lines.append("family II: every u_k has degree 24, A has degree 48")
    return lines


# ---- Family I in exact arithmetic --------------------------------------------------------

def pmul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def padd(*ps):
    r = [Fr(0)] * max(len(p) for p in ps)
    for p in ps:
        for i, x in enumerate(p):
            r[i] += x
    return r


def pscale(p, c):
    return [c * x for x in p]


def ppow(p, e):
    r = [Fr(1)]
    for _ in range(e):
        r = pmul(r, p)
    return r


def pder(p):
    return [i * p[i] for i in range(1, len(p))] or [Fr(0)]


def solve(A, b):
    n = len(A)
    M_ = [list(map(Fr, row)) + [Fr(v)] for row, v in zip(A, b)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M_[r][c] != 0)
        M_[c], M_[piv] = M_[piv], M_[c]
        for r in range(n):
            if r != c and M_[r][c] != 0:
                f = M_[r][c] / M_[c][c]
                M_[r] = [x - f * y for x, y in zip(M_[r], M_[c])]
    return [M_[i][n] / M_[i][i] for i in range(n)]


def family1(lam):
    """Forms u_k (affine chart t = 1, as polynomials in x = s - lam) and their lambda-derivatives."""
    # base forms as polynomials in s: (s-lam), (s-lam)^3, s(s-1)^2, s^2, (s-1)
    L = [-lam, Fr(1)]
    base = [L, ppow(L, 3), pmul([Fr(0), Fr(1)], ppow([Fr(-1), Fr(1)], 2)), [Fr(0), Fr(0), Fr(1)], [Fr(-1), Fr(1)]]
    dbase = [[Fr(-1)], pscale(ppow(L, 2), Fr(-3)), [Fr(0)], [Fr(0)], [Fr(0)]]   # d/dlambda at fixed s
    rows = [[(base[k] + [Fr(0)] * 4)[i] for k in range(1, 5)] for i in range(4)]
    c = [Fr(1)] + solve(rows, [-(base[0] + [Fr(0)] * 4)[i] for i in range(4)])
    # derivative of c: sum_k cdot_k base_k + sum_k c_k dbase_k = 0, cdot_0 = 0
    rhs = padd(*[pscale(dbase[k], c[k]) for k in range(5)]) + [Fr(0)] * 4
    cd = [Fr(0)] + solve(rows, [-rhs[i] for i in range(4)])
    u = [pscale(base[k], c[k]) for k in range(5)]
    ud = [padd(pscale(base[k], cd[k]), pscale(dbase[k], c[k])) for k in range(5)]
    return c, u, ud


def shift(p, x0):
    """p(s) -> p(x + x0), coefficients in x."""
    r = [Fr(0)]
    for a in reversed(p):
        r = padd(pmul(r, [x0, Fr(1)]), [a])
    return r


def residue1(lam):
    c, u, ud = family1(lam)
    assert all(x == 0 for x in padd(*u)), "the forms do not add up to zero"
    rest = (0, 3, 4)
    D = [[u[k] for k in rest], [ud[k] for k in rest], [pder(u[k]) for k in rest]]

    def det3(m):
        (a, b, cc), (d, e, f), (g, h, i) = m
        return padd(pmul(a, padd(pmul(e, i), pscale(pmul(f, h), -1))),
                    pscale(pmul(b, padd(pmul(d, i), pscale(pmul(f, g), -1))), -1),
                    pmul(cc, padd(pmul(d, h), pscale(pmul(e, g), -1))))
    Dt = det3(D)
    A = pmul(pmul([Fr(0), Fr(1)], [-lam, Fr(1)]), ppow([Fr(-1), Fr(1)], 2))       # s (s-lam) (s-1)^2
    num = shift(pmul(A, Dt), lam)
    den = shift(pmul(pmul(pmul(pmul(u[0], u[1]), u[2]), u[3]), u[4]), lam)
    k = next(i for i, x in enumerate(den) if x != 0)
    assert k == 4 and all(x == 0 for x in num[:1])
    W = den[k:]
    # power series of num / W up to x^(k-1); residue = coefficient of x^(k-1)
    inv = [Fr(1) / W[0]]
    for n in range(1, k):
        inv.append(-sum(W[j] * inv[n - j] for j in range(1, min(n, len(W) - 1) + 1)) / W[0])
    return c, sum(num[j] * inv[k - 1 - j] for j in range(0, k) if j < len(num))


def closed_form(lam):
    return -(lam ** 3 - 3 * lam ** 2 + 1) * (2 * lam ** 3 + 12 * lam ** 2 - 21 * lam + 8) / (
        lam * (lam - 1) ** 2 * (3 * lam - 2) * (2 * lam ** 2 - 1))


def family1_lines():
    lines = []
    for lam in (Fr(-3), Fr(5, 2), Fr(7, 3)):
        c, I = residue1(lam)
        assert all(x != 0 for x in c) and lam not in (0, 1)
        assert I == closed_form(lam) and I != 0
        lines.append("family I at lambda = %s: sum u_k = 0, c = (%s), I = %s, equal to the closed formula"
                     % (lam, ", ".join(str(x) for x in c), I))
    return lines


# ---- lattices ---------------------------------------------------------------------------

def lattice_lines():
    import flint
    lines = []

    def u(a, m):
        v = [0] * (m - 1)
        for x in a:
            v[x % m - 1] += 1
        return v

    def S_gens(m):
        rows = []
        for y in range(1, m):
            v = [0] * (m - 1); v[y - 1] += 1; v[(-y) % m - 1] += 1; rows.append(v)
        return rows + [u(s, m) for s in standard(m)]

    def snf(rows):
        S = flint.fmpz_mat(rows).snf()
        return [int(S[i, i]) for i in range(min(S.nrows(), S.ncols())) if S[i, i] != 0]

    def Kbasis_rank(m):
        A = flint.fmpz_mat([[2 * (t * y % m) - m for y in range(1, m)] for t in units(m)])
        return m - 1 - A.rank()
    for m, extra in ((57, None), (114, BETA)):
        rK = Kbasis_rank(m)
        S = S_gens(m)
        half = []
        if m % 2 == 0:
            half = [[1 if y == m // 2 else 0 for y in range(1, m)]]
        dS = snf(S + half)
        lines.append("level %d: rank K = %d, rank S + (m/2) = %d, invariant factors %s"
                     % (m, rK, len(dS), [x for x in dS if x > 1]))
        if extra:
            dL = snf(S + half + [u(extra, m)])
            assert len(dL) == rK and all(x == 1 for x in dL)
            lines.append("level %d: S + (m/2) + Z u(beta) is saturated of rank %d, so B = S + Z u(beta)" % (m, rK))
        else:
            assert len(dS) == rK and [x for x in dS if x > 1] == [2]
            lines.append("level %d: [B : S] = 2" % m)
    return lines


if __name__ == "__main__":
    out = characters() + parity() + families()
    if "--common" not in sys.argv:
        out += family1_lines()
    if "--lattice" in sys.argv:
        out += lattice_lines()
    for line in out:
        print(line)
    print("%d lines, all checks passed" % len(out))
