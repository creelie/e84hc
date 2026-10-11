"""Finite checks for the Fermat varieties of degree 52 (Subsection "ssec:degree52").

Prints, line for line as c/fermat52.c and julia/fermat52.jl:
  * the threefold characters alpha = (1, 5, 16, 37, 45) and alpha' = (29, 18, 42, 50, 17) of
    level 52: entries nonzero, |t alpha|, |t alpha'| in {2, 3} and |t alpha| + |t alpha'| = 5 for
    every unit t, |alpha| = |9 alpha'| = 2, and their join beta, which has no pair and is a Hodge
    character of the Fermat eightfold;
  * the order parity nu_13: beta has exactly one entry of order 13, and every generator of
    Aoki's group S_52 (the pairs and the standard characters) has an even number;
  * every balanced multiset of 4 or 6 nonzero residues modulo 52 has nu_13 = 0;
  * the exponent conditions of the two block families, of degrees 14 and 5.
With --lattice (needs python-flint) the lattice computation B_52 = S_52 + Z u(beta) and
[B_52 : S_52] = 2 is also run, without Aoki's theorem.
"""
import sys
from math import gcd

M = 52
ALPHA = (1, 5, 16, 37, 45)
ALPHA2 = (29, 18, 42, 50, 17)
BETA = ALPHA + ALPHA2
# Family of degree 14 for alpha: blocks G (quartic), s, F (septic), t, H = s^2 + kappa s t + t^2;
# u0 = c0 F^2, u1 = c1 s F H^3, u2 = s t^13, u3 = c3 G^3 H, u4 = c4 s^3 G F.
FAMA = (("G", (0, 0, 0, 3, 1), 4), ("s", (0, 1, 1, 0, 3), 1), ("F", (2, 1, 0, 0, 1), 7),
        ("t", (0, 0, 13, 0, 0), 1), ("H", (0, 3, 0, 1, 0), 2))
# Family of degree 5 for 9 alpha' = (1, 6, 14, 34, 49): blocks t, s, s - t, L = s + kappa t, Q;
# u0 = c0 s^3 (s-t)^2, u1 = c1 L^3 Q, u2 = t^5, u3 = c3 t (s-t)^3 L, u4 = c4 s Q^2.
FAMB = (("t", (0, 0, 5, 1, 0), 1), ("s", (3, 0, 0, 0, 1), 1), ("s-t", (2, 0, 0, 3, 0), 1),
        ("L", (0, 3, 0, 1, 0), 1), ("Q", (0, 1, 0, 0, 2), 2))


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


def norm(a, t, m=M):
    return sum(t * x % m for x in a) // m


def order(y, m=M):
    return m // gcd(y, m)


def tup(a):
    return "(" + ", ".join(str(x) for x in a) + ")"


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
    assert all(x % M for x in BETA) and sum(ALPHA) % M == 0 and sum(ALPHA2) % M == 0
    na = [norm(ALPHA, t) for t in units(M)]
    nb = [norm(ALPHA2, t) for t in units(M)]
    assert all(x in (2, 3) for x in na + nb) and all(x + y == 5 for x, y in zip(na, nb))
    a9 = tuple(9 * x % M for x in ALPHA2)
    assert norm(ALPHA, 1) == 2 and a9 == (1, 6, 14, 34, 49) and norm(a9, 1) == 2
    lines.append("alpha %s |alpha| = %d, |t alpha| in {2,3} for all %d units, %d of them 2"
                 % (tup(ALPHA), norm(ALPHA, 1), len(na), na.count(2)))
    lines.append("alpha' %s, 9 alpha' = %s with |9 alpha'| = 2, |t alpha| + |t alpha'| = 5 for all %d units"
                 % (tup(ALPHA2), tup(a9), len(nb)))
    lines.append("units t < 26: " + " ".join("%d:%d%d" % (t, x, y) for t, x, y in zip(units(M), na, nb) if t < 26))
    assert not any((BETA[i] + BETA[j]) % M == 0 for i in range(10) for j in range(i + 1, 10))
    assert all(sum(t * x % M for x in BETA) == 5 * M for t in units(M))
    lines.append("beta = alpha * alpha': |t beta| = 5 for all units t, no pair: Hodge character of X^8_52")
    return lines


def parity():
    lines = []
    o13 = [y for y in BETA if order(y) == 13]
    assert o13 == [16]
    lines.append("nu_13(beta) = 1: the only entry of order 13 is %d" % o13[0])
    gens = [(y, M - y) for y in range(1, M)] + standard(M)
    assert not [g for g in gens if sum(1 for y in g if order(y) == 13) % 2]
    lines.append("nu_13 vanishes on S_52: %d pairs and %d standard characters checked" % (M - 1, len(standard(M))))
    return lines


def halves(h):
    """All nondecreasing h-tuples of nonzero residues."""
    out = [()]
    for _ in range(h):
        out = [a + (x,) for a in out for x in range(a[-1] if a else 1, M)]
    return out


def small_multisets():
    """Balanced multisets of k nonzero residues, k = 4, 6.  A balanced multiset, sorted, splits
    into its k/2 smallest and its k/2 largest elements A and C, with f(A) + f(C) = (k/2) M for
    f(A)_t = sum <t a>; we match the two halves through f."""
    lines = []
    U = units(M)
    for k in (4, 6):
        h = k // 2
        hs = halves(h)
        table = {}
        for a in hs:
            table.setdefault(tuple(sum(t * x % M for x in a) for t in U), []).append(a)
        count = odd = 0
        for a in hs:
            want = tuple(h * M - sum(t * x % M for x in a) for t in U)
            for c in table.get(want, []):
                if c[0] >= a[-1]:
                    count += 1
                    odd += sum(1 for y in a + c if order(y) == 13) % 2
        assert odd == 0
        lines.append("balanced multisets of %d nonzero residues mod 52: %d, all with nu_13 = 0" % (k, count))
    return lines


def family(name, al, fam, D):
    lines = []
    degs = [0] * 5
    adeg = 0
    for bname, e, d in fam:
        w = sum(a * x for a, x in zip(al, e))
        assert w % M == 0 and any(e) and not all(e)
        adeg += w // M * d
        for k in range(5):
            degs[k] += e[k] * d
        lines.append("family %s block %s (degree %d) exponents %s weight %d = %d*52"
                     % (name, bname, d, tup(e), w, w // M))
    assert degs == [D] * 5 and adeg == 2 * D
    return lines, degs


def families():
    la, da = family("A", ALPHA, FAMA, 14)
    lb, db = family("B", (1, 6, 14, 34, 49), FAMB, 5)
    assert not any(e[0] and e[2] for _, e, _ in FAMA) and not any(e[1] and e[2] for _, e, _ in FAMB)
    return la + ["family A: every u_k has degree 14, A has degree 28; (0,2) shares no block"] + \
        lb + ["family B: every u_k has degree 5, A has degree 10; (1,2) shares no block"]


def lattice_lines():
    import flint

    def u(a):
        v = [0] * (M - 1)
        for x in a:
            v[x % M - 1] += 1
        return v

    rows = []
    for y in range(1, M):
        v = [0] * (M - 1); v[y - 1] += 1; v[(-y) % M - 1] += 1; rows.append(v)
    rows += [u(s) for s in standard(M)]
    half = [u((M // 2,))]

    def snf(r):
        S = flint.fmpz_mat(r).snf()
        return [int(S[i, i]) for i in range(min(S.nrows(), S.ncols())) if S[i, i] != 0]
    A = flint.fmpz_mat([[2 * (t * y % M) - M for y in range(1, M)] for t in units(M)])
    rK = M - 1 - A.rank()
    dS = snf(rows + half)
    dL = snf(rows + half + [u(BETA)])
    assert len(dS) == rK and [x for x in dS if x > 1] == [2]
    assert len(dL) == rK and all(x == 1 for x in dL)
    return ["level 52: rank K = %d, rank S + (26) = %d, invariant factors %s, so [B : S] = 2" % (rK, len(dS), [x for x in dS if x > 1]),
            "level 52: S + (26) + Z u(beta) is saturated of rank %d, so B = S + Z u(beta)" % rK]


if __name__ == "__main__":
    out = characters() + parity() + small_multisets() + families()
    if "--lattice" in sys.argv:
        out += lattice_lines()
    for line in out:
        print(line)
    print("%d lines, all checks passed" % len(out))
