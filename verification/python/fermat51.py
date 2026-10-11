"""Finite checks for the Fermat varieties of degree 51 (Subsection "ssec:degree51").

The class left by Aoki's reduction lives at level 102.  Prints, line for line as
c/fermat51.c and julia/fermat51.jl:
  * the threefold characters alpha = (1, 7, 51, 60, 85) and alpha' = (91, 34, 26, 98, 57) of
    level 102: entries nonzero, |t alpha|, |t alpha'| in {2, 3} and |t alpha| + |t alpha'| = 5
    for every unit t, |5 alpha| = |37 alpha'| = 2, and their join beta, which has no pair and is a
    Hodge character of the Fermat eightfold;
  * the order parity nu_17: beta has exactly one entry of order 17, and every generator of
    Aoki's group S_102 (the pairs and the standard characters) has an even number;
  * every balanced multiset of 4 or 6 nonzero residues modulo 102 has nu_17 = 0;
  * the exponent conditions of the two block families, of degrees 6 and 18.
With --lattice (needs python-flint) the lattice computation B_102 = S_102 + Z u(beta) and
[B_102 : S_102] = 2 is also run, without Aoki's theorem.
"""
import sys
from math import gcd

M = 102
ALPHA = (1, 7, 51, 60, 85)
ALPHA2 = (91, 34, 26, 98, 57)
BETA = ALPHA + ALPHA2
# Family of degree 6 for 37 alpha' = (1, 34, 44, 56, 69): blocks s, t, Q (quadratic), F (cubic);
# u0 = F^2, u1 = c1 Q^3, u2 = c2 t^3 F, u3 = c3 s^3 F, u4 = c4 s^2 t^4.
FAMA = (("s", (0, 0, 0, 3, 2), 1), ("t", (0, 0, 3, 0, 4), 1), ("Q", (0, 3, 0, 0, 0), 2),
        ("F", (2, 0, 1, 1, 0), 3))
# Family of degree 18 for 5 alpha = (5, 35, 51, 96, 17): blocks Q (quadratic), t, F (nonic), s,
# G (sextic); u0 = G^3, u1 = c1 s^6 G^2, u2 = c2 F^2, u3 = c3 s t^17, u4 = c4 Q^6 G.
FAMB = (("Q", (0, 0, 0, 0, 6), 2), ("t", (0, 0, 0, 17, 0), 1), ("F", (0, 0, 2, 0, 0), 9),
        ("s", (0, 6, 0, 1, 0), 1), ("G", (3, 2, 0, 0, 1), 6))


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
    assert all(x % M for x in BETA) and sum(ALPHA) == 2 * M and sum(ALPHA2) == 3 * M
    na = [norm(ALPHA, t) for t in units(M)]
    nb = [norm(ALPHA2, t) for t in units(M)]
    assert all(x in (2, 3) for x in na + nb) and all(x + y == 5 for x, y in zip(na, nb))
    a5 = tuple(5 * x % M for x in ALPHA)
    a37 = tuple(37 * x % M for x in ALPHA2)
    assert a5 == (5, 35, 51, 96, 17) and norm(a5, 1) == 2
    assert a37 == (1, 34, 44, 56, 69) and norm(a37, 1) == 2
    lines.append("alpha %s |alpha| = %d, 5 alpha = %s with |5 alpha| = 2, |t alpha| in {2,3} for all %d units, %d of them 2"
                 % (tup(ALPHA), norm(ALPHA, 1), tup(a5), len(na), na.count(2)))
    lines.append("alpha' %s, 37 alpha' = %s with |37 alpha'| = 2, |t alpha| + |t alpha'| = 5 for all %d units"
                 % (tup(ALPHA2), tup(a37), len(nb)))
    lines.append("units t < 51: " + " ".join("%d:%d%d" % (t, x, y) for t, x, y in zip(units(M), na, nb) if t < 51))
    assert not any((BETA[i] + BETA[j]) % M == 0 for i in range(10) for j in range(i + 1, 10))
    assert all(sum(t * x % M for x in BETA) == 5 * M for t in units(M))
    lines.append("beta = alpha * alpha': |t beta| = 5 for all units t, no pair: Hodge character of X^8_102")
    return lines


def parity():
    lines = []
    o17 = [y for y in BETA if order(y) == 17]
    assert o17 == [60]
    lines.append("nu_17(beta) = 1: the only entry of order 17 is %d" % o17[0])
    gens = [(y, M - y) for y in range(1, M)] + standard(M)
    assert not [g for g in gens if sum(1 for y in g if order(y) == 17) % 2]
    lines.append("nu_17 vanishes on S_102: %d pairs and %d standard characters checked" % (M - 1, len(standard(M))))
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
                    odd += sum(1 for y in a + c if order(y) == 17) % 2
        assert odd == 0
        lines.append("balanced multisets of %d nonzero residues mod 102: %d, all with nu_17 = 0" % (k, count))
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
        lines.append("family %s block %s (degree %d) exponents %s weight %d = %d*102"
                     % (name, bname, d, tup(e), w, w // M))
    assert degs == [D] * 5 and adeg == 2 * D
    return lines, degs


def families():
    la, da = family("A", (1, 34, 44, 56, 69), FAMA, 6)
    lb, db = family("B", (5, 35, 51, 96, 17), FAMB, 18)
    assert not any(e[0] and e[4] for _, e, _ in FAMA) and not any(e[2] and e[3] for _, e, _ in FAMB)
    return la + ["family A: every u_k has degree 6, A has degree 12; (0,4) shares no block"] + \
        lb + ["family B: every u_k has degree 18, A has degree 36; (2,3) shares no block"]


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
    return ["level 102: rank K = %d, rank S + (51) = %d, invariant factors %s, so [B : S] = 2" % (rK, len(dS), [x for x in dS if x > 1]),
            "level 102: S + (51) + Z u(beta) is saturated of rank %d, so B = S + Z u(beta)" % rK]


if __name__ == "__main__":
    out = characters() + parity() + small_multisets() + families()
    if "--lattice" in sys.argv:
        out += lattice_lines()
    for line in out:
        print(line)
    print("%d lines, all checks passed" % len(out))
