"""Finite checks for the Fermat varieties of degree 44 (Subsection "ssec:degree44").

Prints, line for line as c/fermat44.c and julia/fermat44.jl:
  * the threefold character alpha and the curve character b of level 44: entries nonzero,
    |t alpha| + |t b| = 4 for every unit t, |alpha| = 2, and their join beta, which has no
    pair and is a Hodge character of the Fermat sixfold;
  * the order parity nu_11: beta has exactly one entry of order 11, and every generator of
    Aoki's group S_44 (the pairs and the standard characters) has an even number;
  * every balanced multiset of 4 or 6 nonzero residues modulo 44 has nu_11 = 0;
  * the exponent conditions of the block family of curves of degree 11.
With --lattice (needs python-flint) the lattice computation B_44 = S_44 + Z u(beta) and
[B_44 : S_44] = 2 is also run, without Aoki's theorem.
"""
import sys
from math import gcd

M = 44
ALPHA = (1, 5, 8, 33, 41)
B = (9, 37, 42)
BETA = ALPHA + B
# u0 = c0 s^3 P Q, u1 = c1 P Q^2, u2 = t^11, u3 = c3 Q S^4, u4 = s P^2; deg P, Q, S = 5, 3, 2.
FAM = (("s", (3, 0, 0, 0, 1), 1), ("t", (0, 0, 11, 0, 0), 1), ("P", (1, 1, 0, 0, 2), 5),
       ("Q", (1, 2, 0, 1, 0), 3), ("S", (0, 0, 0, 4, 0), 2))


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
    assert all(x % M for x in BETA) and sum(ALPHA) % M == 0 and sum(B) % M == 0
    na = [norm(ALPHA, t) for t in units(M)]
    nb = [norm(B, t) for t in units(M)]
    assert all(x + y == 4 for x, y in zip(na, nb)) and norm(ALPHA, 1) == 2
    lines.append("alpha %s |alpha| = %d, |t alpha| in {2,3} for all %d units, %d of them 2"
                 % (tup(ALPHA), norm(ALPHA, 1), len(na), na.count(2)))
    lines.append("b %s |b| = %d, |t alpha| + |t b| = 4 for all %d units" % (tup(B), norm(B, 1), len(nb)))
    lines.append("units t < 22: " + " ".join("%d:%d%d" % (t, x, y) for t, x, y in zip(units(M), na, nb) if t < 22))
    assert not any((BETA[i] + BETA[j]) % M == 0 for i in range(8) for j in range(i + 1, 8))
    assert all(2 * sum(t * x % M for x in BETA) == 8 * M for t in units(M))
    lines.append("beta = alpha * b: |t beta| = 4 for all units t, no pair: Hodge character of X^6_44")
    return lines


def parity():
    lines = []
    o11 = [y for y in BETA if order(y) == 11]
    assert o11 == [8]
    lines.append("nu_11(beta) = 1: the only entry of order 11 is %d" % o11[0])
    gens = [(y, M - y) for y in range(1, M)] + standard(M)
    assert not [g for g in gens if sum(1 for y in g if order(y) == 11) % 2]
    lines.append("nu_11 vanishes on S_44: %d pairs and %d standard characters checked" % (M - 1, len(standard(M))))
    return lines


def small_multisets():
    """Balanced multisets of k nonzero residues, k = 4, 6, by a nondecreasing search."""
    lines = []
    U = units(M)
    for k in (4, 6):
        count = odd = 0
        stack = [((), 1)]
        while stack:
            a, lo = stack.pop()
            if len(a) == k:
                if sum(a) % M == 0 and all(2 * sum(t * x % M for x in a) == k * M for t in U):
                    count += 1
                    odd += sum(1 for y in a if order(y) == 11) % 2
                continue
            for x in range(M - 1, lo - 1, -1):
                stack.append((a + (x,), x))
        assert odd == 0
        lines.append("balanced multisets of %d nonzero residues mod 44: %d, all with nu_11 = 0" % (k, count))
    return lines


def family():
    lines = []
    degs = [0] * 5
    adeg = 0
    for name, e, d in FAM:
        w = sum(a * x for a, x in zip(ALPHA, e))
        assert w % M == 0 and any(e) and not all(e)
        adeg += w // M * d
        for k in range(5):
            degs[k] += e[k] * d
        lines.append("family block %s (degree %d) exponents %s weight %d = %d*44" % (name, d, tup(e), w, w // M))
    assert degs == [11] * 5 and adeg == 22
    lines.append("family: every u_k has degree 11, A has degree 22; (0,2) shares no block")
    return lines


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
    return ["level 44: rank K = %d, rank S + (22) = %d, invariant factors %s, so [B : S] = 2" % (rK, len(dS), [x for x in dS if x > 1]),
            "level 44: S + (22) + Z u(beta) is saturated of rank %d, so B = S + Z u(beta)" % rK]


if __name__ == "__main__":
    out = characters() + parity() + small_multisets() + family()
    if "--lattice" in sys.argv:
        out += lattice_lines()
    for line in out:
        print(line)
    print("%d lines, all checks passed" % len(out))
