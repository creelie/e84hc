#!/usr/bin/env python3
"""
make_weil_tori.py

Writes the certificates of Section 60 of HodgeObstruction.lean (item (LI),
the Hodge classes of a very general Weil torus).

Model.  V_K = V_+ + V_- with K-bases u^+_1..u^+_2n (generators 0..2n-1) and
u^-_j = sigma(u^+_j) (generators 2n..4n-1), sigma the Galois conjugation.  A
member of the K-linear family is V^{1,0} = X + sigma(Y), X, Y complementary
n-planes of V_+, and V^{0,1} = sigma(V^{1,0}).  A rational class c of degree
2k is of type (k,k) at the member iff c ^ e_I = 0 for every product e_I of
2n-k+1 vectors of a basis of V^{1,0}, and of V^{0,1}.

Member 0 is the balanced member X = <u^+_1..u^+_n>, Y = <u^+_(n+1)..u^+_2n>,
at which the conditions say exactly that c is supported on the monomials T
with k factors in V^{1,0}.  The further members have X, Y spanned by the rows
of an integral K-matrix given by a formula.  Working modulo the prime
q = 754974721, at which delta = sqrt(-d) goes to a square root s of -d, the
script picks rows of the conditions of the further members, restricted to
the columns T, whose rank is |T| - (2 if k = n else 0); it records them
grouped by (member, conjugate or not, I) with their target monomials.
This is done at n = 2 (d = 1, 3).  At n = 3 the kernel instead uses the
orbit of member 1 under the diagonal torus (part (E) of Section 60), which
needs no recorded data.

Run from the repository root:  python3 lean/generate/make_weil_tori.py > out
"""
from itertools import combinations

Q = 754974721
CASES = [(2, 1, 3), (2, 3, 3)]   # (n, d, number of further members)


def sqrt_mod(a, q=Q):
    a %= q
    for z in range(2, 10 ** 6):
        if pow(z, (q - 1) // 2, q) == q - 1:
            break
    Qd, S = q - 1, 0
    while Qd % 2 == 0:
        Qd //= 2
        S += 1
    M, c, t, R = S, pow(z, Qd, q), pow(a, Qd, q), pow(a, (Qd + 1) // 2, q)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % q
            i += 1
        b = pow(c, 1 << (M - i - 1), q)
        M, c, t, R = i, b * b % q, t * b * b % q, R * b % q
    return R


def member_matrix(n, j):
    """the integral K-matrix (a + b delta) of member j >= 1: 2n rows of length
    2n; the first n rows span X, the last n span Y"""
    m = 2 * n
    return [[(((r * (j + 2) + c * c * (j + 1) + r * c * (2 * j + 1) + j) % 7) - 3,
              ((r * r * (j + 3) + c * (j + 5) + r * c + 2 * j + 1) % 5) - 2)
             for c in range(m)] for r in range(m)]


def popc(x):
    return bin(x).count("1")


def merge_odd(a, b):
    """sign of e_a e_b -> e_(a|b): odd number of pairs i in a, j in b, i > j"""
    s = 0
    bb = b
    while bb:
        low = bb & -bb
        s += popc(a & ~((low << 1) - 1))
        bb ^= low
    return s & 1


def wedge(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if a & b:
                continue
            val = ca * cb % Q
            if merge_odd(a, b):
                val = (Q - val) % Q
            out[a | b] = (out.get(a | b, 0) + val) % Q
    return {k: x for k, x in out.items() if x}


def vectors(n, d, j, s):
    """the bases of V^{1,0} and V^{0,1} of member j, as one-forms mod Q"""
    m = 2 * n
    if j == 0:
        hol = [{1 << i: 1} for i in range(n)] + [{1 << (m + i): 1} for i in range(n, m)]
        anti = [{1 << (m + i): 1} for i in range(n)] + [{1 << i: 1} for i in range(n, m)]
        return hol, anti
    A = member_matrix(n, j)

    def vec(row, off, conj):
        out = {}
        for c, (a, b) in enumerate(row):
            val = (a + (-b if conj else b) * s) % Q
            if val:
                out[1 << (off + c)] = val
        return out
    hol = [vec(A[r], 0, False) for r in range(n)] + [vec(A[r], m, True) for r in range(n, m)]
    anti = [vec(A[r], m, True) for r in range(n)] + [vec(A[r], 0, False) for r in range(n, m)]
    return hol, anti


def rank_rows(rows, ncols):
    basis = {}
    r = 0
    for row in rows:
        v = dict(row)
        while v:
            p = min(v)
            if p not in basis:
                inv = pow(v[p], Q - 2, Q)
                basis[p] = {k: x * inv % Q for k, x in v.items()}
                r += 1
                break
            f = v[p]
            for k, x in basis[p].items():
                v[k] = (v.get(k, 0) - f * x) % Q
                if v[k] == 0:
                    del v[k]
    return r, basis


def main():
    out = []
    names = []
    for n, d, count in CASES:
        m, N = 2 * n, 4 * n
        s = sqrt_mod(-d)
        assert s * s % Q == (-d) % Q
        hol0 = set(range(n)) | set(range(m + n, m + m))
        for k in range(1, n + 1):
            T = [sum(1 << i for i in mu) for mu in combinations(range(N), 2 * k)
                 if len(set(mu) & hol0) == k]
            col = {mu: i for i, mu in enumerate(T)}
            want = len(T) - (2 if k == n else 0)
            groups = []
            basis = {}
            r = 0
            for j in range(1, count + 1):
                hol, anti = vectors(n, d, j, s)
                for flag, vs in ((0, hol), (1, anti)):
                    for I in combinations(range(m), 2 * n - k + 1):
                        eI = {0: 1}
                        for i in I:
                            eI = wedge(eI, vs[i])
                        targets = {}
                        for nu, c in eI.items():
                            for mu in T:
                                if mu & nu:
                                    continue
                                val = c if not merge_odd(mu, nu) else (Q - c) % Q
                                targets.setdefault(mu | nu, {})
                                t = targets[mu | nu]
                                t[col[mu]] = (t.get(col[mu], 0) + val) % Q
                        kept = []
                        for tau in sorted(targets):
                            row = {kk: x for kk, x in targets[tau].items() if x}
                            v = dict(row)
                            while v:
                                p = min(v)
                                if p not in basis:
                                    inv = pow(v[p], Q - 2, Q)
                                    basis[p] = {kk: x * inv % Q for kk, x in v.items()}
                                    r += 1
                                    kept.append(tau)
                                    break
                                f = v[p]
                                for kk, x in basis[p].items():
                                    v[kk] = (v.get(kk, 0) - f * x) % Q
                                    if v[kk] == 0:
                                        del v[kk]
                            if r == want:
                                break
                        if kept:
                            groups.append((j, flag, I, kept))
                        if r == want:
                            break
                    if r == want:
                        break
                if r == want:
                    break
            assert r == want, (n, d, k, r, want)
            tag = "vt%d%d%d" % (n, d, k)
            names.append((tag, n, d, k, len(T), want))
            out.append("def %sRows : List (Nat × Nat × List Nat × List Nat) := [\n%s]" % (
                tag, ",\n".join("  (%d, %d, [%s], [%s])" % (j, f, ", ".join(map(str, I)),
                                                            ", ".join(map(str, ts)))
                                for j, f, I, ts in groups)))
            out.append("")
    out.append("/-- the cases `(n, d, k, |T|, rank, rows)`. -/")
    out.append("def vtCases : List (Nat × Nat × Nat × Nat × Nat × List (Nat × Nat × List Nat × List Nat)) := [")
    out.append(",\n".join("  (%d, %d, %d, %d, %d, %sRows)" % (n, d, k, t, w, tag)
                          for tag, n, d, k, t, w in names) + "]")
    print("\n".join(out))


if __name__ == "__main__":
    main()
