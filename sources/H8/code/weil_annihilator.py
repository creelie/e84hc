#!/usr/bin/env python3
"""
weil_annihilator.py

The annihilator of the Weil line in H^{0,2}, and the rank-zero obstruction.

Verifies, modulo a prime congruent to 1 mod 4 so that sqrt(-1) exists and the
Hodge decomposition of the split member is defined over F_p:

  (a) dim Ann_{H^{0,2}}(omega) = n^2 for both rational generators of the
      Weil line at n = 2, 3, 4.  This is Lemma 8.7.

  (b) For the explicit six-line-bundle object at n = 3, the semiregularity
      map splits by parity into an even part (cosh) and an odd part (sinh),
      and the odd kernel has dimension exactly n^2 = 9, the annihilator of
      (a) tensored with the sign vector.  This is the odd side of
      Corollary 8.9.

  (c) Every configuration lambda_i = s_i gamma + c_i ell with
      sum s_i = sum c_i = 0 in a box of side 7 whose virtual Chern character
      lies on the Weil line has semiregularity kernel exactly 15, while a
      generic configuration has kernel 0.  This is Remark 8.10.

Full rank modulo p certifies full rank over Q(i); a kernel found modulo p is
a lower bound that is confirmed by the structural argument of the lemma.
"""

import sys
from itertools import product
from collections import Counter
from math import comb

import semireg_fast as S
from semireg_fast import P, wedge, eadd, escale

NP = NF = 0


def check(name, ok, detail=""):
    global NP, NF
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    if ok:
        NP += 1
    else:
        NF += 1


def nullity(cols):
    keys = sorted({k for c in cols for k in c})
    idx = {k: i for i, k in enumerate(keys)}
    rows = [[0] * len(cols) for _ in keys]
    for j, c in enumerate(cols):
        for k, v in c.items():
            rows[idx[k]][j] = v % P
    rank = 0
    nr = len(rows)
    for c in range(len(cols)):
        piv = next((i for i in range(rank, nr) if rows[i][c]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        iv = pow(rows[rank][c], P - 2, P)
        rows[rank] = [(x * iv) % P for x in rows[rank]]
        for i in range(nr):
            if i != rank and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[rank])]
        rank += 1
        if rank == nr:
            break
    return len(cols) - rank


def deg_part(x, dd):
    return {k: v for k, v in x.items() if bin(k).count("1") == dd}


def weil_generators(mf, n, d):
    """The real and imaginary parts of (gamma -+ sqrt(-d) ell)^n, up to a
    constant; these span the Weil line at the split member."""
    def gpow(k):
        out = {0: 1}
        for _ in range(k):
            out = wedge(out, mf.gamma)
        return out

    def lpow(k):
        out = {0: 1}
        for _ in range(k):
            out = wedge(out, mf.ell)
        return out

    w1, w2 = {}, {}
    for j in range(n + 1):
        term = wedge(gpow(n - j), lpow(j))
        if j % 2 == 0:
            w1 = eadd(w1, escale((comb(n, j) * ((-d) ** (j // 2))) % P, term))
        else:
            w2 = eadd(w2, escale((comb(n, j) * ((-d) ** ((j - 1) // 2))) % P, term))
    return w1, w2


def part_a():
    print("  (a) the annihilator of the Weil line in H^{0,2}")
    rows, ok = [], True
    for n in (2, 3, 4):
        d = 3
        mf = S.Model(n, d)
        w1, w2 = weil_generators(mf, n, d)
        zb = mf.h02()
        a1 = nullity([wedge(w1, z) for z in zb])
        a2 = nullity([wedge(w2, z) for z in zb])
        rows.append("n=%d: dim H^{0,2} = %d, Ann(omega_1) = %d, Ann(omega_2) = %d, n^2 = %d"
                    % (n, len(zb), a1, a2, n * n))
        ok = ok and a1 == n * n and a2 == n * n
    check("dim Ann_{H^{0,2}}(omega) = n^2 for both generators at n = 2, 3, 4",
          ok, "\n".join(rows))


def part_b():
    print("  (b) the parity split of the semiregularity map at n = 3")
    d = 3
    mf = S.Model(3, d)
    zb = mf.h02()

    def cls(s, c):
        return eadd(escale(s % P, mf.gamma), escale(c % P, mf.ell))

    def cosh_sinh(x):
        e = mf.expcl(x)
        em = mf.expcl(escale(P - 1, x))
        return eadd(e, em), eadd(e, escale(P - 1, em))

    rows, ok = [], True
    for name, lams in (("explicit object", [(1, 3), (-2, 0), (1, -3)]),
                       ("second member", [(-1, 1), (0, -2), (1, 1)]),
                       ("generic triple", [(1, 2), (2, -1), (-1, 3)])):
        cl = [cls(s, c) for s, c in lams]
        cs = [cosh_sinh(x) for x in cl]
        kp = nullity([wedge(ch, z) for ch, _ in cs for z in zb])
        km = nullity([wedge(sh, z) for _, sh in cs for z in zb])
        tot = {}
        for x in cl:
            tot = eadd(tot, eadd(mf.expcl(x), escale(P - 1, mf.expcl(escale(P - 1, x)))))
        ch3 = deg_part(tot, 6)
        ann = nullity([wedge(ch3, z) for z in zb]) if ch3 else None
        rows.append("%-16s even kernel %2d, odd kernel %2d, total %2d, Ann(ch_3) = %s"
                    % (name, kp, km, kp + km, ann))
        if name != "generic triple":
            ok = ok and km == 9 and ann == 9 and kp + km == 15
        else:
            ok = ok and kp == 0 and km == 0
    check("odd kernel = Ann(omega) = n^2 = 9 and total = 15 for Weil objects; 0 for generic",
          ok, "\n".join(rows))


def part_c():
    print("  (c) every Weil configuration in the family has the same kernel")
    d = 3
    mf = S.Model(3, d)
    w1, w2 = weil_generators(mf, 3, d)
    eta3 = wedge(wedge(mf.eta, mf.eta), mf.eta)

    def rank_of(vecs):
        return len(vecs) - nullity(vecs)

    def cls(s, c):
        return eadd(escale(s % P, mf.gamma), escale(c % P, mf.ell))

    B = 7
    seen, res = set(), Counter()
    for s1, s2, c1, c2 in product(range(-B, B + 1), repeat=4):
        s3, c3 = -s1 - s2, -c1 - c2
        if abs(s3) > B or abs(c3) > B:
            continue
        lams = [(s1, c1), (s2, c2), (s3, c3)]
        if (0, 0) in lams or len({*lams, *[(-a, -b) for a, b in lams]}) < 6:
            continue
        s, c = (s1, s2, s3), (c1, c2, c3)
        if sum(a * b * b for a, b in zip(s, c)) != -d * sum(x ** 3 for x in s):
            continue
        if sum(x ** 3 for x in c) != -d * sum(a * a * b for a, b in zip(s, c)):
            continue
        key = frozenset(lams)
        if key in seen:
            continue
        seen.add(key)
        cl = [cls(a, b) for a, b in lams]
        tot = {}
        for x in cl:
            tot = eadd(tot, eadd(mf.expcl(x), escale(P - 1, mf.expcl(escale(P - 1, x)))))
        ch3, ch5 = deg_part(tot, 6), deg_part(tot, 10)
        if not ch3 or ch5:
            continue
        if rank_of([eta3, w1, w2, ch3]) != 3 or rank_of([eta3, ch3]) != 2:
            continue
        r, cc = S.injectivity(mf, cl + [escale(P - 1, x) for x in cl])
        res[(r, cc)] += 1
    total = sum(res.values())
    ok = total >= 10 and set(res) == {(75, 90)}
    check("every Weil configuration in the box has rank exactly 75 of 90",
          ok, "configurations with Weil ch_3 and ch_5 = 0: %d, rank distribution %s"
          % (total, dict(res)))


def main():
    print("the annihilator of the Weil line and the rank-zero obstruction")
    part_a()
    part_b()
    part_c()
    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
