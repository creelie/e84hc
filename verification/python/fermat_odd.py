"""Hodge characters of Fermat fourfolds of odd degree divisible by 3.

For every odd m divisible by 3 with 3 <= m <= M (M from the command line,
default 45) list, by exhaustive search, the balanced sextuples: multisets of
six nonzero residues mod m whose representatives in [0, m) add up to 3m after
multiplication by every unit t.  These are the Hodge characters of the Fermat
fourfold of degree m.  For each one that contains no pair a, -a and generates
Z/m, look for a direct or a lowering move (Definition "def:move" of the
paper); if there is none, check that tA is one of the three exceptional sets
O21, O33, O39 for some unit t (Theorem "thm:moves").  Then check the
identities of Lemma "lem:exceptional" and that the exceptional sets have no
move.

The output is line for line the same as that of c/fermat_odd.c and
julia/fermat_odd.jl.
"""

import sys
from math import gcd

EXCEPTIONAL = {21: [1, 4, 9, 15, 16, 18], 33: [1, 4, 16, 22, 25, 31],
               39: [1, 7, 16, 22, 34, 37]}


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


def balanced(a, m):
    h = len(a) * m // 2
    return sum(a) % m == 0 and all(sum(t * x % m for x in a) == h for t in units(m))


def has_pair(a, m):
    return any((a[i] + a[k]) % m == 0 for i in range(len(a)) for k in range(i + 1, len(a)))


def odd_primes(m):
    return [p for p in range(3, m + 1, 2) if m % p == 0 and all(p % q for q in range(2, p))]


def profile(a, m):
    return sorted((m // gcd(x, m) for x in a), reverse=True)


def move(a, m, want):
    """Return True if a has a move of the kind want ('direct' or 'lowering')."""
    prof = profile(a, m)
    for l in odd_primes(m):
        d = m // l
        for x in range(d):
            if l * x % m == 0:
                continue
            fib = [(x + j * d) % m for j in range(l)]
            s = [y for y in fib if y in a]
            size = 7 + l - 2 * len(s)
            if want == 'direct' and size <= 4:
                return True
            if want == 'lowering' and size == 6:
                b = list(a)
                for y in s:
                    b.remove(y)
                b += [(-y) % m for y in fib if y not in s] + [l * x % m]
                if profile(b, m) < prof:
                    return True
    return False


def exceptional(a, m):
    if m not in EXCEPTIONAL:
        return False
    return any(sorted(t * x % m for x in a) == EXCEPTIONAL[m] for t in units(m))


def generates(a, m):
    g = m
    for x in a:
        g = gcd(g, x)
    return g == 1


def census(M):
    bad = False
    for m in range(3, M + 1, 6):
        s = np = gen = dm = lm = ex = 0
        for a0 in range(1, m):
            for a1 in range(a0, m):
                for a2 in range(a1, m):
                    for a3 in range(a2, m):
                        for a4 in range(a3, m):
                            a5 = 3 * m - a0 - a1 - a2 - a3 - a4
                            if a5 < a4 or a5 >= m:
                                continue
                            a = [a0, a1, a2, a3, a4, a5]
                            if not balanced(a, m):
                                continue
                            s += 1
                            if has_pair(a, m):
                                continue
                            np += 1
                            if not generates(a, m):
                                continue
                            gen += 1
                            if move(a, m, 'direct'):
                                dm += 1
                            elif move(a, m, 'lowering'):
                                lm += 1
                            elif exceptional(a, m):
                                ex += 1
                            else:
                                bad = True
                                print(f"NO MOVE AND NOT EXCEPTIONAL: m={m} {a}")
        print(f"H {m} sextuples {s} without_pair {np} generating {gen} "
              f"direct {dm} lowering {lm} exceptional {ex}")
    return bad


def msum(*parts):
    out = []
    for p in parts:
        out += p
    return sorted(out)


def identities():
    bad = False
    for m, o in EXCEPTIONAL.items():
        ok = balanced(o, m) and not has_pair(o, m) and generates(o, m) \
            and not move(o, m, 'direct') and not move(o, m, 'lowering')
        print(f"O{m} balanced, without pair, generating, no move: {'yes' if ok else 'NO'}")
        bad |= not ok
    # O21 + {2,19} = sigma_{3,2} + Q at level 21
    sig = [2, 9, 16, 15]
    q = [1, 4, 18, 19]
    ok = msum(EXCEPTIONAL[21], [2, 19]) == msum(sig, q) and balanced(sig, 21) \
        and balanced(q, 21)
    print(f"O21 + {{2,19}} = sigma(3,2) + Q, all parts balanced: {'yes' if ok else 'NO'}")
    bad |= not ok
    for m, x1, x2, pairs, q in ((33, 32, 8, [1, 65, 25, 41], [1, 25, 44, 62]),
                                (39, 32, 5, [5, 73, 7, 71], [2, 7, 73, 74])):
        M = 2 * m

        def T(x):
            return [x, (x + m) % M, (-2 * x) % M, m]
        a = [2 * y for y in EXCEPTIONAL[m]]
        ok = msum(a, pairs, [m, m]) == msum(q, T(x1), T(x2)) and balanced(a, M) \
            and balanced(q, M) and balanced(T(x1), M) and balanced(T(x2), M)
        print(f"2*O{m} + pairs + {{{m},{m}}} = Q + T({x1}) + T({x2}) at level {M}, "
              f"all parts balanced: {'yes' if ok else 'NO'}")
        bad |= not ok
    # every 2-standard quadruple T(x) is balanced, for every even level up to 200
    ok = all(balanced([x, (x + M // 2) % M, (-2 * x) % M, M // 2], M)
             for M in range(4, 201, 2) for x in range(1, M) if 2 * x % M)
    print(f"T(x) = {{x, x+M/2, -2x, M/2}} balanced for all even M <= 200: {'yes' if ok else 'NO'}")
    bad |= not ok
    return bad


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 45
    bad = census(M)
    bad |= identities()
    if bad:
        print("FAILURE")
        sys.exit(1)
    print("every generating Hodge sextuple without a pair has a move or is exceptional")


if __name__ == "__main__":
    main()
