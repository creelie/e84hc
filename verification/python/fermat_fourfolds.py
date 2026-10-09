"""Hodge characters of Fermat surfaces and fourfolds of degree prime to 6.

For every m prime to 6 with 5 <= m <= M (M from the command line, default 55)
list, by exhaustive search, the multisets of four and of six nonzero residues
mod m with sum zero whose representatives in [0, m) add up to 2m (four
entries) or 3m (six entries) after multiplication by every unit t.  These are
the Hodge characters of the Fermat surface and fourfold of degree m.  Check
the classification proved in the paper: every such quadruple contains a pair
a, -a, and every such sextuple contains a pair or is 5-standard,
{x, x + m/5, ..., x + 4m/5, -5x}.

The output is line for line the same as that of c/fermat_fourfolds.c and
julia/fermat_fourfolds.jl.
"""

import sys
from math import gcd


def balanced(a, m, units, h):
    return all(sum(t * x % m for x in a) == h for t in units)


def has_pair(a, m):
    return any((a[i] + a[k]) % m == 0 for i in range(len(a)) for k in range(i + 1, len(a)))


def standard5(a, m):
    if m % 5:
        return False
    for i in range(6):
        r = a[:i] + a[i + 1:]
        if len(set(r)) == 5 and all((5 * y - 5 * r[0]) % m == 0 for y in r) \
                and (a[i] + 5 * r[0]) % m == 0:
            return True
    return False


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 55
    bad = False
    for m in range(5, M + 1):
        if m % 2 == 0 or m % 3 == 0:
            continue
        units = [t for t in range(1, m) if gcd(t, m) == 1]
        q = qn = s = sn = ss = 0
        for a0 in range(1, m):
            for a1 in range(a0, m):
                for a2 in range(a1, m):
                    a3 = (3 * m - a0 - a1 - a2) % m
                    if a3 >= a2 and a0 + a1 + a2 + a3 == 2 * m:
                        a = [a0, a1, a2, a3]
                        if balanced(a, m, units, 2 * m):
                            q += 1
                            if not has_pair(a, m):
                                qn += 1
                                bad = True
                    for a3 in range(a2, m):
                        for a4 in range(a3, m):
                            t5 = a0 + a1 + a2 + a3 + a4
                            a5 = (5 * m - t5) % m
                            if a5 < a4 or t5 + a5 != 3 * m:
                                continue
                            a = [a0, a1, a2, a3, a4, a5]
                            if not balanced(a, m, units, 3 * m):
                                continue
                            s += 1
                            if not has_pair(a, m):
                                sn += 1
                                if standard5(a, m):
                                    ss += 1
                                else:
                                    bad = True
        print(f"H {m} quadruples {q} without_pair {qn} sextuples {s} without_pair {sn} 5-standard {ss}")
    if bad:
        print("COUNTEREXAMPLE FOUND")
        sys.exit(1)
    print("all Hodge quadruples have a pair; all Hodge sextuples have a pair or are 5-standard")


if __name__ == "__main__":
    main()
