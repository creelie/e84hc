"""Block patterns of cor:patterns and the homomorphism nu_R of lem:nusqrt.

For each row (m, D, alpha, columns) of the table of cor:patterns, checks that
alpha has entries in [1, m) adding up to 2m, and conditions (P1)-(P3) of
def:blockpattern: every column sum sum_l delta_l e_kl equals D, every column
has a positive and a zero entry and a weight e_l . alpha divisible by m, and
sum_l delta_l > D.  Then, for M = 33 and 39, lists the elements of square 1,
checks that O_M is balanced with nu_R(O_M) = 1, and that nu_R vanishes on
pairs and on the standard characters.  Prints one line per row and per level;
exits with status 1 if a check fails.
"""
import sys
from math import gcd

ROWS = [
    (114, 3, (51, 21, 86, 14, 56),
     [((0, 0, 1, 2, 0), 1), ((0, 0, 2, 0, 1), 1), ((1, 3, 0, 0, 0), 1), ((2, 0, 0, 1, 2), 1)]),
    (114, 24, (1, 25, 43, 57, 102),
     [((3, 1, 2, 0, 0), 7), ((0, 1, 5, 0, 1), 2), ((0, 0, 0, 2, 0), 12), ((1, 5, 0, 0, 1), 3),
      ((0, 0, 0, 0, 19), 1)]),
    (44, 11, (1, 5, 8, 33, 41),
     [((3, 0, 0, 0, 1), 1), ((0, 0, 11, 0, 0), 1), ((1, 1, 0, 0, 2), 5), ((1, 2, 0, 1, 0), 3),
      ((0, 0, 0, 4, 0), 2)]),
    (52, 14, (1, 5, 16, 37, 45),
     [((0, 0, 0, 3, 1), 4), ((0, 1, 1, 0, 3), 1), ((2, 1, 0, 0, 1), 7), ((0, 0, 13, 0, 0), 1),
      ((0, 3, 0, 1, 0), 2)]),
    (52, 5, (1, 6, 14, 34, 49),
     [((0, 0, 5, 1, 0), 1), ((3, 0, 0, 0, 1), 1), ((2, 0, 0, 3, 0), 1), ((0, 3, 0, 1, 0), 1),
      ((0, 1, 0, 0, 2), 2)]),
    (102, 6, (1, 34, 44, 56, 69),
     [((0, 0, 0, 3, 2), 1), ((0, 0, 3, 0, 4), 1), ((0, 3, 0, 0, 0), 2), ((2, 0, 1, 1, 0), 3)]),
    (102, 18, (5, 35, 51, 96, 17),
     [((0, 0, 0, 0, 6), 2), ((0, 0, 0, 17, 0), 1), ((0, 0, 2, 0, 0), 9), ((0, 6, 0, 1, 0), 1),
      ((3, 2, 0, 0, 1), 6)]),
]

LEVELS = [(33, (3, 11), (1, 4, 16, 22, 25, 31)), (39, (3, 13), (1, 7, 16, 22, 34, 37))]

ok = True


def fail(msg):
    global ok
    ok = False
    print("FAIL " + msg)


def j(v):
    return ",".join(str(x) for x in v)


for m, D, a, cols in ROWS:
    if not (len(a) == 5 and all(0 < x < m for x in a) and sum(a) == 2 * m):
        fail("character %s at level %d" % (j(a), m))
    sums = [sum(e[k] * d for e, d in cols) for k in range(5)]
    if sums != [D] * 5:
        fail("(P1) for %s: column sums %s" % (j(a), j(sums)))
    weights = []
    for e, d in cols:
        w = sum(x * y for x, y in zip(a, e))
        weights.append(w)
        if not (d > 0 and any(x > 0 for x in e) and any(x == 0 for x in e) and w % m == 0):
            fail("(P2) for %s, column %s" % (j(a), j(e)))
    degs = sum(d for _, d in cols)
    if not degs > D:
        fail("(P3) for %s" % j(a))
    print("m=%d alpha=(%s) D=%d degrees=%d weights=%s" % (m, j(a), D, degs, j(weights)))

for M, primes, O in LEVELS:
    roots = [y for y in range(M) if y * y % M == 1]

    def nu(v):
        return sum(1 for y in v if y * y % M == 1) % 2

    for t in range(1, M):
        if gcd(t, M) == 1 and sum(t * x % M for x in O) != 3 * M:
            fail("O_%d is not balanced at t=%d" % (M, t))
    if nu(O) != 1:
        fail("nu_R(O_%d) = 0" % M)
    for y in range(1, M):
        if nu((y, M - y)) != 0:
            fail("nu_R on the pair (%d,%d)" % (y, M - y))
    nstd = 0
    for p in primes:
        d = M // p
        for i in range(1, d):
            s = [i + k * d for k in range(p)] + [(-p * i) % M]
            nstd += 1
            if nu(s) != 0:
                fail("nu_R on sigma_{%d,%d}" % (p, i))
    print("M=%d roots=%s O=(%s) in_O=%s nu_R(O)=%d standard=%d pairs=%d"
          % (M, j(roots), j(O), j([y for y in O if y in roots]), nu(O), nstd, M - 1))

if not ok:
    sys.exit(1)
print("7 block patterns and nu_R at levels 33, 39: all checks passed")
