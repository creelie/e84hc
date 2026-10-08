"""Item (LXIX): the secant plane and the lattice of line bundles.

Classes in Q[Theta]/(Theta^5) are written as sum_k c_k Theta^k/k!, so that
e^{j Theta} has coordinates (1, j, j^2, j^3, j^4).  The lattice L_Theta is the
Z-span of these.  Binomial moments m_k are defined by
    c_i = sum_k S(i,k) k! m_k
(S = Stirling numbers of the second kind); a class lies in L_Theta iff all
m_k are integers (Lemma [Binomial moments]).  The secant class
a u_Theta + b v_Theta has coordinates (a, b, -ad, -bd, a d^2).

Every call of check() below is one check and prints one [PASS] or [FAIL]
line, which verify_all.py counts.  Exact rational arithmetic throughout.

Paper: Lemma [Binomial moments] (lem:binomialmoments), Theorem [The secant
plane and the lattice of line bundles] (thm:lattice), Corollary [Split
resolutions, for every rank and every twist] (cor:latticeburch), Remark [What
the congruence measures] (rem:latticedefect) and Lemma [The injectivity
condition for a smooth support] (lem:smoothinjective).
"""
import sys
from fractions import Fraction as Fr
from math import lcm

PASS, FAIL = [], []
def check(cond, msg=""):
    ok = bool(cond)
    (PASS if ok else FAIL).append(msg)
    print(("  [PASS] " if ok else "  [FAIL] ") + str(msg))

# Stirling numbers of the second kind S(i,k) for i,k <= 4
S = {(0, 0): 1, (1, 1): 1, (2, 1): 1, (2, 2): 1, (3, 1): 1, (3, 2): 3, (3, 3): 1,
     (4, 1): 1, (4, 2): 7, (4, 3): 6, (4, 4): 1}
FACT = [1, 1, 2, 6, 24]

def moments(c):
    """Solve c_i = sum_k S(i,k) k! m_k for m (unitriangular system)."""
    m = [Fr(0)] * 5
    for i in range(5):
        rest = sum(S.get((i, k), 0) * FACT[k] * m[k] for k in range(i))
        m[i] = Fr(c[i] - rest, S.get((i, i), 1) * FACT[i])
    return m

def secant(a, b, d):
    return [Fr(a), Fr(b), Fr(-a * d), Fr(-b * d), Fr(a * d * d)]

def formula(a, b, d):
    return [Fr(a), Fr(b), Fr(-a * d - b, 2), Fr(3 * a * d + 2 * b - b * d, 6),
            Fr(a * d * d - 11 * a * d + 6 * b * d - 6 * b, 24)]

def integral(m):
    return all(x.denominator == 1 for x in m)

# (1) closed formula against the solved system
for a in (1, 2):
    for b in (1, 3):
        for d in range(1, 49):
            check(moments(secant(a, b, d)) == formula(a, b, d),
                  "moments of a u + b v at (a,b,d) = %s" % ((a, b, d),))

# (2) b=3, a=1: in the lattice iff d = 15, 23 (mod 24), for d < 400
for d in range(1, 400):
    check(integral(moments(secant(1, 3, d))) == (d % 24 in (15, 23)),
          "u + 3v in L_Theta iff d = 15, 23 mod 24, d = %d" % d)

# (3) second decision of lattice membership, for d < 60, by solving against
#     the unimodular basis e^{j Theta}, j = 0..4 (Vandermonde rows (1,j,..,j^4))
def solve_vandermonde(t):
    # rows v_j = (j^0, ..., j^4); find x with sum_j x_j v_j = t, by Gaussian
    # elimination over Q on the transposed system
    n = 5
    A = [[Fr(j) ** i for j in range(n)] + [Fr(t[i])] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        A[col] = [x / A[col][col] for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
    return [A[i][n] for i in range(n)]

for d in range(1, 60):
    x = solve_vandermonde(secant(1, 3, d))
    check(all(v.denominator == 1 for v in x) == (d % 24 in (15, 23)),
          "Vandermonde decision agrees, d = %d" % d)

# (4) the witness of Theorem [Secant sheaves exist in every dimension] at
#     d = 3, (a,b) = (1,1): 6(u+v) = -23 e^0 + 66 e^1 - 54 e^2 + 20 e^3 - 3 e^4
w = [-23, 66, -54, 20, -3]
tot = [sum(w[j] * Fr(j) ** i for j in range(5)) for i in range(5)]
check(tot == [6 * x for x in secant(1, 1, 3)],
      "witness 6(u+v) = -23 + 66 e - 54 e^2 + 20 e^3 - 3 e^4 at d = 3")
check(lcm(*[x.denominator for x in moments(secant(1, 1, 3))]) == 6,
      "6 is the least common denominator of the moments of u + v at d = 3")

# (5) the four smooth discriminants: the defect of m_4, Markman's
#     normalisation count, and the moments of O_S
for d in (1, 3, 5, 7):
    m4 = moments(secant(1, 3, d))[4]
    check(m4 == Fr((d + 9) * (d - 2), 24), "defect of m_4 at d = %d" % d)
    check((3 * (d + 9) * (d - 1)) % 24 == 0, "24 | 3(d+9)(d-1) at d = %d" % d)
for N in (5, 6, 7, 8):
    chi = 4 * N * (18 - N)
    mS = moments([Fr(0), Fr(0), Fr(2 * N), Fr(-12 * N), Fr(chi)])
    check(mS[:4] == [0, 0, N, -3 * N] and mS[4] == Fr(N * (83 - 2 * N), 12),
          "moments of O_S at N = %d" % N)
    check(mS[4].denominator > 1, "m_4(O_S) is not integral at N = %d" % N)

# (6) e(S) != [S]^2 at b = 3 for 1 <= N <= 40 (Lemma [injectivity for a smooth support])
for N in range(1, 41):
    check(12 * N * (36 - 3 * N) != 24 * N * N, "e(S) != [S]^2 at b = 3, N = %d" % N)

print("item (LXIX): passed %d, failed %d" % (len(PASS), len(FAIL)))
sys.exit(0 if not FAIL else 1)
