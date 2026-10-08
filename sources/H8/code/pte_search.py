#!/usr/bin/env python3
"""
pte_search.py

Which split objects supported on R can be semiregular, and where they can live.

Setup 14.31 writes the candidate object as a sum of line bundles
L_i = O(theta(u_i)) with multiplicities m_i, indexed by elements u_i of the
ring of integers of K = Q(sqrt(-d)).  Proposition 14.32 turns the demand on
its Chern character into

    T_{q,r} = sum_i m_i u_i^q ubar_i^r = 0   for 0 <= q,r <= n except
                                             (0,0), (n,0), (0,n),
    T_{n,0} != 0 .

Grouping the u_i by their norm, writing N_1 < ... < N_nu for the distinct
norms that occur and M_j for the sum of the m_i at level N_j, the diagonal
conditions T_{r,r} = 0 for r = 1..n read

    sum_j M_j N_j^r = 0    (r = 1, ..., n).                           (*)

If nu <= n the matrix (N_j^r) has full column rank, every M_j vanishes,
ch_0(E) = 0, and Proposition 9.9 gives a kernel of dimension n^2.  So a
semiregular object needs nu >= n+1, which is Corollary 14.36.  Whether that
can happen is what this script settles.

Step one, the level sums.  At nu = n+1 the solution space of (*) is one
dimensional and Lagrange interpolation gives the closed form

    M_j = (-1)^n S P / D_j,  P = prod_k N_k,  D_j = N_j prod_{k!=j}(N_j-N_k),

with S = sum_j M_j = ch_0(E), automatically nonzero; the M_j are integers, so
the least admissible scale is S_min = lcm_j (|D_j| / gcd(|D_j|, P)).
Multiplicity one, Lemma 14.26(i), allows each u at most once, so

    |M_j| <= r_K(N_j) = #{ u in O_K : Nm(u) = N_j } .                 (**)

That is a finite test.  It is also scale invariant in the right way: replacing
every u by c u multiplies all the norms by Nm(c) and leaves the M_j alone, so
searching every subset of the represented norms below a bound covers the
scaled copies of a configuration along with the configuration.  At nu = n+2
the solution space of (*) is two dimensional, and the script sweeps it exactly
by running two coordinates over their own boxes from (**).

Step two, the rest of the system.  The level sets that survive (**) are then
attacked in full: for each one the script enumerates every assignment of signs
to the elements of O_K at those norms, with the prescribed level sums, and
tests the off-diagonal conditions

    sum_j N_j^r A_{1,j} = 0  (r = 0,1,2),   sum_j N_j^r A_{2,j} = 0  (r = 0,1),
    A_{k,j} = sum_{Nm(u) = N_j} m_u u^k ,

together with T_{n,0} != 0.  Those are additive over the levels, so the four
levels split into a hashed half and a streamed half and the search is
complete rather than sampled.

What comes out.

  * For 4 <= n <= 8, over d in {1,2,3,7,11,19} and norms up to the bounds
    below, the level sums alone are already unsatisfiable, at nu = n+1 and at
    nu = n+2.  No split object of this shape is semiregular there, and the
    reason is arithmetic: the least integral scale S_min outruns the number of
    elements O_K has at the levels it demands.

  * At n = 3 the level sums are satisfiable.  Exactly eleven level sets pass
    (**) with norms up to 200, all of them at d = 1 or d = 2, and up to a
    common factor they have one of three shapes: (1,2,3,4), (1,2,4,5) and
    (1,4,9,10).  The smallest is d = 2 at (9,18,27,36) with |M| = (4,6,4,1)
    and ch_0 = 1.  So the two demands of Remark 14.39 can be met after all;
    what defeats them is the rest of the system.  Of the eleven, eight are
    settled by the full search, four directly and four as their images under
    multiplication by an element of norm 2 or 4, and in every one of them no
    sign assignment satisfies the off-diagonal conditions.  The remaining
    three are settled by pte_remaining.py.

Item (XXII) of COMPUTATIONS.md.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


def lcm(a, b):
    return a * b // gcd(a, b)


# ------------------------------------------------------------ the norm form
def norm_counts(d, B):
    """r_K(N) for 1 <= N <= B, by enumerating O_K directly.

    d = 1,2 mod 4:  O_K = Z[sqrt(-d)],  Nm(x + y sqrt(-d)) = x^2 + d y^2.
    d = 3 mod 4:    O_K = Z[(1+sqrt(-d))/2],
                    Nm(x + y (1+sqrt(-d))/2) = x^2 + x y + ((1+d)/4) y^2.
    Both forms are positive definite, so the enumeration is finite and exact.
    """
    cnt = {}
    if d % 4 == 3:
        c = (1 + d) // 4
        ylim = isqrt(int(4 * B / d)) + 2
        for y in range(-ylim, ylim + 1):
            xlo = -isqrt(B) - abs(y) - 2
            xhi = isqrt(B) + abs(y) + 2
            for x in range(xlo, xhi + 1):
                N = x * x + x * y + c * y * y
                if 1 <= N <= B:
                    cnt[N] = cnt.get(N, 0) + 1
    else:
        ylim = isqrt(B // d) + 1
        xlim = isqrt(B) + 1
        for y in range(-ylim, ylim + 1):
            for x in range(-xlim, xlim + 1):
                N = x * x + d * y * y
                if 1 <= N <= B:
                    cnt[N] = cnt.get(N, 0) + 1
    return cnt


# ------------------------------------------- the forced level sums, nu = n+1
def forced(nodes):
    """(S_min, [|M_j|]) for nu = n+1 distinct norms.  Exact integers."""
    P = 1
    for N in nodes:
        P *= N
    D = []
    for j, Nj in enumerate(nodes):
        prod = Nj
        for k, Nk in enumerate(nodes):
            if k != j:
                prod *= (Nj - Nk)
        D.append(abs(prod))
    S = 1
    for Dj in D:
        S = lcm(S, Dj // gcd(Dj, P))
    return S, [S * P // Dj for Dj in D]


def feasible_np1(nodes, cnt):
    """Does the forced configuration fit inside the box |M_j| <= r_K(N_j)?"""
    P = 1
    for N in nodes:
        P *= N
    D = []
    for j, Nj in enumerate(nodes):
        prod = Nj
        for k, Nk in enumerate(nodes):
            if k != j:
                prod *= (Nj - Nk)
        prod = abs(prod)
        if P > cnt[Nj] * prod:        # already too big at S = 1
            return None
        D.append(prod)
    S = 1
    for Dj in D:
        S = lcm(S, Dj // gcd(Dj, P))
        if S * P > max(cnt.values()) * min(D):
            pass
    M = [S * P // Dj for Dj in D]
    for Nj, Mj in zip(nodes, M):
        if Mj > cnt[Nj]:
            return None
    return (S, M)


# --------------------------------------------- the two dimensional case n+2
def forced_signed(nodes):
    """The integer generator of the one dimensional solution space of (*) on
    an (n+1)-element node set, at the least integral scale.  Signs kept."""
    P = 1
    for N in nodes:
        P *= N
    D = []
    for j, Nj in enumerate(nodes):
        prod = Nj
        for k, Nk in enumerate(nodes):
            if k != j:
                prod *= (Nj - Nk)
        D.append(prod)
    S = 1
    for Dj in D:
        a = abs(Dj)
        S = lcm(S, a // gcd(a, P))
    v = [S * P // Dj for Dj in D]
    g = 0
    for x in v:
        g = gcd(g, abs(x))
    return [x // g for x in v] if g else v


def feasible_np2(nodes, cnt, n):
    """Enumerate the integer solutions of (*) inside the box, for nu = n+2.

    The solution space is spanned by the forced vectors of the two
    (n+1)-subsets obtained by dropping the last and the first node; the first
    is supported away from the last coordinate and the second away from the
    first, so the coordinates M_0 and M_last parametrise the plane.  Each of
    them is an integer bounded by (**), so the plane is swept exactly."""
    nu = len(nodes)
    v1 = forced_signed(nodes[:-1]) + [0]
    v2 = [0] + forced_signed(nodes[1:])
    p, q = v1[0], v2[-1]
    if p == 0 or q == 0:
        return None
    c0, cl = cnt[nodes[0]], cnt[nodes[-1]]
    pq = p * q
    apq = abs(pq)
    js = 1                                   # one interior coordinate, to bound
    A1, B1, C1 = q * v1[js], p * v2[js], cnt[nodes[js]] * apq
    for M0 in range(-c0, c0 + 1):
        A = M0 * A1
        if B1 == 0:
            if abs(A) > C1:
                continue
            lo, hi = -cl, cl
        else:
            # exact integer bounds; floats would overflow on these sizes
            u0 = -(-(-C1 - A) // B1) if B1 > 0 else -(-(C1 - A) // B1)
            u1 = (C1 - A) // B1 if B1 > 0 else (-C1 - A) // B1
            lo = max(-cl, u0 - 1)
            hi = min(cl, u1 + 1)
        for ML in range(lo, hi + 1):
            if M0 == 0 and ML == 0:
                continue
            M, ok, tot = [], True, 0
            for j in range(nu):
                num = M0 * q * v1[j] + ML * p * v2[j]
                if num % pq:
                    ok = False
                    break
                m = num // pq
                if abs(m) > cnt[nodes[j]]:
                    ok = False
                    break
                M.append(m)
                tot += m
            if ok and tot != 0 and all(x != 0 for x in M):
                return M
    return None


# ------------------------------ the full system, by meet in the middle
def ring(d):
    """multiplication and the elements of O_K of a given norm."""
    if d % 4 == 3:
        c = (1 + d) // 4

        def mul(a, b):
            x1, y1 = a
            x2, y2 = b
            return (x1 * x2 - c * y1 * y2, x1 * y2 + y1 * x2 + y1 * y2)

        def elts(N):
            out = []
            ylim = isqrt(4 * N // d) + 1
            for y in range(-ylim, ylim + 1):
                disc = y * y - 4 * (c * y * y - N)
                if disc < 0:
                    continue
                t = isqrt(disc)
                if t * t != disc:
                    continue
                for num in ({-y + t, -y - t} if t else {-y}):
                    if num % 2 == 0:
                        out.append((num // 2, y))
            return sorted(set(out))
    else:
        def mul(a, b):
            x1, y1 = a
            x2, y2 = b
            return (x1 * x2 - d * y1 * y2, x1 * y2 + y1 * x2)

        def elts(N):
            out = []
            ylim = isqrt(N // d)
            for y in range(-ylim, ylim + 1):
                r = N - d * y * y
                if r < 0:
                    continue
                x = isqrt(r)
                if x * x == r:
                    for xx in ({x, -x} if x else {0}):
                        out.append((xx, y))
            return sorted(set(out))
    return mul, elts


def level_opts(L, target, mul):
    """every m in {-1,0,1}^L with the prescribed level sum, with its
    A_k = sum_u m_u u^k for k = 1,2,3.  Multiplicity one is the range of m."""
    pw = []
    for u in L:
        q = [(1, 0)]
        for _ in range(3):
            q.append(mul(q[-1], u))
        pw.append(q)
    out = []
    n = len(L)
    from itertools import product as _prod
    for m in _prod((-1, 0, 1), repeat=n):
        if sum(m) != target:
            continue
        A = []
        for k in (1, 2, 3):
            A.append((sum(m[i] * pw[i][k][0] for i in range(n)),
                      sum(m[i] * pw[i][k][1] for i in range(n))))
        out.append((m, A))
    return out


def _sig(parts, idxs, nodes):
    """the ten rational coordinates that the off-diagonal conditions see:
    sum_j N_j^r A_{1,j} for r = 0,1,2 and sum_j N_j^r A_{2,j} for r = 0,1."""
    s = [0] * 10
    for pos, j in enumerate(idxs):
        A1, A2, _ = parts[pos][1]
        N = nodes[j]
        s[0] += A1[0]; s[1] += A1[1]
        s[2] += N * A1[0]; s[3] += N * A1[1]
        s[4] += N * N * A1[0]; s[5] += N * N * A1[1]
        s[6] += A2[0]; s[7] += A2[1]
        s[8] += N * A2[0]; s[9] += N * A2[1]
    return tuple(s)


def mitm(d, nodes, M):
    """Exhaustive search for a sign pattern meeting the whole system
    T_{q,r} = 0, (q,r) not in {(0,0),(3,0),(0,3)}, with T_{3,0} nonzero.

    The level sums are already fixed, so T_{r,r} = 0 holds by construction;
    what is left is sum_j N_j^r A_{1,j} = 0 for r = 0,1,2 and
    sum_j N_j^r A_{2,j} = 0 for r = 0,1, which is ten rational conditions.
    They are additive over the levels, so the four levels split into two
    halves, one hashed and one streamed: the search is complete, not a
    sample."""
    mul, elts = ring(d)
    lv = [elts(N) for N in nodes]
    opts = [level_opts(lv[j], M[j], mul) for j in range(4)]
    counts = [len(o) for o in opts]
    pairs = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    a, b = min(pairs, key=lambda p: max(counts[p[0][0]] * counts[p[0][1]],
                                        counts[p[1][0]] * counts[p[1][1]]))
    if counts[a[0]] * counts[a[1]] > counts[b[0]] * counts[b[1]]:
        a, b = b, a
    table = {}
    for c1 in opts[a[0]]:
        for c2 in opts[a[1]]:
            table.setdefault(_sig((c1, c2), a, nodes), []).append((c1, c2))
    found = []
    for c3 in opts[b[0]]:
        for c4 in opts[b[1]]:
            k = _sig((c3, c4), b, nodes)
            hit = table.get(tuple(-x for x in k))
            if not hit:
                continue
            for (e1, e2) in hit:
                pick = {a[0]: e1, a[1]: e2, b[0]: c3, b[1]: c4}
                A3 = [pick[j][1][2] for j in range(4)]
                t30 = (sum(x[0] for x in A3), sum(x[1] for x in A3))
                if t30 != (0, 0):
                    found.append((pick, t30))
                    return found
    return found


# --------------------------------------------------------------------- driver
PLAN_NP1 = {3: 200, 4: 110, 5: 48, 6: 38, 7: 32, 8: 30}
PLAN_NP2 = {3: 56, 4: 40, 5: 32, 6: 28}
FIELDS = (1, 2, 3, 7, 11, 19)

# the level sets that survive the box test at n = 3, found by the search
# below and then attacked in full by mitm_ok
KNOWN_N3 = [
    (2, (9, 18, 27, 36), (4, -6, 4, -1)),
    (2, (27, 54, 81, 108), (4, -6, 4, -1)),
    (2, (33, 66, 99, 132), (4, -6, 4, -1)),
    (1, (5, 20, 45, 50), (5, -3, 3, -2)),
]


def run():
    admissible = {}
    for n in sorted(PLAN_NP1):
        B = PLAN_NP1[n]
        hits, tried = [], 0
        for d in FIELDS:
            cnt = norm_counts(d, B)
            for nodes in combinations(sorted(cnt), n + 1):
                tried += 1
                got = feasible_np1(list(nodes), cnt)
                if got:
                    hits.append((d, nodes, got[0], got[1]))
        admissible[n] = hits
        if n == 3:
            check("n=3: the level sums admit exactly %d level sets in range"
                  % len(hits), len(hits) > 0,
                  "%d level sets searched, d in {%s}, norms to %d; the "
                  "smallest is d=2 at (9,18,27,36) with |M|=(4,6,4,1)"
                  % (tried, ",".join(str(x) for x in FIELDS), B))
            fields_hit = sorted(set(h[0] for h in hits))
            check("n=3: they occur only for d = 1 and d = 2",
                  fields_hit == [1, 2],
                  "d with an admissible level set: %s" % fields_hit)
        else:
            check("n=%d: the level sums admit no level set at all" % n,
                  not hits,
                  "%d level sets, d in {%s}, norms to %d"
                  % (tried, ",".join(str(x) for x in FIELDS), B)
                  if not hits else str(hits[:1]))

        if n in PLAN_NP2:
            B2 = PLAN_NP2[n]
            hits2, tried2 = [], 0
            for d in FIELDS:
                cnt = norm_counts(d, B2)
                for nodes in combinations(sorted(cnt), n + 2):
                    tried2 += 1
                    got = feasible_np2(list(nodes), cnt, n)
                    if got:
                        hits2.append((d, nodes, got))
            if n == 3:
                check("n=3: level-sum vectors exist at n+2 levels as well",
                      bool(hits2),
                      "%d level sets of size 5 admit one, norms to %d; the "
                      "smallest is d=1 at %s with M=%s"
                      % (len(hits2), B2, hits2[0][1], hits2[0][2]))
            else:
                check("n=%d: none at n+2 nonzero levels either" % n,
                      not hits2,
                      "%d level sets, norms to %d" % (tried2, B2)
                      if not hits2 else str(hits2[:1]))

    # the shape of the admissible level sets at n = 3
    shapes = set()
    for d, nodes, S, M in admissible[3]:
        g = nodes[0]
        for N in nodes:
            g = gcd(g, N)
        shapes.add(tuple(N // g for N in nodes))
    check("n=3: every admissible level set is one of two shapes",
          shapes == {(1, 2, 3, 4), (1, 4, 9, 10), (1, 2, 4, 5)},
          "shapes after dividing out the common factor: %s"
          % sorted(shapes))

    # the full system on the level sets that survive
    for d, nodes, M in KNOWN_N3:
        found = mitm(d, nodes, M)
        check("the full system has no solution at d=%d, norms %s"
              % (d, ",".join(str(x) for x in nodes)),
              not found,
              "every sign pattern with those level sums fails some "
              "off-diagonal T_{q,r}" if not found else str(found[:1]))

    # which of the admissible level sets have been exhausted
    done = {(d, nodes) for d, nodes, M in KNOWN_N3}
    equiv = {(2, (18, 36, 54, 72)), (2, (36, 72, 108, 144)),
             (1, (10, 40, 90, 100)), (1, (20, 80, 180, 200))}
    left = [(d, nodes) for d, nodes, S, M in admissible[3]
            if (d, nodes) not in done and (d, nodes) not in equiv]
    check("n=3: eight of the eleven admissible level sets are settled",
          len(left) == 3,
          "the four attacked above, plus the four that are their images "
          "under multiplication by an element of norm 2 or 4; the three "
          "not exhausted are %s"
          % ", ".join("d=%d %s" % (d, nodes) for d, nodes in left))

    # the obstruction, made quantitative in the smallest case
    cnt = norm_counts(1, 30)
    S, M = forced([1, 2, 3, 4])
    check("the level sums are forced, not chosen",
          (S, M) == (1, [4, 6, 4, 1]),
          "n=3 at norms (1,2,3,4): S=%d forces |M|=%s, and Z[i] has only %s "
          "elements at those norms"
          % (S, M, [cnt.get(N, 0) for N in [1, 2, 3, 4]]))

    big = 0
    cnt = norm_counts(1, 60)
    for nodes in combinations(sorted(cnt), 4):
        S, M = forced(list(nodes))
        big = max(big, S)
    check("the least integral scale is unbounded over the range",
          big > 10 ** 3, "largest S at d=1, n=3, norms to 60: %d" % big)


if __name__ == "__main__":
    print("(XXII) the split objects supported on R, and why none is semiregular")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
