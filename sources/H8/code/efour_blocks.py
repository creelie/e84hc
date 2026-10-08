"""Item (LXXVII): groups that no product touches on E_0^8, and the shift
arrangements within five consecutive values.

Setting of items (LXXI) and (LXXIV) at n = 4: A = B_1 x ... x B_4,
B_j = E_0 x E_0, E_0 = C/Z[i]; the 128 pieces L_zeta, zeta in mu_4^4 with
prod zeta = +-1, external products of line bundles on the B_j; the
multiples M_1, M_2, M_3 with forms t_i Id, |t_i - p| >= 2; shifts with
(-1)^d = prod zeta for L_zeta.  A morphism of degree one from P_a to P_b of
Ext degree q has d_b = d_a + 1 - q.  A ratio of two pieces is written
additively, r in (Z/4)^4 with zeta'_j = i^(r_j) zeta_j; its sum is even, and
it changes the parity exactly when the sum is 2 mod 4.

Paper: Section "Convolutions of line bundles" (ssec:convolutions):
lem:efourspread, lem:cayleycut, thm:efourspreadtwo, thm:efourspreadthree,
prop:efourgap, cor:efourfive, prop:efourcupkernel, rem:convolutionsopen.

  (A) the counts: the 13 ratios of one parity with every coordinate moved
      and one of them by -1 have D = 256 once and 64 twelve times, 1024 in
      all; the 8 others with every coordinate moved have D = 16; between a
      piece and the pieces of the other parity, the groups H^5 have
      dimensions 4 * 60, 12 * 16 and 4 * (64 + 6 * 16), 1072 in all, and
      64 * 1072 - 128 * 8 = 67584; at spread five the groups H^7 have
      64 * 16 = 1024 classes, no more than the loops;
  (B) every term with leaves between pieces L_zeta that the degrees on the
      four surfaces and the degree drop of lem:degreedrop allow, enumerated
      over the ratios: at spread two the 13 groups H^4 are reached by
      nothing and left by nothing, while the 8 others are reached and left;
      at spread three nothing leaves any group; at spread one every term
      leaving a group H^3 of three moved coordinates has chains of total
      drop one or two;
  (C) the runs through the multiples: for a group of spread 1, 2 or 3 the
      output degree 3 + delta + X - U + 7D of a term through a run is
      never a degree of the target, in all four placements and for every
      drop X >= 0 of the parts between pieces L_zeta;
  (D) the cut: in the Cayley graph of the 64 ratios of one parity with the
      13 generators and weights D, every subgroup H has
      |H| * w(S - H) >= 1024, with equality only for H = 0; the least
      weighted cut is 1024, at one vertex (Stoer-Wagner), and the least
      number of edges in a cut is 13;
  (E) arrangements: for 40 random splits of one parity between two values
      two apart, or three with the middle one occupied, the groups H^4 of
      the 13 ratios weigh at least 1024; piece by piece, with the degrees of
      item (LXXIV) and the shifts of the multiples free, the spread-three
      arrangement in two placements (2816 groups, 68608 classes, left by no
      term, reached only through the loops at their two pieces) and four
      gap arrangements of prop:efourgap (every group H^3 beside the gap
      reached by nothing and left by nothing);
  (F) the shift arrangements within five consecutive values, by the sets of
      values occupied by each parity: every one is covered by one of
      thm:efourtwolevels, thm:efourspreadtwo, thm:efourspreadthree and
      prop:efourgap;
  (G) the cup products on the 3668 diagonal classes at n = 4, for general
      components on every pair the degrees allow: the graphs Gamma_tau have
      4 components for the four types (2,0,0,0) and 16 for the six types
      (1,1,0,0); exact rank 3184 modulo 1000003 on the 3584 classes of the
      pieces L_zeta, so the kernel is 400 + 84 = 484.
"""
import itertools
import random
import sys

import convolutions_efour as cv

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


n = 4
RAT = [r for r in itertools.product(range(4), repeat=n) if sum(r) % 2 == 0]
NZ = [r for r in RAT if any(r)]


def flip(r):
    """1 if the ratio changes the parity of the piece"""
    return (sum(r) % 4) // 2


def add(a, b):
    return tuple((x + y) % 4 for x, y in zip(a, b))


def gap(x):
    return 0 if x == 0 else (4 if x == 2 else 2)


def Dr(r):
    d = 1
    for x in r:
        if x:
            d *= gap(x)
    return d


def moved(r):
    return sum(1 for x in r if x)


SPREAD2 = [r for r in RAT if moved(r) == 4 and flip(r) == 0]
R4 = [r for r in SPREAD2 if 2 in r]
PM = [r for r in SPREAD2 if 2 not in r]


# ----------------------------------------------------------------------
def binom(m, k):
    if k < 0 or k > m:
        return 0
    c = 1
    for i in range(k):
        c = c * (m - i) // (i + 1)
    return c


def h_dim(r, q):
    """dim H^q between two pieces of ratio r != 0"""
    k = moved(r)
    return Dr(r) * binom(2 * (n - k), q - k)


def part_A():
    ok = len(R4) == 13 and len(PM) == 8
    ok &= sorted(Dr(r) for r in R4) == [64] * 12 + [256]
    ok &= sum(Dr(r) for r in R4) == 1024
    ok &= all(Dr(r) == 16 for r in PM)
    ok &= all(h_dim(r, 4) == Dr(r) for r in SPREAD2)
    check("(A) the 13 ratios with every coordinate moved, one of them by -1, "
          "and no change of parity: D = 256 once and 64 twelve times, 1024 in "
          "all; the 8 others have D = 16", ok)
    opp = [r for r in NZ if flip(r) == 1]
    by_k = {}
    for r in opp:
        by_k.setdefault(moved(r), []).append(h_dim(r, 5))
    ok = sorted(by_k[1]) == [60] * 4 and sorted(by_k[2]) == [16] * 12
    ok &= sorted(by_k[3]) == [16] * 24 + [64] * 4 and set(by_k[4]) == {0}
    tot = sum(sum(v) for v in by_k.values())
    ok &= tot == 4 * 60 + 12 * 16 + 4 * (64 + 6 * 16) == 1072
    ok &= 64 * 1072 == 68608 and 128 * 8 == 1024 and 68608 - 1024 == 67584
    check("(A) spread three: the groups H^5 between a piece and the 64 of the "
          "other parity have dimensions 4 * 60 + 12 * 16 + 4 * (64 + 6 * 16) "
          "= 1072; 64 * 1072 - 128 * 8 = 67584", ok, "total %d" % tot)
    five = sum(h_dim(r, 7) for r in opp)
    ok = five == 16 and 64 * five == 1024 == 128 * 8
    check("(A) spread five: the groups H^7 between a piece and the other "
          "parity have dimension 4 * 4 = 16, so 64 * 16 = 1024, the dimension "
          "of the loops at the 128 pieces", ok)


# ----------------------------------------------------------------------
# (B) terms between pieces L_zeta, over the ratios
def comp_options(r):
    """a component of ratio r != 0: (drop, degrees, non-units) per surface;
    degree 1 where r moves, 0, 1 or 2 elsewhere; drop = Ext degree - 1,
    whose parity is the change of parity"""
    ch = [[(1, 1)] if r[j] else [(0, 0), (1, 1), (2, 1)] for j in range(n)]
    out = []
    for c in itertools.product(*ch):
        q = sum(d for d, _ in c)
        if q < 1 or (q - 1) % 2 != flip(r):
            continue
        out.append((q - 1, tuple(d for d, _ in c), tuple(u for _, u in c)))
    return out


COMP = {r: comp_options(r) for r in NZ}
LOOPS = [(0, tuple(int(j == m) for j in range(n)),
          tuple(int(j == m) for j in range(n))) for m in range(n)]


def vadd(a, b, cap=9):
    return tuple(min(x + y, cap) for x, y in zip(a, b))


def feasible(k, sdeg, u, ranges):
    """a tree with k leaves of total degrees sdeg on the surfaces, u_j of
    them not a unit on B_j, can land in degrees from ranges: the drops
    d_j add up to k - 2 with 0 <= d_j <= max(0, u_j - 2)"""
    lo = hi = 0
    for j in range(n):
        dmax = max(0, u[j] - 2)
        ds = [sdeg[j] - q for q in ranges[j] if 0 <= sdeg[j] - q <= dmax]
        if not ds:
            return False
        lo += min(ds)
        hi += max(ds)
    return lo <= k - 2 <= hi


def trange(rho):
    return tuple((1,) if rho[j] else (0, 1, 2) for j in range(n))


def blocks(dlt):
    """the groups of classes of degree two between two pieces of spread
    d_a - d_b = dlt: (ratio, degrees on the surfaces, non-units)"""
    q = 2 + dlt
    out = []
    for g in NZ:
        if flip(g) != dlt % 2:
            continue
        ch = [[1] if g[j] else [0, 1, 2] for j in range(n)]
        for dx in itertools.product(*ch):
            if sum(dx) == q:
                ux = tuple(int(bool(g[j]) or dx[j] > 0) for j in range(n))
                out.append((g, dx, ux))
    return out


def out_terms(g, dx, ux, dlt):
    """terms of d_E on a class x of ratio g, spread dlt: chains of
    components c' -> ... -> a (drop X1) and b -> ... -> e' (drop X2), the
    output of Ext degree 3 + dlt + X1 + X2 <= 8 in H(c', e'); c' = e' would
    need dlt + X1 + X2 = 0.  Returns the set of (X1, X2) that occur."""
    maxc = 5 - dlt
    start = (g, 0, 0, dx, ux, 0)
    seen = {start}
    frontier = [start]
    found = set()
    while frontier:
        new = []
        for st in frontier:
            rho, c1, c2, sd, u, nc = st
            if nc >= 1 and any(rho) and feasible(nc + 1, sd, u, trange(rho)):
                found.add((c1, c2))
            for r in NZ:
                for drop, dg, nu in COMP[r]:
                    if c1 + c2 + drop > maxc:
                        continue
                    for side in (0, 1):
                        s2 = (add(rho, r), c1 + drop * (side == 0),
                              c2 + drop * (side == 1), vadd(sd, dg),
                              vadd(u, nu), nc + 1)
                        if s2 not in seen:
                            seen.add(s2)
                            new.append(s2)
        frontier = new
    return found


def in_terms(g, dx, dlt):
    """coboundaries with a component in the group (g, dx) of spread dlt:
    leaves of degree one along a path of total drop dlt, one of them u,
    which may be a loop in H^1(a, a); returns True if one is allowed"""
    target = tuple((d,) for d in dx)
    start = ((0,) * n, 0, (0,) * n, (0,) * n, 0, False)
    seen = {start}
    frontier = [start]
    while frontier:
        new = []
        for st in frontier:
            rho, cost, sd, u, k, lp = st
            if k >= 2 and rho == g and cost == dlt and \
                    feasible(k, sd, u, target):
                return True
            nxt = []
            for r in NZ:
                for drop, dg, nu in COMP[r]:
                    if cost + drop <= dlt:
                        nxt.append((add(rho, r), cost + drop, vadd(sd, dg),
                                    vadd(u, nu), k + 1, lp))
            if not lp:
                for drop, dg, nu in LOOPS:
                    nxt.append((rho, cost, vadd(sd, dg), vadd(u, nu), k + 1,
                                True))
            for s2 in nxt:
                if s2 not in seen:
                    seen.add(s2)
                    new.append(s2)
        frontier = new
    return False


def part_B():
    b2 = blocks(2)
    iso = [(g, dx, ux) for g, dx, ux in b2 if g in R4]
    oth = [(g, dx, ux) for g, dx, ux in b2 if g in PM]
    ok = len(iso) == 13 and all(dx == (1, 1, 1, 1) for g, dx, ux in iso)
    ok &= all(not out_terms(g, dx, ux, 2) and not in_terms(g, dx, 2)
              for g, dx, ux in iso)
    check("(B) spread two: the 13 groups H^4 with a coordinate moved by -1 "
          "are reached by no coboundary and left by no term between pieces", ok)
    ok = len(oth) == 8 and all(out_terms(g, dx, ux, 2) and in_terms(g, dx, 2)
                               for g, dx, ux in oth)
    check("(B) spread two: the 8 groups H^4 with every coordinate moved by +-i "
          "are reached and left, so the hypothesis on -1 is needed", ok)
    b3 = blocks(3)
    left = [(g, dx) for g, dx, ux in b3 if out_terms(g, dx, ux, 3)]
    reach = sum(1 for g, dx, ux in b3 if in_terms(g, dx, 3))
    check("(B) spread three: no term between pieces leaves any of the %d "
          "groups of classes of degree two" % len(b3), not left,
          "%d of them are reached by some coboundary" % reach)
    b1 = [(g, dx, ux) for g, dx, ux in blocks(1) if moved(g) == 3]
    drops = set()
    for g, dx, ux in b1:
        drops |= out_terms(g, dx, ux, 1)
    ok = drops and all(1 <= a + b <= 2 for a, b in drops)
    ok &= not any(in_terms(g, dx, 1) for g, dx, ux in b1)
    check("(B) spread one: the %d groups H^3 of three moved coordinates are "
          "reached by nothing, and every term leaving them has chains of "
          "total drop one or two" % len(b1), ok,
          "drops (X1, X2): %s" % sorted(drops))


# ----------------------------------------------------------------------
# (C) runs through the multiples
PLACEMENTS = cv.PLACEMENTS


def runs(vals, Ms):
    """runs of distinct multiples ending at the value of the pieces (first
    chain) and starting at it (second chain): (start, U, D)"""
    def ud(seq):
        U = D = 0
        for x, y in zip(seq, seq[1:]):
            if vals[y] > vals[x]:
                U += 1
            else:
                D += 1
        return U, D
    first, second = [], []
    for k in range(0, 4):
        for X in itertools.permutations(Ms, k):
            U, D = ud(list(X) + ['L'])
            first.append((X[0] if k else 'L', U, D, k))
            U, D = ud(['L'] + list(X))
            second.append((X[-1] if k else 'L', U, D, k))
    return first, second


def part_C():
    ok = True
    sols = 0
    for Ts in PLACEMENTS:
        vals = {'L': 0, 0: Ts[0], 1: Ts[1], 2: Ts[2]}
        first, second = runs(vals, [0, 1, 2])
        for dlt in (1, 2, 3):
            for (c, U1, D1, k1) in first:
                for (e, U2, D2, k2) in second:
                    if k1 + k2 == 0:
                        continue
                    base = 3 + dlt - (U1 + U2) + 7 * (D1 + D2)
                    if c == e:
                        targets = {3}
                    else:
                        targets = {0 if vals[e] > vals[c] else 8}
                    for X in range(0, 12):
                        if base + X in targets:
                            ok = False
                            sols += 1
    check("(C) runs through the multiples: for spread 1, 2, 3 the degree "
          "3 + delta + X - U + 7D is never the degree of H(c, e), for every "
          "X >= 0 and all four placements", ok, "%d solutions" % sols)


# ----------------------------------------------------------------------
# (D) the cut
G0 = [g for g in itertools.product(range(4), repeat=n) if sum(g) % 4 == 0]
W = {g: Dr(g) for g in R4}


def closure(gens):
    S = {(0,) * n}
    fr = list(S)
    while fr:
        nw = []
        for a in fr:
            for g in gens:
                b = add(a, g)
                if b not in S:
                    S.add(b)
                    nw.append(b)
        fr = nw
    return frozenset(S)


def stoer_wagner(Wm):
    m = len(Wm)
    w = [row[:] for row in Wm]
    verts = list(range(m))
    best = None
    groups = {v: [v] for v in verts}
    while len(verts) > 1:
        wt = {v: w[verts[0]][v] for v in verts[1:]}
        A = [verts[0]]
        last = 0
        while wt:
            v = max(wt, key=lambda x: wt[x])
            last = wt.pop(v)
            A.append(v)
            for x in wt:
                wt[x] += w[v][x]
        s, t = A[-2], A[-1]
        if best is None or last < best[0]:
            best = (last, list(groups[t]))
        groups[s] += groups[t]
        for x in verts:
            w[s][x] += w[t][x]
            w[x][s] = w[s][x]
        verts.remove(t)
    return best


def part_D():
    ok = all(g in G0 for g in R4) and len(G0) == 64
    ok &= closure(R4) == frozenset(G0)
    subs = set()
    for k in range(0, 4):
        for gens in itertools.combinations(G0, k):
            subs.add(closure(gens))
    best = None
    eq = []
    for H in subs:
        if len(H) == 64:
            continue
        val = len(H) * sum(v for g, v in W.items() if g not in H)
        if best is None or val < best:
            best = val
        if val == 1024:
            eq.append(len(H))
    ok &= best == 1024 and eq == [1]
    check("(D) the Cayley graph of the 64 ratios of one parity with the 13 "
          "generators: every proper subgroup H has |H| w(S - H) >= 1024, "
          "with equality only for H = 0", ok,
          "%d subgroups" % len(subs))
    idx = {g: i for i, g in enumerate(G0)}
    Wm = [[0] * 64 for _ in range(64)]
    for a in G0:
        for g, v in W.items():
            Wm[idx[a]][idx[add(a, g)]] = v
    sym = all(Wm[i][j] == Wm[j][i] for i in range(64) for j in range(64))
    cut, side = stoer_wagner(Wm)
    U = [[int(x > 0) for x in row] for row in Wm]
    cu, _ = stoer_wagner(U)
    ok = sym and cut == 1024 and min(len(side), 64 - len(side)) == 1 and cu == 13
    check("(D) Stoer-Wagner: the least weighted cut is 1024, at one vertex, "
          "and the least number of edges in a cut is 13", ok,
          "cut %d, side %d, edges %d" % (cut, len(side), cu))


# ----------------------------------------------------------------------
# (E) arrangements, piece by piece
LS = cv.LS
NL = cv.NL


def ratio(z, w):
    return tuple((b - a) % 4 for a, b in zip(z, w))


def spread_two_weight(level, cls):
    """sum of D over pairs c, e of parity cls with d_c - d_e = 2 and ratio
    in R4"""
    P = [a for a in range(NL) if cv.parity(LS[a]) == cls]
    tot = 0
    for a in P:
        for b in P:
            if level[a] - level[b] == 2 and ratio(LS[a], LS[b]) in W:
                tot += W[ratio(LS[a], LS[b])]
    return tot


def cached(C):
    """the degrees of the groups between pieces, memoised"""
    memo = {}
    orig = C.degs

    def degs(a, b):
        if (a, b) not in memo:
            memo[(a, b)] = orig(a, b)
        return memo[(a, b)]
    C.degs = degs
    return C


def part_E():
    rnd = random.Random(44)
    worst = None
    ok = True
    for trial in range(40):
        cls = trial % 2
        level = [0] * NL
        P = [a for a in range(NL) if cv.parity(LS[a]) == cls]
        if trial % 4 < 2:
            k = rnd.choice([1, 2, 3, 5, 17, 32, 47, 63])
            for a in rnd.sample(P, k):
                level[a] = -2
        else:
            rnd.shuffle(P)
            i, j = sorted(rnd.sample(range(1, 64), 2))
            for a in P[:i]:
                level[a] = 2
            for a in P[j:]:
                level[a] = -2
        wgt = spread_two_weight(level, cls)
        worst = wgt if worst is None else min(worst, wgt)
        ok &= wgt >= 1024
    check("(E) one parity at two values two apart, or at three with the "
          "middle one occupied: 40 random arrangements, the groups H^4 of "
          "the 13 ratios weigh at least 1024", ok, "least %d" % worst)
    # spread three: one parity at s, the other at s - 3 or s + 3
    for Ts, top in ((PLACEMENTS[0], 0), (PLACEMENTS[1], 1)):
        C = cached(cv.Conf(Ts))
        level = [0 if cv.parity(z) == top else -3 for z in LS] + [None] * 3
        if top == 1:
            for a in range(NL):
                if cv.parity(LS[a]) == 0 and LS[a][0] % 2 == 0:
                    level[a] = 3
        res = spread_three(C, level)
        check("(E) spread three, t = %s, %s: %d groups, %d classes, the "
              "terms the degrees allow leave none, and only the loops at "
              "the two pieces reach them" % (
                  Ts, "other parity below" if top == 0 else
                  "other parity above and below", res[0], res[1]),
              res[0] == 64 * 44 and res[1] == 68608 and res[2] == 0
              and res[3] == 0)
    # the gap: one parity at y, the other at y + 1 and y - 3 (or y - 1, y + 3)
    for Ts, (hi, lo), cls, near in ((PLACEMENTS[0], (1, -3), 0, 1),
                                    (PLACEMENTS[2], (1, -3), 1, 1),
                                    (PLACEMENTS[1], (3, -1), 0, -1),
                                    (PLACEMENTS[3], (5, 1), 1, 1)):
        C = cached(cv.Conf(Ts))
        level = [None] * (NL + 3)
        other = [a for a in range(NL) if cv.parity(LS[a]) != cls]
        rnd.shuffle(other)
        k = rnd.randrange(1, 9)
        if near == -1:
            k = 64 - k
        for a in range(NL):
            if cv.parity(LS[a]) == cls:
                level[a] = 0
        for a in other[:k]:
            level[a] = hi
        for a in other[k:]:
            level[a] = lo
        res = gap_blocks(C, level, near)
        nnear = sum(1 for a in range(NL) if level[a] == near)
        check("(E) a gap, t = %s, other parity at %s and %s (%d at %d): "
              "%d groups H^3 between the pieces at %d and %d, %d classes, "
              "reached by nothing, left by nothing" % (
                  Ts, hi, lo, nnear, near, res[0], 0, near, res[1]),
              res[1] == 640 * nnear and res[2] == 0 and res[3] == 0)


def spread_three(C, level):
    F, Bk = {}, {}

    def fw(x):
        if x not in F:
            F[x] = cv.chains(C, level, x, +1)
        return F[x]

    def bw(x):
        if x not in Bk:
            Bk[x] = cv.chains(C, level, x, -1)
        return Bk[x]
    nb = dims = hits = kills = 0
    for a in range(NL):
        for b in range(NL):
            if level[a] - level[b] != 3:
                continue
            dim = h_dim(ratio(LS[a], LS[b]), 5)
            if not dim:
                continue
            nb += 1
            dims += dim
            for (a1, ma, va) in fw(a):
                for (b1, mb, vb) in bw(b):
                    if (a1, b1) == (a, b) or not cv.consistent(ma, mb):
                        continue
                    qu = 1 + cv.shift_of(C, level, a1, ma) - \
                        cv.shift_of(C, level, b1, mb)
                    if qu in C.degs(a1, b1):
                        # allowed: a loop u in H^1 at a or at b, with the
                        # component a -> b
                        if a1 == b1 and a1 in (a, b):
                            continue
                        hits += 1
            for (c, mc, vc) in bw(a):
                for (e, me, ve) in fw(b):
                    if (c, e) == (a, b) or not cv.consistent(mc, me):
                        continue
                    q = 3 + cv.shift_of(C, level, c, mc) - \
                        cv.shift_of(C, level, e, me)
                    if q in C.degs(c, e):
                        kills += 1
    return nb, dims, hits, kills


def gap_blocks(C, level, near):
    """groups H^3 between the pieces at 0 and at near (= +-1), of three
    moved coordinates, with the degrees of item (LXXIV)"""
    F, Bk = {}, {}

    def fw(x):
        if x not in F:
            F[x] = cv.chains(C, level, x, +1)
        return F[x]

    def bw(x):
        if x not in Bk:
            Bk[x] = cv.chains(C, level, x, -1)
        return Bk[x]
    nb = dims = hits = kills = 0
    for a in range(NL):
        for b in range(NL):
            if {level[a], level[b]} != {0, near} or level[a] != level[b] + 1:
                continue
            if cv.ndiff(LS[a], LS[b]) != 3:
                continue
            nb += 1
            dims += cv.Dval(LS[a], LS[b])
            for (a1, ma, va) in fw(a):
                for (b1, mb, vb) in bw(b):
                    if (a1, b1) == (a, b) or not cv.consistent(ma, mb):
                        continue
                    qu = 1 + cv.shift_of(C, level, a1, ma) - \
                        cv.shift_of(C, level, b1, mb)
                    hits += qu in C.degs(a1, b1)
            for (c, mc, vc) in bw(a):
                for (e, me, ve) in fw(b):
                    if (c, e) == (a, b) or not cv.consistent(mc, me):
                        continue
                    q = 3 + cv.shift_of(C, level, c, mc) - \
                        cv.shift_of(C, level, e, me)
                    kills += q in C.degs(c, e)
    return nb, dims, hits, kills


# ----------------------------------------------------------------------
# (F) five consecutive values
def covered(A, Bv):
    """A, Bv: the sets of shifts of the two parities (A even values, Bv odd
    values, or the reverse).  Returns the result that excludes it."""
    for S in (A, Bv):
        v = sorted(S)
        if len(v) in (2, 3) and all(y - x == 2 for x, y in zip(v, v[1:])):
            return "spread two"
    if len(A) == 1 and len(Bv) == 1:
        d = abs(next(iter(A)) - next(iter(Bv)))
        if d == 1:
            return "two shifts"
        if d == 3:
            return "spread three"
        return None
    for single, other in ((A, Bv), (Bv, A)):
        if len(single) == 1:
            y = next(iter(single))
            if (y + 1 in other and y - 1 not in other and y + 3 not in other) \
                    or (y - 1 in other and y + 1 not in other
                        and y - 3 not in other):
                return "gap"
    return None


def part_F():
    ok = True
    count = {}
    for s in range(2):
        vals = list(range(0, 5))
        ev = [v for v in vals if v % 2 == s]
        od = [v for v in vals if v % 2 != s]
        for ka in range(1, len(ev) + 1):
            for A in itertools.combinations(ev, ka):
                for kb in range(1, len(od) + 1):
                    for Bv in itertools.combinations(od, kb):
                        r = covered(set(A), set(Bv))
                        count[r] = count.get(r, 0) + 1
                        ok &= r is not None
    check("(F) every arrangement of the two parities within five consecutive "
          "values is excluded by one of the four results", ok,
          ", ".join("%s: %d" % kv for kv in sorted(count.items(),
                                                    key=lambda x: str(x[0]))))
    # within six values exactly the arrangements at two single values five
    # apart and the two gaps on both sides are left
    left = []
    for s in range(2):
        vals = list(range(0, 6))
        ev = [v for v in vals if v % 2 == s]
        od = [v for v in vals if v % 2 != s]
        for ka in range(1, len(ev) + 1):
            for A in itertools.combinations(ev, ka):
                for kb in range(1, len(od) + 1):
                    for Bv in itertools.combinations(od, kb):
                        if covered(set(A), set(Bv)) is None:
                            left.append((A, Bv))
    kinds = sorted(set((len(A), len(B)) for A, B in left))
    check("(F) within six values only two single values five apart and two "
          "values four apart for each parity are left", kinds == [(1, 1), (2, 2)],
          "%d arrangements: %s" % (len(left), left))


# ----------------------------------------------------------------------
# (G) the cup products on the diagonal at n = 4
P = 1000003


def wedge(A, B):
    """product of basis monomials (bitmasks) of an exterior algebra:
    (mask, sign) or None"""
    if A & B:
        return None
    s = 1
    a = A
    while a:
        low = a & -a
        i = low.bit_length() - 1
        s *= -1 if bin(B & ((1 << i) - 1)).count("1") % 2 else 1
        a ^= low
    return A | B, s


def masks_of(tau):
    """basis of H^tau(O_A): surface j has generators 2j, 2j + 1"""
    per = []
    for j in range(n):
        g = [2 * j, 2 * j + 1]
        if tau[j] == 0:
            per.append([0])
        elif tau[j] == 1:
            per.append([1 << g[0], 1 << g[1]])
        else:
            per.append([(1 << g[0]) | (1 << g[1])])
    out = []
    for c in itertools.product(*per):
        m = 0
        for x in c:
            m |= x
        out.append(m)
    return out


def part_G():
    from flint import nmod_mat
    rng = random.Random(7)
    types = [t for t in itertools.product(range(3), repeat=n) if sum(t) == 2]
    pcs = LS
    total_rank = 0
    comps_ok = True
    for tau in types:
        basis = masks_of(tau)
        bi = {m: i for i, m in enumerate(basis)}
        dimt = len(basis)
        rows = []
        par = list(range(NL))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for ia in range(NL):
            for ib in range(ia + 1, NL):
                r = ratio(pcs[ia], pcs[ib])
                S = [j for j in range(n) if r[j] == 0]
                if any(tau[j] for j in range(n) if r[j]):
                    continue
                kD = moved(r)
                vdim = Dr(r)
                prows = []
                for e in itertools.product(range(3), repeat=len(S)):
                    if any(e[i] + tau[S[i]] > 2 for i in range(len(S))):
                        continue
                    q = kD + sum(e)
                    if q < 1 or (q - 1) % 2 != flip(r):
                        continue
                    # a general component: for each of the vdim basis vectors
                    # of the tensor product of the H^1 on the moved surfaces,
                    # a random element of multidegree e on the others
                    emon = []
                    for i, j in enumerate(S):
                        g = [2 * j, 2 * j + 1]
                        if e[i] == 0:
                            emon.append([0])
                        elif e[i] == 1:
                            emon.append([1 << g[0], 1 << g[1]])
                        else:
                            emon.append([(1 << g[0]) | (1 << g[1])])
                    mons = []
                    for c in itertools.product(*emon):
                        m = 0
                        for x in c:
                            m |= x
                        mons.append(m)
                    for v in range(vdim):
                        coef = {m: rng.randrange(P) for m in mons}
                        out = {}
                        for col, y in enumerate(basis):
                            for m, cf in coef.items():
                                w = wedge(y, m)
                                if w is None:
                                    continue
                                out.setdefault(w[0], [0] * dimt)
                                out[w[0]][col] = (out[w[0]][col] + w[1] * cf) % P
                        prows.extend(out.values())
                if not prows:
                    continue
                M = nmod_mat(len(prows), dimt, [x for rw in prows for x in rw], P)
                M = M.rref()[0]
                rk = M.rank()
                if rk:
                    par[find(ia)] = find(ib)
                for i in range(rk):
                    f = [int(M[i, j]) for j in range(dimt)]
                    row = {}
                    for j in range(dimt):
                        if f[j]:
                            row[ia * dimt + j] = (-f[j]) % P
                            row[ib * dimt + j] = f[j]
                    rows.append(row)
        ncomp = len(set(find(x) for x in range(NL)))
        comps_ok &= ncomp == (4 if 2 in tau else 16)
        ncol = NL * dimt
        M = nmod_mat(len(rows), ncol, P)
        for i, row in enumerate(rows):
            for j, v in row.items():
                M[i, j] = v
        total_rank += M.rank()
    check("(G) the graphs Gamma_tau: 4 components for the types (2,0,0,0) and "
          "16 for the types (1,1,0,0)", comps_ok)
    ok = total_rank == 3184 and 128 * 28 - 3184 == 400
    ok &= 4 * 4 * 1 + 6 * 16 * 4 == 400 and 400 + 3 * 28 == 484
    ok &= 484 - 104 == 380 and 131 * 28 == 3668
    check("(G) general components on every pair: cup rank 3184 on the 3584 "
          "classes of the L_zeta, kernel 400; with the 84 of the multiples "
          "484, so higher products must have rank >= 484 - 104 = 380", ok,
          "rank %d" % total_rank)


def main():
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    print()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
