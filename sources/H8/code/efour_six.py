"""Item (LXXVIII): the diagonal at a lonely shift on E_0^8, interleaved
shifts, and the shift arrangements within six consecutive values.

Setting of items (LXXIV) and (LXXVII) at n = 4: A = B_1 x ... x B_4,
B_j = E_0 x E_0, E_0 = C/Z[i]; the 128 pieces L_zeta, zeta in mu_4^4 with
prod zeta = +-1, external products of line bundles on the B_j; the
multiples M_1, M_2, M_3 with forms t_i Id, |t_i - p| >= 2; shifts with
(-1)^d = prod zeta for L_zeta.  A ratio of two pieces is written
additively, r in (Z/4)^4 of even sum; it changes the parity exactly when
its sum is 2 mod 4.

Paper: Section "Convolutions of line bundles" (ssec:convolutions):
lem:efourlonely, prop:efoursingle, prop:efourpairs, cor:efoursix,
rem:convolutionsopen.

  (A) the runs: a run from a piece through m <= 3 distinct multiples to a
      piece lowers the shift by 4, 5, 6, 12, 13 or 20 over the four
      placements, never by 7;
  (B) the lonely diagonal: with the parities at single shifts s and s - g,
      g = 5, 7, 9, 11, 13, both parities on top and the four placements,
      every term on a diagonal class that the degrees allow, enumerated
      with the shifts of the multiples free: at each shift exactly four,
      the only piece on the path is the piece of the class, the path runs
      through the three multiples (once with three steps up, three times
      with two up and one down, as in the footnote), the shifts of the
      piece and the multiples are pairwise incongruent modulo 4, and the
      shifts of the multiples for the two shifts never agree;
  (C) interleaved shifts: the 28 ratios S_3 that move three coordinates
      and change the parity weigh 640 and generate the 128 ratios; over the
      636 subgroups H, |H| * w(S_3 - H) >= 640 with equality only at
      H = 0; the least cut is 640, at one vertex (Stoer-Wagner); and, piece
      by piece with the degrees of item (LXXIV) and the shifts of the
      multiples free, for random splits of the parities between
      {s, s - 4} and {s - 1, s - 5} the groups H^3 between adjacent shifts
      are reached by nothing and left by nothing, and weigh at least 640;
  (D) the shift arrangements within six consecutive values, by the sets of
      values occupied by each parity: every one is covered by the results
      of item (LXXVII) or by prop:efoursingle and prop:efourpairs, and
      single shifts at every odd distance are covered.
"""
import itertools
import random
import sys

import convolutions_efour as cv
import efour_blocks as eb

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


NL, LS = cv.NL, cv.LS


# ---------------------------------------------------------------- (A)
def run_drops(Ts):
    C = cv.Conf(Ts)
    Ms = [NL, NL + 1, NL + 2]
    drops = set()
    for m in range(1, 4):
        for X in itertools.permutations(Ms, m):
            seq = [0] + list(X) + [1]
            dsh = 0
            for u, v in zip(seq, seq[1:]):
                q = C.degs(u, v)
                dsh += 1 - next(iter(q))
            drops.add(-dsh)
    return drops


def part_A():
    allv = set()
    ok = True
    for Ts in cv.PLACEMENTS:
        d = run_drops(Ts)
        allv |= d
        ok &= 7 not in d and min(d) >= 4
    ok &= allv == {4, 5, 6, 12, 13, 20}
    check("(A) a run from a piece through distinct multiples to a piece "
          "lowers the shift by 4, 5, 6, 12, 13 or 20, never by 7", ok,
          "drops %s" % sorted(allv))


# ---------------------------------------------------------------- (B)
def diagonal_terms(C, level, a):
    """the degree-allowed terms of d_E on a diagonal class at a: pairs of a
    chain into a and a chain out of a, disjoint apart from a, with
    consistent shifts of the multiples, landing in a degree of H(c, e)"""
    B = cv.chains(C, level, a, -1)
    F = cv.chains(C, level, a, +1)
    out = []
    for (c, mc, vc) in B:
        for (e, me, ve) in F:
            if c == a and e == a:
                continue
            if not cv.consistent(mc, me) or ((vc - {a}) & (ve - {a})):
                continue
            q = 3 + cv.shift_of(C, level, c, mc) - cv.shift_of(C, level, e, me)
            if q in C.degs(c, e):
                m = dict(mc)
                m.update(me)
                out.append((c, e, vc | ve, m))
    return out


def part_B():
    ok = True
    total = 0
    for g in (5, 7, 9, 11, 13):
        for Ts in cv.PLACEMENTS:
            for top in (0, 1):
                C = cv.Conf(Ts)
                level = [0 if cv.parity(z) == top else -g for z in LS] + [None] * 3
                pats = {}
                for name, d in (("top", 0), ("bottom", -g)):
                    a = next(x for x in range(NL) if level[x] == d)
                    terms = diagonal_terms(C, level, a)
                    S = set()
                    for (c, e, vis, m) in terms:
                        pieces = [x for x in vis if x < NL]
                        ok &= pieces == [a] and len(m) == 3
                        res = {d % 4} | {v % 4 for v in m.values()}
                        ok &= len(res) == 4
                        S.add(tuple(sorted(m.items())))
                    ok &= len(S) == 4
                    pats[name] = S
                    total += len(S)
                ok &= not (pats["top"] & pats["bottom"])
                # the four paths of the footnote: one with three steps up,
                # three with the largest j values first, j = 1, 2, 3
                vals = sorted([(t, NL + i) for i, t in enumerate(Ts)] + [(0, "a")])
                names = [x for _, x in vals]
                expect = set()
                for j in range(0, 4):
                    order = names if j == 0 else names[4 - j:] + names[:4 - j]
                    sh = {}
                    pos = order.index("a")
                    for k, x in enumerate(order):
                        step = 0
                        for u in range(min(k, pos), max(k, pos)):
                            up = (j == 0) or (u != j - 1)
                            step += 1 if up else -7
                        sh[x] = step if k > pos else -step
                    expect.add(tuple(sorted((x, v) for x, v in sh.items() if x != "a")))
                ok &= expect == pats["top"]
    check("(B) single shifts s and s - g, g = 5, ..., 13, four placements, "
          "both parities on top: the diagonal at each shift carries exactly "
          "four degree-allowed terms, each through the three multiples with "
          "no other piece, shifts pairwise incongruent mod 4, never shared "
          "by the two shifts, as in the footnote", ok,
          "%d patterns" % total)


# ---------------------------------------------------------------- (C)
GAMMA = [r for r in itertools.product(range(4), repeat=4) if sum(r) % 2 == 0]
S3 = [r for r in GAMMA if eb.moved(r) == 3 and sum(r) % 4 == 2]


def grp_close(gens):
    H = {(0, 0, 0, 0)}
    frontier = [(0, 0, 0, 0)]
    while frontier:
        nf = []
        for h in frontier:
            for x in gens:
                k = eb.add(h, x)
                if k not in H:
                    H.add(k)
                    nf.append(k)
        frontier = nf
    return frozenset(H)


def part_C():
    ok = len(S3) == 28 and sum(eb.Dr(r) for r in S3) == 640
    ok &= sorted(eb.Dr(r) for r in S3) == [16] * 24 + [64] * 4
    ok &= len(grp_close(S3)) == 128
    subs = {frozenset({(0, 0, 0, 0)})}
    layer = set(subs)
    while layer:
        new = set()
        for H in layer:
            for x in GAMMA:
                if x not in H:
                    K = grp_close(list(H) + [x])
                    if K not in subs:
                        subs.add(K)
                        new.add(K)
        layer = new
    vals = [(len(H) * sum(eb.Dr(r) for r in S3 if r not in H), len(H))
            for H in subs if len(H) < 128]
    least = min(vals)
    ok &= len(subs) == 636 and least == (640, 1)
    ok &= sum(1 for v in vals if v[0] == 640) == 1
    idx = {r: k for k, r in enumerate(GAMMA)}
    Wm = [[0] * 128 for _ in range(128)]
    for a in GAMMA:
        for r in S3:
            Wm[idx[a]][idx[eb.add(a, r)]] += eb.Dr(r)
    cut, side = eb.stoer_wagner(Wm)
    ok &= cut == 640 and min(len(side), 128 - len(side)) == 1
    check("(C) the 28 ratios S_3 weigh 640 (16 twenty-four times, 64 four "
          "times) and generate the 128 ratios; over the 636 subgroups, "
          "|H| w(S_3 - H) >= 640 with equality only at H = 0; least cut 640 "
          "at one vertex", ok, "%d subgroups, least %d" % (len(subs), least[0]))

    rnd = random.Random(45)
    least_w = None
    ok = True
    for trial in range(2):
        Ts = cv.PLACEMENTS[trial]
        C = cv.Conf(Ts)
        top = trial % 2
        level = []
        for z in LS:
            if cv.parity(z) == top:
                level.append(rnd.choice([0, -4]))
            else:
                level.append(rnd.choice([-1, -5]))
        level += [None] * 3
        for d in (0, -4, -1, -5):
            if d not in level:
                level[next(x for x in range(NL) if level[x] in
                           ((0, -4) if d in (0, -4) else (-1, -5)))] = d
        F = {x: cv.chains(C, level, x, +1) for x in range(NL)}
        B = {x: cv.chains(C, level, x, -1) for x in range(NL)}
        w = 0
        for W in range(NL):
            for V in range(NL):
                if level[W] - level[V] != 1 or level[W] not in (0, -4):
                    continue
                if cv.ndiff(LS[W], LS[V]) != 3:
                    continue
                h, k = cv.block_terms(C, level, W, V, F[W], B[V], B[W], F[V])
                ok &= h == 0 and k == 0
                w += cv.Dval(LS[W], LS[V])
        ok &= w >= 640
        least_w = w if least_w is None else min(least_w, w)
    check("(C) interleaved shifts {s, s-4} and {s-1, s-5}, two random splits "
          "in two placements, one for each parity on top, piece by piece with the shifts of the "
          "multiples free: every group H^3 between adjacent shifts is "
          "reached by nothing and left by nothing, and they weigh >= 640", ok,
          "least %d" % least_w)


# ---------------------------------------------------------------- (D)
def covered6(A, Bv):
    r = eb.covered(A, Bv)
    if r is not None:
        return r
    if len(A) == 1 and len(Bv) == 1:
        if abs(next(iter(A)) - next(iter(Bv))) % 2 == 1:
            return "single shifts"
    for P1, P2 in ((A, Bv), (Bv, A)):
        v1, v2 = sorted(P1), sorted(P2)
        if len(v1) == 2 and len(v2) == 2 and v1[1] - v1[0] == 4 \
                and v2[1] - v2[0] == 4 and v1[1] - v2[1] == 1:
            return "interleaved"
    return None


def part_D():
    ok = True
    count = {}
    for s in range(2):
        vals = list(range(0, 6))
        ev = [v for v in vals if v % 2 == s]
        od = [v for v in vals if v % 2 != s]
        for ka in range(1, len(ev) + 1):
            for A in itertools.combinations(ev, ka):
                for kb in range(1, len(od) + 1):
                    for Bv in itertools.combinations(od, kb):
                        r = covered6(set(A), set(Bv))
                        count[r] = count.get(r, 0) + 1
                        ok &= r is not None
    ok &= all(covered6({0}, {g}) is not None for g in range(-41, 42, 2))
    check("(D) every arrangement of the two parities within six consecutive "
          "values is excluded, and single shifts at every odd distance up "
          "to 41", ok,
          ", ".join("%s: %d" % kv for kv in sorted(count.items(),
                                                   key=lambda kv: str(kv[0]))))
    ok = 64 * 28 == 1792 > 104 and min(640, 1024, 1792, 40960, 67584) == 640
    check("(D) the bounds: 64 * 28 = 1792 diagonal classes at a lonely shift; "
          "the least bound within six values is 640 > 104", ok)


def main():
    part_A()
    part_B()
    part_C()
    part_D()
    print()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
