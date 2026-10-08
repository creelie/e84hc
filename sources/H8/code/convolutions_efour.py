"""Item (LXXIV): convolutions of the Weil pieces on E_0^8 at two and three
shifts.

Setting of item (LXXI) at n = 4: A = B_1 x ... x B_4, B_j = E_0 x E_0,
E_0 = C/Z[i]; the 128 pieces L_zeta, zeta in mu_4^4 with prod zeta = +-1,
hermitian form [[p, zeta_j], [conj zeta_j, p]] on B_j, external products of
line bundles on the B_j; the multiples M_1, M_2, M_3 with forms t_i Id,
|t_i - p| >= 2; shifts with (-1)^d = prod zeta for L_zeta.  A morphism of
degree one from P_a to P_b of Ext degree q has d_b = d_a + 1 - q.

Paper: Section "Convolutions of line bundles" (ssec:convolutions):
lem:efourshifts, thm:efourtwolevels, thm:efourthreelevels,
rem:convolutionsopen.

  (A) the counts: 64 pieces of each parity; each has 4, 12, 28 and 20
      partners of the other parity differing in 1, 2, 3 and 4 coordinates;
      the 28 have D = prod |zeta_j - zeta'_j|^2 = 16 (24 of them) and 64
      (4 of them), 640 in all; 64 * 640 = 40960 > r = 7 * 16 - 2 * 4 = 104;
  (B) the Ext degrees between the L_zeta: no H^0 between distinct pieces,
      and H^1 only between pieces of opposite parities, so a component
      between distinct L_zeta has Ext degree >= 2 (lem:efourshifts (i));
  (C) the runs through the multiples: every sequence of morphisms of degree
      one from an L to an L through multiples, distinct before and after one
      marked step (a component or a diagonal class), lowers the shift by at
      least 4, in all four placements of the t_i (lem:efourshifts (iii));
  (D) the two-level theorem: for every placement, both orientations and
      every top piece W, no element of degree one has a component in
      H^3(W, V), and no term of d_E is nonzero on it, for every partner V
      of W differing in three coordinates, with the shifts of the multiples
      left free; also the counting argument of the proof (Q = 4 - U + 7D);
  (E) with a third shift the same enumeration finds terms that the degrees
      allow on such blocks, so the vanishing of d_E needs the two shifts;
  (F) three consecutive shifts (thm:efourthreelevels): the pieces of one
      parity at s - 1, the others at s (the set T) or s - 2 (the set B).
      The targets: a piece has 63 partners of its own parity, 18 differing
      in two coordinates (H^5 of dimension 4D, D = 16 for 6 and 4 for 12),
      24 in three (H^5 of dimension D = 16) and 21 in four (no H^5): 960 in
      all, so the targets weigh at most 32 * 960 = 30720 and the bound is
      40960 - 30720 = 10240 > 104;
  (G) the same, at the level of the types T, Q, B and the multiples, valid
      for every split of the pieces between T and B: the only terms of d_E
      that the degrees allow on a block land in H^5(c, e), c in T, e in B;
  (H) piece by piece, for every placement, a random split and the two
      extreme ones: 1792 blocks of dimension 40960 in total, nothing reaches
      them, every term the degrees allow lands in H^5(c, e) with c in T,
      e in B differing in two or three coordinates, and the targets weigh at
      most min(|T|, |B|) * 960 and at most 18432;
  (I) the weights depend only on the ratio of the two pieces, so the targets
      form a cut of a Cayley graph on the group of ratios: its eigenvalues
      are 960, 384, 192, 96, -32, -64, -128, -192, so a cut weighs at most
      16 * (960 + 192) = 18432, which the split by zeta_3 zeta_4 in {1, i}
      attains, and dim Ext^2 >= 40960 - 18432 = 22528.
"""
import itertools
import sys

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


n = 4
LS = [z for z in itertools.product(range(4), repeat=n) if sum(z) % 2 == 0]
NL = len(LS)


def parity(z):
    return 0 if sum(z) % 4 == 0 else 1


def gap(a, b):
    r = (b - a) % 4
    return 0 if r == 0 else (4 if r == 2 else 2)


def ndiff(z, w):
    return sum(1 for a, b in zip(z, w) if a != b)


def Dval(z, w):
    p = 1
    for a, b in zip(z, w):
        if a != b:
            p *= gap(a, b)
    return p


# ----------------------------------------------------------------------
def part_A():
    ev = [z for z in LS if parity(z) == 0]
    od = [z for z in LS if parity(z) == 1]
    ok = len(ev) == 64 and len(od) == 64
    for z in LS:
        Q = od if parity(z) == 0 else ev
        cnt = [sum(1 for w in Q if ndiff(z, w) == k) for k in range(5)]
        three = [Dval(z, w) for w in Q if ndiff(z, w) == 3]
        ok &= cnt == [0, 4, 12, 28, 20]
        ok &= sorted(three) == [16] * 24 + [64] * 4 and sum(three) == 640
    r = 7 * n * n - 2 * n
    ok &= r == 104 and 64 * 640 == 40960 > r and (NL + 3) * n * (2 * n - 1) == 3668
    check("(A) each L_zeta has 4, 12, 28, 20 partners of the other parity "
          "differing in 1, 2, 3, 4 coordinates; the 28 have D = 16 (24) and "
          "64 (4), 640 in all; 64 * 640 = 40960 > 104; 3668 diagonal classes", ok)


# ----------------------------------------------------------------------
# the configuration: pieces 0..127 are the L_zeta, 128..130 the multiples
class Conf:
    def __init__(self, Ts, p=0):
        self.Ts, self.p = list(Ts), p
        self.N = NL + 3

    def isM(self, a):
        return a >= NL

    def t(self, a):
        return self.Ts[a - NL]

    def degs(self, a, b):
        """the degrees of H^*(A, P_a^{-1} P_b)"""
        if a == b:
            return set(range(2 * n + 1))
        if not self.isM(a) and not self.isM(b):
            k = ndiff(LS[a], LS[b])
            return set(range(k, k + 2 * (n - k) + 1))
        if self.isM(a) and self.isM(b):
            return {0} if self.t(b) > self.t(a) else {2 * n}
        if not self.isM(a):           # L -> M: form t - [[p, z], [z, p]]
            return {0} if self.t(b) > self.p else {2 * n}
        return {0} if self.t(a) < self.p else {2 * n}   # M -> L


def part_B():
    C = Conf([2, 5, 6])
    ok = True
    for a in range(NL):
        for b in range(NL):
            if a == b:
                continue
            ds = C.degs(a, b)
            ok &= 0 not in ds
            if 1 in ds:
                ok &= parity(LS[a]) != parity(LS[b]) and ndiff(LS[a], LS[b]) == 1
    check("(B) between distinct L_zeta there is no H^0, and H^1 only for one "
          "differing coordinate, between opposite parities: a component has "
          "Ext degree >= 2 and lowers the shift by >= 1", ok)


PLACEMENTS = [[2, 5, 6], [-2, 2, 5], [-5, -2, 2], [-6, -5, -2]]


def part_C():
    ok = True
    worst = 99
    count = 0
    for Ts in PLACEMENTS:
        C = Conf(Ts)
        Ms = [NL, NL + 1, NL + 2]
        L0 = 0      # a representative L; the degrees only see the values

        def step(a, b):
            q = C.degs(a, b)
            assert len(q) == 1
            return 1 - next(iter(q))      # shift change d_b - d_a
        # sequences: L -> X_1 ... X_a (distinct) [marked step] Y_1 ... Y_b
        # (distinct) -> L; the marked step is a component X_a -> Y_1 or, if
        # X_a = Y_1, a diagonal class at it (shift change 0)
        for a_len in range(0, 4):
            for X in itertools.permutations(Ms, a_len):
                for b_len in range(0, 4):
                    for Y in itertools.permutations(Ms, b_len):
                        if a_len + b_len == 0:
                            continue
                        seq = [L0] + list(X)
                        diag_options = [False]
                        if a_len and b_len and X[-1] == Y[0]:
                            diag_options = [True]
                        for diag in diag_options:
                            seq2 = seq + (list(Y[1:]) if diag else list(Y)) + [L0 + 1]
                            # the last L is another piece of the same value
                            dsh = 0
                            for u, v in zip(seq2, seq2[1:]):
                                if not C.isM(u) and not C.isM(v):
                                    dsh = None
                                    break
                                dsh += step(u, v)
                            if dsh is None:
                                continue
                            count += 1
                            worst = min(worst, -dsh)
                            ok &= -dsh >= 4
    check("(C) every run L -> multiples -> L of morphisms of degree one, the "
          "multiples distinct before and after one marked step, lowers the "
          "shift by at least 4, in all four placements", ok,
          "%d runs, least drop %d" % (count, worst))


# ----------------------------------------------------------------------
def chains(C, level, start, dirn, maxlen=6):
    """chains of components from start (dirn=+1) or into start (dirn=-1).
    level[a] is the shift of an L piece; the shifts of the multiples are
    free and assigned along the chain.  Returns (end, mshifts, visited)."""
    out = []
    d0 = level[start] if not C.isM(start) else 0

    def rec(x, dx, msh, vis):
        out.append((x, dict(msh), frozenset(vis)))
        if len(vis) > maxlen:
            return
        for y in range(C.N):
            if y in vis:
                continue
            a, b = (x, y) if dirn > 0 else (y, x)
            ds = C.degs(a, b)
            if C.isM(y):
                if y in msh:
                    cand = [msh[y]]
                else:
                    cand = [dx + dirn * (1 - q) for q in ds]
            else:
                cand = [level[y]] if level[y] is not None else []
            for dy in cand:
                q = 1 + (dx - dy if dirn > 0 else dy - dx)
                if q not in ds:
                    continue
                msh2 = dict(msh)
                if C.isM(y):
                    msh2[y] = dy
                rec(y, dy, msh2, vis | {y})
    msh0 = {start: d0} if C.isM(start) else {}
    rec(start, d0, msh0, {start})
    # keep one chain for each end and assignment of shifts
    uniq = {}
    for (x, msh, vis) in out:
        uniq.setdefault((x, tuple(sorted(msh.items()))), (x, msh, vis))
    return list(uniq.values())


def shift_of(C, level, a, msh):
    return msh[a] if C.isM(a) else level[a]


def consistent(m1, m2):
    return all(m2[k] == v for k, v in m1.items() if k in m2)


def block_terms(C, level, W, V, FW, BV, BW, FV):
    """(hits, kills): degree-allowed ways in which a class of degree one
    reaches H^3(W, V), and terms of d_E on H^3(W, V)"""
    hits = kills = 0
    # (i) u of degree one in H(a', b'), chains W -> a' and b' -> V
    for (a1, ma, va) in FW:
        for (b1, mb, vb) in BV:
            if (a1, b1) == (W, V) or not consistent(ma, mb):
                continue
            qu = 1 + shift_of(C, level, a1, ma) - shift_of(C, level, b1, mb)
            if qu in C.degs(a1, b1):
                hits += 1
    # (ii) chains c -> W and V -> e, at least one component
    for (c, mc, vc) in BW:
        for (e, me, ve) in FV:
            if (c, e) == (W, V) or not consistent(mc, me):
                continue
            Q = 3 + shift_of(C, level, c, mc) - shift_of(C, level, e, me)
            if Q in C.degs(c, e):
                kills += 1
    return hits, kills


def two_level(Ts, top):
    C = Conf(Ts)
    level = [0 if parity(z) == top else -1 for z in LS] + [None] * 3
    tops = [a for a in range(NL) if parity(LS[a]) == top]
    bots = [a for a in range(NL) if parity(LS[a]) != top]
    FW = {W: chains(C, level, W, +1) for W in tops}
    BW = {W: chains(C, level, W, -1) for W in tops}
    FV = {V: chains(C, level, V, +1) for V in bots}
    BV = {V: chains(C, level, V, -1) for V in bots}
    nblocks = H = K = 0
    dims = 0
    for W in tops:
        for V in bots:
            if ndiff(LS[W], LS[V]) != 3:
                continue
            nblocks += 1
            dims += Dval(LS[W], LS[V])
            h, k = block_terms(C, level, W, V, FW[W], BV[V], BW[W], FV[V])
            H += h
            K += k
    return nblocks, dims, H, K


def part_D():
    for Ts in PLACEMENTS:
        res = []
        ok = True
        for top in (0, 1):
            nb, dims, H, K = two_level(Ts, top)
            ok &= nb == 64 * 28 and dims == 40960 and H == 0 and K == 0
            res.append("%d blocks, %d classes, %d hits, %d terms" % (nb, dims, H, K))
        check("(D) two shifts, t = %s: every block H^3(W, V), W on top, V a "
              "three-coordinate partner below, is reached by nothing and killed "
              "by no term the degrees allow" % Ts, ok, "; ".join(res))
    # the counting of the proof: Q = 4 - U + 7D against the targets
    ok = True
    for Ts in PLACEMENTS:
        vals = {'L': 0}
        for i, t in enumerate(Ts):
            vals[i] = t
        Ms = [0, 1, 2]

        def ud(seq):
            U = D = 0
            for x, y in zip(seq, seq[1:]):
                if vals[y] > vals[x]:
                    U += 1
                else:
                    D += 1
            return U, D
        for a_len in range(0, 4):
            for X in itertools.permutations(Ms, a_len):          # c = X[0]
                for b_len in range(0, 4):
                    for Y in itertools.permutations(Ms, b_len):  # e = Y[-1]
                        if a_len + b_len == 0:
                            continue
                        U1, D1 = ud(list(X) + ['L'])
                        U2, D2 = ud(['L'] + list(Y))
                        U, D = U1 + U2, D1 + D2
                        Q = 4 - U + 7 * D
                        c = X[0] if a_len else 'L'
                        e = Y[-1] if b_len else 'L'
                        if c == e:
                            target = {3}            # d_c = d_e forces Q = 3
                            allowed = Q == 3
                        elif c == 'L' or e == 'L':
                            other = e if c == 'L' else c
                            up = vals[e] > vals[c]
                            allowed = Q == (0 if up else 8)
                        else:
                            up = vals[e] > vals[c]
                            allowed = Q == (0 if up else 8)
                        ok &= not allowed
    check("(D) the counting of the proof: along multiples-only chains the "
          "output degree is 4 - U + 7D, never a degree of H(c, e)", ok)


def part_E():
    C = Conf([2, 5, 6])
    top = 0
    level = [0 if parity(z) == top else -1 for z in LS] + [None] * 3
    # put one piece of the top parity two steps lower
    low = next(a for a in range(NL) if parity(LS[a]) == top and LS[a] != (0, 0, 0, 0))
    level[low] = -2
    W = LS.index((0, 0, 0, 0))
    found = 0
    for V in range(NL):
        if parity(LS[V]) == top or ndiff(LS[W], LS[V]) != 3:
            continue
        h, k = block_terms(C, level, W, V, chains(C, level, W, +1),
                           chains(C, level, V, -1), chains(C, level, W, -1),
                           chains(C, level, V, +1))
        found += (h + k > 0)
    check("(E) with one piece moved to a third shift, terms that the degrees "
          "allow reach some of these blocks, so the theorem needs two shifts",
          found > 0, "%d of 28 blocks at W = (1,1,1,1)" % found)


# ----------------------------------------------------------------------
# three consecutive shifts
def h5(z, w):
    """dim H^5(A, L_z^{-1} L_w) for distinct pieces of the same parity"""
    S = [j for j in range(n) if z[j] != w[j]]
    D = Dval(z, w)
    k, rest, m = len(S), 5 - len(S), 2 * (n - len(S))
    if rest < 0 or rest > m:
        return 0
    c = 1
    for i in range(rest):
        c = c * (m - i) // (i + 1)
    return D * c


def part_F():
    ok = True
    for z in LS:
        same = [w for w in LS if w != z and parity(w) == parity(z)]
        by_k = {}
        for w in same:
            by_k.setdefault(ndiff(z, w), []).append(h5(z, w))
        ok &= len(same) == 63
        ok &= sorted(by_k[2]) == [16] * 12 + [64] * 6
        ok &= by_k[3] == [16] * 24 and len(by_k[3]) == 24
        ok &= set(by_k[4]) == {0} and len(by_k[4]) == 21
        ok &= sum(by_k[2]) == 576 and sum(by_k[3]) == 384
    ok &= 32 * 960 == 30720 and 64 * 640 - 30720 == 10240 > 104
    check("(F) three shifts: a piece has 18, 24, 21 partners of its parity "
          "differing in 2, 3, 4 coordinates, with H^5 of dimensions adding "
          "up to 576, 384, 0, so 960; 40960 - 32 * 960 = 10240 > 104", ok)


TYPES = {'T': 0, 'Q': -1, 'B': -2}
TCLS = {'T': 0, 'B': 0, 'Q': 1}


def type_terms(Ts, p=0, maxlen=8):
    """the terms of d_E that the degrees allow on a block of type (T, Q) or
    (Q, B), the L pieces replaced by their types (several pieces of one type
    may occur on a chain) and the degrees between two types by the union
    over the possible numbers of differing coordinates"""
    phi = {'M%d' % i: t for i, t in enumerate(Ts)}
    for x in TYPES:
        phi[x] = p
    nodes = ['T', 'Q', 'B', 'M0', 'M1', 'M2']

    def tdegs(a, b, same=False):
        if a in TYPES and b in TYPES:
            if a == b and same:
                return set(range(2 * n + 1))
            return set(range(2, 7)) if TCLS[a] == TCLS[b] else set(range(1, 8))
        if a == b:
            return set(range(2 * n + 1))
        return {0} if phi[b] > phi[a] else {2 * n}

    def tchains(start, dirn):
        out = []

        def rec(x, dx, msh, length):
            out.append((x, dx, dict(msh), length))
            if length >= maxlen:
                return
            for y in nodes:
                if y.startswith('M') and (y in msh or y == x):
                    continue
                a, b = (x, y) if dirn > 0 else (y, x)
                ds = tdegs(a, b)
                cand = [TYPES[y]] if y in TYPES else \
                    [dx + dirn * (1 - q) for q in ds]
                for dy in cand:
                    q = 1 + (dx - dy if dirn > 0 else dy - dx)
                    if q in ds:
                        m2 = dict(msh)
                        if y.startswith('M'):
                            m2[y] = dy
                        rec(y, dy, m2, length + 1)
        rec(start, TYPES[start], {}, 0)
        return out

    found = set()
    for (a, b) in (('T', 'Q'), ('Q', 'B')):
        for (c, dc, mc, l1) in tchains(a, -1):
            for (e, de, me, l2) in tchains(b, +1):
                if l1 + l2 == 0 or not consistent(mc, me):
                    continue
                q = 3 + dc - de
                if q in tdegs(c, e, c == e):
                    found.add((a, b, c, e, q))
    return found


def part_G():
    ok = True
    for Ts in PLACEMENTS:
        found = type_terms(Ts)
        ok &= found == {('T', 'Q', 'T', 'B', 5), ('Q', 'B', 'T', 'B', 5)}
    check("(G) three shifts, every split: on the blocks of types (T, Q) and "
          "(Q, B) the degrees allow terms of d_E only into H^5(c, e), c in T, "
          "e in B, in all four placements", ok)


def three_level(Ts, Pcls, top):
    C = Conf(Ts)
    level = [(0 if a in top else -2) if parity(z) == Pcls else -1
             for a, z in enumerate(LS)] + [None] * 3
    F, Bk = {}, {}

    def fw(x):
        if x not in F:
            F[x] = chains(C, level, x, +1)
        return F[x]

    def bw(x):
        if x not in Bk:
            Bk[x] = chains(C, level, x, -1)
        return Bk[x]
    nb = dims = hits = 0
    targets = set()
    for a in range(NL):
        for b in range(NL):
            if ndiff(LS[a], LS[b]) != 3 or level[a] != level[b] + 1:
                continue
            nb += 1
            dims += Dval(LS[a], LS[b])
            for (a1, ma, va) in fw(a):
                for (b1, mb, vb) in bw(b):
                    if (a1, b1) == (a, b) or not consistent(ma, mb):
                        continue
                    qu = 1 + shift_of(C, level, a1, ma) - \
                        shift_of(C, level, b1, mb)
                    hits += qu in C.degs(a1, b1)
            for (c, mc, vc) in bw(a):
                for (e, me, ve) in fw(b):
                    if (c, e) == (a, b) or not consistent(mc, me):
                        continue
                    q = 3 + shift_of(C, level, c, mc) - \
                        shift_of(C, level, e, me)
                    if q in C.degs(c, e):
                        targets.add((c, e, q))
    good = all(not C.isM(c) and not C.isM(e) and q == 5 and c in top and
               level[e] == -2 and ndiff(LS[c], LS[e]) in (2, 3)
               for (c, e, q) in targets)
    tdim = sum(h5(LS[c], LS[e]) for (c, e, q) in targets)
    return nb, dims, hits, good, tdim


def part_H():
    import random
    rnd = random.Random(43)
    for i, Ts in enumerate(PLACEMENTS):
        Pcls = i % 2
        Ps = [a for a in range(NL) if parity(LS[a]) == Pcls]
        splits = [set(rnd.sample(Ps, 32))]
        if i == 0:
            splits += [set(Ps[:1]), set(Ps[1:])]
        res = []
        ok = True
        for top in splits:
            nb, dims, hits, good, tdim = three_level(Ts, Pcls, top)
            bound = min(len(top), 64 - len(top)) * 960
            ok &= nb == 1792 and dims == 40960 and hits == 0 and good
            ok &= tdim <= bound and tdim <= 18432
            res.append("|T| = %d: targets %d" % (len(top), tdim))
        check("(H) three shifts, t = %s, %s parity in the middle: 1792 blocks, "
              "40960 classes, nothing reaches them, every term lands in "
              "H^5(T, B)" % (Ts, "odd" if Pcls == 0 else "even"), ok,
              "; ".join(res))


def part_I():
    G0 = [g for g in itertools.product(range(4), repeat=n) if sum(g) % 4 == 0]
    zero = (0,) * n
    w = {g: h5(zero, g) for g in G0 if g != zero}
    RE, IM = [1, 0, -1, 0], [0, 1, 0, -1]
    eig = set()
    real = True
    for m in itertools.product(range(4), repeat=n):
        e = [sum(a * b for a, b in zip(m, g)) % 4 for g in w]
        re = sum(v * RE[k] for v, k in zip(w.values(), e))
        real &= sum(v * IM[k] for v, k in zip(w.values(), e)) == 0
        eig.add(re)
    ok = real and sorted(eig) == [-192, -128, -64, -32, 96, 192, 384, 960]
    lam = min(eig)
    bound = len(G0) * (sum(w.values()) - lam) // 4
    ok &= sum(w.values()) == 960 and bound == 18432
    # the split by zeta_3 zeta_4 in {1, i} attains it, in both classes
    for cls in (0, 1):
        P = [z for z in LS if parity(z) == cls]
        T = [z for z in P if (z[2] + z[3]) % 4 in (0, 1)]
        Bs = [z for z in P if (z[2] + z[3]) % 4 in (2, 3)]
        cut = sum(h5(z, y) for z in T for y in Bs)
        ok &= len(T) == len(Bs) == 32 and cut == 18432
    ok &= 64 * 640 - 18432 == 22528
    check("(I) the targets form a cut of a Cayley graph with eigenvalues "
          "960, 384, 192, 96, -32, -64, -128, -192: a cut weighs at most "
          "16 * 1152 = 18432, attained by zeta_3 zeta_4 in {1, i}; "
          "40960 - 18432 = 22528", ok)


def main():
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    part_H()
    part_I()
    print()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
