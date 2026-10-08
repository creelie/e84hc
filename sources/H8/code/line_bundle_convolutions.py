"""Item (LXXI): convolutions of line bundles and the diagonal of Ext^2.

Setting.  A = E^{2n}, E = C/Z[i], with K = Q(i) acting by i on the first n
coordinates and by -i on the last n, polarised by the product polarisation
theta; it is a member of a Weil family for K.  Write B_j = E x E for the
surface with coordinates (z_j, z_{n+j}), so that A = B_1 x ... x B_n.  For
zeta in mu_4^n and an integer p let L_zeta be a line bundle with hermitian
form h^(j) = [[p, zeta_j], [conj zeta_j, p]] on B_j, and let M_t have
hermitian form t Id.  A convolution E of the L_zeta with prod zeta = +-1
(sign prod zeta) and of three M_{t_i} (signs sigma_i) has

    ch(E) = 2 4^{n-1} (alpha + conj alpha) + sum_i sigma_i e^{t_i theta},

alpha = prod_j (i/2) dz_j ^ dz-bar_{n+j} a Weil class.

Paper: Section "Convolutions of line bundles" (ssec:convolutions) of the
secant objects section: prop:weilpieces, lem:indexsum, lem:harmonicmodel,
thm:fewpieces (with prop:rigidity), lem:degreedrop, prop:nothingenters, prop:cupkernel,
thm:esixdiagonal, prop:mixedplacement, rem:convolutionsopen.

  (A) the pure Weil character: exact in the exterior algebra over Q(i) for
      n = 2, 3 and three values of p, and the per-surface identity
      sum_z z e^{D(z)} = 4 c' behind it;
  (B) Hankel rank 3 for three distinct multiples, r = 7n^2 - 2n, the counts
      2 4^{n-1} + 3 pieces, 525 and 3668 diagonal classes, the gap 468;
  (C) the first-order kernel: v -| D = 0 for every tangent vector of the
      polarised family forces D in C theta (n = 2, 3, 4, exact);
  (D) the index lemma: n(X + Y) <= n(X) + n(Y), and a loop of nondegenerate
      differences has total index at least g (random hermitian data);
  (E) the excess of a loop: every closed walk of degree-one steps among the
      pieces has excess at least 1 for n = 3, 4 (so nothing enters the
      diagonal), and a closed walk of excess 0 exists at n = 2;
  (F) the degree drop: on binary trees with up to 8 leaves, distinct marked
      leaf sets of size >= 2 other than the full set number at most u - 2;
  (G) the cup kernel at n = 3: the pairs that can carry a cup product, the
      component counts 4 and 16, and rank 276 for generic data, so a kernel
      of 204 + 45 = 249;
  (H) the higher products at n = 3: with the multiples above the Weil pieces
      only the length-four chains M_{t2} -> M_{t3} -> L -> M_{t1} survive the
      degree bookkeeping and the Maurer-Cartan equation, and only for
      sigma_1 = sigma_3 = -sigma_2; pure Weil pieces carry none; with t_1
      below p and t_2, t_3 above (prop:mixedplacement) only the patterns
      sigma_1 = sigma_2 = -sigma_3 carry products, along M_{t2} -> M_{t3} ->
      M_{t1} -> L and M_{t3} -> M_{t1} -> L -> M_{t2}; the other placements
      are their duals; the pruned search agrees with the exhaustive one;
  (I) the thresholds: 249 - 57 = 192, (t_2 - t_1)^6 = 1, 64 < 192 <= 729,
      and for the mixed placement 16 ((t_2 - p)^2 - 1)^3 >= 432;
  (J) n = 4: chains of length three and four among the Weil pieces pass the
      bookkeeping, so the analysis does not close there.
"""
import itertools
import random
import sys
from fractions import Fraction as Fr
from functools import lru_cache
from math import comb

import sympy as sp

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ----------------------------------------------------------------------
# (A) exterior algebra over Q(i); a form is {bitmask: (re, im)}

def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def wsign(A, B):
    s = 0
    b = B
    while b:
        low = b & -b
        s += bin(A & ~((low << 1) - 1)).count("1")
        b ^= low
    return -1 if s % 2 else 1


def fmul(X, Y, top):
    out = {}
    for a, ca in X.items():
        for b, cb in Y.items():
            if a & b:
                continue
            if bin(a | b).count("1") > top:
                continue
            c = gmul(ca, cb)
            if wsign(a, b) < 0:
                c = (-c[0], -c[1])
            out[a | b] = gadd(out.get(a | b, (Fr(0), Fr(0))), c)
    return {k: v for k, v in out.items() if v != (0, 0)}


def fexp(D, top):
    res = {0: (Fr(1), Fr(0))}
    term = {0: (Fr(1), Fr(0))}
    k = 0
    while True:
        k += 1
        term = fmul(term, D, top)
        if not term:
            break
        term = {m: (c[0] / k, c[1] / k) for m, c in term.items()}
        for m, c in term.items():
            res[m] = gadd(res.get(m, (Fr(0), Fr(0))), c)
    return {k: v for k, v in res.items() if v != (0, 0)}


MU4 = [(1, 0), (0, 1), (-1, 0), (0, -1)]      # i^k


def dzz(n, k, l):
    """bitmask of dz_k ^ dzbar_l (0-based), generators dz_0.. then dzbar_0.."""
    return (1 << k) | (1 << (2 * n + l)), (1 if (2 * n + l) > k else -1)


def c1form(n, H):
    """(i/2) sum H_kl dz_k ^ dzbar_l for a Gaussian-integer hermitian H."""
    out = {}
    for k in range(2 * n):
        for l in range(2 * n):
            h = H[k][l]
            if h == (0, 0):
                continue
            m, s = dzz(n, k, l)
            c = gmul((Fr(0), Fr(1, 2)), (Fr(h[0]), Fr(h[1])))
            c = (s * c[0], s * c[1])
            out[m] = gadd(out.get(m, (Fr(0), Fr(0))), c)
    return {k: v for k, v in out.items() if v != (0, 0)}


def weil_alpha(n, conj=False):
    X = {0: (Fr(1), Fr(0))}
    for j in range(n):
        k, l = (j, n + j) if not conj else (n + j, j)
        m, s = dzz(n, k, l)
        X = fmul(X, {m: (Fr(0), Fr(s, 2))}, 4 * n)
    return X


def pieces_H(n, p):
    out = []
    for z in itertools.product(range(4), repeat=n):
        if sum(z) % 2:
            continue
        H = [[(0, 0)] * (2 * n) for _ in range(2 * n)]
        for j in range(n):
            H[j][j] = (p, 0)
            H[n + j][n + j] = (p, 0)
            H[j][n + j] = MU4[z[j]]
            H[n + j][j] = (MU4[z[j]][0], -MU4[z[j]][1])
        out.append((z, H, 1 if sum(z) % 4 == 0 else -1))
    return out


def part_A():
    print("(A) the pure Weil character")
    for n in (2, 3):
        for p in (0, 1, -3):
            tot = {}
            P = pieces_H(n, p)
            for z, H, s in P:
                e = fexp(c1form(n, H), 4 * n)
                for m, c in e.items():
                    tot[m] = gadd(tot.get(m, (Fr(0), Fr(0))), (s * c[0], s * c[1]))
            tot = {k: v for k, v in tot.items() if v != (0, 0)}
            a = weil_alpha(n)
            ab = weil_alpha(n, True)
            want = {}
            for X in (a, ab):
                for m, c in X.items():
                    want[m] = gadd(want.get(m, (Fr(0), Fr(0))),
                                   (2 * 4 ** (n - 1) * c[0], 2 * 4 ** (n - 1) * c[1]))
            want = {k: v for k, v in want.items() if v != (0, 0)}
            check("(A) n = %d, p = %d: %d pieces, sum of signed e^{D_zeta} is "
                  "exactly 2 4^(n-1) (alpha + conj alpha)" % (n, p, len(P)),
                  tot == want and len(P) == 2 * 4 ** (n - 1))
            # alpha is real up to conjugation: conj(alpha) is the second product
    # per-surface identity sum_z z e^{D(z)} = 4 c' with c' = (i/2) dz_2 ^ dzbar_1
    n = 1
    ok = True
    for p in range(-3, 4):
        tot = {}
        for k in range(4):
            H = [[(p, 0), MU4[k]], [(MU4[k][0], -MU4[k][1]), (p, 0)]]
            e = fexp(c1form(n, H), 4)
            for m, c in e.items():
                tot[m] = gadd(tot.get(m, (Fr(0), Fr(0))), gmul(MU4[k], c))
        tot = {k: v for k, v in tot.items() if v != (0, 0)}
        m, s = dzz(1, 1, 0)
        ok &= tot == {m: (Fr(0), Fr(4 * s, 2))}
    check("(A) on one surface, sum over z in mu_4 of z e^{D(z)} = 4 (i/2) "
          "dz_2 ^ dzbar_1 for p = -3..3", ok)


# ----------------------------------------------------------------------
# (B) Hankel rank, counts

def part_B():
    print("(B) Hankel rank and counts")
    for n in (3, 4):
        for ts, sg in (((2, 4, 6), (1, -1, 1)), ((-2, 2, 5), (1, 1, -1)),
                       ((0, 3, 7), (-1, 1, 1))):
            mu = [sum(s * sp.Integer(t) ** m for t, s in zip(ts, sg))
                  for m in range(2 * n + 1)]
            H = sp.Matrix(2 * n - 1, 3, lambda j, i: mu[j + i])
            check("(B) n = %d, t = %s: Hankel rank 3" % (n, ts), H.rank() == 3)
    for n, r in ((2, 24), (3, 57), (4, 104)):
        check("(B) r = 7n^2 - 2n = %d at n = %d" % (r, n), 7 * n * n - 2 * n == r)
    npc = {n: 2 * 4 ** (n - 1) + 3 for n in (3, 4)}
    check("(B) 35 pieces at n = 3 and 131 at n = 4", npc == {3: 35, 4: 131})
    check("(B) diagonal classes: 35 C(6,2) = 525 and 131 C(8,2) = 3668",
          35 * comb(6, 2) == 525 and 131 * comb(8, 2) == 3668)
    check("(B) the gap at n = 3: 525 - 57 = 468", 525 - 57 == 468)


# ----------------------------------------------------------------------
# (C) first-order kernel on divisor classes

def part_C():
    print("(C) the first-order kernel on H^{1,1}")
    for n in (2, 3, 4):
        g = 2 * n
        vs = []
        for k in range(g):
            for l in range(k + 1, g):
                if (k < n) != (l < n):
                    v = sp.zeros(g, g)
                    v[k, l] = 1
                    v[l, k] = 1
                    vs.append(v)
        cs = sp.symbols("c0:%d" % (g * g))
        C = sp.Matrix(g, g, cs)
        rows = []
        for v in vs:
            M = v.T * C
            for a in range(g):
                for b in range(a + 1, g):
                    e = sp.expand(M[a, b] - M[b, a])
                    rows.append([e.coeff(c) for c in cs])
        A = sp.Matrix(rows)
        ns = A.nullspace()
        ok = len(vs) == n * n and len(ns) == 1 and \
            sp.Matrix(g, g, list(ns[0])) == ns[0][0] * sp.eye(g)
        check("(C) n = %d: the %d tangent vectors of the polarised family "
              "kill exactly C theta in H^{1,1}" % (n, n * n), ok)


# ----------------------------------------------------------------------
# (D) index lemma

def part_D():
    print("(D) the index lemma")
    import numpy as np
    rng = np.random.default_rng(32)
    ok_sub = True
    for _ in range(3000):
        g = int(rng.integers(2, 7))
        X = rng.normal(size=(g, g)) + 1j * rng.normal(size=(g, g))
        Y = rng.normal(size=(g, g)) + 1j * rng.normal(size=(g, g))
        X = X + X.conj().T
        Y = Y + Y.conj().T
        n_ = lambda M: int((np.linalg.eigvalsh(M) < -1e-9).sum())
        ok_sub &= n_(X + Y) <= n_(X) + n_(Y)
    check("(D) n(X + Y) <= n(X) + n(Y) on 3000 random hermitian pairs", ok_sub)
    ok_loop = True
    for _ in range(2000):
        g = int(rng.integers(2, 7))
        k = int(rng.integers(2, 7))
        Hs = []
        for _ in range(k - 1):
            X = rng.normal(size=(g, g)) + 1j * rng.normal(size=(g, g))
            Hs.append(X + X.conj().T)
        Hs.append(-sum(Hs))
        ev = [np.linalg.eigvalsh(H) for H in Hs]
        if min(abs(e).min() for e in ev) < 1e-6:
            continue
        ok_loop &= sum(int((e < 0).sum()) for e in ev) >= g
    check("(D) nondegenerate H_1 + ... + H_k = 0 has sum of indices >= g "
          "(2000 random loops)", ok_loop)


# ----------------------------------------------------------------------
# chain model shared by (E), (G), (H), (J)

def setup(n, p, Ts, Msigns):
    pieces = []
    for z in itertools.product(range(4), repeat=n):
        s = sum(z) % 4
        if s in (0, 2):
            pieces.append((tuple(('L', k) for k in z), 1 if s == 0 else -1))
    for t, sg in zip(Ts, Msigns):
        pieces.append((tuple(('M', t) for _ in range(n)), sg))
    return pieces


def degset(o1, o2, p):
    """per-surface degrees of the cohomology of Hom(o1, o2); None when equal."""
    if o1 == o2:
        return None
    (x, a), (y, b) = o1, o2
    if x == 'L' and y == 'L':
        return (1,)

    def fromeig(e1, e2):
        neg = (e1 < 0) + (e2 < 0)
        if e1 == 0 or e2 == 0:
            return (neg, neg + 1)
        return (neg,)
    if x == 'L' and y == 'M':
        return fromeig(b - p + 1, b - p - 1)
    if x == 'M' and y == 'L':
        return fromeig(p - a + 1, p - a - 1)
    return (0,) if b > a else (2,)


class Config:
    def __init__(s, n, p, Ts, Msigns):
        s.n = n
        s.p = p
        s.pieces = setup(n, p, Ts, Msigns)
        s.N = len(s.pieces)
        s.opts = {}
        for a in range(s.N):
            for b in range(s.N):
                if a == b:
                    continue
                pa, pb = s.pieces[a][0], s.pieces[b][0]
                choices = []
                for j in range(n):
                    ds = degset(pa[j], pb[j], p)
                    if ds is None:
                        choices.append([(0, 0), (1, 1), (2, 1)])
                    else:
                        choices.append([(d, 1) for d in ds])
                s.opts[(a, b)] = list(itertools.product(*choices))
        s.flip = [[s.pieces[a][1] != s.pieces[b][1] for b in range(s.N)]
                  for a in range(s.N)]

    def target_range(s, a, b):
        pa, pb = s.pieces[a][0], s.pieces[b][0]
        out = []
        for j in range(s.n):
            ds = degset(pa[j], pb[j], s.p)
            out.append((0, 1, 2) if ds is None else ds)
        return out

    def isM(s, i):
        return s.pieces[i][0][0][0] == 'M'


def feasible(n, k, sdeg, u, qranges):
    lo = hi = 0
    for j in range(n):
        dmax = max(0, u[j] - 2)
        ds = [sdeg[j] - q for q in qranges[j] if 0 <= sdeg[j] - q <= dmax]
        if not ds:
            return False
        lo += min(ds)
        hi += max(ds)
    return lo <= k - 2 <= hi


def taus(n, m):
    return [t for t in itertools.product(range(3), repeat=n) if sum(t) == m]


def step_options(C, a, b, w):
    out = []
    par = (w + C.flip[a][b]) % 2
    for c in C.opts[(a, b)]:
        h = sum(d for d, _ in c)
        if h % 2 == par:
            out.append((h, tuple(d for d, _ in c), tuple(nu for _, nu in c)))
    return out


def min_step_excess(C):
    ex = {}
    for (a, b) in C.opts:
        o = step_options(C, a, b, 1)
        ex[(a, b)] = min(h for h, _, _ in o) - 1 if o else None
    return ex


def min_closed_walk(C):
    INF = 10 ** 9
    N = C.N
    ex = min_step_excess(C)
    d = [[INF] * N for _ in range(N)]
    for (a, b), v in ex.items():
        if v is not None:
            d[a][b] = v
    for k in range(N):
        dk = d[k]
        for i in range(N):
            dik = d[i][k]
            if dik >= INF:
                continue
            di = d[i]
            for j in range(N):
                v = dik + dk[j]
                if v < di[j]:
                    di[j] = v
    return min(d[i][i] for i in range(N))


def make_future(C):
    Ms = [i for i in range(C.N) if C.isM(i)]
    Ls = [i for i in range(C.N) if not C.isM(i)]
    so = {k: step_options(C, k[0], k[1], 1) for k in C.opts}
    mc = {k: (min(h for h, _, _ in v) - 1 if v else None) for k, v in so.items()}
    LM = {t: min(mc[(l, t)] for l in Ls if mc[(l, t)] is not None) for t in Ms}
    ML = {t: min(mc[(t, l)] for l in Ls if mc[(t, l)] is not None) for t in Ms}

    @lru_cache(None)
    def fut(cur_is_M, cur, unv):
        best = 0
        for t in unv:
            c = mc[(cur, t)] if cur_is_M else LM[t]
            if c is None:
                continue
            best = min(best, c + fut(True, t, tuple(x for x in unv if x != t)))
        if cur_is_M:
            best = min(best, ML[cur] + fut(False, -1, unv))
        return best
    return so, fut, Ms


def future(C):
    """make_future(C), computed once per configuration."""
    if not hasattr(C, "_future"):
        C._future = make_future(C)
    return C._future


def outgoing_dp(C, m, starts, cap=12):
    """over-approximation (revisits of L pieces allowed) of the chains that
    carry a diagonal class of degree m out of the diagonal; returns
    (s, e, tau, k, cost)."""
    n = C.n
    hi = 2 * n - m - 1
    lo = -(m + 1)
    so, fut, Ms = future(C)
    cl = lambda v: tuple(min(x, cap) for x in v)
    found = set()
    for s in starts:
        start = (s, 0, (0,) * n, (0,) * n, 1, tuple(x for x in Ms if x != s))
        frontier = {start}
        seen = {start}
        while frontier:
            new = set()
            for (cur, cost, sd, u, npieces, unv) in frontier:
                if npieces >= 2:
                    tr = C.target_range(s, cur)
                    for tau in taus(n, m):
                        sdeg = tuple(x + t for x, t in zip(sd, tau))
                        uu = tuple(x + (1 if t > 0 else 0) for x, t in zip(u, tau))
                        if lo <= cost <= hi and feasible(n, npieces, sdeg, uu, tr):
                            found.add((s, cur, tau, npieces, cost))
                for nxt in range(C.N):
                    if nxt == cur or nxt == s:
                        continue
                    if C.isM(nxt) and nxt not in unv:
                        continue
                    unv2 = tuple(x for x in unv if x != nxt)
                    for h, dg, nu in so[(cur, nxt)]:
                        c2 = cost + h - 1
                        f = fut(C.isM(nxt), nxt if C.isM(nxt) else -1, unv2)
                        if c2 + f > hi:
                            continue
                        st = (nxt, c2, cl(tuple(x + y for x, y in zip(sd, dg))),
                              cl(tuple(x + y for x, y in zip(u, nu))),
                              min(npieces + 1, cap), unv2)
                        if st not in seen:
                            seen.add(st)
                            new.add(st)
            frontier = new
    return found


def paths_exact(C, m, s, e, k, prune=True):
    """every path s -> ... -> e of k distinct pieces, with its step degrees
    and the type tau of the diagonal class, meeting the conditions above.
    With prune, a branch is cut as soon as the least excess of any
    continuation (fut, which visits the remaining M_i in the cheapest way)
    takes the total above hi; the output is the same."""
    n = C.n
    hi = 2 * n - m - 1
    lo = -(m + 1)
    so, fut, Ms = future(C)
    out = []
    tr = C.target_range(s, e)

    def dfs(path, degs, cost, sd, u):
        cur = path[-1]
        if prune:
            unv = tuple(x for x in Ms if x not in path)
            if cost + fut(C.isM(cur), cur if C.isM(cur) else -1, unv) > hi:
                return
        if len(path) == k:
            if cur != e or not (lo <= cost <= hi):
                return
            for tau in taus(n, m):
                sdeg = tuple(x + t for x, t in zip(sd, tau))
                uu = tuple(x + (1 if t > 0 else 0) for x, t in zip(u, tau))
                if feasible(n, k, sdeg, uu, tr):
                    out.append((tuple(path), tuple(degs), tau))
            return
        for nxt in range(C.N):
            if nxt in path:
                continue
            if len(path) == k - 1 and nxt != e:
                continue
            for h, dg, nu in so[(cur, nxt)]:
                dfs(path + [nxt], degs + [dg], cost + h - 1,
                    tuple(x + y for x, y in zip(sd, dg)),
                    tuple(x + y for x, y in zip(u, nu)))
    dfs([s], [], 0, (0,) * n, (0,) * n)
    return out


def mc_alternatives(C, a, b, c, maxk=6, prune=True):
    """the other paths a -> ... -> c of total excess -2 that contribute to
    the component of the Maurer-Cartan equation containing a -> b -> c.
    With prune the search stops at the first one and cuts a branch when no
    continuation can bring the excess down to -2; only emptiness is used."""
    n = C.n
    so, fut, Ms = future(C)
    res = []

    def dfs(path, cost, sd, u):
        if prune and res:
            return
        cur = path[-1]
        if cur == c:
            k = len(path) - 1
            if cost == -2 and not (k == 2 and path[1] == b):
                if k >= 2 and feasible(n, k, sd, u, [(0,)] * n):
                    res.append(tuple(path))
            return
        if len(path) > maxk:
            return
        if prune:
            unv = tuple(x for x in Ms if x not in path)
            if cost + fut(C.isM(cur), cur if C.isM(cur) else -1, unv) > -2:
                return
        for nxt in range(C.N):
            if nxt in path:
                continue
            for h, dg, nu in so[(cur, nxt)]:
                c2 = cost + h - 1
                if c2 > 4:
                    continue
                dfs(path + [nxt], c2, tuple(x + y for x, y in zip(sd, dg)),
                    tuple(x + y for x, y in zip(u, nu)))
    dfs([a], 0, (0,) * n, (0,) * n)
    return res


def mc_filter(C, pieces, degs, prune=True):
    if not hasattr(C, "_mcalt"):
        C._mcalt = {}
    for i in range(len(pieces) - 2):
        if all(d == 0 for d in degs[i]) and all(d == 0 for d in degs[i + 1]):
            key = (pieces[i], pieces[i + 1], pieces[i + 2], prune)
            if key not in C._mcalt:
                C._mcalt[key] = bool(mc_alternatives(C, *key[:3], prune=prune))
            if not C._mcalt[key]:
                return False
    return True


def piece_name(C, x):
    if C.isM(x):
        return 'M%d%s' % (C.pieces[x][0][0][1], '+' if C.pieces[x][1] > 0 else '-')
    return 'L' + ('+' if C.pieces[x][1] > 0 else '-')


def higher_shapes(n, p, Ts, Ms, prune=True):
    C = Config(n, p, Ts, Ms)
    Lp = [i for i in range(C.N) if not C.isM(i) and C.pieces[i][1] == 1][0]
    Lm = [i for i in range(C.N) if not C.isM(i) and C.pieces[i][1] == -1][0]
    Mi = [i for i in range(C.N) if C.isM(i)]
    r = outgoing_dp(C, 2, [Lp, Lm] + Mi)
    hk = sorted(set((s, e, k) for s, e, tau, k, cost in r if k >= 3))
    surv = []
    for s, e, k in hk:
        for pieces, degs, tau in paths_exact(C, 2, s, e, k, prune):
            if mc_filter(C, pieces, degs, prune):
                surv.append((pieces, degs, tau))
    shapes = sorted(set(' -> '.join(piece_name(C, x) for x in pc)
                        for pc, _, _ in surv))
    return len(hk), shapes, surv, C


# ----------------------------------------------------------------------
# (E) excess of loops

def part_E():
    print("(E) the excess of a loop")
    for n, Ts in ((3, (2, 4, 6)), (3, (-2, 2, 4)), (3, (-6, -4, -2)),
                  (3, (2, 3, 7)), (4, (2, 4, 6)), (4, (-2, 3, 5))):
        for sg in ((1, -1, 1), (1, 1, -1), (-1, -1, -1)):
            C = Config(n, 0, list(Ts), list(sg))
            w = min_closed_walk(C)
            check("(E) n = %d, t = %s, signs %s: every closed walk of "
                  "degree-one steps has excess >= 1 (least %d)" % (n, Ts, sg, w),
                  w >= 1)
    C = Config(3, 0, [], [])
    ex = min_step_excess(C)
    check("(E) n = 3: every step between two Weil pieces has excess >= 1",
          all(v is None or v >= 1 for v in ex.values()))
    C = Config(2, 0, [2, 4, 6], [1, -1, 1])
    w = min_closed_walk(C)
    check("(E) n = 2: a closed walk of excess %d <= 0 exists, so n >= 3 is "
          "needed" % w, w <= 0)


# ----------------------------------------------------------------------
# (F) degree drop on trees

def trees(leaves):
    """full binary trees on the ordered leaf tuple; a tree is a leaf index
    or a pair (left, right)."""
    if len(leaves) == 1:
        return [leaves[0]]
    out = []
    for i in range(1, len(leaves)):
        for L in trees(leaves[:i]):
            for R in trees(leaves[i:]):
                out.append((L, R))
    return out


def subtree_sets(T, root=True, acc=None):
    """leaf sets below the internal non-root nodes."""
    if acc is None:
        acc = []
    if isinstance(T, int):
        return {T}, acc
    l, _ = subtree_sets(T[0], False, acc)
    r, _ = subtree_sets(T[1], False, acc)
    s = l | r
    if not root:
        acc.append(frozenset(s))
    return s, acc


def part_F():
    print("(F) the degree drop")
    ok = True
    sharp = {}
    for k in range(2, 9):
        for T in trees(tuple(range(k))):
            _, sets = subtree_sets(T)
            for u in range(0, k + 1):
                for U in itertools.combinations(range(k), u):
                    U = frozenset(U)
                    Ns = set(S & U for S in sets)
                    good = [N for N in Ns if len(N) >= 2 and N != U]
                    bound = max(0, u - 2)
                    ok &= len(good) <= bound
                    sharp[u] = max(sharp.get(u, 0), len(good))
    check("(F) binary trees with 2..8 leaves: at most max(0, u - 2) distinct "
          "marked sets of size >= 2 other than the full set", ok)
    check("(F) the bound is attained for u = 2..8",
          all(sharp[u] == max(0, u - 2) for u in range(2, 9)), "%s" % sharp)


# ----------------------------------------------------------------------
# (G) cup kernel at n = 3

def part_G():
    print("(G) the cup products on the diagonal at n = 3")
    P = 1000003
    n = 3
    gens = 2 * n
    pairs = [(a, b) for a in range(gens) for b in range(a + 1, gens)]
    pidx = {pr: i for i, pr in enumerate(pairs)}
    fac = lambda g: g // 2
    pcs = [z for z in itertools.product(range(4), repeat=n) if sum(z) % 2 == 0]
    N = len(pcs)
    # which pairs can carry a nonzero cup product on a class of type tau
    # (per-surface degrees tau, |tau| = 2), from the degrees and the parity
    def cup_possible(a, b, tau):
        D = [j for j in range(n) if a[j] != b[j]]
        S = [j for j in range(n) if a[j] == b[j]]
        if any(tau[j] for j in D):
            return False
        flip = (sum(a) - sum(b)) % 4 != 0
        # delta: degree 1 on D, e_j in {0,1,2} on S with e_j + tau_j <= 2
        for e in itertools.product(range(3), repeat=len(S)):
            if any(e[i] + tau[S[i]] > 2 for i in range(len(S))):
                continue
            h = len(D) + sum(e)
            if h % 2 != (1 + flip) % 2:
                continue
            # the product in a shared surface with tau_j = 1 needs e_j <= 1,
            # with tau_j = 2 needs e_j = 0; a surface with e_j = tau_j = 1 is
            # W ^ W, nonzero in general
            return True
        return False
    types = [t for t in itertools.product(range(3), repeat=n) if sum(t) == 2]
    ncomp = {}
    edge_kinds = set()
    for tau in types:
        par = list(range(N))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for ia in range(N):
            for ib in range(ia + 1, N):
                if cup_possible(pcs[ia], pcs[ib], tau):
                    par[find(ia)] = find(ib)
                    D = tuple(sorted((pcs[ib][j] - pcs[ia][j]) % 4
                                     for j in range(n) if pcs[ia][j] != pcs[ib][j]))
                    edge_kinds.add(D)
        ncomp[tau] = len(set(find(x) for x in range(N)))
    check("(G) cup products occur only between pieces differing by -1 in one "
          "coordinate or by (i, i), (-i, -i) in two",
          edge_kinds == {(2,), (1, 1), (3, 3)}, "%s" % sorted(edge_kinds))
    want = {t: (4 if 2 in t else 16) for t in types}
    check("(G) components: 4 for the types (2,0,0) and 16 for (1,1,0)",
          ncomp == want, "%s" % ncomp)
    lower = sum((1 if 2 in t else 4) * ncomp[t] for t in types)
    check("(G) so the kernel of the cup products on the 480 Weil diagonal "
          "classes is at least 12 + 192 = 204", lower == 204)
    # generic data: exact rank modulo a prime
    rng = random.Random(5)
    rows = []

    def w2x1(pr, g):
        if g in pr:
            return None, 0
        perm = [pr[0], pr[1], g]
        sg = 1
        for i in range(3):
            for j in range(i + 1, 3):
                if perm[i] > perm[j]:
                    sg = -sg
        return tuple(sorted(perm)), sg
    for ia, a in enumerate(pcs):
        for ib, b in enumerate(pcs):
            if ib <= ia:
                continue
            D = [j for j in range(n) if a[j] != b[j]]
            S = [j for j in range(n) if a[j] == b[j]]
            rat = [(b[j] - a[j]) % 4 for j in D]
            if len(D) == 1 and rat == [2]:
                for _ in range(4):
                    w = {g: rng.randrange(P) for g in range(gens) if fac(g) in S}
                    block = {}
                    for pr in pairs:
                        if fac(pr[0]) in S and fac(pr[1]) in S:
                            for g, c in w.items():
                                t, sg = w2x1(pr, g)
                                if t is None:
                                    continue
                                block.setdefault(t, {})
                                block[t][pr] = (block[t].get(pr, 0) + sg * c) % P
                    for t, ent in block.items():
                        row = {}
                        for pr, c in ent.items():
                            row[(ia, pidx[pr])] = c
                            row[(ib, pidx[pr])] = (-c) % P
                        rows.append(row)
            elif len(D) == 2 and rat in ([1, 1], [3, 3]):
                j = S[0]
                pr = (2 * j, 2 * j + 1)
                for _ in range(4):
                    c = rng.randrange(1, P)
                    rows.append({(ia, pidx[pr]): c, (ib, pidx[pr]): (-c) % P})
    cols = [(i, k) for i in range(N) for k in range(len(pairs))]
    cidx = {c: i for i, c in enumerate(cols)}
    M = []
    for row in rows:
        r = [0] * len(cols)
        for c, v in row.items():
            r[cidx[c]] = v % P
        M.append(r)
    rk = 0
    for c in range(len(cols)):
        piv = None
        for r in range(rk, len(M)):
            if M[r][c]:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], P - 2, P)
        M[rk] = [x * inv % P for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][c]:
                f = M[r][c]
                M[r] = [(x - f * y) % P for x, y in zip(M[r], M[rk])]
        rk += 1
    check("(G) generic data on all 48 + 96 pairs: cup rank 276, kernel "
          "480 - 276 = 204", rk == 276 and len(cols) - rk == 204,
          "rank %d of %d" % (rk, len(cols)))
    check("(G) with the 45 diagonal classes of the multiples, on which every "
          "cup product vanishes: 204 + 45 = 249", 204 + 3 * comb(6, 2) == 249)


# ----------------------------------------------------------------------
# (H) higher products at n = 3

def part_H():
    print("(H) the higher products on the diagonal at n = 3")
    nk, shapes, _, _ = higher_shapes(3, 0, [], [])
    check("(H) pure Weil pieces: no product of length >= 3 leaves the "
          "diagonal", nk == 0 and shapes == [])
    expect = {(1, -1, 1): ['M4- -> M6+ -> L- -> M2+'],
              (-1, 1, -1): ['M4+ -> M6- -> L+ -> M2-']}
    for sg in itertools.product([1, -1], repeat=3):
        nk, shapes, surv, C = higher_shapes(3, 0, [2, 4, 6], list(sg))
        want = expect.get(sg, [])
        detail = "%d candidate triples, surviving %s" % (nk, shapes)
        check("(H) t = (2, 4, 6) above p = 0, signs %s: surviving chains "
              "%s" % (sg, want if want else "none"), shapes == want, detail)
        if want:
            ok = all(len(pc) == 4 for pc, _, _ in surv)
            ok &= all([C.isM(x) for x in pc] == [True, True, False, True]
                      for pc, _, _ in surv)
            check("(H) signs %s: every survivor is M_{t2} -> M_{t3} -> L -> "
                  "M_{t1}, length four, landing in Hom(M_4, M_2)" % (sg,), ok)
    _, _, s0, _ = higher_shapes(3, 0, [2, 4, 6], [1, -1, 1], prune=False)
    _, _, s1, _ = higher_shapes(3, 0, [2, 4, 6], [1, -1, 1])
    check("(H) the pruned search finds the same %d surviving paths as the "
          "exhaustive one at t = (2, 4, 6), signs (1, -1, 1)" % len(s1),
          sorted(s0) == sorted(s1) and len(s1) == 96)
    part_H_mixed()


def flip_name(nm):
    """the name of a piece of the dual configuration E^vee[1]: the value
    t goes to -t and the sign changes."""
    sg = '-' if nm[-1] == '+' else '+'
    if nm[0] == 'L':
        return 'L' + sg
    return 'M%d%s' % (-int(nm[1:-1]), sg)


def dual_shapes(shapes):
    return sorted(' -> '.join(flip_name(x) for x in reversed(sh.split(' -> ')))
                  for sh in shapes)


def part_H_mixed():
    """placements on both sides of p (prop:mixedplacement)."""
    A, B = 'M2+ -> M4- -> M-2+ -> L-', 'M4- -> M-2+ -> L- -> M2+'
    expect = {(1, 1, -1): [A, B],
              (-1, -1, 1): ['M2- -> M4+ -> M-2- -> L+',
                            'M4+ -> M-2- -> L+ -> M2-']}
    for sg in itertools.product([1, -1], repeat=3):
        nk, shapes, surv, C = higher_shapes(3, 0, [-2, 2, 4], list(sg))
        want = expect.get(sg, [])
        check("(H) mixed placement t = (-2, 2, 4), signs %s: surviving "
              "chains %s" % (sg, want if want else "none"), shapes == want,
              "%d candidate triples, surviving %s" % (nk, shapes))
        if not want:
            continue
        t1, t2, t3 = [i for i in range(C.N) if C.isM(i)]
        ok_len = all(len(pc) == 4 for pc, _, _ in surv)
        pa = [(pc, dg) for pc, dg, _ in surv if pc[0] == t2]
        pb = [(pc, dg) for pc, dg, _ in surv if pc[0] == t3]
        ok_a = all(pc[1:3] == (t3, t1) and not C.isM(pc[3])
                   and C.pieces[pc[3]][1] == sg[2]
                   and dg == ((0, 0, 0), (2, 2, 2), (0, 0, 0))
                   for pc, dg in pa)
        ok_b = all(pc[1] == t1 and not C.isM(pc[2]) and pc[3] == t2
                   and C.pieces[pc[2]][1] == sg[2]
                   and dg == ((2, 2, 2), (0, 0, 0), (0, 0, 0))
                   for pc, dg in pb)
        check("(H) signs %s: every survivor has length four and is "
              "(a) M_{t2} -> M_{t3} -> M_{t1} -> L or (b) M_{t3} -> M_{t1} -> "
              "L -> M_{t2}, with Ext degrees 0, 6, 0 or 6, 0, 0 and "
              "prod zeta = sigma_3" % (sg,),
              ok_len and ok_a and ok_b and len(pa) + len(pb) == len(surv)
              and len(pa) > 0 and len(pb) > 0)
        ends = set(pc[3] for pc, _ in pa)
        check("(H) signs %s: the paths (a) end at all 16 pieces L_zeta with "
              "prod zeta = sigma_3, the paths (b) pass through all 16"
              % (sg,), len(ends) == 16
              and len(set(pc[2] for pc, _ in pb)) == 16)
        # shifts: a step of Ext degree q between a and b has degree one when
        # d_b = d_a + 1 - q; the signs are (-1)^d and the value lies in
        # H^{3 + d_s - d_e}
        ok = True
        for pc, dg in pa + pb:
            d = [0]
            for q in dg:
                d.append(d[-1] + 1 - sum(q))
            ok &= all(C.pieces[x][1] * C.pieces[pc[0]][1] == (-1) ** (dx % 2)
                      for x, dx in zip(pc, d))
            ok &= 3 + d[0] - d[-1] == 6
        check("(H) signs %s: the shifts forced by degree one give the signs "
              "of the pieces and put the value in H^6" % (sg,), ok)
        check("(H) signs %s: (a) puts M_{t2} before M_{t3} and (b) puts "
              "M_{t3} before M_{t2}, so no convolution carries both" % (sg,),
              all(pc.index(t2) < pc.index(t3) for pc, _ in pa)
              and all(pc.index(t3) < pc.index(t2) for pc, _ in pb))
    for Ts, Td in (([-2, 2, 4], [-4, -2, 2]), ([2, 4, 6], [-6, -4, -2])):
        ok = True
        for sg in itertools.product([1, -1], repeat=3):
            _, shapes, _, _ = higher_shapes(3, 0, list(Td), list(sg))
            src = tuple(-x for x in reversed(sg))
            _, shp, _, _ = higher_shapes(3, 0, list(Ts), list(src))
            ok &= shapes == dual_shapes(shp)
        check("(H) t = %s: for each of the eight sign patterns the survivors "
              "are the duals E^vee[1] of those at t = %s" % (tuple(Td), tuple(Ts)),
              ok)


# ----------------------------------------------------------------------
# (I) thresholds

def part_I():
    print("(I) thresholds")
    check("(I) 249 - 57 = 192 dimensions must come from the length-four "
          "products", 249 - 57 == 192)
    check("(I) their target Hom^3(M_{t2}, M_{t1}) has dimension "
          "(t2 - t1)^6: 1, 64, 729 for gaps 1, 2, 3",
          [g ** 6 for g in (1, 2, 3)] == [1, 64, 729])
    check("(I) so gaps 1, 2 leave dim Ext^2 >= 248, 185 > 57, and a gap of "
          "at least 3 is needed", 249 - 1 == 248 and 249 - 64 == 185
          and 64 < 192 <= 729)
    check("(I) (t2 - t1)^6 >= 192 exactly when t2 - t1 >= 3",
          all((g ** 6 >= 192) == (g >= 3) for g in range(1, 20)))
    ok = True
    for g in range(2, 8):
        for z in (1, sp.I, -1, -sp.I):
            H = sp.Matrix([[-g, z], [sp.conjugate(z), -g]])
            ev = sorted(H.eigenvals())
            ok &= ev == [-g - 1, -g + 1] and H.det() == g * g - 1
    check("(I) mixed placement: on each surface the difference of M_{t2} and "
          "L_zeta has eigenvalues p - t2 -+ 1 < 0 and determinant "
          "(t2 - p)^2 - 1, so the target of the paths (a) has dimension "
          "((t2 - p)^2 - 1)^3, 27 at t2 - p = 2", ok and (2 ** 2 - 1) ** 3 == 27)
    check("(I) its sixteen targets have dimension 16 ((t2 - p)^2 - 1)^3 >= "
          "432 >= 192, so the count leaves the paths (a) open; the paths (b) "
          "land in H^6(M_{t3}, M_{t2}) and need t3 - t2 >= 3",
          all(16 * ((g * g - 1) ** 3) >= 432 for g in range(2, 20))
          and 432 >= 192 and all((g ** 6 >= 192) == (g >= 3)
                                 for g in range(1, 20)))


# ----------------------------------------------------------------------
# (J) n = 4

def part_J():
    print("(J) n = 4")
    C = Config(4, 0, [], [])
    Lp = [i for i in range(C.N) if C.pieces[i][1] == 1][0]
    Lm = [i for i in range(C.N) if C.pieces[i][1] == -1][0]
    r = outgoing_dp(C, 2, [Lp, Lm])
    ks = sorted(set(k for s, e, tau, k, cost in r if k >= 3))
    ex = []
    for s, e, k in sorted(set((s, e, k) for s, e, tau, k, cost in r if k == 3))[:6]:
        for pc, dg, tau in paths_exact(C, 2, s, e, k):
            if mc_filter(C, pc, dg):
                ex.append((pc, dg, tau))
        if ex:
            break
    check("(J) n = 4, pure Weil pieces: chains of length 3 and 4 pass the "
          "bookkeeping", 3 in ks and 4 in ks, "lengths %s" % ks)
    check("(J) one of length three survives the Maurer-Cartan test",
          len(ex) > 0, ("%s" % (ex[0],)) if ex else "")


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
    part_J()
    print()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
