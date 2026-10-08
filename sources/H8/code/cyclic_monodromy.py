"""Item (LXXVI): monodromy of cyclic covers of degree 3, 4 and 6.

Setting.  For m in {3, 4, 6} and a = (a_1, ..., a_k) with a_i in Z/m
nonzero, sum a_i = 0 and gcd(m, a_1, ..., a_k) = 1 (a has order m), let D_a
be the cyclic cover y^m = prod (t - lambda_i)^{a_i} of the line and V_a the
eigenspace of H_1(D_a) on which the deck transformation acts by a primitive
m-th root of unity; dim V_a = n = k - 2, with Hodge numbers
p = -1 + sum <-a_i/m>, q = n - p.

The model.  With F_k = <x_1, ..., x_k> the fundamental group of the plane
minus the k points and t_i = zeta^{a_i} the monodromy of the local system,
H_1(F_k, L) is the kernel of d(e_i) = t_i - 1 on K^k, K = Q(zeta_m), and V_a
is its quotient by the loop around infinity, l = sum t_1...t_{i-1} e_i.  A
pure braid acts on F_k by Artin's automorphisms and on K^k by its Fox
Jacobian evaluated at x_i -> t_i; the formula sum_j (dw/dx_j)(x_j - 1) =
w - 1 shows that the kernel and l are preserved.

Paper: prop:cyclicmonodromy, lem:cabling, lem:hyperplanes, lem:merge and
lem:newdisc in tex/sections/11b_closuregraph.tex, used in
thm:vgvandermonde.  Everything below is exact arithmetic in Q(zeta_m).

  (A) the model: each generator A_st of the pure braid group acts on V_a as
      a pseudo-reflection with determinant (t_s t_t)^{+-1}, the full twist of
      a block of points with sum zero as a transvection (rank one, square
      zero), for every a of order m with k = 5, 6;
  (B) the base of the induction: for every a of order m in {3, 4, 6} with
      n = 3 or 4 and p, q >= 1 (up to order and sign), the logarithms of the
      transvections of (A), with brackets and conjugation by the A_st,
      span sl(V_a), of dimension n^2 - 1;
  (C) the induction step in the model, for k = 5, ..., 9 points: the cycle
      I = (1 - t_2) e_1 - (1 - t_1) e_2 of a disk around the first two points
      and the cycles outside it, {v_2 = t_1 v_1}, split the kernel when
      t_1 t_2 != 1; the cabled braids act on the cycles outside as the braids
      of a' = (a_1 + a_2, a_3, ...) and on I by a root of unity; the full
      twist of the second and third points moves both the line of I and the
      hyperplane of the cycles outside;
  (D) the merge lemma, proved by hand in the paper: every a of order m with
      k >= 7 and p, q >= 1 has two coordinates with a_i + a_j != 0 whose
      merge keeps the order m and p, q >= 1; checked for every k <= 40
      (k <= 30 for m = 6);
  (E) the discriminant of the new part (lem:newdisc): the determinant of the
      trace form of a hermitian lattice over Z[i], |det Tr(v^T M w / 2i)| =
      det(M)^2; 2 is a norm from Q(i) and not from Q(sqrt(-3)); the genus
      of the quotient curves, and the balanced characters of degree six
      with an odd number of coordinates 3, which exist from N = 7 on;
  (F) the very general count for d in {4, 6}: Hodge classes of degree r by
      enumeration of the characters against 1 + C(N+1, r+2) T_d(r+2), plus
      sum_{j > r/2 + 1} C(N+1, 2j) for d even, where T_d(k) is the number of
      sequences in {1, ..., d-1}^k with sum dk/2 (the balanced characters
      with support of size k), and against h^{r/2,r/2}.
"""
import itertools
import math
import random
import sys
from fractions import Fraction as Fr

from diagonal_ci import hodge_middle_ci

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ---------------------------------------------------------------- Q(zeta_m)

class Cyc:
    """x + y zeta in Q(zeta_m), m in {3, 4, 6}, zeta^2 = A zeta - 1"""
    A = {3: -1, 4: 0, 6: 1}
    __slots__ = ("m", "x", "y")

    def __init__(self, m, x, y=0):
        self.m, self.x, self.y = m, Fr(x), Fr(y)

    def __add__(self, o):
        o = self._c(o)
        return Cyc(self.m, self.x + o.x, self.y + o.y)

    __radd__ = __add__

    def __neg__(self):
        return Cyc(self.m, -self.x, -self.y)

    def __sub__(self, o):
        return self + (-self._c(o))

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        A = Cyc.A[self.m]
        return Cyc(self.m, self.x * o.x - self.y * o.y,
                   self.x * o.y + self.y * o.x + A * self.y * o.y)

    __rmul__ = __mul__

    def conj(self):
        # conj(zeta) = zeta^{-1} = A - zeta
        A = Cyc.A[self.m]
        return Cyc(self.m, self.x + A * self.y, -self.y)

    def norm(self):
        A = Cyc.A[self.m]
        return self.x * self.x + A * self.x * self.y + self.y * self.y

    def inv(self):
        n = self.norm()
        c = self.conj()
        return Cyc(self.m, c.x / n, c.y / n)

    def __truediv__(self, o):
        return self * self._c(o).inv()

    def __eq__(self, o):
        o = self._c(o)
        return self.x == o.x and self.y == o.y

    def __hash__(self):
        return hash((self.m, self.x, self.y))

    def __bool__(self):
        return self.x != 0 or self.y != 0

    def _c(self, o):
        return o if isinstance(o, Cyc) else Cyc(self.m, o)

    def __repr__(self):
        return "(%s%+s z)" % (self.x, self.y)


def zpow(m, e):
    z, r = Cyc(m, 0, 1), Cyc(m, 1)
    for _ in range(e % m):
        r = r * z
    return r


# ---------------------------------------------------------------- linear algebra

def zeros(m, r, c):
    return [[Cyc(m, 0) for _ in range(c)] for _ in range(r)]


def eye(m, n):
    M = zeros(m, n, n)
    for i in range(n):
        M[i][i] = Cyc(m, 1)
    return M


def mul(A, B):
    m = A[0][0].m
    n, p, q = len(A), len(B), len(B[0])
    C = zeros(m, n, q)
    for i in range(n):
        Ai = A[i]
        for k in range(p):
            a = Ai[k]
            if a:
                Bk = B[k]
                Ci = C[i]
                for j in range(q):
                    if Bk[j]:
                        Ci[j] = Ci[j] + a * Bk[j]
    return C


def sub(A, B):
    return [[a - b for a, b in zip(r, s)] for r, s in zip(A, B)]


def inverse(M):
    m, n = M[0][0].m, len(M)
    A = [list(r) + list(e) for r, e in zip(M, eye(m, n))]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c])
        A[c], A[piv] = A[piv], A[c]
        p = A[c][c].inv()
        A[c] = [x * p for x in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [r[n:] for r in A]


def det(M):
    m, n = M[0][0].m, len(M)
    A = [list(r) for r in M]
    d = Cyc(m, 1)
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c]), None)
        if piv is None:
            return Cyc(m, 0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = -d
        d = d * A[c][c]
        p = A[c][c].inv()
        for i in range(c + 1, n):
            if A[i][c]:
                f = A[i][c] * p
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return d


class Span:
    """row-echelon span of vectors over Q(zeta_m)"""

    def __init__(self, m, length):
        self.m, self.length = m, length
        self.rows = []          # (pivot, normalised row)

    def reduce(self, v):
        v = list(v)
        for piv, r in self.rows:
            if v[piv]:
                f = v[piv]
                v = [x - f * y for x, y in zip(v, r)]
        return v

    def add(self, v):
        v = self.reduce(v)
        piv = next((i for i, x in enumerate(v) if x), None)
        if piv is None:
            return False
        p = v[piv].inv()
        v = [x * p for x in v]
        new = []
        for q, r in self.rows:
            if r[piv]:
                f = r[piv]
                r = [x - f * y for x, y in zip(r, v)]
            new.append((q, r))
        self.rows = new + [(piv, v)]
        return True

    def dim(self):
        return len(self.rows)


def rank(M):
    if not M:
        return 0
    S = Span(M[0][0].m, len(M[0]))
    for r in M:
        S.add(r)
    return S.dim()


# ---------------------------------------------------------------- free group, Artin action, Fox calculus

def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def inv_word(w):
    return [-x for x in reversed(w)]


def sigma_image(i, eps, j):
    """image of the generator x_j (1-based) under sigma_i^eps"""
    if eps == 1:
        if j == i:
            return [i, i + 1, -i]
        if j == i + 1:
            return [i]
    else:
        if j == i:
            return [i + 1]
        if j == i + 1:
            return [-(i + 1), i, i + 1]
    return [j]


def apply_gen(g, w):
    i, eps = g
    out = []
    for x in w:
        img = sigma_image(i, eps, abs(x))
        out.extend(img if x > 0 else inv_word(img))
    return reduce_word(out)


def automorphism(braid, k):
    """images of x_1, ..., x_k under the braid word (list of (i, +-1))"""
    imgs = []
    for j in range(1, k + 1):
        w = [j]
        for g in reversed(braid):
            w = apply_gen(g, w)
        imgs.append(w)
    return imgs


def is_pure(imgs):
    """each x_j goes to a conjugate of x_j"""
    for j, w in enumerate(imgs, 1):
        n = len(w)
        if n % 2 == 0 or w[n // 2] != j:
            return False
        if w[:n // 2] != inv_word(w[n // 2 + 1:]):
            return False
    return True


def fox_jacobian(imgs, t):
    """J[i][j] = d imgs[i] / d x_j at x -> t (t a list of Cyc)"""
    m, k = t[0].m, len(t)
    tinv = [x.inv() for x in t]
    J = zeros(m, k, k)
    for i, w in enumerate(imgs):
        P = Cyc(m, 1)
        for x in w:
            j = abs(x) - 1
            if x > 0:
                J[i][j] = J[i][j] + P
                P = P * t[j]
            else:
                P = P * tinv[j]
                J[i][j] = J[i][j] - P
    return J


def pure_generator(s, t):
    """A_st = sigma_{t-1} ... sigma_{s+1} sigma_s^2 sigma_{s+1}^-1 ... (1-based)"""
    left = [(i, 1) for i in range(t - 1, s, -1)]
    return left + [(s, 1), (s, 1)] + [(i, -1) for i in range(s + 1, t)]


def block_twist(s, t):
    """full twist of the consecutive points s, ..., t"""
    return [(i, 1) for i in range(s, t)] * (t - s + 1)


class Model:
    """the monodromy of V_a in the Fox model"""

    def __init__(self, m, a):
        self.m, self.a, self.k = m, list(a), len(a)
        self.t = [zpow(m, x) for x in a]
        k, t = self.k, self.t
        # basis of ker d: b_l = (t_{l+1} - 1) e_l - (t_l - 1) e_{l+1}
        self.B = []
        for l in range(k - 1):
            v = [Cyc(m, 0) for _ in range(k)]
            v[l] = t[l + 1] - 1
            v[l + 1] = -(t[l] - 1)
            self.B.append(v)
        P, ell = Cyc(m, 1), []
        for x in t:
            ell.append(P)
            P = P * x
        assert P == 1
        self.ell = ell
        c = self.coords(ell)
        self.p0 = next(i for i, x in enumerate(c) if x)
        rows = [c] + [[Cyc(m, 1 if j == i else 0) for j in range(k - 1)]
                      for i in range(k - 1) if i != self.p0]
        self.Pm = rows
        self.Pinv = inverse(rows)

    def coords(self, w):
        """coordinates of w in ker d in the basis b"""
        k, t = self.k, self.t
        c = []
        for l in range(k - 1):
            val = w[l]
            if l > 0:
                val = val + c[l - 1] * (t[l - 1] - 1)
            c.append(val / (t[l + 1] - 1))
        last = -c[k - 2] * (t[k - 2] - 1)
        assert last == w[k - 1], "not in the kernel"
        return c

    def on_kernel(self, J):
        """matrix of v -> vJ on ker d, rows = images of b_l in basis b"""
        return [self.coords(mul([b], J)[0]) for b in self.B]

    def on_V(self, J):
        M = self.on_kernel(J)
        Mp = mul(mul(self.Pm, M), self.Pinv)
        # the loop at infinity is fixed
        assert Mp[0][0] == 1 and not any(Mp[0][1:])
        return [r[1:] for r in Mp[1:]]

    def braid_on_V(self, braid):
        imgs = automorphism(braid, self.k)
        assert is_pure(imgs)
        return self.on_V(fox_jacobian(imgs, self.t))

    def vector_to_V(self, w):
        """class in V of a vector of ker d, in the quotient basis"""
        c = self.coords(w)
        cp = mul([c], self.Pinv)[0]
        return cp[1:]


def hodge_p(m, a):
    return sum(Fr((-x) % m, m) for x in a) - 1


def order_of(m, a):
    return m // math.gcd(m, *a)


def lie_closure(m, n, seeds, conj, limit):
    """dimension of the span of seeds closed under brackets and X -> g X g^-1"""
    S = Span(m, n * n)
    basis, frontier = [], []
    for X in seeds:
        if S.add([x for r in X for x in r]):
            basis.append(X)
            frontier.append(X)
    while frontier and S.dim() < limit:
        new = []
        for X in frontier:
            cands = [mul(mul(g, X), gi) for g, gi in conj]
            cands += [sub(mul(X, Y), mul(Y, X)) for Y in basis]
            for Y in cands:
                if S.add([x for r in Y for x in r]):
                    basis.append(Y)
                    new.append(Y)
                    if S.dim() >= limit:
                        break
            if S.dim() >= limit:
                break
        frontier = new
    return S.dim()


def multisets(m, k):
    """multisets of nonzero residues mod m of size k, sum 0, order m,
    one representative of each pair {a, -a}"""
    seen = set()
    for a in itertools.combinations_with_replacement(range(1, m), k):
        if sum(a) % m or order_of(m, a) != m:
            continue
        b = tuple(sorted((-x) % m for x in a))
        if b in seen:
            continue
        seen.add(a)
        yield a


# ---------------------------------------------------------------- (A), (B)

def transvection_seeds(M):
    """logarithms of the unipotent block twists, consecutive blocks of the
    ordering and of its rotations"""
    m, k, a = M.m, M.k, M.a
    n = k - 2
    I = eye(m, n)
    seeds = []
    for s in range(1, k + 1):
        for t in range(s + 1, k + 1):
            if t - s + 1 > k - 2 or sum(a[s - 1:t]) % m:
                continue
            T = M.braid_on_V(block_twist(s, t))
            N = sub(T, I)
            seeds.append(N)
    return seeds


def pure_generators(M):
    gens = []
    for s in range(1, M.k + 1):
        for t in range(s + 1, M.k + 1):
            g = M.braid_on_V(pure_generator(s, t))
            gens.append((g, inverse(g)))
    return gens


def part_A():
    ok, count = True, 0
    for m in (3, 4, 6):
        for k in (5, 6):
            for a in multisets(m, k):
                M = Model(m, a)
                n = k - 2
                I = eye(m, n)
                for s in range(1, k + 1):
                    for t in range(s + 1, k + 1):
                        g = M.braid_on_V(pure_generator(s, t))
                        N = sub(g, I)
                        ok &= rank(N) == 1
                        dg = det(g)
                        ts = M.t[s - 1] * M.t[t - 1]
                        ok &= dg == ts or dg == ts.inv()
                for s in range(1, k + 1):
                    for t in range(s + 1, k + 1):
                        if t - s + 1 > k - 2 or sum(a[s - 1:t]) % m:
                            continue
                        T = M.braid_on_V(block_twist(s, t))
                        N = sub(T, I)
                        ok &= rank(N) == 1
                        ok &= not any(x for r in mul(N, N) for x in r)
                count += 1
    check("(A) the model: the generators A_st act as pseudo-reflections of "
          "determinant (t_s t_t)^{+-1}, full twists of blocks with sum zero as "
          "transvections, k = 5, 6, m = 3, 4, 6", ok, "%d characters" % count)


def base_case(m, a):
    M = Model(m, a)
    n = M.k - 2
    seeds = transvection_seeds(M)
    if not seeds:
        return None
    conj = pure_generators(M)
    return lie_closure(m, n, seeds, conj, n * n - 1)


def part_B():
    ok, table, nos = True, [], []
    for m in (3, 4, 6):
        for k in (5, 6):
            n = k - 2
            tot = 0
            for a in multisets(m, k):
                p = hodge_p(m, a)
                q = n - p
                if p < 1 or q < 1:
                    continue
                # try the orderings until one has a transvection
                dim = None
                for perm in sorted(set(itertools.permutations(a))):
                    dim = base_case(m, perm)
                    if dim is not None:
                        break
                if dim is None:
                    nos.append((m, a))
                    ok = False
                    continue
                ok &= dim == n * n - 1
                tot += 1
            table.append((m, n, tot))
    check("(B) base: for every a of order m in {3,4,6} with n = 3, 4 and "
          "p, q >= 1 the transvections generate sl(V_a) under brackets and "
          "conjugation, dimension n^2 - 1", ok,
          "(m, n, characters) %s%s" % (table, (" no seed: %s" % nos) if nos else ""))


def hermitian_inertia(H):
    """(positive, negative) inertia of a hermitian matrix over Q(zeta_m),
    by exact congruence; the pivots are rational"""
    m, n = H[0][0].m, len(H)
    A = [list(r) for r in H]
    pos = neg = 0
    idx = list(range(n))
    while idx:
        piv = next((i for i in idx if A[i][i]), None)
        if piv is None:
            # all diagonal entries zero: replace e_i by e_i + c e_j
            i, j = next(((i, j) for i in idx for j in idx if A[i][j]), (None, None))
            if i is None:
                break
            c = A[i][j].inv().conj()   # makes the new diagonal entry 2
            for l in range(n):
                A[i][l] = A[i][l] + c * A[j][l]
            for l in range(n):
                A[l][i] = A[l][i] + A[l][j] * c.conj()
            piv = i
        d = A[piv][piv]
        assert d.y == 0
        if d.x > 0:
            pos += 1
        else:
            neg += 1
        idx.remove(piv)
        for i in idx:
            if A[i][piv]:
                f = A[i][piv] / d
                for l in range(n):
                    A[i][l] = A[i][l] - f * A[piv][l]
                for l in range(n):
                    A[l][i] = A[l][i] - A[l][piv] * f.conj()
    return pos, neg


def invariant_form(M):
    """the space of H with g H conj(g)^T = H for the generators A_st"""
    m, n = M.m, M.k - 2
    S = Span(m, n * n)
    for g, _ in pure_generators(M):
        gb = [[x.conj() for x in r] for r in g]
        for a_ in range(n):
            for b_ in range(n):
                row = []
                for i in range(n):
                    for j in range(n):
                        v = g[a_][i] * gb[b_][j]
                        if a_ == i and b_ == j:
                            v = v - 1
                        row.append(v)
                S.add(row)
    pivots = {p for p, _ in S.rows}
    free = [j for j in range(n * n) if j not in pivots]
    sols = []
    for f in free:
        v = [Cyc(m, 0) for _ in range(n * n)]
        v[f] = Cyc(m, 1)
        for p, r in S.rows:
            v[p] = -r[f]
        sols.append([v[i * n:(i + 1) * n] for i in range(n)])
    return sols


def part_A2():
    ok, count = True, 0
    for m in (3, 4, 6):
        for k in (5, 6, 7):
            for a in multisets(m, k):
                M = Model(m, a)
                n = k - 2
                sols = invariant_form(M)
                ok &= len(sols) == 1
                if len(sols) != 1:
                    continue
                H = sols[0]
                # rescale to a hermitian matrix: H^* = lam H, mu/conj(mu) = lam
                i, j = next((i, j) for i in range(n) for j in range(n) if H[i][j])
                lam = H[j][i].conj() / H[i][j]
                ok &= all(H[b][a_].conj() == lam * H[a_][b]
                          for a_ in range(n) for b in range(n))
                mu = 1 + lam if (1 + lam) else Cyc(m, 0, 1) - Cyc(m, 0, 1).conj()
                Hh = [[mu * x for x in r] for r in H]
                ok &= all(Hh[b][a_].conj() == Hh[a_][b]
                          for a_ in range(n) for b in range(n))
                pos, neg = hermitian_inertia(Hh)
                p = hodge_p(m, a)
                ok &= pos + neg == n and {pos, neg} == {p, n - p}
                count += 1
    check("(A) the invariant hermitian form of the model is unique up to a "
          "scalar, nondegenerate, of signature {p, q} given by the exponents, "
          "k = 5, 6, 7", ok, "%d characters" % count)


# ---------------------------------------------------------------- (C)

def cable(braid):
    """double the first strand of a braid on k - 1 strands"""
    c, out = 1, []
    for i, e in braid:
        if i == c:
            seq, c = [(i + 1, 1), (i, 1)], i + 1
        elif i + 1 == c:
            seq, c = [(i, 1), (i + 1, 1)], i
        else:
            seq = [(i if i < c else i + 1, 1)]
        out += seq if e == 1 else [(j, -1) for j, _ in reversed(seq)]
    assert c == 1
    return out


def part_C():
    rng = random.Random(42)
    ok, count = True, 0
    for m in (3, 4, 6):
        for k in range(5, 10):
            cases = list(multisets(m, k))
            rng.shuffle(cases)
            for a in cases[:6]:
                a = list(a)
                rng.shuffle(a)
                # put a pair with a_1 + a_2 != 0 first
                pair = next(((i, j) for i in range(k) for j in range(i + 1, k)
                             if (a[i] + a[j]) % m), None)
                if pair is None:
                    continue
                i, j = pair
                rest = [a[l] for l in range(k) if l not in (i, j)]
                a = [a[i], a[j]] + rest
                M = Model(m, a)
                t = M.t
                ap = [(a[0] + a[1]) % m] + a[2:]
                Mp = Model(m, ap)
                z = Cyc(m, 0)
                I = [z] * k
                I = list(I)
                I[0], I[1] = 1 - t[1], -(1 - t[0])
                # (i) splitting of ker d
                U = [[b[0], t[0] * b[0]] + b[1:] for b in Mp.B]
                ok &= rank(U) == k - 2 and rank(U + [I]) == k - 1
                ok &= rank(U + [M.ell]) == k - 2
                # (ii) cabled braids: on the cycles outside as the braids of a',
                #      on I by a root of unity
                for s in range(1, k):
                    for u in range(s + 1, k):
                        bp = pure_generator(s, u)
                        imgs = automorphism(cable(bp), k)
                        ok &= is_pure(imgs)
                        J = fox_jacobian(imgs, t)
                        Jp = fox_jacobian(automorphism(bp, k - 1), Mp.t)
                        for b, io in zip(Mp.B, U):
                            w = mul([b], Jp)[0]
                            ok &= mul([io], J)[0] == [w[0], t[0] * w[0]] + w[1:]
                        gi = mul([I], J)[0]
                        ratio = gi[0] / I[0]
                        ok &= all(x == ratio * y for x, y in zip(gi, I))
                        ok &= any(ratio == zpow(m, e) for e in range(m))
                # (iii) the full twist of points 2 and 3
                J = fox_jacobian(automorphism(pure_generator(2, 3), k), t)
                gI = mul([I], J)[0]
                I23 = list([z] * k)
                I23[1], I23[2] = 1 - t[2], -(1 - t[1])
                ok &= gI == [x + (1 - t[0]) * t[1] * y for x, y in zip(I, I23)]
                g = M.braid_on_V(pure_generator(2, 3))
                IV = M.vector_to_V(I)
                gIV = mul([IV], g)[0]
                ok &= rank([IV, gIV]) == 2
                UV = [M.vector_to_V(u) for u in U]
                ok &= rank(UV) == k - 3
                gUV = mul(UV, g)
                ok &= rank(UV + gUV) == k - 2
                count += 1
    check("(C) the induction step: I and the cycles outside the disk split "
          "the kernel; cabled braids act on the outside as the braids of a' "
          "and on I by a root of unity; the twist of points 2, 3 moves the "
          "line of I and the hyperplane, k = 5..9", ok, "%d characters" % count)


# ---------------------------------------------------------------- (D)

def generates(m, residues):
    return math.gcd(m, *residues) == 1 if residues else False


def count_vectors(m, k):
    for c in itertools.product(range(k + 1), repeat=m - 1):
        if sum(c) != k:
            continue
        if sum(v * c[v - 1] for v in range(1, m)) % m:
            continue
        if not generates(m, [v for v in range(1, m) if c[v - 1]]):
            continue
        yield c


def good_merge(m, c):
    k = sum(c)
    f = {v: Fr(m - v, m) for v in range(1, m)}
    p = sum(f[v] * c[v - 1] for v in range(1, m)) - 1
    q = k - 2 - p
    if p < 1 or q < 1:
        return None
    for v in range(1, m):
        for w in range(v, m):
            if (v + w) % m == 0:
                continue
            cc = list(c)
            cc[v - 1] -= 1
            cc[w - 1] -= 1
            if min(cc) < 0:
                continue
            if not generates(m, [x for x in range(1, m) if cc[x - 1]]):
                continue
            s = f[v] + f[w]
            if (s < 1 and q >= 2) or (s > 1 and p >= 2):
                return (v, w)
    return False


def part_D():
    ok, tested = True, 0
    for m in (3, 4, 6):
        for k in range(7, 41 if m < 6 else 31):
            for c in count_vectors(m, k):
                r = good_merge(m, c)
                if r is None:
                    continue
                ok &= bool(r)
                tested += 1
    check("(D) merge lemma: every a of order m in {3,4,6} with k >= 7 points "
          "and p, q >= 1 has a merge a_i + a_j != 0 keeping the order and "
          "p, q >= 1 (k <= 40, and k <= 30 for m = 6)", ok,
          "%d multisets" % tested)


# ---------------------------------------------------------------- (E)

def part_E():
    rng = random.Random(7)
    ok = True
    # trace form over Z[i]: |det Tr(c v^T M conj w)| = 4^g N(c)^g det(M)^2
    for g in range(1, 5):
        for _ in range(6):
            M = zeros(4, g, g)
            for i in range(g):
                M[i][i] = Cyc(4, rng.randint(-5, 5))
                for j in range(i + 1, g):
                    z = Cyc(4, rng.randint(-5, 5), rng.randint(-5, 5))
                    M[i][j], M[j][i] = z, z.conj()
            dM = det(M)
            assert dM.y == 0
            c = Cyc(4, 0, 1).inv() / 2          # 1/(2i)
            basis = []
            for j in range(g):
                for u in (Cyc(4, 1), Cyc(4, 0, 1)):
                    v = [Cyc(4, 0)] * g
                    v = list(v)
                    v[j] = u
                    basis.append(v)
            B = []
            for v in basis:
                row = []
                for w in basis:
                    s = sum((v[i] * M[i][j] * w[j].conj()
                             for i in range(g) for j in range(g)), Cyc(4, 0))
                    s = c * s
                    row.append(2 * s.x)        # trace = 2 Re, Re = x for i
                B.append(row)
            from fractions import Fraction
            Bq = [[Fraction(x) for x in r] for r in B]
            # rational determinant
            n = len(Bq)
            A = [list(r) for r in Bq]
            d = Fraction(1)
            for col in range(n):
                piv = next((i for i in range(col, n) if A[i][col] != 0), None)
                if piv is None:
                    d = Fraction(0)
                    break
                if piv != col:
                    A[col], A[piv] = A[piv], A[col]
                    d = -d
                d *= A[col][col]
                for i in range(col + 1, n):
                    f = A[i][col] / A[col][col]
                    A[i] = [a - f * b for a, b in zip(A[i], A[col])]
            ok &= abs(d) == dM.x * dM.x
    # 2 is a norm from Q(i), not from Q(sqrt(-3)): x^2 + xy + y^2 is even only
    # when x and y are, so its 2-adic valuation is even
    ok &= Cyc(4, 1, 1).norm() == 2
    ok &= all((x * x + x * y + y * y) % 2 == 1 or (x % 2 == 0 and y % 2 == 0)
              for x in range(4) for y in range(4))
    # genus of the quotients against the eigenspace dimensions
    for _ in range(200):
        m = rng.choice((4, 6))
        k = rng.randint(4, 10)
        a = [rng.randint(1, m - 1) for _ in range(k - 1)]
        last = (-sum(a)) % m
        if last == 0:
            continue
        a.append(last)
        dims = {j: sum(1 for x in a if (j * x) % m) - 2 for j in range(1, m)}
        if m == 4:
            g_prime = (sum(1 for x in a if x % 2) - 2) // 2
            ok &= 2 * g_prime == dims[2]
        else:
            ok &= 2 * ((sum(1 for x in a if x % 2) - 2) // 2) == dims[3]
            ok &= sum(1 for x in a if x % 3) - 2 == dims[2] == dims[4]
    # balanced characters of order six on 8 points with c_3 odd
    odd = even = 0
    for s in itertools.product(range(1, 6), repeat=8):
        if sum(s) != 24 or order_of(6, s) != 6:
            continue
        if s.count(3) % 2:
            odd += 1
        else:
            even += 1
    ok &= odd > 0 and even > 0
    ex = (1, 1, 2, 2, 3, 5, 5, 5)
    ok &= sum(ex) == 24 and order_of(6, ex) == 6 and ex.count(3) == 1
    check("(E) discriminants: the trace form over Z[i]; 2 a norm from Q(i) and "
          "not from Q(sqrt(-3)); genus of the quotient curves; balanced "
          "characters of order six on 8 points with c_3 odd exist", ok,
          "c_3 odd %d, even %d, e.g. %s" % (odd, even, ex))


# ---------------------------------------------------------------- (F)

def T(d, k):
    return sum(1 for s in itertools.product(range(1, d), repeat=k)
               if 2 * sum(s) == d * k)


def vg_count_enum(d, N, r):
    total = 1
    for a in itertools.product(range(d), repeat=N + 1):
        if sum(a) % d or not any(a):
            continue
        s = [x for x in a if x]
        o = order_of(d, s)
        if o == 2:
            total += len(s) - 2 >= r
        elif len(s) == r + 2 and hodge_p(o, [x * o // d for x in s]) == r // 2:
            total += 1
    return total


def vg_count_formula(d, N, r):
    """1 + C(N+1, r+2) T_d(r+2), and for d even the characters of order two
    with larger support: sum_{j > r/2 + 1} C(N+1, 2j)"""
    total = 1 + math.comb(N + 1, r + 2) * T(d, r + 2)
    if d % 2 == 0:
        total += sum(math.comb(N + 1, 2 * j)
                     for j in range(r // 2 + 2, (N + 1) // 2 + 1))
    return total


def part_F():
    ok, rec = True, []
    cases = [(4, N, r) for N in range(5, 9) for r in (4, 6) if r <= N - 1] + \
            [(6, N, r) for N in range(5, 8) for r in (4, 6) if r <= N - 1] + \
            [(3, N, r) for N in range(5, 8) for r in (4, 6) if r <= N - 1] + \
            [(2, N, r) for N in range(5, 9) for r in (4, 6) if r <= N - 1]
    for d, N, r in cases:
        e, f = vg_count_enum(d, N, r), vg_count_formula(d, N, r)
        h = hodge_middle_ci(d, N, N - r)[r // 2]
        ok &= e == f and f <= h
        if N - r == 1:
            ok &= f == h
        rec.append((d, N, r, f, h))
    ok &= T(4, 6) == 141 and T(3, 6) == math.comb(6, 3) and T(2, 6) == 1
    check("(F) the very general count for d = 2, 3, 4, 6 by enumeration = "
          "1 + C(N+1,r+2) T_d(r+2) (+ sum_{j > r/2+1} C(N+1,2j) for d even), "
          "never above h^{r/2,r/2}, equal to it for hypersurfaces", ok,
          "T_4(6) = %d, T_6(6) = %d, T_4(8) = %d, T_6(8) = %d; (d,N,r,count,h) %s"
          % (T(4, 6), T(6, 6), T(4, 8), T(6, 8),
             [x for x in rec if x[0] in (4, 6)]))


def main():
    print("=" * 70)
    print("(LXXVI) monodromy of cyclic covers of degree 3, 4 and 6")
    print("=" * 70)
    part_A()
    part_A2()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    print("\n  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
