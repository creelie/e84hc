"""model.py -- independent model of the split member A = X x X^ (paper, thm:splitclosed).

Real generators of H^1(A,Q): x_0..x_{2n-1} -> indices 0..2n-1,
xi_0..xi_{2n-1} -> indices 2n..4n-1.
beta = sum_{j<n} x_j x_{n+j}; betahat = sum_j xi_j xi_{n+j}; ell = sum_i x_i xi_i.
B x_j = xi_{n+j}, B x_{n+j} = -xi_j (paper).  K-action on H^1: u -> -Bu, phi -> d B^{-1} phi.
Weil classes computed from the eigenspaces directly (not from the closed formula):
omega_+ = wedge_i (x_i + tau B x_i), tau = sqrt(-d)/d, over Q(sqrt(-d)).
Complex structure: dz_j = x_j + i x_{n+j}, dw_j = xi_j + i xi_{n+j}.
Complex generators: dz_j -> j, dw_j -> n+j, dzbar_j -> 2n+j, dwbar_j -> 3n+j.
"""
from fractions import Fraction as F
from math import factorial
from itertools import combinations
from ea import *


class Model:
    def __init__(self, n, d):
        self.n, self.d = n, d
        self.m = 2 * n
        self.N = 4 * n

    def x(self, i): return i
    def xi(self, i): return self.m + i

    def Bx(self, i):
        n = self.n
        return g(self.xi(n + i)) if i < n else g(self.xi(i - n), F(-1))

    def beta(self):
        n = self.n
        return add(*[mul(g(self.x(j)), g(self.x(n + j))) for j in range(n)])

    def betahat(self):
        n = self.n
        return add(*[mul(g(self.xi(j)), g(self.xi(n + j))) for j in range(n)])

    def ell(self):
        return add(*[mul(g(self.x(i)), g(self.xi(i))) for i in range(self.m)])

    def eta(self):
        return add(sc(F(self.d), self.beta()), self.betahat())

    def Mstar(self, i):
        """M^* on the real generator i."""
        n, d = self.n, self.d
        if i < self.m:           # x_i -> -B x_i
            return sc(F(-1), self.Bx(i))
        j = i - self.m           # xi_j -> d B^{-1} xi_j ; B^{-1} xi_j = -x_{n+j} (j<n), B^{-1} xi_{n+j} = x_j
        if j < n:
            return g(self.x(n + j), F(-d))
        return g(self.x(j - n), F(d))

    def weil_pm(self):
        """omega_+ = wedge (x_i + tau B x_i), coefficients in Q(sqrt(-d)); returns (re, im) rational
        classes with omega_+ = re + sqrt(-d) im."""
        d = self.d
        tau = Qm(0, F(1, d), d)
        w = {(): Qm(1, 0, d)}
        for i in range(self.m):
            v = add({(self.x(i),): Qm(1, 0, d)}, {k: tau * c for k, c in self.Bx(i).items()})
            w = mul(w, v)
        re = clean({k: c.a for k, c in w.items()})
        im = clean({k: c.b for k, c in w.items()})
        return re, im

    def vol(self):
        n = self.n
        return mul(sc(F(1, factorial(n)), power(self.beta(), n)), sc(F(1, factorial(n)), power(self.betahat(), n)))

    def integral(self, u):
        top = tuple(range(self.N))
        return u.get(top, 0) / self.vol()[top]

    # ---------------- complex structure over Q(i)
    def cx(self, u):
        n, m = self.n, self.m
        h = Qm(F(1, 2), 0, 1); mh = Qm(0, F(-1, 2), 1)
        im = {}
        for j in range(n):
            im[self.x(j)] = {(j,): h, (m + j,): h}
            im[self.x(n + j)] = {(j,): mh, (m + j,): -mh}
            im[self.xi(j)] = {(n + j,): h, (m + n + j,): h}
            im[self.xi(n + j)] = {(n + j,): mh, (m + n + j,): -mh}
        uu = {k: Qm(c, 0, 1) if not isinstance(c, Qm) else c for k, c in u.items()}
        return linsub(uu, im)

    def is_type(self, uc, p):
        m = self.m
        return all(sum(1 for i in k if i < m) == p and sum(1 for i in k if i >= m) == p for k in uc)

    # HT^1 operators: wedge with a (0,1) generator (index m..2m-1), contraction with a (1,0) generator (0..m-1)
    def ht1(self):
        return [("w", self.m + i) for i in range(self.m)] + [("c", i) for i in range(self.m)]

    @staticmethod
    def apply(op, u):
        return mul({(op[1],): Qm(1, 0, 1)}, u) if op[0] == "w" else contract(op[1], u)

    def htk_images(self, uc, k):
        ops = self.ht1()
        out = []
        for S in combinations(range(len(ops)), k):
            v = uc
            for s in reversed(S):
                v = self.apply(ops[s], v)
            out.append(v)
        return out

    def r(self, u, k=2):
        return rank(self.htk_images(self.cx(u), k))

    def profile(self, u, kmax):
        uc = self.cx(u)
        return [rank(self.htk_images(uc, k)) for k in range(kmax + 1)]

    # ---------------- H^1(T) = Hom(H^{1,0}, H^{0,1}); D_v = sum_a v(e_a) ^ iota_a
    def Dv(self, v, uc):
        """v: dict (b, a) -> coeff, meaning e_a (1,0 generator a) -> sum_b coeff * ebar_b (generator m+b)."""
        out = {}
        for (b, a), c in v.items():
            y = mul({(self.m + b,): c}, contract(a, uc))
            for k, x in y.items():
                out[k] = out.get(k, 0) + x
        return clean(out)

    def M_on_10(self):
        """matrix of M^* on H^{1,0} in basis dz_j (j), dw_j (n+j): M^* dz_j = i dw_j, M^* dw_j = i d dz_j.
        Computed from Mstar and cx rather than typed in."""
        n, m = self.n, self.m
        mat = {}
        for a in range(m):
            # e_a as real combination: dz_j = x_j + i x_{n+j}; dw_j = xi_j + i xi_{n+j}
            if a < n:
                real = add({(self.x(a),): Qm(1, 0, 1)}, {(self.x(n + a),): Qm(0, 1, 1)})
            else:
                j = a - n
                real = add({(self.xi(j),): Qm(1, 0, 1)}, {(self.xi(n + j),): Qm(0, 1, 1)})
            img = {}
            for (i,), c in real.items():
                for k, cc in self.Mstar(i).items():
                    img[k] = img.get(k, 0) + c * Qm(cc, 0, 1)
            imgc = self.cx(clean(img))
            for (k,), c in imgc.items():
                mat[(k, a)] = c   # M e_a = sum_k mat[k,a] e_k  (k may be 0..2m-1)
        return mat

    def tangent(self):
        """T = {v in Hom(H^{1,0},H^{0,1}) : v K-linear, v _| eta = 0}, computed from M and eta only."""
        m = self.m
        Mm = self.M_on_10()
        # check M preserves H^{1,0}
        assert all(k < m for (k, a) in Mm), "M does not preserve H^{1,0}"
        # M on H^{0,1}: conj.  ebar_a = generator m+a; M ebar_a = sum conj(mat[k,a]) ebar_k
        etac = self.cx(self.eta())
        basis = [(b, a) for b in range(m) for a in range(m)]
        cols = []
        for (b, a) in basis:
            # equations: (vM - Mv)(e_c) for all c, and D_v eta
            eq = {}
            # v M e_c = sum_k M[k,c] v(e_k) ; v(e_a) = ebar_b
            for c in range(m):
                coeff = Mm.get((a, c), 0)
                if not isz(coeff):
                    eq[("K", c, b)] = eq.get(("K", c, b), 0) + coeff
                # M v e_c : v(e_c) = ebar_b if c == a ; M ebar_b = sum_k conj(M[k,b]) ebar_k
                if c == a:
                    for k in range(m):
                        mk = Mm.get((k, b), 0)
                        if not isz(mk):
                            eq[("K", c, k)] = eq.get(("K", c, k), 0) - mk.conj()
            y = self.Dv({(b, a): Qm(1, 0, 1)}, etac)
            for k, c in y.items():
                eq[("E", k)] = c
            cols.append(clean(eq))
        # kernel of the map coefficient vector -> sum cols
        return kernel(cols, basis)


def kernel(cols, labels):
    """kernel of x -> sum x_i cols_i (cols sparse dicts). Returns list of dict label->coeff."""
    keys = sorted({k for c in cols for k in c}, key=repr)
    idx = {k: i for i, k in enumerate(keys)}
    n = len(cols)
    R = [[0] * n for _ in keys]
    for j, c in enumerate(cols):
        for k, v in c.items():
            R[idx[k]][j] = v
    pivcols = []
    ri = 0
    for col in range(n):
        p = None
        for i in range(ri, len(R)):
            if not isz(R[i][col]):
                p = i; break
        if p is None:
            continue
        R[ri], R[p] = R[p], R[ri]
        pv = R[ri][col]
        R[ri] = [c / pv for c in R[ri]]
        for i in range(len(R)):
            if i != ri and not isz(R[i][col]):
                f = R[i][col]
                R[i] = [a - f * b for a, b in zip(R[i], R[ri])]
        pivcols.append(col)
        ri += 1
    free = [c for c in range(n) if c not in pivcols]
    out = []
    for fcol in free:
        vec = {labels[fcol]: Qm(1, 0, 1)}
        for i, pc in enumerate(pivcols):
            val = -R[i][fcol]
            if not isz(val):
                vec[labels[pc]] = val if isinstance(val, Qm) else Qm(val, 0, 1)
        out.append(vec)
    return out
