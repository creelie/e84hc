"""
split.py -- the split member A = X x X^ in exact coordinates.

Generators of H^1(A,Q): x_0..x_{2n-1} (bits 0..2n-1), xi_0..xi_{2n-1}
(bits 2n..4n-1).  beta = sum_{j<n} x_j x_{n+j}, betahat = sum xi_j xi_{n+j},
ell = sum_i x_i xi_i, gamma0 = d beta - betahat, eta = d beta + betahat.
Weil classes: w1 = Re (gamma0 - delta ell)^n, w2 = coefficient of delta.
Complex structure (for Hodge-theoretic ranks): X = E_i^n,
dz_j = x_j + i x_{n+j};  H^{1,0}(X^) = ann(H^{1,0}(X)), dw_j = xi_j + i xi_{n+j}.
"""
from fractions import Fraction as Fr
from math import comb, factorial
from ext import (GQ, wedge, eadd, escale, epow, eexp, gen, degree_part,
                 substitute, interior, wedge_left, rank_and_kernel,
                 solve_in_span, to_gq, popcount, iszero)


class Split:
    def __init__(self, n, d):
        self.n, self.d = n, d
        self.m = 2 * n
        self.N = 4 * n

    def x(self, i):
        return i

    def xi(self, i):
        return self.m + i

    def beta(self):
        n = self.n
        return eadd(*[wedge(gen(self.x(j)), gen(self.x(n + j))) for j in range(n)])

    def betahat(self):
        n = self.n
        return eadd(*[wedge(gen(self.xi(j)), gen(self.xi(n + j))) for j in range(n)])

    def ell(self):
        return eadd(*[wedge(gen(self.x(i)), gen(self.xi(i))) for i in range(self.m)])

    def eta(self):
        return eadd(escale(Fr(self.d), self.beta()), self.betahat())

    def gamma0(self):
        return eadd(escale(Fr(self.d), self.beta()), escale(Fr(-1), self.betahat()))

    def weil(self):
        n, d = self.n, self.d
        g, l = self.gamma0(), self.ell()
        re, im = {}, {}
        for k in range(n + 1):
            term = escale(Fr(comb(n, k)), wedge(epow(g, n - k), epow(l, k)))
            # (-delta)^k
            if k % 2 == 0:
                re = eadd(re, escale(Fr((-d) ** (k // 2)), term))
            else:
                im = eadd(im, escale(Fr(-((-d) ** ((k - 1) // 2))), term))
        return re, im

    def vol(self):
        """the class of a point of A, with int = 1."""
        return wedge(escale(Fr(1, factorial(self.n)), epow(self.beta(), self.n)),
                     escale(Fr(1, factorial(self.n)), epow(self.betahat(), self.n)))

    def integral(self, u):
        top = (1 << self.N) - 1
        v = self.vol()
        return u.get(top, 0) / v[top]

    # ------------------------------------------------ complex structure
    def to_complex(self, u):
        """rewrite u in the basis dz_j, dw_j (bits 0..2n-1: dz_0..dz_{n-1},
        dw_0..dw_{n-1}) and conjugates (bits 2n..4n-1)."""
        n, m = self.n, self.m
        # complex generator indices: dz_j -> j, dw_j -> n + j,
        # dzbar_j -> 2n + j, dwbar_j -> 3n + j
        half = GQ(Fr(1, 2))
        mhi = GQ(0, Fr(-1, 2))   # 1/(2i) = -i/2
        images = {}
        for j in range(n):
            images[self.x(j)] = {1 << j: half, 1 << (m + j): half}
            images[self.x(n + j)] = {1 << j: mhi, 1 << (m + j): -mhi}
            images[self.xi(j)] = {1 << (n + j): half, 1 << (m + n + j): half}
            images[self.xi(n + j)] = {1 << (n + j): mhi, 1 << (m + n + j): -mhi}
        out = {}
        for mask, c in u.items():
            piece = {0: GQ(c) if not isinstance(c, GQ) else c}
            for i in range(self.N):
                if mask >> i & 1:
                    piece = wedge(piece, images[i])
            out = eadd(out, piece)
        return out

    def hodge_type_ok(self, uc, p):
        """all components of the complex form uc of type (p,p)?"""
        m = self.m
        for mask in uc:
            a = popcount(mask & ((1 << m) - 1))
            b = popcount(mask >> m)
            if a != p or b != p:
                return False
        return True

    def ht_ops(self):
        """the 4n generators of HT^1 as operators on complex forms:
        wedge with a (0,1) generator, contraction with a (1,0) one."""
        m = self.m
        ops = []
        for i in range(m):
            ops.append(("w", m + i))
        for i in range(m):
            ops.append(("c", i))
        return ops

    def apply_op(self, op, u):
        kind, i = op
        return wedge_left(i, u) if kind == "w" else interior(i, u)

    def ht2_images(self, uc):
        ops = self.ht_ops()
        imgs = []
        labels = []
        for a in range(len(ops)):
            ua = self.apply_op(ops[a], uc)
            for b in range(a + 1, len(ops)):
                imgs.append(self.apply_op(ops[b], ua))
                labels.append((ops[a], ops[b]))
        return imgs, labels

    def htk_images(self, uc, k):
        from itertools import combinations
        ops = self.ht_ops()
        imgs = []
        for S in combinations(range(len(ops)), k):
            v = uc
            for s in reversed(S):
                v = self.apply_op(ops[s], v)
            imgs.append(v)
        return imgs

    def r_of(self, u):
        uc = self.to_complex(u)
        imgs, _ = self.ht2_images(uc)
        return rank_and_kernel(imgs)

    def profile(self, u, kmax=None):
        uc = self.to_complex(u)
        kmax = kmax or self.N
        return [rank_and_kernel(self.htk_images(uc, k)) for k in range(0, kmax + 1)]

    # ------------------------------------------------ flat Hodge classes
    def flat_basis(self):
        e = self.eta()
        w1, w2 = self.weil()
        basis = [epow(e, k) for k in range(2 * self.n + 1)]
        return basis + [w1, w2]

    def corrected_coords(self, u):
        """u = sum c_k eta^k + a w1 + b w2 ?  returns (c, a, b) or None."""
        x = solve_in_span(u, self.flat_basis())
        if x is None:
            return None
        k = 2 * self.n + 1
        return x[:k], x[k], x[k + 1]
