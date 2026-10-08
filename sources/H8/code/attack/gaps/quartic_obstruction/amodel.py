"""amodel.py -- the split member A = X x Xhat with the action of the quartic CM
field F = F0(sqrt(-q)) (track A1), following Markman's construction for RM
(arXiv:2509.23079; framework only, statements used are re-derived here).

Generators of H^1(A,Q): x_0..x_7 (H^1(X)), xi_0..xi_7 (H^1(Xhat)) = indices 0..15.
B: x_j -> xi_{4+j}, x_{4+j} -> -xi_j (the polarisation isomorphism, as in T3).
F0 acts on x's through R (a1model), on xi's through Rhat = B R B^{-1}.
M = sqrt(-q):  x -> -B x,   xi -> q B^{-1} xi;  M^2 = -q.
Polarisation class (to be checked): eta = beta_q + betahat,
  beta_q = sum_{j<4} (q x_j) x_{4+j},  betahat = sum_{j<4} xi_j xi_{4+j}.
ell = sum_i x_i xi_i (c_1 of the Poincare bundle).
"""
from fractions import Fraction as Fr
from ealib import *
from a1model import RMModel


def matmul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def matadd(A, B, c=1):
    return [[A[i][j] + c * B[i][j] for j in range(len(A))] for i in range(len(A))]


def ident(n):
    return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]


def zero(n):
    return [[Fr(0)] * n for _ in range(n)]


def transpose(A):
    return [list(r) for r in zip(*A)]


class AModel:
    def __init__(self, q=(2, 1), Rm=((0, 1), (1, 1))):
        self.X = RMModel(Rm)
        self.q = q
        n = 16
        # R on x's (8x8) as matrix acting on generator coordinates: column = image of generator
        RA = zero(n)
        for col, lst in self.X.act_R().items():
            for (row, c) in lst:
                RA[row][col] = c
        Bm = zero(n)          # B: x -> xi  (as map on generators, column = image)
        for j in range(4):
            Bm[8 + 4 + j][j] = Fr(1)
            Bm[8 + j][4 + j] = Fr(-1)
        Binv = zero(n)        # B^{-1}: xi -> x
        for j in range(4):
            Binv[4 + j][8 + 4 + j] = Fr(-1) * -1  # B x_{4+j} = -xi_j  => B^{-1} xi_j = -x_{4+j}
        Binv = zero(n)
        for j in range(4):
            Binv[j][8 + 4 + j] = Fr(1)       # B^{-1} xi_{4+j} = x_j
            Binv[4 + j][8 + j] = Fr(-1)      # B^{-1} xi_j = -x_{4+j}
        self.Bm, self.Binv = Bm, Binv
        # Rhat = B R B^{-1} on xi's
        Rhat = matmul(matmul(Bm, RA), Binv)
        self.R = matadd(RA, Rhat)            # F0-generator R acting on all of H^1(A)
        q0, q1 = Fr(q[0]), Fr(q[1])
        self.Q = matadd([[q0 * x for x in r] for r in ident(n)], self.R, q1)
        # M: x -> -B x ; xi -> q B^{-1} xi
        Px = zero(n)
        for j in range(8):
            Px[j][j] = Fr(1)
        Pxi = zero(n)
        for j in range(8, 16):
            Pxi[j][j] = Fr(1)
        self.M = matadd([[-c for c in r] for r in matmul(Bm, Px)], matmul(self.Q, matmul(Binv, Pxi)))
        self.n = n

    def A_of(self, Mat):
        return mat_to_A(Mat)

    # classes
    def ell(self):
        return add(*[wedge(gen(i), gen(8 + i)) for i in range(8)])

    def beta_f(self, f):
        """pr_X^* theta_f."""
        return self.X.theta_f(f)

    def betahat(self):
        return add(*[wedge(gen(8 + j), gen(12 + j)) for j in range(4)])

    def gram(self, u):
        """antisymmetric Gram matrix G of a degree-2 class u = sum_{i<j} G_ij g_i g_j."""
        G = zero(self.n)
        for m, c in u.items():
            b = [i for i in range(self.n) if m >> i & 1]
            assert len(b) == 2
            i, j = b
            G[i][j] += c
            G[j][i] -= c
        return G

    def from_gram(self, G):
        out = {}
        for i in range(self.n):
            for j in range(i + 1, self.n):
                if G[i][j] != 0:
                    out[(1 << i) | (1 << j)] = G[i][j]
        return out
