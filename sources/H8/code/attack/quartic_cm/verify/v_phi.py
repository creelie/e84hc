#!/usr/bin/env python3
"""v_phi.py -- independent exact check of the T1 quaternion-algebra claim, done directly in
F-coordinates (not via Q-lifts), with a NON-diagonal hermitian form and a GROUP element of U(V,H).
F = Q(z), z^4+z^3+z^2+z+1 = 0 (Q(zeta_5)), conj(z) = z^4.
V = F^4, H hermitian (H^* = H) with det H in F0.  On T = wedge^2_F V (F-dim 6):
  q(x,y) := coefficient of e1234 in x^y   (F-bilinear symmetric)
  h(x,y) := det[H(x_i,y_j)] on decomposables, H(u,v) = u^T H conj(v)   (sesquilinear)
  phi    := the conj-semilinear map with q(x,y) = h(x, phi y).
Checks: phi^2 = (det H)^{-1}; q(gx,gy) = det(g) q(x,y), h(gx,gy) = h(x,y) for g in U(V,H);
phi g = conj(det g) g phi, so phi commutes with SU(V,H)."""
from fractions import Fraction as Fr
import itertools, random

# ---- F = Q(zeta5) arithmetic: elements are 4-tuples in basis 1,z,z^2,z^3
def fmul(a, b):
    c = [Fr(0)] * 7
    for i in range(4):
        for j in range(4):
            c[i + j] += a[i] * b[j]
    # reduce z^k, k>=4: z^4 = -(1+z+z^2+z^3)
    for k in range(6, 3, -1):
        t = c[k]; c[k] = Fr(0)
        for m in range(4):
            c[k - 4 + m] -= t
    return tuple(c[:4])
def fadd(a, b): return tuple(x + y for x, y in zip(a, b))
def fsub(a, b): return tuple(x - y for x, y in zip(a, b))
def fneg(a): return tuple(-x for x in a)
ZERO = (Fr(0),) * 4; ONE = (Fr(1), Fr(0), Fr(0), Fr(0))
def fpow_z(k):
    r = ONE
    for _ in range(k % 5): r = fmul(r, (Fr(0), Fr(1), Fr(0), Fr(0)))
    return r
def conj(a):
    # sum a_i z^i -> sum a_i z^{-i}
    r = ZERO
    for i in range(4):
        r = fadd(r, tuple(a[i] * x for x in fpow_z(-i)))
    return r
def finv(a):
    # solve a*x = 1 by linear algebra over Q
    import flint
    M = flint.fmpq_mat(4, 4)
    for j in range(4):
        e = [Fr(0)] * 4; e[j] = Fr(1)
        col = fmul(a, tuple(e))
        for i in range(4): M[i, j] = flint.fmpq(col[i].numerator, col[i].denominator)
    rhs = flint.fmpq_mat(4, 1, [1, 0, 0, 0])
    x = M.solve(rhs)
    return tuple(Fr(int(x[i, 0].p), int(x[i, 0].q)) for i in range(4))
def fq(x): return (Fr(x), Fr(0), Fr(0), Fr(0))
s5 = fadd(fq(1), tuple(2 * v for v in fadd(fpow_z(1), fpow_z(4))))  # 1 + 2(z+z^-1) = sqrt5
assert fmul(s5, s5) == fq(5)
w = fsub(fpow_z(1), fpow_z(4))  # z - z^-1, purely imaginary

def det(M):
    n = len(M)
    if n == 1: return M[0][0]
    r = ZERO
    for j in range(n):
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        t = fmul(M[0][j], det(minor))
        r = fadd(r, t) if j % 2 == 0 else fsub(r, t)
    return r

# ---- a non-diagonal hermitian H of signature (2,2) at both places (checked numerically below)
a = fadd(fq(1), w)                      # off-diagonal entry
H = [[fq(2), a, ZERO, ZERO],
     [conj(a), fq(3), ZERO, fq(1)],
     [ZERO, ZERO, fneg(fq(1)), s5],
     [ZERO, fq(1), s5, fneg(fq(7))]]
for i in range(4):
    for j in range(4):
        assert H[i][j] == conj(H[j][i])
dH = det(H)
assert conj(dH) == dH

def Hform(u, v):
    r = ZERO
    for i in range(4):
        for j in range(4):
            r = fadd(r, fmul(fmul(u[i], H[i][j]), conj(v[j])))
    return r

PAIRS = list(itertools.combinations(range(4), 2))
def e(i):
    v = [ZERO] * 4; v[i] = ONE; return v
def h2(I, J):
    return fsub(fmul(Hform(e(I[0]), e(J[0])), Hform(e(I[1]), e(J[1]))),
                fmul(Hform(e(I[0]), e(J[1])), Hform(e(I[1]), e(J[0]))))
def qsign(I, J):
    if set(I) & set(J): return 0
    perm = list(I) + list(J)
    inv = sum(1 for x in range(4) for y in range(x + 1, 4) if perm[x] > perm[y])
    return -1 if inv % 2 else 1
Hmat = [[h2(I, J) for J in PAIRS] for I in PAIRS]   # h(e_I, e_J)
Qmat = [[fq(qsign(I, J)) for J in PAIRS] for I in PAIRS]

# phi: q(x,y) = h(x, phi y).  With h(x,y) = x^T Hm conj(y), phi(y) = conj(P) conj(y)?  Solve:
# q(e_I, y) = sum_J Q_IJ y_J ; h(e_I, phi y) = sum_K Hm_IK conj((phi y)_K).
# Put phi(y) = Pm conj(y) (semilinear).  Then conj((phi y)_K) = sum_J conj(Pm_KJ) y_J, so
# Q = Hm conj(Pm), i.e. conj(Pm) = Hm^{-1} Q.
def matmul(A, B):
    return [[(lambda i, j: __import__('functools').reduce(fadd, [fmul(A[i][k], B[k][j]) for k in range(len(B))], ZERO))(i, j)
             for j in range(len(B[0]))] for i in range(len(A))]
def matinv(A):
    n = len(A)
    M = [list(row) + [ONE if i == j else ZERO for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != ZERO)
        M[c], M[p] = M[p], M[c]
        iv = finv(M[c][c])
        M[c] = [fmul(iv, x) for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != ZERO:
                f = M[r][c]
                M[r] = [fsub(x, fmul(f, y)) for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]
def mconj(A): return [[conj(x) for x in row] for row in A]
Pm = mconj(matmul(matinv(Hmat), Qmat))
# phi^2 (y) = Pm conj(Pm conj(y)) = Pm conj(Pm) y
phi2 = matmul(Pm, mconj(Pm))
target = finv(dH)
ok_phi2 = all(phi2[i][j] == (target if i == j else ZERO) for i in range(6) for j in range(6))
print("phi^2 = (det H)^{-1} * id  (non-diagonal H):", ok_phi2)

# ---- a group element of U(V,H): Cayley transform g = (1 - X)^{-1}(1 + X) with X in u(V,H):
# X in u(V,H) iff X^T H + H conj(X) = 0  <=>  (H conj(X))^T ... use X = H^{-1} S with ... simpler:
# for hermitian form u^T H conj(v), invariance of g means g^T H conj(g) = H.
# Take X = conj(Hinv) A with A^T = -conj(A)?  Check numerically instead of deriving: build X = Hinv^T? We
# param X := M0 - (adjoint of M0) where adjoint wrt H: X^+ = conj(H)^{-1}... ; verify directly.
Hinv = matinv(H)
def transpose(A): return [list(r) for r in zip(*A)]
rng = random.Random(1)
def rand_f():
    return tuple(Fr(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(4))
M0 = [[rand_f() for _ in range(4)] for _ in range(4)]
# condition X^T H + H conj(X) = 0.  Set X = M0 - Hstar(M0) where Hstar(M) = conj(Hinv^T ... ) solve:
# Let Y = H conj(M0); want X with X^T H = -H conj(X).  Take X = M0 - conj(Hinv) M0^{T*}... verify numerically.
Xadj = matmul(mconj(Hinv), matmul(transpose(mconj(M0)), mconj(H)))  # candidate adjoint
X = [[fsub(M0[i][j], Xadj[i][j]) for j in range(4)] for i in range(4)]
lhs = matmul(transpose(X), H); rhs = matmul(H, mconj(X))
ok_u = all(fadd(lhs[i][j], rhs[i][j]) == ZERO for i in range(4) for j in range(4))
print("X in u(V,H):", ok_u)
I4 = [[ONE if i == j else ZERO for j in range(4)] for i in range(4)]
g = matmul(matinv([[fsub(I4[i][j], X[i][j]) for j in range(4)] for i in range(4)]),
           [[fadd(I4[i][j], X[i][j]) for j in range(4)] for i in range(4)])
gg = matmul(transpose(g), matmul(H, mconj(g)))
ok_g = all(gg[i][j] == H[i][j] for i in range(4) for j in range(4))
dg = det(g)
print("g in U(V,H):", ok_g, "; N(det g) = 1:", fmul(dg, conj(dg)) == ONE, "; det g in Q:", dg[1:] == (0, 0, 0))
# wedge^2 g on T
def w2(g):
    return [[fsub(fmul(g[I[0]][J[0]], g[I[1]][J[1]]), fmul(g[I[0]][J[1]], g[I[1]][J[0]])) for J in PAIRS] for I in PAIRS]
G2 = w2(g)
# phi g = conj(det g) g phi  on T :  Pm conj(G2) conj(y) vs conj(dg) G2 Pm conj(y)
L = matmul(Pm, mconj(G2)); R = [[fmul(conj(dg), x) for x in row] for row in matmul(G2, Pm)]
print("phi o g = conj(det g) g o phi on T:", L == R)
# an element of SU: g' = g * diag(1/det g,1,1,1) is not unitary in general; instead check phi commutes
# with wedge^2 of the Lie algebra element X0 = X - (tr X/4) I (in su(V,H)):
trX = X[0][0]
for i in range(1, 4): trX = fadd(trX, X[i][i])
X0 = [[fsub(X[i][j], fmul(finv(fq(4)), trX)) if i == j else X[i][j] for j in range(4)] for i in range(4)]
def w2lie(X):
    # derivation action on e_I = e_a ^ e_b : X e_a ^ e_b + e_a ^ X e_b, in coordinates (columns = images)
    out = [[ZERO] * 6 for _ in range(6)]
    for c, (a, b) in enumerate(PAIRS):
        for k in range(4):
            for (p, qv, coef) in ((k, b, X[k][a]), (a, k, X[k][b])):
                if p == qv or coef == ZERO: continue
                I = tuple(sorted((p, qv))); sg = 1 if (p, qv) == I else -1
                r = PAIRS.index(I)
                out[r][c] = fadd(out[r][c], coef if sg == 1 else fneg(coef))
    return out
DX = w2lie(X0)
L2 = matmul(Pm, mconj(DX)); R2 = matmul(DX, Pm)
print("phi commutes with wedge^2 of su(V,H) element:", L2 == R2)
print("det H =", dH)
