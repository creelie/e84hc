#!/usr/bin/env python3
"""
t4_example.py -- an explicit direct sum of natural objects at n = 4 with a
corrected Chern character, N != 0, Hankel rank 3, and all the numbers of (b).

E = (+) O_{B_i}^{|m_i|}[k_i]  (+)  O(eta) (+) O(2 eta) (+) O(3 eta),
B_i = B_(p_i,q_i) the eight abelian subvarieties {(p x, q phi x)} for
(p,q) in PQ below, m_i the (unique up to scale) integers with
sum m_i [B_i] in the Weil plane, k_i = 0 if m_i > 0 and 1 if m_i < 0.

Printed:
  (E1) the m_i, the Weil class, purity of sum m_i [B_i]
  (E2) ch(E) = N omega + sum c_k eta^k exactly; c_k; rho; r(gamma)
  (E3) cross Ext: chi(O_Bi, O_Bj) = |p_i q_j - p_j q_i|^8 (degree 4),
       chi(O(t eta), O_B) = (t(d p^2 + q^2))^4 (degree 4),
       chi(O(t eta), O(t' eta)) = (t'-t)^8 d^4 (degree 0 if t' > t)
       -> with shifts in {0,1} no cross Ext^1 and no cross Ext^2
  (E4) dim Ext^2(E,E), dim Ext^1(E,E), against r(gamma)
  (E5) kappa >= rank of T -> (+)_i H^*, v -> (v _| ch F_i)_i   (mod p, lower bound)
       and rank of sigma_E on the trace parts = dim sum_i HT^2 _| ch F_i (mod p)
  (E6) the flatness form: e - k against the dimension 8 * sum|m_i| of the
       locus of split deformations inside K_E
"""
import sys, os, time
from fractions import Fraction as Fr
from math import factorial, gcd
from ext import *

n = 4
d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
S = Split(n, d)
b, bh, l, eta = S.beta(), S.betahat(), S.ell(), S.eta()
W1, W2 = S.weil_pair()
PQ_REF = [(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1), (1, -2), (2, -1)]
PQ_SMALL = [(1, -3), (1, -2), (1, 2), (1, 3), (2, -1), (2, 1), (3, -1), (3, 1)]
PQ = PQ_SMALL if (len(sys.argv) > 2 and sys.argv[2] == 'small') else PQ_REF
print("points (p,q):", PQ)
B = [S.subtorus(p, q) for (p, q) in PQ]
t0 = time.time()

# (E1) relation sum m_i B_i = x W1 + y W2 : solve in the 9-dim span
# unknowns m_1..m_8, x, y ; equations: coefficients of every monomial
keys = sorted(set().union(*[set(v) for v in B + [W1, W2]]))
vecs = B + [scale(W1, -1), scale(W2, -1)]
# nullspace of the matrix with columns vecs
cols = len(vecs)
rows = [[Fr(v.get(k, 0)) for v in vecs] for k in keys]
# gaussian elimination
M = [r[:] for r in rows]
piv = []
r = 0
for c in range(cols):
    pr = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
    if pr is None:
        continue
    M[r], M[pr] = M[pr], M[r]
    pv = M[r][c]
    M[r] = [x / pv for x in M[r]]
    for i in range(len(M)):
        if i != r and M[i][c] != 0:
            f = M[i][c]
            M[i] = [x - f * y for x, y in zip(M[i], M[r])]
    piv.append(c)
    r += 1
free = [c for c in range(cols) if c not in piv]
print("(E1) nullity of [B_1..B_8, W1, W2] =", len(free), "(expect 1)")
fc = free[0]
sol = [Fr(0)] * cols
sol[fc] = Fr(1)
for i, c in enumerate(piv):
    sol[c] = -M[i][fc]
den = 1
for x in sol:
    den = den * x.denominator // gcd(den, x.denominator)
sol = [x * den for x in sol]
g = 0
for x in sol:
    g = gcd(g, int(x))
sol = [int(x) // g for x in sol]
m = sol[:8]
xw, yw = sol[8], sol[9]
print("     m_i =", m, "  Weil class = %d W1 + %d W2" % (xw, yw))
core = {}
for mi, Bi in zip(m, B):
    core = add(core, Bi, 1, mi)
print("     sum m_i [B_i] == x W1 + y W2 exactly:", add(core, add(scale(W1, xw), scale(W2, yw)), 1, -1) == {})
print("     all m_i nonzero:", all(mi != 0 for mi in m), "  sum m_i^2 =", sum(mi * mi for mi in m))

# (E2) theta-bundles and the full character
ts = [1, 2, 3]
theta_part = {}
for t in ts:
    theta_part = add(theta_part, exp_class(scale(eta, t), 16))
gamma = add(core, theta_part)
# c_k: theta_part = sum_k c_k eta^k with c_k = sum_t t^k/k!
c = [sum(Fr(t) ** k / factorial(k) for t in ts) for k in range(9)]
chk = {}
for k in range(9):
    chk = add(chk, power(eta, k), 1, c[k])
chk = add(chk, add(scale(W1, xw), scale(W2, yw)))
print("(E2) ch(E) == (x W1 + y W2) + sum_k c_k eta^k exactly:", add(gamma, chk, 1, -1) == {})
mu = [factorial(k) * c[k] for k in range(9)]
H = [{i: mu[j + i] for i in range(3) if mu[j + i]} for j in range(7)]
rho = rank_of(H)
print("     c_k =", [str(x) for x in c])
print("     Hankel rank rho = %d, r(gamma) = (4+rho)16 - 8 = %d" % (rho, (4 + rho) * 16 - 8))
rgamma = (4 + rho) * 16 - 8

# (E3) cross Ext via Riemann-Roch (Todd class trivial): chi(F,G) = int ch(F)^dual ch(G)
def dual(u):
    return {k: (c if (popcount(k) // 2) % 2 == 0 else -c) for k, c in u.items()}
def chi(u, v):
    return S.integral(wedge(dual(u), v))
ok = True
for i in range(8):
    for j in range(8):
        if i == j:
            continue
        (p1, q1), (p2, q2) = PQ[i], PQ[j]
        exp_ = abs(p1 * q2 - p2 * q1) ** 8
        if chi(B[i], B[j]) != exp_:
            ok = False
print("(E3) chi(O_Bi, O_Bj) = |det|^8 for all i != j:", ok)
ok = True
for t in ts:
    et = exp_class(scale(eta, t), 16)
    for (p, q), Bi in zip(PQ, B):
        if chi(et, Bi) != (t * (d * p * p + q * q)) ** 4:
            ok = False
        if chi(Bi, et) != (t * (d * p * p + q * q)) ** 4:
            ok = False
print("     chi(O(t eta), O_B) = chi(O_B, O(t eta)) = (t(dp^2+q^2))^4:", ok)
ok = True
for t in ts:
    for t2 in ts:
        if t2 != t:
            v = chi(exp_class(scale(eta, t), 16), exp_class(scale(eta, t2), 16))
            if v != (t2 - t) ** 8 * d ** 4:
                ok = False
print("     chi(O(t eta), O(t' eta)) = (t'-t)^8 d^4:", ok)
print("     degrees: O_Bi -> O_Bj in degree 4 (transversal subtori, local Ext^4 only);")
print("     O(t eta) -> O_B and O_B -> O(t eta) in degree 4 (eta|_B ample, Serre duality);")
print("     O(t eta) -> O(t' eta) in degree 0 for t' > t, 8 for t' < t.")
shifts = [0 if mi > 0 else 1 for mi in m] + [0, 0, 0]
degs = {}
objs = list(range(11))
def conc(i, j):
    if i < 8 and j < 8:
        return 4
    if i < 8 or j < 8:
        return 4
    return 0 if ts[j - 8] > ts[i - 8] else 8
X1 = X2 = 0
mult = [abs(mi) for mi in m] + [1, 1, 1]
for i in objs:
    for j in objs:
        if i == j:
            continue
        dg = conc(i, j)
        # Ext^q(F_i[k_i], F_j[k_j]) = Ext^{q + k_j - k_i}(F_i, F_j)
        if 1 + shifts[j] - shifts[i] == dg:
            X1 += 1
        if 2 + shifts[j] - shifts[i] == dg:
            X2 += 1
print("     with shifts k_i in {0,1}: number of pairs with cross Ext^1 = %d, cross Ext^2 = %d" % (X1, X2))

# (E4)
sm2 = sum(mm * mm for mm in mult)
ext2 = 28 * sm2
ext1 = 8 * sm2
print("(E4) dim Ext^2(E,E) = 28 * sum m^2 = %d  vs  r(gamma) = %d  (excess %d)"
      % (ext2, rgamma, ext2 - rgamma))
print("     dim Ext^1(E,E) = 8 * sum m^2 = %d" % ext1)

# (E5) kappa and the rank of sigma on trace parts, mod p
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import contraction as C
import numpy as np
from tspace import compute_T, T_apply
Tbasis = compute_T(d, eta)
print('     dim T (mod p) =', len(Tbasis))
chs = B + [exp_class(scale(eta, t), 16) for t in ts]
dvs = [C.dense(x) for x in chs]
# T -> (+)_i H^*: stack the 11 images of each basis vector of T into one long vector
Trows = []
for V in Tbasis:
    Trows.append(np.concatenate([T_apply(V, dv) for dv in dvs]))
rT = C.rank_mod(Trows)
print("(E5) rank of T -> (+)_i H^*, v -> (v _| ch F_i)_i  (mod p) = %d  => kappa >= %d" % (rT, rT))
imgs = []
for dv in dvs:
    imgs += C.span_basis(C.ht2_images(dv))
rs = C.rank_mod(imgs)
print("     dim sum_i HT^2 _| ch F_i (mod p, lower bound) = %d of %d  => kappa <= %d"
      % (rs, 28 * len(chs), 28 * len(chs) - rs))
kappa_lb = rT
k_lb = 28 * sum(mm * mm - 1 for mm in mult) + kappa_lb + X2
print("     dim ker sigma_E >= 28 sum(m^2-1) + kappa = %d" % k_lb)

# (E6)
split_dim = 8 * sum(mult)
print("(E6) e - k <= %d - %d = %d  <  %d = 8 sum|m_i| <= dim K_E"
      % (ext1, k_lb, ext1 - k_lb, split_dim))
print("     => the hypothesis dim K_E = e - k of prop:p2flat(ii) fails:", ext1 - k_lb < split_dim)
print("time %.1fs" % (time.time() - t0))
