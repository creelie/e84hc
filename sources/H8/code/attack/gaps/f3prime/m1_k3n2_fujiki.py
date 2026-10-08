#!/usr/bin/env python3
# Supporting script for item (LXI), code/k3_hodge.py (round 19, (F3') through motives).
"""
Exact checks for projective hyper-Kahler fourfolds of K3^[2]-type.

H^2 = Lambda (x) Q with Lambda = U^3 + E8(-1)^2 + <-2>, the Beauville-Bogomolov
lattice (rank 23, signature (3,20)).  H^4 = Sym^2 H^2 (b_4 = 276), with the
intersection pairing given by the polarised Fujiki relation (Fujiki constant 3):
    int a b c d = q(a,b)q(c,d) + q(a,c)q(b,d) + q(a,d)q(b,c).

Checks:
 (1) b_4(S^[2]) = 276 from Goettsche's formula, = dim Sym^2 of a 23-dim space.
 (2) The Fujiki pairing on Sym^2 H^2 is nondegenerate (exact determinant).
 (3) q^vee = sum G^{-1}_{ij} e_i e_j satisfies int q^vee x y = 25 q(x,y).
 (4) c_2 := (6/5) q^vee satisfies int c_2 x y = 30 q(x,y) (the known value) and
     int c_2^2 = 828; with c_4 = 324, Todd_4 = 3 = chi(O) and HRR gives
     chi(L) = binom(q(L)/2+3, 2).  Since the pairing on H^4 is nondegenerate
     and H^4 = Sym^2 H^2, c_2(X) = (6/5) q^vee exactly.
 (5) Casimir splitting q^vee = q_NS^vee + q_T^vee for NS = <h, n> (explicit),
     with q_T^vee in Sym^2 T.
 (6) The key identity of the CM argument: for a q-isometry u of T and
     f = u + id_NS, the class Z' = sum_i b_i (x) f(a_i) (b_i the dual basis of
     a_i for B(x,y) = int x y h^2) has cup-product image
        m(Z') = (1/q(h)) * [ (u+u^*)/2 as a symmetric tensor on T ]
                + (a class in Sym^2 NS),
     i.e. Delta^* of the algebraic class Z' is the Hodge class of Sym^2 T
     attached to the self-adjoint element (u+u^*)/2.
 (7) The converse operator: for c in Sym^2 T attached to a self-adjoint C,
     the map x -> Lambda(c cup x) on T equals (tr C + 2C)/q(h).
All arithmetic is exact (sympy Rational, python-flint fmpz_mat).
"""
import itertools, random, sys
from fractions import Fraction
import sympy as sp
import flint

random.seed(20260928)

def e8_cartan():
    # Bourbaki numbering: 1-3-4-5-6-7-8 chain, 2 attached to 4
    C = [[0]*8 for _ in range(8)]
    for i in range(8):
        C[i][i] = 2
    edges = [(0,2),(2,3),(3,4),(4,5),(5,6),(6,7),(1,3)]
    for a,b in edges:
        C[a][b] = C[b][a] = -1
    return C

def bb_lattice():
    n = 23
    G = [[0]*n for _ in range(n)]
    # U^3
    for k in range(3):
        G[2*k][2*k+1] = G[2*k+1][2*k] = 1
    E = e8_cartan()
    for blk in range(2):
        off = 6 + 8*blk
        for i in range(8):
            for j in range(8):
                G[off+i][off+j] = -E[i][j]
    G[22][22] = -2
    return sp.Matrix(G)

G = bb_lattice()
n = G.shape[0]
Ginv = G.inv()
assert G.det() != 0
# signature
ev = G.evalf().eigenvals()
pos = sum(m for v,m in ev.items() if v > 0); neg = sum(m for v,m in ev.items() if v < 0)
print(f"BB lattice: rank {n}, det {G.det()}, signature ({pos},{neg})")

def q(x, y):
    return (x.T * G * y)[0, 0]

# ---------- (1) Goettsche: Betti numbers of S^[2] for a K3 surface ----------
z, t = sp.symbols('z t')
b = [1, 0, 22, 0, 1]
N = 2
gen = 1
for k in range(1, N+1):
    for i in range(5):
        gen *= (1 - (-1)**i * z**(2*k-2+i) * t**k)**(-(-1)**i * b[i])
ser = sp.series(gen, t, 0, N+1).removeO()
P2 = sp.expand(ser.coeff(t, N))
print("Poincare polynomial of S^[2] (K3):", sp.Poly(P2, z).all_coeffs()[::-1])
assert sp.Poly(P2, z).coeff_monomial(z**4) == 276 == n*(n+1)//2
print("(1) b_4 = 276 = dim Sym^2 H^2: OK")

# ---------- (2) nondegeneracy of the Fujiki pairing on Sym^2 ----------
pairs = [(i, j) for i in range(n) for j in range(i, n)]
Gi = [[int(G[i, j]) for j in range(n)] for i in range(n)]
def fuj(a, b_, c, d):
    return Gi[a][b_]*Gi[c][d] + Gi[a][c]*Gi[b_][d] + Gi[a][d]*Gi[b_][c]
M = flint.fmpz_mat(len(pairs), len(pairs),
                   [fuj(i, j, k, l) for (i, j) in pairs for (k, l) in pairs])
detM = M.det()
print(f"(2) det of the Fujiki pairing on Sym^2 H^2 (276x276) = {detM}")
assert detM != 0

# Sym^2 elements as dicts {(i,j): coeff} with i<=j, meaning sum coeff * e_i e_j
def sym_from_matrix(Ssym):
    """symmetric matrix S -> element sum_{i,j} S_ij e_i e_j of Sym^2."""
    d = {}
    for i in range(n):
        for j in range(i, n):
            c = Ssym[i, j] if i == j else 2*Ssym[i, j]
            if c != 0:
                d[(i, j)] = sp.Rational(c)
    return d

def int_c_xy(c, x, y):
    Gx = G*x; Gy = G*y
    qxy = q(x, y)
    s = 0
    for (i, j), cij in c.items():
        s += cij*(G[i, j]*qxy + Gx[i]*Gy[j] + Gy[i]*Gx[j])
    return sp.Rational(s)

def int_cc(c, d):
    s = 0
    for (i, j), cij in c.items():
        for (k, l), dkl in d.items():
            s += cij*dkl*fuj(i, j, k, l)
    return sp.Rational(s)

qvee = sym_from_matrix(Ginv)
basis = [sp.Matrix([1 if r == k else 0 for r in range(n)]) for k in range(n)]
ok = True
for k in range(n):
    for l in range(k, n):
        if int_c_xy(qvee, basis[k], basis[l]) != 25*G[k, l]:
            ok = False
print("(3) int q^vee x y = 25 q(x,y) on all basis pairs:", ok)
assert ok

c2 = {key: sp.Rational(6, 5)*v for key, v in qvee.items()}
ok = all(int_c_xy(c2, basis[k], basis[l]) == 30*G[k, l] for k in range(n) for l in range(k, n))
c2sq = int_cc(c2, c2)
print("(4) int c_2 x y = 30 q(x,y):", ok, "; int c_2^2 =", c2sq)
assert ok and c2sq == 828
c4 = 324
td4 = sp.Rational(3*c2sq - c4, 720)
assert td4 == 3
qq = sp.symbols('qq')
chi = sp.expand(3*qq**2/24 + sp.Rational(1, 24)*30*qq + td4)
target = sp.expand(sp.binomial(qq/2 + 3, 2).expand(func=True))
assert sp.simplify(chi - target) == 0
print("    Todd_4 = (3*828-324)/720 =", td4, "; chi(L) =", chi, "= binom(q/2+3,2): OK")

# ---------- (5) Casimir splitting ----------
h = basis[0] + basis[1]            # q(h) = 2, in the first U
nvec = basis[6]                    # a root of E8(-1): q = -2
NSb = [h, nvec]
GNS = sp.Matrix(2, 2, lambda a, b_: q(NSb[a], NSb[b_]))
# T = NS^perp: kernel of the map x -> (q(h,x), q(n,x))
A = sp.Matrix.vstack((G*h).T, (G*nvec).T)
Tb = A.nullspace()
assert len(Tb) == n - 2
GT = sp.Matrix(len(Tb), len(Tb), lambda a, b_: q(Tb[a], Tb[b_]))
assert GT.det() != 0
def sym_from_vectors(vecs, gram_inv):
    S = sp.zeros(n, n)
    for a in range(len(vecs)):
        for b_ in range(len(vecs)):
            S += gram_inv[a, b_]*vecs[a]*vecs[b_].T
    return S
S_NS = sym_from_vectors(NSb, GNS.inv())
S_T = sym_from_vectors(Tb, GT.inv())
assert sp.simplify(S_NS + S_T - Ginv) == sp.zeros(n, n)
print("(5) q^vee = q_NS^vee + q_T^vee with q_T^vee in Sym^2 T: OK")

# ---------- (6) the Delta^* identity for f = u + id_NS ----------
m = len(Tb)
# random q_T-skew matrix A (GT*A skew)  -> Cayley transform u is a q_T-isometry
S = sp.zeros(m, m)
for a in range(m):
    for b_ in range(a+1, m):
        v = sp.Rational(random.randint(-3, 3), random.randint(1, 3))
        S[a, b_] = v; S[b_, a] = -v
Askew = GT.inv()*S
I_m = sp.eye(m)
u = (I_m - Askew)*(I_m + Askew).inv()          # in the basis Tb
assert sp.simplify(u.T*GT*u - GT) == sp.zeros(m, m)
# f on H^2 in the standard basis: change of basis P = [NS | T]
P = sp.Matrix.hstack(*(NSb + Tb))
Pinv = P.inv()
blk = sp.diag(sp.eye(2), u)
f = P*blk*Pinv
assert sp.simplify(f.T*G*f - G) == sp.zeros(n, n)   # f is a q-isometry of H^2
# B(x,y) = int x y h^2 = q(h)q(x,y) + 2 q(x,h) q(y,h)
qh = q(h, h)
Gh = G*h
Bmat = qh*G + 2*Gh*Gh.T
# check B against the Fujiki pairing
for _ in range(5):
    x = sp.Matrix([random.randint(-2, 2) for _ in range(n)])
    y = sp.Matrix([random.randint(-2, 2) for _ in range(n)])
    hh = sym_from_matrix(h*h.T)  # the class h*h (h^2 in Sym^2)
    # int x y h^2 via the Fujiki pairing: (h h) is sum_{ij} h_i h_j e_i e_j
    assert int_c_xy(hh, x, y) == (x.T*Bmat*y)[0, 0]
Binv = Bmat.inv()
# a_i = e_i ; b_i = B-dual basis: b_i = column i of Binv (since B(e_j, b_i) = delta)
# Z' = sum_i b_i (x) f(e_i)   -> as a matrix Zp[r, s] = sum_i b_i[r] f(e_i)[s]
Zp = Binv*f.T          # Zp[r,s] = sum_i Binv[r,i]*f[s,i]
m_Zp = (Zp + Zp.T)/2   # its cup-product image in Sym^2 (symmetric part)
# prediction: (1/q(h)) * sym tensor of (u+u*)/2 on T  +  something in Sym^2 NS
uplus = (u + GT.inv()*u.T*GT)/2                # q_T-adjoint average, in basis Tb
# symmetric tensor on T of a self-adjoint operator C (basis Tb): sum_{a} t_a^vee (x) C t_a
def tensor_of_operator_T(C):
    # tensor = sum_{a,b} (GT^{-1} C^T)?  Write it directly:
    # tau(C) = sum_a (dual_a) (x) (C t_a), dual_a = sum_b GTinv[a,b] t_b
    GTinv = GT.inv()
    Tm = sp.Matrix.hstack(*Tb)           # n x m
    dual = Tm*GTinv                      # column a = dual_a
    Ct = Tm*C                            # column a = C t_a
    return dual*Ct.T
pred_T = tensor_of_operator_T(uplus)/qh
pred_T = (pred_T + pred_T.T)/2
diff = sp.simplify(m_Zp - pred_T)
# diff must lie in Sym^2 NS: diff = NSmat * K * NSmat^T for a 2x2 symmetric K
NSm = sp.Matrix.hstack(*NSb)
K = sp.Matrix(2, 2, sp.symbols('k0:4'))
sol = sp.solve(list(NSm*K*NSm.T - diff), list(K))
print("(6) m(Z') - (1/q(h)) Sym[(u+u*)/2 on T] lies in Sym^2 NS:", bool(sol), sol)
assert sol
# (u+u*)/2 is not a scalar (so the class is new) for this random u
assert sp.simplify(uplus - uplus[0, 0]*I_m) != sp.zeros(m, m)

# ---------- (7) the converse operator ----------
# c in Sym^2 T attached to self-adjoint C (basis Tb); x -> Lambda(c cup x):
# the element z in H^2 with B(z, y) = int c x y for all y.
Csa = uplus  # a self-adjoint operator on T
c_mat = tensor_of_operator_T(Csa); c_mat = (c_mat + c_mat.T)/2
c_sym = sym_from_matrix(c_mat)
trC = Csa.trace()
Tm = sp.Matrix.hstack(*Tb)
for a in range(3):
    x = Tb[a]
    rhs = sp.Matrix([int_c_xy(c_sym, x, basis[k]) for k in range(n)])  # int c x e_k
    zvec = Binv*rhs   # B(z, e_k) = rhs_k  ->  Bmat z = rhs
    pred = (trC*x + 2*(Tm*Csa[:, a]))/qh
    assert sp.simplify(zvec - pred) == sp.zeros(n, 1)
print("(7) Lambda(c cup x) = (tr C + 2C)x/q(h) on T: OK")
print("ALL CHECKS PASSED")
