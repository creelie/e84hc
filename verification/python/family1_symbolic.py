"""Family I of the paper (Proposition "prop:family1") in exact symbolic arithmetic (sympy).

Solves sum_k c_k b_k(s) = 0 for the coefficients c_k(lambda), checks the identity of binary
forms prod_k u_k^{alpha_k} = Psi * A^114 through the block exponents, and computes the residue
I(lambda) = Res_{s = lambda} A * Delta / (u_1 u_2) ds in closed form."""
import sympy as sp

s, lam = sp.symbols("s lambda")
m = 114
al = (51, 21, 86, 14, 56)                       # 13 * (39, 63, 68, 80, 92) mod 114
E = [(0, 0, 1, 2, 0), (0, 0, 2, 0, 1), (1, 3, 0, 0, 0), (2, 0, 0, 1, 2)]
pos = [sp.Integer(0), sp.Integer(1), lam, None]  # the last block sits at s = infinity
c = sp.symbols("c0:5")
base = []
for k in range(5):
    f = sp.Integer(1)
    for a in range(4):
        if pos[a] is not None:
            f *= (s - pos[a]) ** E[a][k]
    base.append(sp.expand(f))
eqs = sp.Poly(sum(c[k] * base[k] for k in range(5)), s).all_coeffs()
sol = sp.solve(eqs + [c[0] - 1], c, dict=True)
assert len(sol) == 1
cs = [sp.factor(sol[0][ck]) for ck in c]
u = [cs[k] * base[k] for k in range(5)]
assert sp.cancel(sp.together(sum(u))) == 0
rest = [0, 3, 4]
ud = [sp.diff(uk, lam) for uk in u]
Delta = sp.Matrix([[1, 1, 1], [sp.cancel(ud[k] / u[k]) for k in rest],
                   [sp.cancel(sp.diff(u[k], s) / u[k]) for k in rest]]).det()
A = sp.Integer(1)
for a in range(4):
    Aa = sum(x * y for x, y in zip(al, E[a]))
    assert Aa % m == 0
    if pos[a] is not None:
        A *= (s - pos[a]) ** (Aa // m)
eta = sp.cancel(sp.together(A * Delta / (u[1] * u[2])))
I = sp.factor(sp.residue(eta, s, lam))
target = -(lam**3 - 3*lam**2 + 1) * (2*lam**3 + 12*lam**2 - 21*lam + 8) / (
    lam * (lam - 1)**2 * (3*lam - 2) * (2*lam**2 - 1))
assert sp.cancel(I - target) == 0
print("c(lambda) =", cs)
print("A =", sp.factor(A))
print("I(lambda) =", I)
print("closed formula confirmed")
