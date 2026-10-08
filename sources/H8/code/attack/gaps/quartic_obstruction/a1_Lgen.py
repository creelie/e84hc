"""a1_Lgen.py -- (L_gen): for F0 in {Q(sqrt5), Q(sqrt2), Q(sqrt13)} (O_0 = Z[omega], different
d = (omega - omegabar)), the integral F0-Hodge ring of a principally polarised abelian fourfold
with RM by O_0 is
     R_Z = { V in Herm_3(O_0) : V_11 = V_20 (mod d) }        (V-coordinates),
checked by double inclusion against the saturation R cap H^ev(X,Z) (track A1)."""
import sys
from fractions import Fraction as Fr
import flint
from ealib import *
from a1model import RMModel, QS
import a1_general as GEN   # only for saturate_classes (module-level model is replaced below)

FIELDS = {"sqrt5": ((0, 1), (1, 1)), "sqrt2": ((1, 1), (1, -1)), "sqrt13": ((2, 1), (1, -1)), "sqrt17": ((0, 2), (2, 1)), "sqrt10": ((1, 3), (3, -1))}
for name, Rm in FIELDS.items():
    M = RMModel(Rm)
    S = M.disc
    om = M.r1
    dd = om - om.conj()           # generator of the different
    def ab(x):
        b = 2 * x.b
        a = x.a - b * M.tr / 2
        return a, b
    def inO(x):
        a, b = ab(x)
        return a.denominator == 1 and b.denominator == 1
    th, thR = M.theta, M.thetaR
    gens = [wedge(power(th, i), power(thR, j)) for i in range(5) for j in range(5 - i)]
    RZ = GEN.saturate_classes(gens) if GEN.M.disc == S else None
    if RZ is None:
        GEN.M = M
        RZ = GEN.saturate_classes(gens)
    ok_sub = True
    for v in RZ:
        V = M.to_V(v)
        cond = all(inO(V[i][j]) for i in range(3) for j in range(3))
        cond = cond and all(V[i][i].b == 0 and V[i][i].a.denominator == 1 for i in range(3))
        cond = cond and all(V[j][i] == V[i][j].conj() for i in range(3) for j in range(3))
        cond = cond and inO((V[1][1] - V[2][0]) / dd)
        ok_sub = ok_sub and cond
    # generators of the congruence lattice Lambda = {(g, c) : g - c in d} x ...:
    # Lambda_(g,c) = {(c + delta, c) : c in Z, delta in d} is spanned by (1,1), (dd,0), (dd*omega,0)
    def el(a, b):
        return QS(a, 0, S) + om * b
    Z = QS(0, 0, S)
    def cls(r, h, g, c, k, m):
        V = [[QS(r, 0, S), h.conj(), g.conj()], [h, QS(c, 0, S), k.conj()], [g, k, QS(m, 0, S)]]
        u = M.from_V(V)
        out = {}
        for kk, x in u.items():
            assert x.b == 0
            if x.a != 0:
                out[kk] = x.a
        return out
    O1, Om = el(1, 0), el(0, 1)
    cg = [cls(1, Z, Z, 0, Z, 0), cls(0, Z, Z, 0, Z, 1), cls(0, O1, Z, 0, Z, 0), cls(0, Om, Z, 0, Z, 0),
          cls(0, Z, Z, 0, O1, 0), cls(0, Z, Z, 0, Om, 0), cls(0, Z, O1, 1, Z, 0), cls(0, Z, dd, 0, Z, 0),
          cls(0, Z, dd * om, 0, Z, 0)]
    # each generator is integral (all monomial coefficients integers) -> in R cap H^ev(Z) = R_Z
    ok_sup = all(all(Fr(x).denominator == 1 for x in v.values()) for v in cg)
    G1 = flint.fmpz_mat([[int(M.chi(a, b)) for b in RZ] for a in RZ]).det()
    check("%s: R_Z (saturation) lies in the congruence lattice (V_11 = V_20 mod %s)" % (name, dd), ok_sub)
    check("%s: the spanning set of the congruence lattice lies in H^ev(X,Z) (so R_Z = congruence lattice); det chi|R_Z = %s"
          % (name, G1), ok_sup)
summary()
