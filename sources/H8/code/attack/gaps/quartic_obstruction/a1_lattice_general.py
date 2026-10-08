"""a1_lattice_general.py -- the integral F0-Hodge ring of a principally polarised
abelian fourfold with real multiplication by O = Z[sqrt D], for D = 3, 6, 7, 10, 14,
on the lattice H_1(X,Z) = O e + O f + d^{-1} e* + d^{-1} f*, polarised by
E = Tr psi, with psi the O-bilinear alternating form psi(e, e*) = psi(f, f*) = 1.

The bases {1, sqrt D} of O and {1/2, 1/(2 sqrt D)} of the inverse different
d^{-1} are dual under the trace, so u = (e, sqrt D e, f, sqrt D f) and
w = (e*/2, e*/(2 sqrt D), f*/2, f*/(2 sqrt D)) form a symplectic basis of
H_1(X,Z) for E; x_0..x_7 is the dual basis of H^1(X,Z), and
theta = sum_{j<4} x_j x_{4+j} is the principal polarisation.  sqrt D acts on
H_1 by u_1 -> u_2, u_2 -> D u_1 (and likewise on u_3, u_4), and by
w_1 -> D w_2, w_2 -> w_1 (and likewise on w_3, w_4); on H^1 it acts by the
transpose.  This lattice exists for every real quadratic field, whether or not
D is a sum of two squares.

The script computes the saturation R_Z = R cap H^ev(X,Z) of the F0-Hodge ring R
spanned by theta^i theta_R^j, and tests the description
    R_Z = { V in Herm_3(O) : V_11 = V_20 (mod d) },   d = (2 sqrt D),
by double inclusion, as a1_Lgen.py does for the product model.
"""
import sys
from fractions import Fraction as Fr
import flint
from ealib import *
from a1model import RMModel, QS
import a1_general as GEN


class LatticeModel(RMModel):
    """RMModel with the O^2 + (d^{-1})^2 lattice in place of S (x) M."""

    def __init__(self, D):
        self.D = D
        # action of sqrt D on H_1, as columns: basis index -> list of (row, coeff)
        # H_1 basis: 0..3 = u_1..u_4, 4..7 = w_1..w_4
        h1 = {0: [(1, 1)], 1: [(0, D)], 2: [(3, 1)], 3: [(2, D)],
              4: [(5, D)], 5: [(4, 1)], 6: [(7, D)], 7: [(6, 1)]}
        # on H^1 (dual basis x_j) the action is the transpose: R^* x_row = sum c x_col
        A = {j: [] for j in range(8)}
        for col, entries in h1.items():
            for (row, c) in entries:
                A[col].append((row, Fr(c)))
        # act_R is read as: column j lists (row, c) with R x_j = sum c x_row
        At = {j: [] for j in range(8)}
        for j, entries in A.items():
            for (row, c) in entries:
                At[row].append((j, c))
        self._act = At
        super().__init__(((0, D), (1, 0)))

    def act_R(self):
        return self._act


def main():
    Ds = [int(a) for a in sys.argv[1:]] or [3, 6, 7, 10, 14]
    for D in Ds:
        M = LatticeModel(D)
        S = M.disc
        om = M.r1
        dd = om - om.conj()
        # the form theta(R x, y) is symmetric: R is E-self-adjoint
        th, thR = M.theta, M.thetaR
        gens = [wedge(power(th, i), power(thR, j)) for i in range(5) for j in range(5 - i)]
        GEN.M = M
        RZ = GEN.saturate_classes(gens)
        check("D = %d: R_Z has rank 9" % D, len(RZ) == 9)

        def ab(x):
            b = 2 * x.b
            a = x.a - b * M.tr / 2
            return a, b

        def inO(x):
            a, b = ab(x)
            return a.denominator == 1 and b.denominator == 1

        ok_sub = True
        for v in RZ:
            V = M.to_V(v)
            cond = all(inO(V[i][j]) for i in range(3) for j in range(3))
            cond = cond and all(V[i][i].b == 0 and V[i][i].a.denominator == 1 for i in range(3))
            cond = cond and all(V[j][i] == V[i][j].conj() for i in range(3) for j in range(3))
            cond = cond and inO((V[1][1] - V[2][0]) / dd)
            ok_sub = ok_sub and cond

        sq = QS(0, Fr(1, 2), S)         # sqrt(disc)/2 = sqrt D
        Z = QS(0, 0, S)
        O1 = QS(1, 0, S)

        def cls(r, h, g, c, k, m):
            V = [[QS(r, 0, S), h.conj(), g.conj()], [h, QS(c, 0, S), k.conj()], [g, k, QS(m, 0, S)]]
            u = M.from_V(V)
            out = {}
            for kk, x in u.items():
                assert x.b == 0
                if x.a != 0:
                    out[kk] = x.a
            return out

        cg = [cls(1, Z, Z, 0, Z, 0), cls(0, Z, Z, 0, Z, 1), cls(0, O1, Z, 0, Z, 0), cls(0, sq, Z, 0, Z, 0),
              cls(0, Z, Z, 0, O1, 0), cls(0, Z, Z, 0, sq, 0), cls(0, Z, O1, 1, Z, 0), cls(0, Z, dd, 0, Z, 0),
              cls(0, Z, dd * sq, 0, Z, 0)]
        ok_sup = all(all(Fr(x).denominator == 1 for x in v.values()) for v in cg)
        G1 = flint.fmpz_mat([[int(M.chi(a, b)) for b in RZ] for a in RZ]).det()
        check("D = %d: R_Z (saturation) lies in the congruence lattice (V_11 = V_20 mod 2 sqrt D)" % D, ok_sub)
        check("D = %d: the congruence lattice lies in H^ev(X,Z), so R_Z is the congruence lattice; "
              "det chi|R_Z = %s" % (D, G1), ok_sup)
    summary()


if __name__ == "__main__":
    main()
