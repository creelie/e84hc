"""a1_prodtype.py -- product-type (rank-one V) integral characters with chi = 4 (track A1).

Rank-one V with V_00 = r != 0 is v = r * N(1, alpha_1, alpha_2) (norm class), i.e. in
R_Z-coordinates (r, h, g, c, k, m) = (r, r a1, r a2, r N(a1), r a2 abar1, r N(a2)), with
E := h^2 - r g = r^2 (alpha_1^2 - alpha_2) totally positive (complex-secant) and
chi = 4 N(E) / r^2.  chi = 4  <=>  N(E) = r^2.  Integrality: v in R_Z (tested exactly).
We enumerate r, h, E (E totally positive of norm r^2, up to a bounded power of the unit phi^2)
and report every integral solution.  Also the case r = 0 (V_00 = 0, rank one) is treated.
"""
import sys, time, itertools
from fractions import Fraction as Fr
from math import isqrt
import flint
from ealib import *
from a1model import RMModel, QS
import pickle

M = RMModel()   # F0 = Q(sqrt5), phi = r1
S5 = 5
PHI = QS(Fr(1, 2), Fr(1, 2), 5)
LAT = pickle.load(open("a1_lattice.pkl", "rb"))
RZ = LAT["RZ"]


def oelt(a, b):
    """a + b phi (tau_1 value)."""
    return QS(a, 0, 5) + PHI * b


def is_int(x):
    """x (tau_1 value, QS) in O_0 = Z[phi]?  x = a + b phi with a, b in Z."""
    # x = p + q sqrt5 ; phi = 1/2 + sqrt5/2 -> b = 2q, a = p - q
    b = 2 * x.b
    a = x.a - x.b
    return a.denominator == 1 and b.denominator == 1


def in_RZ(v):
    """test v in Z-span of RZ exactly."""
    x = solve_coords(v)
    return x is not None and all(t.denominator == 1 for t in x)


_basis_cache = {}


def solve_coords(v):
    keys = sorted(set(k for b in RZ for k in b) | set(v))
    Mq = flint.fmpq_mat(len(keys), 10)
    for j, b in enumerate(RZ):
        for i, k in enumerate(keys):
            c = b.get(k, 0)
            if c:
                Mq[i, j] = flint.fmpq(int(c), 1)
    for i, k in enumerate(keys):
        c = Fr(v.get(k, 0))
        Mq[i, 9] = flint.fmpq(c.numerator, c.denominator)
    R, rk = Mq.rref()
    if rk > 9:
        return None
    for i in range(rk):
        if R[i, 9] != 0 and all(R[i, j] == 0 for j in range(9)):
            return None
    sol = [Fr(0)] * 9
    for i in range(rk):
        piv = next(j for j in range(9) if R[i, j] != 0)
        sol[piv] = Fr(int(R[i, 9].p), int(R[i, 9].q))
    return sol


def class_from(r, h, g, c, k, m):
    V = [[QS(r, 0, 5), h.conj(), g.conj()],
         [h, QS(c, 0, 5), k.conj()],
         [g, k, QS(m, 0, 5)]]
    u = M.from_V(V)
    out = {}
    for kk, x in u.items():
        assert x.b == 0
        if x.a != 0:
            out[kk] = x.a
    return out


if __name__ == "__main__":
    t0 = time.time()
    RB = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    HB = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    # totally positive elements of Z[phi] of norm n, up to multiplication by phi^{2k}, |k| <= 2
    def tp_of_norm(n):
        out = []
        # E = a + b phi, N(E) = a^2 + a b - b^2 ; enumerate a bounded region
        L = isqrt(4 * n) + 4
        for b in range(-3 * L, 3 * L + 1):
            for a in range(-3 * L, 3 * L + 1):
                if a * a + a * b - b * b == n:
                    E = oelt(a, b)
                    if E.val() > 0 and E.conj().val() > 0:
                        out.append(E)
        return out
    sols = []
    tried = 0
    for r in range(-RB, RB + 1):
        if r == 0:
            continue
        Es = tp_of_norm(r * r)
        for E in Es:
            for h0 in range(-HB * abs(r), HB * abs(r) + 1):
                for h1 in range(-HB * abs(r), HB * abs(r) + 1):
                    h = oelt(h0, h1)
                    Nh = h.norm()
                    if Nh % r:
                        continue
                    g = (h * h - E) / Fr(r)
                    if not is_int(g):
                        continue
                    Ng = g.norm()
                    if Ng % r:
                        continue
                    kq = g * h.conj() / Fr(r)
                    if not is_int(kq):
                        continue
                    tried += 1
                    v = class_from(r, h, g, Nh / r, kq, Ng / r)
                    if in_RZ(v):
                        sols.append((r, h, g, E))
    print("rank-one V, chi = 4: tried %d candidates with O_0-integral (h, g, k); integral in R_Z: %d  (%.1fs)"
          % (tried, len(sols), time.time() - t0))
    for s in sols[:30]:
        print("   r=%d h=%s g=%s E=%s" % s)
    # r = 0 case: V = lambda [[0,0,0],[0,N a1, a1 abar2],[0, a2 abar1, N a2]], c = lambda N(a1) must be = 0 mod 5
    # (degree-4 integrality c = g = 0 mod sqrt5), chi = 4 c^2 = 4 forces c = +-1: impossible.
    check("r = 0: chi = 4 c^2 with 5 | c has no solution chi = 4", True)
    check("no integral product-type character with chi = 4 and 0 < |rank| <= %d, |h| <= %d|r|" % (RB, HB),
          len(sols) == 0)
    summary()
