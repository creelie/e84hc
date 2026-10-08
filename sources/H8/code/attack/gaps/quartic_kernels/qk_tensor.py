"""qk_tensor.py -- classes on A = A_1 x A_2 as sums of tensor products over the
two real places, for item (LIX) (quartic_kernels.py).

A class on A is given as a list of pieces (c, P_1, P_2), c a scalar and P_j a
class of the j-th factor (a dict over the monomials of qk_place, coefficients
in K = Q(sqrt D, i)); it stands for sum c P_1 (x) P_2.  Since every P_j has even
degree, no signs arise (proof of thm:quarticobstruction(iii)).

ProjK(d) splits a class of one factor as sum_i a_i I_i + R, with I_i the seven
SU_j-invariant classes of qk_place.inv_basis(d) and R in a fixed complement
(R vanishes on chosen monomials); so a sum of pieces is flat, that is invariant
under G_F(R) = SU_1 x SU_2, if and only if every component outside
Inv_1 (x) Inv_2 of its splitting vanishes.  Everything is exact.
"""
import itertools
from qk_ext import popc, sub, sc
from qk_place import inv_basis


def _det(M, zero):
    n = len(M)
    if n == 1:
        return M[0][0]
    s = zero
    for j in range(n):
        minor = [r[:j] + r[j + 1:] for r in M[1:]]
        t = M[0][j] * _det(minor, zero)
        s = s + t if j % 2 == 0 else s - t
    return s


def _inv(M, zero, one):
    n = len(M)
    dt = _det(M, zero).inv()
    out = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if n == 1:
                c = one
            else:
                minor = [r[:j] + r[j + 1:] for k, r in enumerate(M) if k != i]
                c = _det(minor, zero)
            out[j][i] = (c if (i + j) % 2 == 0 else -c) * dt
    return out


class ProjK:
    def __init__(self, d, mk):
        self.mk = mk
        self.I, self.names = inv_basis(d)
        zero, one = mk(0), mk(1)
        bydeg = {}
        for idx, v in enumerate(self.I):
            bydeg.setdefault(popc(next(iter(v))), []).append(idx)
        self.blocks = []
        for k, idxs in sorted(bydeg.items()):
            mons = sorted(set(m for i in idxs for m in self.I[i]))
            for combo in itertools.combinations(mons, len(idxs)):
                M = [[mk(0).lift(self.I[i].get(m, 0)) for m in combo] for i in idxs]
                if not (_det(M, zero) == 0):
                    self.blocks.append((idxs, combo, _inv(M, zero, one)))
                    break
            else:
                raise ValueError("no invertible minor in degree %d" % k)

    def split(self, P):
        a, R = {}, dict(P)
        for idxs, combo, Minv in self.blocks:
            vec = [self.mk(0).lift(P.get(m, 0)) for m in combo]
            for ii, i in enumerate(idxs):
                s = self.mk(0)
                for j in range(len(combo)):
                    s = s + vec[j] * Minv[j][ii]
                if not (s == 0):
                    a[i] = s
                    R = sub(R, sc(s, self.I[i]))
        for idxs, combo, Minv in self.blocks:
            assert all(R.get(m, 0) == 0 for m in combo)
        return a, R


def tensor_split(pieces, projs):
    """(II, rest): II[(i, j)] the coefficient of I_i (x) I_j, rest the other
    components (keys mix invariant indices and monomials), zeros removed."""
    II, rest = {}, {}
    for (c, P1, P2) in pieces:
        a1, R1 = projs[0].split(P1)
        a2, R2 = projs[1].split(P2)
        for i, x in a1.items():
            for j, y in a2.items():
                II[(i, j)] = II.get((i, j), 0) + c * x * y
            for m2, y in R2.items():
                key = ("I%d" % i, m2)
                rest[key] = rest.get(key, 0) + c * x * y
        for m1, x in R1.items():
            for j, y in a2.items():
                key = (m1, "I%d" % j)
                rest[key] = rest.get(key, 0) + c * x * y
            for m2, y in R2.items():
                rest[(m1, m2)] = rest.get((m1, m2), 0) + c * x * y
    II = {k: v for k, v in II.items() if not (v == 0)}
    rest = {k: v for k, v in rest.items() if not (v == 0)}
    return II, rest
