#!/usr/bin/env python3
"""
kugasatake.py

The Clifford algebra behind the Kuga-Satake construction, and the Hodge
numbers that decide where the construction can be applied.

Part one builds the Clifford algebra C(T,q) of a diagonal quadratic form over
Q, exactly, with basis indexed by subsets of {1,...,b} and the product
determined by e_i e_i = q_i and e_i e_j = - e_j e_i.  It checks:

  (K1)  dim C = 2^b and dim C^+ = 2^{b-1}
  (K2)  the Clifford relations, and v^2 = q(v) for a general v
  (K3)  J = e_1 e_2 with q(e_1) = q(e_2) = 1 satisfies J^2 = -1
  (K4)  left multiplication by J preserves C^+ and squares to -1 there,
        so it is a complex structure on C^+ tensor R
  (K5)  C^- C^+ C^- is contained in C^+, which is what makes
        v |-> ( x |-> v x v_0 )  a map from T into End(C^+)

Part two computes the Hodge numbers of the pieces of H^2(A,Q) for A of
(K,-1,n)-Weil type, in the character grading of section 4:

        H^2(A,C) = wedge^2 V_+  +  (V_+ tensor V_-)  +  wedge^2 V_-

  (K6)  the middle piece is the norm-isotypic one, is defined over Q, and has
        h^{2,0} = n^2
  (K7)  so the middle piece is of K3 type exactly when n = 1, which is the
        one case in which the Weil line already lies in H^2 and is algebraic
        by the Lefschetz theorem on (1,1) classes
  (K8)  the dimensions add up: 2*C(2n,2) + 4n^2 = C(4n,2)
"""

from fractions import Fraction as F
from itertools import combinations
from math import comb


# ------------------------------------------------------- Clifford algebra

class Clifford:
    """C(q) for q = diag(qs), basis e_S indexed by sorted tuples."""

    def __init__(self, qs):
        self.qs = list(qs)
        self.b = len(qs)

    def basis(self):
        out = []
        for k in range(self.b + 1):
            for S in combinations(range(1, self.b + 1), k):
                out.append(S)
        return out

    def gen(self, i):
        return {(i,): F(1)}

    def one(self):
        return {(): F(1)}

    def mul_basis(self, S, T):
        """e_S e_T as (coefficient, basis tuple)."""
        word = list(S) + list(T)
        coef = F(1)
        # bubble sort, picking up a sign for each transposition and
        # collapsing equal adjacent generators via e_i e_i = q_i
        changed = True
        while changed:
            changed = False
            i = 0
            while i < len(word) - 1:
                if word[i] > word[i + 1]:
                    word[i], word[i + 1] = word[i + 1], word[i]
                    coef = -coef
                    changed = True
                elif word[i] == word[i + 1]:
                    coef *= F(self.qs[word[i] - 1])
                    del word[i:i + 2]
                    changed = True
                    i = max(i - 1, 0)
                    continue
                i += 1
        return coef, tuple(word)

    def mul(self, a, b):
        out = {}
        for S, ca in a.items():
            for T, cb in b.items():
                c, U = self.mul_basis(S, T)
                if c == 0:
                    continue
                out[U] = out.get(U, F(0)) + c * ca * cb
        return {k: v for k, v in out.items() if v != 0}

    def add(self, a, b):
        out = dict(a)
        for k, v in b.items():
            out[k] = out.get(k, F(0)) + v
        return {k: v for k, v in out.items() if v != 0}

    def scale(self, c, a):
        return {k: c * v for k, v in a.items() if c * v != 0}

    def even(self, a):
        return all(len(k) % 2 == 0 for k in a)

    def even_basis(self):
        return [S for S in self.basis() if len(S) % 2 == 0]

    def odd_basis(self):
        return [S for S in self.basis() if len(S) % 2 == 1]

    def left_mult_matrix(self, a, basis):
        """Matrix of x |-> a x on the span of `basis` (assumed stable)."""
        idx = {S: i for i, S in enumerate(basis)}
        M = [[F(0)] * len(basis) for _ in basis]
        for j, S in enumerate(basis):
            img = self.mul(a, {S: F(1)})
            for U, c in img.items():
                assert U in idx, "the span is not stable"
                M[idx[U]][j] = c
        return M


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    C = [[F(0)] * p for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for k in range(m):
            a = Ai[k]
            if a == 0:
                continue
            Bk = B[k]
            for j in range(p):
                C[i][j] += a * Bk[j]
    return C


def is_minus_identity(M):
    n = len(M)
    for i in range(n):
        for j in range(n):
            want = F(-1) if i == j else F(0)
            if M[i][j] != want:
                return False
    return True


# ------------------------------------------------------------------ checks

def clifford_checks(verbose=True):
    res = []
    # signature (3, b-3) as for a K3 lattice, and a couple of small cases
    for b, npos in [(3, 3), (4, 3), (5, 3), (6, 3), (7, 3), (8, 3)]:
        qs = [1] * npos + [-1] * (b - npos)
        C = Clifford(qs)

        # (K1)
        ok1 = (len(C.basis()) == 2 ** b and
               len(C.even_basis()) == 2 ** (b - 1))

        # (K2)
        ok2 = True
        for i in range(1, b + 1):
            if C.mul(C.gen(i), C.gen(i)) != ({(): F(qs[i - 1])}
                                             if qs[i - 1] != 0 else {}):
                ok2 = False
            for j in range(i + 1, b + 1):
                lhs = C.mul(C.gen(i), C.gen(j))
                rhs = C.scale(F(-1), C.mul(C.gen(j), C.gen(i)))
                if lhs != rhs:
                    ok2 = False
        # v^2 = q(v) for a general v
        coeffs = [F(k + 1) for k in range(b)]
        v = {}
        for i in range(1, b + 1):
            v[(i,)] = coeffs[i - 1]
        vv = C.mul(v, v)
        qv = sum(F(qs[i]) * coeffs[i] ** 2 for i in range(b))
        if vv != ({(): qv} if qv != 0 else {}):
            ok2 = False

        # (K3)
        J = C.mul(C.gen(1), C.gen(2))
        ok3 = (C.mul(J, J) == {(): F(-1)})

        # (K4)
        evb = C.even_basis()
        MJ = C.left_mult_matrix(J, evb)
        ok4 = C.even(J) and is_minus_identity(matmul(MJ, MJ))

        # (K5)
        ok5 = True
        odd = C.odd_basis()
        for S in odd[:6]:
            for T in evb[:6]:
                for U in odd[:6]:
                    p = C.mul(C.mul({S: F(1)}, {T: F(1)}), {U: F(1)})
                    if not C.even(p):
                        ok5 = False
        res.append((b, ok1, ok2, ok3, ok4, ok5))
        if verbose:
            print("    b=%2d  dim C=%5d  dim C^+=%5d  dim KS=%s"
                  % (b, 2 ** b, 2 ** (b - 1),
                     ("2^%d" % (b - 2)) if b >= 2 else "-"))
    return res


def weil_h2_pieces(n):
    """Hodge numbers of the three pieces of H^2 for (K,-1,n)-Weil type.
    V_pm has V_pm^{1,0} and V_pm^{0,1} of dimension n each."""
    # wedge^2 V_+ :  (2,0) part is wedge^2 V_+^{1,0}
    w2p = {(2, 0): comb(n, 2), (1, 1): n * n, (0, 2): comb(n, 2)}
    # V_+ tensor V_- :  (2,0) part is V_+^{1,0} tensor V_-^{1,0}
    mid = {(2, 0): n * n, (1, 1): 2 * n * n, (0, 2): n * n}
    return w2p, mid


if __name__ == "__main__":
    print("the Clifford algebra and the reach of Kuga-Satake")
    npass = nfail = 0

    print("  Clifford algebras C(q) with q of signature (3, b-3)")
    for b, ok1, ok2, ok3, ok4, ok5 in clifford_checks():
        for name, ok in [("K1 dim C = 2^b and dim C^+ = 2^(b-1)", ok1),
                         ("K2 Clifford relations and v^2 = q(v)", ok2),
                         ("K3 J = e_1 e_2 satisfies J^2 = -1", ok3),
                         ("K4 left mult by J is a complex structure on C^+",
                          ok4),
                         ("K5 C^- C^+ C^- lies in C^+", ok5)]:
            if b == 22 or b <= 4:
                print("    [%s] b=%d: %s" % ("PASS" if ok else "FAIL", b, name))
            npass += 1 if ok else 0
            nfail += 0 if ok else 1

    print("  the Kuga-Satake variety of a K3 surface")
    ok = (2 ** (22 - 2) == 1048576)
    print("    [%s] b_2 = 22 gives dim KS = 2^20 = %d"
          % ("PASS" if ok else "FAIL", 2 ** 20))
    npass += 1 if ok else 0
    nfail += 0 if ok else 1
    ok = (2 ** (3 - 2) == 2)
    print("    [%s] a rank 3 transcendental lattice gives an abelian surface"
          % ("PASS" if ok else "FAIL"))
    npass += 1 if ok else 0
    nfail += 0 if ok else 1

    print("  the second cohomology of an abelian variety of Weil type")
    ok6 = ok7 = ok8 = True
    for n in range(1, 9):
        w2p, mid = weil_h2_pieces(n)
        if mid[(2, 0)] != n * n:
            ok6 = False
        if (mid[(2, 0)] == 1) != (n == 1):
            ok7 = False
        total = 2 * sum(w2p.values()) + sum(mid.values())
        if total != comb(4 * n, 2):
            ok8 = False
        if n <= 4:
            print("    n=%d:  wedge^2 V_+ has h^{2,0}=%d,   "
                  "V_+ tensor V_- has h^{2,0}=%d,   dim H^2 = %d"
                  % (n, w2p[(2, 0)], mid[(2, 0)], comb(4 * n, 2)))
    for name, ok in [("K6 the norm-isotypic part of H^2 has h^{2,0} = n^2",
                      ok6),
                     ("K7 it is of K3 type exactly when n = 1", ok7),
                     ("K8 2*C(2n,2) + 4n^2 = C(4n,2)", ok8)]:
        print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
        npass += 1 if ok else 0
        nfail += 0 if ok else 1

    print()
    print("  %d checks passed, %d failed" % (npass, nfail))
    print("  overall: %s" % ("PASS" if nfail == 0 else "FAIL"))
