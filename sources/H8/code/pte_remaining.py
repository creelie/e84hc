#!/usr/bin/env python3
"""
pte_remaining.py

Completes Theorem 14.40(iv): the three admissible level sets at n = 3 that the
search of pte_search.py left open,

    d = 1 at (13, 52, 117, 130),  (17, 68, 153, 170),  (25, 50, 100, 125),

admit no solution of the full system (14.29).  Here O_K = Z[i] and the levels
have 8, 8, 8, 16 and 12, 12, 12, 16 elements, so the direct meet in the middle
of pte_search.py, which expands a level of sixteen elements in pure Python,
is replaced by a vectorised one.

The search.  The level sums are forced by Theorem 14.40(i) up to the scale S;
every |S| >= 2 violates the box |M_j| <= r_K(N_j), and S -> -S is the
symmetry m -> -m, so S = S_min is the only case.  For each level j every
m in {-1,0,1}^{L_j} with the prescribed sum is enumerated, and its
contribution to the ten integer coordinates

    sum_j N_j^r A_{1,j}  (r = 0,1,2),   sum_j N_j^r A_{2,j}  (r = 0,1),
    A_{k,j} = sum_{Nm(u) = N_j} m_u u^k   (real and imaginary parts)

is recorded.  Levels 1 to 3 are streamed against level 4, matched through a
linear hash of the ten coordinates, and every match is re-checked on all ten
coordinates exactly.  A genuine solution has all ten coordinates zero, so its
hash is zero and it cannot be missed; the exact re-check removes the hash
collisions.  The search is therefore complete.

Needs numpy.  Everything else is integer arithmetic.
"""

import os
import sys
from fractions import Fraction as F
from itertools import product

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pte_search import ring, forced  # noqa: E402

NP = NF = 0


def check(name, ok, detail=""):
    global NP, NF
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("           " + detail)
    if ok:
        NP += 1
    else:
        NF += 1


def signed_levels(nodes, scale=1):
    """M_j = (-1)^n S P / D_j with n = 3."""
    S0, _ = forced(list(nodes))
    P = 1
    for N in nodes:
        P *= N
    out = []
    for j, Nj in enumerate(nodes):
        D = Nj
        for k, Nk in enumerate(nodes):
            if k != j:
                D *= (Nj - Nk)
        x = F(-S0 * scale * P, D)
        assert x.denominator == 1
        out.append(int(x))
    return out


def options(n, s):
    """every m in {-1,0,1}^n with sum s, built from two halves."""
    h = n // 2
    A = np.array(list(product((-1, 0, 1), repeat=h)), dtype=np.int8)
    B = np.array(list(product((-1, 0, 1), repeat=n - h)), dtype=np.int8)
    sa, sb = A.sum(1), B.sum(1)
    out = []
    for t in range(-h, h + 1):
        a, b = A[sa == t], B[sb == s - t]
        if len(a) and len(b):
            out.append(np.hstack([np.repeat(a, len(b), 0),
                                  np.tile(b, (len(a), 1))]))
    return np.vstack(out) if out else np.zeros((0, n), dtype=np.int8)


def search(d, nodes, M):
    mul, elts = ring(d)
    lv = [elts(N) for N in nodes]

    def pw(u, k):
        q = (1, 0)
        for _ in range(k):
            q = mul(q, u)
        return q

    coef = np.random.default_rng(20260923).integers(
        1, 1 << 19, size=10).astype(np.int64)
    H, SIG, T3, cnt = [], [], [], []
    for j, L in enumerate(lv):
        N = nodes[j]
        C = np.array([[pw(u, 1)[0], pw(u, 1)[1],
                       N * pw(u, 1)[0], N * pw(u, 1)[1],
                       N * N * pw(u, 1)[0], N * N * pw(u, 1)[1],
                       pw(u, 2)[0], pw(u, 2)[1],
                       N * pw(u, 2)[0], N * pw(u, 2)[1]] for u in L],
                     dtype=np.int64)
        O = options(len(L), M[j]).astype(np.int64)
        cnt.append(len(O))
        SIG.append(O @ C)
        H.append(SIG[-1] @ coef)
        T3.append(O @ np.array([pw(u, 3) for u in L], dtype=np.int64))
    order = np.argsort(H[3])
    h4 = H[3][order]
    h12 = (H[0][:, None] + H[1][None, :]).ravel()
    n2, n3 = len(H[1]), len(H[2])
    collisions, sols = 0, []
    for c in range(0, len(h12), 2000):
        tgt = -(h12[c:c + 2000][:, None] + H[2][None, :]).ravel()
        pos = np.searchsorted(h4, tgt)
        pos[pos >= len(h4)] = 0
        for q in np.nonzero(h4[pos] == tgt)[0]:
            i12, i3 = divmod(int(c * n3 + q), n3)
            i1, i2 = divmod(i12, n2)
            p = int(pos[q])
            while p < len(h4) and h4[p] == tgt[q]:
                i4 = order[p]
                sig = SIG[0][i1] + SIG[1][i2] + SIG[2][i3] + SIG[3][i4]
                if np.any(sig != 0):
                    collisions += 1
                else:
                    t3 = T3[0][i1] + T3[1][i2] + T3[2][i3] + T3[3][i4]
                    sols.append((int(t3[0]), int(t3[1])))
                p += 1
    return [len(L) for L in lv], cnt, collisions, sols


if __name__ == "__main__":
    print("(XXII, completed) the three open level sets at n = 3")
    # control: a level set already settled by pte_search.py
    cases = [(2, (9, 18, 27, 36)), (1, (5, 20, 45, 50)),
             (1, (13, 52, 117, 130)), (1, (17, 68, 153, 170)),
             (1, (25, 50, 100, 125))]
    for d, nodes in cases:
        mul, elts = ring(d)
        sizes = [len(elts(N)) for N in nodes]
        # only S = +-S_min fits the box
        box = all(any(abs(m) > s for m, s in zip(signed_levels(nodes, k),
                                                 sizes)) for k in (2, 3, 4))
        M = signed_levels(nodes)
        lv, cnt, coll, sols = search(d, nodes, M)
        tag = "control" if nodes in ((9, 18, 27, 36), (5, 20, 45, 50)) \
            else "open"
        check("d=%d, norms %s (%s): no solution of the full system"
              % (d, ",".join(map(str, nodes)), tag),
              box and not sols,
              "level sizes %s, M = %s, sign patterns per level %s, "
              "%d hash collisions rejected, %d exact solutions"
              % (lv, M, cnt, coll, len(sols)))
    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    sys.exit(0 if NF == 0 else 1)
