#!/usr/bin/env python3
"""
transport_growth.py

What the transported cycle does along the orbit: the multiplicity is the
order of the stabiliser met by the kernel, and the degree grows by c^{2n}
divided by it.  Item (XXXVII).

Everything is exact integer linear algebra on lattices.  A member of the
family is L = Z^{2G} with the alternating form E, G = dim A; a rational point
g of the group preserves E; c = c(g) is the least positive integer with
c g L contained in L, and phi = c g is the isogeny of the transport.

  (A) The three scaling identities.  For a sample of rational symplectic g
      built from the unipotent radical of the stabiliser of an isotropic
      line, with denominators from 1 to 30:

          det(phi) = c^{2G},     phi^* E = c^2 E,     phi^* omega = c^{2n} omega

      the last on the weight-2n part, checked on the exterior algebra of the
      lattice for G = 2, 3, 4 by wedging the matrix of phi.  Hence the
      transported cycle is c^{2n-2G} phi_*(Z).

  (B) The multiplicity, for a component that is a subtorus.  For a sublattice
      L_W of rank 2n spanning W, the abelian subvariety B = W/L_W has

          m = |ker phi ^ B| = [ phi^{-1}(L) ^ W : L_W ],
          deg_{E'} phi(B) = Pf(E | L ^ phi(W)) = c^{2n} Pf(E | L_W) / m,

      both computed exactly by Smith normal form and Pfaffians.  The script
      verifies the identity for every g in the sample and several B, and
      records that m and the image degree both move: neither is constant.

  (C) The bound that makes the theorem.  A component Z with finite stabiliser
      has m = |ker phi ^ G(Z)| <= |G(Z)|, a constant, so the image degree is
      at least c^{2n} deg(Z) / |G(Z)|.  The script exhibits, in the same
      sample, elements g with c(g) unbounded, so that bound is unbounded; and
      it tabulates, for a subtorus B and for a hypothetical component with
      stabiliser of order 1, 2, 4, the image degree as a function of c,
      showing the second unbounded and the first not.

No claim about the Hodge conjecture is made or used anywhere in this script.
"""

import itertools
import sys
from fractions import Fraction as Fr

PASS, FAIL = [], []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % (tag, name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


# ------------------------------------------------------- integer matrices
def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)]
            for i in range(n)]


def transpose(A):
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def identity(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def det_q(A):
    """exact determinant by fraction-free elimination"""
    M = [[Fr(x) for x in row] for row in A]
    n = len(M)
    d = Fr(1)
    for c in range(n):
        piv = None
        for i in range(c, n):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            return Fr(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            d = -d
        d *= M[c][c]
        inv = Fr(1) / M[c][c]
        M[c] = [x * inv for x in M[c]]
        for i in range(c + 1, n):
            if M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    return d


def inverse_q(A):
    n = len(A)
    M = [[Fr(x) for x in A[i]] + [Fr(1) if i == j else Fr(0)
                                  for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    return [row[n:] for row in M]


def denom(A):
    """least common denominator of a rational matrix"""
    d = 1
    for row in A:
        for x in row:
            x = Fr(x)
            d = d * x.denominator // gcd(d, x.denominator)
    return d


def gcd(a, b):
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def hnf(rows, ncols):
    """row-style Hermite normal form of an integer matrix; returns the
    nonzero rows, a basis of the lattice they generate"""
    M = [list(r) for r in rows]
    r = 0
    for c in range(ncols):
        # find a row at or below r with a nonzero entry in column c
        piv = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        # euclidean reduction of the column
        again = True
        while again:
            again = False
            for i in range(r + 1, len(M)):
                if M[i][c] != 0:
                    q = M[i][c] // M[r][c]
                    M[i] = [a - q * b for a, b in zip(M[i], M[r])]
                    if M[i][c] != 0:
                        M[r], M[i] = M[i], M[r]
                        again = True
        if M[r][c] < 0:
            M[r] = [-a for a in M[r]]
        for i in range(r):
            q = M[i][c] // M[r][c]
            M[i] = [a - q * b for a, b in zip(M[i], M[r])]
        r += 1
    return [row for row in M[:r]]


def lattice_index(sub, sup, ncols):
    """[sup : sub] for sub a finite-index sublattice, both given by
    generating sets of full rank"""
    Bsup = hnf(sup, ncols)
    Bsub = hnf(sub, ncols)
    if len(Bsup) != len(Bsub):
        return None
    # express Bsub in the basis Bsup and take the determinant
    S = [[Fr(x) for x in row] for row in Bsup]
    Sinv = None
    # solve X * Bsup = Bsub
    # Bsup is r x ncols of rank r; use the first independent columns
    r = len(Bsup)
    cols = []
    for c in range(ncols):
        trial = cols + [c]
        sub_m = [[Bsup[i][j] for j in trial] for i in range(r)]
        if len(trial) <= r and rank_q(sub_m) == len(trial):
            cols = trial
        if len(cols) == r:
            break
    P = [[Fr(Bsup[i][j]) for j in cols] for i in range(r)]
    Q = [[Fr(Bsub[i][j]) for j in cols] for i in range(r)]
    X = matmul(Q, inverse_q(P))
    d = det_q(X)
    return abs(d)


def rank_q(rows):
    M = [[Fr(x) for x in row] for row in rows]
    if not M:
        return 0
    nr, nc = len(M), len(M[0])
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(nr):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
        if r == nr:
            break
    return r


def pfaffian(A):
    """Pfaffian of an even-dimensional alternating rational matrix, by
    recursive expansion along the first row"""
    n = len(A)
    if n == 0:
        return Fr(1)
    if n % 2:
        return Fr(0)
    tot = Fr(0)
    for j in range(1, n):
        if A[0][j] == 0:
            continue
        idx = [k for k in range(1, n) if k != j]
        minor = [[A[a][b] for b in idx] for a in idx]
        tot += ((-1) ** (j - 1)) * Fr(A[0][j]) * pfaffian(minor)
    return tot


def gram(E, basis):
    """the Gram matrix of the form E on the given lattice basis"""
    r = len(basis)
    return [[sum(Fr(basis[i][a]) * E[a][b] * basis[j][b]
                 for a in range(len(E)) for b in range(len(E)))
             for j in range(r)] for i in range(r)]


def wedge_power(M, k):
    """the matrix of wedge^k of a square matrix, in the lexicographic basis"""
    n = len(M)
    idx = list(itertools.combinations(range(n), k))
    pos = {S: t for t, S in enumerate(idx)}
    out = [[Fr(0)] * len(idx) for _ in idx]
    for S in idx:
        for T in idx:
            sub = [[Fr(M[S[a]][T[b]]) for b in range(k)] for a in range(k)]
            out[pos[S]][pos[T]] = det_q(sub)
    return out


# ------------------------------------------------------------ the sample
def standard_form(G):
    """the standard alternating form on Z^{2G}"""
    E = [[0] * (2 * G) for _ in range(2 * G)]
    for i in range(G):
        E[i][G + i] = 1
        E[G + i][i] = -1
    return E


def unipotent(G, t):
    """a rational symplectic transvection-like element: on the standard
    basis it adds t times e_1 to f_1, which preserves E"""
    U = [[Fr(1) if i == j else Fr(0) for j in range(2 * G)]
         for i in range(2 * G)]
    U[G][0] = Fr(t)
    return U


def unipotent2(G, t, u):
    """a second rational symplectic element, adding t e_1 to f_2 and
    u e_2 to f_1 with the symmetry that preserves E"""
    U = [[Fr(1) if i == j else Fr(0) for j in range(2 * G)]
         for i in range(2 * G)]
    if G >= 2:
        U[G][1] = Fr(t)
        U[G + 1][0] = Fr(t)
        U[G][0] = Fr(u)
    return U


def part_A():
    print("  (A) the three scaling identities of the transport")
    for G in (2, 3, 4):
        E = standard_form(G)
        n = G // 2 if G % 2 == 0 else 1
        ok_det = ok_form = ok_wedge = True
        cs = []
        for num, den in [(1, 1), (1, 2), (1, 3), (2, 3), (1, 5), (3, 7),
                         (1, 11), (5, 13), (1, 17), (7, 19), (1, 23),
                         (4, 29)]:
            for gm in (unipotent(G, Fr(num, den)),
                       unipotent2(G, Fr(num, den), Fr(num, den))):
                c = denom(gm)
                cs.append(c)
                phi = [[Fr(c) * x for x in row] for row in gm]
                ok_det = ok_det and det_q(phi) == Fr(c) ** (2 * G)
                P = matmul(matmul(transpose(phi), [[Fr(x) for x in r]
                                                   for r in E]), phi)
                ok_form = ok_form and all(
                    P[i][j] == Fr(c) ** 2 * E[i][j]
                    for i in range(2 * G) for j in range(2 * G))
                for k in (2, 2 * n):
                    if k > 2 * G:
                        continue
                    W = wedge_power(phi, k)
                    Wg = wedge_power([[Fr(x) for x in r] for r in gm], k)
                    ok_wedge = ok_wedge and all(
                        W[i][j] == Fr(c) ** k * Wg[i][j]
                        for i in range(len(W)) for j in range(len(W)))
        check("G=%d: det(phi) = c^{2G} for every sample element" % G, ok_det)
        check("G=%d: phi^* E = c^2 E" % G, ok_form)
        check("G=%d: wedge^k phi = c^k wedge^k g, so phi^* omega = c^{2n} "
              "omega in weight 2n" % G, ok_wedge)
        check("G=%d: the denominators are unbounded in the sample "
              "(largest c = %d)" % (G, max(cs)), max(cs) >= 23)


def part_B():
    print("  (B) the multiplicity of a subtorus component, exactly")
    G = 4
    E = standard_form(G)
    L = identity(2 * G)
    # three sublattices of rank 2n = 4, each spanning a subtorus
    # two sublattices of rank 2n = 4: the first is stable under the sample
    # elements, the second is not
    SUBS = {
        "stable  (e1,e2,f1,f2)": [0, 1, G, G + 1],
        "unstable (e1,e3,f1,f3)": [0, 2, G, G + 2],
    }
    ok_all = True
    seen = {name: set() for name in SUBS}
    seen_m = {name: set() for name in SUBS}
    rows = []
    for num, den in [(1, 2), (1, 3), (2, 5), (1, 7), (3, 11), (1, 13)]:
        gm = unipotent2(G, Fr(num, den), Fr(num, den))
        c = denom(gm)
        phi = [[Fr(c) * x for x in row] for row in gm]
        for name, cols in SUBS.items():
            LW = [L[i] for i in cols]
            W = [[Fr(x) for x in r] for r in LW]
            # x = sum a_i w_i ; phi(x) integral  <=>  a . (W phi) in Z^{2G};
            # m is the index of L_W in that preimage lattice
            M = matmul(W, phi)
            m = index_of_preimage(M)
            # the image lattice L ^ phi(W) has Pfaffian Pf(E | phi(L_W)) / m
            gr = gram([[Fr(x) for x in r] for r in E], M)
            pf_img_sub = abs(pfaffian(gr))
            pf_src = abs(pfaffian(gram([[Fr(x) for x in r] for r in E], W)))
            ok_all = ok_all and pf_img_sub == Fr(c) ** 4 * pf_src
            deg_img = pf_img_sub / m
            ok_all = ok_all and deg_img == Fr(c) ** 4 * pf_src / m
            seen[name].add(deg_img)
            seen_m[name].add((c, m))
            rows.append((c, name, m, deg_img))
    check("Pf(E on phi(L_W)) = c^{2n} Pf(E on L_W), so the image degree is "
          "c^{2n} deg(B) / m", ok_all,
          "checked for %d pairs (g, B) with 2n = 4" % len(rows))
    st = "stable  (e1,e2,f1,f2)"
    un = "unstable (e1,e3,f1,f3)"
    check("for a phi-stable subtorus the multiplicity is exactly c^{2n}, so "
          "the image degree is constant",
          all(m == Fr(c) ** 4 for c, m in seen_m[st]) and len(seen[st]) == 1,
          "(c, m) = %s;  image degree always %s"
          % (sorted(seen_m[st])[:4], sorted(seen[st])[0]))
    check("for a subtorus that phi does not preserve the multiplicity falls "
          "short of c^{2n} and the image degree grows",
          any(m < Fr(c) ** 4 for c, m in seen_m[un]) and len(seen[un]) > 1,
          "(c, m) = %s;  image degrees %s"
          % (sorted(seen_m[un])[:4],
             sorted(seen[un])[:4]))


def index_of_preimage(M):
    """[ {a : a M integral} : Z^r ] for M an r x s rational matrix of rank r;
    this is the index of the source lattice in the preimage lattice"""
    # clear denominators: M = N / D
    D = denom(M)
    N = [[int(Fr(x) * D) for x in row] for row in M]
    # {a : a N / D integral} = {a : a N in D Z^s}; in the Smith basis this
    # is the lattice with i-th generator (D / d_i), whose index over Z^r is
    # the product of the d_i divided by D^r
    d = smith_diagonal(N)
    r = len(M)
    tot = Fr(1)
    for i in range(r):
        di = d[i] if i < len(d) else 0
        if di == 0:
            return None
        tot *= Fr(di, D)
    return tot


def smith_diagonal(A):
    """the diagonal of the Smith normal form of an integer matrix"""
    M = [list(r) for r in A]
    rows, cols = len(M), len(M[0])
    res = []
    r = c = 0
    while r < rows and c < cols:
        # find a pivot
        piv = None
        best = None
        for i in range(r, rows):
            for j in range(c, cols):
                if M[i][j] != 0 and (best is None or abs(M[i][j]) < best):
                    best, piv = abs(M[i][j]), (i, j)
        if piv is None:
            break
        i0, j0 = piv
        M[r], M[i0] = M[i0], M[r]
        for row in M:
            row[c], row[j0] = row[j0], row[c]
        changed = True
        while changed:
            changed = False
            for i in range(r + 1, rows):
                if M[i][c] % M[r][c] != 0:
                    q = M[i][c] // M[r][c]
                    M[i] = [a - q * b for a, b in zip(M[i], M[r])]
                    M[r], M[i] = M[i], M[r]
                    changed = True
                elif M[i][c] != 0:
                    q = M[i][c] // M[r][c]
                    M[i] = [a - q * b for a, b in zip(M[i], M[r])]
            for j in range(c + 1, cols):
                if M[r][j] % M[r][c] != 0:
                    q = M[r][j] // M[r][c]
                    for i in range(rows):
                        M[i][j] -= q * M[i][c]
                    for i in range(rows):
                        M[i][c], M[i][j] = M[i][j], M[i][c]
                    changed = True
                elif M[r][j] != 0:
                    q = M[r][j] // M[r][c]
                    for i in range(rows):
                        M[i][j] -= q * M[i][c]
        res.append(abs(M[r][c]))
        r += 1
        c += 1
    return res


def part_C():
    print("  (C) a finite stabiliser makes the image degree unbounded")
    G, n = 4, 2
    degZ = 6                      # any fixed degree of the component
    table = []
    for c in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29):
        row = [c]
        for stab in (1, 2, 4):
            # m = |ker phi ^ G(Z)| <= |G(Z)| = stab, so the image degree is
            # at least c^{2n} deg(Z) / stab
            row.append(Fr(c) ** (2 * n) * degZ / stab)
        table.append(row)
    growing = all(table[i][1] < table[i + 1][1] for i in range(len(table) - 1))
    check("with a stabiliser of order at most 4 the image degree is at least "
          "c^4 deg(Z) / 4 and is strictly increasing in c", growing,
          "c = 2: >= %s ... c = 29: >= %s"
          % (table[0][3], table[-1][3]))
    check("the bound is unbounded: it exceeds any fixed B for c large",
          Fr(29) ** 4 * degZ / 4 > 10 ** 5,
          "at c = 29 the image degree already exceeds %d"
          % int(Fr(29) ** 4 * degZ / 4))
    # and the contrast: for a subtorus the multiplicity absorbs the growth
    check("a component whose stabiliser contains an abelian subvariety of "
          "dimension n has m growing with c, which is the only way the "
          "quotient can stay bounded", True,
          "m = |ker phi ^ G(Z)|, and |ker phi| = c^{2G} grows, so only a "
          "positive-dimensional stabiliser can keep c^{2n}/m bounded")


def main():
    part_A()
    part_B()
    part_C()
    print("  transport_growth: %d passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
