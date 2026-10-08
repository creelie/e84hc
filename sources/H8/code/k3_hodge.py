#!/usr/bin/env python3
"""
k3_hodge.py

Item (LXI) of the computations: Hodge classes on the powers and Hilbert
schemes of a K3 surface and on varieties of K3^[n] type, for
prop:k3powers, prop:k3ntype, cor:fanolines and prop:aclosure(v).

Notation.  H^2 = H^2(X, Q) of a variety of K3^[2] type is the
Beauville-Bogomolov lattice U^3 + E_8(-1)^2 + <-2> (rank 23, Gram matrix G)
tensored with Q, and the polarised Fujiki relation with constant 3 is
    int a b c d = q(a,b) q(c,d) + q(a,c) q(b,d) + q(a,d) q(b,c).
For K3^[n] type the Fujiki constant is c_n = (2n)!/(n! 2^n).  NS = <h, e>
with q(h) = 2 and e a root of E_8(-1); T = NS^perp, of dimension 21.  For a
q-self-adjoint operator phi of T, c_phi = sum_i t_i^vee . phi(t_i) in
Sym^2 T, with (t_i^vee) the q-dual basis of (t_i).

What is checked:

  (A) the Betti numbers of S^[2] for a K3 surface S, from the decomposition
      of de Cataldo and Migliorini (Sym^2 H^*(S) plus H^*(S) shifted by
      two) and from Goettsche's product formula: (1,0,23,0,276,0,23,0,1),
      so b_4 = 276 = dim Sym^2 H^2 and the Euler number is 324;

  (B) the pairing on Sym^2 H^2 given by the Fujiki relation has determinant
      det(G)^(m+1) 2^(m-1) (m+2), m = dim H^2, in the monomial basis (checked
      on random lattices of rank 2 to 6 and on the lattice of rank 23, where
      it is 2^46 . 25); it is nonzero, so Sym^2 H^2 -> H^4 is injective and,
      with (A), an isomorphism;

  (C) q^vee = sum G^{ij} e_i e_j satisfies int q^vee x y = 25 q(x,y) on all
      basis pairs; c_2 = (6/5) q^vee satisfies int c_2 x y = 30 q(x,y),
      which is the Riemann-Roch polynomial chi(L) = binom(q(L)/2 + 3, 2);
      int c_2^2 = 828, and with c_4 = 324, Todd_4 = (3.828 - 324)/720 = 3,
      the value of chi(O_X);

  (D) on examples, exactly: int c_phi x y = tr(phi) q(x,y) + 2 q(phi x, y)
      for x in T and y in H^2; the polarised Fujiki formula
      int x y h^(2n-2) = c_n/(2n-1) q(h)^(n-2) [q(h) q(x,y)
      + 2(n-1) q(x,h) q(y,h)] for n = 2, 3, 4; for a random rational
      isometry u of T (a Cayley transform) and n = 2, 3, the restriction to
      the diagonal of sum_i b_i (x) f(a_i), f = id_NS + u, (b_i) the dual
      basis of (a_i) for int x y h^(2n-2), is kappa^{-1} c_{(u+u^*)/2} plus
      a class of Sym^2 NS, kappa = c_n/(2n-1) q(h)^(n-1); and for n = 2 the
      operator x -> L^{-2}(c_phi x) acts on T as (tr(phi) + 2 phi)/q(h);

  (E) for every t <= 21 the least n such that some partition of n has t
      distinct part sizes is t(t+1)/2 (a dynamic programme over all
      partitions of n <= 240, confirmed by listing the partitions of n <= 30);
      for a very general K3 surface, t = 21 and t(t+1)/2 = 231;

  (F) for W = Q + T, T = Q^t with the standard form, and a group G
      permuting the factors of W^(x)l in blocks of sizes a_1, ..., a_r, the
      G-invariant SO(t)-invariants of W^(x)l are O(t)-invariant exactly when
      r < t (t = 3 with l <= 4 and t = 4 with l = 4, by exact ranks); and the
      symmetrisation of det(T) placed on t factors vanishes when two of them
      lie in one block, and not otherwise;

  (G) the elements of norm one span E, and the elements (u + ubar)/2 span
      its totally real subfield E_0, for ten CM fields of degree 2 to 10
      (the Cayley elements (1 + s y)/(1 - s y), y purely imaginary);

  (H) the cohomology of the generalised Kummer variety K_{m-1}(A) of an
      abelian surface, sector by sector with the action of A[m], for
      m = 2, ..., 6: the Euler numbers m^3 sigma(m) = 24, 108, 448, 750, 2592,
      the known Betti numbers for m = 3, 4, the A[m]-invariant part equal to
      P(A^[m])/(1+z)^4 (Goettsche's formula), the non-invariant part (15; 80;
      15, 345, 15 in degrees 4, 6, 8; 624; ...), carried only by sectors that
      are finite sets of points exactly when m is prime;

  (I) for six Galois totally real fields E, the span of the elements of E
      with rational square (the compositum E_mq of the quadratic subfields):
      Q for the cyclic cubic and quintic fields Q(zeta_7)^+, Q(zeta_9)^+,
      Q(zeta_11)^+, Q(sqrt 2) for Q(sqrt(2 + sqrt 2)), Q(sqrt 5) for
      Q(zeta_15)^+, and all of Q(sqrt 2, sqrt 3).

Everything is exact: rational arithmetic, and python-flint for the
determinant of (B) and the integer ranks of (F).  The longer attack scripts
behind these checks are in attack/gaps/f3prime/ (m1_ to m6_), with their
transcripts.

Run:  python3 k3_hodge.py
"""
import itertools
import random
from fractions import Fraction as Fr
from math import comb, factorial, gcd
from functools import reduce

import flint

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("         " + detail)


# ------------------------------------------------------------ linear algebra
def mat(r, c, f=lambda i, j: Fr(0)):
    return [[f(i, j) for j in range(c)] for i in range(r)]


def mul(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(row, col)) for col in Bt] for row in A]


def tr(A):
    return [list(r) for r in zip(*A)]


def add(A, B, s=1):
    return [[a + s * b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def scal(c, A):
    return [[c * a for a in r] for r in A]


def eye(n):
    return mat(n, n, lambda i, j: Fr(int(i == j)))


def inv(M):
    n = len(M)
    A = [list(map(Fr, r)) + [Fr(int(i == j)) for j in range(n)]
         for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [r[n:] for r in A]


def nullspace(M, ncols):
    """basis of {v : M v = 0} over Q, as a list of column vectors."""
    A = [list(map(Fr, r)) for r in M]
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [Fr(0)] * ncols
        v[fc] = Fr(1)
        for i, pc in enumerate(piv):
            v[pc] = -A[i][fc]
        basis.append(v)
    return basis


def rank_q(rows):
    if not rows:
        return 0
    A = [list(map(Fr, r)) for r in rows]
    rk, ncols = 0, len(A[0])
    for c in range(ncols):
        p = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[rk], A[p] = A[p], A[rk]
        for i in range(rk + 1, len(A)):
            if A[i][c] != 0:
                f = A[i][c] / A[rk][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[rk])]
        rk += 1
    return rk


# ------------------------------------------------ the Beauville-Bogomolov lattice
def bb_lattice():
    n = 23
    G = [[0] * n for _ in range(n)]
    for k in range(3):
        G[2 * k][2 * k + 1] = G[2 * k + 1][2 * k] = 1
    C = [[0] * 8 for _ in range(8)]
    for i in range(8):
        C[i][i] = 2
    for a, b in [(0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (1, 3)]:
        C[a][b] = C[b][a] = -1
    for blk in range(2):
        off = 6 + 8 * blk
        for i in range(8):
            for j in range(8):
                G[off + i][off + j] = -C[i][j]
    G[22][22] = -2
    return G


def int_sym_xy(M, G, x, y):
    """int (sum_ij M_ij e_i e_j) x y for the Fujiki relation with constant 3
    (M symmetric): tr(M G) q(x,y) + 2 (Gx)^T M (Gy)."""
    n = len(G)
    Gx = [sum(G[i][j] * x[j] for j in range(n)) for i in range(n)]
    Gy = [sum(G[i][j] * y[j] for j in range(n)) for i in range(n)]
    qxy = sum(x[i] * Gy[i] for i in range(n))
    trMG = sum(M[i][j] * G[j][i] for i in range(n) for j in range(n))
    cross = sum(Gx[i] * M[i][j] * Gy[j] for i in range(n) for j in range(n))
    return trMG * qxy + 2 * cross


# ------------------------------------------------------------------ (A)
def part_A():
    bS = [1, 0, 22, 0, 1]
    # de Cataldo-Migliorini: H^*(S^[2]) = Sym^2 H^*(S) + H^*(S)[-2]
    sq = [0] * 9
    for i, a in enumerate(bS):
        for j, b in enumerate(bS):
            sq[i + j] += a * b
    spread = [0] * 9
    for i, a in enumerate(bS):
        spread[2 * i] += a
    sym2 = [(s + p) // 2 for s, p in zip(sq, spread)]
    dcm = [sym2[k] + (bS[k - 2] if 2 <= k <= 6 else 0) for k in range(9)]
    # Goettsche's product formula, coefficient of t^2 (integer series)
    b = bS
    ser = [dict() for _ in range(3)]
    ser[0][0] = 1
    for k in range(1, 3):
        for i in range(5):
            if b[i] == 0:
                continue
            a = 2 * k - 2 + i
            new = [dict() for _ in range(3)]
            for td in range(3):
                for zd, c in ser[td].items():
                    j = 0
                    while td + j * k <= 2:
                        cc = comb(b[i] + j - 1, j)
                        key = zd + j * a
                        new[td + j * k][key] = new[td + j * k].get(key, 0) + c * cc
                        j += 1
            ser = new
    got = [ser[2].get(k, 0) for k in range(9)]
    want = [1, 0, 23, 0, 276, 0, 23, 0, 1]
    check("Betti numbers of S^[2]: (1,0,23,0,276,0,23,0,1) from the "
          "decomposition of de Cataldo-Migliorini and from Goettsche's formula",
          dcm == want and got == want)
    check("b_4(S^[2]) = 276 = dim Sym^2 H^2 = 23.24/2, b_odd = 0, Euler "
          "number 324", want[4] == 23 * 24 // 2 and sum(want) == 324)


# ------------------------------------------------------------------ (B)
def sym2_pairing(G):
    m = len(G)
    pairs = [(i, j) for i in range(m) for j in range(i, m)]
    ent = [G[i][j] * G[k][l] + G[i][k] * G[j][l] + G[i][l] * G[j][k]
           for (i, j) in pairs for (k, l) in pairs]
    return flint.fmpz_mat(len(pairs), len(pairs), ent)


def part_B():
    rng = random.Random(191)
    ok = True
    for m in range(2, 7):
        for _ in range(3):
            A = [[rng.randint(-3, 3) for _ in range(m)] for _ in range(m)]
            G = [[A[i][j] + A[j][i] + (2 * rng.randint(-2, 2) if i == j else 0)
                  for j in range(m)] for i in range(m)]
            dG = int(flint.fmpz_mat(m, m, [x for r in G for x in r]).det())
            dP = int(sym2_pairing(G).det())
            ok = ok and dP == dG ** (m + 1) * 2 ** (m - 1) * (m + 2)
    check("the Fujiki pairing on Sym^2 V has determinant "
          "det(G)^(m+1) 2^(m-1) (m+2) (15 random forms, m = 2..6)", ok)
    G = bb_lattice()
    dG = int(flint.fmpz_mat(23, 23, [x for r in G for x in r]).det())
    dP = int(sym2_pairing(G).det())
    check("on the Beauville-Bogomolov lattice (det 2, rank 23) the pairing "
          "on Sym^2 H^2 (276 x 276) has determinant 2^46 . 25 != 0, so "
          "Sym^2 H^2 -> H^4 is injective",
          dG == 2 and dP == 2 ** 46 * 25 == dG ** 24 * 2 ** 22 * 25,
          "det = %d" % dP)


# ------------------------------------------------------------------ (C)
def part_C():
    G = bb_lattice()
    Gi = inv(G)
    n = 23
    E = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    ok = all(int_sym_xy(Gi, G, E[k], E[l]) == 25 * G[k][l]
             for k in range(n) for l in range(k, n))
    check("int q^vee x y = 25 q(x,y) on all basis pairs", ok)
    c2 = scal(Fr(6, 5), Gi)
    ok = all(int_sym_xy(c2, G, E[k], E[l]) == 30 * G[k][l]
             for k in range(n) for l in range(k, n))
    # int c c' = sum M_ij M'_kl (G_ij G_kl + G_ik G_jl + G_il G_jk)
    MG = mul(c2, G)
    trMG = sum(MG[i][i] for i in range(n))
    MGMG = mul(MG, MG)
    c2sq = trMG ** 2 + 2 * sum(MGMG[i][i] for i in range(n))
    check("c_2 = (6/5) q^vee: int c_2 x y = 30 q(x,y) on all basis pairs, "
          "int c_2^2 = 828", ok and c2sq == 828)
    c4 = 324
    td4 = Fr(3 * c2sq - c4, 720)
    # chi(L) = int L^4/24 + int c_2 L^2/24 + Todd_4 with int L^4 = 3 q^2
    chi = [td4, Fr(30, 24), Fr(3, 24)]           # coefficients of 1, q, q^2
    target = [Fr(3), Fr(5, 4), Fr(1, 8)]         # binom(q/2 + 3, 2)
    check("Todd_4 = (3.828 - 324)/720 = 3 = chi(O_X), and Riemann-Roch gives "
          "chi(L) = binom(q(L)/2 + 3, 2)", td4 == 3 and chi == target)


# ------------------------------------------------------------------ (D)
def fujiki_general(vs, c, q):
    """symmetric multilinear form with F(a,...,a) = c q(a)^n, by matchings."""
    def matchings(lst):
        if not lst:
            yield []
            return
        a = lst[0]
        for i in range(1, len(lst)):
            rest = lst[1:i] + lst[i + 1:]
            for mm in matchings(rest):
                yield [(a, lst[i])] + mm
    k = len(vs)
    df = 1
    for i in range(1, k, 2):
        df *= i
    tot = Fr(0)
    for mm in matchings(list(range(k))):
        p = Fr(1)
        for a, b in mm:
            p *= q(vs[a], vs[b])
        tot += p
    return Fr(c, df) * tot


def part_D():
    rng = random.Random(2026)
    G = bb_lattice()
    n = 23
    Gf = [[Fr(x) for x in r] for r in G]

    def q(x, y):
        return sum(x[i] * G[i][j] * y[j] for i in range(n) for j in range(n)
                   if G[i][j])
    E = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    h = [E[0][i] + E[1][i] for i in range(n)]          # q(h) = 2
    e = E[6]                                            # a root, q = -2
    NS = [h, e]
    Gh = [sum(G[i][j] * h[j] for j in range(n)) for i in range(n)]
    Ge = [sum(G[i][j] * e[j] for j in range(n)) for i in range(n)]
    Tb = nullspace([Gh, Ge], n)                          # T = NS^perp
    m = len(Tb)
    Tm = tr(Tb)                                          # n x m
    GT = mul(mul(tr(Tm), Gf), Tm)
    GTi = inv(GT)
    # a random q_T-self-adjoint phi = GT^{-1} S
    S = mat(m, m)
    for a in range(m):
        for b in range(a, m):
            S[a][b] = S[b][a] = Fr(rng.randint(-3, 3))
    phi = mul(GTi, S)

    def cphi(P):
        """symmetric matrix of c_P = sum_a t_a^vee . P(t_a)."""
        M = mul(mul(Tm, GTi), mul(tr(P), tr(Tm)))
        return [[(M[i][j] + M[j][i]) / 2 for j in range(n)] for i in range(n)]
    Mphi = cphi(phi)
    trphi = sum(phi[a][a] for a in range(m))
    ok = True
    for a in range(4):
        x = [r[a] for r in Tm]
        phix = [sum(Tm[i][b] * phi[b][a] for b in range(m)) for i in range(n)]
        for k in range(n):
            ok = ok and int_sym_xy(Mphi, G, x, E[k]) == \
                trphi * q(x, E[k]) + 2 * q(phix, E[k])
    check("int c_phi x y = tr(phi) q(x,y) + 2 q(phi x, y) for x in T, y in "
          "H^2, phi a random self-adjoint operator of T (dim T = 21)", ok)

    # the polarised Fujiki formula on a small lattice, n = 2, 3, 4
    Q4 = [[2, 1, 0, 0], [1, -2, 0, 0], [0, 0, -2, 1], [0, 0, 1, 4]]

    def q4(x, y):
        return sum(x[i] * Q4[i][j] * y[j] for i in range(4) for j in range(4))
    B4 = [[Fr(int(i == j)) for j in range(4)] for i in range(4)]
    hh = [Fr(1), Fr(1), Fr(0), Fr(1)]
    ok = True
    for nn in (2, 3, 4):
        cn = factorial(2 * nn) // (factorial(nn) * 2 ** nn)
        for x in B4:
            for y in B4:
                lhs = fujiki_general([x, y] + [hh] * (2 * nn - 2), cn, q4)
                rhs = Fr(cn, 2 * nn - 1) * q4(hh, hh) ** (nn - 2) * (
                    q4(hh, hh) * q4(x, y) + 2 * (nn - 1) * q4(x, hh) * q4(y, hh))
                ok = ok and lhs == rhs
    check("int x y h^(2n-2) = c_n/(2n-1) q(h)^(n-2) [q(h) q(x,y) + 2(n-1) "
          "q(x,h) q(y,h)] for n = 2, 3, 4 (c_n = 3, 15, 105)", ok)

    # a rational isometry u of T: Cayley transform of a q_T-skew operator
    K = mat(m, m)
    for a in range(m):
        for b in range(a + 1, m):
            v = Fr(rng.randint(-2, 2), rng.randint(1, 3))
            K[a][b], K[b][a] = v, -v
    A = mul(GTi, K)
    u = mul(add(eye(m), A, -1), inv(add(eye(m), A)))
    iso = mul(mul(tr(u), GT), u) == GT
    ustar = mul(mul(GTi, tr(u)), GT)
    uplus = scal(Fr(1, 2), add(u, ustar))
    # f = id_NS + u in the standard basis: P = [NS | T]
    P = tr(NS + Tb)
    Pi = inv(P)
    blk = mat(n, n)
    blk[0][0] = blk[1][1] = Fr(1)
    for a in range(m):
        for b in range(m):
            blk[2 + a][2 + b] = u[a][b]
    f = mul(mul(P, blk), Pi)
    qh = q(h, h)
    Nm = tr(NS)                                          # n x 2
    ok = iso and uplus != scal(uplus[0][0], eye(m))
    for nn in (2, 3):
        cn = factorial(2 * nn) // (factorial(nn) * 2 ** nn)
        c0 = Fr(cn, 2 * nn - 1) * qh ** (nn - 2)
        Bm = [[c0 * (qh * G[i][j] + 2 * (nn - 1) * Gh[i] * Gh[j])
               for j in range(n)] for i in range(n)]
        Zp = mul(inv(Bm), tr(f))            # Zp[r][s] = sum_i b_i[r] f(e_i)[s]
        mZ = [[(Zp[i][j] + Zp[j][i]) / 2 for j in range(n)] for i in range(n)]
        kappa = Fr(cn, 2 * nn - 1) * qh ** (nn - 1)
        Mu = cphi(uplus)
        diff = [[mZ[i][j] - Mu[i][j] / kappa for j in range(n)]
                for i in range(n)]
        # diff must be N K N^T with K symmetric 2 x 2: solve on rows 0 and 6
        rows = [0, 6]
        Ns = [[Nm[r][c] for c in range(2)] for r in rows]
        Nsi = inv(Ns)
        Dsub = [[diff[r][s] for s in rows] for r in rows]
        Kk = mul(mul(Nsi, Dsub), tr(Nsi))
        ok = ok and mul(mul(Nm, Kk), tr(Nm)) == diff
    check("for a random rational isometry u of T and n = 2, 3: Delta^* of "
          "sum_i b_i (x) (id_NS + u)(a_i) is kappa^{-1} c_{(u+u^*)/2} plus a "
          "class of Sym^2 NS", ok)

    # n = 2: x -> L^{-2}(c_phi x) acts on T as (tr phi + 2 phi)/q(h)
    Bm = [[qh * G[i][j] + 2 * Gh[i] * Gh[j] for j in range(n)]
          for i in range(n)]
    Bi = inv(Bm)
    ok = True
    for a in range(3):
        x = [r[a] for r in Tm]
        rhs = [int_sym_xy(Mphi, G, x, E[k]) for k in range(n)]
        z = [sum(Bi[i][k] * rhs[k] for k in range(n)) for i in range(n)]
        pred = [(trphi * x[i] + 2 * sum(Tm[i][b] * phi[b][a]
                                       for b in range(m))) / qh
                for i in range(n)]
        ok = ok and z == pred
    check("for n = 2 the operator x -> L^{-2}(c_phi x) acts on T as "
          "(tr(phi) + 2 phi)/q(h)", ok)


# ------------------------------------------------------------------ (E)
def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def part_E():
    N = 240
    NEG = -1
    D = [NEG] * (N + 1)
    D[0] = 0
    for j in range(1, N + 1):        # decide the multiplicity of the part j
        new = D[:]
        for s in range(N + 1):
            if D[s] == NEG:
                continue
            mlt = 1
            while s + mlt * j <= N:
                new[s + mlt * j] = max(new[s + mlt * j], D[s] + 1)
                mlt += 1
        D = new
    ok = all(min(n for n in range(N + 1) if D[n] >= t) == t * (t + 1) // 2
             for t in range(1, 22))
    brute = all(max(len(set(p)) for p in partitions(n)) == D[n]
                for n in range(1, 31))
    check("for t = 1..21 the least n with a partition of n into t distinct "
          "part sizes is t(t+1)/2 (all partitions of n <= 240, and a list of "
          "the partitions of n <= 30)", ok and brute,
          "t = 21: n = %d" % (21 * 22 // 2))


# ------------------------------------------------------------------ (F)
def tensor_index(digits, d):
    r = 0
    for x in digits:
        r = r * d + x
    return r


def invariant_dims(t, blocks):
    """dims of the G-invariant SO(t)- and O(t)-invariants in W^(x)l,
    W = Q + T, T = Q^t, G = product of symmetric groups on the blocks."""
    d = t + 1
    l = sum(blocks)
    Nn = d ** l
    allidx = list(itertools.product(range(d), repeat=l))
    rows = []
    # so(t): L_ab e_a = e_b, L_ab e_b = -e_a (a, b >= 1), derivations
    for a in range(1, d):
        for b in range(a + 1, d):
            M = [[0] * Nn for _ in range(Nn)]
            for col, dig in enumerate(allidx):
                for pos in range(l):
                    x = dig[pos]
                    if x == a:
                        nd = list(dig)
                        nd[pos] = b
                        M[tensor_index(nd, d)][col] += 1
                    elif x == b:
                        nd = list(dig)
                        nd[pos] = a
                        M[tensor_index(nd, d)][col] -= 1
            rows.extend(M)
    # G: adjacent transpositions inside each block, minus the identity
    start = 0
    for a in blocks:
        for pos in range(start, start + a - 1):
            M = [[0] * Nn for _ in range(Nn)]
            for col, dig in enumerate(allidx):
                nd = list(dig)
                nd[pos], nd[pos + 1] = nd[pos + 1], nd[pos]
                M[tensor_index(nd, d)][col] += 1
                M[col][col] -= 1
            rows.extend(M)
        start += a
    so = Nn - flint.fmpz_mat(len(rows), Nn,
                             [x for r in rows for x in r]).rank()
    # the reflection e_1 -> -e_1
    M = [[0] * Nn for _ in range(Nn)]
    for col, dig in enumerate(allidx):
        M[col][col] = (-1) ** sum(1 for x in dig if x == 1) - 1
    rows.extend(M)
    o = Nn - flint.fmpz_mat(len(rows), Nn,
                            [x for r in rows for x in r]).rank()
    return so, o


def part_F():
    cases = [(3, (3,)), (3, (2, 1)), (3, (1, 1, 1)), (3, (4,)), (3, (3, 1)),
             (3, (2, 2)), (3, (2, 1, 1)), (3, (1, 1, 1, 1)),
             (4, (4,)), (4, (2, 2)), (4, (2, 1, 1)), (4, (1, 1, 1, 1))]
    ok, info = True, []
    for t, blocks in cases:
        so, o = invariant_dims(t, blocks)
        ok = ok and ((so > o) == (len(blocks) >= t))
        info.append("t=%d %s: %d/%d" % (t, blocks, so, o))
    check("the G-invariant SO(t)-invariants of (Q + T)^(x)l exceed the "
          "O(t)-invariants exactly when there are at least t blocks "
          "(12 cases, t = 3, 4)", ok, "; ".join(info[:6]))
    print("         " + "; ".join(info[6:]))

    # the symmetrisation of det(T) on t factors, t = 3, l = 4
    rng = random.Random(3)
    t, l = 3, 4
    dmn = t + 1

    def det_tensor(I, y):
        """det on the factors I (T-part, indices 1..t), y on the others."""
        out = {}
        rest = [p for p in range(l) if p not in I]
        for perm in itertools.permutations(range(1, t + 1)):
            sgn = 1
            pl = list(perm)
            for i in range(len(pl)):
                for j in range(i + 1, len(pl)):
                    if pl[i] > pl[j]:
                        sgn = -sgn
            for ydig in itertools.product(range(dmn), repeat=len(rest)):
                cy = 1
                for pos, v in zip(rest, ydig):
                    cy *= y[pos][v]
                if cy == 0:
                    continue
                dig = [0] * l
                for pos, v in zip(I, pl):
                    dig[pos] = v
                for pos, v in zip(rest, ydig):
                    dig[pos] = v
                key = tuple(dig)
                out[key] = out.get(key, 0) + sgn * cy
        return out

    def symmetrise(tens, blocks):
        groups, start = [], 0
        for a in blocks:
            groups.append(list(range(start, start + a)))
            start += a
        out = {}
        for perms in itertools.product(*[list(itertools.permutations(g))
                                         for g in groups]):
            sigma = list(range(l))
            for g, pg in zip(groups, perms):
                for src, dst in zip(g, pg):
                    sigma[src] = dst
            for key, c in tens.items():
                nk = [0] * l
                for pos in range(l):
                    nk[sigma[pos]] = key[pos]
                nk = tuple(nk)
                out[nk] = out.get(nk, 0) + c
        return {k: c for k, c in out.items() if c}

    ok = True
    for blocks in [(2, 1, 1), (2, 2), (3, 1), (1, 1, 1, 1)]:
        groups, start = [], 0
        for a in blocks:
            groups.append(set(range(start, start + a)))
            start += a
        for I in itertools.combinations(range(l), t):
            y = [[rng.randint(-3, 3) for _ in range(dmn)] for _ in range(l)]
            s = symmetrise(det_tensor(list(I), y), blocks)
            two = any(len(set(I) & g) >= 2 for g in groups)
            ok = ok and ((not s) == two)
    check("the symmetrisation of det(T) placed on t = 3 of l = 4 factors "
          "vanishes exactly when two of them lie in one block", ok)


# ------------------------------------------------------------------ (G)
class NumberField:
    def __init__(self, f, conj_img):
        self.f = [Fr(c) for c in f]           # monic, low to high
        self.d = len(f) - 1
        self.basis_conj = [self.power(conj_img, k) for k in range(self.d)]

    def red(self, p):
        p = list(p) + [Fr(0)] * max(0, self.d - len(p))
        for k in range(len(p) - 1, self.d - 1, -1):
            c = p[k]
            if c:
                for i in range(self.d + 1):
                    p[k - self.d + i] -= c * self.f[i]
        return p[:self.d]

    def mul(self, a, b):
        p = [Fr(0)] * (2 * self.d)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    p[i + j] += x * y
        return self.red(p)

    def power(self, poly, k):
        r = self.red([Fr(1)])
        base = self.red([Fr(c) for c in poly])
        for _ in range(k):
            r = self.mul(r, base)
        return r

    def inv(self, a):
        cols = []
        e = [Fr(0)] * self.d
        for k in range(self.d):
            ek = [Fr(0)] * self.d
            ek[k] = Fr(1)
            cols.append(self.mul(a, ek))
        M = tr(cols)
        Mi = inv(M)
        e[0] = Fr(1)
        return [sum(Mi[i][j] * e[j] for j in range(self.d))
                for i in range(self.d)]

    def conj(self, a):
        out = [Fr(0)] * self.d
        for k, c in enumerate(a):
            if c:
                for i in range(self.d):
                    out[i] += c * self.basis_conj[k][i]
        return out


def cyclotomic(m):
    """coefficients (low to high) of the m-th cyclotomic polynomial."""
    def pmul(a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                r[i + j] += x * y
        return r

    def pdiv(a, b):
        a = a[:]
        q = [0] * (len(a) - len(b) + 1)
        for k in range(len(a) - len(b), -1, -1):
            c = a[k + len(b) - 1] // b[-1]
            q[k] = c
            for i, y in enumerate(b):
                a[k + i] -= c * y
        assert all(x == 0 for x in a)
        return q
    num = [-1] + [0] * (m - 1) + [1]
    for dd in range(1, m):
        if m % dd == 0:
            num = pdiv(num, cyclotomic(dd))
    return num


def real_roots(f):
    """number of real roots of an integer polynomial (Sturm, exact)."""
    def deriv(p):
        return [i * p[i] for i in range(1, len(p))]

    def trim(p):
        while p and p[-1] == 0:
            p = p[:-1]
        return p

    def prem(a, b):
        a = [Fr(x) for x in a]
        while len(a) >= len(b):
            c = a[-1] / b[-1]
            sh = len(a) - len(b)
            for i, y in enumerate(b):
                a[sh + i] -= c * y
            a = trim(a[:-1]) if a[-1] == 0 else trim(a)
        return a
    seq = [[Fr(x) for x in f], [Fr(x) for x in deriv(f)]]
    while True:
        r = prem(seq[-2], seq[-1])
        if not r:
            break
        seq.append([-x for x in r])

    def sign_changes(vals):
        vals = [v for v in vals if v != 0]
        return sum(1 for a, b in zip(vals, vals[1:]) if (a > 0) != (b > 0))
    at_pinf = [p[-1] for p in seq]
    at_minf = [p[-1] * (-1) ** (len(p) - 1) for p in seq]
    return sign_changes(at_minf) - sign_changes(at_pinf)


def part_G():
    def xpow(k):
        return [0] * k + [1]
    fields = [
        ("Q(sqrt -5)", [5, 0, 1], [0, -1]),
        ("Q(zeta_5)", cyclotomic(5), xpow(4)),
        ("Q(zeta_8)", cyclotomic(8), xpow(7)),
        ("Q(zeta_12)", cyclotomic(12), xpow(11)),
        ("Q(sqrt -(2+sqrt 2))", [2, 0, 4, 0, 1], [0, -1]),
        ("Q(sqrt -(3+sqrt 3))", [6, 0, 6, 0, 1], [0, -1]),
        ("Q(zeta_7)", cyclotomic(7), xpow(6)),
        ("Q(zeta_9)", cyclotomic(9), xpow(8)),
        ("Q(zeta_15)", cyclotomic(15), xpow(14)),
        ("Q(zeta_11)", cyclotomic(11), xpow(10)),
    ]
    ok, info = True, []
    for name, f, cimg in fields:
        K = NumberField(f, cimg)
        d = K.d
        one = K.red([Fr(1)])
        theta = K.red([Fr(0), Fr(1)])
        good = K.conj(K.conj(theta)) == theta and real_roots(f) == 0
        # purely imaginary elements: kernel of conj + 1
        Cm = tr([K.conj([Fr(int(i == k)) for i in range(d)])
                 for k in range(d)])
        anti = nullspace(add(Cm, eye(d)), d)
        fixed = nullspace(add(Cm, eye(d), -1), d)
        good = good and len(fixed) == d // 2 and len(anti) == d // 2
        us, ss = [], []
        rng = random.Random(d)
        ys = list(anti)
        for _ in range(2):
            cf = [rng.randint(-3, 3) for _ in anti]
            ys.append([sum(c * v[i] for c, v in zip(cf, anti))
                       for i in range(d)])
        for y in ys:
            if not any(y):
                continue
            for s in [Fr(k) for k in range(1, d + 1)]:
                sy = [s * c for c in y]
                num = [a + b for a, b in zip(one, sy)]
                den = [a - b for a, b in zip(one, sy)]
                u = K.mul(num, K.inv(den))
                good = good and K.mul(u, K.conj(u)) == one
                us.append(u)
                ss.append([(a + b) / 2 for a, b in zip(u, K.conj(u))])
        du, ds = rank_q(us), rank_q(ss)
        good = good and du == d and ds == d // 2
        ok = ok and good
        info.append("%s %d/%d" % (name, du, ds))
    check("the elements of norm one span E and the (u + ubar)/2 span E_0 "
          "(ten CM fields of degree 2 to 10, totally imaginary by Sturm)", ok,
          "; ".join(info[:5]))
    print("         " + "; ".join(info[5:]))


# ------------------------------------------------------------------ (H)
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def pdiv_exact(a, b):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    q = [Fr(0)] * (len(a) - len(b) + 1)
    a = [Fr(x) for x in a]
    for k in range(len(a) - len(b), -1, -1):
        c = a[k + len(b) - 1] / b[-1]
        q[k] = c
        for i, y in enumerate(b):
            a[k + i] -= c * y
    assert all(x == 0 for x in a)
    return q


def cycle_type(perm):
    n = len(perm)
    seen = [False] * n
    ct = []
    for i in range(n):
        if not seen[i]:
            L, j = 0, i
            while not seen[j]:
                seen[j] = True
                j = perm[j]
                L += 1
            ct.append(L)
    return ct


def invariant_series(nu):
    """graded dims of H^*(B_nu)^{C(nu)}, H^1(B_nu) = H^1(A) (x) W^vee."""
    l = len(nu)
    blocks = {}
    for i, p in enumerate(nu):
        blocks.setdefault(p, []).append(i)
    bl = list(blocks.values())
    total, count = [0], 0
    for perms in itertools.product(*[list(itertools.permutations(b))
                                     for b in bl]):
        perm = list(range(l))
        for b, pb in zip(bl, perms):
            for src, dst in zip(b, pb):
                perm[src] = dst
        detQ = [1]
        for c in cycle_type(perm):
            fac = [0] * (c + 1)
            fac[0] = 1
            fac[c] = -((-1) ** c)            # 1 - (-z)^c
            detQ = pmul(detQ, fac)
        detW = pdiv_exact(detQ, [1, 1])      # remove the trivial line
        p4 = [Fr(1)]
        for _ in range(4):
            p4 = pmul(p4, detW)
        total = padd(total, p4)
        count += 1
    return [Fr(x) / count for x in total]


def hilb_abelian(m):
    b = [1, 4, 6, 4, 1]
    ser = [dict() for _ in range(m + 1)]
    ser[0][0] = 1
    for k in range(1, m + 1):
        for i in range(5):
            a = 2 * k - 2 + i
            new = [dict() for _ in range(m + 1)]
            for td in range(m + 1):
                for zd, c in ser[td].items():
                    j = 0
                    while td + j * k <= m:
                        cc = comb(b[i] + j - 1, j) if i % 2 == 0 \
                            else comb(b[i], j)
                        if cc:
                            key = zd + j * a
                            new[td + j * k][key] = \
                                new[td + j * k].get(key, 0) + c * cc
                        j += 1
            ser = new
    top = max(ser[m])
    return [ser[m].get(k, 0) for k in range(top + 1)]


def part_H():
    known = {3: [1, 0, 7, 8, 108, 8, 7, 0, 1],
             4: [1, 0, 7, 8, 51, 56, 458, 56, 51, 8, 7, 0, 1]}
    noninv_want = {2: {2: 15}, 3: {4: 80}, 4: {4: 15, 6: 345, 8: 15},
                   5: {8: 624}}
    ok_e, ok_known, ok_inv, ok_non, ok_prime = True, True, True, True, True
    eulers = []
    for m in range(2, 7):
        dimK = 2 * (m - 1)
        inv_p = [Fr(0)] * (2 * dimK + 1)
        non_p = [Fr(0)] * (2 * dimK + 1)
        trans = False
        for nu in partitions(m):
            l, d = len(nu), reduce(gcd, nu)
            I = invariant_series(nu)
            sh = 2 * (m - l)
            for k, c in enumerate(I):
                inv_p[sh + k] += c
                non_p[sh + k] += (d ** 4 - 1) * c
            if d > 1 and l >= 2:
                trans = True
        tot = [a + b for a, b in zip(inv_p, non_p)]
        eu = sum((-1) ** k * c for k, c in enumerate(tot))
        sigma = sum(x for x in range(1, m + 1) if m % x == 0)
        eulers.append(int(eu))
        ok_e = ok_e and eu == m ** 3 * sigma
        if m in known:
            ok_known = ok_known and tot == known[m]
        hil = hilb_abelian(m)
        q = pdiv_exact(hil, [1, 4, 6, 4, 1])
        q = q + [Fr(0)] * (len(inv_p) - len(q))
        ok_inv = ok_inv and q == inv_p
        if m in noninv_want:
            got = {k: int(c) for k, c in enumerate(non_p) if c}
            ok_non = ok_non and got == noninv_want[m]
        isprime = all(m % p for p in range(2, m))
        ok_prime = ok_prime and (trans != isprime)
    check("generalised Kummer K_{m-1}(A), m = 2..6: Euler numbers "
          "m^3 sigma(m) = 24, 108, 448, 750, 2592, and the known Betti "
          "numbers for m = 3, 4", ok_e and ok_known and
          eulers == [24, 108, 448, 750, 2592])
    check("the A[m]-invariant part is P(A^[m])/(1+z)^4 (Goettsche), and the "
          "rest is 15; 80; 15, 345, 15 in degrees 4, 6, 8; 624 for "
          "m = 2, 3, 4, 5", ok_inv and ok_non)
    check("the non-invariant part is carried only by sectors that are finite "
          "sets of points exactly when m is prime (m = 2..6)", ok_prime)


# ------------------------------------------------------------------ (I)
def part_I():
    def auto_matrix(K, img):
        """matrix of the automorphism theta -> img on the power basis."""
        cols = [K.power(img, k) for k in range(K.d)]
        return tr(cols)

    def mq_span(K, gens):
        """span of the eigenspaces of the Galois group (given by
        generators) for its characters with values +-1."""
        mats = [auto_matrix(K, g) for g in gens]
        vecs = []
        for signs in itertools.product((1, -1), repeat=len(mats)):
            rows = []
            for M, s in zip(mats, signs):
                rows.extend(add(M, scal(s, eye(K.d)), -1))
            vecs.extend(nullspace(rows, K.d))
        return rank_q(vecs) if vecs else 0
    cases = [
        ("Q(zeta_7)^+", [-1, -2, 1, 1], [[-2, 0, 1]], 1),
        ("Q(zeta_9)^+", [1, -3, 0, 1], [[-2, 0, 1]], 1),
        ("Q(zeta_11)^+", [1, 3, -3, -4, 1, 1], [[-2, 0, 1]], 1),
        ("Q(sqrt(2+sqrt 2))", [2, 0, -4, 0, 1], [[0, -3, 0, 1]], 2),
        ("Q(zeta_15)^+", [1, 4, -4, -1, 1], [[-2, 0, 1]], 2),
        ("Q(sqrt 2, sqrt 3)", [1, 0, -10, 0, 1],
         [[0, 10, 0, -1], [0, -10, 0, 1]], 4),
    ]
    ok, info = True, []
    for name, f, gens, want in cases:
        K = NumberField(f, [0, 1])
        good = real_roots(f) == K.d          # totally real
        th = K.red([Fr(0), Fr(1)])
        for g in gens:                       # each generator is a field map
            img = K.red([Fr(c) for c in g])
            val = [Fr(0)] * K.d
            pw = K.red([Fr(1)])
            for c in K.f:
                val = [a + c * b for a, b in zip(val, pw)]
                pw = K.mul(pw, img)
            good = good and all(v == 0 for v in val) and img != th
        dmq = mq_span(K, gens)
        good = good and dmq == want
        ok = ok and good
        info.append("%s: %d" % (name, dmq))
    check("the span of the elements with rational square: Q for the cyclic "
          "fields of degree 3 and 5, Q(sqrt 2) in Q(sqrt(2+sqrt 2)), Q(sqrt 5) "
          "in Q(zeta_15)^+, all of Q(sqrt 2, sqrt 3)", ok, "; ".join(info))


if __name__ == "__main__":
    print("(LXI) Hodge classes on powers and Hilbert schemes of K3 surfaces "
          "and on varieties of K3^[n] type")
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    part_H()
    part_I()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
