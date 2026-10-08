#!/usr/bin/env python3
"""
mumford_motivic.py

Item (LX) of the computations: the four possible motivic groups of a Mumford
fourfold, the formal obstruction to the exceptional classes, and the lattices
behind the Kuga-Satake base points (prop:mumfordmotivic, prop:mumfordformal,
rem:mumfordks, rem:mumfordpowersopen).

Split model over Q:  V = V_1 (x) V_2 (x) V_3 with V_k = Q^2, basis index
a = 4 b_1 + 2 b_2 + b_3, psi = eps (x) eps (x) eps, G = SL(2)^3 acting
factorwise, g = sl(2)^3 its Lie algebra.  The permutations of the three
factors act by the matrices P_sigma, and zeta is the cyclic permutation
v_1 (x) v_2 (x) v_3 -> v_3 (x) v_1 (x) v_2.

What is checked:

  (A) sp(V, psi) = g + P, where P is spanned by the 27 products
      x_1 (x) x_2 (x) x_3, x_k in sl(V_k); P is stable under g and is an
      irreducible g-module (its commutant is Q), and by weights
      S^2 V = L(2,2,2) + L(2,0,0) + L(0,2,0) + L(0,0,2), of dimensions
      27 + 3 + 3 + 3.  So a g-submodule of sp(V, psi) containing g is g or
      sp(V, psi);

  (B) the six P_sigma lie in Sp(V, psi), normalise g and carry the k-th
      factor of g to the sigma(k)-th; the commutant of g in End V is Q, and
      -1 is the image of (-1, 1, 1); the subgroups of S_3 stable under
      conjugation by A_3 (or by S_3) are exactly 1, A_3 and S_3;

  (C) on V (x) V the projectors pi_0, pi_12, pi_13, pi_23 onto the summands
      Q theta, U_12, U_13, U_23 of wedge^2 V have ranks 1, 9, 9, 9, and zeta
      carries pi_12 -> pi_23 -> pi_13 -> pi_12 and fixes pi_0; so
      zeta(omega_a) = omega_a if and only if a_1 = a_2 = a_3;

  (D) r_1 = s_1 + s_2 + s_3 commutes with g and with the six P_sigma, and
      acts on S^2 V by 3 on S^2V_1 S^2V_2 S^2V_3 and by -1 on the three
      summands S^2V_i wedge^2V_j wedge^2V_k, so it is not Sp(V, psi)-
      equivariant; Cayley's hyperdeterminant is sl(2)^3-invariant, fixed by
      the six P_sigma and not sp(V, psi)-invariant; dim (S^4 V)^G = 1 and
      dim (S^4 V)^Sp = 0 (Weyl's alternating sum);

  (E) dim (V^{(x)2m})^H for H = G, G.A_3, N, Sp(V, psi) and m = 1, 2, 3 is
      1, 1, 1, 1;  8, 4, 4, 3;  125, 45, 35, 15: the G-invariants are the
      products over the three factors of the non-crossing pairings (a basis,
      explicit Gram), zeta and a transposition permute this basis, so the
      A_3- and S_3-invariants are counted by orbits (Burnside); the
      Sp-invariants are the (2m-1)!! pairings of psi, of rank 1, 3, 15; the
      G- and Sp-dimensions are confirmed by Weyl's alternating sum;

  (F) (V (x) V)^g = Q psi, so (S^2 V)^G = 0 and (wedge^2 V)^G = Q psi; the
      divisor classes of X x X are sp(V)-invariant; the Weil classes of
      X x X for Q(i) acting through M_2(Q), and the mixed Weil classes of
      X x X x B for Q(i) acting diagonally, are sl(V)-invariant on the
      V-part; the orientation class of X x X is sl(V)-invariant;

  (G) lattices: for F = Q(2 cos(2 pi/7)) and D = (-1, c)_F (a Mumford datum:
      definite at exactly two real places, Cor D split) the space
      (T, q_1) = (D^0, Tr trd) has signature (2, 7) and Witt index 2, with an
      explicit decomposition H + H + K, K negative definite of rank 5, and
      W = H + H + <k> of signature (2, 3); U + <2a> + <-2b> and U^2 + <-2m>
      embed primitively in U^3; for an abelian surface with NS = <h>,
      h^2 = 2d, T(B) contains U + U(-1) + <-2d>; <6, -2, -2> is anisotropic
      over Q_3 (Hilbert symbol and a descent mod 9), so U + <6> + <-2> + <-2>
      has Witt index 1, and it embeds primitively in the K3 lattice with
      signature (2, 3).

Everything is exact: integer and rational arithmetic, ranks and nullspaces
by python-flint.  The scripts of the attack that these checks condense, with
their transcripts, are in attack/gaps/mumford/.

Run:  python3 mumford_motivic.py
"""
import itertools
from math import comb, gcd
from fractions import Fraction as Fr

import numpy as np
from flint import fmpz_mat

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        print("         " + detail)


def rank(rows):
    rows = [[int(x) for x in r] for r in rows]
    if not rows:
        return 0
    return fmpz_mat(rows).rank()


def nullity(rows, ncols):
    if not rows:
        return ncols
    return ncols - rank(rows)


# ------------------------------------------------------------------ model
I2 = np.eye(2, dtype=np.int64)
EE = np.array([[0, 1], [0, 0]], dtype=np.int64)
FF = np.array([[0, 0], [1, 0]], dtype=np.int64)
HH = np.array([[1, 0], [0, -1]], dtype=np.int64)
EPS = np.array([[0, 1], [-1, 0]], dtype=np.int64)
SL2 = [EE, FF, HH]
I8 = np.eye(8, dtype=np.int64)


def k3(a, b, c):
    return np.kron(np.kron(a, b), c)


PSI = k3(EPS, EPS, EPS)
PSI_INV = -PSI                      # psi^2 = eps^2 (x) eps^2 (x) eps^2 = -1
G_BASIS = []                        # k-th factor: G_BASIS[3k : 3k + 3]
for k in range(3):
    for X in SL2:
        f = [I2, I2, I2]
        f[k] = X
        G_BASIS.append(k3(*f))
P27 = [k3(X, Y, Z) for X in SL2 for Y in SL2 for Z in SL2]


def in_sp(X):
    return ((X.T @ PSI + PSI @ X) == 0).all()


SP_BASIS = []                       # X = psi^{-1} S, S symmetric
for i in range(8):
    for j in range(i, 8):
        S = np.zeros((8, 8), dtype=np.int64)
        S[i, j] = 1
        S[j, i] = 1
        SP_BASIS.append(PSI_INV @ S)


def br(X, Y):
    return X @ Y - Y @ X


def perm_matrix(sigma):
    """P e_{a_1 a_2 a_3} = e_b with b_{sigma(k)} = a_k (factor k -> sigma(k))"""
    P = np.zeros((8, 8), dtype=np.int64)
    for a in itertools.product((0, 1), repeat=3):
        b = [0, 0, 0]
        for k in range(3):
            b[sigma[k]] = a[k]
        P[4 * b[0] + 2 * b[1] + b[2], 4 * a[0] + 2 * a[1] + a[2]] = 1
    return P


S3 = list(itertools.permutations(range(3)))
PM = {s: perm_matrix(s) for s in S3}
CYC = (1, 2, 0)                     # zeta: v1 v2 v3 -> v3 v1 v2
ZETA = PM[CYC]


# ------------------------------------------------------------------ (A)
def coords27(M):
    """coordinates of M in the basis P27 (read off: E at (0,1), F at (1,0),
    H at (0,0) in each factor)"""
    pos = {0: (0, 1), 1: (1, 0), 2: (0, 0)}
    out = []
    for x, y, z in itertools.product(range(3), repeat=3):
        r = 4 * pos[x][0] + 2 * pos[y][0] + pos[z][0]
        c = 4 * pos[x][1] + 2 * pos[y][1] + pos[z][1]
        out.append(int(M[r, c]))
    return out


def conv(m1, m2):
    out = {}
    for a, x in m1.items():
        for b, y in m2.items():
            c = tuple(p + q for p, q in zip(a, b))
            out[c] = out.get(c, 0) + x * y
    return out


W_V = {s: 1 for s in itertools.product((1, -1), repeat=3)}   # weights of V


def sym_power_weights(wmult, n):
    """weights of S^n of a representation with 1-dimensional weight spaces
    given as a list of weights"""
    ws = list(wmult)
    out = {}
    for combo in itertools.combinations_with_replacement(range(len(ws)), n):
        c = tuple(sum(ws[i][t] for i in combo) for t in range(len(ws[0])))
        out[c] = out.get(c, 0) + 1
    return out


def peel_sl2cube(wmult):
    w = {c: v for c, v in wmult.items() if v}
    res = {}
    while w:
        hw = max((c for c, v in w.items() if v > 0), key=lambda c: (sum(c), c))
        m = w[hw]
        res[hw] = res.get(hw, 0) + m
        for c in itertools.product(*[range(-n, n + 1, 2) for n in hw]):
            w[c] = w.get(c, 0) - m
        w = {c: v for c, v in w.items() if v}
        assert all(v > 0 for v in w.values())
    return res


def part_A():
    ok_psi = (PSI.T == -PSI).all() and (PSI @ PSI_INV == I8).all()
    check("psi = eps (x) eps (x) eps is alternating and invertible", ok_psi)
    ok = all(in_sp(X) for X in G_BASIS) and all(in_sp(X) for X in P27)
    ok = ok and all(in_sp(X) for X in SP_BASIS)
    r_sp = rank([X.flatten() for X in SP_BASIS])
    r_all = rank([X.flatten() for X in G_BASIS + P27])
    check("g and the 27 products x_1 (x) x_2 (x) x_3 lie in sp(V, psi), and "
          "together span it: dim g + dim P = 9 + 27 = 36 = dim sp(V, psi)",
          ok and r_sp == 36 and r_all == 36 and rank(
              [X.flatten() for X in G_BASIS]) == 9)
    stable = all(rank([Y.flatten() for Y in P27] + [br(x, y).flatten()]) == 27
                 for x in G_BASIS for y in P27)
    check("P is stable under ad(g)", stable)
    # commutant of ad(g) on P: C A_x = A_x C for the 9 matrices A_x
    A = []
    for x in G_BASIS:
        cols = [coords27(br(x, y)) for y in P27]
        A.append(np.array(cols, dtype=np.int64).T)      # A[:, j] = [x, y_j]
    I27 = np.eye(27, dtype=np.int64)
    rows = []
    for Ax in A:
        M = np.kron(I27, Ax.T) - np.kron(Ax, I27)       # vec(C A - A C)
        rows.extend(M.tolist())
    n1 = nullity(rows, 729)
    check("P is an absolutely irreducible g-module: the commutant of ad(g) "
          "on P has dimension 1", n1 == 1, "nullity %d of a %dx729 system"
          % (n1, len(rows)))
    dec = peel_sl2cube(sym_power_weights(W_V, 2))
    check("by weights, S^2 V = sp(V, psi) is L(2,2,2) + L(2,0,0) + L(0,2,0) "
          "+ L(0,0,2), of dimensions 27 + 3 + 3 + 3, multiplicity free",
          dec == {(2, 2, 2): 1, (2, 0, 0): 1, (0, 2, 0): 1, (0, 0, 2): 1},
          str(dec))
    check("hence a g-submodule of sp(V, psi) containing g is g or sp(V, psi)"
          " (P irreducible, not isomorphic to a submodule of g)",
          n1 == 1 and r_all == 36 and stable)


# ------------------------------------------------------------------ (B)
def compose(s, t):
    return tuple(s[t[k]] for k in range(3))


def inverse(s):
    inv = [0] * 3
    for k in range(3):
        inv[s[k]] = k
    return tuple(inv)


def part_B():
    ok = all((PM[s].T @ PSI @ PM[s] == PSI).all() for s in S3)
    check("the six factor permutations P_sigma lie in Sp(V, psi)", ok)
    gflat = [X.flatten() for X in G_BASIS]
    ok = all(rank(gflat + [(PM[s] @ X @ PM[s].T).flatten()
                           for X in G_BASIS]) == 9 for s in S3)
    check("each P_sigma normalises g", ok)
    ok = True
    for s in S3:
        for k in range(3):
            blk = [G_BASIS[3 * s[k] + t].flatten() for t in range(3)]
            img = [(PM[s] @ G_BASIS[3 * k + t] @ PM[s].T).flatten()
                   for t in range(3)]
            ok = ok and rank(blk + img) == 3
    check("P_sigma carries the k-th factor sl(V_k) of g to the sigma(k)-th",
          ok)
    rows = []
    for x in G_BASIS:
        rows.extend((np.kron(I8, x.T) - np.kron(x, I8)).tolist())
    check("the commutant of g in End(V) is Q (V absolutely irreducible), so "
          "the centraliser of G in Sp(V, psi) is {1, -1}",
          nullity(rows, 64) == 1)
    check("-1 on V is the image of (-1, 1, 1), so {1, -1} lies in G",
          (k3(-I2, I2, I2) == -I8).all())
    subs = set()
    for r in range(1, 7):
        for c in itertools.combinations(S3, r):
            cs = set(c)
            if all(compose(a, b) in cs for a in cs for b in cs):
                subs.add(frozenset(cs))
    A3 = frozenset({(0, 1, 2), CYC, compose(CYC, CYC)})
    for image in (A3, frozenset(S3)):
        stable = sorted(len(H) for H in subs
                        if all(frozenset(compose(compose(g, h), inverse(g))
                                         for h in H) == H for g in image))
        check("the subgroups of S_3 stable under conjugation by %s are "
              "exactly 1, A_3, S_3" % ("A_3" if len(image) == 3 else "S_3"),
              stable == [1, 3, 6])


# ------------------------------------------------------------------ (C), (D)
def slot_swap_VV(k):
    """exchange of the two copies of V_k on V (x) V (index 8 a + b)"""
    M = np.zeros((64, 64), dtype=np.int64)
    bit = 2 - k
    for a in range(8):
        for b in range(8):
            ba, bb = (a >> bit) & 1, (b >> bit) & 1
            a2 = (a & ~(1 << bit)) | (bb << bit)
            b2 = (b & ~(1 << bit)) | (ba << bit)
            M[8 * a2 + b2, 8 * a + b] = 1
    return M


SK = [slot_swap_VV(k) for k in range(3)]
I64 = np.eye(64, dtype=np.int64)


def proj8(signs):
    """8 prod_k (1 + sign_k s_k)/2"""
    M = I64.copy()
    for k in range(3):
        M = M @ (I64 + signs[k] * SK[k])
    return M


def part_C():
    full = SK[0] @ SK[1] @ SK[2]
    pi = {"0": proj8((-1, -1, -1)), "12": proj8((1, 1, -1)),
          "13": proj8((1, -1, 1)), "23": proj8((-1, 1, 1))}
    ok = all((M @ full == -M).all() for M in pi.values())
    ranks = {key: rank(M.tolist()) for key, M in pi.items()}
    check("pi_0, pi_12, pi_13, pi_23 are supported on wedge^2 V, of ranks "
          "1, 9, 9, 9", ok and ranks == {"0": 1, "12": 9, "13": 9, "23": 9},
          str(ranks))
    Z2 = np.kron(ZETA, ZETA)
    Z2i = Z2.T
    img = {key: next((t for t, N in pi.items()
                      if (Z2 @ M @ Z2i == N).all()), None)
           for key, M in pi.items()}
    check("zeta carries pi_12 -> pi_23, pi_23 -> pi_13, pi_13 -> pi_12 and "
          "fixes pi_0", img == {"0": "0", "12": "23", "23": "13",
                                "13": "12"}, str(img))
    # zeta(omega_a) = omega_a iff a_1 = a_2 = a_3
    a = (Fr(0), Fr(1), Fr(2), Fr(5))   # a_0, a_1, a_2, a_3 distinct
    coeff = {"0": a[0], "12": a[1], "13": a[2], "23": a[3]}
    new = {img[key]: v for key, v in coeff.items()}
    check("so zeta fixes omega_a only when a_1 = a_2 = a_3; no exceptional "
          "class (distinct conjugates) is zeta-fixed",
          new != coeff and all(
              {img[kk]: v for kk, v in {"0": 1, "12": t, "13": t,
                                         "23": t}.items()}
              == {"0": 1, "12": t, "13": t, "23": t} for t in (0, 3)))


def diag_action(x, n=2):
    """x acting on V^{(x)n} as a derivation (n = 2 only)"""
    return np.kron(x, I8) + np.kron(I8, x)


# polynomials as dicts {exponent tuple: coefficient}
def pmul(p, q):
    out = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c}


def padd(*ps):
    out = {}
    for p in ps:
        for e, c in p.items():
            out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}


def pscale(p, s):
    return {e: s * c for e, c in p.items()}


def var(i):
    e = [0] * 8
    e[i] = 1
    return {tuple(e): 1}


def hyperdet():
    def A(i, j, k):
        return var(4 * i + 2 * j + k)

    def m(*fs):
        out = {tuple([0] * 8): 1}
        for f in fs:
            out = pmul(out, f)
        return out
    sq = padd(m(A(0, 0, 0), A(0, 0, 0), A(1, 1, 1), A(1, 1, 1)),
              m(A(0, 0, 1), A(0, 0, 1), A(1, 1, 0), A(1, 1, 0)),
              m(A(0, 1, 0), A(0, 1, 0), A(1, 0, 1), A(1, 0, 1)),
              m(A(1, 0, 0), A(1, 0, 0), A(0, 1, 1), A(0, 1, 1)))
    two = padd(m(A(0, 0, 0), A(0, 0, 1), A(1, 1, 0), A(1, 1, 1)),
               m(A(0, 0, 0), A(0, 1, 0), A(1, 0, 1), A(1, 1, 1)),
               m(A(0, 0, 0), A(1, 0, 0), A(0, 1, 1), A(1, 1, 1)),
               m(A(0, 0, 1), A(0, 1, 0), A(1, 0, 1), A(1, 1, 0)),
               m(A(0, 0, 1), A(1, 0, 0), A(0, 1, 1), A(1, 1, 0)),
               m(A(0, 1, 0), A(1, 0, 0), A(0, 1, 1), A(1, 0, 1)))
    four = padd(m(A(0, 0, 0), A(0, 1, 1), A(1, 0, 1), A(1, 1, 0)),
                m(A(0, 0, 1), A(0, 1, 0), A(1, 0, 0), A(1, 1, 1)))
    return padd(sq, pscale(two, -2), pscale(four, 4))


def pderiv_action(X, p):
    """d/dt p(exp(tX) a) at t = 0 = sum_r dp/da_r (X a)_r"""
    out = {}
    for e, c in p.items():
        for r in range(8):
            if e[r] == 0:
                continue
            base = list(e)
            base[r] -= 1
            for s in range(8):
                x = int(X[r, s])
                if x == 0:
                    continue
                e2 = list(base)
                e2[s] += 1
                e2 = tuple(e2)
                out[e2] = out.get(e2, 0) + c * e[r] * x
    return {e: c for e, c in out.items() if c}


def psubst(P, p):
    """p(P a) for a permutation matrix P"""
    out = {}
    for e, cf in p.items():
        e2 = [0] * 8
        for r in range(8):                 # (P a)_r = a_c with P[r, c] = 1
            c = int(np.nonzero(P[r, :])[0][0])
            e2[c] += e[r]
        e2 = tuple(e2)
        out[e2] = out.get(e2, 0) + cf
    return {e: c for e, c in out.items() if c}


def weyl_A1cube():
    out = []
    for signs in itertools.product((1, -1), repeat=3):
        out.append((lambda v, s=signs: tuple(x * y for x, y in zip(v, s)),
                    signs[0] * signs[1] * signs[2]))
    return out


def perm_sign(p):
    s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s = -s
    return s


def weyl_C4():
    out = []
    for p in itertools.permutations(range(4)):
        for signs in itertools.product((1, -1), repeat=4):
            def act(v, p=p, signs=signs):
                o = [0] * 4
                for i in range(4):
                    o[p[i]] = signs[i] * v[i]
                return tuple(o)
            out.append((act, perm_sign(p) * signs[0] * signs[1] * signs[2]
                        * signs[3]))
    return out


W_V_C4 = {}
for _i in range(4):
    for _sg in (1, -1):
        _e = [0] * 4
        _e[_i] = _sg
        W_V_C4[tuple(_e)] = 1


def trivial_mult(wmult, rho, weyl):
    tot = 0
    for act, sgn in weyl:
        mu = tuple(a - r for a, r in zip(act(rho), rho))
        tot += sgn * wmult.get(mu, 0)
    return tot


def part_D():
    r1 = SK[0] + SK[1] + SK[2]
    ok_g = all((diag_action(x) @ r1 == r1 @ diag_action(x)).all()
               for x in G_BASIS)
    ok_p = all((np.kron(PM[s], PM[s]) @ r1 == r1 @ np.kron(PM[s], PM[s])).all()
               for s in S3)
    check("r_1 = s_1 + s_2 + s_3 on V (x) V commutes with g and with the six "
          "P_sigma (so it is N-invariant)", ok_g and ok_p)
    e123 = proj8((1, 1, 1))
    es = [proj8(tuple(1 if t == i else -1 for t in range(3)))
          for i in range(3)]
    full = SK[0] @ SK[1] @ SK[2]
    ok = (r1 @ e123 == 3 * e123).all() and rank(e123.tolist()) == 27
    ok = ok and all((r1 @ e == -e).all() and rank(e.tolist()) == 3
                    for e in es)
    ok = ok and (e123 + es[0] + es[1] + es[2] == 4 * (I64 + full)).all()
    check("S^2 V = S^2V_1 S^2V_2 S^2V_3 + three summands S^2V_i wedge^2V_j "
          "wedge^2V_k (ranks 27, 3, 3, 3), on which r_1 acts by 3 and by -1;"
          " as S^2 V is Sp-irreducible, r_1 is not Sp(V, psi)-equivariant",
          ok)
    ok_sp = not all((diag_action(x) @ r1 == r1 @ diag_action(x)).all()
                    for x in SP_BASIS)
    check("r_1 does not commute with sp(V, psi) (direct check)", ok_sp)
    Det = hyperdet()
    check("Cayley's hyperdeterminant is killed by sl(2)^3",
          all(not pderiv_action(X, Det) for X in G_BASIS),
          "%d monomials" % len(Det))
    check("it is fixed by the six factor permutations",
          all(psubst(PM[s], Det) == Det for s in S3))
    check("it is not sp(V, psi)-invariant",
          any(pderiv_action(X, Det) for X in SP_BASIS))
    dG = trivial_mult(sym_power_weights(W_V, 4), (1, 1, 1), weyl_A1cube())
    dSp = trivial_mult(sym_power_weights(W_V_C4, 4), (4, 3, 2, 1), weyl_C4())
    check("dim (S^4 V)^G = 1 and dim (S^4 V)^Sp = 0 (Weyl's alternating "
          "sum), so the line of Det is N-stable and not Sp-fixed",
          dG == 1 and dSp == 0, "dims %d, %d" % (dG, dSp))


# ------------------------------------------------------------------ (E)
def matchings(points):
    if not points:
        yield []
        return
    a = points[0]
    for i in range(1, len(points)):
        b = points[i]
        rest = points[1:i] + points[i + 1:]
        for m in matchings(rest):
            yield [(a, b)] + m


def noncrossing(m):
    for (a, b), (c, d) in itertools.combinations(m, 2):
        if a < c < b < d or c < a < d < b:
            return False
    return True


def eps_tensor(match, n):
    """the SL(2)-invariant tensor prod_{(i,j)} eps(x_i, x_j) in (Q^2)^{(x)n}
    as a dict {bits: coefficient}"""
    out = {}
    for bits in itertools.product((0, 1), repeat=n):
        v = 1
        for i, j in match:
            v *= int(EPS[bits[i], bits[j]])
            if v == 0:
                break
        if v:
            out[bits] = v
    return out


def sl2_kills(t, n):
    for X in SL2:
        acc = {}
        for bits, c in t.items():
            for pos in range(n):
                for r in (0, 1):
                    x = int(X[r, bits[pos]])
                    if x:
                        nb = bits[:pos] + (r,) + bits[pos + 1:]
                        acc[nb] = acc.get(nb, 0) + c * x
        if any(acc.values()):
            return False
    return True


def dot(t, u):
    if len(t) > len(u):
        t, u = u, t
    return sum(c * u.get(k, 0) for k, c in t.items())


def product_tensor(ts):
    """(x)_k t_k on V^{(x)n}: index tuple of n values in range(8)"""
    out = {}
    for (b1, c1), (b2, c2), (b3, c3) in itertools.product(
            ts[0].items(), ts[1].items(), ts[2].items()):
        idx = tuple(4 * x + 2 * y + z for x, y, z in zip(b1, b2, b3))
        out[idx] = c1 * c2 * c3
    return out


def apply_factor_perm(sigma, t):
    """P_sigma on every copy of V"""
    P = PM[sigma]
    img = {a: int(np.nonzero(P[:, a])[0][0]) for a in range(8)}
    return {tuple(img[a] for a in idx): c for idx, c in t.items()}


def weights_tensor_power(wmult, k):
    out = {tuple(0 for _ in next(iter(wmult))): 1}
    for _ in range(k):
        out = conv(out, wmult)
    return out


def part_E():
    results = {}
    for m in (1, 2, 3):
        n = 2 * m
        allm = list(matchings(list(range(n))))
        ncm = [mm for mm in allm if noncrossing(mm)]
        c = comb(n, m) - comb(n, m + 1)
        base = [eps_tensor(mm, n) for mm in ncm]
        ok_inv = all(sl2_kills(t, n) for t in base)
        gram = [[dot(s, t) for t in base] for s in base]
        ok_basis = len(base) == c and rank(gram) == c and ok_inv
        # the G-invariants of V^{(x)n}: products over the three factors
        idx = list(itertools.product(range(c), repeat=3))
        prods = None
        if m <= 2:
            prods = {i: product_tensor([base[i[0]], base[i[1]], base[i[2]]])
                     for i in idx}
            gram3 = [[dot(prods[i], prods[j]) for j in idx] for i in idx]
            ok_basis = ok_basis and rank(gram3) == c ** 3
        else:
            sample = [idx[0], idx[7], idx[31], idx[62], idx[124]]
            prods = {i: product_tensor([base[i[0]], base[i[1]], base[i[2]]])
                     for i in sample}
        # zeta and the transposition (0 1) permute the product basis
        tr = (1, 0, 2)
        ok_perm = True
        for i, t in prods.items():
            zi = (i[2], i[0], i[1])            # factor k -> CYC[k]
            ti = (i[1], i[0], i[2])
            zt = product_tensor([base[zi[0]], base[zi[1]], base[zi[2]]])
            tt = product_tensor([base[ti[0]], base[ti[1]], base[ti[2]]])
            ok_perm = ok_perm and apply_factor_perm(CYC, t) == zt \
                and apply_factor_perm(tr, t) == tt
        orbitsA3 = len({min((i, (i[2], i[0], i[1]), (i[1], i[2], i[0])))
                         for i in idx})
        orbitsS3 = len({tuple(sorted(i)) for i in idx})
        # Sp-invariants: all pairings of psi; Gram = (factor Gram)^3 entrywise
        fac = [eps_tensor(mm, n) for mm in allm]
        gfac = [[dot(s, t) for t in fac] for s in fac]
        gsp = [[x ** 3 for x in row] for row in gfac]
        dSp = rank(gsp)
        if m <= 2:
            psis = [product_tensor([t, t, t]) for t in fac]
            ok_sp = all(dot(psis[i], psis[j]) == gsp[i][j]
                        for i in range(len(fac)) for j in range(len(fac)))
            ok_sp = ok_sp and all(apply_factor_perm(CYC, t) == t
                                  for t in psis)
        else:
            ok_sp = True
        rsG = trivial_mult(weights_tensor_power(W_V, n), (1, 1, 1),
                           weyl_A1cube())
        rsSp = trivial_mult(weights_tensor_power(W_V_C4, n), (4, 3, 2, 1),
                            weyl_C4())
        results[m] = (c ** 3, orbitsA3, orbitsS3, dSp)
        check("m = %d: the %d products of non-crossing pairings form a basis "
              "of (V^(x)%d)^G, and zeta and a transposition of the factors "
              "permute it" % (m, c ** 3, n), ok_basis and ok_perm
              and rsG == c ** 3,
              "Weyl's sum gives dim (V^(x)%d)^G = %d" % (n, rsG))
        check("m = %d: the %d pairings of psi span (V^(x)%d)^Sp, of "
              "dimension %d (Weyl's sum %d), and are fixed by zeta"
              % (m, len(fac), n, dSp, rsSp), ok_sp and dSp == rsSp)
    burn = {m: ((c ** 3 + 2 * c) // 3, (c ** 3 + 3 * c ** 2 + 2 * c) // 6)
            for m, c in ((1, 1), (2, 2), (3, 5))}
    check("dimensions of (V^(x)2m)^H for H = G, G.A_3, N, Sp: m = 1: "
          "1, 1, 1, 1; m = 2: 8, 4, 4, 3; m = 3: 125, 45, 35, 15",
          results == {1: (1, 1, 1, 1), 2: (8, 4, 4, 3),
                      3: (125, 45, 35, 15)}, str(results))
    check("Burnside: (c^3 + 2c)/3 = 4, 45 and (c^3 + 3c^2 + 2c)/6 = 4, 35 "
          "for c = 2, 5", burn[2] == (4, 4) and burn[3] == (45, 35))


# ------------------------------------------------------------------ (F)
def sort_sign(idx):
    if len(set(idx)) < len(idx):
        return None, 0
    arr = list(idx)
    sign = 1
    for i in range(len(arr)):
        for j in range(len(arr) - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                sign = -sign
    return tuple(arr), sign


def ext_act(X, A, nV, ncopies):
    """derivation action of X in gl(V) on the V-part of an exterior algebra
    with basis e_a (x) f_j (index a + nV j, j < ncopies); larger indices are
    untouched"""
    out = {}
    for mono, c in A.items():
        for s, idx in enumerate(mono):
            if idx >= nV * ncopies:
                continue
            a, j = idx % nV, idx // nV
            for d in range(nV):
                x = int(X[d, a])
                if x == 0:
                    continue
                new = list(mono)
                new[s] = d + nV * j
                mm, sg = sort_sign(new)
                if sg:
                    out[mm] = out.get(mm, 0) + sg * c * x
    return {m: c for m, c in out.items() if c}


def psi_class(j, k):
    out = {}
    for a in range(8):
        for b in range(8):
            w = int(PSI_INV[a, b])
            if w:
                mm, s = sort_sign((a + 8 * j, b + 8 * k))
                if s:
                    out[mm] = out.get(mm, 0) + s * w
    return {m: c for m, c in out.items() if c}


def weil_class(nV, nextra, off):
    """Re and Im of /\\_a (e_a (x) u) /\\ /\\_h (h (x) u), u = f_0 - i f_1"""
    Re, Im = {}, {}
    for S in itertools.product((0, 1), repeat=nV + nextra):
        k = sum(S)
        idx = [a + nV * S[a] for a in range(nV)] + \
              [off + h + nextra * S[nV + h] for h in range(nextra)]
        mm, s = sort_sign(tuple(idx))
        if k % 4 == 0:
            Re[mm] = Re.get(mm, 0) + s
        elif k % 4 == 2:
            Re[mm] = Re.get(mm, 0) - s
        elif k % 4 == 1:
            Im[mm] = Im.get(mm, 0) - s
        else:
            Im[mm] = Im.get(mm, 0) + s
    return ({m: c for m, c in Re.items() if c},
            {m: c for m, c in Im.items() if c})


def part_F():
    rows = []
    for x in G_BASIS:
        rows.extend(diag_action(x).tolist())
    null = fmpz_mat([[int(v) for v in r] for r in rows]).nullspace()[0]
    vecs = [[int(null[i, j]) for i in range(64)]
            for j in range(null.ncols())
            if any(null[i, j] for i in range(64))]
    psiv = [int(PSI[a, b]) for a in range(8) for b in range(8)]
    ok = len(vecs) == 1 and rank(vecs + [psiv]) == 1
    check("(V (x) V)^g = Q psi: so (S^2 V)^G = 0 and (wedge^2 V)^G = Q psi, "
          "and the divisor classes of a power of X are Sp-invariant", ok)
    sl_basis = []
    for i in range(8):
        for j in range(8):
            if i != j:
                M = np.zeros((8, 8), dtype=np.int64)
                M[i, j] = 1
                sl_basis.append(M)
    for i in range(7):
        M = np.zeros((8, 8), dtype=np.int64)
        M[i, i] = 1
        M[i + 1, i + 1] = -1
        sl_basis.append(M)
    P = [psi_class(0, 0), psi_class(0, 1), psi_class(1, 1)]
    check("the divisor classes psi_00, psi_01, psi_11 of X x X are "
          "sp(V)-invariant",
          all(not ext_act(X, c, 8, 2) for X in SP_BASIS for c in P))
    Re, Im = weil_class(8, 0, 16)
    check("the Weil classes of X x X for Q(i) acting through M_2(Q) are "
          "sl(V)-invariant (63 elementary traceless matrices)",
          all(not ext_act(X, Re, 8, 2) and not ext_act(X, Im, 8, 2)
              for X in sl_basis), "supports %d, %d" % (len(Re), len(Im)))
    ReY, ImY = weil_class(8, 2, 16)
    check("the Weil classes of X x X x B, H^1(B) = Q^2 (x) Q^2, for Q(i) "
          "acting diagonally, are sl(V)-invariant on the V-part",
          all(not ext_act(X, ReY, 8, 2) and not ext_act(X, ImY, 8, 2)
              for X in sl_basis))
    top = {tuple(range(16)): 1}
    check("the orientation class of X x X is sl(V)-invariant",
          all(not ext_act(X, top, 8, 2) for X in sl_basis))


# ------------------------------------------------------------------ (G)
def inertia(Gm):
    A = [[Fr(x) for x in row] for row in Gm]
    pos = neg = zero = 0
    while A:
        m = len(A)
        piv = next((i for i in range(m) if A[i][i] != 0), None)
        if piv is None:
            hit = next(((i, j) for i in range(m) for j in range(m)
                        if A[i][j] != 0), None)
            if hit is None:
                zero += m
                break
            i, j = hit
            A[i] = [A[i][t] + A[j][t] for t in range(m)]
            for r in range(m):
                A[r][i] = A[r][i] + A[r][j]
            continue
        d = A[piv][piv]
        if d > 0:
            pos += 1
        else:
            neg += 1
        keep = [r for r in range(m) if r != piv]
        A = [[A[r][s] - A[r][piv] * A[piv][s] / d for s in keep]
             for r in keep]
    return pos, neg, zero


def gram(vecs, Gm):
    n = len(Gm)
    return [[sum(Fr(u[a]) * Gm[a][b] * v[b] for a in range(n)
                 for b in range(n)) for v in vecs] for u in vecs]


def hilbert(a, b, p):
    a, b = Fr(a), Fr(b)

    def split(x):
        num, den = x.numerator, x.denominator
        v = 0
        while num % p == 0:
            num //= p
            v += 1
        while den % p == 0:
            den //= p
            v -= 1
        return v, Fr(num, den)
    va, ua = split(a)
    vb, ub = split(b)

    def unit_mod(u, mod):
        return (u.numerator * pow(u.denominator, -1, mod)) % mod
    if p != 2:
        def leg(u):
            return 1 if pow(unit_mod(u, p), (p - 1) // 2, p) == 1 else -1
        s = (-1) ** ((va * vb * ((p - 1) // 2)) % 2)
        s *= leg(ua) ** (vb % 2)
        s *= leg(ub) ** (va % 2)
        return s
    ua8, ub8 = unit_mod(ua, 8), unit_mod(ub, 8)

    def e(u):
        return ((u - 1) // 2) % 2

    def w(u):
        return ((u * u - 1) // 8) % 2
    return -1 if (e(ua8) * e(ub8) + va * w(ub8) + vb * w(ua8)) % 2 else 1


def fmul(x, y):
    """multiplication in F = Q[c], c^3 = -c^2 + 2c + 1, basis 1, c, c^2"""
    prod = [Fr(0)] * 5
    for i in range(3):
        for j in range(3):
            prod[i + j] += Fr(x[i]) * Fr(y[j])
    c4 = prod[4]
    prod[3] -= c4
    prod[2] += 2 * c4
    prod[1] += c4
    c3 = prod[3]
    prod[2] -= c3
    prod[1] += 2 * c3
    prod[0] += c3
    return prod[:3]


def ftrace(x):
    # traces of 1, c, c^2: 3, -1, 5
    return 3 * Fr(x[0]) - Fr(x[1]) + 5 * Fr(x[2])


def part_G():
    # the field and the quaternion algebra
    def p(x):
        return x ** 3 + x ** 2 - 2 * x - 1
    vals = [p(Fr(t)) for t in (-2, -1, 0, 1, 2)]
    signs = [1 if v > 0 else -1 for v in vals]
    roots_loc = [(-2, -1), (-1, 0), (1, 2)]
    ok = signs == [-1, 1, -1, -1, 1]
    cc = [0, 1, 0]
    c2 = fmul(cc, cc)
    ok_tr = ftrace(cc) == -1 and ftrace(c2) == 5 and ftrace([1, 0, 0]) == 3
    # norm of c = product of conjugates = -p(0)... = 1 for x^3+x^2-2x-1
    normc = -p(Fr(0))
    check("c = 2cos(2pi/7): x^3 + x^2 - 2x - 1 has its roots in (-2,-1), "
          "(-1,0), (1,2), so c < 0 at exactly two real places; N(c) = 1",
          ok and ok_tr and normc == 1, "roots in %s" % roots_loc)
    check("D = (-1, c)_F is definite exactly where c < 0 (two places) and "
          "Cor D = (-1, N(c))_Q = (-1, 1)_Q is split: a Mumford datum",
          hilbert(-1, 1, 2) == 1 and hilbert(-1, 1, 3) == 1 and normc == 1)
    powers = [[1, 0, 0], cc, c2]
    eps = [[-1, 0, 0], cc, cc]                          # i^2, j^2, k^2
    Gm = [[Fr(0)] * 9 for _ in range(9)]
    for m in range(3):
        for r in range(3):
            for s in range(3):
                Gm[3 * m + r][3 * m + s] = ftrace(
                    fmul([2 * e for e in eps[m]], fmul(powers[r], powers[s])))
    sig = inertia(Gm)
    check("(T, q_1) = (D^0, Tr trd) has signature (2, 7)", sig == (2, 7, 0),
          str(sig))
    v1 = [-1, -1, 0, -1, -1, -1, -1, 0, 0]
    v2 = [-1, 0, 0, -1, -1, -1, 0, 1, 0]
    g2 = gram([v1, v2], Gm)
    ok_iso = g2 == [[0, 0], [0, 0]] and rank([v1, v2]) == 2
    # hyperbolic partners
    a1 = [sum(Gm[i][j] * v1[j] for j in range(9)) for i in range(9)]
    a2 = [sum(Gm[i][j] * v2[j] for j in range(9)) for i in range(9)]
    pair = next((i, j) for i in range(9) for j in range(9)
                if a1[i] * a2[j] - a1[j] * a2[i] != 0)
    i, j = pair
    det = a1[i] * a2[j] - a1[j] * a2[i]

    def solve(t1, t2):
        w = [Fr(0)] * 9
        w[i] = (t1 * a2[j] - t2 * a1[j]) / det
        w[j] = (a1[i] * t2 - a2[i] * t1) / det
        return w
    w1, w2 = solve(1, 0), solve(0, 1)

    def ip(x, y):
        return sum(Fr(x[a]) * Gm[a][b] * y[b] for a in range(9)
                   for b in range(9))
    w1 = [w1[t] - ip(w1, w1) / 2 * v1[t] for t in range(9)]
    w2 = [w2[t] - ip(w2, w2) / 2 * v2[t] for t in range(9)]
    w2 = [w2[t] - ip(w1, w2) * v1[t] for t in range(9)]
    H4 = [v1, w1, v2, w2]
    ok_h = gram(H4, Gm) == [[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1],
                            [0, 0, 1, 0]]
    check("T contains the totally isotropic plane <v1, v2> and H + H = "
          "<v1, w1> + <v2, w2>: Witt index exactly 2 (signature (2, 7))",
          ok_iso and ok_h)
    # orthogonal complement K of H + H
    den = 1
    for vec in H4:
        for x in vec:
            den = den * Fr(x).denominator // gcd(den, Fr(x).denominator)
    rows = [[int(sum(Fr(vec[a]) * Gm[a][b] for a in range(9)) * den)
             for b in range(9)] for vec in H4]
    ns = fmpz_mat(rows).nullspace()[0]
    K = [[int(ns[r, c]) for r in range(9)] for c in range(ns.ncols())
         if any(ns[r, c] for r in range(9))]
    sigK = inertia(gram(K, Gm))
    check("K = (H + H)^perp is negative definite of rank 5",
          len(K) == 5 and sigK == (0, 5, 0), str(sigK))
    W = H4 + [K[0]]
    sigW = inertia(gram(W, Gm))
    rowsW = [[int(sum(Fr(vec[a]) * Gm[a][b] for a in range(9)) * den)
              for b in range(9)] for vec in W]
    nsW = fmpz_mat(rowsW).nullspace()[0]
    NW = [[int(nsW[r, c]) for r in range(9)] for c in range(nsW.ncols())
          if any(nsW[r, c] for r in range(9))]
    check("W = H + H + <k> (k in K) has signature (2, 3) and Witt index 2, "
          "with negative definite complement of rank 4 in T",
          sigW == (2, 3, 0) and len(NW) == 4
          and inertia(gram(NW, Gm)) == (0, 4, 0))
    # U^3 and the rational reach of Shioda-Inose structures
    U3 = [[0] * 6 for _ in range(6)]
    for t in range(3):
        U3[2 * t][2 * t + 1] = U3[2 * t + 1][2 * t] = 1

    def e6(t):
        v = [0] * 6
        v[t] = 1
        return v
    ok = True
    for a, b in ((1, 1), (3, 2), (5, 7)):
        L = [e6(0), e6(1), [0, 0, 1, a, 0, 0], [0, 0, 0, 0, 1, -b]]
        gL = gram(L, U3)
        ok = ok and gL == [[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 2 * a, 0],
                           [0, 0, 0, -2 * b]]
        ok = ok and all(abs(int(fmpz_mat(L).snf()[t, t])) == 1
                        for t in range(4))
    for mm in (1, 2, 6):
        L = [e6(0), e6(1), e6(2), e6(3), [0, 0, 0, 0, 1, -mm]]
        ok = ok and gram(L, U3)[4][4] == -2 * mm and all(
            abs(int(fmpz_mat(L).snf()[t, t])) == 1 for t in range(5))
    check("U + <2a> + <-2b> and U^2 + <-2m> embed primitively in U^3 "
          "((a, b) = (1, 1), (3, 2), (5, 7); m = 1, 2, 6): the lattices of "
          "the rational reach of Shioda-Inose structures", ok)
    # abelian surfaces
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

    def wsign(I, J):
        idx = list(I) + list(J)
        if len(set(idx)) < 4:
            return 0
        return sort_sign(idx)[1]
    Q6 = [[wsign(pairs[r], pairs[s]) for s in range(6)] for r in range(6)]
    ok = inertia(Q6) == (3, 3, 0) and fmpz_mat(Q6).det() == -1
    for d in (1, 2, 3, 5):
        def ev(p_):
            v = [0] * 6
            v[pairs.index(p_)] = 1
            return v
        h = [x + d * y for x, y in zip(ev((0, 1)), ev((2, 3)))]
        vecs = [ev((0, 2)), ev((1, 3)), ev((0, 3)), ev((1, 2)),
                [x - d * y for x, y in zip(ev((0, 1)), ev((2, 3)))]]
        g_ = gram([h] + vecs, Q6)
        ok = ok and g_[0][0] == 2 * d and all(g_[0][t] == 0
                                              for t in range(1, 6))
        ok = ok and [row[1:] for row in g_[1:]] == [
            [0, -1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, 0, 1, 0],
            [0, 0, 1, 0, 0], [0, 0, 0, 0, -2 * d]]
    check("H^2(B, Z) = wedge^2 Z^4 is U^3, and for NS(B) = <h>, h^2 = 2d, "
          "T(B) contains U(-1) + U + <-2d>: T(B)_Q has Witt index 2 "
          "(d = 1, 2, 3, 5)", ok)
    # <6, -2, -2> over Q_3
    # <a, b, c> is isotropic over Q_p iff (-ac, -bc)_p = 1; for
    # (a, b, c) = (6, -2, -2) this is (12, -4)_3
    hs = hilbert(12, -4, 3)
    iso3 = hilbert(-Fr(6) * -2, -Fr(-2) * -2, 3) == 1
    descent = all(not ((y * y + z * z) % 3 == 0 and (y % 3 or z % 3))
                  for y in range(3) for z in range(3))
    descent = descent and all((3 * x * x) % 9 != 0 or x % 3 == 0
                              for x in range(9))
    check("<6, -2, -2> is anisotropic over Q_3: (12, -4)_3 = (3, -1)_3 = -1,"
          " and by descent (6x^2 = 2y^2 + 2z^2 forces 3 | y, z, then 3 | x)",
          hs == -1 and not iso3 and descent
          and hilbert(3, -1, 3) == -1 and hilbert(3, -1, 2) == -1)
    check("so U + <6> + <-2> + <-2> has rational Witt index 1: if it were 2, "
          "cancelling a hyperbolic plane would make <6, -2, -2> isotropic",
          not iso3)
    E8 = [[2, -1, 0, 0, 0, 0, 0, 0], [-1, 2, -1, 0, 0, 0, 0, 0],
          [0, -1, 2, -1, 0, 0, 0, -1], [0, 0, -1, 2, -1, 0, 0, 0],
          [0, 0, 0, -1, 2, -1, 0, 0], [0, 0, 0, 0, -1, 2, -1, 0],
          [0, 0, 0, 0, 0, -1, 2, 0], [0, 0, -1, 0, 0, 0, 0, 2]]
    LK3 = [[0] * 22 for _ in range(22)]
    for t in range(3):
        LK3[2 * t][2 * t + 1] = LK3[2 * t + 1][2 * t] = 1
    for blk in (6, 14):
        for r in range(8):
            for s in range(8):
                LK3[blk + r][blk + s] = -E8[r][s]
    ok = fmpz_mat(E8).det() == 1 and inertia(E8) == (8, 0, 0)
    ok = ok and fmpz_mat(LK3).det() == -1 and inertia(LK3) == (3, 19, 0)

    def u22(t):
        v = [0] * 22
        v[t] = 1
        return v
    Lv = [u22(0), u22(1), [x + 3 * y for x, y in zip(u22(2), u22(3))],
          [x - y for x, y in zip(u22(4), u22(5))], u22(6)]
    gL = gram(Lv, LK3)
    snf = fmpz_mat(Lv).snf()
    ok = ok and gL == [[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 6, 0, 0],
                       [0, 0, 0, -2, 0], [0, 0, 0, 0, -2]]
    ok = ok and all(abs(int(snf[t, t])) == 1 for t in range(5))
    check("U + <6> + <-2> + <-2> embeds primitively in U^3 + E8(-1)^2 "
          "(Smith invariants 1) with signature (2, 3): a very general K3 "
          "surface with this transcendental lattice has Picard number 17",
          ok and inertia(gL) == (2, 3, 0))


if __name__ == "__main__":
    print("(LX) the motivic group of a Mumford fourfold, the formal "
          "obstruction, and the Kuga-Satake base points")
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
