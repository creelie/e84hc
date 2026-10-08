#!/usr/bin/env python3
"""
mumford_rm.py

The two exceptional Hodge classes on the self-product of an abelian fourfold
of Mumford type are a real multiplication, and a K3 surface of Picard number
thirteen carries the same data.  Item (XLI).

Setting.  X is an abelian fourfold whose Hodge group G is a Q-form of
SL(2)^3, split by the Galois closure of a totally real cubic field F; over
Q-bar, H^1(X) = V = V_1 (x) V_2 (x) V_3 with V_i the standard representation
of the i-th factor, and the Galois group permutes the three factors as it
permutes the three embeddings of F.  The Hodge cocharacter lives in one
factor, say the third: H^{1,0} = V_1 (x) V_2 (x) V_3^{1,0}.  The polarisation
is psi = eps (x) eps (x) eps with eps the standard symplectic form on Q^2.

Everything below is computed in exact integer and rational arithmetic on this
explicit model, with the Lie algebra sl(2)^3 acting through its nine
generators e_i, f_i, h_i.

  (A) The commutant of G in End(wedge^2 V) has dimension four and is spanned
      by the four isotypic projectors: onto the line of the polarisation and
      onto U_12, U_13, U_23, where U_ij = Sym^2 V_i (x) Sym^2 V_j, each of
      dimension nine; the four projectors are computed from the three
      Casimir operators and are checked to be orthogonal idempotents summing
      to the identity.  Since End_G(H^2(X)) is the space of Hodge classes in
      the (2,2) Kunneth component of H^4(X x X), and the Galois group
      permutes U_12, U_13, U_23 transitively, the rational commutant is
      Q x F: the identity and the projector onto the polarisation come from
      divisors, and the trace-zero part of F gives the two exceptional
      classes.  So the two classes are exactly the real multiplication by F
      on the 27-dimensional weight two Hodge structure U = H^2_prim(X).

  (B) Hodge numbers, read off the grading by the number of V_3^{1,0} factors:
      H^2(X) has h^{2,0} = 6; U_12 is of pure type (1,1); U_13 and U_23 each
      have Hodge numbers (3,3,3); and T = sl(V_1) + sl(V_2) + sl(V_3), the
      Lie algebra of G, which is a sub-Hodge structure of End(H^1(X)), has
      Hodge numbers (1,7,1): it is of K3 type, of rank nine, with real
      multiplication by F.  This is the Hodge structure of the K3 surfaces of
      Picard number thirteen attached to X.

  (C) The map mu(t, t') = t^T Psi t' + t'^T Psi t from T (x) T to the
      alternating forms on V, built from the polarisation and the action of
      End(H^1), carries T_i (x) T_j onto U_ij with rank nine for each i != j,
      and T_i (x) T_i to the line of the polarisation.  Its image is the
      whole of H^2(X).

  (D) The adjoint.  With the Lefschetz pairing int_X x y theta^2 on H^2(X)
      and the form q_lambda = l_i tr(x y) on T_i, the endomorphism
      mu_kappa mu_kappa^dagger of H^2(X), where kappa is multiplication
      by e_i on T_i followed by the inclusion in End(V), acts on U_ij by
      nu g_i g_j with g = e^2/lambda and one nonzero rational nu, and
      preserves the line of theta.  When g_1, g_2, g_3 are distinct it
      generates on U the whole algebra spanned by the three projectors, and
      when they coincide only the scalars.  The norm form kappa^dagger kappa
      of the Kuga-Satake map, for the trace form on End(V), is
      multiplication by 4 e^2/lambda.  Here e_i and l_i stand for the three
      conjugates of elements e and lambda of F.

  (E) The Kuga-Satake map on the explicit Clifford algebra C(T, q_lambda),
      with stand-ins (1, 2, 5) for the conjugates of lambda.  The spin lifts
      of the three copies of sl(2) act on C^+(T), of dimension 256, and the
      vectors of highest weight (1,1,1) span 32 dimensions, so that
      C^+(T) = V (x) W with dim W = 32.  In the basis obtained by lowering,
      the map Psi(v) x = v x v_0 of the Kuga-Satake construction is
      v (x) N_i for v in T_i, with one matrix N_i on W for each factor; the
      three N_i anticommute pairwise and square to nonzero scalars
      proportional to the conjugates of lambda, so they are linearly
      independent.  Over Q the entries of the Kuga-Satake map are
      multiplications by elements e_ab of F with N_i = (sigma_i(e_ab)), and
      the independence forces the e_ab to span F.

Nothing here makes the two classes algebraic.  The computation says what they
are, and what one K3 surface would have to supply for them to be algebraic.
"""
from fractions import Fraction as Fr
from itertools import product

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


# ----------------------------------------------------------- matrices over Q
def zeros(r, c):
    return [[Fr(0)] * c for _ in range(r)]


def eye(n):
    m = zeros(n, n)
    for i in range(n):
        m[i][i] = Fr(1)
    return m


def mm(A, B):
    n, k, m = len(A), len(B), len(B[0])
    out = zeros(n, m)
    for i in range(n):
        Ai = A[i]
        for t in range(k):
            a = Ai[t]
            if a:
                Bt = B[t]
                row = out[i]
                for j in range(m):
                    if Bt[j]:
                        row[j] += a * Bt[j]
    return out


def madd(A, B, c=Fr(1)):
    return [[a + c * b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def mscale(A, c):
    return [[c * a for a in r] for r in A]


def tr(A):
    return [list(r) for r in zip(*A)]


def kron(A, B):
    n, m, p, q = len(A), len(A[0]), len(B), len(B[0])
    out = zeros(n * p, m * q)
    for i in range(n):
        for j in range(m):
            if A[i][j]:
                for k in range(p):
                    for l in range(q):
                        out[i * p + k][j * q + l] = A[i][j] * B[k][l]
    return out


def rank(rows):
    rows = [list(r) for r in rows]
    if not rows:
        return 0
    m = len(rows[0])
    r = 0
    for c in range(m):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        p = rows[r][c]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / p
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def nullspace(rows, n):
    rows = [list(r) for r in rows]
    piv_cols, R = [], []
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        p = rows[r][c]
        rows[r] = [x / p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv_cols.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv_cols]
    basis = []
    for f in free:
        v = [Fr(0)] * n
        v[f] = Fr(1)
        for i, pc in enumerate(piv_cols):
            v[pc] = -rows[i][f]
        basis.append(v)
    return basis


# ------------------------------------------------------------ the model
E2 = [[Fr(0), Fr(1)], [Fr(0), Fr(0)]]
F2 = [[Fr(0), Fr(0)], [Fr(1), Fr(0)]]
H2 = [[Fr(1), Fr(0)], [Fr(0), Fr(-1)]]
I2 = eye(2)
EPS = [[Fr(0), Fr(1)], [Fr(-1), Fr(0)]]


def on_factor(i, m):
    fs = [I2, I2, I2]
    fs[i] = m
    return kron(kron(fs[0], fs[1]), fs[2])


GENS = [(i, on_factor(i, m)) for i in range(3) for m in (E2, F2, H2)]
PSI = kron(kron(EPS, EPS), EPS)          # the polarisation, alternating
N = 8

# wedge^2 V with basis e_a ^ e_b, a < b
PAIRS = [(a, b) for a in range(N) for b in range(a + 1, N)]
IDX = {p: k for k, p in enumerate(PAIRS)}


def wedge2_op(X):
    """the action of a Lie algebra element X of gl(V) on wedge^2 V"""
    M = zeros(len(PAIRS), len(PAIRS))
    for col, (a, b) in enumerate(PAIRS):
        # X(e_a ^ e_b) = X e_a ^ e_b + e_a ^ X e_b
        for c in range(N):
            x = X[c][a]
            if x:
                if c != b:
                    lo, hi, s = (c, b, 1) if c < b else (b, c, -1)
                    M[IDX[(lo, hi)]][col] += s * x
            y = X[c][b]
            if y:
                if c != a:
                    lo, hi, s = (a, c, 1) if a < c else (c, a, -1)
                    M[IDX[(lo, hi)]][col] += s * y
    return M


def casimir(i):
    e, f, h = [wedge2_op(on_factor(i, m)) for m in (E2, F2, H2)]
    return madd(madd(mm(e, f), mm(f, e)), mm(h, h), Fr(1, 2))


def part_A():
    ops = [wedge2_op(X) for _, X in GENS]
    D = len(PAIRS)
    # commutant: M with X M - M X = 0 for all nine generators
    eqs = []
    for X in ops:
        for r in range(D):
            for c in range(D):
                row = [Fr(0)] * (D * D)
                for t in range(D):
                    if X[r][t]:
                        row[t * D + c] += X[r][t]        # (X M)[r][c]
                    if X[t][c]:
                        row[r * D + t] -= X[t][c]        # (M X)[r][c]
                if any(row):
                    eqs.append(row)
    # the system is large but very sparse; reduce it modulo nothing, exactly,
    # on the columns that can be nonzero
    ns = nullspace(eqs, D * D)
    check("the commutant of sl(2)^3 in End(wedge^2 V) has dimension four",
          len(ns) == 4, "dimension %d" % len(ns))

    Cs = [casimir(i) for i in range(3)]
    # eigenvalues: 0 on the trivial summand, 4 on the factors Sym^2 V_i
    # (with this normalisation the Casimir of Sym^2 is 4)
    Id = eye(D)
    P = {}
    # p_ij = (C_i/4)(C_j/4)(1 - C_k/4) etc.; on U_ij, C_i = C_j = 4, C_k = 0
    q = [mscale(C, Fr(1, 4)) for C in Cs]
    one_minus = [madd(Id, qq, Fr(-1)) for qq in q]
    P["12"] = mm(mm(q[0], q[1]), one_minus[2])
    P["13"] = mm(mm(q[0], q[2]), one_minus[1])
    P["23"] = mm(mm(q[1], q[2]), one_minus[0])
    P["0"] = mm(mm(one_minus[0], one_minus[1]), one_minus[2])
    idem = all(mm(P[k], P[k]) == P[k] for k in P)
    orth = all(mm(P[a], P[b]) == zeros(D, D) for a in P for b in P if a != b)
    total = madd(madd(P["12"], P["13"]), madd(P["23"], P["0"]))
    check("the four isotypic projectors are orthogonal idempotents summing "
          "to the identity", idem and orth and total == Id)
    ranks = {k: rank(P[k]) for k in P}
    check("their ranks are 1, 9, 9, 9", sorted(ranks.values()) == [1, 9, 9, 9],
          "trivial %d, U_12 %d, U_13 %d, U_23 %d"
          % (ranks["0"], ranks["12"], ranks["13"], ranks["23"]))
    # the projectors commute with G and span the commutant
    flat = [[x for r in P[k] for x in r] for k in ("0", "12", "13", "23")]
    comm = all(mm(X, P[k]) == mm(P[k], X) for X in ops for k in P)
    span = rank(flat + [list(v) for v in ns]) == 4 and rank(flat) == 4
    check("they commute with G and span the commutant", comm and span)
    return P


# -------------------------------------------------------- (B) Hodge numbers
def part_B(P):
    # basis e_(abc) of V, with bit c the V_3 index: c = 0 is V_3^{1,0}
    def p_of(v):
        a, b, c = (v >> 2) & 1, (v >> 1) & 1, v & 1
        return 1 if c == 0 else 0
    # H^2 = wedge^2 V: the (p, q) type of e_u ^ e_v is (p_u + p_v, ...)
    types = [p_of(u) + p_of(v) for (u, v) in PAIRS]
    h20 = sum(1 for t in types if t == 2)
    check("h^{2,0}(X) = 6", h20 == 6,
          "h^{2,0} = %d, h^{1,1} = %d, h^{0,2} = %d"
          % (h20, sum(1 for t in types if t == 1),
             sum(1 for t in types if t == 0)))
    # Hodge numbers of each U_ij: the projectors commute with the grading
    # operator h_3, which is diagonal in this basis, so count by trace
    D = len(PAIRS)
    out = {}
    for k in ("12", "13", "23", "0"):
        Pk = P[k]
        hn = []
        for p in (2, 1, 0):
            Dp = zeros(D, D)
            for i, t in enumerate(types):
                if t == p:
                    Dp[i][i] = Fr(1)
            hn.append(rank(mm(Pk, Dp)))
        out[k] = tuple(hn)
    check("U_12 is of pure type (1,1), and U_13, U_23 have Hodge numbers "
          "(3,3,3)", out["12"] == (0, 9, 0) and out["13"] == (3, 3, 3)
          and out["23"] == (3, 3, 3),
          "U_12 %s, U_13 %s, U_23 %s, polarisation %s"
          % (out["12"], out["13"], out["23"], out["0"]))
    # T = sl(V_1) + sl(V_2) + sl(V_3) inside End(V); an endomorphism e_u ->
    # e_v has type p_v - p_u, shifted by one to weight two
    Tbasis = [on_factor(i, m) for i in range(3) for m in (E2, F2, H2)]
    hodge = [0, 0, 0]
    for i in range(3):
        for m, s in ((E2, +1), (F2, -1), (H2, 0)):
            # on V_3, e raises the index 1 -> 0, i.e. (0,1) -> (1,0)
            if i == 2:
                hodge[1 - s] += 1
            else:
                hodge[1] += 1
    check("T = Lie(G) is of K3 type, with Hodge numbers (1,7,1)",
          tuple(hodge) == (1, 7, 1), "Hodge numbers %s" % (tuple(hodge),))
    return Tbasis


# ----------------------------------------------------- (C) the map mu
def alt_to_vec(M):
    return [M[a][b] for (a, b) in PAIRS]


def part_C(P, Tbasis):
    def Mu(t, s):
        A = mm(mm(tr(t), PSI), s)
        return madd(A, tr(A), Fr(-1))
    blocks = {}
    for i in range(3):
        for j in range(3):
            vecs = [alt_to_vec(Mu(t, s)) for t in Tbasis[3 * i:3 * i + 3]
                    for s in Tbasis[3 * j:3 * j + 3]]
            blocks[(i, j)] = vecs
    # the forms here live in wedge^2 V^dual; with psi symplectic on each
    # factor the dual is identified with wedge^2 V by eps, which is
    # G-equivariant, so the isotypic projectors apply after that
    # identification.  Identify by the matrix of eps^{(x)3} acting on both
    # slots.
    def dual_to_primal(vec):
        M = zeros(N, N)
        for k, (a, b) in enumerate(PAIRS):
            M[a][b] = vec[k]
            M[b][a] = -vec[k]
        Pinv = PSI                        # PSI^{-1} = -PSI, sign irrelevant
        Y = mm(mm(Pinv, M), tr(Pinv))
        return [Y[a][b] for (a, b) in PAIRS]

    def comp(vecs, key):
        Pk = P[key]
        return [[sum(Pk[r][c] * v[c] for c in range(len(v)))
                 for r in range(len(v))] for v in map(dual_to_primal, vecs)]

    name = {(0, 1): "12", (0, 2): "13", (1, 2): "23"}
    ok_mixed = True
    detail = []
    for (i, j), key in name.items():
        vecs = blocks[(i, j)]
        rk = rank([dual_to_primal(v) for v in vecs])
        inside = rank(comp(vecs, key)) == rk
        outside = all(rank(comp(vecs, other)) == 0
                      for other in ("0", "12", "13", "23") if other != key)
        ok_mixed &= (rk == 9 and inside and outside)
        detail.append("T_%d (x) T_%d -> U_%s: rank %d"
                      % (i + 1, j + 1, key, rk))
    check("mu carries T_i (x) T_j onto U_ij, with rank nine, for i != j",
          ok_mixed, "\n".join(detail))
    ok_diag = True
    for i in range(3):
        vecs = blocks[(i, i)]
        ok_diag &= all(rank(comp(vecs, k)) == 0 for k in ("12", "13", "23"))
        ok_diag &= rank([dual_to_primal(v) for v in vecs]) == 1
    check("mu carries T_i (x) T_i onto the line of the polarisation",
          ok_diag)
    allv = [dual_to_primal(v) for key in blocks for v in blocks[key]]
    check("the image of T (x) T is the whole of H^2(X)", rank(allv) == 28,
          "rank %d of 28" % rank(allv))


# ------------------------------------------ (D) the adjoint and the transport
def wedge_bits(x, y):
    """sign and product of two basis monomials of the exterior algebra of V,
    given as bitmasks; the sign is that of sorting the concatenation"""
    if x & y:
        return 0, 0
    s = 0
    for b in range(N):
        if (y >> b) & 1:
            s += bin(x >> (b + 1)).count("1")
    return (-1 if s % 2 else 1), x | y


def wedge(u, v):
    out = {}
    for x, a in u.items():
        for y, b in v.items():
            s, z = wedge_bits(x, y)
            if s:
                out[z] = out.get(z, Fr(0)) + s * a * b
    return {k: c for k, c in out.items() if c}


def vec_to_form(vec):
    return {(1 << a) | (1 << b): c for (a, b), c in zip(PAIRS, vec) if c}


def gram_lefschetz(P):
    """B(x, y) = coefficient of x ^ y ^ theta ^ theta in wedge^8 V, where
    theta spans the line of the polarisation; this is the pairing
    int_X x y theta^2, and it is given by an algebraic class"""
    D = len(PAIRS)
    theta = None
    for c in range(D):
        col = [P["0"][r][c] for r in range(D)]
        if any(col):
            theta = col
            break
    tt = wedge(vec_to_form(theta), vec_to_form(theta))
    top = (1 << N) - 1
    G = zeros(D, D)
    for p in range(D):
        ep = {(1 << PAIRS[p][0]) | (1 << PAIRS[p][1]): Fr(1)}
        ept = wedge(ep, tt)
        for q in range(D):
            eq = {(1 << PAIRS[q][0]) | (1 << PAIRS[q][1]): Fr(1)}
            G[p][q] = wedge(eq, ept).get(top, Fr(0))
    return G, theta


def gram_T(weights):
    """q_lambda on T = sl(V_1) + sl(V_2) + sl(V_3): l_i tr(x y) on the i-th
    factor, in the basis e, f, h of each factor"""
    g = [[Fr(0), Fr(1), Fr(0)], [Fr(1), Fr(0), Fr(0)], [Fr(0), Fr(0), Fr(2)]]
    G = zeros(9, 9)
    for i in range(3):
        for a in range(3):
            for b in range(3):
                G[3 * i + a][3 * i + b] = weights[i] * g[a][b]
    return G


def inverse(M):
    n = len(M)
    A = [list(r) + list(e) for r, e in zip(M, eye(n))]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        p = A[c][c]
        A[c] = [x / p for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [r[n:] for r in A]


def phi_matrix(Tbasis, e):
    """the 28 x 81 matrix of mu_kappa(x (x) y) = mu(kappa x, kappa y), with
    kappa multiplication by e_i on T_i followed by the inclusion in End(V)"""
    def Mu(t, s):
        A = mm(mm(tr(t), PSI), s)
        return madd(A, tr(A), Fr(-1))

    def dual_to_primal(M):
        Y = mm(mm(PSI, M), tr(PSI))
        return [Y[a][b] for (a, b) in PAIRS]
    kt = [mscale(Tbasis[a], e[a // 3]) for a in range(9)]
    cols = [dual_to_primal(Mu(kt[a], kt[b])) for a in range(9)
            for b in range(9)]
    return tr(cols)


def part_D(P, Tbasis):
    D = len(PAIRS)
    GB, theta = gram_lefschetz(P)
    check("the Lefschetz pairing int x y theta^2 on H^2(X) is nondegenerate",
          rank(GB) == D, "rank %d of %d" % (rank(GB), D))

    def E_of(e, l):
        Mu = phi_matrix(Tbasis, e)
        GT = gram_T(l)
        GTi = inverse(GT)
        G2i = kron(GTi, GTi)                   # (q_l (x) q_l)^{-1}
        return mm(mm(mm(Mu, G2i), tr(Mu)), GB)   # mu mu^dagger

    # the scalar nu with mu mu^dagger = nu on U, for the canonical form
    E1 = E_of([Fr(1)] * 3, [Fr(1)] * 3)
    scal = {}
    for k in ("0", "12", "13", "23"):
        Pk = P[k]
        EP = mm(E1, Pk)
        c = None
        for r in range(D):
            for s in range(D):
                if Pk[r][s] != 0:
                    c = EP[r][s] / Pk[r][s]
                    break
            if c is not None:
                break
        scal[k] = c if EP == mscale(Pk, c) else None
    ok = (all(scal[k] is not None for k in scal)
          and scal["12"] == scal["13"] == scal["23"] != 0)
    c = scal["12"]
    check("mu mu^dagger acts on each U_ij by one and the same nonzero "
          "rational nu", ok,
          "nu = %s on U_12, U_13, U_23; %s on the line of theta"
          % (c, scal["0"]))

    # the transport: with kappa = e and q_lambda = l, mu_kappa mu_kappa^dagger
    # acts on U_ij by nu g_i g_j, g = e^2 / l
    samples = [((Fr(1), Fr(2), Fr(3)), (Fr(1), Fr(1), Fr(1))),
               ((Fr(2), Fr(-1), Fr(5)), (Fr(3), Fr(7), Fr(2))),
               ((Fr(1, 2), Fr(3), Fr(-2)), (Fr(5), Fr(1, 3), Fr(4)))]
    ok = True
    detail = []
    for e, l in samples:
        E = E_of(list(e), list(l))
        g = [e[i] * e[i] / l[i] for i in range(3)]
        want = {"12": c * g[0] * g[1], "13": c * g[0] * g[2],
                "23": c * g[1] * g[2]}
        good = all(mm(E, P[k]) == mscale(P[k], want[k]) for k in want)
        # and the line of theta is preserved
        line = mm(E, P["0"])
        good &= rank([list(r) for r in tr(line)] + [theta]) == 1
        ok &= good
        detail.append("e = (%s), lambda = (%s): on U_ij by nu g_i g_j, "
                      "g = (%s)" % (", ".join(map(str, e)),
                                    ", ".join(map(str, l)),
                                    ", ".join(map(str, g))))
    check("with kappa = e and the form q_lambda, mu mu^dagger acts on U_ij "
          "by nu g_i g_j, where g = e^2/lambda", ok, "\n".join(detail))

    # the algebra that E generates on U: three-dimensional, and equal to the
    # span of the three projectors, exactly when g_1, g_2, g_3 are distinct;
    # one-dimensional when they coincide
    PW = madd(eye(D), P["0"], Fr(-1))
    flatP = [[x for r in P[k] for x in r] for k in ("12", "13", "23")]
    ok = True
    detail = []
    for e, l in [((Fr(1), Fr(1), Fr(1)), (Fr(1), Fr(1), Fr(1)))] + samples[1:]:
        EW = mm(E_of(list(e), list(l)), PW)
        pw = [PW, EW, mm(EW, EW)]
        flat = [[x for r in M for x in r] for M in pw]
        g = [e[i] * e[i] / l[i] for i in range(3)]
        distinct = len(set(g)) == 3
        dim = rank(flat)
        same = rank(flat + flatP) == 3
        ok &= (dim == 3 and same) if distinct else dim == 1
        detail.append("g = (%s): the algebra generated on U has dimension %d"
                      % (", ".join(map(str, g)), dim))
    check("E generates on U the full algebra spanned by the three "
          "projectors when g has distinct conjugates, and only the scalars "
          "when it does not", ok, "\n".join(detail))

    # the norm form of the Kuga-Satake map itself: kappa^dagger kappa, with the
    # trace form on End(V), is multiplication by 4 e_i^2 / l_i on T_i
    ok = True
    for e, l in samples:
        kt = [mscale(Tbasis[a], e[a // 3]) for a in range(9)]
        M = [[sum(mm(kt[a], kt[b])[r][r] for r in range(N)) for b in range(9)]
             for a in range(9)]
        KK = mm(inverse(gram_T(list(l))), M)
        want = zeros(9, 9)
        for a in range(9):
            want[a][a] = 4 * e[a // 3] ** 2 / l[a // 3]
        ok &= KK == want
    check("kappa^dagger kappa, for the trace form on End(V), is "
          "multiplication by 4 e^2/lambda", ok)
    return c


# ------------------------------------ (E) the Kuga-Satake map, explicitly
# The Clifford algebra C(T, q_lambda) of the split model: T = T_1 + T_2 + T_3,
# T_i = sl(2) with the form l_i tr(xy), in the orthogonal basis h, e + f,
# e - f of each factor, whose squares are 2 l_i, 2 l_i, -2 l_i.  Monomials
# are bit masks on the nine generators.
NT = 9
LAM = [Fr(1), Fr(2), Fr(5)]      # stand-ins for the conjugates of lambda
QSQ = [z for l in LAM for z in (2 * l, 2 * l, -2 * l)]
EVEN = [m for m in range(1 << NT) if bin(m).count("1") % 2 == 0]
EIDX = {m: k for k, m in enumerate(EVEN)}


def cmono(a, b):
    s = 0
    for k in range(NT):
        if (b >> k) & 1:
            s += bin(a >> (k + 1)).count("1")
    coef = Fr(-1) if s % 2 else Fr(1)
    both = a & b
    for k in range(NT):
        if (both >> k) & 1:
            coef *= QSQ[k]
    return coef, a ^ b


def cmul(x, y):
    out = {}
    for a, ca in x.items():
        for b, cb in y.items():
            c, m = cmono(a, b)
            v = out.get(m, 0) + c * ca * cb
            if v:
                out[m] = v
            else:
                out.pop(m, None)
    return out


def cadd(x, y, c=1):
    out = dict(x)
    for k, v in y.items():
        w = out.get(k, 0) + c * v
        if w:
            out[k] = w
        else:
            out.pop(k, None)
    return out


def gen(k):
    return {1 << k: Fr(1)}


def tvec(i, name):
    """e, f, h of the i-th factor as vectors of T inside C(T)"""
    b = 3 * i
    if name == "h":
        return {1 << b: Fr(1)}
    s = Fr(1, 2) if name == "e" else Fr(-1, 2)
    return {1 << (b + 1): Fr(1, 2), 1 << (b + 2): s}


def tbracket(i, x, y):
    """[x, y] in sl(2), for x, y vectors of the i-th factor"""
    b = 3 * i

    def mat(v):
        c1, c2, ch = (v.get(1 << (b + 1), 0), v.get(1 << (b + 2), 0),
                      v.get(1 << b, 0))
        return [[ch, c1 + c2], [c1 - c2, -ch]]
    X, Y = mat(x), mat(y)
    Z = [[sum(X[r][t] * Y[t][c] - Y[r][t] * X[t][c] for t in range(2))
          for c in range(2)] for r in range(2)]
    a, bb, c = Z[0][1], Z[1][0], Z[0][0]
    out = {}
    for k, v in ((b, c), (b + 1, (a + bb) / 2), (b + 2, (a - bb) / 2)):
        if v:
            out[1 << k] = Fr(v)
    return out


def spin_lift(i, x):
    """the element of the span of the bivectors of T_i whose commutator with
    every v in T_i is [x, v]: the action of x on the spinors"""
    b = 3 * i
    biv = [cmul(gen(p), gen(q)) for p, q in ((b, b + 1), (b, b + 2),
                                              (b + 1, b + 2))]
    rows = []
    for c in range(b, b + 3):
        target = tbracket(i, x, gen(c))
        imgs = [cadd(cmul(z, gen(c)), cmul(gen(c), z), -1) for z in biv]
        keys = set(target).union(*imgs)
        for kk in keys:
            rows.append([im.get(kk, Fr(0)) for im in imgs]
                        + [target.get(kk, Fr(0))])
    sol = nullspace([r[:3] + [-r[3]] for r in rows], 4)
    sol = [v for v in sol if v[3] != 0]
    v = [z / sol[0][3] for z in sol[0]]
    out = {}
    for c, z in zip(v[:3], biv):
        out = cadd(out, z, c)
    return out


def left_cols(z):
    return [cmul(z, {m: Fr(1)}) for m in EVEN]


def apply_cols(cols, vec):
    out = {}
    for m, c in vec.items():
        out = cadd(out, cols[EIDX[m]], c)
    return out


def sparse_nullspace(rows, n):
    piv = {}
    for row in rows:
        r = {k: v for k, v in row.items() if v}
        while True:
            hit = [k for k in r if k in piv]
            if not hit:
                break
            f = r[hit[0]]
            for k, v in piv[hit[0]].items():
                w = r.get(k, 0) - f * v
                if w:
                    r[k] = w
                else:
                    r.pop(k, None)
        if not r:
            continue
        lead = min(r)
        f = r[lead]
        r = {k: v / f for k, v in r.items()}
        for prow in piv.values():
            if lead in prow:
                g = prow[lead]
                for k, v in r.items():
                    w = prow.get(k, 0) - g * v
                    if w:
                        prow[k] = w
                    else:
                        prow.pop(k, None)
        piv[lead] = r
    basis = []
    for fcol in (c for c in range(n) if c not in piv):
        v = {fcol: Fr(1)}
        for pc, prow in piv.items():
            if fcol in prow:
                v[pc] = -prow[fcol]
        basis.append(v)
    return basis


def part_E():
    D = len(EVEN)
    lifts = {(i, nm): spin_lift(i, tvec(i, nm)) for i in range(3)
             for nm in "efh"}
    ok = all(cadd(cmul(lifts[(i, "e")], lifts[(i, "f")]),
                  cmul(lifts[(i, "f")], lifts[(i, "e")]), -1)
             == lifts[(i, "h")] for i in range(3))
    check("the spin lifts of the three copies of sl(2) satisfy [e, f] = h "
          "in C^+(T)", ok)
    ops = {k: left_cols(v) for k, v in lifts.items()}
    # highest weight vectors of weight (1,1,1): e_i x = 0 and h_i x = x
    rows = []
    for i in range(3):
        for nm, shift in (("e", 0), ("h", 1)):
            R = {}
            for j, col in enumerate(ops[(i, nm)]):
                for m, c in col.items():
                    R.setdefault(m, {})[j] = R.get(m, {}).get(j, 0) + c
            if shift:
                for j in range(D):
                    R.setdefault(EVEN[j], {})[j] = \
                        R.get(EVEN[j], {}).get(j, 0) - 1
            rows += [r for r in R.values() if any(r.values())]
    HW = [{EVEN[j]: c for j, c in v.items()}
          for v in sparse_nullspace(rows, D)]
    fops = [ops[(i, "f")] for i in range(3)]

    def lower(abc, w):
        for i in range(3):
            if (abc >> (2 - i)) & 1:
                w = apply_cols(fops[i], w)
        return w
    B = [lower(abc, w) for abc in range(8) for w in HW]
    M = [[Fr(0)] * D for _ in range(D)]
    for j, vec in enumerate(B):
        for m, c in vec.items():
            M[EIDX[m]][j] = c
    Minv = inverse(M)
    check("C^+(T) has dimension 256 and is V^{32}: the vectors of highest "
          "weight (1,1,1) span 32 dimensions, and lowering them gives a basis",
          D == 256 and len(HW) == 32 and Minv is not None,
          "dim C^+ = %d, highest weight vectors %d" % (D, len(HW)))

    def coords(vec):
        out = [Fr(0)] * D
        for m, c in vec.items():
            col = EIDX[m]
            for r in range(D):
                if Minv[r][col]:
                    out[r] += Minv[r][col] * c
        return out
    v0 = gen(0)

    def psi(v, x):
        return cmul(cmul(v, x), v0)
    m = 32
    Ns, ok = [], True
    for i in range(3):
        N = [[Fr(0)] * m for _ in range(m)]
        for k in range(m):
            cc = coords(psi(tvec(i, "h"), B[k]))
            for l in range(m):
                N[l][k] = cc[l]
        Ns.append(N)
        for nm in "efh":
            R = [[Fr(0)] * 8 for _ in range(8)]
            for abc in range(8):
                cc = coords(apply_cols(ops[(i, nm)], B[abc * m]))
                for abc2 in range(8):
                    R[abc2][abc] = cc[abc2 * m]
            v = tvec(i, nm)
            for j in range(D):
                cc = coords(psi(v, B[j]))
                abc, k = divmod(j, m)
                for j2 in range(D):
                    abc2, l = divmod(j2, m)
                    if cc[j2] != R[abc2][abc] * N[l][k]:
                        ok = False
    check("the Kuga-Satake map Psi(v) x = v x v_0 acts on V (x) W as "
          "v (x) N_i for v in T_i, with one N_i per factor", ok)

    def mul32(A, C):
        return [[sum(A[r][t] * C[t][c] for t in range(m) if A[r][t])
                 for c in range(m)] for r in range(m)]
    anti = all(madd(mul32(Ns[i], Ns[j]), mul32(Ns[j], Ns[i])) == zeros(m, m)
               for i in range(3) for j in range(3) if i < j)
    sq = []
    for i in range(3):
        Q = mul32(Ns[i], Ns[i])
        s = Q[0][0]
        sq.append(s if Q == mscale(eye(m), s) and s != 0 else None)
    check("N_1, N_2, N_3 anticommute pairwise and each squares to a nonzero "
          "scalar, proportional to the conjugate of lambda", anti
          and all(z is not None for z in sq)
          and len({sq[i] / LAM[i] for i in range(3)}) == 1,
          "N_i^2 = %s for lambda = (%s)" % (", ".join(map(str, sq)),
                                            ", ".join(map(str, LAM))))
    flat = [[x for r in N for x in r] for N in Ns]
    check("so N_1, N_2, N_3 are linearly independent, which forces the "
          "entries of the Kuga-Satake map to span the cubic field",
          rank(flat) == 3,
          "rank %d" % rank(flat))


if __name__ == "__main__":
    print("(XLI) the exceptional classes of a Mumford fourfold as a real "
          "multiplication")
    print()
    print("  (A) the commutant of G in End(H^2)")
    P = part_A()
    print("  (B) Hodge numbers")
    T = part_B(P)
    print("  (C) the map mu from T (x) T to H^2(X)")
    part_C(P, T)
    print("  (D) the adjoint of mu, and the transport of the real "
          "multiplication")
    part_D(P, T)
    print("  (E) the Kuga-Satake map on the explicit Clifford algebra")
    part_E()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
