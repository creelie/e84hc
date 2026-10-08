#!/usr/bin/env python3
"""
cm_source.py

Item (LXIV) of the computations: the Weil structure of a Mumford fourfold at
a CM point, and what the cycles on its square have to use.

Model.  As in item (XLIV): V = V_1 (x) V_2 (x) V_3 with basis indexed by
(a,b,c) in {0,1}^3 and weight (1-2a, 1-2b, 1-2c), psi = eps (x) eps (x) eps,
H^1(X x X) = V (+) V on bits 0..7 and 8..15.  At a CM point c the Hodge group
of X_c is the diagonal torus of the weight basis, so the Hodge classes of X_c
and of X_c x X_c are spanned by the monomials of weight zero, and
End^0(X_c) (x) C is the algebra A of diagonal matrices; a pair (phi, psi) of
diagonal matrices acts on 1-forms by e_w -> phi_w e_w^(1) + psi_w e_w^(2),
and the pull-back of a class along (phi, psi) is the induced ring map.  The
zero-sum 4-subsets of the weights that contain no pair of opposite weights
are the two tetrahedra T_+ (an even number of -1) and T_- = -T_+; the
monomials t_+, t_- are the two Hodge classes of X_c of degree four that are
not products of divisor classes, the Weil line of X_c for the field k_c that
is constant on each tetrahedron.  A_W is the subalgebra of A constant on T_+
and on T_- (k_c (x) C), A^+ the subalgebra with phi_w = phi_{-w} (the Rosati
fixed algebra K_c^+ (x) C).

What is checked:

  (A) the weight-zero monomials of degree 2 and 4 on X_c x X_c number 16 and
      132; the products of the 16 divisor classes span 100 dimensions, the
      products of the three Sp-invariant ones 6; the zero-sum 4-subsets of
      the weights are the six unions of two opposite pairs and the two
      tetrahedra, T_- = -T_+, each meeting every opposite pair once; the 32
      weight-zero monomials that are not products of two divisor classes are
      exactly the tetrahedron monomials e^(c)_T, T = T_+, T_-, c in {1,2}^T;

  (B) the pull-backs (a,b)^* t_{+-} along scalar pairs have five homogeneous
      components each (by the number of factors from the second copy),
      spanning 10 dimensions; with the divisor products they span 110 of the
      132, and with the Sp-invariant divisor products 16; pull-backs along
      forty random pairs in A_W add nothing to the 110;

  (C) the exceptional classes pi_12 - pi_13 and pi_12 - pi_23, and four
      random omega_a with a_0 = 0 and a_1, a_2, a_3 not all equal, lie outside
      the 110-dimensional span, while pi_0 and pi_12 + pi_13 + pi_23 lie
      inside it, so that the span meets the space of the four pi exactly in
      the classes with a_1 = a_2 = a_3;

  (D) pull-backs of t_{+-} along forty random pairs in A^+ span, with the
      divisor products, all 132 Hodge classes;

  (E) the four pi are the classes of the operators (1 + s_1 + s_2 - s_3)/4,
      (1 + s_1 - s_2 + s_3)/4, (1 - s_1 + s_2 + s_3)/4 and
      (1 - s_1 - s_2 - s_3)/4 on wedge^2 V, where s_t exchanges the t-th
      tensor factors of the two slots; this is the identity behind the proof
      in the paper;

  (F) an omega_a with a_0 = 0 is supported on the 12 mixed tetrahedron
      monomials e^(1)_S e^(2)_{T-S}, |S| = 2, and on 24 products of two
      divisor classes, 16 of the form e^(1)_i e^(1)_j e^(2)_{-i} e^(2)_{-j}
      and 8 of the form e^(1)_w e^(1)_{-w} e^(2)_{w'} e^(2)_{-w'}; on each
      tetrahedron the coefficients of the six mixed monomials have absolute
      values |a_2 - a_3|/2, |a_1 - a_3|/2, |a_1 - a_2|/2 on the pairs of
      monomials whose two weights differ in the coordinates {1,2}, {1,3},
      {2,3}; pi_0 and pi_12 + pi_13 + pi_23 contain no tetrahedron monomial;
      and the (2,2)-component of a scalar pull-back of t_T has all six
      coefficients of absolute value one.

Everything is exact rational arithmetic in the exterior algebra.

Run:  python3 cm_source.py
"""
import itertools
import random

import sympy

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


NB = 16


def popcount(m):
    return bin(m).count("1")


def mono_sign(a, b):
    if a & b:
        return 0
    s, bb = 0, b
    while bb:
        j = (bb & -bb).bit_length() - 1
        s += popcount(a >> (j + 1))
        bb &= bb - 1
    return -1 if s % 2 else 1


def wt(i):
    j = i % 8
    return (1 - 2 * ((j >> 2) & 1), 1 - 2 * ((j >> 1) & 1), 1 - 2 * (j & 1))


def eps(a, b):
    return 1 if (a, b) == (0, 1) else (-1 if (a, b) == (1, 0) else 0)


def psi(i, j):
    if i // 8 != j // 8:
        return 0
    a, b = i % 8, j % 8
    v = 1
    for bit in (2, 1, 0):
        v *= eps((a >> bit) & 1, (b >> bit) & 1)
    return v


# ------------------------------------------------- wedge^2 V and the tensors
PAIRS = [(a, b) for a in range(8) for b in range(a + 1, 8)]
PIDX = {p: k for k, p in enumerate(PAIRS)}


def gen_matrix(t, raising):
    M = sympy.zeros(8, 8)
    bit = 2 - t
    for i in range(8):
        if raising and (i >> bit) & 1:
            M[i - (1 << bit), i] = 1
        if (not raising) and not (i >> bit) & 1:
            M[i + (1 << bit), i] = 1
    return M


def on_wedge2(M):
    W = sympy.zeros(28, 28)
    for k, (a, b) in enumerate(PAIRS):
        for r in range(8):
            if M[r, a] != 0 and r != b:
                s, p = (1, (r, b)) if r < b else (-1, (b, r))
                W[PIDX[p], k] += s * M[r, a]
            if M[r, b] != 0 and r != a:
                s, p = (1, (a, r)) if a < r else (-1, (r, a))
                W[PIDX[p], k] += s * M[r, b]
    return W


def tensor_class(cols):
    """The class in H^4(X x X) of an operator on wedge^2 V given by its
    columns (images of the basis e_a e_b, as vectors in the PAIRS basis):
    sum over a < b of A(e_a e_b) (x) (dual of e_a e_b), the dual basis being
    taken for the form induced by psi."""
    out = {}
    for k, (a, b) in enumerate(PAIRS):
        u = cols[k]
        na, nb = a ^ 7, b ^ 7
        chi = psi(a, na) * psi(b, nb)
        if na < nb:
            j, vsign = PIDX[(na, nb)], chi
        else:
            j, vsign = PIDX[(nb, na)], -chi
        (c, d) = PAIRS[j]
        m2 = ((1 << c) | (1 << d)) << 8
        for i in range(28):
            if u[i] == 0:
                continue
            (aa, bb) = PAIRS[i]
            m1 = (1 << aa) | (1 << bb)
            s = mono_sign(m1, m2)
            out[m1 | m2] = out.get(m1 | m2, 0) + s * u[i] * vsign
    return {k: sympy.nsimplify(v) for k, v in out.items() if v != 0}


def build_tensors():
    cas = []
    for t in range(3):
        E = on_wedge2(gen_matrix(t, True))
        F = on_wedge2(gen_matrix(t, False))
        H = on_wedge2(sympy.diag(*[wt(i)[t] for i in range(8)]))
        cas.append(H * H + 2 * (E * F + F * E))
    pieces = {}
    for key, pat in (("0", (0, 0, 0)), ("12", (1, 1, 0)), ("13", (1, 0, 1)),
                     ("23", (0, 1, 1))):
        M = sympy.Matrix.vstack(*[cas[t] - (8 if pat[t] else 0) * sympy.eye(28)
                                  for t in range(3)])
        pieces[key] = M.nullspace()
    B = sympy.zeros(28, 28)
    for k, (a, b) in enumerate(PAIRS):
        for l, (c, d) in enumerate(PAIRS):
            B[k, l] = psi(a, c) * psi(b, d) - psi(a, d) * psi(b, c)
    PI = {}
    for key, basis in pieces.items():
        Ub = sympy.Matrix.hstack(*basis)
        dual = Ub * (Ub.T * B * Ub).inv().T
        out = {}
        for k in range(Ub.shape[1]):
            u, v = Ub[:, k], dual[:, k]
            for i in range(28):
                if u[i] == 0:
                    continue
                for j in range(28):
                    if v[j] == 0:
                        continue
                    (a, b), (c, d) = PAIRS[i], PAIRS[j]
                    m1 = (1 << a) | (1 << b)
                    m2 = ((1 << c) | (1 << d)) << 8
                    s = mono_sign(m1, m2)
                    out[m1 | m2] = out.get(m1 | m2, 0) + s * u[i] * v[j]
        PI[key] = {k: sympy.nsimplify(v) for k, v in out.items() if v != 0}
    return pieces, PI


def swap_operator(t):
    """s_t on wedge^2 V: exchange the t-th tensor factors of the two slots.
    On e_a e_b it is the identity if a and b agree in coordinate t, and
    otherwise flips coordinate t of both.  Returned as its 28 columns."""
    bit = 2 - t
    cols = []
    for (a, b) in PAIRS:
        v = [0] * 28
        if ((a >> bit) & 1) == ((b >> bit) & 1):
            v[PIDX[(a, b)]] = 1
        else:
            a2, b2 = a ^ (1 << bit), b ^ (1 << bit)
            if a2 < b2:
                v[PIDX[(a2, b2)]] = 1
            else:
                v[PIDX[(b2, a2)]] = -1
        cols.append(v)
    return cols


def combine(terms):
    """A rational combination of column lists."""
    cols = []
    for k in range(28):
        v = [0] * 28
        for coef, C in terms:
            for i in range(28):
                v[i] += coef * C[k][i]
        cols.append(v)
    return cols


def wedge(x, y):
    out = {}
    for m, c in x.items():
        for n, d in y.items():
            if m & n:
                continue
            s = mono_sign(m, n)
            out[m | n] = out.get(m | n, 0) + s * c * d
    return {k: v for k, v in out.items() if v != 0}


def add(x, y, cy=1):
    out = dict(x)
    for m, c in y.items():
        out[m] = out.get(m, 0) + cy * c
    return {k: v for k, v in out.items() if v != 0}


def span_rank(forms):
    keys = sorted(set().union(*[set(f) for f in forms]))
    M = sympy.Matrix([[f.get(k, 0) for k in keys] for f in forms])
    return M.rank()


def in_span(forms, target):
    return span_rank(forms + [target]) == span_rank(forms)


def weight16(i):
    return wt(i % 8)


def pull(T, phi, ps):
    """The pull-back of the monomial t_T along the pair (phi, ps) of
    diagonal matrices, phi and ps indexed by the eight weights."""
    form = {0: 1}
    for i in T:
        form = wedge(form, {1 << i: phi[i], 1 << (i + 8): ps[i]})
    return form


def run():
    W = {i: wt(i) for i in range(8)}
    neg = {i: i ^ 7 for i in range(8)}
    assert all(W[neg[i]] == tuple(-x for x in W[i]) for i in range(8))

    # ------------------------------------------------------------- (A)
    hodge2 = [S for S in itertools.combinations(range(16), 2)
              if all(sum(weight16(i)[k] for i in S) == 0 for k in range(3))]
    hodge4 = [S for S in itertools.combinations(range(16), 4)
              if all(sum(weight16(i)[k] for i in S) == 0 for k in range(3))]
    cm_divs = [{(1 << S[0]) | (1 << S[1]): 1} for S in hodge2]
    theta1 = {(1 << i) | (1 << j): psi(i, j) for i in range(8)
              for j in range(i + 1, 8) if psi(i, j)}
    theta2 = {(1 << (i + 8)) | (1 << (j + 8)): psi(i, j) for i in range(8)
              for j in range(i + 1, 8) if psi(i, j)}
    mixed = {}
    for i in range(8):
        for j in range(8):
            if psi(i, j):
                mixed[(1 << i) | (1 << (j + 8))] = psi(i, j) * mono_sign(
                    1 << i, 1 << (j + 8))
    inv_divs = [theta1, theta2, mixed]
    deg4_cm = [wedge(a, b) for a in cm_divs for b in cm_divs]
    deg4_inv = [wedge(a, b) for a in inv_divs for b in inv_divs]
    zero4 = [S for S in itertools.combinations(range(8), 4)
             if all(sum(W[i][k] for i in S) == 0 for k in range(3))]
    pairs = [S for S in zero4 if all(neg[i] in S for i in S)]
    tets = [S for S in zero4 if S not in pairs]
    tet_ok = (len(tets) == 2 and set(tets[1]) == {neg[i] for i in tets[0]}
              and all(len({min(i, neg[i]) for i in T}) == 4 for T in tets))
    # the tetrahedron monomials e^(c)_T and the divisor-product monomials
    tetmonos = set()
    for T in tets:
        for cc in itertools.product((0, 1), repeat=4):
            tetmonos.add(sum(1 << (i + 8 * s) for i, s in zip(T, cc)))
    divmonos = set()
    for f in deg4_cm:
        divmonos |= set(f)
    allmonos = {sum(1 << i for i in S) for S in hodge4}
    check("16 Hodge classes of degree 2 and 132 of degree 4 at a CM point; "
          "divisor products span 100, Sp-invariant divisor products 6; the "
          "zero-sum 4-subsets are 6 unions of opposite pairs and 2 "
          "tetrahedra T_- = -T_+, each meeting every opposite pair once; the "
          "32 non-divisor-product monomials are the tetrahedron monomials",
          len(hodge2) == 16 and len(hodge4) == 132 and span_rank(deg4_cm) == 100
          and span_rank(deg4_inv) == 6 and len(pairs) == 6 and tet_ok
          and len(tetmonos) == 32 and len(divmonos) == 100
          and allmonos == tetmonos | divmonos and not (tetmonos & divmonos),
          "T_+ = %s" % [W[i] for i in tets[0]])

    # ------------------------------------------------------------- (B)
    def components(T):
        comps = {k: {} for k in range(5)}
        for assign in itertools.product((0, 1), repeat=4):
            form = {0: 1}
            for i, s in zip(T, assign):
                form = wedge(form, {1 << (i + 8 * s): 1})
            k = sum(assign)
            for m, c in form.items():
                comps[k][m] = comps[k].get(m, 0) + c
        return [comps[k] for k in range(5)]
    comps = components(tets[0]) + components(tets[1])
    rng = random.Random(11)
    weil = []
    for _ in range(40):
        vals = [rng.randint(-6, 6) for _ in range(4)]
        phi = [vals[0] if i in tets[0] else vals[1] for i in range(8)]
        ps = [vals[2] if i in tets[0] else vals[3] for i in range(8)]
        weil += [pull(T, phi, ps) for T in tets]
    r_scalar = span_rank(deg4_cm + comps)
    check("the scalar pull-backs (a,b)^* t_{+-} have ten independent "
          "components; with the divisor products they span 110 of the 132, "
          "with the Sp-invariant divisor products 16; forty random "
          "pull-backs along pairs constant on each tetrahedron add nothing",
          span_rank(comps) == 10 and r_scalar == 110
          and span_rank(deg4_inv + comps) == 16
          and span_rank(deg4_cm + comps + weil) == 110, "rank %d" % r_scalar)

    # ------------------------------------------------------------- (C)
    pieces, PI = build_tensors()
    exc1 = add(PI["12"], PI["13"], -1)
    exc2 = add(PI["12"], PI["23"], -1)
    sumpi = add(add(PI["12"], PI["13"]), PI["23"])
    base = deg4_cm + comps
    outside = (not in_span(base, exc1) and not in_span(base, exc2)
               and in_span(base, PI["0"]) and in_span(base, sumpi))
    for _ in range(4):
        a = [rng.randint(-7, 7) for _ in range(3)]
        if a[0] == a[1] == a[2]:
            a[0] += 1
        om = add(add({m: a[0] * v for m, v in PI["12"].items()},
                     PI["13"], a[1]), PI["23"], a[2])
        outside = outside and not in_span(base, om)
    allpi = [PI[k] for k in ("0", "12", "13", "23")]
    check("pi_12 - pi_13, pi_12 - pi_23 and four random omega_a with a_0 = 0 "
          "lie outside the 110-dimensional span; pi_0 and the sum of the "
          "pi_ij lie inside; the span meets the four pi in a plane",
          outside and span_rank(base + allpi) == 112)

    # ------------------------------------------------------------- (D)
    rm = []
    for _ in range(40):
        vals = [rng.randint(-6, 6) for _ in range(8)]
        phi = [vals[min(i, neg[i])] for i in range(8)]
        ps = [vals[4 + min(i, neg[i])] for i in range(8)]
        rm += [pull(T, phi, ps) for T in tets]
    check("pull-backs of t_{+-} along forty random pairs with "
          "phi_w = phi_{-w}, psi_w = psi_{-w} span, with the divisor "
          "products, all 132 Hodge classes",
          span_rank(deg4_cm + rm) == 132 and in_span(deg4_cm + rm, exc1)
          and in_span(deg4_cm + rm, exc2))

    # ------------------------------------------------------------- (E)
    one = [[1 if i == k else 0 for i in range(28)] for k in range(28)]
    s = [swap_operator(t) for t in range(3)]
    q = sympy.Rational(1, 4)
    ops = {"12": combine([(q, one), (q, s[0]), (q, s[1]), (-q, s[2])]),
           "13": combine([(q, one), (q, s[0]), (-q, s[1]), (q, s[2])]),
           "23": combine([(q, one), (-q, s[0]), (q, s[1]), (q, s[2])]),
           "0": combine([(q, one), (-q, s[0]), (-q, s[1]), (-q, s[2])])}
    # s_1 s_2 s_3 = -1 on wedge^2 V
    prod = combine([(1, s[0])])
    for t in (1, 2):
        prod = [[sum(s[t][j][i] * prod[k][j] for j in range(28))
                 for i in range(28)] for k in range(28)]
    minus_one = all(prod[k][i] == -one[k][i] for k in range(28)
                    for i in range(28))
    same = all(tensor_class(ops[k]) == PI[k] for k in ops)
    check("s_1 s_2 s_3 = -1 on wedge^2 V, and the four pi are the classes "
          "of (1 + s_1 + s_2 - s_3)/4, (1 + s_1 - s_2 + s_3)/4, "
          "(1 - s_1 + s_2 + s_3)/4 and (1 - s_1 - s_2 - s_3)/4",
          minus_one and same)

    # ------------------------------------------------------------- (F)
    def dset(i, j):
        return frozenset(t for t in range(3) if W[i][t] != W[j][t])

    def kind(m):
        c1 = [i for i in range(8) if m >> i & 1]
        c2 = [i for i in range(8) if m >> (i + 8) & 1]
        if len(c1) != 2 or len(c2) != 2:
            return "other"
        if m in tetmonos:
            return "tet"
        i, j = c1
        if neg[i] == j:
            return "pairprod"
        if set(c2) == {neg[i], neg[j]}:
            return "cross"
        return "other"

    def tet_profile(form):
        """For each tetrahedron and each difference set D, the set of
        absolute values of the coefficients on the mixed monomials whose
        copy-1 pair has difference set D."""
        prof = {}
        for ti, T in enumerate(tets):
            for S in itertools.combinations(T, 2):
                m = sum(1 << (i if i in S else i + 8) for i in T)
                D = dset(*S)
                prof.setdefault((ti, D), set()).add(abs(form.get(m, 0)))
        return prof

    def expected(a1, a2, a3):
        e = {frozenset({0, 1}): abs(sympy.Rational(a2 - a3, 2)),
             frozenset({0, 2}): abs(sympy.Rational(a1 - a3, 2)),
             frozenset({1, 2}): abs(sympy.Rational(a1 - a2, 2))}
        return {(ti, D): {e[D]} for ti in range(2) for D in e}

    ok = True
    kinds1 = {}
    for m in exc1:
        kinds1[kind(m)] = kinds1.get(kind(m), 0) + 1
    ok = ok and kinds1 == {"tet": 12, "cross": 16, "pairprod": 8}
    ok = ok and tet_profile(exc1) == expected(1, -1, 0)
    for _ in range(6):
        a = [rng.randint(-9, 9) for _ in range(3)]
        om = add(add({m: a[0] * v for m, v in PI["12"].items()},
                     PI["13"], a[1]), PI["23"], a[2])
        ok = ok and all(kind(m) != "other" for m in om)
        ok = ok and tet_profile(om) == expected(*a)
    ok = ok and not (set(PI["0"]) & tetmonos) and not (set(sumpi) & tetmonos)
    for T in tets:
        c22 = components(T)[2]
        ok = ok and len(c22) == 6 and all(abs(v) == 1 for v in c22.values())
    check("an omega_a with a_0 = 0 is supported on the 12 mixed tetrahedron "
          "monomials and on 24 products of two divisor classes (16 cross, 8 "
          "products of opposite pairs); on each tetrahedron its coefficients "
          "have absolute values |a_2 - a_3|/2, |a_1 - a_3|/2, |a_1 - a_2|/2 "
          "on the pairs with difference sets {1,2}, {1,3}, {2,3}; pi_0 and "
          "the sum of the pi_ij have no tetrahedron monomial; a scalar "
          "(2,2)-component has six coefficients of absolute value one", ok,
          "monomial kinds of pi_12 - pi_13: %s" % sorted(kinds1.items()))


if __name__ == "__main__":
    print("(LXIV) the Weil structure at a CM point and what the cycles on the "
          "square have to use")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
