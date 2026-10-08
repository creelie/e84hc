#!/usr/bin/env python3
"""
mumford_rigidity.py

Item (XLIV) of COMPUTATIONS.md: the exact computations behind the
rigidity of the exceptional classes on the square of a Mumford fourfold, and
behind the numerical form of the semiregularity criterion for them.

Model.  V = V_1 (x) V_2 (x) V_3, V_i = C^2 with basis e_0 (weight +1) and
e_1 (weight -1); a basis vector of V is indexed by (a,b,c) in {0,1}^3 and has
weight (1-2a, 1-2b, 1-2c).  The symplectic form is psi = eps (x) eps (x) eps.
H^1(X x X) = V (+) V, bits 0..7 and 8..15.  At a point of the Mumford curve
the Hodge structure comes from the third factor: V^{1,0} is spanned by the
vectors of third weight +1 and V^{0,1} by those of third weight -1.
wedge^2 V = 1 (+) U_12 (+) U_13 (+) U_23, the pieces cut out by the three
Casimir operators; pi_0, pi_12, pi_13, pi_23 are the corresponding invariant
tensors in wedge^2 V (x) wedge^2 V, inside wedge^4(V (+) V).  The Hodge classes
of Kunneth type (2,2) on X x X are the combinations

      omega_a = a_0 pi_0 + a_1 pi_12 + a_2 pi_13 + a_3 pi_23 ;

a rational one has (a_1, a_2, a_3) the three conjugates of an element alpha of
the totally real cubic field F, pairwise distinct unless alpha is rational,
in which case omega_a is a combination of products of divisor classes.

What is checked:

  (a) the pieces of wedge^2 V have dimensions 1, 9, 9, 9 and the tensors
      pi are invariant;

  (b) the tangent space of the Hodge locus of omega_a in the Siegel space of
      (V (+) V, psi (+) psi), which is the kernel of X -> X.omega_a on
      sp^{-1,1}, splits into nine blocks by the weights of the first two
      factors; the Gram determinant of each block is a positive constant times
      a product of the seven forms
          P1 = a1^2+a2^2+a3^2 - a1a2 - a1a3 - a2a3,
          P2 = a1^2+a2^2+a3^2 + a1a2 + a1a3 + a2a3,
          Q1, Q2, Q3, Q4 (quadratic forms in a0..a3, listed below),
          a2^2 + a3^2 ;
      and the block of weight (0,0) has in addition the one kernel vector of
      the Mumford curve, independent of a;

  (c) each of the seven forms is a sum of squares with the displayed
      rational coefficients, and its real zeros force two of a1, a2, a3 to
      coincide; so for pairwise distinct a1, a2, a3 the tangent space is
      one dimensional, while for a1 = a2 = a3 it has dimension 10 (20 when
      moreover a0 = a1);

  (d) the annihilator of omega_a in HH^2(X x X), of dimension 120, is one
      dimensional for forty random real coefficient vectors with pairwise
      distinct a1, a2, a3, and has dimension 36 for the class with all
      coefficients equal;

  (e) exactly, for every coefficient vector: HH^2 = H^{0,2} + H^1(T) +
      H^0(wedge^2 T) (28 + 64 + 28) splits into 54 blocks by type, by the
      weights of the first two factors and by the parity under the exchange
      of the two factors of X x X, each mapped by contraction into omega_a
      into its own summand; the Gram determinant of every block is a
      positive constant times a product of the forms P1, ..., R above, four
      forms S1, ..., S4, six positive definite forms Z1, ..., Z6, and the
      linear forms a2, a3, L0 = a0+a1+a2+a3, L1, L2, L3; the one block with a
      kernel is the even block of weight (0,0) of H^1(T), and its kernel is
      the derivation of the Mumford curve, for every a;

  (f) certificates: every S and Z is a sum of squares of rational linear
      forms with positive coefficients, the Z with four independent forms;
      the zeros of each S force a_i = a_j or a_i = 0 for some i != j in
      {1,2,3}; the linear forms other than L0 have unequal coefficients on
      a1, a2, a3, so none vanishes at the conjugates of an irrational
      element of a cubic field; and on the hyperplane L0 = 0 the annihilator
      has dimension 10 at sample points, the nine extra directions being
      bivectors.

Run:  python3 mumford_rigidity.py
"""
import random
from collections import defaultdict

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


def build_tensors():
    cas = []
    raise_ops = []
    for t in range(3):
        E = on_wedge2(gen_matrix(t, True))
        F = on_wedge2(gen_matrix(t, False))
        H = on_wedge2(sympy.diag(*[wt(i)[t] for i in range(8)]))
        cas.append(H * H + 2 * (E * F + F * E))
        raise_ops.append(gen_matrix(t, True))
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
    return pieces, PI, raise_ops


def act(M, x):
    """derivation action of a 16 x 16 matrix (list of lists) on a form"""
    out = {}
    for m, c in x.items():
        bits = [i for i in range(NB) if m >> i & 1]
        for k, i in enumerate(bits):
            left = sum(1 << b for b in bits[:k])
            right = sum(1 << b for b in bits[k + 1:])
            for r in range(NB):
                a = M[r][i]
                if a == 0 or ((left | right) >> r & 1):
                    continue
                s = mono_sign(left, 1 << r) * mono_sign(left | (1 << r), right)
                new = left | (1 << r) | right
                out[new] = out.get(new, 0) + s * a * c
    return {k: v for k, v in out.items() if v != 0}


a0, a1, a2, a3 = sympy.symbols("a0 a1 a2 a3")
AS = {"0": a0, "12": a1, "13": a2, "23": a3}

P1 = a1**2 + a2**2 + a3**2 - a1*a2 - a1*a3 - a2*a3
P2 = a1**2 + a2**2 + a3**2 + a1*a2 + a1*a3 + a2*a3
Q1 = (3*a0**2 - 2*a0*a1 - 2*a0*a2 - 2*a0*a3 + 11*a1**2 - 10*a1*a2
      - 10*a1*a3 + 11*a2**2 - 10*a2*a3 + 11*a3**2)
Q2 = (3*a0**2 + 6*a0*a1 - 2*a0*a2 + 6*a0*a3 + 51*a1**2 + 30*a1*a2
      + 6*a1*a3 + 11*a2**2 + 30*a2*a3 + 51*a3**2)
Q3 = (3*a0**2 + 6*a0*a1 + 6*a0*a2 - 2*a0*a3 + 51*a1**2 + 6*a1*a2
      + 30*a1*a3 + 51*a2**2 + 30*a2*a3 + 11*a3**2)
Q4 = (a0**2 - 6*a0*a1 + 2*a0*a2 + 2*a0*a3 + 9*a1**2 - 6*a1*a2 - 6*a1*a3
      + 17*a2**2 - 30*a2*a3 + 17*a3**2)
R = a2**2 + a3**2
FORMS = [P1, P2, Q1, Q2, Q3, Q4, R]

# sums of squares with integer coefficients after clearing denominators
SOS = [
    (2 * P1, [(1, a1 - a2), (1, a1 - a3), (1, a2 - a3)]),
    (2 * P2, [(1, a1 + a2), (1, a1 + a3), (1, a2 + a3)]),
    (33 * Q1, [(3, 11*a1 - a0 - 5*a2 - 5*a3), (8, 6*a2 - a0 - 5*a3),
               (88, a3 - a0)]),
    (119 * Q2, [(21, 17*a1 + a0 + 5*a2 + a3), (16, 7*a2 - 2*a0 + 15*a3),
                (272, 3*a3 + a0)]),
    (51 * Q3, [(9, 17*a1 + a0 + a2 + 5*a3), (8, 18*a2 + a0 + 5*a3),
               (136, a3 - a0)]),
    (Q4, [(1, 3*a1 - a0 - a2 - a3), (16, a2 - a3)]),
    (R, [(1, a2), (1, a3)]),
]


def run():
    pieces, PI, raise_ops = build_tensors()
    dims = {k: len(v) for k, v in pieces.items()}
    inv_ok = True
    for t in range(3):
        R3 = raise_ops[t]
        M16 = [[0] * NB for _ in range(NB)]
        for r in range(8):
            for i in range(8):
                M16[r][i] = R3[r, i]
                M16[r + 8][i + 8] = R3[r, i]
        for key in PI:
            if act(M16, PI[key]):
                inv_ok = False
    check("wedge^2 V splits as 1 + 9 + 9 + 9 and the four tensors pi are "
          "invariant", dims == {"0": 1, "12": 9, "13": 9, "23": 9} and inv_ok,
          "dimensions %s" % dims)

    # sp^{-1,1}, split by the weights of the first two factors
    Psi = sympy.Matrix(NB, NB, lambda i, j: psi(i, j))
    unk = [(r, i) for r in range(NB) if wt(r)[2] == -1
           for i in range(NB) if wt(i)[2] == 1]
    groups = defaultdict(list)
    for (r, i) in unk:
        groups[(wt(r)[0] - wt(i)[0], wt(r)[1] - wt(i)[1])].append((r, i))
    total = 0
    bdims = {}
    factors_ok = True
    kernel_ok = True
    blocks = {}
    for mu, us in sorted(groups.items()):
        zs = sympy.symbols("z0:%d" % len(us))
        Xb = sympy.zeros(NB, NB)
        for z, (r, i) in zip(zs, us):
            Xb[r, i] = z
        cons = [c for c in list(Xb.T * Psi + Psi * Xb) if c != 0]
        if cons:
            A = sympy.Matrix([[sympy.diff(c, z) for z in zs] for c in cons])
            nb = A.nullspace()
        else:
            nb = [sympy.eye(len(us))[:, k] for k in range(len(us))]
        total += len(nb)
        bdims[mu] = len(nb)
        cols = []
        for v in nb:
            M = [[0] * NB for _ in range(NB)]
            for c, (r, i) in zip(v, us):
                M[r][i] = c
            img = {}
            for key, s in AS.items():
                for mm, c in act(M, PI[key]).items():
                    img[mm] = img.get(mm, 0) + s * c
            cols.append({k: sympy.expand(x) for k, x in img.items()
                         if sympy.expand(x) != 0})
        keys = sorted({k for c in cols for k in c})
        Mb = sympy.Matrix([[c.get(k, 0) for c in cols] for k in keys])
        Mg = Mb.subs({a0: 3, a1: 5, a2: -7, a3: 11})
        ker = Mg.nullspace()
        if ker:
            if mu != (0, 0) or len(ker) != 1:
                kernel_ok = False
            kv = ker[0]
            if any(sympy.expand(e) != 0 for e in Mb * kv):
                kernel_ok = False
            drop = [j for j in range(len(cols)) if kv[j] != 0][0]
            keep = [j for j in range(len(cols)) if j != drop]
            Mb = Mb.extract(list(range(Mb.shape[0])), keep)
        det = sympy.factor((Mb.T * Mb).det())
        const, flist = sympy.factor_list(det)
        ok = const > 0 and all(
            any(sympy.expand(f - g) == 0 or sympy.expand(f + g) == 0
                for g in FORMS) for f, e in flist)
        factors_ok = factors_ok and ok
        blocks[mu] = [str(f) for f, e in flist]
    check("sp^{-1,1} has dimension 36, split into nine weight blocks",
          total == 36, "block dimensions %s" % bdims)
    check("the generic kernel is one vector, in the block of weight (0,0), "
          "and it does not depend on a", kernel_ok,
          "the tangent direction of the Mumford curve")
    check("every Gram determinant is a positive constant times a product of "
          "P1, P2, Q1, Q2, Q3, Q4 and a2^2 + a3^2", factors_ok)

    sos_ok = all(sympy.expand(lhs - sum(c * l**2 for c, l in terms)) == 0
                 and all(c > 0 for c, _ in terms) for lhs, terms in SOS)
    check("each of the seven forms is a sum of squares of rational linear forms "
          "with positive coefficients", sos_ok)

    # the real zeros of each form force two of a1, a2, a3 to coincide
    zero_ok = True
    for lhs, terms in SOS:
        sol = sympy.solve([l for _, l in terms], [a0, a1, a2, a3], dict=True)
        for s in sol:
            vals = [sympy.simplify(x.subs(s)) for x in (a1, a2, a3)]
            if not (sympy.simplify(vals[0] - vals[1]) == 0
                    or sympy.simplify(vals[0] - vals[2]) == 0
                    or sympy.simplify(vals[1] - vals[2]) == 0):
                zero_ok = False
    check("the common zeros of the squared linear forms of each form have two "
          "of a1, a2, a3 equal", zero_ok,
          "so for pairwise distinct a1, a2, a3 every block has full rank and "
          "the tangent space is one dimensional")

    # direct confirmation of the tangent dimensions at sample points
    allcols = []
    zs = sympy.symbols("y0:%d" % len(unk))
    Xs = sympy.zeros(NB, NB)
    for z, (r, i) in zip(zs, unk):
        Xs[r, i] = z
    cons = [c for c in list(Xs.T * Psi + Psi * Xs) if c != 0]
    A = sympy.Matrix([[sympy.diff(c, z) for z in zs] for c in cons])
    for v in A.nullspace():
        M = [[0] * NB for _ in range(NB)]
        for c, (r, i) in zip(v, unk):
            M[r][i] = c
        allcols.append(M)

    def tangent(vals):
        om = {}
        for key, c in zip(("0", "12", "13", "23"), vals):
            for m, x in PI[key].items():
                om[m] = om.get(m, 0) + c * x
        om = {k: x for k, x in om.items() if x != 0}
        cols = [act(M, om) for M in allcols]
        keys = sorted({k for c in cols for k in c})
        Mx = sympy.Matrix([[c.get(k, 0) for c in cols] for k in keys])
        return len(allcols) - Mx.rank()
    t_gen = tangent((3, 5, -7, 11))
    t_eq = tangent((3, 5, 5, 5))
    t_all = tangent((5, 5, 5, 5))
    check("tangent dimensions: 1 for distinct coefficients, 10 for "
          "a1 = a2 = a3, 20 for a0 = a1 = a2 = a3", (t_gen, t_eq, t_all)
          == (1, 10, 20), "computed %d, %d, %d" % (t_gen, t_eq, t_all))

    # (d) the annihilator in HH^2
    hol = [i for i in range(NB) if wt(i)[2] == 1]
    anti = [i for i in range(NB) if wt(i)[2] == -1]
    gens = [("w", i) for i in anti] + [("c", i) for i in hol]

    def apply(g, x):
        kind, i = g
        out = {}
        for m, c in x.items():
            if kind == "w":
                if m >> i & 1:
                    continue
                s = mono_sign(1 << i, m)
                out[m | (1 << i)] = out.get(m | (1 << i), 0) + s * c
            else:
                if not (m >> i & 1):
                    continue
                s = (-1) ** popcount(m & ((1 << i) - 1))
                out[m ^ (1 << i)] = out.get(m ^ (1 << i), 0) + s * c
        return {k: v for k, v in out.items() if v != 0}

    pairs2 = [(p, q) for p in range(len(gens)) for q in range(p + 1, len(gens))]
    pre = {key: [apply(gens[p], apply(gens[q], PI[key])) for (p, q) in pairs2]
           for key in PI}

    def ann(vals):
        cols = []
        for j in range(len(pairs2)):
            c = {}
            for key, s in zip(("0", "12", "13", "23"), vals):
                for m, x in pre[key][j].items():
                    c[m] = c.get(m, 0) + s * x
            cols.append({k: x for k, x in c.items() if x != 0})
        keys = sorted({k for c in cols for k in c})
        Mx = sympy.Matrix([[c.get(k, 0) for c in cols] for k in keys])
        return len(pairs2) - Mx.rank()
    def admissible(v):
        # pairwise distinct, none zero, and no relation a_k = a_i + a_j: no
        # nonzero element of a cubic field satisfies such a relation among
        # its conjugates
        x = v[1:]
        if len(set(x)) < 3 or 0 in x:
            return False
        for i in range(3):
            for j in range(3):
                for k in range(3):
                    if len({i, j, k}) == 3 and x[k] == x[i] + x[j]:
                        return False
        return True
    random.seed(20260924)
    sizes = []
    while len(sizes) < 40:
        vals = [random.randint(-30, 30) for _ in range(4)]
        if admissible(vals):
            sizes.append(ann(vals))
    a_eq = ann((1, 1, 1, 1))
    check("the annihilator in HH^2 (dimension 120) of an exceptional class is "
          "one dimensional at forty random admissible points, and 36 "
          "dimensional for the class with equal coefficients",
          set(sizes) == {1} and a_eq == 36 and len(pairs2) == 120,
          "so on a nonempty Zariski open set of classes, which contains "
          "rational ones, the least dimension of Ext^2 is 119")
    j1, j2 = ann((3, 5, 0, 11)), ann((28, 4, 10, 14))
    check("the annihilator does jump on special loci, which contain no "
          "rational exceptional class", j1 == 7 and j2 == 4,
          "dimension %d at a2 = 0 and %d on the hyperplane "
          "a0 - 3 a1 - 3 a2 + a3 = 0" % (j1, j2))

    # (e) the exact annihilator in HH^2, block by block
    def gwt(g):
        kind, i = g
        w = wt(i)
        return w if kind == "w" else tuple(-x for x in w)

    gidx = {g: k for k, g in enumerate(gens)}

    def sw(i):
        return i + 8 if i < 8 else i - 8

    def swap_pair(pq):
        p, q = pq
        gp, gq = gens[p], gens[q]
        p2 = gidx[(gp[0], sw(gp[1]))]
        q2 = gidx[(gq[0], sw(gq[1]))]
        return ((p2, q2), 1) if p2 < q2 else ((q2, p2), -1)

    def swap_form(x):
        out = {}
        for m, c in x.items():
            nb = [sw(i) for i in range(NB) if m >> i & 1]
            sgn, arr = 1, nb[:]
            for i in range(len(arr)):
                for j in range(len(arr) - 1 - i):
                    if arr[j] > arr[j + 1]:
                        arr[j], arr[j + 1] = arr[j + 1], arr[j]
                        sgn = -sgn
            mm = sum(1 << b for b in nb)
            out[mm] = out.get(mm, 0) + sgn * c
        return {k: v for k, v in out.items() if v != 0}

    swap_ok = all(swap_form(PI[k]) == PI[k] for k in PI)
    pre_all = {}
    for pq in pairs2:
        c = {}
        for key, s_ in AS.items():
            for mm, x in pre[key][pairs2.index(pq)].items():
                c[mm] = c.get(mm, 0) + s_ * x
        pre_all[pq] = {k: sympy.expand(x) for k, x in c.items()
                       if sympy.expand(x) != 0}
    TYPE = {"ww": "z", "wc": "v", "cw": "v", "cc": "pi"}
    raw = defaultdict(list)
    for (p, q) in pairs2:
        w1, w2 = gwt(gens[p]), gwt(gens[q])
        raw[(TYPE[gens[p][0] + gens[q][0]],
             (w1[0] + w2[0], w1[1] + w2[1]))].append((p, q))
    S1 = (a0 - a2)**2 + 3*(a1 - a3)**2
    S2 = (a0 + a2)**2 + 3*(a1 + a3)**2 + 8*a2**2
    S3 = (a0 - a3)**2 + 3*(a1 - a2)**2
    S4 = (a0 + a3)**2 + 3*(a1 + a2)**2 + 8*a3**2
    Z = [
        (9*a0**2 + 2*a0*a1 + 2*a0*a2 + 2*a0*a3 + 73*a1**2 + 2*a1*a2
         + 2*a1*a3 + 73*a2**2 + 2*a2*a3 + 73*a3**2,
         [(9, a0 + a1/9 + a2/9 + a3/9),
          (sympy.Rational(656, 9), a1 + a2/82 + a3/82),
          (sympy.Rational(2988, 41), a2 + a3/83),
          (sympy.Rational(6048, 83), a3)]),
        (9*a0**2 - 6*a0*a1 + 2*a0*a2 - 6*a0*a3 + 81*a1**2 - 6*a1*a2
         + 18*a1*a3 + 73*a2**2 - 6*a2*a3 + 81*a3**2,
         [(9, a0 - a1/3 + a2/9 - a3/3), (80, a1 - a2/30 + a3/10),
          (sympy.Rational(364, 5), a2 - 3*a3/91),
          (sympy.Rational(7200, 91), a3)]),
        (9*a0**2 - 6*a0*a1 - 6*a0*a2 + 2*a0*a3 + 81*a1**2 + 18*a1*a2
         - 6*a1*a3 + 81*a2**2 - 6*a2*a3 + 73*a3**2,
         [(9, a0 - a1/3 - a2/3 + a3/9), (80, a1 + a2/10 - a3/30),
          (sympy.Rational(396, 5), a2 - a3/33),
          (sympy.Rational(800, 11), a3)]),
        (a0**2 + 9*a1**2 + 11*a2**2 + 9*a3**2,
         [(1, a0), (9, a1), (11, a2), (9, a3)]),
        (a0**2 + 9*a1**2 + 9*a2**2 + 11*a3**2,
         [(1, a0), (9, a1), (9, a2), (11, a3)]),
        (3*a0**2 + 6*a0*a1 - 2*a0*a2 - 2*a0*a3 + 51*a1**2 - 18*a1*a2
         - 18*a1*a3 + 27*a2**2 + 6*a2*a3 + 27*a3**2,
         [(3, a0 + a1 - a2/3 - a3/3), (48, a1 - a2/6 - a3/6),
          (sympy.Rational(76, 3), a2 + a3/19),
          (sympy.Rational(480, 19), a3)]),
    ]
    L0 = a0 + a1 + a2 + a3
    LIN = [a2, a3, L0, a0 - 3*a1 + a2 - 3*a3, a0 - 3*a1 - 3*a2 + a3,
           a0 + 9*a1 - 3*a2 - 3*a3]
    ALL = FORMS + [sympy.expand(f) for f in (S1, S2, S3, S4)] + \
        [sympy.expand(z) for z, _ in Z] + LIN
    # the derivation of the Mumford curve: the lowering operator of the
    # third factor, on both copies of V, as an element of H^0,1 (x) T
    D = {}
    for i in range(NB):
        if wt(i)[2] == 1:
            D[(gidx[("w", i + 1)], gidx[("c", i)])] = 1
    total, kinds, kernel_blocks, facs_ok = 0, defaultdict(int), [], True
    curve_ok, special = False, []
    for key, prs in sorted(raw.items()):
        for par in (1, -1):
            vecs, seen = [], set()
            for pq in prs:
                if pq in seen:
                    continue
                spq, sg = swap_pair(pq)
                seen.update((pq, spq))
                if spq == pq:
                    if sg * par == 1:
                        vecs.append({pq: 1})
                    continue
                vecs.append({pq: 1, spq: sg * par})
            if not vecs:
                continue
            total += len(vecs)
            kinds[key[0]] += len(vecs)
            cols = []
            for v in vecs:
                c = {}
                for pq, co in v.items():
                    for mm, x in pre_all[pq].items():
                        c[mm] = c.get(mm, 0) + co * x
                cols.append({mm: sympy.expand(x) for mm, x in c.items()
                             if sympy.expand(x) != 0})
            keys = sorted({mm for c in cols for mm in c})
            Mb = sympy.Matrix([[c.get(mm, 0) for c in cols] for mm in keys])
            ker = Mb.subs({a0: 3, a1: 5, a2: -7, a3: 11}).nullspace()
            if ker:
                kernel_blocks.append((key, par, len(ker)))
                kv = ker[0]
                if all(sympy.expand(e) == 0 for e in Mb * kv):
                    # compare with the curve derivation
                    dv = sympy.Matrix([sum(D.get(pq, 0) * co
                                           for pq, co in v.items())
                                       for v in vecs])
                    curve_ok = (sympy.Matrix.hstack(kv, dv).rank() == 1
                                and any(dv))
                drop = [j for j in range(len(cols)) if kv[j] != 0][0]
                Mb = Mb.extract(list(range(Mb.shape[0])),
                                [j for j in range(len(cols)) if j != drop])
            det = sympy.factor((Mb.T * Mb).det(method="berkowitz"))
            const, flist = sympy.factor_list(det)
            ok = const > 0 and all(
                any(sympy.expand(f - g) == 0 or sympy.expand(f + g) == 0
                    for g in ALL) for f, e in flist)
            facs_ok = facs_ok and ok
            if any(sympy.expand(f - L0) == 0 or sympy.expand(f + L0) == 0
                   for f, e in flist):
                special.append((key, par))
    check("HH^2 = H^{0,2} + H^1(T) + H^0(wedge^2 T) splits into blocks by "
          "type, weight and exchange parity, and omega_a is exchange "
          "invariant", total == 120 and dict(kinds) == {"z": 28, "v": 64,
                                                       "pi": 28} and swap_ok,
          "dimensions %s" % dict(kinds))
    check("every block Gram determinant is a positive constant times a "
          "product of P1, P2, Q1..Q4, R, S1..S4, Z1..Z6, a2, a3, L0, L1, L2, "
          "L3", facs_ok)
    check("the only block with a kernel at a generic point is the exchange "
          "even block of weight (0,0) of H^1(T), its kernel is independent of "
          "a and is the derivation of the Mumford curve",
          kernel_blocks == [(("v", (0, 0)), 1, 1)] and curve_ok)
    check("L0 = a0 + a1 + a2 + a3 divides only the Gram determinants of the "
          "exchange odd blocks of bivectors", all(k[0] == "pi" and p == -1
                                                   for k, p in special)
          and len(special) == 9, "%d blocks" % len(special))
    # (f) certificates
    cert_ok = True
    for f, terms in [(S1, [(1, a0 - a2), (3, a1 - a3)]),
                     (S2, [(1, a0 + a2), (3, a1 + a3), (8, a2)]),
                     (S3, [(1, a0 - a3), (3, a1 - a2)]),
                     (S4, [(1, a0 + a3), (3, a1 + a2), (8, a3)])]:
        if sympy.expand(f - sum(c * l**2 for c, l in terms)) != 0:
            cert_ok = False
        for sol in sympy.solve([l for _, l in terms], [a0, a1, a2, a3],
                               dict=True):
            v = [sympy.simplify(x.subs(sol)) for x in (a1, a2, a3)]
            if not (any(sympy.simplify(v[i] - v[j]) == 0
                        for i in range(3) for j in range(i + 1, 3))
                    or any(x == 0 for x in v)):
                cert_ok = False
    pd_ok = True
    for f, terms in Z:
        if sympy.expand(f - sum(c * l**2 for c, l in terms)) != 0:
            pd_ok = False
        if not all(c > 0 for c, _ in terms):
            pd_ok = False
        J = sympy.Matrix([[sympy.diff(l, x) for x in (a0, a1, a2, a3)]
                          for _, l in terms])
        if J.rank() != 4:
            pd_ok = False
    lin_ok = all(len({sympy.diff(l, x) for x in (a1, a2, a3)}) > 1
                 for l in LIN if sympy.expand(l - L0) != 0)
    check("S1..S4 are sums of squares whose zeros force two of a1, a2, a3 to "
          "coincide or one to vanish; Z1..Z6 are positive definite, as sums "
          "of four squares of independent forms with positive coefficients",
          cert_ok and pd_ok)
    check("every linear factor other than L0 has unequal coefficients on "
          "a1, a2, a3", lin_ok,
          "so it does not vanish at the conjugates of an irrational element "
          "of a cubic field, whatever the rational a0")
    s0 = [ann(v) for v in ((3, 1, 3, -7), (0, 1, 3, -4), (-6, 1, 7, -2))]
    check("on the hyperplane L0 = 0 the annihilator has dimension 10",
          s0 == [10, 10, 10], "at three sample points: %s" % s0)


if __name__ == "__main__":
    print("(XLIV) the exceptional classes of a Mumford square are rigid")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
