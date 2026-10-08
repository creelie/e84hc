#!/usr/bin/env python3
"""
quartic_rank.py

Item (LXV) of the computations: the exact rank of the contraction
HT^2(A) -> H^*(A,C), xi -> xi _| gamma, for gamma = omega + p(theta_1,theta_2)
on a member A of a quartic CM family at n = 2.

Model.  As in item (LV), track T1: H^1(A,C) has basis a_{s,k} (type (1,0))
and b_{s,k} (type (0,1)), s = 0,1,2,3 the embeddings, k = 0,1, with s and
s+1 conjugate over the real place tau_1 for s = 0 and over tau_2 for s = 2.
alpha_s = a_{s,0} a_{s,1} b_{s,0} b_{s,1},
theta_1 = sum_k (a_{0,k} b_{1,k} + a_{1,k} b_{0,k}), theta_2 likewise with
s = 2,3, and omega = sum_s u_s alpha_s, with u_s = 1 unless stated.
p = sum_{i,j <= 4} e_{ij} theta_1^i theta_2^j / (i! j!), so that e_{ij} is
the (i,j)-th derivative of p at 0.  HT^2 = wedge^2 H^{0,1} + H^{0,1} (x) T +
wedge^2 T acts by wedge with the b's and contraction with the duals of the
a's.

Put mu(p) = 0 if d_1 d_2 p = 0 and 1 otherwise; rho_1(p) the dimension of
the span of d_1 p and d_1^2 p modulo theta_1^3 (the rank of the 2 x 15
matrix of the pairs (e_{i,j}, e_{i+1,j}), 1 <= i <= 3); rho_2(p) likewise.

What is checked:

  (A) the torus S of the basis that fixes theta_1, theta_2 and the four
      alpha_s has dimension 6; it splits the 120 basis operators of HT^2
      into 34 weight spaces, eight of dimension 1, twenty-four of dimension
      4 (sixteen mixing tau_1 and tau_2, eight not) and two of dimension 8,
      and the images of different weight spaces lie in disjoint sets of
      monomials, so the rank is the sum of the ranks of the 34 blocks;

  (B) each block of dimension 1 kills every theta_1^i theta_2^j and not
      omega: rank 1;

  (C) each of the sixteen mixed blocks has three columns free of p that
      span the first three coordinates, and the last coordinates of the
      other columns are, up to sign, exactly the sixteen e_{ij} with
      i, j >= 1: rank 3 + mu(p);

  (D) each of the eight unmixed blocks of dimension 4 has a column free of
      p along the first coordinate, its second and third rows are opposite,
      and its (second, fourth) coordinates are, after one global sign, the
      pairs +-(e_{i,j}, e_{i+1,j}) (tau_1) or +-(e_{i,j}, e_{i,j+1}) (tau_2):
      rank 1 + rho_1(p) or 1 + rho_2(p);

  (E) in each block of dimension 8 the columns that do not vanish at p = 0
      involve only e_{10}, ..., e_{40} (resp. e_{01}, ..., e_{04}); two of
      them are the first two unit vectors, and on the other six coordinates
      the remaining eight form a 6 x 8 matrix N whose 5 x 5 minors generate
      the unit ideal (so R >= 7), whose 6 x 6 minors vanish exactly on
      V_+ u V_-, V_+- = {h_3 = +-e_3, 2h_2 = +-e_4, 2h_1 + 1 = +-e_2},
      h_1 = e_1 e_3 - e_2^2, h_2 = e_2 e_4 - e_3^2, h_3 = e_1 e_4 - e_2 e_3,
      and together with the 2 x 2 minors of the Hankel matrix
      [[e_1, e_2, e_3], [e_2, e_3, e_4]] generate the unit ideal (so R = 7
      forces rho = 2); after the row changes r3 + r4, r5 + r6 the block is
      two unit columns, two columns reaching the new rows, and the 4 x 30
      matrix K = (K^0 | diag(H, H)) of the paper; and the hand reduction of
      the proof holds: the six columns of K^0 have rank 2 + rank Q, the
      entries of Q generate the unit ideal, its 2 x 2 minors lie in the
      ideals of V_+ and V_-, the squares of the products of their generators
      lie in the ideal of the minors, and the minors with the Hankel minors
      generate the unit ideal;

  (F) r(omega + p) = 64 + 16 mu + 4 rho_1 + 4 rho_2 + R_1 + R_2 at forty
      random p and at the fifteen explicit p below, the rank computed on all
      120 operators at once;

  (G) the fifteen explicit p realise the values 80, 84, 87, 88, 91, 92, 94,
      95, 96, 104, 107, 108, 110, 111, 112, and the tuples allowed by
      (B)-(E) (mu = 1 forces rho_1, rho_2 >= 1; R_t = 7 forces rho_t = 2)
      give exactly these fifteen values; the least is 80, only at mu = 0,
      rho_1 = rho_2 = 0, R_1 = R_2 = 8, that is, for p constant, and 100 is
      not a value;

  (H) for omega = 4 alpha_0 + alpha_1 + alpha_2 + alpha_3 the exceptional
      coefficients of theta_1^2 / 2 move with the torus of the proof,
      e_{20} -> e_{20} kappa^2, kappa^4 = 1/(u_0 u_1): r = 87 at e_{20} = 2
      and r = 88 at e_{20} = 3;

  (I) for the Kaehler class kappa_0 = theta_1 + theta_2 of the Weil tori of
      the field: int alpha_s kappa_0^6 = 0, int alpha_s alpha_r alpha_q
      kappa_0^2 = 0, and int alpha_s alpha_r kappa_0^4 is nonzero exactly
      when r is conjugate to s, the facts used for the subvarieties of the
      Weil tori in the proof that the pure form is never met.

  (J) theta_1^4 and theta_2^4 are nonzero multiples of alpha_0 alpha_1 and
      alpha_2 alpha_3, so a polynomial in the theta_1^i theta_2^j with
      i, j in {0, 4} stays of Hodge type on every Weil torus of the field,
      while theta_1, theta_1^2, theta_1^3 are not such multiples; and
      r(omega + theta_1^4/24 + theta_2^4/24) = 88 (mu = 0, rho = 1, 1),
      r = 104 with theta_1^4 theta_2^4 / 576 added: the characters at the
      values 88 and 104 that the Weil tori exclude.

  (K) the first order deformations of A that keep gamma of Hodge type: on
      the 64 operators of H^1(T_A) = H^{0,1} (x) T the kernel of
      xi -> xi _| (omega + p) consists of F-linear operators (those between
      V_s^{1,0} and V_s^{0,1}), and it is the space of F-linear xi with
      xi _| theta_t = 0 at every place t at which p has a monomial whose
      exponent of theta_t is 1, 2 or 3; so its dimension is 8 + 4 (number
      of places without such a monomial), for the nine patterns of
      exponents and two choices of omega; the characters left at 88
      (linear or exponential in each theta_t) and a quadratic one give 8,
      the tangent space of the polarised family, and the constant and the
      theta^4 shapes give 16, all F-linear deformations.

  (L) the exceptional places: a place t at which p has a monomial with
      theta_t-exponent 1, 2 or 3 adds one first order deformation that is
      not F-linear exactly when the only such monomial is c_t theta_t^2 and
      16 c_t^2 = u_s u_s' (s, s' over tau_t), that is c_t^2 theta_t^4 =
      (3/4) omega_t^2 with theta_t^4 = 24 alpha_s alpha_s' and omega_t^2 =
      2 u_s u_s' alpha_s alpha_s'; the rational shapes exceptional at both
      places have rank 94 or 110 and annihilator of dimension 10 in
      H^1(T_A); the stabiliser of omega_t + c_t theta_t^2 in gl(V_s + V_s')
      is so(4,3) (dimension 21, orbit of dimension 5, trace form of signature
      (12, 9)) at the exceptional value and su(2,2) (15, 4, (8, 7)) at an
      ordinary one; along the locus no class of degree two and exactly the
      span of the two classes X_t = omega_t + c_t theta_t^2 of degree four
      stay of Hodge type; and int X_1 kappa^6 has the constant sign of -c_1
      (theta_t here is sqrt(-1) times a real class) on the Kaehler classes of
      six positive hermitian forms on the whole tangent space, with Gaussian
      rational entries, while both signs occur at c = 1/10.

Everything is exact rational arithmetic, with Groebner bases over Q.

Run:  python3 quartic_rank.py
"""
import itertools
import random
from fractions import Fraction as Fr
from math import factorial

import sympy

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ------------------------------------------------------ exterior algebra
NG = 16


def gen(s, kind, k):
    """kind 0: a_{s,k} of type (1,0); kind 1: b_{s,k} of type (0,1)"""
    return 4 * s + 2 * kind + k


A_GENS = [gen(s, 0, k) for s in range(4) for k in range(2)]
B_GENS = [gen(s, 1, k) for s in range(4) for k in range(2)]


def below(mask, g):
    return bin(mask & ((1 << g) - 1)).count("1")


def wedge_gen(mask, g):
    if mask >> g & 1:
        return 0, None
    return (-1) ** below(mask, g), mask | (1 << g)


def contract_gen(mask, g):
    if not mask >> g & 1:
        return 0, None
    return (-1) ** below(mask, g), mask & ~(1 << g)


def wedge(f, h):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in h.items():
            if m1 & m2:
                continue
            sgn = 1
            mm = m2
            for i in range(NG):
                if m1 >> i & 1:
                    sgn *= (-1) ** below(mm, i)
            out[m1 | m2] = out.get(m1 | m2, 0) + sgn * c1 * c2
    return {m: c for m, c in out.items() if c != 0}


def mono(gs):
    f = {0: 1}
    for g in gs:
        f = wedge(f, {1 << g: 1})
    return f


def addf(f, h, c=1):
    out = dict(f)
    for m, v in h.items():
        out[m] = out.get(m, 0) + c * v
    return {m: v for m, v in out.items() if v != 0}


def theta(t):
    s0, s1 = 2 * t, 2 * t + 1
    f = {}
    for k in range(2):
        f = addf(f, mono([gen(s0, 0, k), gen(s1, 1, k)]))
        f = addf(f, mono([gen(s1, 0, k), gen(s0, 1, k)]))
    return f


def alpha(s):
    return mono([gen(s, 0, 0), gen(s, 0, 1), gen(s, 1, 0), gen(s, 1, 1)])


def powf(f, n):
    out = {0: 1}
    for _ in range(n):
        out = wedge(out, f)
    return out


TH = [theta(0), theta(1)]
IJ = [(i, j) for i in range(5) for j in range(5)]
# theta_1^i theta_2^j / (i! j!)
THP = {}
for (i, j) in IJ:
    f = wedge(powf(TH[0], i), powf(TH[1], j))
    THP[(i, j)] = {m: Fr(c, factorial(i) * factorial(j)) for m, c in f.items()}


def omega(u=(1, 1, 1, 1)):
    f = {}
    for s in range(4):
        f = addf(f, alpha(s), u[s])
    return f


# ------------------------------------------------------ the operators of HT^2
OPS = []
for x, y in itertools.combinations(B_GENS, 2):
    OPS.append((("z", x, y), [("w", y), ("w", x)]))
for x in B_GENS:
    for y in A_GENS:
        OPS.append((("v", x, y), [("c", y), ("w", x)]))
for x, y in itertools.combinations(A_GENS, 2):
    OPS.append((("pi", x, y), [("c", y), ("c", x)]))


def apply_op(op, f):
    out = {}
    for m, c in f.items():
        sgn, mm = 1, m
        ok = True
        for kind, g in op[1]:
            s, mm = (wedge_gen if kind == "w" else contract_gen)(mm, g)
            if not s:
                ok = False
                break
            sgn *= s
        if ok:
            out[mm] = out.get(mm, 0) + sgn * c
    return {m: c for m, c in out.items() if c != 0}


def op_char(op):
    v = [0] * NG
    for kind, g in op[1]:
        v[g] += 1 if kind == "w" else -1
    return v


# the torus S: characters of monomials of theta_t and alpha_s are trivial on S
Lrows = []
for f in TH + [alpha(s) for s in range(4)]:
    for m in f:
        Lrows.append([m >> i & 1 for i in range(NG)])
PROJ = sympy.Matrix.hstack(*sympy.Matrix(Lrows).nullspace()).T


def s_char(v):
    return tuple(PROJ * sympy.Matrix(v))


BLOCKS = {}
for idx, op in enumerate(OPS):
    BLOCKS.setdefault(s_char(op_char(op)), []).append(idx)
BLOCKS = list(BLOCKS.values())

# ------------------------------------------------------ symbolic block matrices
E = {ij: sympy.Symbol("e%d%d" % ij) for ij in IJ}
IMG_OMEGA = {}
IMG_TH = {}
for idx, op in enumerate(OPS):
    IMG_OMEGA[idx] = apply_op(op, omega())
    for ij in IJ:
        IMG_TH[(idx, ij)] = apply_op(op, THP[ij])


def block_matrix(ops, u=(1, 1, 1, 1)):
    """rows: operators; columns: image monomials; entries linear in the e's"""
    om = omega(u)
    cols = {}
    for r, i in enumerate(ops):
        for m, c in apply_op(OPS[i], om).items():
            cols.setdefault(m, [0] * len(ops))[r] += sympy.Rational(c)
        for ij in IJ:
            for m, c in IMG_TH[(i, ij)].items():
                cols.setdefault(m, [0] * len(ops))[r] += \
                    sympy.Rational(c.numerator, c.denominator) * E[ij]
    keys = sorted(cols)
    return sympy.Matrix([[sympy.expand(cols[m][r]) for m in keys]
                         for r in range(len(ops))])


def kind_of(ops):
    names = [OPS[i][0] for i in ops]
    if len(ops) == 1:
        return "one"
    if len(ops) == 8:
        return "eight"
    z = [n for n in names if n[0] == "z"][0]
    t1 = (z[1] // 4) // 2
    t2 = (z[2] // 4) // 2
    return "mixed" if t1 != t2 else "unmixed%d" % (t1 + 1)


def tau_of_eight(ops):
    z = [OPS[i][0] for i in ops if OPS[i][0][0] == "z"][0]
    return (z[1] // 4) // 2 + 1


# ------------------------------------------------------ sparse exact rank
def sparse_rank(vectors):
    pivots = {}
    rank = 0
    for v in vectors:
        v = {k: Fr(c) for k, c in v.items() if c != 0}
        while v:
            k = min(v)
            if k in pivots:
                pv = pivots[k]
                f = v[k] / pv[k]
                for kk, cc in pv.items():
                    nv = v.get(kk, 0) - f * cc
                    if nv == 0:
                        v.pop(kk, None)
                    else:
                        v[kk] = nv
            else:
                pivots[k] = v
                rank += 1
                break
    return rank


def gamma_form(e, u=(1, 1, 1, 1)):
    g = {m: Fr(c) for m, c in omega(u).items()}
    for ij, c in e.items():
        if c:
            g = addf(g, THP[ij], Fr(c))
    return g


def direct_rank(e, u=(1, 1, 1, 1)):
    g = gamma_form(e, u)
    return sparse_rank([apply_op(op, g) for op in OPS])


# ------------------------------------------------------ the invariants
def mu(e):
    return int(any(e.get((i, j), 0) != 0 for i in range(1, 5)
                   for j in range(1, 5)))


def rho(e, t):
    cols = []
    for i in range(1, 4):
        for j in range(5):
            if t == 1:
                cols.append((e.get((i, j), 0), e.get((i + 1, j), 0)))
            else:
                cols.append((e.get((j, i), 0), e.get((j, i + 1), 0)))
    return sympy.Matrix(cols).T.rank() if cols else 0


def main():
    print("(A) the torus and the blocks")
    kinds = [kind_of(b) for b in BLOCKS]
    from collections import Counter
    cnt = Counter((kind_of(b), len(b)) for b in BLOCKS)
    check("dim S = 6, 120 operators in 34 weight spaces: 8 of dim 1, 16 mixed "
          "and 8 unmixed of dim 4, 2 of dim 8",
          PROJ.shape[0] == 6 and len(OPS) == 120 and len(BLOCKS) == 34
          and cnt[("one", 1)] == 8 and cnt[("mixed", 4)] == 16
          and cnt[("unmixed1", 4)] + cnt[("unmixed2", 4)] == 8
          and cnt[("unmixed1", 4)] == 4 and cnt[("eight", 8)] == 2,
          str(sorted(cnt.items())))
    supports = []
    for b in BLOCKS:
        s = set()
        for i in b:
            s |= set(IMG_OMEGA[i])
            for ij in IJ:
                s |= set(IMG_TH[(i, ij)])
        supports.append(s)
    disjoint = all(not (supports[a] & supports[c])
                   for a in range(34) for c in range(a + 1, 34))
    check("the images of different weight spaces lie in disjoint sets of "
          "monomials, so r(gamma) is the sum of the block ranks", disjoint,
          "%d image monomials in all" % sum(len(s) for s in supports))

    print("(B) the eight blocks of dimension one")
    ok = True
    for b in BLOCKS:
        if len(b) != 1:
            continue
        i = b[0]
        ok &= bool(IMG_OMEGA[i]) and all(not IMG_TH[(i, ij)] for ij in IJ)
    check("each kills every theta_1^i theta_2^j and not omega: rank 1", ok)

    print("(C) the sixteen mixed blocks")
    ok = True
    target = {E[(i, j)] for i in range(1, 5) for j in range(1, 5)}
    for b in BLOCKS:
        if kind_of(b) != "mixed":
            continue
        M = block_matrix(b)
        const = [M[:, c] for c in range(M.shape[1]) if not M[:, c].free_symbols
                 and any(x != 0 for x in M[:, c])]
        cm = sympy.Matrix.hstack(*const)
        ok &= cm.rank() == 3 and all(cm[3, c] == 0 for c in range(cm.shape[1]))
        last = set()
        for c in range(M.shape[1]):
            x = M[3, c]
            if x == 0:
                continue
            x = -x if sympy.Poly(x, *E.values()).LC() < 0 else x
            last.add(x)
        ok &= last == target
    check("three p-free columns span the first three coordinates, and the "
          "last coordinates are exactly +-e_ij, i, j >= 1: rank 3 + mu(p)", ok)

    print("(D) the eight unmixed blocks of dimension four")
    ok = True
    for b in BLOCKS:
        k = kind_of(b)
        if not k.startswith("unmixed"):
            continue
        t = int(k[-1])
        M = block_matrix(b)
        const = [M[:, c] for c in range(M.shape[1])
                 if not M[:, c].free_symbols and any(x != 0 for x in M[:, c])]
        ok &= len(const) >= 1 and all(
            col[1] == 0 and col[2] == 0 and col[3] == 0 and col[0] != 0
            for col in const)
        ok &= all(sympy.expand(M[1, c] + M[2, c]) == 0
                  for c in range(M.shape[1]))
        if t == 1:
            want = {(E[(i, j)], E[(i + 1, j)]) for i in range(1, 4)
                    for j in range(5)}
        else:
            want = {(E[(j, i)], E[(j, i + 1)]) for i in range(1, 4)
                    for j in range(5)}
        found = None
        for s4 in (1, -1):
            pairs = set()
            good = True
            for c in range(M.shape[1]):
                x, y = M[1, c], s4 * M[3, c]
                if x == 0 and y == 0:
                    continue
                cand = [(x, y), (-x, -y)]
                hit = [q for q in cand if q in want]
                if not hit:
                    good = False
                    break
                pairs.add(hit[0])
            if good and pairs == want:
                found = s4
        ok &= found is not None
    check("a p-free column along the first coordinate, opposite second and "
          "third rows, and (second, fourth) coordinates the Hankel pairs: "
          "rank 1 + rho_1(p) or 1 + rho_2(p)", ok)

    print("(E) the two blocks of dimension eight")
    e1, e2, e3, e4 = sympy.symbols("e1 e2 e3 e4")
    h1 = e1 * e3 - e2 ** 2
    h2 = e2 * e4 - e3 ** 2
    h3 = e1 * e4 - e2 * e3
    Vp = [h3 - e3, 2 * h2 - e4, 2 * h1 + 1 - e2]
    Vm = [h3 + e3, 2 * h2 + e4, 2 * h1 + 1 + e2]
    hankel = [h1, h2, h3]
    for b in BLOCKS:
        if len(b) != 8:
            continue
        t = tau_of_eight(b)
        M = block_matrix(b)
        zero = {x: 0 for x in E.values()}
        cc = [c for c in range(M.shape[1])
              if any(x != 0 for x in M[:, c].subs(zero))]
        allowed = {E[(k, 0)] if t == 1 else E[(0, k)] for k in range(5)}
        ok1 = all(M[:, c].free_symbols <= allowed for c in cc)
        Mc = sympy.Matrix.hstack(*[M[:, c] for c in cc])
        # the two z rows are covered by unit columns
        units = [c for c in range(Mc.shape[1])
                 if not Mc[:, c].free_symbols
                 and sum(1 for x in Mc[:, c] if x != 0) == 1]
        unit_rows = sorted({[r for r in range(8) if Mc[r, c] != 0][0]
                            for c in units})
        ok1 &= unit_rows == [0, 1]
        rest = [c for c in range(Mc.shape[1]) if c not in units]
        rows = [r for r in range(8) if r not in unit_rows]
        N = Mc.extract(rows, rest)
        sub = ({E[(k, 0)]: [0, e1, e2, e3, e4][k] for k in range(1, 5)}
               if t == 1 else
               {E[(0, k)]: [0, e1, e2, e3, e4][k] for k in range(1, 5)})
        N = N.subs(sub)
        # drop duplicate columns up to sign
        uniq = []
        for c in range(N.shape[1]):
            v = tuple(sympy.expand(x) for x in N[:, c])
            if v not in uniq and tuple(-x for x in v) not in uniq:
                uniq.append(v)
        N = sympy.Matrix([[v[r] for v in uniq] for r in range(6)])
        ok1 &= N.shape == (6, 8) and not (N.free_symbols - {e1, e2, e3, e4})
        m5 = set()
        for R in itertools.combinations(range(6), 5):
            for C in itertools.combinations(range(8), 5):
                d = sympy.expand(N.extract(list(R), list(C)).det())
                if d != 0:
                    m5.add(d)
        g5 = sympy.groebner(list(m5), e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
        m6 = set()
        for C in itertools.combinations(range(8), 6):
            d = sympy.expand(N.extract(list(range(6)), list(C)).det())
            if d != 0:
                m6.add(d)
        g6h = sympy.groebner(list(m6) + hankel, e1, e2, e3, e4,
                             order="grevlex", domain=sympy.QQ)
        gp = sympy.groebner(Vp, e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
        gm = sympy.groebner(Vm, e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
        in_both = all(gp.reduce(d)[1] == 0 and gm.reduce(d)[1] == 0
                      for d in m6)
        g6 = sympy.groebner(list(m6), e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
        prods = all(g6.reduce(sympy.expand((f * g) ** 2))[1] == 0
                    for f in Vp for g in Vm)
        check("tau_%d: the p-dependent part involves only the e's of theta_%d, "
              "two unit columns, and a 6 x 8 matrix N" % (t, t), ok1)
        check("tau_%d: the 5 x 5 minors of N generate the unit ideal (R >= 7)"
              % t, list(g5.exprs) == [1], "%d nonzero minors" % len(m5))
        check("tau_%d: the 6 x 6 minors of N lie in the ideals of V_+ and V_-, "
              "and the squares of the products of their generators lie in "
              "the ideal of the minors: rank N = 5 exactly on V_+ u V_-" % t,
              in_both and prods)
        check("tau_%d: the 6 x 6 minors and the 2 x 2 minors of the Hankel "
              "matrix generate the unit ideal (R = 7 forces rho = 2)" % t,
              list(g6h.exprs) == [1])

        # the reduced form of the paper: R_t = 4 + rank K_t
        T = sympy.zeros(8, 8)
        for a, c in ((0, 0), (1, 1), (2, 2), (3, 2), (3, 3), (4, 4), (5, 4),
                     (5, 5), (6, 6), (7, 7)):
            T[a, c] = 1
        TM = (T * M).applyfunc(sympy.expand)
        cols = [tuple(TM[:, c]) for c in range(TM.shape[1])
                if any(x != 0 for x in TM[:, c])]
        st = [c for c in cols if c[3] != 0 or c[5] != 0]
        rest = [c for c in cols if c[3] == 0 and c[5] == 0]
        st_ok = (len(set(st)) == 4 and
                 sympy.Matrix([[c[3], c[5]] for c in set(st)]).rank() == 2)

        def normed(v):
            v = tuple(sympy.expand(x) for x in v)
            for x in v:
                if x != 0:
                    lead = (sympy.Poly(x, *E.values()).coeffs()[0]
                            if x.free_symbols else x)
                    return v if lead > 0 else tuple(-y for y in v)
            return None

        def proj(c):
            return (c[2], c[7], c[4], c[6])
        Kblock = {normed(proj(c)) for c in rest} - {None}
        stl = sorted(set(st), key=str)
        for i1 in range(4):
            for i2 in range(i1 + 1, 4):
                v = tuple((x + y) / 2 for x, y in zip(stl[i1], stl[i2]))
                if v[3] == 0 and v[5] == 0 and normed(proj(v)):
                    Kblock.add(normed(proj(v)))

        def ee(i, j):
            return E[(i, j)] if t == 1 else E[(j, i)]

        def hh(i, j):
            return (ee(i, j), ee(i + 1, j))
        hf = sympy.Rational(1, 2)
        Kwant = set()
        for a, c in ((hh(1, 0), (0, -1)), (hh(2, 0), (hf, 0)),
                     (tuple(-x for x in hh(3, 0)), (0, 0)),
                     ((0, -1), hh(1, 0)), ((-hf, 0), tuple(-x for x in hh(2, 0))),
                     ((0, 0), tuple(-x for x in hh(3, 0)))):
            Kwant.add(normed(tuple(a) + tuple(c)))
        for j in range(1, 5):
            for i in range(1, 4):
                Kwant.add(normed(tuple(hh(i, j)) + (0, 0)))
                Kwant.add(normed((0, 0) + tuple(hh(i, j))))
        check("tau_%d: after the row changes r3 + r4, r5 + r6 the block is two "
              "unit columns, two columns reaching the new rows, and the 4 x 30 "
              "matrix K_t of the paper: R_t = 4 + rank K_t" % t,
              st_ok and Kblock == Kwant, "%d columns of K_t" % len(Kwant))

    q3 = [e3, e4]
    q4 = [-e1 * e2, e2 ** 2 - 2 * e1 * e3 - 1]
    q5 = [2 * e2 ** 2 - e1 * e3 - sympy.Rational(1, 2), e2 * e3]
    q6 = [e1 * e4 - 2 * e2 * e3, e2 * e4 - 2 * e3 ** 2]
    Q = sympy.Matrix([q3, q4, q5, q6])
    qm = [sympy.expand(Q.extract([a, c], [0, 1]).det())
          for a, c in itertools.combinations(range(4), 2)]
    gQ = sympy.groebner([x for x in Q if x != 0], e1, e2, e3, e4,
                        order="grevlex", domain=sympy.QQ)
    gqm = sympy.groebner(qm, e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
    gp = sympy.groebner(Vp, e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
    gm = sympy.groebner(Vm, e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
    gqh = sympy.groebner(qm + hankel, e1, e2, e3, e4, order="grevlex", domain=sympy.QQ)
    K6 = sympy.Matrix([[e1, e2, -e3, 0, -hf, 0], [e2, e3, -e4, -1, 0, 0],
                       [0, hf, 0, e1, -e2, -e3], [-1, 0, 0, e2, -e3, -e4]])
    rnd0 = random.Random(7)
    agree = True
    for trial in range(30):
        pt = {x: sympy.Rational(rnd0.randint(-6, 6), rnd0.randint(1, 3))
              for x in (e1, e2, e3, e4)}
        agree &= K6.subs(pt).rank() == 2 + Q.subs(pt).rank()
    for pt in ({e1: 0, e2: -1, e3: 0, e4: 0}, {e1: 5, e2: hf, e3: 0, e4: 0},
               {e1: 4, e2: 1, e3: sympy.Rational(1, 4), e4: sympy.Rational(1, 8)}):
        agree &= K6.subs(pt).rank() == 2 + Q.subs(pt).rank() == 3
    check("the hand reduction of the proof: the six p-free columns of K have "
          "rank 2 + rank Q, the entries of Q generate the unit ideal, the "
          "2 x 2 minors of Q lie in the ideals of V_+ and V_-, the squares of "
          "the products of their generators lie in the ideal of the minors, "
          "and the minors with the Hankel minors generate the unit ideal",
          agree and list(gQ.exprs) == [1]
          and all(gp.reduce(x)[1] == 0 and gm.reduce(x)[1] == 0 for x in qm)
          and all(gqm.reduce(sympy.expand((f * g) ** 2))[1] == 0
                  for f in Vp for g in Vm)
          and list(gqh.exprs) == [1])

    BIG = {tau_of_eight(b): block_matrix(b) for b in BLOCKS if len(b) == 8}

    def big_rank(e, t):
        M = BIG[t]
        return M.subs({E[ij]: sympy.Rational(e.get(ij, 0))
                               for ij in IJ}).rank()

    def formula(e):
        R1, R2 = big_rank(e, 1), big_rank(e, 2)
        return (64 + 16 * mu(e) + 4 * rho(e, 1) + 4 * rho(e, 2) + R1 + R2,
                R1, R2)

    print("(F) the formula r = 64 + 16 mu + 4 rho_1 + 4 rho_2 + R_1 + R_2")
    rnd = random.Random(20260929)
    ok = True
    Rs = set()
    for trial in range(40):
        e = {}
        k = rnd.choice([1, 2, 3, 5, 25])
        for ij in rnd.sample(IJ, k):
            e[ij] = Fr(rnd.randint(-9, 9), rnd.randint(1, 5))
        f, R1, R2 = formula(e)
        Rs |= {R1, R2}
        ok &= f == direct_rank(e)
    check("the formula agrees with the rank on all 120 operators at forty "
          "random p", ok, "R values seen: %s" % sorted(Rs))

    half = Fr(1, 2)
    examples = [
        (80, {}), (84, {(1, 0): 1}), (88, {(2, 0): 2}),
        (92, {(2, 0): 2, (0, 1): 1}), (96, {(2, 0): 2, (0, 2): 2}),
        (104, {(1, 1): 1}), (108, {(1, 2): 1}), (112, {(2, 2): 1}),
        (87, {(2, 0): 1}), (91, {(2, 0): 1, (0, 1): 1}),
        (95, {(2, 0): 1, (0, 2): 2}), (94, {(2, 0): 1, (0, 2): 1}),
        (107, {(2, 0): 1, (1, 1): 1}),
        (111, {(2, 0): 1, (1, 1): 1, (0, 2): 2}),
        (110, {(2, 0): 1, (1, 1): 1, (0, 2): 1}),
    ]
    print("(G) fifteen values")
    ok = True
    realised = []
    for want, e in examples:
        d = direct_rank(e)
        f, R1, R2 = formula(e)
        ok &= d == want == f
        realised.append(d)
        print("      e = %-34s r = %3d  (mu %d, rho %d %d, R %d %d)" % (
            {("e%d%d" % k): str(v) for k, v in e.items()}, d, mu(e),
            rho(e, 1), rho(e, 2), R1, R2))
    check("the fifteen explicit p have the listed ranks, computed on all 120 "
          "operators and by the formula", ok)
    vals = set()
    minimal = set()
    for m in (0, 1):
        for r1 in (0, 1, 2):
            for r2 in (0, 1, 2):
                for R1 in (7, 8):
                    for R2 in (7, 8):
                        if m == 1 and (r1 == 0 or r2 == 0):
                            continue
                        if (R1 == 7 and r1 != 2) or (R2 == 7 and r2 != 2):
                            continue
                        v = 64 + 16 * m + 4 * r1 + 4 * r2 + R1 + R2
                        vals.add(v)
                        if v == 80:
                            minimal.add((m, r1, r2, R1, R2))
    check("the allowed tuples give exactly the fifteen realised values; the "
          "least, 80, only at (0,0,0,8,8), that is for p constant; 100 is not "
          "a value", vals == set(realised) and min(vals) == 80
          and minimal == {(0, 0, 0, 8, 8)} and 100 not in vals,
          str(sorted(vals)))

    print("(H) the exceptional coefficients move with omega")
    u = (4, 1, 1, 1)
    r2 = direct_rank({(2, 0): 2}, u)
    r3 = direct_rank({(2, 0): 3}, u)
    check("omega = 4 alpha_0 + alpha_1 + alpha_2 + alpha_3: r = 87 at "
          "e_20 = 2 and r = 88 at e_20 = 3", r2 == 87 and r3 == 88,
          "r = %d, %d" % (r2, r3))

    print("(I) the Kaehler class of the Weil tori")
    th = addf(TH[0], TH[1])
    top = (1 << NG) - 1
    al = [alpha(s) for s in range(4)]

    def integral(f):
        return f.get(top, 0)
    conj = {0: 1, 1: 0, 2: 3, 3: 2}
    ok = all(integral(wedge(al[s], powf(th, 6))) == 0 for s in range(4))
    for S3 in itertools.combinations(range(4), 3):
        f = wedge(wedge(al[S3[0]], al[S3[1]]), al[S3[2]])
        ok &= integral(wedge(f, powf(th, 2))) == 0
    for s, r in itertools.combinations(range(4), 2):
        v = integral(wedge(wedge(al[s], al[r]), powf(th, 4)))
        ok &= (v != 0) == (r == conj[s])
    check("with kappa_0 = theta_1 + theta_2: int alpha_s kappa_0^6 = 0, "
          "int alpha_s alpha_r alpha_q kappa_0^2 = 0, and int alpha_s alpha_r "
          "kappa_0^4 is nonzero exactly for r conjugate to s", ok)

    print("(J) the characters that stay of Hodge type on the Weil tori")

    def proportional(f, g):
        if not f or set(f) != set(g):
            return False
        k = next(iter(f))
        c = Fr(f[k]) / Fr(g[k])
        return c != 0 and all(Fr(f[m]) == c * Fr(g[m]) for m in f)
    ok = proportional(powf(TH[0], 4), wedge(al[0], al[1]))
    ok &= proportional(powf(TH[1], 4), wedge(al[2], al[3]))
    ok &= all(not proportional(powf(TH[0], i), wedge(al[0], al[1]))
              for i in (1, 2, 3))
    e88 = {(4, 0): 1, (0, 4): 1}
    e104 = {(4, 0): 1, (0, 4): 1, (4, 4): 1}
    r88, r104 = direct_rank(e88), direct_rank(e104)
    ok &= (r88, mu(e88), rho(e88, 1), rho(e88, 2)) == (88, 0, 1, 1)
    ok &= (r104, mu(e104), rho(e104, 1), rho(e104, 2)) == (104, 1, 1, 1)
    check("theta_1^4 and theta_2^4 are nonzero multiples of alpha_0 alpha_1 "
          "and alpha_2 alpha_3; r(omega + theta_1^4/24 + theta_2^4/24) = 88 "
          "with mu = 0, rho_1 = rho_2 = 1, and adding theta_1^4 theta_2^4/576 "
          "gives 104", ok, "r = %d, %d" % (r88, r104))

    print("(K) the first order deformations that keep gamma of Hodge type")
    V1 = [i for i, op in enumerate(OPS) if op[0][0] == "v"]

    def emb(g):
        return g // 4

    FLIN = [i for i in V1 if emb(OPS[i][0][1]) == emb(OPS[i][0][2])]

    def kernel(vectors):
        keys = sorted({k for v in vectors for k in v})
        M = sympy.Matrix([[sympy.Rational(v.get(k, 0).numerator,
                                          v.get(k, 0).denominator)
                           if isinstance(v.get(k, 0), Fr)
                           else v.get(k, 0) for k in keys]
                          for v in vectors]).T
        return M.nullspace()

    def ann_h1(e, u):
        g = gamma_form(e, u)
        return kernel([apply_op(OPS[i], g) for i in V1])

    def d_theta(ops_idx, t):
        """the F-linear operators, as columns, and their images of theta_t"""
        return [apply_op(OPS[i], TH[t]) for i in ops_idx]

    def mid(e, t):
        return any(c != 0 and (ij[t] in (1, 2, 3)) for ij, c in e.items())

    def predicted(e):
        """F-linear xi with xi _| theta_t = 0 at each place t where p has a
        monomial whose exponent of theta_t is 1, 2 or 3"""
        vecs = []
        for i in FLIN:
            v = {}
            for t in (0, 1):
                if mid(e, t):
                    for m, c in apply_op(OPS[i], TH[t]).items():
                        v[(t, m)] = v.get((t, m), 0) + c
            vecs.append(v)
        if not any(vecs):
            return len(FLIN)
        keys = sorted({k for v in vecs for k in v})
        M = sympy.Matrix([[v.get(k, 0) for k in keys] for v in vecs]).T
        return len(FLIN) - M.rank()

    ok = len(V1) == 64 and len(FLIN) == 16
    rnd = random.Random(20260930)
    allowed = {"none": (0,), "four": (0, 4), "mid": (0, 1, 2, 3, 4)}
    seen = []
    for c1 in ("none", "four", "mid"):
        for c2 in ("none", "four", "mid"):
            for u in ((1, 1, 1, 1), (2, -3, 5, 7)):
                e = {}
                for i in allowed[c1]:
                    for j in allowed[c2]:
                        if (i, j) != (0, 0):
                            e[(i, j)] = Fr(rnd.randint(1, 9) *
                                           rnd.choice([-1, 1]),
                                           rnd.randint(1, 4))
                ker = ann_h1(e, u)
                dim = len(ker)
                want = 8 + 4 * (c1 != "mid") + 4 * (c2 != "mid")
                inflin = all(all(vec[r] == 0 for r in range(64)
                                 if V1[r] not in FLIN) for vec in ker)
                for vec in ker:
                    for t in (0, 1):
                        if not mid(e, t):
                            continue
                        img = {}
                        for r in range(64):
                            if vec[r] != 0:
                                for m, c in apply_op(OPS[V1[r]],
                                                     TH[t]).items():
                                    img[m] = img.get(m, 0) + vec[r] * c
                        inflin &= all(c == 0 for c in img.values())
                ok &= dim == want == predicted(e) and inflin
                seen.append(dim)
    check("on H^1(T_A) the annihilator of omega + p consists of F-linear "
          "deformations, and it is cut out by xi _| theta_t = 0 at each place "
          "where p has a monomial with theta_t-exponent 1, 2 or 3: dimension "
          "8 + 4 (places without one), for all nine patterns and two omega",
          ok, "dimensions %s" % sorted(set(seen)))

    ok = True
    shapes = [({(1, 0): 1, (0, 1): 1}, 8), ({(1, 0): 2, (0, 1): -3}, 8),
              ({(2, 0): 1, (0, 2): 1}, 8), ({}, 16),
              ({(4, 0): 1, (0, 4): 1}, 16), ({(4, 4): 1}, 16)]
    for lam, b in ((2, 1), (Fr(1, 3), 5), (-1, 2)):
        e = {}
        for i in range(1, 5):
            e[(i, 0)] = Fr(b) * Fr(lam) ** i
            e[(0, i)] = Fr(b + 1) * Fr(2 * lam + 1) ** i
        shapes.append((e, 8))
    dims = []
    for e, want in shapes:
        d = len(ann_h1(e, (1, 1, 1, 1)))
        dims.append(d)
        ok &= d == want
    check("the characters left at 88, c + f(theta_1) + f'(theta_2) with f "
          "linear or exponential, and a quadratic one have annihilator of "
          "dimension 8 on H^1(T_A), the tangent space of the family; the "
          "constant and the theta^4 shapes have 16, all F-linear deformations",
          ok, "dimensions %s" % dims)

    print("(L) the exceptional places and the Hodge locus of the character")

    def nonflin(vecs):
        return sum(1 for vec in vecs
                   if any(vec[r] != 0 and V1[r] not in FLIN
                          for r in range(64)))

    h, t4 = Fr(1, 2), Fr(1, 4)
    cases = [({(2, 0): h}, (1, 1, 1, 1), 13, 1),
             ({(2, 0): -h}, (1, 1, 1, 1), 13, 1),
             ({(2, 0): 1}, (4, 1, 1, 1), 13, 1),
             ({(2, 0): -1}, (4, 1, 1, 1), 13, 1),
             ({(2, 0): h, (4, 0): 3}, (1, 1, 1, 1), 13, 1),
             ({(2, 0): 1}, (1, 1, 1, 1), 12, 0),
             ({(2, 0): -1}, (1, 1, 1, 1), 12, 0),
             ({(2, 0): Fr(1, 3)}, (1, 1, 1, 1), 12, 0),
             ({(2, 0): 2}, (4, 1, 1, 1), 12, 0),
             ({(2, 0): h, (1, 0): 1}, (1, 1, 1, 1), 12, 0),
             ({(2, 0): h, (3, 0): 1}, (1, 1, 1, 1), 12, 0),
             ({(2, 0): h, (2, 4): 1}, (1, 1, 1, 1), 12, 0),
             ({(2, 0): h, (2, 1): 1}, (1, 1, 1, 1), 8, 0),
             ({(2, 0): h, (0, 2): h}, (1, 1, 1, 1), 10, 2),
             ({(2, 0): h, (0, 2): -h}, (1, 1, 1, 1), 10, 2),
             ({(2, 0): -h, (0, 2): -h, (4, 0): 3, (0, 4): 3, (4, 4): 5},
              (1, 1, 1, 1), 10, 2),
             ({(2, 0): h, (0, 2): 1}, (1, 1, 1, 1), 9, 1)]
    ok = True
    got = []
    for e, u, want, extra in cases:
        ker = ann_h1(e, u)
        got.append((len(ker), nonflin(ker)))
        ok &= (len(ker), nonflin(ker)) == (want, extra)
    check("a mid place t is exceptional, with one more first order deformation "
          "that is not F-linear, exactly when the only monomial with "
          "theta_t-exponent 1, 2 or 3 is theta_t^2 itself and 16 c_t^2 = "
          "u_s u_s' for its coefficient c_t = e/2 (e_20 = +-1/2 at u = 1, "
          "+-1 at u = (4,1,1,1)); theta_t^4 terms keep it, any other mid "
          "monomial kills it", ok, "(dim, not F-linear) %s" % got)

    t14 = powf(TH[0], 4)
    a01 = wedge(alpha(0), alpha(1))
    om1 = addf(alpha(0), alpha(1), 1)
    ok = (t14 == {m: 24 * c for m, c in a01.items()} and
          wedge(om1, om1) == {m: 2 * c for m, c in a01.items()})
    check("theta_1^4 = 24 alpha_0 alpha_1 and omega_1^2 = 2 u_0 u_1 alpha_0 "
          "alpha_1, so 16 c^2 = u_0 u_1 reads c^2 theta_1^4 = (3/4) "
          "omega_1^2, the ratio of rem:p2primeexceptional place by place", ok)

    r94 = direct_rank({(2, 0): h, (0, 2): h})
    r94b = direct_rank({(2, 0): -h, (0, 2): -h, (4, 0): 3, (0, 4): 3})
    r110 = direct_rank({(2, 0): h, (0, 2): h, (4, 4): 1})
    check("a character exceptional at both places with rational shape has "
          "rank 94, or 110 with theta_1^4 theta_2^4, never 88",
          (r94, r94b, r110) == (94, 94, 110),
          "r = %d, %d, %d" % (r94, r94b, r110))

    # the stabiliser of omega_1 + c theta_1^2 in gl(V_0 + V_1)
    G8 = [gen(s, k, l) for s in (0, 1) for k in (0, 1) for l in (0, 1)]
    ISA = [(g % 4) // 2 == 0 for g in G8]
    POS = {g: t for t, g in enumerate(G8)}

    def der8(i, j, f):
        out = {}
        for m, c in f.items():
            s1, mm = contract_gen(m, G8[j])
            if not s1:
                continue
            s2, mm2 = wedge_gen(mm, G8[i])
            if not s2:
                continue
            out[mm2] = out.get(mm2, 0) + s1 * s2 * c
        return {m: c for m, c in out.items() if c != 0}

    PERM = sympy.zeros(8, 8)
    for k in range(2):
        for x, y in ((gen(0, 0, k), gen(1, 1, k)), (gen(1, 0, k), gen(0, 1, k))):
            PERM[POS[x], POS[y]] = 1
            PERM[POS[y], POS[x]] = 1

    def inertia(Gm):
        Gm = sympy.Matrix(Gm)
        pos = neg = 0
        n = Gm.shape[0]
        while n:
            piv = next((i for i in range(n) if Gm[i, i] != 0), None)
            if piv is None:
                pr = next(((i, j) for i in range(n) for j in range(n)
                           if Gm[i, j] != 0), None)
                if pr is None:
                    break
                i, j = pr
                Gm[:, i] = Gm[:, i] + Gm[:, j]
                Gm[i, :] = Gm[i, :] + Gm[j, :]
                piv = i
            d = Gm[piv, piv]
            pos, neg = pos + int(bool(d > 0)), neg + int(bool(d < 0))
            v = Gm[:, piv]
            Gm = Gm - v * v.T / d
            keep = [i for i in range(n) if i != piv]
            Gm = Gm.extract(keep, keep)
            n -= 1
        return pos, neg

    def stab_data(c):
        th2 = wedge(TH[0], TH[0])
        X1 = addf(addf(addf({}, alpha(0), 1), alpha(1), 1), th2, c)
        idx = [(i, j) for i in range(8) for j in range(8)]
        vecs = [der8(i, j, X1) for (i, j) in idx]
        keys = sorted({k for v in vecs for k in v})
        M = sympy.Matrix([[v.get(k, 0) for v in vecs] for k in keys])
        ns = M.nullspace()
        d = len(ns)
        B = sympy.Matrix.hstack(*ns)
        rows_p = [r for r, (i, j) in enumerate(idx) if ISA[j] and not ISA[i]]
        in_p = d - B.extract(rows_p, list(range(d))).rank()
        mats = [sympy.Matrix(8, 8, lambda i, j: v[8 * i + j]) for v in ns]
        sym = [m + PERM * m * PERM for m in mats]
        asym = [m - PERM * m * PERM for m in mats]
        basis = []
        for group, sgn in ((sym, 1), (asym, -1)):
            flat = sympy.Matrix([list(m) for m in group])
            rr = flat.rref()[0]
            for r in range(flat.rank()):
                basis.append((sympy.Matrix(8, 8, list(rr.row(r))), sgn))
        # the real form is spanned by the m + PmP and the i(m - PmP), and
        # the trace form pairs the two kinds to zero
        Gm = [[(-1 if sa == sb == -1 else 1) * (X * Y).trace()
               for (Y, sb) in basis] for (X, sa) in basis]
        cross = all((X * Y).trace() == 0 for (X, sa) in basis
                    for (Y, sb) in basis if sa != sb)
        if not cross:
            return None
        return d, d - in_p, len(basis), inertia(Gm)

    ex, ordn = stab_data(t4), stab_data(h)
    check("the stabiliser of omega_1 + c theta_1^2 in gl(V_0 + V_1) has "
          "dimension 21, orbit of dimension 5 in the Grassmannian and a real "
          "form whose trace form has signature (12, 9), so(4,3), at the "
          "exceptional c = 1/4; dimension 15, orbit 4 and signature (8, 7), "
          "su(2,2), at c = 1/2",
          ex == (21, 5, 21, (12, 9)) and ordn == (15, 4, 15, (8, 7)),
          "exceptional %s, ordinary %s" % (ex, ordn))

    # Hodge classes of degree 2 and 4 kept along the locus
    e_ex = {(2, 0): h, (0, 2): h}
    ker = ann_h1(e_ex, (1, 1, 1, 1))
    ops_ker = []
    for vec in ker:
        ops_ker.append({V1[r]: vec[r] for r in range(64) if vec[r] != 0})

    def kept(classes):
        cols = []
        for cl in classes:
            col = {}
            for n, opsv in enumerate(ops_ker):
                for i, c in opsv.items():
                    for m, x in apply_op(OPS[i], cl).items():
                        col[(n, m)] = col.get((n, m), 0) + c * x
            cols.append(col)
        keys = sorted({k for v in cols for k in v})
        if not keys:
            return len(classes)
        M = sympy.Matrix([[v.get(k, 0) for v in cols] for k in keys])
        return len(classes) - M.rank()

    deg4 = [wedge(TH[0], TH[0]), wedge(TH[0], TH[1]), wedge(TH[1], TH[1])] + \
        [alpha(s) for s in range(4)]
    k2, k4 = kept(TH), kept(deg4)
    x1 = addf(addf(addf({}, alpha(0), 1), alpha(1), 1), THP[(2, 0)], h)
    x2 = addf(addf(addf({}, alpha(2), 1), alpha(3), 1), THP[(0, 2)], h)
    k4x = kept([x1, x2])
    check("for omega + (theta_1^2 + theta_2^2)/4, exceptional at both places, "
          "no combination of theta_1, theta_2 stays of type (1,1) along the "
          "locus, and of theta_1^2, theta_1 theta_2, theta_2^2 and the four "
          "alpha_s exactly the span of X_t = omega_t + theta_t^2/4 stays of "
          "Hodge type", (k2, k4, k4x) == (0, 2, 2),
          "kept: %d of 2, %d of 7, %d of X_1, X_2" % (k2, k4, k4x))

    # the sign of int X_1 kappa^6 on Kaehler classes
    class GQ:
        __slots__ = ("re", "im")

        def __init__(s, re=0, im=0):
            s.re, s.im = Fr(re), Fr(im)

        @staticmethod
        def _c(o):
            return o if isinstance(o, GQ) else GQ(o)

        def __add__(s, o):
            o = GQ._c(o)
            return GQ(s.re + o.re, s.im + o.im)
        __radd__ = __add__

        def __mul__(s, o):
            o = GQ._c(o)
            return GQ(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
        __rmul__ = __mul__

        def __eq__(s, o):
            o = GQ._c(o)
            return s.re == o.re and s.im == o.im

        def __ne__(s, o):
            return not s == o

        def conj(s):
            return GQ(s.re, -s.im)

    AG = [gen(s, 0, k) for s in range(4) for k in range(2)]
    CJ = {}
    for k in range(2):
        CJ[gen(0, 0, k)], CJ[gen(1, 0, k)] = gen(1, 1, k), gen(0, 1, k)
        CJ[gen(2, 0, k)], CJ[gen(3, 0, k)] = gen(3, 1, k), gen(2, 1, k)

    def kappa_h(H):
        f = {}
        for j in range(8):
            for l in range(8):
                if H[j][l] != 0:
                    f = addf(f, mono([AG[j], CJ[AG[l]]]), GQ(0, 1) * H[j][l])
        return f

    def total(f):
        s = GQ(0)
        for c in f.values():
            s = s + c
        return s

    def eye8():
        return [[GQ(1) if j == l else GQ(0) for l in range(8)]
                for j in range(8)]

    vol = total(powf(kappa_h(eye8()), 8))
    hs = [eye8()]
    for z in (Fr(9, 10), Fr(-9, 10)):
        H = eye8()
        H[0][2] = H[2][0] = GQ(Fr(9, 10))
        H[1][3] = H[3][1] = GQ(z)
        hs.append(H)
    rng = random.Random(20260929)
    for _ in range(3):
        Mx = [[GQ(rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(8)]
              for _ in range(8)]
        hs.append([[total({k: Mx[j][k] * Mx[l][k].conj() for k in range(8)})
                    for l in range(8)] for j in range(8)])
    th2 = wedge(TH[0], TH[0])
    signs = {t4: set(), -t4: set(), Fr(1, 10): set()}
    for H in hs:
        k6 = powf(kappa_h(H), 6)
        for c in signs:
            X1 = addf(addf(addf({}, alpha(0), 1), alpha(1), 1), th2, c)
            v = total(wedge(X1, k6))
            ok_real = v.im == 0 and vol.im == 0
            signs[c].add((v.re / vol.re > 0) - (v.re / vol.re < 0)
                         if ok_real else None)
    check("int X_1 kappa^6 has the constant sign of -c at the exceptional "
          "c = +-1/4, for the Kaehler classes of six positive hermitian forms "
          "on the whole tangent space, and takes both signs at c = 1/10",
          signs[t4] == {-1} and signs[-t4] == {1} and
          signs[Fr(1, 10)] == {-1, 1},
          "signs %s" % {str(c): sorted(s) for c, s in signs.items()})

    print()
    print("%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    raise SystemExit(main())
