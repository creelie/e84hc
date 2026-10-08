#!/usr/bin/env python3
"""
v3_tspace.py d -- independent exact computation (over Q(i), no reduction mod p)
of T = T_[A] D_{4,4} at the split member A = X x Xhat, X = C^4/(Z^4 + i Z^4),
and of rank(T -> H^*, v -> v _| ch F) for natural objects F.

Complex structure: H^{1,0}(X) = <x_j + i x_{4+j}>, H^{1,0}(Xhat) = B H^{1,0}(X)
= <xi_{4+j} - i xi_j>.  T = {v in Hom(H^{1,0}, H^{0,1}) : v M = M v,
D_v eta = 0}, D_v the derivation of wedge^* H^1 extending v (zero on H^{0,1}).
Claims checked: dim T = 16; T kills eta, W1, W2; rank T _| ch F = 6 for line
bundles off Q eta, subtori, twisted subtori; 0 for O(eta).
"""
import sys, time
from fractions import Fraction as Fr
from v4lib import Model, wedge, lin, pw, _sgn, QD, RREF

d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
n = 4
Mo = Model(n, d)
t0 = time.time()
I = QD(0, 1, 1)      # Gaussian rationals: delta^2 = -1 in this helper
ONE = QD(1, 0, 1)
ZERO = QD(0, 0, 1)
NG = 16   # generators: 0..7 x_1..x_8, 8..15 xi_1..xi_8


def gx(i):
    return i - 1


def gxi(i):
    return 8 + i - 1


# 1-forms as length-16 lists of QD
def vec(pairs):
    v = [ZERO] * NG
    for g, c in pairs:
        v[g] = v[g] + c
    return v


# holomorphic basis h_0..h_7: dz_j (j=1..4), then B dz_j
hol = []
for j in range(1, 5):
    hol.append(vec([(gx(j), ONE), (gx(4 + j), I)]))
for j in range(1, 5):
    # B x_j = xi_{4+j}, B x_{4+j} = -xi_j : B dz_j = xi_{4+j} - i xi_j
    hol.append(vec([(gxi(4 + j), ONE), (gxi(j), -I)]))


def conj(v):
    return [QD(c.a, -c.b, 1) for c in v]


antihol = [conj(h) for h in hol]
# express each rational generator g as sum_a P[g][a] hol_a + Q[g][a] antihol_a
# solve the 16x16 system exactly
basis = hol + antihol   # 16 vectors in C^16


def solve(Mcols, rhs):
    """solve sum_k y_k Mcols[k] = rhs over Q(i); Mcols list of 16 vectors"""
    m = len(Mcols)
    # augmented matrix rows = coordinates
    A = [[Mcols[k][r] for k in range(m)] + [rhs[r]] for r in range(NG)]
    # gaussian elimination
    piv_cols = []
    row = 0
    for col in range(m):
        pr = None
        for r in range(row, NG):
            if A[r][col]:
                pr = r
                break
        if pr is None:
            continue
        A[row], A[pr] = A[pr], A[row]
        inv = inverse(A[row][col])
        A[row] = [x * inv for x in A[row]]
        for r in range(NG):
            if r != row and A[r][col]:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[row])]
        piv_cols.append(col)
        row += 1
    y = [ZERO] * m
    for r, col in enumerate(piv_cols):
        y[col] = A[r][m]
    return y


def inverse(z):
    nrm = z.a * z.a + z.b * z.b
    return QD(z.a / nrm, -z.b / nrm, 1)


decomp = []
for g in range(NG):
    e = [ZERO] * NG
    e[g] = ONE
    decomp.append(solve(basis, e))   # 16 coefficients: first 8 hol, last 8 antihol

# M acting on 1-forms (rational 16x16): x -> -Bx, xi -> d B^{-1} xi
def M_on_gen(g):
    if g < 8:
        i = g + 1
        if i <= 4:
            return vec([(gxi(4 + i), QD(-1, 0, 1))])
        return vec([(gxi(i - 4), QD(1, 0, 1))])
    j = g - 8 + 1
    if j <= 4:   # B^{-1} xi_j = -x_{4+j}
        return vec([(gx(4 + j), QD(-d, 0, 1))])
    return vec([(gx(j - 4), QD(d, 0, 1))])


def apply_lin(Mgen, v):
    out = [ZERO] * NG
    for g in range(NG):
        if v[g]:
            img = Mgen(g)
            for t in range(NG):
                if img[t]:
                    out[t] = out[t] + v[g] * img[t]
    return out


# M in the complex basis: M hol_a = sum_b Mh[a][b] hol_b (must stay holomorphic)
def coords_in_basis(v):
    return solve(basis, v)


Mh = []
ok_pres = True
for a in range(8):
    c = coords_in_basis(apply_lin(M_on_gen, hol[a]))
    if any(c[8 + k] for k in range(8)):
        ok_pres = False
    Mh.append(c[:8])
Ma = []
for a in range(8):
    c = coords_in_basis(apply_lin(M_on_gen, antihol[a]))
    if any(c[k] for k in range(8)):
        ok_pres = False
    Ma.append(c[8:])
print("(T0) M preserves H^{1,0} and H^{0,1}:", ok_pres)

# unknown v: v(hol_a) = sum_b V[a][b] antihol_b ; 64 unknowns
# condition 1: v(M hol_a) = M v(hol_a):
#   sum_c Mh[a][c] V[c][b] = sum_c V[a][c] Ma[c][b]  for all a,b
# condition 2: D_v eta = 0.
eta = Mo.eta()


def Dv_on_gen(Vm):
    """return function g -> 16-vector D_v(generator g) in the rational basis"""
    imgs = []
    for g in range(NG):
        co = decomp[g]      # hol coefficients co[0..7]
        out = [ZERO] * NG
        for a in range(8):
            if co[a]:
                for b_ in range(8):
                    if Vm[a][b_]:
                        c = co[a] * Vm[a][b_]
                        for t in range(NG):
                            if antihol[b_][t]:
                                out[t] = out[t] + c * antihol[b_][t]
        imgs.append(out)
    return imgs


def derivation(imgs, x):
    """D x for x a class (dict mask->coeff, coeff rational or QD) with D on gens given"""
    out = {}
    for m, c in x.items():
        if not isinstance(c, QD):
            c = QD(c, 0, 1)
        mm = m
        while mm:
            g = (mm & -mm).bit_length() - 1
            mm &= mm - 1
            rest = m & ~(1 << g)
            # g_1..g_r = (-1)^{#gens before g} g ^ rest
            s = bin(m & ((1 << g) - 1)).count("1")
            sg = -1 if s & 1 else 1
            img = imgs[g]
            for t in range(NG):
                if img[t] and not (rest >> t) & 1:
                    sign = sg * _sgn(1 << t, rest)
                    k = rest | (1 << t)
                    val = c * img[t] * sign
                    out[k] = out.get(k, ZERO) + val
    return {k: v for k, v in out.items() if v}


# build linear system for V
unknowns = [(a, b_) for a in range(8) for b_ in range(8)]
eqs = []
for a in range(8):
    for b_ in range(8):
        row = {}
        for c in range(8):
            if Mh[a][c]:
                row[(c, b_)] = row.get((c, b_), ZERO) + Mh[a][c]
            if Ma[c][b_]:
                row[(a, c)] = row.get((a, c), ZERO) - Ma[c][b_]
        eqs.append(row)
# eta condition: D_v eta is linear in V; compute for each unit V
unit_imgs = {}
for (a, b_) in unknowns:
    Vm = [[ZERO] * 8 for _ in range(8)]
    Vm[a][b_] = ONE
    unit_imgs[(a, b_)] = Dv_on_gen(Vm)
eta_rows = {}
for u in unknowns:
    De = derivation(unit_imgs[u], eta)
    for k, c in De.items():
        eta_rows.setdefault(k, {})[u] = c
eqs += list(eta_rows.values())


# solve homogeneous system over Q(i): RREF over QD
def rref_qd(rows, keys):
    piv = []
    R = []
    for r in rows:
        r = {k: v for k, v in r.items() if v}
        for pk, prow in R:
            c = r.get(pk)
            if c:
                for k, x in prow.items():
                    nv = r.get(k, ZERO) - c * x
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
        if not r:
            continue
        pk = min(r, key=lambda k: keys.index(k))
        inv = inverse(r[pk])
        r = {k: x * inv for k, x in r.items()}
        newR = []
        for opk, prow in R:
            c = prow.get(pk)
            if c:
                prow = dict(prow)
                for k, x in r.items():
                    nv = prow.get(k, ZERO) - c * x
                    if nv:
                        prow[k] = nv
                    else:
                        prow.pop(k, None)
            newR.append((opk, prow))
        newR.append((pk, r))
        R = newR
    return R


R = rref_qd(eqs, unknowns)
pivots = set(pk for pk, _ in R)
free = [u for u in unknowns if u not in pivots]
print("(T1) dim T = %d (expect n^2 = 16)" % len(free))
Tbasis = []
for f in free:
    sol = {f: ONE}
    for pk, prow in R:
        c = prow.get(f)
        if c:
            sol[pk] = -c
    Vm = [[ZERO] * 8 for _ in range(8)]
    for (a, b_), c in sol.items():
        Vm[a][b_] = c
    Tbasis.append(Dv_on_gen(Vm))


def rank_qd(vecs):
    rows = [{k: v for k, v in x.items()} for x in vecs]
    keys_all = sorted(set().union(*[set(r) for r in rows])) if rows else []
    R = []
    for r in rows:
        r = dict(r)
        for pk, prow in R:
            c = r.get(pk)
            if c:
                for k, x in prow.items():
                    nv = r.get(k, ZERO) - c * x
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
        if not r:
            continue
        pk = min(r)
        inv = inverse(r[pk])
        r = {k: x * inv for k, x in r.items()}
        R.append((pk, r))
    return len(R)


def T_rank(x):
    return rank_qd([derivation(imgs, x) for imgs in Tbasis])


b, bh, l = Mo.beta(), Mo.betahat(), Mo.ell()
# Weil classes
gam = lin((d, b), (-1, bh))
from v4lib import QD as Q2
gq = {k: Q2(c, 0, d) for k, c in gam.items()}
lq = {k: Q2(0, -c, d) for k, c in l.items()}
P4 = pw(lin((1, gq), (1, lq)), 4)
W1 = {k: c.a for k, c in P4.items() if c.a}
W2 = {k: c.b for k, c in P4.items() if c.b}
print("(T2) rank T_|eta = %d, T_|W1 = %d, T_|W2 = %d (expect 0,0,0)"
      % (T_rank(eta), T_rank(W1), T_rank(W2)))
tests = [("O(beta)", Mo.expo(b)),
         ("O(beta+betahat-ell)", Mo.expo(lin((1, b), (1, bh), (-1, l)))),
         ("O(2beta-betahat+3ell)", Mo.expo(lin((2, b), (-1, bh), (3, l)))),
         ("[B_(1,0)]", Mo.subtorus_track(1, 0)),
         ("[B_(2,1)]", Mo.subtorus_track(2, 1)),
         ("[B_(3,-2)]", Mo.subtorus_track(3, -2)),
         ("[B_(1,1)] e^beta", wedge(Mo.subtorus_track(1, 1), Mo.expo(b))),
         ("[B_(1,2)] e^eta", wedge(Mo.subtorus_track(1, 2), Mo.expo(eta))),
         ("point", {Mo.top: 1}),
         ("O(eta)", Mo.expo(eta)),
         ("O(-2 eta)", Mo.expo(lin((-2, eta))))]
for name, x in tests:
    print("(T3) %-24s rank T _| ch = %d" % (name, T_rank(x)))
# joint rank for the explicit example set (d=1): v -> (v _| ch F_i)_i
pts = [(1, -3), (1, -2), (1, 2), (1, 3), (2, -1), (2, 1), (3, -1), (3, 1)]
joint = []
for imgs in Tbasis:
    big = {}
    for idx, (p, q) in enumerate(pts):
        Dx = derivation(imgs, Mo.subtorus_track(p, q))
        for k, c in Dx.items():
            big[(idx, k)] = c
    joint.append(big)
print("(T4) joint rank of v -> (v _| [B_i])_i over the 8 subtori of the example = %d"
      % rank_qd(joint))
print("time %.1fs" % (time.time() - t0))
