#!/usr/bin/env python3
"""
make_quartic_kernels.py

Writes the data of item (LIX), kernels on X x X for a quartic CM field, for
HodgeObstruction.lean.  The model is the one-place model of
code/attack/gaps/quartic_kernels/qk_place.py, which this script imports, with
d = p / q and classes scaled by powers of q.  It records

  * for d = 1, 2, 3, 5/2, 2/5 an integral basis of su_j(d) (fifteen matrices),
    a minor of size 15 of the basis and a minor of size 49 of the linear
    conditions defining su_j(d) (so the basis spans it), and a minor of size 3
    of eta^2, Omega, Lambda;
  * for d = 1, 3, 2/5 and each degree k = 1, ..., 7 a minor of the stacked
    derivations of degree k, of size C(8, k) minus the number of invariant
    classes of degree k, and a minor of size 62 of the conditions on the
    commutant;
  * for d = 1, 3 the minors and the kernel vectors over Z[i] of the
    contraction maps of w = ch Phi(T(d) - P) and of Omega + eta^2 / 3;
  * the 56 classes (b, a)_*(c) and their transforms, also as the rows of their
    coefficients on each monomial, and for them a minor of
    size 24 and 32 independent
    kernel vectors, and for d = 1, 3, 2/5 a minor of size 29 of the invariant
    classes together with the transforms; for the four twists e^B a minor of
    size 29 of the classes e^(-B) I, I invariant, together with the transforms,
    and the coefficients writing e^(-B) e^(g eta) in Phi(L);
  * for the pure spinors the minors of size 8 and the eight annihilating
    elements of V + V^*, and the minors of size 9 for the classes that are
    not pure.

Run from the repository root:  python3 lean/generate/make_quartic_kernels.py
"""
import os
import sys
from fractions import Fraction as Fr
from math import gcd
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "code", "attack", "gaps", "quartic_kernels"))
from qk_ext import popc, wedge, add, sc, sub, gen, one, derivation, interior  # noqa: E402
from qk_ext import nullspace_Q, field, rank_K, dict_rank_Q  # noqa: E402
from qk_place import (theta_x, thetahat, ell, eta, omega_w, su_basis, lin_to_mat,  # noqa: E402
                      mat_to_lin, Mstar, invariants, orlov, graph_class, W_class,
                      HT2_images, inv_basis)

P = 1000003
PG = 1000033
RG = 649529
DS = [(1, 1), (2, 1), (3, 1), (5, 2), (2, 5)]
DINV = [(1, 1), (3, 1), (2, 5)]
PAIRS = [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2), (3, 1)]
TWISTS = [((3, 1), (Fr(0), Fr(0), Fr(-1, 2))), ((3, 1), (Fr(1), Fr(1, 2), Fr(1, 3))),
          ((3, 1), (Fr(-2), Fr(1), Fr(-1, 2))), ((2, 5), (Fr(1, 3), Fr(-1), Fr(1, 2)))]
SPIN = [(1, 1, 0), (2, 1, 1), (1, -1, 2), (3, 2, -1), (1, 0, 1), (0, 1, 1), (2, 3, 1)]


def lcm(a, b):
    return a * b // gcd(a, b)


def integral(vals):
    den = 1
    for v in vals:
        den = lcm(den, Fr(v).denominator)
    xs = [int(Fr(v) * den) for v in vals]
    g = 0
    for x in xs:
        g = gcd(g, abs(x))
    return [x // g for x in xs] if g else xs


def pick_minor(rows, p=P, conv=lambda x: x % P, limit=None):
    """rows and columns of a nonsingular minor of maximal size modulo p
    (of size limit, when given)."""
    A = [[conv(x) for x in r] for r in rows]
    B = [r[:] for r in A]
    live = list(range(len(B)))
    rs, cs = [], []
    for j in range(len(B[0]) if B else 0):
        piv = next((i for i in live if B[i][j]), None)
        if piv is None:
            continue
        if limit is not None and len(rs) == limit:
            break
        live.remove(piv)
        rs.append(piv)
        cs.append(j)
        inv = pow(B[piv][j], p - 2, p)
        for i in live:
            if B[i][j]:
                f = B[i][j] * inv % p
                B[i] = [(a - f * b) % p for a, b in zip(B[i], B[piv])]
    return sorted(rs), sorted(cs)


def gmod(z):
    return (z[0] + RG * z[1]) % PG


def lst(x):
    return "[" + ", ".join(map(str, x)) + "]"


def mats(Bm):
    return "[" + ", ".join("[" + ", ".join(lst(r) for r in X) + "]" for X in Bm) + "]"


# ------------------------------------------------------------------ the model, as in Lean
def qeta(p, q):
    return add(sc(p, theta_x()), sc(q, thetahat()))


def qgamma(p, q):
    return add(sc(p, theta_x()), sc(-q, thetahat()))


def qomega(p, q):
    g = qgamma(p, q)
    return add(wedge(g, g), sc(-p * q, wedge(ell(), ell())))


def qinv(p, q):
    e = qeta(p, q)
    e2 = wedge(e, e)
    return [one(1), e, e2, qomega(p, q), wedge(qgamma(p, q), ell()), wedge(e, e2), wedge(e2, e2)]


def qM(p, q):
    M = lin_to_mat(Mstar(Fr(p, q)))
    return [[int(x * q) for x in r] for r in M]


def su_rows(p, q):
    M = qM(p, q)
    comm = []
    for ij in range(64):
        i, j = divmod(ij, 8)
        comm.append([(M[b][j] if a == i else 0) - (M[i][a] if b == j else 0)
                     for a, b in (divmod(ab, 8) for ab in range(64))])
    e = qeta(p, q)
    ders = []
    for ab in range(64):
        X = [[1 if 8 * i + j == ab else 0 for j in range(8)] for i in range(8)]
        ders.append(derivation(e, mat_to_lin(X)))
    mons = [m for m in range(256) if popc(m) == 2]
    drows = [[v.get(m, 0) for v in ders] for m in mons]
    tr = [M[ab % 8][ab // 8] for ab in range(64)]
    return comm + drows + [tr]


def su_int(p, q):
    out = []
    for X in su_basis(Fr(p, q)):
        Mx = lin_to_mat(X)
        flat = integral([Mx[i][j] for i in range(8) for j in range(8)])
        out.append([flat[8 * i:8 * i + 8] for i in range(8)])
    return out


def der(X, u):
    return derivation(u, mat_to_lin(X))


def main():
    out = []
    # ---------------------------------------------------------- su_j(d)
    sus = {}
    for (p, q) in DS:
        Bm = su_int(p, q)
        assert len(Bm) == 15
        rows = su_rows(p, q)
        for X in Bm:
            v = [X[i][j] for i in range(8) for j in range(8)]
            assert all(sum(r[k] * v[k] for k in range(64)) == 0 for r in rows)
        rs, cs = pick_minor(rows)
        assert len(rs) == 49
        brs, bcs = pick_minor([[X[i][j] for i in range(8) for j in range(8)] for X in Bm])
        assert len(brs) == 15
        sus[(p, q)] = Bm
        m4 = [m for m in range(256) if popc(m) == 4]
        I = qinv(p, q)
        im = pick_minor([[I[k].get(m, 0) for m in m4] for k in (2, 3, 4)])
        assert len(im[0]) == 3
        out.append("-- d = %d/%d" % (p, q))
        out.append("def qkSu_%d_%d : List (List (List Int)) := %s" % (p, q, mats(Bm)))
        out.append("def qkSuMinor_%d_%d : (List Nat × List Nat) × List Nat := ((%s, %s), %s)"
                   % (p, q, lst(rs), lst(cs), lst(bcs)))
        out.append("def qkInvIndep_%d_%d : List Nat := %s" % (p, q, lst(im[1])))
    # ---------------------------------------------------------- invariants and commutant
    for (p, q) in DINV:
        Bm = sus[(p, q)]
        invc = [1, 0, 1, 0, 3, 0, 1, 0, 1]
        mins = []
        for k in range(1, 8):
            ms = [m for m in range(256) if popc(m) == k]
            idx = {m: i for i, m in enumerate(ms)}
            rows = []
            for t, X in enumerate(Bm):
                imgs = [der(X, {m: 1}) for m in ms]
                for tgt in ms:
                    rows.append([im.get(tgt, 0) for im in imgs])
            rs, cs = pick_minor(rows)
            assert len(rs) == len(ms) - invc[k], (k, len(rs))
            mins.append((rs, cs))
        out.append("def qkInvMinors_%d_%d : List (List Nat × List Nat) := [%s]" % (
            p, q, ", ".join("(%s, %s)" % (lst(a), lst(b)) for a, b in mins)))
        rows = []
        for X in Bm:
            for ij in range(64):
                i, j = divmod(ij, 8)
                rows.append([(X[b][j] if a == i else 0) - (X[i][a] if b == j else 0)
                             for a, b in (divmod(ab, 8) for ab in range(64))])
        rs, cs = pick_minor(rows)
        assert len(rs) == 62
        out.append("def qkCommMinor_%d_%d : List Nat × List Nat := (%s, %s)" % (p, q, lst(rs), lst(cs)))
    out += part_rest()
    print("\n".join(out))


# ------------------------------------------------------------------ Gaussian classes
def gw(u, v):
    """wedge of classes with coefficients in Z[i], as dicts mask -> (re, im)."""
    outd = {}
    for k1, a in u.items():
        for k2, b in v.items():
            if k1 & k2:
                continue
            s = 0
            mm = k2
            while mm:
                j = (mm & -mm).bit_length() - 1
                s += popc(k1 >> (j + 1))
                mm &= mm - 1
            c = (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
            if s & 1:
                c = (-c[0], -c[1])
            o = outd.get(k1 | k2, (0, 0))
            outd[k1 | k2] = (o[0] + c[0], o[1] + c[1])
    return {k: c for k, c in outd.items() if c != (0, 0)}


def gint(u, vec):
    outd = {}
    for m, c in u.items():
        r = 0
        for j in range(8):
            if not (m >> j) & 1:
                continue
            a = vec[j]
            if a != (0, 0):
                t = (c[0] * a[0] - c[1] * a[1], c[0] * a[1] + c[1] * a[0])
                if r & 1:
                    t = (-t[0], -t[1])
                o = outd.get(m & ~(1 << j), (0, 0))
                outd[m & ~(1 << j)] = (o[0] + t[0], o[1] + t[1])
            r += 1
    return {k: c for k, c in outd.items() if c != (0, 0)}


def toG(u):
    return {k: (int(c), 0) for k, c in u.items()}


PAIRS_C = [(0, 2), (1, 3), (4, 6), (5, 7)]
QS = [{1 << r: (1, 0), 1 << s: (0, -1)} for r, s in PAIRS_C]
DSV = []
for r, s in PAIRS_C:
    v = [(0, 0)] * 8
    v[r] = (1, 0)
    v[s] = (0, -1)
    DSV.append(v)


def ht2(w):
    imgs = []
    for a in range(4):
        for b in range(a + 1, 4):
            imgs.append(gw(gw(QS[a], QS[b]), w))
    for a in range(4):
        for b in range(4):
            imgs.append(gw(QS[a], gint(w, DSV[b])))
    for a in range(4):
        for b in range(a + 1, 4):
            imgs.append(gint(gint(w, DSV[b]), DSV[a]))
    return imgs


def dense(u, n=256):
    return [u.get(m, (0, 0)) for m in range(n)]


def gnull(vecs):
    """kernel over Q(i) of the vectors (lists of Gaussian integers), scaled to Z[i]."""
    nc = len(vecs)
    nr = len(vecs[0])
    A = [[(Fr(vecs[j][i][0]), Fr(vecs[j][i][1])) for j in range(nc)] for i in range(nr)]

    def mul(x, y):
        return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])

    def inv(x):
        n = x[0] * x[0] + x[1] * x[1]
        return (x[0] / n, -x[1] / n)
    piv, r = [], 0
    for c in range(nc):
        pr = next((i for i in range(r, nr) if A[i][c] != (0, 0)), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        iv = inv(A[r][c])
        A[r] = [mul(iv, x) for x in A[r]]
        for i in range(nr):
            if i != r and A[i][c] != (0, 0):
                f = A[i][c]
                A[i] = [(x[0] - mul(f, y)[0], x[1] - mul(f, y)[1]) for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    res = []
    for fc in [c for c in range(nc) if c not in piv]:
        v = [(Fr(0), Fr(0))] * nc
        v[fc] = (Fr(1), Fr(0))
        for i, c in enumerate(piv):
            v[c] = (-A[i][fc][0], -A[i][fc][1])
        den = 1
        for x in v:
            for y in x:
                den = lcm(den, y.denominator)
        w = [(int(x[0] * den), int(x[1] * den)) for x in v]
        g = 0
        for x in w:
            g = gcd(g, gcd(abs(x[0]), abs(x[1])))
        res.append([(x[0] // g, x[1] // g) for x in w])
    return res


def gcheck_ker(vecs, k):
    tot = [(0, 0)] * len(vecs[0])
    for c, v in zip(k, vecs):
        tot = [(t[0] + c[0] * x[0] - c[1] * x[1], t[1] + c[0] * x[1] + c[1] * x[0]) for t, x in zip(tot, v)]
    return all(t == (0, 0) for t in tot)


def glist(v):
    return "[" + ", ".join("(%d, %d)" % x for x in v) + "]"


def qnull(vecs):
    """integer kernel vectors of the given integer vectors."""
    ns = nullspace_Q([[v[i] for v in vecs] for i in range(len(vecs[0]))], len(vecs))
    return [integral(n) for n in ns]


def ivec(u, n=256):
    return [int(u.get(m, 0)) for m in range(n)]


def even_x():
    return [one(1)] + [wedge(gen(i), gen(j)) for i in range(4) for j in range(i + 1, 4)] + [{15: 1}]


def exp_scaled(G, s):
    """24 s^4 e^(G / s) for an integral even class G (degree four or less in G)."""
    coef = [24 * s ** 4, 24 * s ** 3, 12 * s ** 2, 4 * s, 1]
    t = one(1)
    tot = {}
    for k in range(5):
        tot = add(tot, sc(coef[k], t))
        t = wedge(t, G)
    assert not t
    return tot


def part_rest():
    out = []
    # ---------------------------------------------------------- contraction, d = 1, 3
    for d in (1, 3):
        e = qeta(d, 1)
        w = add(wedge(e, e), qomega(d, 1))           # -ch Phi(4 (T - P)), scaled
        assert {k: -v for k, v in orlov(W_class(Fr(d))).items()} == {k: Fr(v, 4) for k, v in w.items()}
        g3 = add(sc(3, qomega(d, 1)), wedge(e, e))
        iw, ig = ht2(toG(w)), ht2(toG(g3))
        dw, dg = [dense(x) for x in iw], [dense(x) for x in ig]
        kw, kg = gnull(dw), gnull(dg)
        assert len(kw) == 5 and len(kg) == 4
        assert all(gcheck_ker(dw, k) for k in kw + kg) and all(gcheck_ker(dg, k) for k in kg)
        assert all(all(k[i] == (0, 0) for i in list(range(6)) + list(range(22, 28))) for k in kw + kg)
        mw = pick_minor(dw, PG, gmod)
        mg = pick_minor(dg, PG, gmod)
        st = [a + b for a, b in zip(dw, dg)]
        ms = pick_minor(st, PG, gmod)
        assert (len(mw[0]), len(mg[0]), len(ms[0])) == (23, 24, 24)
        mkw = pick_minor(kw, PG, gmod)
        mkg = pick_minor(kg, PG, gmod)
        assert len(mkw[0]) == 5 and len(mkg[0]) == 4
        out.append("def qkContr_%d : (List Nat × List Nat) × (List Nat × List Nat) × (List Nat × List Nat) := "
                   "((%s, %s), (%s, %s), (%s, %s))" % (d, lst(mw[0]), lst(mw[1]), lst(mg[0]), lst(mg[1]),
                                                     lst(ms[0]), lst(ms[1])))
        out.append("def qkContrKerW_%d : List (List (Int × Int)) := [%s]" % (d, ", ".join(glist(k) for k in kw)))
        out.append("def qkContrKerG_%d : List (List (Int × Int)) := [%s]" % (d, ", ".join(glist(k) for k in kg)))
        out.append("def qkContrKerRows_%d : List Nat × List Nat := (%s, %s)" % (d, lst(mkw[1]), lst(mkg[1])))
    # ---------------------------------------------------------- graphs
    L = [graph_class(b, a, c) for b, a in PAIRS for c in even_x()]
    PL = [orlov(z) for z in L]
    Lv = [ivec(z) for z in L]
    kl = qnull(Lv)
    assert len(kl) == 32
    for k in kl:
        assert all(sum(c * v[i] for c, v in zip(k, Lv)) == 0 for i in range(256))
    mkl = pick_minor(kl)
    ml = pick_minor(Lv)
    assert len(mkl[0]) == 32 and len(ml[0]) == 24
    def sparse(u):
        return "[" + ", ".join("(%d, %d)" % (m, int(c)) for m, c in sorted(u.items()) if c) + "]"
    out.append("def qkLData : List (List (Nat × Int)) := [%s]" % ", ".join(sparse(z) for z in L))
    out.append("def qkPLData : List (List (Nat × Int)) := [%s]" % ", ".join(sparse(orlov(z)) for z in L))
    def rows_of(vs):
        R = []
        for m in range(256):
            row = [int(v.get(m, 0)) for v in vs]
            if any(row):
                R.append("(%d, %s)" % (m, lst(row)))
        return "[" + ", ".join(R) + "]"
    out.append("def qkLRows : List (Nat × List Int) := %s" % rows_of(L))
    out.append("def qkPLRows : List (Nat × List Int) := %s" % rows_of(PL))
    out.append("def qkGraphKer : List (List Int) := [%s]" % ", ".join(lst(k) for k in kl))
    out.append("def qkGraphMinors : List Nat × (List Nat × List Nat) := (%s, (%s, %s))"
               % (lst(mkl[1]), lst(ml[0]), lst(ml[1])))
    inter = []
    for (p, q) in DINV:
        vs = [ivec(v) for v in qinv(p, q)] + [ivec(v) for v in PL]
        m = pick_minor(vs)
        assert len(m[0]) == 29
        inter.append(m)
    out.append("def qkGraphInter : List (List Nat × List Nat) := [%s]" % ", ".join(
        "(%s, %s)" % (lst(a), lst(b)) for a, b in inter))
    tw = []
    for (p, q), (f, g, h) in TWISTS:
        # e^B Phi(L) meets the invariants in e^(g eta) span(1, pt) if and only if Phi(L)
        # meets e^(-B) Inv in e^(-B) e^(g eta) span(1, pt), with e^(-B) pt = pt
        Bm6 = add(sc(-int(6 * f), theta_x()), sc(-int(6 * g), thetahat()), sc(-int(6 * h), ell()))
        Em = exp_scaled(Bm6, 6)                      # 31104 e^(-B)
        gq = g / q
        Eg = exp_scaled(sc(gq.numerator, qeta(p, q)), gq.denominator)   # 24 den^4 e^(g eta)
        vs = [ivec(wedge(Em, v)) for v in qinv(p, q)] + [ivec(v) for v in PL]
        m = pick_minor(vs)
        assert len(m[0]) == 29
        cols = [ivec(v) for v in PL] + [ivec(wedge(Em, Eg))]
        dep = [k for k in qnull(cols) if k[-1] != 0]
        assert dep
        k = dep[0]
        assert all(sum(c * x[i] for c, x in zip(k, cols)) == 0 for i in range(256))
        tw.append((m, k))
    out.append("def qkTwists : List ((Int × Int) × (Int × Int × Int) × (Int × Int)) := [%s]" % ", ".join(
        "((%d, %d), (%d, %d, %d), (%d, %d))" % (p, q, int(6 * f), int(6 * g), int(6 * h),
                                               (g / q).numerator, (g / q).denominator)
        for (p, q), (f, g, h) in TWISTS))
    out.append("def qkTwistData : List ((List Nat × List Nat) × List Int) := [%s]" % ", ".join(
        "((%s, %s), %s)" % (lst(m[0]), lst(m[1]), lst(k)) for m, k in tw))
    # ---------------------------------------------------------- pure spinors
    def imgs(v):
        return [wedge(gen(i), v) for i in range(8)] + [interior(v, {i: 1}) for i in range(8)]
    eh = add(one(384), sc(192, ell()), sc(48, wedge(ell(), ell())), sc(8, wedge(wedge(ell(), ell()), ell())),
             wedge(wedge(ell(), ell()), wedge(ell(), ell())))
    sp = []
    for b, a, c in SPIN:
        ec = add(one(1), sc(c, theta_x()), {15: -c * c})
        v = orlov(graph_class(b, a, ec))
        for u in (v, wedge(v, eh)):
            ivs = [ivec(x) for x in imgs(u)]
            m = pick_minor(ivs)
            assert len(m[0]) == 8
            ker = qnull(ivs)
            assert len(ker) == 8
            mk = pick_minor(ker)
            assert len(mk[0]) == 8
            sp.append((m, ker, mk[1]))
    out.append("def qkSpinData : List ((List Nat × List Nat) × List (List Int) × List Nat) := [%s]" % ", ".join(
        "((%s, %s), [%s], %s)" % (lst(m[0]), lst(m[1]), ", ".join(lst(k) for k in ker), lst(r))
        for m, ker, r in sp))
    e = qeta(1, 1)
    w1 = add(wedge(e, e), qomega(1, 1))
    nonpure = []
    for u in (w1, qomega(1, 1)):
        m = pick_minor([ivec(x) for x in imgs(u)], limit=9)
        assert len(m[0]) == 9
        nonpure.append(m)
        assert len(pick_minor([[ivec(x)[c] for c in m[1]] for x in [imgs(u)[r] for r in m[0]]])[0]) == 9
    x = gw(toG(qgamma(1, 1)), {})
    x = {k: c for k, c in toG(qgamma(1, 1)).items()}
    for k, c in toG(ell()).items():
        o = x.get(k, (0, 0))
        x[k] = (o[0], o[1] - c[0])
    x2 = gw(x, x)
    gi = [gw({1 << i: (1, 0)}, x2) for i in range(8)]
    for i in range(8):
        v = [(0, 0)] * 8
        v[i] = (1, 0)
        gi.append(gint(x2, v))
    dg = [dense(t) for t in gi]
    m = pick_minor(dg, PG, gmod)
    assert len(m[0]) == 8
    kg = gnull(dg)
    assert len(kg) == 8 and all(gcheck_ker(dg, k) for k in kg)
    mk = pick_minor(kg, PG, gmod)
    assert len(mk[0]) == 8
    out.append("def qkNonPure : List (List Nat × List Nat) := [%s]" % ", ".join(
        "(%s, %s)" % (lst(a), lst(b)) for a, b in nonpure))
    out.append("def qkWeilSpin : (List Nat × List Nat) × List (List (Int × Int)) × List Nat := ((%s, %s), [%s], %s)"
               % (lst(m[0]), lst(m[1]), ", ".join(glist(k) for k in kg), lst(mk[1])))
    return out


if __name__ == "__main__":
    main()
