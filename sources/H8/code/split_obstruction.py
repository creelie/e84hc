#!/usr/bin/env python3
"""
split_obstruction.py

The first-order obstruction map of a sum of line bundles on a split member,
against the tangent space of the Weil family.  Item (XXV).

Model.  The split member A = X x Xhat with X = E_i^n, over F_p with a square
root of -1, exactly as in semireg_fast.py.  The three divisor classes are
beta, betahat, ell; the Weil polarisation is eta = d beta + betahat and the
Weil line is spanned by omega_1, omega_2, the real and imaginary parts of
(gamma - sqrt(-d) ell)^n with gamma = d beta - betahat.

A first-order deformation of A is v in Hom(H^{1,0}, H^{0,1}), extended by
zero on H^{0,1} and acting on forms as a derivation; we write v _| xi.

  T      = { v : v _| eta = 0, v _| omega_1 = 0, v _| omega_2 = 0 }
           the polarised deformations killing the Weil line, which is the
           tangent space to the Weil family, of dimension n^2
           (Proposition "first-order Hodge locus" and Theorem "annihilator
           is the tangent space");
  T_spl  = { v : v _| beta = v _| betahat = v _| ell = 0 }
           the deformations keeping all three divisor classes of type (1,1),
           which is the tangent space to the split locus, of dimension
           n(n+1)/2, and lies inside T;
  ob_E   : T -> (+)_i H^{0,2},  v |-> ( v _| lambda_i )_i
           the first-order obstruction to deforming E = (+) L_i[p_i] along
           v, lambda_i = c_1(L_i); it is the Atiyah class of E, which is
           diagonal with entries lambda_i, contracted with v;
  sigma_E: (+)_i H^{0,2} -> H^*(A),  (zeta_i) |-> sum_i (-1)^{p_i} zeta_i
           e^{lambda_i},  the semiregularity map of the split object;
  Delta  = { (z, ..., z) : z in Ann(omega_1) }  the copy of T inside
           ker sigma_E of the Corollary "kernel contains the tangent space".

Checks.

  (O1) dim T = n^2, dim T_spl = n(n+1)/2 and T_spl is contained in T, for
       (n, d) = (2,1), (2,3), (3,3).
  (O2) For line bundle classes lambda_i that, together with eta, span
       NS(A)_Q, the kernel of ob_E is exactly T_spl and the rank of ob_E is
       n(n-1)/2, the codimension of the split locus; for the same (n, d).
  (O3) For the explicit object of the paper at n = 3, d = 3 (six classes
       lambda_1, lambda_2, lambda_3, -lambda_1, -lambda_2, -lambda_3, the
       last three shifted by 3): ker ob_E = T_spl of dimension 6, rank 3;
       sigma_E kills the image of ob_E; sigma_E kills Delta, which has
       dimension 9; the image of ob_E meets Delta only in zero, so
       Delta (+) im(ob_E) is a 12-dimensional subspace of ker sigma_E; and
       ker sigma_E has dimension exactly 15, so three dimensions of it lie
       outside both.
"""

import sys
from itertools import combinations
from math import comb

import semireg_fast as S
from semireg_fast import P, wedge, eadd, escale, inv, matinv, rank_mod


# --------------------------------------------------------- linear algebra

def nullspace(M, ncols):
    rows = [[v % P for v in r] for r in M]
    piv, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        iv = inv(rows[r][c])
        rows[r] = [x * iv % P for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [0] * ncols
        v[f] = 1
        for i, c in enumerate(piv):
            v[c] = (-rows[i][f]) % P
        basis.append(v)
    return basis


def rank_rows(vecs):
    """Rank of a list of equal-length integer vectors modulo P."""
    if not vecs:
        return 0
    cols = [{i: v for i, v in enumerate(vec) if v % P} for vec in vecs]
    return rank_mod(cols)


# ------------------------------------------------------------ the model

class Deform:
    """Deformations v in Hom(H^{1,0}, H^{0,1}) of the split model."""

    def __init__(self, n, d):
        self.mf = S.Model(n, d)
        mf = self.mf
        self.n, self.d, self.N, self.m = n, d, mf.N, mf.m
        cols = mf.H10 + mf.H01
        Mst = [[cols[j].get(1 << i, 0) for j in range(self.N)]
               for i in range(self.N)]
        self.Minv = matinv(Mst)
        # the Weil line
        w1, w2 = {}, {}
        for j in range(n + 1):
            term = wedge(S.epow(mf.gamma, n - j), S.epow(mf.ell, j))
            if j % 2 == 0:
                w1 = eadd(w1, escale((comb(n, j) * ((-d) ** (j // 2))) % P,
                                     term))
            else:
                w2 = eadd(w2, escale((comb(n, j) * ((-d) ** ((j - 1) // 2)))
                                     % P, term))
        self.w1, self.w2 = w1, w2

    def columns(self, c):
        """v given by the m x m matrix c (flat list), v(H10[j]) =
        sum_k c[j*m+k] H01[k]; returns v(e_i) for the standard generators."""
        mf, m, N = self.mf, self.m, self.N
        out = []
        for i in range(N):
            co = [self.Minv[j][i] for j in range(N)]
            w = {}
            for j in range(m):
                cj = co[j] % P
                if not cj:
                    continue
                for k in range(m):
                    ck = c[j * m + k] % P
                    if ck:
                        w = eadd(w, escale(cj * ck % P, mf.H01[k]))
            out.append(w)
        return out

    @staticmethod
    def contract(colsv, form):
        """v _| form for the derivation v with v(e_j) = colsv[j]."""
        out = {}
        for key, coef in form.items():
            idx = []
            mm = key
            while mm:
                low = mm & -mm
                idx.append(low.bit_length() - 1)
                mm ^= low
            for t, j in enumerate(idx):
                term = {0: coef % P}
                for s_, jj in enumerate(idx):
                    piece = colsv[jj] if s_ == t else {1 << jj: 1}
                    term = wedge(term, piece)
                    if not term:
                        break
                out = eadd(out, term)
        return out

    def solve(self, forms, inside=None):
        """Basis of { v : v _| f = 0 for f in forms }, as flat matrices; if
        `inside` is a list of such matrices, the solution is sought in their
        span and returned in the same flat form."""
        m = self.m
        if inside is None:
            gens = []
            for u in range(m * m):
                c = [0] * (m * m)
                c[u] = 1
                gens.append(c)
        else:
            gens = inside
        images = [[self.contract(self.columns(c), f) for f in forms]
                  for c in gens]
        keys = [sorted({k for im in images for k in im[fi]})
                for fi in range(len(forms))]
        M = []
        for fi in range(len(forms)):
            for key in keys[fi]:
                M.append([images[u][fi].get(key, 0) for u in range(len(gens))])
        sol = nullspace(M, len(gens)) if M else \
            [[1 if i == j else 0 for j in range(len(gens))]
             for i in range(len(gens))]
        out = []
        for s in sol:
            v = [0] * (m * m)
            for coef, g_ in zip(s, gens):
                if coef % P:
                    v = [(a + coef * b) % P for a, b in zip(v, g_)]
            out.append(v)
        return out

    def tangent(self):
        return self.solve([self.mf.eta, self.w1, self.w2])

    def split_tangent(self):
        mf = self.mf
        return self.solve([mf.beta, mf.betahat, mf.ell])

    def obstruction(self, T, lams):
        """The vectors ob_E(v) for v in T, each a list of dicts, one per
        lambda_i, together with the rank of ob_E."""
        images = []
        for v in T:
            cv = self.columns(v)
            images.append([self.contract(cv, L) for L in lams])
        # rank: flatten into one long coordinate vector per v
        keys = [sorted({k for im in images for k in im[i]})
                for i in range(len(lams))]
        vecs = []
        for im in images:
            vec = []
            for i in range(len(lams)):
                vec.extend(im[i].get(k, 0) for k in keys[i])
            vecs.append(vec)
        return images, rank_rows(vecs)


def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    return (1, 0) if ok else (0, 1)


def flatten(dicts, keys):
    vec = []
    for dct, ks in zip(dicts, keys):
        vec.extend(dct.get(k, 0) for k in ks)
    return vec


def main():
    print("the obstruction map of a split object against the Weil family")
    NP = NF = 0

    print("  (O1) the two tangent spaces")
    rows, ok = [], True
    models = {}
    for (n, d) in [(2, 1), (2, 3), (3, 3)]:
        D = Deform(n, d)
        T = D.tangent()
        Ts = D.split_tangent()
        contained = rank_rows(T + Ts) == len(T)
        good = (len(T) == n * n and len(Ts) == n * (n + 1) // 2 and contained)
        ok = ok and good
        rows.append("n=%d, d=%d: dim T = %d [n^2 = %d], dim T_spl = %d "
                    "[n(n+1)/2 = %d], T_spl inside T: %s"
                    % (n, d, len(T), n * n, len(Ts), n * (n + 1) // 2,
                       contained))
        models[(n, d)] = (D, T, Ts)
    p, f = check("dim T = n^2, dim T_spl = n(n+1)/2, and T_spl lies in T",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    # the control: with beta + d betahat in place of eta, which is the
    # polarisation of the other placement of the factor d, the system
    # mixes two K-actions and the solution space collapses to T_spl
    rows, ok = [], True
    for (n, d), (D, T, Ts) in models.items():
        mf = D.mf
        mixed = eadd(mf.beta, escale(d, mf.betahat))
        Tm = D.solve([mixed, D.w1, D.w2])
        expect = n * n if d == 1 else n * (n + 1) // 2
        ok = ok and len(Tm) == expect
        rows.append("n=%d, d=%d: with beta + d betahat: dim %d [expected %d]"
                    % (n, d, len(Tm), expect))
    p, f = check("control: pairing the Weil line of gamma with the class "
                 "beta + d betahat cuts the dimension to n(n+1)/2 for d > 1",
                 ok, "\n".join(rows))
    NP += p
    NF += f

    print("  (O2) the rank of the obstruction map when the classes span")
    rows, ok = [], True
    for (n, d), (D, T, Ts) in models.items():
        mf = D.mf
        # classes spanning NS together with eta: gamma, ell and one more
        lams = [mf.gamma, mf.ell, mf.klass((1, 2, -1))]
        images, rk = D.obstruction(T, lams)
        # kernel of ob_E inside T
        ker = D.solve(lams, inside=T)
        kernel_is_split = (len(ker) == len(Ts)
                           and rank_rows(ker + Ts) == len(Ts))
        good = (rk == n * (n - 1) // 2 and kernel_is_split)
        ok = ok and good
        rows.append("n=%d, d=%d: rank ob_E = %d [n(n-1)/2 = %d], "
                    "dim ker = %d, ker = T_spl: %s"
                    % (n, d, rk, n * (n - 1) // 2, len(ker), kernel_is_split))
    p, f = check("ker ob_E = T_spl and rank ob_E = n(n-1)/2 for classes "
                 "spanning NS(A)_Q with eta", ok, "\n".join(rows))
    NP += p
    NF += f

    rows, ok = [], True
    for (n, d), (D, T, Ts) in models.items():
        mf = D.mf
        singles = [("gamma", mf.gamma), ("ell", mf.ell),
                   ("gamma + ell", eadd(mf.gamma, mf.ell)),
                   ("gamma + 2 ell", eadd(mf.gamma, escale(2, mf.ell))),
                   ("beta", mf.beta), ("betahat", mf.betahat),
                   ("beta + ell", eadd(mf.beta, mf.ell))]
        dims = []
        for name, th in singles:
            ker = D.solve([th], inside=T)
            same = (len(ker) == len(Ts) and rank_rows(ker + Ts) == len(Ts))
            ok = ok and same
            dims.append(len(ker))
        rows.append("n=%d, d=%d: kernels of v -> v _| theta on T for the "
                    "seven classes: %s [T_spl = %d]"
                    % (n, d, dims, len(Ts)))
    p, f = check("a single class theta not proportional to eta already cuts "
                 "T down to T_spl", ok, "\n".join(rows))
    NP += p
    NF += f

    # the mechanism of the line bundle theorem: for every rational class
    # theta = a beta + b betahat + c ell that is not a multiple of eta, the
    # contraction v -> v _| theta is nonzero on T, while for theta = t eta it
    # vanishes on all of T
    import random
    random.seed(29)
    rows, ok = [], True
    for (n, d), (D, T, Ts) in models.items():
        mf = D.mf
        bad = 0
        tried = 0
        for _ in range(150):
            a, b, c = (random.randint(-6, 6) for _ in range(3))
            if (a, b, c) == (0, 0, 0) or (c == 0 and a == d * b):
                continue                     # zero, or a multiple of eta
            tried += 1
            th = mf.klass((a, b, c))
            ker = D.solve([th], inside=T)
            if len(ker) == len(T):
                bad += 1
        keta = D.solve([mf.eta], inside=T)
        keta2 = D.solve([escale(3, mf.eta)], inside=T)
        good = (bad == 0 and len(keta) == len(T) and len(keta2) == len(T))
        ok = ok and good
        rows.append("n=%d, d=%d: %d random classes off Q eta, each contracts "
                    "nontrivially with T; eta and 3 eta contract to zero"
                    % (n, d, tried))
    p, f = check("every rational divisor class off Q eta is contracted "
                 "nontrivially by some tangent vector of the Weil family, "
                 "and multiples of eta by none", ok, "\n".join(rows))
    NP += p
    NF += f

    print("  (O3) the explicit object at n = 3, d = 3")
    D, T, Ts = models[(3, 3)]
    mf = D.mf
    obj = [(3, -1, 3), (-6, 2, 0), (3, -1, -3)]
    lam3 = [mf.klass(t) for t in obj]
    lams6 = lam3 + [escale(P - 1, L) for L in lam3]
    signs = [1, 1, 1, P - 1, P - 1, P - 1]          # (-1)^{p_i}, p = 0, 0, 0, 3, 3, 3
    images, rk = D.obstruction(T, lams6)
    ker = D.solve(lam3, inside=T)
    kernel_is_split = (len(ker) == len(Ts) and rank_rows(ker + Ts) == len(Ts))
    p, f = check("ker ob_E = T_spl (dimension 6) and rank ob_E = 3",
                 rk == 3 and kernel_is_split,
                 "rank %d, dim ker %d, ker = T_spl: %s"
                 % (rk, len(ker), kernel_is_split))
    NP += p
    NF += f

    # coordinates on (+)_i H^{0,2}: the standard degree two monomials
    keys2 = sorted({(1 << a) | (1 << b) for a, b in combinations(range(mf.N), 2)})
    keys6 = [keys2] * 6

    def sigma(zetas):
        tot = {}
        for i, (z, L) in enumerate(zip(zetas, lams6)):
            tot = eadd(tot, escale(signs[i], wedge(z, mf.expcl(L))))
        return tot

    ob_vecs = [flatten(im, keys6) for im in images]
    ok_sigma_ob = all(not sigma(im) for im in images)
    p, f = check("sigma_E kills the image of ob_E, as sigma_E(ob_E(v)) = "
                 "v _| ch(E) and ch(E) lies on the Weil line",
                 ok_sigma_ob)
    NP += p
    NF += f

    # Delta: z . id_E for z in the annihilator of omega_1 in H^{0,2}
    zb = mf.h02()
    ann_cols = [wedge(z, D.w1) for z in zb]
    ann = nullspace([[c.get(k, 0) for c in ann_cols]
                     for k in sorted({k for c in ann_cols for k in c})],
                    len(zb))
    ann_forms = []
    for a in ann:
        z = {}
        for coef, zz in zip(a, zb):
            if coef % P:
                z = eadd(z, escale(coef, zz))
        ann_forms.append(z)
    delta_vecs = [flatten([z] * 6, keys6) for z in ann_forms]
    ok_delta = (len(ann) == 9 and all(not sigma([z] * 6) for z in ann_forms))
    p, f = check("Delta = { z . id_E : z in Ann(omega_1) } has dimension 9 "
                 "and lies in ker sigma_E", ok_delta,
                 "dim Ann(omega_1) = %d" % len(ann))
    NP += p
    NF += f

    dim_sum = rank_rows(delta_vecs + ob_vecs)
    p, f = check("Delta and im(ob_E) meet only in zero: dim(Delta + im) = "
                 "9 + 3 = 12", dim_sum == 12, "dim(Delta + im(ob_E)) = %d"
                 % dim_sum)
    NP += p
    NF += f

    # the full kernel of sigma_E
    cols_sigma = []
    for i, L in enumerate(lams6):
        e = mf.expcl(L)
        for z in zb:
            cols_sigma.append(escale(signs[i], wedge(e, z)))
    r_sigma = rank_mod(cols_sigma)
    kdim = len(cols_sigma) - r_sigma
    p, f = check("ker sigma_E has dimension 15, so Delta (+) im(ob_E) is a "
                 "12-dimensional subspace of it with a 3-dimensional "
                 "complement", kdim == 15 and dim_sum == 12,
                 "rank %d of %d, kernel %d" % (r_sigma, len(cols_sigma), kdim))
    NP += p
    NF += f

    # the two components on L_i and on L_i^{-1}[3] are negatives, so no
    # vector of the diagonal shape (z, ..., z) other than zero is in the image
    anti = True
    for im in images:
        for i in range(3):
            if eadd(im[i], im[3 + i]):
                anti = False
    p, f = check("ob_E(v) has opposite components on L_i and on L_i^{-1}[3], "
                 "so a uniform shift of all six components cancels it only "
                 "when it is zero", anti)
    NP += p
    NF += f

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
