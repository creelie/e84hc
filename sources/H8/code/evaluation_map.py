#!/usr/bin/env python3
"""
evaluation_map.py

The evaluation map of Hochschild cohomology on the explicit split object, and
the weakened semiregularity criterion of Markman's Question 11.4.  Item
(XXVI).

Setting.  For a coherent sheaf or perfect complex E on a smooth projective Y,
Markman (arXiv:2509.23403, Section 11.4) writes ev_E : HH^2(Y) -> Ext^2(E,E)
for the evaluation of a natural transformation id -> id[2] on E, and records
the commutative square

        HH^2(Y)  --ev_E-->  Ext^2(E,E)
          | HKR                | sigma_E
        HT^2(Y)  --_|ch(E)-->  (+)_q H^{q,q+2}(Y)

with HT^2(Y) = H^2(O_Y) (+) H^1(T_Y) (+) H^0(wedge^2 T_Y), valid on an
abelian variety where the Todd class is trivial.  His Lemma 11.3 says that E
is semiregular when ker(ev_E) = ker(_|ch(E) o HKR) and ev_E is surjective;
Question 11.4 asks whether the semiregularity theorem survives when sigma_E
is only required to be injective on the image of ev_E.

For E = (+)_i L_i[p_i] a sum of shifted line bundles with lambda_i = c_1(L_i)
the Atiyah class is diagonal with entries lambda_i, and ev_E is diagonal:

    ev_E(z, v, pi)_i = z + v _| lambda_i + (1/2) pi _| (lambda_i ^ lambda_i),

where z in H^{0,2} acts through the O-module structure, v in H^1(T) =
Hom(H^{1,0}, H^{0,1}) acts on forms as a derivation, and the bivector
pi in H^0(wedge^2 T) = wedge^2 (H^{1,0})^dual acts by double contraction;
sigma_E(zeta) = sum_i (-1)^{p_i} zeta_i e^{lambda_i}.  Since v and pi act on
e^lambda by (v _| lambda) e^lambda and ((1/2) pi _| lambda^2) e^lambda,
one has sigma_E(ev_E(x)) = x _| ch(E) for every x in HT^2, which is the
square above, and so

    ker(sigma_E) meet im(ev_E) = ev_E( ker( _|ch(E) o HKR ) ).

The weakened criterion of Question 11.4 holds for E exactly when this space
is zero.

Checks, in the model of item (XIII) at n = 3, d = 3 (X = E_i^3, everything
modulo a prime p = 1 mod 4, in the Hodge basis of H^1):

  (E1) the square commutes: sigma_E(ev_E(x)) = x _| ch(E) for every basis
       vector x of HT^2, which has dimension 15 + 36 + 15 = 66;
  (E2) dim Ext^2(E,E) = 6 * 15 = 90 > 66, so ev_E is not surjective and
       Lemma 11.3 cannot apply; the rank of ev_E is computed;
  (E3) ker(_|ch(E) o HKR) splits by degree into Ann(omega_1) in H^{0,2}, of
       dimension 9, the deformations v with v _| omega_1 = 0, of dimension
       18 = 2n^2, and the bivectors pi with pi _| omega_1 = 0;
  (E4) the dimension of ev_E(ker(_|ch(E) o HKR)) = ker(sigma_E) meet
       im(ev_E), against dim ker(sigma_E) = 15: how many of the fifteen
       kernel dimensions lie in the image of ev_E, which is the extent to
       which E fails the weakened criterion;
  (E5) the contribution of each of the three summands of HT^2 separately:
       ev_E(Ann(omega_1)) has dimension 9 (the copy of the tangent space),
       ev_E of the deformation kernel has dimension 3 on the polarised
       K-commuting part T and is computed on the whole 18-dimensional
       kernel, and ev_E of the bivector kernel is computed;
  (E6) the same for every configuration lambda_i = s_i gamma + c_i ell in
       the box of item (XIV) whose virtual Chern character lies on the Weil
       line: for each, dim ker(sigma_E) and dim(ker(sigma_E) meet im(ev_E))
       are computed and compared.
"""

import random
import sys
from itertools import combinations

import semireg_fast as S
from semireg_fast import P, wedge, eadd, escale, inv, rank_mod


def bits(m):
    out = []
    while m:
        low = m & -m
        out.append(low.bit_length() - 1)
        m ^= low
    return out


def interior(a, u):
    """The interior product with the vector dual to generator a."""
    out = {}
    for m, c in u.items():
        if not (m >> a) & 1:
            continue
        below = bin(m & ((1 << a) - 1)).count("1")
        s = c if below % 2 == 0 else (-c) % P
        k = m ^ (1 << a)
        out[k] = (out.get(k, 0) + s) % P
    return {k: c for k, c in out.items() if c}


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
    if not vecs:
        return 0
    return rank_mod([{i: v for i, v in enumerate(vec) if v % P}
                     for vec in vecs])


class HodgeModel:
    """The split model of semireg_fast rewritten in its Hodge basis: bits
    0..m-1 are the (1,0) generators p_a, bits m..2m-1 the (0,1) generators
    q_a."""

    def __init__(self, n, d):
        self.mf = S.Model(n, d)
        self.n, self.d, self.m = n, d, 2 * n
        mf = self.mf
        self.eta = mf.to_hodge(mf.eta)
        # the Weil line, from the closed form, then to the Hodge basis
        from math import comb
        w1, w2 = {}, {}
        for j in range(n + 1):
            term = wedge(S.epow(mf.gamma, n - j), S.epow(mf.ell, j))
            if j % 2 == 0:
                w1 = eadd(w1, escale((comb(n, j) * ((-d) ** (j // 2))) % P,
                                     term))
            else:
                w2 = eadd(w2, escale((comb(n, j) * ((-d) ** ((j - 1) // 2)))
                                     % P, term))
        self.w1, self.w2 = mf.to_hodge(w1), mf.to_hodge(w2)

    def klass(self, t):
        return self.mf.to_hodge(self.mf.klass(t))

    # ---- the three kinds of elements of HT^2 and their actions
    def h02_basis(self):
        m = self.m
        return [{(1 << (m + a)) | (1 << (m + b)): 1}
                for a, b in combinations(range(m), 2)]

    def deriv(self, c, u):
        """v with v(p_a) = sum_b c[a*m+b] q_b, as a derivation on u."""
        m = self.m
        out = {}
        for a in range(m):
            ia = interior(a, u)
            if not ia:
                continue
            va = {1 << (m + b): c[a * m + b] % P for b in range(m)
                  if c[a * m + b] % P}
            if va:
                out = eadd(out, wedge(va, ia))
        return out

    def bivec(self, pc, u):
        """pi = sum_{a<b} pc[(a,b)] d_a ^ d_b acting by double contraction
        iota_b iota_a."""
        out = {}
        for (a, b), coef in pc.items():
            if coef % P:
                out = eadd(out, escale(coef, interior(b, interior(a, u))))
        return out

    def expcl(self, lam):
        out, pw, fact = {0: 1}, {0: 1}, 1
        for k in range(1, 2 * self.n + 1):
            pw = wedge(pw, lam)
            fact = fact * k % P
            out = eadd(out, escale(inv(fact), pw))
        return out


def check(name, ok, detail=""):
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    return (1, 0) if ok else (0, 1)


def main():
    print("the evaluation map and the weakened semiregularity criterion")
    NP = NF = 0
    random.seed(11)
    n, d = 3, 3
    H = HodgeModel(n, d)
    m = H.m
    obj = [(3, -1, 3), (-6, 2, 0), (3, -1, -3)]
    L3 = [H.klass(t) for t in obj]
    L6 = L3 + [escale(P - 1, L) for L in L3]
    signs = [1, 1, 1, P - 1, P - 1, P - 1]
    E6 = [H.expcl(L) for L in L6]
    ch = {}
    for s, e in zip(signs, E6):
        ch = eadd(ch, escale(s, e))
    # ch(E) is concentrated in degree 2n and proportional to omega_1 (the
    # factor is 12 for the primitive integral generator of item (XIII); the
    # generator here is Re (gamma - sqrt(-d) ell)^n without normalisation)
    degs = sorted({bin(k).count("1") for k in ch})
    k0 = next(iter(H.w1))
    r = ch.get(k0, 0) * inv(H.w1[k0]) % P
    ok_ch = (degs == [2 * n] and r != 0 and ch == escale(r, H.w1))
    p, f = check("ch(E) is concentrated in degree %d and is a nonzero "
                 "multiple of omega_1" % (2 * n), ok_ch,
                 "multiple: %d (mod p), that is %d, of Re(gamma - sqrt(-d) "
                 "ell)^n" % (r, r if r < P // 2 else r - P))
    NP += p
    NF += f

    # ---- HT^2: a basis
    zb = H.h02_basis()                                   # 15
    vb = []
    for u in range(m * m):
        c = [0] * (m * m)
        c[u] = 1
        vb.append(c)                                     # 36
    pb = [{(a, b): 1} for a, b in combinations(range(m), 2)]   # 15
    dimHT = len(zb) + len(vb) + len(pb)

    def ev(z, c, pc):
        out = []
        for L in L6:
            comp = dict(z) if z else {}
            if c is not None:
                comp = eadd(comp, H.deriv(c, L))
            if pc is not None:
                comp = eadd(comp, escale(inv(2), H.bivec(pc, wedge(L, L))))
            out.append(comp)
        return out

    def sigma(zeta):
        tot = {}
        for s, z, e in zip(signs, zeta, E6):
            tot = eadd(tot, escale(s, wedge(z, e)))
        return tot

    def contract_ch(z, c, pc):
        tot = {}
        if z:
            tot = eadd(tot, wedge(z, ch))
        if c is not None:
            tot = eadd(tot, H.deriv(c, ch))
        if pc is not None:
            tot = eadd(tot, H.bivec(pc, ch))
        return tot

    # (E1) the square commutes on every basis vector, and on random sums
    ok = True
    for z in zb:
        ok = ok and sigma(ev(z, None, None)) == contract_ch(z, None, None)
    for c in vb:
        ok = ok and sigma(ev({}, c, None)) == contract_ch({}, c, None)
    for pc in pb:
        ok = ok and sigma(ev({}, None, pc)) == contract_ch({}, None, pc)
    for _ in range(5):
        z = {}
        for zz in zb:
            z = eadd(z, escale(random.randrange(P), zz))
        c = [random.randrange(P) for _ in range(m * m)]
        pc = {k: random.randrange(P) for k in combinations(range(m), 2)}
        ok = ok and sigma(ev(z, c, pc)) == contract_ch(z, c, pc)
    p, f = check("sigma_E(ev_E(x)) = x _| ch(E) on every basis vector of "
                 "HT^2 and on random elements, dim HT^2 = %d" % dimHT, ok)
    NP += p
    NF += f

    # coordinates on (+)_i H^{0,2}
    keys = [(1 << (m + a)) | (1 << (m + b)) for a, b in combinations(range(m), 2)]

    def flat(zeta):
        vec = []
        for comp in zeta:
            vec.extend(comp.get(k, 0) for k in keys)
        return vec

    # (E2) rank of ev_E against dim Ext^2(E,E) = 90
    images = [flat(ev(z, None, None)) for z in zb] + \
             [flat(ev({}, c, None)) for c in vb] + \
             [flat(ev({}, None, pc)) for pc in pb]
    rk_ev = rank_rows(images)
    dimExt = 6 * len(keys)
    p, f = check("dim Ext^2(E,E) = %d exceeds dim HT^2 = %d, so ev_E is not "
                 "surjective; rank ev_E = %d" % (dimExt, dimHT, rk_ev),
                 dimExt > dimHT and rk_ev <= dimHT)
    NP += p
    NF += f

    # (E3) the kernel of x -> x _| ch(E), summand by summand
    def kernel_of(action, basis, nb):
        imgs = [action(b) for b in basis]
        ks = sorted({k for im in imgs for k in im})
        M = [[imgs[j].get(k, 0) for j in range(nb)] for k in ks]
        return nullspace(M, nb) if M else \
            [[1 if i == j else 0 for j in range(nb)] for i in range(nb)]

    kz = kernel_of(lambda z: wedge(z, ch), zb, len(zb))
    kv = kernel_of(lambda c: H.deriv(c, ch), vb, len(vb))
    kp = kernel_of(lambda pc: H.bivec(pc, ch), pb, len(pb))
    p, f = check("ker(_|ch(E) o HKR) = Ann(omega_1) (+) {v : v _| omega_1 = 0} "
                 "(+) {pi : pi _| omega_1 = 0} of dimensions %d, %d, %d"
                 % (len(kz), len(kv), len(kp)),
                 len(kz) == n * n and len(kv) == 2 * n * n)
    NP += p
    NF += f

    def comb_z(coefs):
        z = {}
        for co, zz in zip(coefs, zb):
            if co % P:
                z = eadd(z, escale(co, zz))
        return z

    def comb_v(coefs):
        return [sum(co * b[u] for co, b in zip(coefs, vb)) % P
                for u in range(m * m)]

    def comb_p(coefs):
        pc = {}
        for co, b in zip(coefs, pb):
            if co % P:
                for k, v in b.items():
                    pc[k] = (pc.get(k, 0) + co * v) % P
        return pc

    imz = [flat(ev(comb_z(a), None, None)) for a in kz]
    imv = [flat(ev({}, comb_v(a), None)) for a in kv]
    imp = [flat(ev({}, None, comb_p(a))) for a in kp]
    dz, dv, dp = rank_rows(imz), rank_rows(imv), rank_rows(imp)
    dall = rank_rows(imz + imv + imp)

    # the kernel of sigma_E, for comparison
    cols = []
    for s, e in zip(signs, E6):
        for z in zb:
            cols.append(escale(s, wedge(e, z)))
    ksig = dimExt - rank_mod(cols)

    # (E4)
    p, f = check("ker(sigma_E) meet im(ev_E) = ev_E(ker(_|ch o HKR)) has "
                 "dimension %d; dim ker(sigma_E) = %d" % (dall, ksig),
                 dall > 0 and ksig == 15,
                 "the weakened criterion of Question 11.4 fails for E by "
                 "%d dimensions%s" % (dall, "; the whole kernel of sigma_E "
                 "lies in the image of ev_E" if dall == ksig else ""))
    NP += p
    NF += f

    # (E5) the three contributions
    # the polarised K-commuting part T inside the deformation kernel
    kT = kernel_of(lambda c: eadd(H.deriv(c, H.eta), H.deriv(c, H.w1),
                                  H.deriv(c, H.w2)), vb, len(vb))
    imT = [flat(ev({}, comb_v(a), None)) for a in kT]
    dT = rank_rows(imT)
    dzv = rank_rows(imz + imv)
    dzp = rank_rows(imz + imp)
    dvp = rank_rows(imv + imp)
    rows = ["ev_E(Ann(omega_1)): dim %d [the copy of the tangent space]" % dz,
            "ev_E of the %d deformations killing omega_1: dim %d; on the "
            "%d-dimensional polarised K-commuting part T: dim %d"
            % (len(kv), dv, len(kT), dT),
            "ev_E of the %d bivectors killing omega_1: dim %d" % (len(kp), dp),
            "pairwise sums: z+v %d, z+pi %d, v+pi %d; all three %d"
            % (dzv, dzp, dvp, dall)]
    p, f = check("the three summands of HT^2 contribute %d, %d and %d "
                 "dimensions to ker(sigma_E) meet im(ev_E)" % (dz, dv, dp),
                 dz == n * n and dT == n * (n - 1) // 2, "\n".join(rows))
    NP += p
    NF += f

    # (E6) every Weil configuration of item (XIV)
    from itertools import product
    from collections import Counter
    gam, ell = H.mf.gamma, H.mf.ell
    eta3 = wedge(wedge(H.mf.eta, H.mf.eta), H.mf.eta)
    B = 7
    seen, res = set(), Counter()
    for s1, s2, c1, c2 in product(range(-B, B + 1), repeat=4):
        s3, c3 = -s1 - s2, -c1 - c2
        if abs(s3) > B or abs(c3) > B:
            continue
        lams = [(s1, c1), (s2, c2), (s3, c3)]
        if (0, 0) in lams or len({*lams, *[(-a, -b) for a, b in lams]}) < 6:
            continue
        sv, cv = (s1, s2, s3), (c1, c2, c3)
        if sum(a * b * b for a, b in zip(sv, cv)) != -d * sum(x ** 3 for x in sv):
            continue
        if sum(x ** 3 for x in cv) != -d * sum(a * a * b for a, b in zip(sv, cv)):
            continue
        key = frozenset(lams)
        if key in seen:
            continue
        seen.add(key)
        cl_std = [eadd(escale(a % P, gam), escale(b % P, ell)) for a, b in lams]
        tot = {}
        for x in cl_std:
            tot = eadd(tot, eadd(H.mf.expcl(x),
                                 escale(P - 1, H.mf.expcl(escale(P - 1, x)))))
        ch3 = {k: v for k, v in tot.items() if bin(k).count("1") == 6}
        ch5 = {k: v for k, v in tot.items() if bin(k).count("1") == 10}
        if not ch3 or ch5:
            continue
        if rank_mod([eta3, ch3]) != 2:
            continue
        # into the Hodge basis
        Lc = [H.mf.to_hodge(x) for x in cl_std]
        Lc6 = Lc + [escale(P - 1, x) for x in Lc]
        Ec6 = [H.expcl(x) for x in Lc6]
        chc = {}
        for sg, e in zip(signs, Ec6):
            chc = eadd(chc, escale(sg, e))

        def ev_c(z, c, pc):
            out = []
            for x in Lc6:
                comp = dict(z) if z else {}
                if c is not None:
                    comp = eadd(comp, H.deriv(c, x))
                if pc is not None:
                    comp = eadd(comp, escale(inv(2), H.bivec(pc, wedge(x, x))))
                out.append(comp)
            return out

        kz_c = kernel_of(lambda z: wedge(z, chc), zb, len(zb))
        kv_c = kernel_of(lambda c: H.deriv(c, chc), vb, len(vb))
        kp_c = kernel_of(lambda pc: H.bivec(pc, chc), pb, len(pb))
        ims = [flat(ev_c(comb_z(a), None, None)) for a in kz_c] + \
              [flat(ev_c({}, comb_v(a), None)) for a in kv_c] + \
              [flat(ev_c({}, None, comb_p(a))) for a in kp_c]
        meet = rank_rows(ims)
        cols_c = []
        for sg, e in zip(signs, Ec6):
            for z in zb:
                cols_c.append(escale(sg, wedge(e, z)))
        ker_c = dimExt - rank_mod(cols_c)
        res[(ker_c, meet)] += 1
    total = sum(res.values())
    ok = total >= 10 and all(k == mt for (k, mt) in res)
    p, f = check("for every Weil configuration in the box, the whole kernel "
                 "of sigma_E lies in the image of ev_E", ok,
                 "configurations: %d; (dim ker sigma_E, dim ker meet im ev_E) "
                 "distribution: %s" % (total, dict(res)))
    NP += p
    NF += f

    print()
    print("  %d checks passed, %d failed" % (NP, NF))
    print("  overall: %s" % ("PASS" if NF == 0 else "FAIL"))
    return 0 if NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
