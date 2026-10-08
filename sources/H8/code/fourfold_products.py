"""Item (LXXII): the fourfold products on E_0^6 and an explicit convolution.

Setting of item (LXXI) at n = 3: A = B_1 x B_2 x B_3, B_j = E_0 x E_0,
E_0 = C/Z[i], pieces M_t (hermitian form t Id) and L_zeta (form
[[p, zeta_j], [conj zeta_j, p]] on B_j), with p + 2 <= t_1 < t_2 < t_3.  The
products that can act on the diagonal classes are m_4(x1, x2, y, x3) along
M_{t2} -> M_{t3} -> L_zeta -> M_{t1}, with x1 in H^0, x2 in H^6, x3 in H^0
and y in H^2(O_A) at L_zeta, for the harmonic homotopy h = dbar^* G.

Method.  On B_j the isogeny phi(u, v) = (u + v, zeta_j (u - v)) of degree 4
from E_0 x E_0 makes every form on the path diagonal: L_zeta pulls back to
degrees 2(p + 1), 2(p - 1) and M_t to 2t, 2t.  Sections are theta functions
in the unitary gauge; the Laplacian on each cover curve has Landau levels,
level k of a positive bundle of degree d being nabla_z^k of the holomorphic
sections, of norm k! (pi d)^k.  The value of m_4 on y = dzbar_a ^ dzbar_b
(cover curves a < b) is computed from the tree (x1 x2)(y x3), the only one
that survives the degree count, by the selection rules of the levels:

    m_4 = sum_M kA(M) F^M_a (x) Dn_b (x) Cup_rest
        - sum_M kB(M) Dn_a (x) F^M_b (x) Cup_rest,

with Cup the cup product on a curve, Dn the level-one part of x1 x2 lowered
by dbar^*, F^M the level-M part of x1 x2 against nabla x3, and
kA(M) = sqrt(pi d_e^b) / (pi (M d_e^a + d_e^b) pi (d_u^a + d_u^b)),
kB(M) = sqrt(pi d_e^a) / (pi (d_e^a + M d_e^b) pi (d_u^a + d_u^b)).
The outputs are paired with a common basis of H^0(A, (t_2 - t_1) theta)
(products of theta functions in the coordinates of A, pulled back), so the
values for different zeta lie in one space of dimension (t_2 - t_1)^6.

Paper: Section "Convolutions of line bundles" (ssec:convolutions):
prop:fourfoldrank, prop:explicitconvolution, lem:allthree,
thm:noconvolution, rem:convolutionsopen.

  (A) theta functions on E_0: quasi-periodicity, holomorphy, the formula for
      nabla_z, orthonormality, the norms of the levels, Parseval over the
      levels for a product s conj(omega);
  (B) the covers: the K-invariant sections have dimension |det| for the five
      bundles of the path at zeta_j = 1, i, -1, -i, and the theta basis of
      H^0(B_j, Hom(M_1, M_2)) pulls back exactly, K-invariantly, with rank 9;
  (C) the selection rules (level one against holomorphic, level two against
      nabla x3 times holomorphic), convergence in the grid, and Dn, F^0 not
      proportional to the cup product;
  (D) the trees: of the five trees with four leaves only (x1 x2)(y x3)
      survives the degree count, with two assignments of the homotopies;
  (E) the explicit convolution: in the order M_{t2}, M_{t3}, the sixteen
      L_zeta with prod zeta = 1, M_{t1}, the sixteen with prod zeta = -1,
      with shifts 0, 1, -4, -3, -5, the Maurer-Cartan equation is exactly
      x1 x2^zeta = 0 and sum_zeta x2^zeta x3^zeta = 0; the counts of the
      endomorphism complex in degrees 1, 2, 3;
  (F) the rank: at p = 0, t = (2, 5, 6) the products have rank 12 on the 12
      classes of type (1,1,0) at each L_zeta and rank 192 on all 192 of them,
      also with x1 x2^zeta = 0 = x2^zeta x3^zeta, with the relative sign of the
      two terms reversed, and at t = (2, 5, 7);
  (G) the classes that no product removes: each L_zeta has 3, 6 and 7
      partners of the other parity differing in 1, 2 and 3 coordinates, the
      last with D = prod |zeta_j - zeta'_j|^2 = 16 (six) and 64; for those
      with shifts differing by one the block H^3(L_zeta, L_zeta') is never
      hit and has no target of degree three, in the explicit convolution
      (2560 classes) and in random arrangements of the three placements;
      the bound 249 - (45 + 15 * 9) = 69 and 16 * 12 = 192, both > 57.
"""
import itertools
import sys

import numpy as np

PI = np.pi
PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ----------------------------------------------------------------------
# theta functions on E_0 = C/Z[i] in the unitary gauge
#
# A bundle of degree d > 0 with hermitian form d|z|^2 and semicharacter chi
# has holomorphic sections F with F(z+1) = chi(1) e^{pi i d y} F(z) and
# F(z+i) = chi(i) e^{-pi i d x} F(z).  nabla_z = d_z - (pi d/2) zbar,
# nabla_zbar = d_zbar + (pi d/2) z, [nabla_zbar, nabla_z] = -pi d.

class Bundle:
    def __init__(self, d, chi1, chii, M=7):
        assert d > 0
        self.d, self.M = d, M
        self.chi1, self.chii = complex(chi1), complex(chii)
        self.alpha = (np.angle(self.chi1) / (2 * PI)) % 1.0

    def _terms(self, z):
        z = np.asarray(z, dtype=complex).ravel()
        x, y = z.real, z.imag
        d = self.d
        ms = np.arange(-self.M, self.M + 1)[:, None]
        lci = np.log(self.chii)
        for k in range(d):
            s = k + self.alpha
            n = s + ms * d
            xi = y + ms + s / d
            t = np.exp(-PI * d * xi ** 2 + 1j * (PI * d * x * y + 2 * PI * n * x)
                       - ms * lci)
            yield k, xi, t

    def values(self, z, level=0):
        """Basis sections (level 0) or nabla_z^level of them.  On each term
        nabla_z (P(xi) T) = (-(i/2) P' + 2 pi i d xi P) T."""
        P = np.poly1d([1.0 + 0j])
        for _ in range(level):
            P = np.poly1d([-0.5j]) * P.deriv() + \
                np.poly1d([2j * PI * self.d, 0]) * P
        z = np.asarray(z, dtype=complex).ravel()
        out = np.zeros((self.d, z.size), dtype=complex)
        for k, xi, t in self._terms(z):
            out[k] = (P(xi) * t).sum(axis=0)
        return out


class Grid:
    def __init__(self, N):
        t = (np.arange(N) + 0.5) / N
        X, Y = np.meshgrid(t, t, indexing='ij')
        self.z = (X + 1j * Y).ravel()
        self.w = 1.0 / N ** 2


def onb(B, grid, levels=1):
    """Orthonormal basis of H^0(B) and the normalised level states
    nabla^k g / sqrt(k! (pi d)^k), k = 1..levels."""
    V = B.values(grid.z)
    P = (V @ V.conj().T) * grid.w
    L = np.linalg.cholesky((P + P.conj().T) / 2)
    Li = np.linalg.inv(L)
    out = [Li @ V]
    fact = 1.0
    for k in range(1, levels + 1):
        fact *= k * PI * B.d
        out.append(Li @ B.values(grid.z, level=k) / np.sqrt(fact))
    return out


# ----------------------------------------------------------------------
# surfaces B = C^2/Z[i]^2 and the covers phi_zeta

BASIS = [np.array([1, 0], complex), np.array([1j, 0], complex),
         np.array([0, 1], complex), np.array([0, 1j], complex)]


def herm(x, y, H):
    return x @ H @ np.conj(y)


class Piece:
    """Hermitian matrix H (H(x, y) = x^T H conj y) and semicharacter values
    on (1,0), (i,0), (0,1), (0,i)."""

    def __init__(self, H, vals):
        self.H = np.array(H, complex)
        self.vals = np.array(vals, complex)
        E = np.array([[herm(BASIS[k], BASIS[l], self.H).imag
                       for l in range(4)] for k in range(4)])
        assert np.allclose(E, np.round(E))
        self.E = np.round(E).astype(int)

    def chi(self, n):
        q = sum(n[k] * n[l] * self.E[k, l] for k in range(4)
                for l in range(k + 1, 4))
        return np.prod(self.vals ** np.array(n)) * np.exp(1j * PI * q)


class Hom:
    def __init__(self, a, b):
        self.a, self.b = a, b
        self.H = b.H - a.H

    def chi(self, n):
        return self.b.chi(n) / self.a.chi(n)


class Cover:
    def __init__(self, zeta):
        self.zeta = complex(zeta)
        self.P = np.array([[1, 1], [self.zeta, -self.zeta]], complex)

    def phi(self, w):
        return w @ self.P.T

    @staticmethod
    def nvec(x):
        return [int(round(x[0].real)), int(round(x[0].imag)),
                int(round(x[1].real)), int(round(x[1].imag))]

    def pullform(self, hom):
        return self.P.T @ hom.H @ np.conj(self.P)

    def bundles(self, hom):
        Hp = self.pullform(hom)
        assert abs(Hp[0, 1]) < 1e-12
        out = []
        for col in (0, 1):
            d = int(round(Hp[col, col].real))
            e = np.zeros(2, complex)
            e[col] = 1
            out.append(Bundle(d, hom.chi(self.nvec(self.phi(e))),
                              hom.chi(self.nvec(self.phi(1j * e)))))
        return out

    def kinv(self, hom, Bu, Bv, rng):
        """K-invariant sections of phi^* hom in the product basis: the
        automorphy under k = (1/2, 1/2), (i/2, i/2), the kernel of phi."""
        du, dv = Bu.d, Bv.d
        npts = 3 * du * dv + 20
        w = rng.random((npts, 2)) + 1j * rng.random((npts, 2))
        Hp = self.pullform(hom)
        rows = []
        for k in (np.array([0.5, 0.5]), np.array([0.5j, 0.5j])):
            ck = hom.chi(self.nvec(self.phi(k)))
            ph = ck * np.exp(1j * PI * np.array([herm(wi, k, Hp).imag
                                                 for wi in w]))
            A = (np.einsum('ap,bp->pab', Bu.values(w[:, 0] + k[0]),
                           Bv.values(w[:, 1] + k[1]))
                 - ph[:, None, None] * np.einsum('ap,bp->pab',
                                                 Bu.values(w[:, 0]),
                                                 Bv.values(w[:, 1])))
            rows.append(A.reshape(npts, du * dv))
        u, s, vh = np.linalg.svd(np.vstack(rows))
        r = int((s > 1e-8 * s[0]).sum())
        gap = s[r - 1] / s[0] if r else 1.0
        tail = s[r] / s[0] if r < len(s) else 0.0
        return vh[r:].conj().T, gap, tail


def zpull(C, hom, d, bu, bv, rng):
    """Theta basis of H^0(B, hom) in the coordinates of B (degree d in each),
    pulled back by phi and expanded in the product basis of the cover."""
    B1 = Bundle(d, hom.chi([1, 0, 0, 0]), hom.chi([0, 1, 0, 0]))
    B2 = Bundle(d, hom.chi([0, 0, 1, 0]), hom.chi([0, 0, 0, 1]))
    n = 4 * bu.d * bv.d + 40
    w = rng.random((n, 2)) + 1j * rng.random((n, 2))
    zz = C.phi(w)
    Z = np.einsum('ap,bp->abp', B1.values(zz[:, 0]),
                  B2.values(zz[:, 1])).reshape(d * d, n)
    G = np.einsum('ap,bp->pab', bu.values(w[:, 0]),
                  bv.values(w[:, 1])).reshape(n, bu.d * bv.d)
    Zc = np.linalg.lstsq(G, Z.T, rcond=None)[0]
    res = np.abs(G @ Zc - Z.T).max() / np.abs(Z).max()
    return Zc, res


# ----------------------------------------------------------------------
# the per-curve maps

class CurveOps:
    """Trilinear maps (s, conj omega~, u) -> w, with w the coordinates
    alpha -> int alpha phi_w against holomorphic sections phi_w of the dual
    of the output bundle."""

    def __init__(self, bS, bOm, bU, bE, bPhi, grid):
        z, wq = grid.z, grid.w
        sv, ov = bS.values(z), bOm.values(z)
        uv, duv = bU.values(z), bU.values(z, level=1)
        g0, g1, g2 = onb(bE, grid, levels=2)
        fv = bPhi.values(z)
        self.de, self.du = bE.d, bU.d
        so = np.einsum('sp,op->sop', sv, ov.conj())
        self.coef = [np.einsum('sop,gp->sog', so, g) * wq for g in (g0, g1)]
        uf = np.einsum('up,wp->uwp', uv, fv)
        duf = np.einsum('up,wp->uwp', duv, fv)
        P0 = np.einsum('gp,uwp->guw', g0.conj(), uf) * wq
        P0d = np.einsum('gp,uwp->guw', g0.conj(), duf) * wq
        P1d = np.einsum('gp,uwp->guw', g1.conj(), duf) * wq
        self.Cup = np.einsum('sog,guw->souw', self.coef[0], P0)
        self.Dn = np.einsum('sog,guw->souw', self.coef[1], P0)
        self.F = [np.einsum('sog,guw->souw', self.coef[0], P0d),
                  np.einsum('sog,guw->souw', self.coef[1], P1d)]
        # selection rules
        self.sel1 = np.abs(np.einsum('gp,uwp->guw', g1.conj(), uf)).max() * wq
        self.sel2 = np.abs(np.einsum('gp,uwp->guw', g2.conj(), duf)).max() * wq
        self.scale = np.abs(P1d).max()

    def op(self, name):
        return {'Cup': self.Cup, 'Dn': self.Dn, 'F0': self.F[0],
                'F1': self.F[1]}[name]


def rph(rng, k):
    return np.exp(2j * PI * rng.random(k))


class Config:
    """Pieces of the path on the three surfaces.  The restriction of L_zeta
    to B_j depends only on zeta_j; every piece carries a random twist."""

    def __init__(self, p, t1, t2, t3, rng, N=64):
        self.p, self.t, self.rng = p, (t1, t2, t3), rng
        self.grid = Grid(N)
        self.M = [{t: Piece(t * np.eye(2), rph(rng, 4)) for t in (t1, t2, t3)}
                  for _ in range(3)]
        self.Lvals = {}
        d = (t3 - t2) ** 2
        self.x1c = [rng.standard_normal(d) + 1j * rng.standard_normal(d)
                    for _ in range(3)]

    def L(self, zj, j):
        key = (complex(np.round(zj, 6)), j)
        if key not in self.Lvals:
            self.Lvals[key] = rph(self.rng, 4)
        return Piece([[self.p, zj], [np.conj(zj), self.p]], self.Lvals[key])

    def surface(self, zj, j):
        t1, t2, t3 = self.t
        M1, M2, M3 = self.M[j][t1], self.M[j][t2], self.M[j][t3]
        L = self.L(zj, j)
        C = Cover(zj)
        homs = {'S': Hom(M2, M3), 'Om': Hom(L, M3), 'U': Hom(L, M1),
                'E': Hom(L, M2), 'Phi': Hom(M1, M2), 'Q': Hom(M1, M3)}
        bund = {k: C.bundles(h) for k, h in homs.items()}
        ops = [CurveOps(*(bund[k][c] for k in ('S', 'Om', 'U', 'E', 'Phi')),
                        self.grid) for c in (0, 1)]
        kin = {k: C.kinv(homs[k], *bund[k], self.rng)[0]
               for k in ('S', 'Om', 'U')}
        Zc, _ = zpull(C, homs['Phi'], t2 - t1, *bund['Phi'], self.rng)
        Sc, _ = zpull(C, homs['S'], t3 - t2, *bund['S'], self.rng)
        Q = []
        for c in (0, 1):
            ov = bund['Om'][c].values(self.grid.z)
            uv = bund['U'][c].values(self.grid.z)
            qv = bund['Q'][c].values(self.grid.z)
            Q.append(np.einsum('op,up,mp->oum', ov.conj(), uv, qv)
                     * self.grid.w)
        X1 = (Sc @ self.x1c[j]).reshape(bund['S'][0].d, bund['S'][1].d)
        return dict(ops=ops, kin=kin, Zc=Zc, X1=X1, Q=Q, bund=bund)


def right_sign():
    mu4 = [1, 1j, -1, -1j]
    return [z for z in itertools.product(mu4, repeat=3)
            if abs(np.prod(z) - 1) < 1e-9]


def nullspace(A, tol=1e-9):
    u, s, vh = np.linalg.svd(A)
    return vh[int((s > tol * s[0]).sum()):].conj().T


def rvec(rng, V):
    c = rng.standard_normal(V.shape[1]) + 1j * rng.standard_normal(V.shape[1])
    return V @ c


def columns(cfg, zeta, rng, mc=False, sign=-1, info=None):
    """Values of y -> m_4(x1, x2, y, x3) on the 12 classes of type (1,1,0)
    at L_zeta, as vectors in the common space of dimension (t2 - t1)^6."""
    sds = [cfg.surface(zeta[j], j) for j in range(3)]
    X1 = [sd['X1'] for sd in sds]
    X3, Vy, K1, K2 = [], [], [], []
    for m, sd in enumerate(sds):
        bO, bU = sd['bund']['Om'], sd['bund']['U']
        X3.append(rvec(rng, sd['kin']['U']).reshape(bU[0].d, bU[1].d))
        Vc = sd['kin']['Om'].conj()
        o = sd['ops']
        m1 = np.einsum('ab,acg,beh->cegh', X1[m], o[0].coef[0],
                       o[1].coef[0]).reshape(Vc.shape[0], -1)
        m2 = np.einsum('fg,cfm,egn->cemn', X3[m], sd['Q'][0],
                       sd['Q'][1]).reshape(Vc.shape[0], -1)
        k1, k2 = nullspace((Vc.T @ m1).T), nullspace((Vc.T @ m2).T)
        Vy.append(Vc)
        K1.append(Vc @ k1)
        K2.append(Vc @ k2)
        if info is not None:
            info.append((k1.shape[1], k2.shape[1]))
    terms = []
    if mc:
        for j, jp in itertools.permutations(range(3), 2):
            for _ in range(2):
                terms.append([rvec(rng, K1[m] if m == j else K2[m] if m == jp
                                   else Vy[m]) for m in range(3)])
    else:
        terms.append([rvec(rng, Vy[m]) for m in range(3)])
    terms = [[f.reshape(sds[m]['bund']['Om'][0].d, -1)
              for m, f in enumerate(fac)] for fac in terms]
    if mc and info is not None:
        p1 = max(min(np.abs(np.einsum('ab,ce,acg,beh->gh', X1[m], fac[m],
                                      sds[m]['ops'][0].coef[0],
                                      sds[m]['ops'][1].coef[0])).max()
                     for m in range(3)) for fac in terms)
        p2 = max(min(np.abs(np.einsum('ce,fg,cfm,egn->mn', fac[m], X3[m],
                                      sds[m]['Q'][0], sds[m]['Q'][1])).max()
                     for m in range(3)) for fac in terms)
        info.append(('products', p1, p2))
    cache = {}

    def surfvec(m, opu, opv, r):
        key = (m, opu, opv, r)
        if key not in cache:
            o = sds[m]['ops']
            T = np.einsum('ab,ce,fg,acfw,begv->wv', X1[m], terms[r][m], X3[m],
                          o[0].op(opu), o[1].op(opv)).reshape(-1)
            cache[key] = T @ sds[m]['Zc']
        return cache[key]

    def tensor(assign):
        tot = 0
        for r in range(len(terms)):
            vs = [surfvec(m, assign.get(2 * m, 'Cup'),
                          assign.get(2 * m + 1, 'Cup'), r) for m in range(3)]
            tot = tot + np.einsum('a,b,c->abc', *vs).reshape(-1)
        return tot
    de = [sds[c // 2]['ops'][c % 2].de for c in range(6)]
    du = [sds[c // 2]['ops'][c % 2].du for c in range(6)]
    cols = []
    for a, b in [(a, b) for a in range(6) for b in range(a + 1, 6)
                 if a // 2 != b // 2]:
        den = PI * (du[a] + du[b])
        out = 0
        for M in (0, 1):
            kA = np.sqrt(PI * de[b]) / (PI * (de[a] * M + de[b]) * den)
            kB = np.sqrt(PI * de[a]) / (PI * (de[a] + de[b] * M) * den)
            out = out + kA * tensor({a: 'F%d' % M, b: 'Dn'}) \
                + sign * kB * tensor({a: 'Dn', b: 'F%d' % M})
        cols.append(out)
    return np.array(cols).T


def numrank(A, tol=1e-9):
    s = np.linalg.svd(A, compute_uv=False)
    r = int((s > tol * s[0]).sum())
    return r, s[r - 1] / s[0], (s[r] / s[0] if r < len(s) else 0.0)


def total_rank(params, seed, mc=False, sign=-1):
    rng = np.random.default_rng(seed)
    cfg = Config(*params, rng)
    blocks, per, info = [], [], []
    for zeta in right_sign():
        B = columns(cfg, zeta, rng, mc=mc, sign=sign, info=info)
        blocks.append(B)
        per.append(numrank(B)[0])
    return numrank(np.hstack(blocks)), per, info


# ----------------------------------------------------------------------

def part_A():
    rng = np.random.default_rng(1)
    g = Grid(64)
    for d in (2, 6, 14):
        B = Bundle(d, np.exp(2j * PI * rng.random()), np.exp(2j * PI * rng.random()))
        z = rng.random(6) + 1j * rng.random(6)
        F = B.values(z)
        e1 = np.abs(B.values(z + 1) - B.chi1 * np.exp(1j * PI * d * z.imag) * F).max()
        ei = np.abs(B.values(z + 1j) - B.chii * np.exp(-1j * PI * d * z.real) * F).max()
        check("(A) d = %d: F(z+1), F(z+i) have the automorphy factors" % d,
              max(e1, ei) < 1e-10 * np.abs(F).max(), "%.1e" % max(e1, ei))
        h = 1e-5
        Fx = (B.values(z + h) - B.values(z - h)) / (2 * h)
        Fy = (B.values(z + 1j * h) - B.values(z - 1j * h)) / (2 * h)
        nzb = (Fx + 1j * Fy) / 2 + (PI * d / 2) * z * F
        nz = (Fx - 1j * Fy) / 2 - (PI * d / 2) * z.conj() * F
        D = B.values(z, level=1)
        check("(A) d = %d: nabla_zbar F = 0 and nabla_z F as computed" % d,
              np.abs(nzb).max() < 1e-5 * np.abs(F).max()
              and np.abs(nz - D).max() < 1e-5 * np.abs(D).max())
        g0, g1, g2 = onb(B, g, levels=2)
        Gm = np.vstack([g0, g1, g2])
        err = np.abs((Gm @ Gm.conj().T) * g.w - np.eye(3 * d)).max()
        check("(A) d = %d: levels 0, 1, 2 orthonormal with norms k! (pi d)^k" % d,
              err < 1e-10, "%.1e" % err)
    # Parseval over the levels for s conj(omega~) in degree d_omega - d_s
    s_b = Bundle(2, np.exp(0.7j), np.exp(1.9j))
    o_b = Bundle(10, np.exp(0.2j), np.exp(2.3j))
    e_b = Bundle(8, o_b.chi1 / s_b.chi1, o_b.chii / s_b.chii)
    sv, ov = s_b.values(g.z), o_b.values(g.z)
    prod = sv[0] * ov[3].conj()
    states = onb(e_b, g, levels=12)
    tot = (np.abs(prod) ** 2).sum() * g.w
    lev = [(np.abs(st @ prod * g.w) ** 2).sum() for st in states]
    check("(A) Parseval: levels 0..12 of s conj(omega~) carry its whole norm",
          abs(sum(lev) / tot - 1) < 1e-8,
          "levels 0, 1 carry %.3f, the rest %.1e"
          % ((lev[0] + lev[1]) / tot, abs(sum(lev) / tot - 1)))


def part_B():
    rng = np.random.default_rng(3)
    p, t1, t2, t3 = 0, 2, 5, 6
    M = {t: Piece(t * np.eye(2), rph(rng, 4)) for t in (t1, t2, t3)}
    for zeta in (1, 1j, -1, -1j):
        L = Piece([[p, zeta], [np.conj(zeta), p]], rph(rng, 4))
        C = Cover(zeta)
        dims, ok = [], True
        for h in (Hom(M[t2], M[t3]), Hom(L, M[t3]), Hom(L, M[t1]),
                  Hom(L, M[t2]), Hom(M[t1], M[t2])):
            Bu, Bv = C.bundles(h)
            V, gap, tail = C.kinv(h, Bu, Bv, rng)
            det = int(round(abs(np.linalg.det(h.H).real)))
            ok &= V.shape[1] == det and gap > 1e-3 and tail < 1e-10
            dims.append("%dx%d->%d" % (Bu.d, Bv.d, V.shape[1]))
        check("(B) zeta_j = %s: K-invariant sections of dimension |det| on "
              "the cover" % zeta, ok, ", ".join(dims))
        h = Hom(M[t1], M[t2])
        bu, bv = C.bundles(h)
        Zc, res = zpull(C, h, t2 - t1, bu, bv, rng)
        V, _, _ = C.kinv(h, bu, bv, rng)
        inside = np.abs(V @ (V.conj().T @ Zc) - Zc).max() / np.abs(Zc).max()
        check("(B) zeta_j = %s: theta basis of B_j pulls back exactly, "
              "K-invariantly, rank 9" % zeta,
              res < 1e-10 and inside < 1e-10
              and np.linalg.matrix_rank(Zc, 1e-8) == 9,
              "residual %.1e" % res)


def part_C():
    rng = np.random.default_rng(7)
    cfg = Config(0, 2, 5, 6, rng)
    cfg2 = Config(0, 2, 5, 6, np.random.default_rng(7), N=80)
    sd, sd2 = cfg.surface(1j, 0), cfg2.surface(1j, 0)
    for c, name in ((0, 'u'), (1, 'v')):
        o, o2 = sd['ops'][c], sd2['ops'][c]
        check("(C) curve %s (d_e = %d, d_u = %d): selection rules hold"
              % (name, o.de, o.du),
              o.sel1 < 1e-12 * o.scale and o.sel2 < 1e-12 * o.scale,
              "%.1e, %.1e" % (o.sel1, o.sel2))
        diff = max(np.abs(o.op(k) - o2.op(k)).max() for k in ('Cup', 'Dn', 'F0', 'F1'))
        check("(C) curve %s: grid 64 and 80 agree" % name, diff < 1e-12,
              "%.1e" % diff)
        C = o.Cup.reshape(-1)
        res = []
        for k in ('Dn', 'F0'):
            X = o.op(k).reshape(-1)
            lam = (C.conj() @ X) / (C.conj() @ C)
            res.append(np.linalg.norm(X - lam * C) / np.linalg.norm(X))
        check("(C) curve %s: Dn and F^0 are not multiples of the cup product"
              % name, min(res) > 0.5, "relative distances %.3f, %.3f" % tuple(res))


def part_D():
    # leaves x1, x2, y, x3; per curve degrees: on a, b: 0, 1, 1, 0; elsewhere
    # 0, 1, 0, 0.  The output has degree 1 everywhere, so a and b are each
    # lowered once and no other curve is; a product of two 1-forms on a curve
    # vanishes.
    trees = {'((x1 x2) y) x3': ((('x1', 'x2'), 'y'), 'x3'),
             '(x1 (x2 y)) x3': (('x1', ('x2', 'y')), 'x3'),
             '(x1 x2)(y x3)': (('x1', 'x2'), ('y', 'x3')),
             'x1 ((x2 y) x3)': ('x1', (('x2', 'y'), 'x3')),
             'x1 (x2 (y x3))': ('x1', ('x2', ('y', 'x3')))}
    deg = {'x1': 0, 'x2': 1, 'y': 1, 'x3': 0}

    def internal(t, acc):
        if isinstance(t, tuple):
            for s in t:
                if isinstance(s, tuple):
                    acc.append(s)
                internal(s, acc)
        return acc

    def value(t, low):
        # degree on a marked curve, or None if the product vanishes
        if not isinstance(t, tuple):
            return deg[t]
        l, r = value(t[0], low), value(t[1], low)
        if l is None or r is None or l + r > 1:
            return None
        v = l + r
        if id(t) in low:
            if v == 0:
                return None
            v -= 1
        return v
    surv = {}
    for name, t in trees.items():
        edges = internal(t, [])
        n = 0
        for ea, eb in itertools.permutations(edges, 2):
            if value(t, {id(ea)}) == 1 and value(t, {id(eb)}) == 1:
                n += 1
        surv[name] = n
    check("(D) only (x1 x2)(y x3) survives, with two assignments",
          surv == {'((x1 x2) y) x3': 0, '(x1 (x2 y)) x3': 0,
                   '(x1 x2)(y x3)': 2, 'x1 ((x2 y) x3)': 0,
                   'x1 (x2 (y x3))': 0}, str(surv))


def part_E():
    p, t1, t2, t3 = 0, 2, 5, 6
    mu4 = [1, 1j, -1, -1j]
    R = [z for z in itertools.product(mu4, repeat=3) if abs(np.prod(z) - 1) < 1e-9]
    W = [z for z in itertools.product(mu4, repeat=3) if abs(np.prod(z) + 1) < 1e-9]
    pieces = ([('M2', t2 * np.eye(2), 0, None), ('M3', t3 * np.eye(2), 1, None)]
              + [('R', None, -4, z) for z in R] + [('M1', t1 * np.eye(2), -3, None)]
              + [('W', None, -5, z) for z in W])

    def form(x, j):
        if x[0][0] == 'M':
            return x[1]
        z = x[3][j]
        return np.array([[p, z], [np.conj(z), p]])

    def coh(a, b):
        out = {}
        hs = []
        for j in range(3):
            F = form(b, j) - form(a, j)
            if np.allclose(F, 0):
                hs.append({0: 1, 1: 2, 2: 1})
            else:
                ev = np.linalg.eigvalsh(F)
                hs.append({int((ev < 0).sum()): int(round(abs(np.prod(ev))))})
        for (q1, d1), (q2, d2), (q3, d3) in itertools.product(*(h.items() for h in hs)):
            out[q1 + q2 + q3] = out.get(q1 + q2 + q3, 0) + d1 * d2 * d3
        return out
    N = len(pieces)
    H = [[coh(pieces[a], pieces[b]) for b in range(N)] for a in range(N)]
    # components of the twisted differential: delta_ab in degree 1 + d_a - d_b
    edges = {(a, b) for a in range(N) for b in range(a + 1, N)
             if H[a][b].get(1 + pieces[a][2] - pieces[b][2], 0)
             and not (pieces[a][0] == 'M2' and pieces[b][0] == 'W')}
    kinds = sorted({(pieces[a][0], pieces[b][0]) for a, b in edges})
    check("(E) the components: M2->M3, M3->R, R->M1, R->W (and M2->W, set "
          "to zero)", kinds == [('M2', 'M3'), ('M3', 'R'), ('R', 'M1'), ('R', 'W')],
          str(kinds))
    # Maurer-Cartan components: paths of length >= 2 of components, landing
    # in a degree where the cohomology is nonzero
    adj = {}
    for a, b in edges:
        adj.setdefault(a, []).append(b)
    eqs = set()

    def walk(path):
        a, b = path[0], path[-1]
        k = len(path) - 1
        if k >= 2 and H[a][b].get(2 + pieces[a][2] - pieces[b][2], 0):
            eqs.add((tuple(pieces[i][0] for i in path)))
        for c in adj.get(b, []):
            walk(path + [c])
    for a in range(N):
        walk([a])
    check("(E) the Maurer-Cartan equation is x1 x2^zeta = 0 and "
          "sum_zeta x2^zeta x3^zeta = 0", eqs == {('M2', 'M3', 'R'), ('M3', 'R', 'M1')},
          str(sorted(eqs)))
    dims = []
    for k in (1, 2, 3):
        dims.append(sum(H[a][b].get(k + pieces[a][2] - pieces[b][2], 0)
                        for a in range(N) for b in range(N)))
    check("(E) the endomorphism complex has 908979, 233213, 12142 classes in "
          "degrees 1, 2, 3", dims == [908979, 233213, 12142], str(dims))
    big = sum(H[a][b].get(2 + pieces[a][2] - pieces[b][2], 0)
              for a in range(N) for b in range(N)
              if pieces[a][0] == 'M2' and pieces[b][0] == 'R')
    check("(E) 221184 of the classes of degree two lie in Hom(M2, L_zeta), "
          "16 (t2 - p)^2 - 1)^3", big == 16 * ((t2 - p) ** 2 - 1) ** 3 == 221184)


def part_F():
    (r, gap, tail), per, info = total_rank((0, 2, 5, 6), 11)
    check("(F) t = (2,5,6): rank 12 at each of the 16 pieces L_zeta",
          per == [12] * 16)
    check("(F) t = (2,5,6): rank 192 on the 192 classes of type (1,1,0)",
          r == 192 and gap > 1e-4, "smallest/largest singular value %.4f" % gap)
    (r, gap, tail), per, info = total_rank((0, 2, 5, 6), 21, mc=True)
    kd = {x for x in info if len(x) == 2}
    prods = [x for x in info if len(x) == 3]
    check("(F) Maurer-Cartan: ker(x1 .) and ker(. x3) of dimensions 11 and 19 "
          "on every surface, and x1 x2 = x2 x3 = 0",
          kd == {(11, 19)} and max(max(x[1], x[2]) for x in prods) < 1e-10)
    check("(F) with x1 x2^zeta = 0 = x2^zeta x3^zeta: rank 192",
          r == 192 and gap > 1e-4 and per == [12] * 16,
          "smallest/largest singular value %.4f" % gap)
    (r, gap, tail), per, info = total_rank((0, 2, 5, 6), 31, sign=+1)
    check("(F) the relative sign of the two terms reversed: rank 192",
          r == 192 and gap > 1e-4, "%.4f" % gap)
    (r, gap, tail), per, info = total_rank((0, 2, 5, 7), 12)
    check("(F) t = (2,5,7): rank 192", r == 192 and gap > 1e-4, "%.4f" % gap)
    check("(F) the threshold of the corrected criterion: 249 - 57 = 192 = 16 * 12",
          249 - 57 == 192 == 16 * 12)


# ----------------------------------------------------------------------
# (G) the classes between Weil pieces that differ in all three coordinates

MU4 = [1, 1j, -1, -1j]
RP = [z for z in itertools.product(MU4, repeat=3) if abs(np.prod(z) - 1) < 1e-9]
WP = [z for z in itertools.product(MU4, repeat=3) if abs(np.prod(z) + 1) < 1e-9]


def kdiff(z, w):
    return sum(1 for j in range(3) if abs(z[j] - w[j]) > 1e-9)


def block_coh(a, b, p):
    """Dimensions of H^q(A, a^{-1} b) for pieces a = (kind, t, shift, zeta)."""
    def form(x, j):
        if x[0] == 'M':
            return x[1] * np.eye(2)
        z = x[3][j]
        return np.array([[p, z], [np.conj(z), p]])
    hs = []
    for j in range(3):
        F = form(b, j) - form(a, j)
        if np.allclose(F, 0):
            hs.append({0: 1, 1: 2, 2: 1})
        else:
            ev = np.linalg.eigvalsh(F)
            hs.append({int((ev < 0).sum()): int(round(abs(np.prod(ev))))})
    out = {}
    for (q1, d1), (q2, d2), (q3, d3) in itertools.product(*(h.items() for h in hs)):
        out[q1 + q2 + q3] = out.get(q1 + q2 + q3, 0) + d1 * d2 * d3
    return out


def isolated_blocks(pieces, p):
    """Blocks (a, b) of degree two that no term of d_E hits and whose
    differential has no target of degree three, by the path structure."""
    N = len(pieces)
    d = [x[2] for x in pieces]
    H = [[block_coh(pieces[a], pieces[b], p) for b in range(N)] for a in range(N)]
    C = {}
    for a in range(N):
        for b in range(N):
            for q, dim in H[a][b].items():
                C[(a, b, q - d[a] + d[b])] = C.get((a, b, q - d[a] + d[b]), 0) + dim
    edges = [(a, b) for a in range(N) for b in range(a + 1, N)
             if H[a][b].get(1 + d[a] - d[b], 0)]
    reach = [{a} for a in range(N)]
    for a in reversed(range(N)):
        for x, y in edges:
            if x == a:
                reach[a] |= reach[y]
    back = [{c for c in range(N) if a in reach[c]} for a in range(N)]

    def targets(a, b):
        return {(c, e) for c in back[a] for e in reach[b]} - {(a, b)}
    hit = set()
    for (a, b, w), dim in C.items():
        if w == 1 and dim:
            hit |= targets(a, b)
    iso = {}
    for (a, b, w), dim in C.items():
        if w == 2 and dim and a != b and (a, b) not in hit and \
                not any(C.get((c, e, 3), 0) for c, e in targets(a, b)):
            iso[(a, b)] = dim
    return iso


def random_arrangement(rng, placement):
    """Pieces in a random order with random shifts of the right parities,
    the path pieces (sixteen or fewer, prod zeta = 1) at shift r = 0."""
    if placement == 'one side':
        t, M = (2, 5, 6), {'M2': (5, 4, 0.0), 'M3': (6, 5, 1.0), 'M1': (2, 1, 3.0)}
    elif placement == 'path (a)':
        t, M = (-2, 2, 4), {'M2': (2, 3, 0.0), 'M3': (4, 4, 1.0), 'M1': (-2, -1, 2.0)}
    else:
        t, M = (-2, 2, 4), {'M3': (4, 4, 0.0), 'M1': (-2, -1, 1.0), 'M2': (2, 1, 3.0)}
    path_pos = {'one side': 2.0, 'path (a)': 3.0, 'path (b)': 2.0}[placement]
    npath = int(rng.integers(10, 17))
    onpath = set(rng.choice(16, npath, replace=False).tolist())
    items = [(pos, ('M', tt, sh, None)) for tt, sh, pos in M.values()]
    for i, z in enumerate(RP):
        if i in onpath:
            items.append((path_pos + 0.9 * rng.random(), ('L', None, 0, z)))
        else:
            items.append((5 * rng.random() - 1, ('L', None, int(rng.choice([-6, -4, -2, 2, 4])), z)))
    for z in WP:
        items.append((5 * rng.random() - 1, ('L', None, int(rng.choice([-5, -3, -1, 1, 3, 5])), z)))
    items.sort(key=lambda x: x[0])
    return [x[1] for x in items]


def part_G():
    # partners of a piece among the sixteen of the other parity
    ok, dist = True, set()
    for z in WP:
        ks = [kdiff(z, w) for w in RP]
        D3 = sorted(int(round(np.prod([abs(z[j] - w[j]) ** 2 for j in range(3)])))
                    for w in RP if kdiff(z, w) == 3)
        dist.add((ks.count(1), ks.count(2), ks.count(3), tuple(D3)))
    check("(G) each piece has 3, 6, 7 partners of the other parity differing "
          "in 1, 2, 3 coordinates; the 7 have D = 16 (six times) and 64, sum 160",
          dist == {(3, 6, 7, (16, 16, 16, 16, 16, 16, 64))}, str(dist))
    # the explicit convolution of (E)
    p = 0
    pieces = ([('M', 5, 0, None), ('M', 6, 1, None)]
              + [('L', None, -4, z) for z in RP] + [('M', 2, -3, None)]
              + [('L', None, -5, z) for z in WP])
    iso = isolated_blocks(pieces, p)
    k3 = {(a, b) for a in range(len(pieces)) for b in range(len(pieces))
          if pieces[a][0] == pieces[b][0] == 'L'
          and kdiff(pieces[a][3], pieces[b][3]) == 3
          and pieces[a][2] == pieces[b][2] + 1}
    tot = sum(iso[x] for x in k3 if x in iso)
    check("(G) explicit convolution: the 112 blocks H^3(L_zeta, L_zeta') with "
          "all coordinates different are isolated, 2560 = 16 * 160 classes",
          len(k3) == 112 and k3 <= set(iso) and tot == 2560, "%d" % tot)
    # random arrangements in the three placements
    rng = np.random.default_rng(33)
    for placement in ('one side', 'path (a)', 'path (b)'):
        good, n = True, 0
        for trial in range(12):
            pieces = random_arrangement(rng, placement)
            iso = isolated_blocks(pieces, 0)
            N = len(pieces)
            k3 = {(a, b) for a in range(N) for b in range(N)
                  if pieces[a][0] == pieces[b][0] == 'L'
                  and kdiff(pieces[a][3], pieces[b][3]) == 3
                  and pieces[a][2] == pieces[b][2] + 1}
            good &= k3 <= set(iso)
            n += len(k3)
        check("(G) %s: in 12 random arrangements every such block with "
              "shifts differing by one is isolated" % placement, good,
              "%d blocks" % n)
    check("(G) the bound: 249 - (45 + 15 * 9) = 69 > 57 and 16 * 12 = 192 > 57",
          249 - (45 + 15 * 9) == 69 > 57 and 16 * 12 == 192 > 57)


def main():
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    print()
    print("passed %d, failed %d" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
