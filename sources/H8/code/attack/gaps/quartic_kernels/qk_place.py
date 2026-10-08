"""qk_place.py -- the one-place model for item (LIX) (quartic_kernels.py).

Over R the cohomology of X (a principally polarised abelian fourfold with real
multiplication by O = O_{F_0}), of X x X and of A = X x Xhat is a tensor product
over the two real places of F_0 of classes of even degree, and the Orlov
correspondence, the classes eta_j, gamma_j, ell_j and the group G_F(R) =
SU_1 x SU_2 factor accordingly (proof of thm:quarticobstruction(iii)).  This
module is one factor, with d = tau_j(q):

  X_j      : generators x0..x3 (bits 0..3), theta = x0x2 + x1x3,
             int x0x1x2x3 = -1, so that int theta^2 = 2 and pt = theta^2/2;
  X_j x X_j: first factor a0..a3 (bits 0..3), second b0..b3 (bits 4..7);
  A_j      : x0..x3 (bits 0..3) and xi0..xi3 (bits 4..7), ell = sum x_i xi_i,
             thetahat = xi0xi2 + xi1xi3, eta = d theta + thetahat,
             gamma = d theta - thetahat.
  Orlov    : ch Phi(Z)(x, xi) = int_y Z(x + y, y) exp(sum_i y_i xi_i).
  F-action : M*(d) below, sqrt(-q) acting on H^1(A_j) with M*^2 = -d.
  Complex structure of the split member X x Xhat: x0 + i x2, x1 + i x3,
             xi0 + i xi2, xi1 + i xi3 are of type (1,0).

A class Z on X_j x X_j is a correspondence y -> int_a y(a) Z(a, b).
"""
from fractions import Fraction as Fr
from qk_ext import (popc, clean, add, sc, sub, wedge, gen, one, expo, lin_subst,
                    derivation, interior, nullspace_Q, _fq, iszero)

TOP4 = 0b1111
TOP8 = 0xFF
ORI = -1                       # int of g0 g1 g2 g3 over a four-dimensional factor


def integ4(u):
    return ORI * u.get(TOP4, 0)


def theta_x():
    return add(wedge(gen(0), gen(2)), wedge(gen(1), gen(3)))


def thetahat():
    return add(wedge(gen(4), gen(6)), wedge(gen(5), gen(7)))


def ell():
    return add(*[wedge(gen(i), gen(4 + i)) for i in range(4)])


def eta(d):
    return add(sc(d, theta_x()), sc(d * 0 + 1, thetahat()))


def gamma(d):
    return sub(sc(d, theta_x()), sc(d * 0 + 1, thetahat()))


def omega_w(d):
    """Omega = gamma^2 - d ell^2 = ((gamma - s ell)^2 + (gamma + s ell)^2)/2."""
    g = gamma(d)
    return sub(wedge(g, g), sc(d, wedge(ell(), ell())))


def lambda_w(d):
    """Lambda = gamma ell = ((gamma + s ell)^2 - (gamma - s ell)^2)/(4 s)."""
    return wedge(gamma(d), ell())


def inv_basis(d):
    """the seven SU_j-invariant classes 1, eta, eta^2, Omega, Lambda, eta^3, eta^4."""
    e = eta(d)
    e2 = wedge(e, e)
    return ([one(d * 0 + 1), e, e2, omega_w(d), lambda_w(d), wedge(e, e2),
             wedge(e2, e2)],
            ["1", "eta", "eta^2", "Omega", "Lambda", "eta^3", "eta^4"])


# ------------------------------------------------------------------ correspondences
def corr_of_class(Z):
    """16 x 16 matrix of Z_* in the monomial basis of H^*(X_j)."""
    mat = [[0] * 16 for _ in range(16)]
    for yb in range(16):
        for m, c in wedge({yb: Fr(1)}, Z).items():
            if (m & TOP4) == TOP4:
                mat[m >> 4][yb] += ORI * c
    return mat


_CB = None


def class_from_corr(Cmat):
    """the class Z on X_j x X_j with Z_* = Cmat (entries Fractions or K)."""
    global _CB
    if _CB is None:
        import flint
        A = flint.fmpq_mat(256, 256)
        for j in range(256):
            C = corr_of_class({j: Fr(1)})
            for i in range(256):
                x = C[i // 16][i % 16]
                if x != 0:
                    A[i, j] = _fq(x)
        _CB = A.inv()
    vec = [Cmat[i][j] for i in range(16) for j in range(16)]
    Z = {}
    for m in range(256):
        s = 0
        for k in range(256):
            a = _CB[m, k]
            if a != 0 and not iszero(vec[k]):
                s = s + Fr(int(a.p), int(a.q)) * vec[k]
        if not iszero(s):
            Z[m] = s
    return Z


def corr_from_function(f):
    """f sends a monomial mask of H^*(X_j) to its image (a dict)."""
    mat = [[0] * 16 for _ in range(16)]
    for yb in range(16):
        for m, c in f(yb).items():
            mat[m][yb] = mat[m][yb] + c
    return mat


def U0_class():
    """X_j x {0}: y -> (int y) pt."""
    pt = sc(Fr(1, 2), wedge(theta_x(), theta_x()))
    return class_from_corr(corr_from_function(lambda yb: sc(integ4({yb: Fr(1)}), pt)))


def P_class(unit=Fr(1)):
    """X_j x X_j: y -> (int y) 1."""
    return class_from_corr(corr_from_function(
        lambda yb: one(unit * integ4({yb: Fr(1)}))))


def T_class(d):
    """T(d): y_0 -> -(d^2/2) theta^2 y_0, y_2 -> (d/2) y_2, y_3 -> (3d/2) y_3,
    y_4 -> 3d y_4 (graph type)."""
    th2 = wedge(theta_x(), theta_x())

    def f(yb):
        k = popc(yb)
        y = {yb: d * 0 + 1}
        if k == 0:
            return sc(-d * d * Fr(1, 2), wedge(th2, y))
        if k == 2:
            return sc(d * Fr(1, 2), y)
        if k == 3:
            return sc(d * Fr(3, 2), y)
        if k == 4:
            return sc(d * 3, y)
        return {}
    return class_from_corr(corr_from_function(f))


def W_class(d):
    return sub(T_class(d), P_class(d * 0 + 1))


def _pw(x, k):
    r = x * 0 + 1
    for _ in range(k):
        r = r * x
    return r


def graph_class(b, a, c):
    """(b, a)_*(c) for the map x -> (b x, a x) of the factor, c of even degree:
    the correspondence y_k -> b^k a^(4 - k - m) (y_k ^ c_m); b, a Fractions or
    elements of K."""
    if not hasattr(b, "regmat"):
        b = Fr(b)
    if not hasattr(a, "regmat"):
        a = Fr(a)

    def f(yb):
        k = popc(yb)
        out = {}
        for mm, v in wedge({yb: Fr(1)}, c).items():
            tot = popc(mm)
            coef = _pw(b, k) * _pw(a, 4 - tot)
            if not iszero(coef):
                out[mm] = out.get(mm, 0) + coef * v
        return clean(out)
    return class_from_corr(corr_from_function(f))


def graph_geometric(b, a):
    """the class of the graph {(b x, a x)} as prod_i (b b_i - a a_i), up to the
    orientation sign fixed by [Delta]."""
    t = one(Fr(1))
    for i in range(4):
        t = wedge(t, add(gen(4 + i, Fr(b)), gen(i, -Fr(a))))
    return sc(-1, t)


# ------------------------------------------------------------------ Orlov transform
def orlov(Z):
    """ch Phi(Z) on A_j for a class Z on X_j x X_j."""
    imgs = {}
    for i in range(4):
        imgs[i] = add(gen(i), gen(8 + i))          # a_i -> x_i + y_i
        imgs[4 + i] = gen(8 + i)                   # b_i -> y_i
    Zs = lin_subst(Z, imgs)
    ey = expo(add(*[wedge(gen(8 + i), gen(4 + i)) for i in range(4)]))
    out = {}
    for m, c in wedge(Zs, ey).items():
        if (m >> 8) == TOP4:
            k = m & TOP8
            out[k] = out.get(k, 0) + ORI * c
    return clean(out)


# ------------------------------------------------------------------ F-action, SU_j
def Mstar(d):
    im = {0: gen(6, -1), 2: gen(4, 1), 1: gen(7, -1), 3: gen(5, 1),
          4: gen(2, -d), 6: gen(0, d), 5: gen(3, -d), 7: gen(1, d)}
    return im


def Jcx():
    """the complex structure of X x Xhat on H^1(A_j): x0 -> -x2, x2 -> x0, ..."""
    return {0: gen(2, -1), 2: gen(0, 1), 1: gen(3, -1), 3: gen(1, 1),
            4: gen(6, -1), 6: gen(4, 1), 5: gen(7, -1), 7: gen(5, 1)}


def lin_to_mat(im, n=8):
    return [[im.get(j, {}).get(1 << i, 0) for j in range(n)] for i in range(n)]


def mat_to_lin(A, n=8):
    im = {}
    for j in range(n):
        v = {1 << i: A[i][j] for i in range(n) if not iszero(A[i][j])}
        if v:
            im[j] = v
    return im


def su_basis(d):
    """a basis of su_j(d) = {X : [X, M*] = 0, X.eta = 0, tr(M* X) = 0}, d rational."""
    d = Fr(d)
    Mm = lin_to_mat(Mstar(d))
    rows = []
    for i in range(8):
        for j in range(8):
            r = [Fr(0)] * 64
            for k in range(8):
                r[i * 8 + k] += Mm[k][j]
                r[k * 8 + j] -= Mm[i][k]
            rows.append(r)
    et = eta(d)
    cols = []
    for idx in range(64):
        A = [[Fr(0)] * 8 for _ in range(8)]
        A[idx // 8][idx % 8] = Fr(1)
        cols.append(derivation(et, mat_to_lin(A)))
    for k in sorted(set(k for c in cols for k in c)):
        rows.append([c.get(k, Fr(0)) for c in cols])
    r = [Fr(0)] * 64
    for i in range(8):
        for k in range(8):
            r[k * 8 + i] += Mm[i][k]
    rows.append(r)
    basis = []
    for vec in nullspace_Q(rows, 64):
        X = [[vec[i * 8 + j] for j in range(8)] for i in range(8)]
        basis.append(mat_to_lin(X))
    return basis


def invariants(d, degs=range(9)):
    """a basis of the su_j(d)-invariant classes of A_j (d rational)."""
    B = su_basis(d)
    out = []
    for k in degs:
        mons = [m for m in range(256) if popc(m) == k]
        rows = []
        for X in B:
            imgs = [derivation({m: Fr(1)}, X) for m in mons]
            for kk in sorted(set(kk for im in imgs for kk in im)):
                rows.append([im.get(kk, Fr(0)) for im in imgs])
        for vec in nullspace_Q(rows, len(mons)):
            out.append({m: vec[t] for t, m in enumerate(mons) if vec[t] != 0})
    return out


def is_flat(u, basis):
    return all(not derivation(u, X) for X in basis)


# ------------------------------------------------------------------ contraction on A_j
def complex_ops(mk, places=1):
    """for each holomorphic coordinate p = g_r + i g_s: the vector d_p (dual to p)
    as an interior-product map, and the antiholomorphic 1-form q = conj(p);
    mk constructs elements of Q(sqrt D, i)."""
    I = mk(0, 0, 1)
    half = mk(Fr(1, 2))
    mhalfi = mk(0, 0, Fr(-1, 2))
    ds, qs = [], []
    for place in range(places):
        off = 8 * place
        for (r, s) in [(0, 2), (1, 3), (4, 6), (5, 7)]:
            ds.append({off + r: half, off + s: mhalfi})
            qs.append({1 << (off + r): mk(1), 1 << (off + s): -I})
    return ds, qs


def HT2_images(w, mk, places=1):
    """images of the basis of HT^2 = wedge^2 H^{0,1} + H^{0,1} T + wedge^2 T,
    with labels (kind, a, b)."""
    ds, qs = complex_ops(mk, places)
    n = len(ds)
    imgs, labels = [], []
    for a in range(n):
        for b in range(a + 1, n):
            imgs.append(wedge(wedge(qs[a], qs[b]), w))
            labels.append(("QQ", a, b))
    for a in range(n):
        for b in range(n):
            imgs.append(wedge(qs[a], interior(w, ds[b])))
            labels.append(("QD", a, b))
    for a in range(n):
        for b in range(a + 1, n):
            imgs.append(interior(interior(w, ds[b]), ds[a]))
            labels.append(("DD", a, b))
    return imgs, labels


def HT1_images(w, mk, places=1):
    ds, qs = complex_ops(mk, places)
    return [wedge(q, w) for q in qs] + [interior(w, dd) for dd in ds]
