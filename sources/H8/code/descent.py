#!/usr/bin/env python3
"""
descent.py

Descent and scalar extension for Weil classes.  Item (LIV).

Write W(F,n,delta) for the statement that every abelian variety of
(F,n,delta)-Weil type, F a CM field of degree 2m, has algebraic Weil classes
(m = 1 is the imaginary quadratic case, where the paper writes W(K,n,delta)).

  DESCENT.  Let B be of (F,n,delta)-Weil type and Y of (F,1,delta')-Weil
  type, dim Y = 2m.  Then X = B x Y, with the diagonal F-action and the
  product polarisation, is of (F,n+1,delta*delta')-Weil type, and the
  algebraic correspondence

        P(x) = pr_{B*}( x . pr_Y^*( eta_Y^{2m-2} . y' ) ),

  y' a nonzero Weil class of Y, which lies in H^2 and is algebraic by the
  Lefschetz theorem on (1,1) classes, maps W_F(X) isomorphically onto
  W_F(B).  So W(F,n+1,delta'') implies W(F,n,delta) for every delta.

  SCALAR EXTENSION.  For CM fields K contained in F and B of (K,n,delta)-Weil
  type, B_F = B (x)_{O_K} O_F is of (F,n,iota(delta))-Weil type, and for
  j : B -> B_F, b -> b (x) 1, one has j^* Tr_{F/Q}(a det_F) =
  Tr_{K/Q}(Tr_{F/K}(a) det_K), so j^* maps W_F(B_F) onto W_K(B).  So
  W(F,n,iota(delta)) implies W(K,n,delta).

What is checked, in exact rational arithmetic, with cohomology classes as
alternating Q-multilinear forms on H_1 = F^N, Weil classes the forms
Tr_{F/Q}(a det_F), a in F, and the polarisation Tr_{F/Q}(xi H):

  (A) descent, for F = Q(i), Q(sqrt-2), Q(sqrt-3), Q(zeta5), Q(zeta8) and
      small n: dim W_F(B) = 2m, P(W_F(X)) has rank 2m and lies in W_F(B),
      and, as a control, P kills W_F(X) when y' is replaced by the
      polarisation of Y, which is not a Weil class;

  (B) the discriminant of B x Y is the product, and H_Y = diag(1,-t),
      t in Q_{>0}, realises every class, so that every (K,n,delta) lies
      under (K,n+1,delta'') for any delta'';

  (C) scalar extension for Q(i) in Q(zeta8), Q(sqrt-7) in Q(zeta7) and
      Q(sqrt-3) in Q(zeta9): j^* W_F(B_F) = W_K(B).

With --extreme, (A) is run for n up to 5 over Q(i), up to 4 over Q(sqrt-2)
and Q(sqrt-3), up to 3 over Q(sqrt-5), Q(zeta5) and Q(zeta8), and up to 2 over
the degree-six field Q(zeta7); and (C) for n up to 3.

The case K imaginary quadratic, n + 1 = 3, is the degeneration argument of
Schoen through which Markman obtains every Weil fourfold from sixfolds of
trivial discriminant; the lemma is its form in every dimension and for every
CM field.

Run:  python3 descent.py             (under a minute)
      python3 descent.py --extreme   (a few minutes)
"""

from fractions import Fraction as Fr
from itertools import combinations, product
import sys

# ----------------------------------------------------------- number fields
class Field:
    """F = Q[x]/(f), power basis 1, z, ..., z^{D-1}; conj given as a vector"""
    def __init__(self, name, minpoly, conj_z, xi, tpos):
        self.name = name
        self.f = [Fr(c) for c in minpoly]          # monic, low -> high, len D+1
        self.D = len(minpoly) - 1
        self.m = self.D // 2
        # multiplication table of basis elements
        D = self.D
        red = {}
        # z^k for k < 2D-1 reduced
        pw = []
        for k in range(2 * D - 1):
            v = [Fr(0)] * (2 * D)
            v[k] = Fr(1)
            for e in range(2 * D - 2, D - 1, -1):
                c = v[e]
                if c:
                    v[e] = Fr(0)
                    for t in range(D):
                        v[e - D + t] -= c * self.f[t]
            pw.append(v[:D])
        self.pw = pw
        self.conj_z = [Fr(c) for c in conj_z]
        # conj of z^k
        self.conj_basis = [self.one()]
        for k in range(1, D):
            self.conj_basis.append(self.mul(self.conj_basis[-1], self.conj_z))
        # trace of basis elements: Tr(z^k) = trace of mult matrix
        self.trb = []
        for k in range(D):
            tr = Fr(0)
            for j in range(D):
                tr += pw[k + j][j]
            self.trb.append(tr)
        self.xi = [Fr(c) for c in xi]
        self.tpos = [Fr(c) for c in tpos]   # a totally positive element of F0

    def one(self):
        v = [Fr(0)] * self.D
        v[0] = Fr(1)
        return v

    def basis(self, k):
        v = [Fr(0)] * self.D
        v[k] = Fr(1)
        return v

    def mul(self, a, b):
        out = [Fr(0)] * self.D
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        c = ai * bj
                        row = self.pw[i + j]
                        for t in range(self.D):
                            if row[t]:
                                out[t] += c * row[t]
        return out

    def add(self, a, b):
        return [x + y for x, y in zip(a, b)]

    def scal(self, c, a):
        return [c * x for x in a]

    def conj(self, a):
        out = [Fr(0)] * self.D
        for k, ak in enumerate(a):
            if ak:
                for t in range(self.D):
                    out[t] += ak * self.conj_basis[k][t]
        return out

    def tr(self, a):
        return sum(ak * self.trb[k] for k, ak in enumerate(a))


def perm_sign(seq):
    s, seq = 1, list(seq)
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                s = -s
    return s


# ------------------------------------------------------------ forms on W
# W = F^N ; Q-basis index q = i*D + j  <->  z^j in F-coordinate i.
def weil_form(Fd, N, a, coords):
    """the alternating form Tr(a det_F) restricted to the Q-basis tuples
    whose F-coordinates, in the order of `coords` (the F-coordinates of the
    variety), each occur once.  Returns dict: sorted q-tuple -> value."""
    D = Fd.D
    out = {}
    for js in product(range(D), repeat=len(coords)):
        qs = [coords[t] * D + js[t] for t in range(len(coords))]
        # det_F( z^{j_t} e_{coords[t]} ) in the order given = prod z^{j_t}
        # times the sign of the permutation sorting coords (here coords sorted)
        pr = Fd.one()
        for j in js:
            pr = Fd.mul(pr, Fd.basis(j))
        val = Fd.tr(Fd.mul(a, pr))
        order = sorted(range(len(qs)), key=lambda t: qs[t])
        sgn = perm_sign(order)
        key = tuple(sorted(qs))
        if val:
            out[key] = out.get(key, Fr(0)) + sgn * val
    return out


def wedge(al, be):
    """wedge of alternating forms given on sorted tuples (no factorials)"""
    out = {}
    for S, a in al.items():
        for T, b in be.items():
            if set(S) & set(T):
                continue
            U = S + T
            sgn = perm_sign(sorted(range(len(U)), key=lambda t: U[t]))
            key = tuple(sorted(U))
            out[key] = out.get(key, Fr(0)) + sgn * a * b
    return {k: v for k, v in out.items() if v}


def herm_form_2(Fd, coords, hdiag):
    """eta(w,w') = Tr(xi * H(l w, l w')), H = diag(hdiag) (entries in F0),
    H(x,y) = sum_i x_i h_i conj(y_i); as a dict on sorted pairs"""
    D = Fd.D
    out = {}
    for ci, i in enumerate(coords):
        for j in range(D):
            for j2 in range(D):
                q1, q2 = i * D + j, i * D + j2
                if q1 >= q2:
                    continue
                # eta(z^j e_i, z^j2 e_i) = Tr(xi h_i z^j conj(z^j2))
                v = Fd.tr(Fd.mul(Fd.mul(Fd.xi, hdiag[ci]),
                                 Fd.mul(Fd.basis(j), Fd.conj(Fd.basis(j2)))))
                if v:
                    out[(q1, q2)] = v
    return out


def rank(rows):
    """exact rank of a list of equal-length Fraction vectors"""
    M = [list(r) for r in rows if any(r)]
    if not M:
        return 0
    rk, ncol = 0, len(M[0])
    for c in range(ncol):
        piv = None
        for r in range(rk, len(M)):
            if M[r][c] != 0:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        pv = M[rk][c]
        for r in range(len(M)):
            if r != rk and M[r][c] != 0:
                f = M[r][c] / pv
                M[r] = [x - f * y for x, y in zip(M[r], M[rk])]
        rk += 1
    return rk


def descent_check(Fd, n, tval):
    D, m = Fd.D, Fd.m
    NB, NY = 2 * n, 2                   # F-dimensions
    cB = list(range(NB))
    cY = list(range(NB, NB + NY))
    Yq = [i * D + j for i in cY for j in range(D)]          # Q-indices of W_Y
    # W_F(B), W_F(X) spanned by a = basis elements of F
    WB = [weil_form(Fd, NB, Fd.basis(k), cB) for k in range(D)]
    WX = [weil_form(Fd, NB + NY, Fd.basis(k), cB + cY) for k in range(D)]
    # Y's Weil class y' = Tr(det_F) on Y, and its polarisation
    yprime = weil_form(Fd, NY, Fd.one(), cY)
    t = Fd.tpos if tval is None else tval
    hY = [Fd.one(), Fd.scal(Fr(-1), t)]              # H_Y = diag(1, -t)
    etaY = herm_form_2(Fd, cY, hY)
    mt = dict(yprime)
    for _ in range(2 * m - 2):
        mt = wedge(etaY, mt)
    # control: eta^{2m-1} in place of eta^{2m-2} y'
    ctrl = {(): Fr(1)}
    for _ in range(2 * m - 1):
        ctrl = wedge(etaY, ctrl)
    Ytop = tuple(Yq)

    def P(x, mform):
        """pr_{B*}(x u pr_Y^* mform): value on each 2n-tuple U of B-indices"""
        out = {}
        for key, val in x.items():
            U = tuple(q for q in key if q < NB * D)
            T = tuple(q for q in key if q >= NB * D)
            comp = tuple(q for q in Ytop if q not in T)
            mv = mform.get(comp)
            if not mv:
                continue
            # (x ^ m)(U, Ytop): sign of arranging U+T+comp into U+Ytop
            seq = list(U) + list(T) + list(comp)
            sgn = perm_sign(sorted(range(len(seq)), key=lambda s: seq[s]))
            out[U] = out.get(U, Fr(0)) + sgn * val * mv
        return {k: v for k, v in out.items() if v}

    keys = sorted(set().union(*[set(w) for w in WB]))
    vecB = [[w.get(k, Fr(0)) for k in keys] for w in WB]
    PX = [P(x, mt) for x in WX]
    extra = set().union(*[set(p) for p in PX]) - set(keys)
    vecP = [[p.get(k, Fr(0)) for k in keys] for p in PX]
    rB, rP, rJ = rank(vecB), rank(vecP), rank(vecB + vecP)
    PC = [P(x, ctrl) for x in WX]
    ctrl_zero = all(not p for p in PC)
    ok = (rB == D and rP == D and rJ == D and not extra and ctrl_zero)
    return ok, (rB, rP, rJ, not extra, ctrl_zero)


FIELDS = [
    # name, minpoly (low->high, monic), conj(z), xi (totally imaginary), t in F0 >> 0
    ("Q(i)",      [1, 0, 1],          [0, -1],            [0, 1],           [3, 0]),
    ("Q(sqrt-2)", [2, 0, 1],          [0, -1],            [0, 1],           [5, 0]),
    ("Q(sqrt-3)", [3, 0, 1],          [0, -1],            [0, 1],           [7, 0]),
    ("Q(sqrt-5)", [5, 0, 1],          [0, -1],            [0, 1],           [2, 0]),
    # Q(zeta5): z^4+z^3+z^2+z+1 ; conj z = z^4 = -1-z-z^2-z^3 ; xi = z - z^4
    #           t = 3 + z + z^4 = 3 + (z + conj z), totally positive
    ("Q(zeta5)",  [1, 1, 1, 1, 1],    [-1, -1, -1, -1],   [1, 2, 1, 1],     [2, 0, -1, -1]),
    # Q(zeta8) = Q(i, sqrt2): z^4 + 1 ; conj z = z^7 = -z^3 ; xi = z^2 = i
    #           t = 3 + z - z^3 = 3 + sqrt2, totally positive
    ("Q(zeta8)",  [1, 0, 0, 0, 1],    [0, 0, 0, -1],      [0, 0, 1, 0],     [3, 1, 0, -1]),
    # Q(zeta7), degree 6: conj z = z^6 = -1-z-...-z^5 ; xi = z - z^6
    ("Q(zeta7)",  [1, 1, 1, 1, 1, 1, 1], [-1, -1, -1, -1, -1, -1],
                  [1, 2, 1, 1, 1, 1], [3, 0, 0, 0, 0, 0]),
]


def sanity(Fd):
    """xi totally imaginary: conj(xi) = -xi ; t in F0: conj(t) = t"""
    cx = Fd.conj(Fd.xi)
    ct = Fd.conj(Fd.tpos)
    return (all(a == -b for a, b in zip(cx, Fd.xi))
            and all(a == b for a, b in zip(ct, Fd.tpos)))


def scalar_check(Fbig, Ksmall, s_in_F, n):
    """s_in_F: coordinates in Fbig of the generator s of Ksmall (s^2 = -d)."""
    DK, DF = Ksmall.D, Fbig.D
    # images of the K-basis 1, s in F
    jb = [Fbig.one(), [Fr(c) for c in s_in_F]]
    # sanity: s^2 in F equals s^2 in K (i.e. -d)
    s2K = Ksmall.mul(Ksmall.basis(1), Ksmall.basis(1))     # = [-d, 0]
    s2F = Fbig.mul(jb[1], jb[1])
    assert s2F == [s2K[0]] + [Fr(0)] * (DF - 1), (s2F, s2K)
    tuples = list(product(range(DK), repeat=2 * n))
    # W_K(B) on K-basis tuples (one basis vector b_j e_i per coordinate i)
    WK = []
    for k in range(DK):
        row = []
        for js in tuples:
            pr = Ksmall.one()
            for j in js:
                pr = Ksmall.mul(pr, Ksmall.basis(j))
            row.append(Ksmall.tr(Ksmall.mul(Ksmall.basis(k), pr)))
        WK.append(row)
    # j^* W_F(B_F): value Tr_F(a * prod j(b_{j_i}))
    JW = []
    for k in range(DF):
        row = []
        for js in tuples:
            pr = Fbig.one()
            for j in js:
                pr = Fbig.mul(pr, jb[j])
            row.append(Fbig.tr(Fbig.mul(Fbig.basis(k), pr)))
        JW.append(row)
    rK, rJ, rAll = rank(WK), rank(JW), rank(WK + JW)
    return rK == 2 and rJ == 2 and rAll == 2, (rK, rJ, rAll)



PASS, FAIL = [], []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % (tag, name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


def main():
    extreme = "--extreme" in sys.argv
    fields = {row[0]: Field(*row) for row in FIELDS}
    plan = ({"Q(i)": [1, 2, 3, 4, 5], "Q(sqrt-2)": [1, 2, 3, 4],
             "Q(sqrt-3)": [1, 2, 3, 4], "Q(sqrt-5)": [1, 2, 3],
             "Q(zeta5)": [1, 2, 3], "Q(zeta8)": [1, 2, 3], "Q(zeta7)": [1, 2]}
            if extreme else
            {"Q(i)": [1, 2, 3], "Q(sqrt-2)": [1, 2], "Q(sqrt-3)": [1, 2],
             "Q(zeta5)": [1, 2], "Q(zeta8)": [1, 2]})
    print("  (A) descent: P maps W_F(B x Y) isomorphically onto W_F(B)")
    for name, ns in plan.items():
        Fd = fields[name]
        check("%s: the field data are consistent (xi totally imaginary, "
              "t totally positive)" % name, sanity(Fd))
        for n in ns:
            ok, (rB, rP, rJ, supp, ctrl) = descent_check(Fd, n, None)
            check("%s, n=%d -> n+1=%d: dim W_F(B) = %d, rank P(W_F(X)) = %d, joint "
                  "rank %d, control killed: %s" % (name, n, n + 1, rB, rP, rJ, ctrl), ok)
    print("  (B) the discriminant")
    ok, rng = True, __import__("random").Random(7)
    for n in range(1, 6):
        for t in (Fr(1), Fr(2), Fr(3), Fr(5), Fr(7, 3)):
            # a hermitian form of signature (n,n), diagonalised over K_0 = Q
            hB = [Fr(rng.randint(1, 9), rng.randint(1, 5)) for _ in range(n)] + \
                 [-Fr(rng.randint(1, 9), rng.randint(1, 5)) for _ in range(n)]
            hX = hB + [Fr(1), -t]
            det = lambda h: __import__("functools").reduce(lambda a, b: a * b, h, Fr(1))
            sig = lambda h: (sum(1 for x in h if x > 0), sum(1 for x in h if x < 0))
            discB = Fr(-1) ** n * det(hB)
            discX = Fr(-1) ** (n + 1) * det(hX)
            ok = ok and discX == discB * t and sig(hX) == (n + 1, n + 1)
    check("H_X = H_B (+) diag(1,-t) has signature (n+1,n+1) and normalised "
          "discriminant (-1)^(n+1) det H_X = [(-1)^n det H_B] t, so every class of "
          "Q_{>0}/Nm(K^x) is reached by choosing Y", ok)
    print("  (C) scalar extension: j^* W_F(B_F) = W_K(B)")
    Qi = Field("Q(i)", [1, 0, 1], [0, -1], [0, 1], [3, 0])
    Qz8 = fields["Q(zeta8)"]
    Q7 = Field("Q(sqrt-7)", [7, 0, 1], [0, -1], [0, 1], [2, 0])
    Qz7 = fields["Q(zeta7)"]
    Q3 = Field("Q(sqrt-3)", [3, 0, 1], [0, -1], [0, 1], [2, 0])
    Qz9 = Field("Q(zeta9)", [1, 0, 0, 1, 0, 0, 1], [0, 0, -1, 0, 0, -1],
                [1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0])
    for n in ((1, 2, 3) if extreme else (1, 2)):
        for Fb, Ks, s, label in ((Qz8, Qi, [0, 0, 1, 0], "Q(i) in Q(zeta8), i = z^2"),
                                 (Qz7, Q7, [1, 2, 2, 0, 2, 0],
                                  "Q(sqrt-7) in Q(zeta7), sqrt-7 = the Gauss sum"),
                                 (Qz9, Q3, [1, 0, 0, 2, 0, 0],
                                  "Q(sqrt-3) in Q(zeta9), sqrt-3 = 2z^3 + 1")):
            ok, (rK, rJ, rAll) = scalar_check(Fb, Ks, s, n)
            check("%s, n=%d: dim W_K(B) = %d, rank j^*W_F(B_F) = %d, joint %d"
                  % (label, n, rK, rJ, rAll), ok)


if __name__ == "__main__":
    print("(LIV) descent and scalar extension for Weil classes")
    main()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
