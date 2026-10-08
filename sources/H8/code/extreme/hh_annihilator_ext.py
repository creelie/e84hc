#!/usr/bin/env python3
"""
hh_annihilator_ext.py  (round 11, track E, item 2)

Stress test of item (XXXVIII) / thm:hhsplitting at larger n.

Model: exactly the model of code/hochschild_annihilator.py (imported
read-only).  4n cohomology generators x (0..n-1), y (n..2n-1), bar x
(2n..3n-1), bar y (3n..4n-1); alpha_+ = x ^ bar x, alpha_- = y ^ bar y;
HH^1 = P + Q with P = (wedge bar x, contract y), Q = (wedge bar y, contract x),
monomials of HH^* acting by HA.apply-order (decreasing operator index first).

For each n and each degree k = 0..4n this script computes, EXACTLY (Python
Fractions, or Gaussian rationals for a complex omega):

  rank of  HH^k -> H^*(A),  xi |-> xi _| omega,  omega = a alpha_+ + b alpha_-

by sparse Gaussian elimination on the image rows (every row has at most two
nonzero entries, and the elimination never creates rows with more), and
compares dim Ann = binom(4n,k) - rank with

     binom(4n,k) - 2 binom(2n,k) + delta_{k,2n}   (k >= 1),     0  (k = 0).

It also re-checks the structural statements (A), (C), (D) of item (XXXVIII)
at every n run: P, Q are the degree-one annihilators of alpha_+, alpha_-;
every monomial meeting both P and Q kills omega, and there are
2^{4n} - (2^{2n+1} - 1) of them; contraction with alpha_- is injective on
wedge^* P, with alpha_+ on wedge^* Q, and the two images meet in exactly
one line, in degree 2n.

The action of a monomial is computed by a fast bitwise routine; that routine
is compared with HA.wedge_gen / HA.contract_gen (the paper's own code) on
EVERY monomial for n <= 4 before being trusted.

Run:  python3 hh_annihilator_ext.py [nmax]      (default nmax = 5)
"""
import os
import sys
import time
from fractions import Fraction as Fr
from math import comb

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import hochschild_annihilator as HA  # noqa: E402

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("\n         " + detail) if detail else ""), flush=True)


# ---------------------------------------------------------- Gaussian rationals
class GQ:
    """a + b i with a, b Fractions (exact)"""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(self, o):
        o = o if isinstance(o, GQ) else GQ(o)
        return GQ(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, GQ) else GQ(o)
        return GQ(self.a - o.a, self.b - o.b)

    def __rsub__(self, o):
        return GQ(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, GQ) else GQ(o)
        return GQ(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def __neg__(self):
        return GQ(-self.a, -self.b)

    def __truediv__(self, o):
        o = o if isinstance(o, GQ) else GQ(o)
        nrm = o.a * o.a + o.b * o.b
        return GQ((self.a * o.a + self.b * o.b) / nrm,
                  (self.b * o.a - self.a * o.b) / nrm)

    def __eq__(self, o):
        o = o if isinstance(o, GQ) else GQ(o)
        return self.a == o.a and self.b == o.b

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        return hash((self.a, self.b))

    def __repr__(self):
        return "(%s%s%si)" % (self.a, "-" if self.b < 0 else "+", abs(self.b))


def is_zero(x):
    return x == 0


# ------------------------------------------------------------- the model
def build(n):
    N = 4 * n
    XS = list(range(0, n))
    YS = list(range(n, 2 * n))
    BXS = list(range(2 * n, 3 * n))
    BYS = list(range(3 * n, 4 * n))
    ops = ([("w", i) for i in BXS] + [("c", j) for j in YS]
           + [("w", i) for i in BYS] + [("c", j) for j in XS])
    assert len(ops) == N

    def top(idx):
        u = {0: Fr(1)}
        for i in idx:
            u = HA.wedge_gen(i, u)
        return u

    alpha_p = top(XS + BXS)
    alpha_m = top(YS + BYS)
    return N, ops, alpha_p, alpha_m


def ha_apply_mono(ops, mask, u):
    """the paper's own action (HA.run_n.apply_mono), verbatim"""
    for t in sorted(HA.bits(mask), reverse=True):
        kind, i = ops[t]
        u = HA.wedge_gen(i, u) if kind == "w" else HA.contract_gen(i, u)
        if not u:
            return {}
    return u


def fast_apply(ops_kind, ops_idx, N, mask, cmask, csign):
    """action of the HH monomial `mask` on the single cohomology monomial
    csign * e_{cmask}; returns (newmask, sign) or None.  Same conventions as
    HA.wedge_gen / HA.contract_gen, operators applied in decreasing order."""
    t = N - 1
    s = csign
    a = cmask
    m = mask
    while m:
        t = m.bit_length() - 1
        m ^= 1 << t
        i = ops_idx[t]
        bit = 1 << i
        if ops_kind[t]:            # wedge e_i ^ a
            if a & bit:
                return None
            # sign of merging (1<<i, a): number of elements of a below i ...
            # HA.wedge_sign(1<<i, a): for each element j of a, if bin((1<<i)
            # >> (j+1)).count("1") is odd flip; that is j < i.
            if bin(a & (bit - 1)).count("1") & 1:
                s = -s
            a |= bit
        else:                      # contraction iota_i a
            if not (a & bit):
                return None
            if bin(a & (bit - 1)).count("1") & 1:
                s = -s
            a ^= bit
    return a, s


def compare_with_ha(n):
    """compare fast_apply with the paper's code on every HH monomial, on
    alpha_+ and alpha_-"""
    N, ops, ap, am = build(n)
    kinds = [1 if k == "w" else 0 for k, _ in ops]
    idxs = [i for _, i in ops]
    (kp, vp), = ap.items()
    (km, vm), = am.items()
    bad = 0
    for mask in range(1 << N):
        for key, val, alpha in ((kp, vp, ap), (km, vm, am)):
            ref = ha_apply_mono(ops, mask, alpha)
            got = fast_apply(kinds, idxs, N, mask, key, int(val))
            if got is None:
                ok = (ref == {})
            else:
                ok = (ref == {got[0]: Fr(got[1])})
            if not ok:
                bad += 1
    return bad


# ----------------------------------------------------- sparse exact rank
def sparse_rank(rows):
    """exact rank of sparse rows {col: field element}; pivot = least column.
    Rows with <= 2 entries stay with <= 2 entries under this reduction."""
    piv = {}
    maxlen = 0
    for r in rows:
        r = {c: v for c, v in r.items() if not is_zero(v)}
        while r:
            c = min(r)
            if c in piv:
                p = piv[c]
                f = r[c] / p[c]
                for cc, vv in p.items():
                    x = r.get(cc, 0) - f * vv
                    if is_zero(x):
                        r.pop(cc, None)
                    else:
                        r[cc] = x
            else:
                piv[c] = r
                maxlen = max(maxlen, len(r))
                break
    return len(piv), maxlen


def run_n(n, coeff_pairs, compare_ha):
    print("=" * 72)
    print("n = %d: HH^* of dimension 2^%d = %d" % (n, 4 * n, 2 ** (4 * n)),
          flush=True)
    t0 = time.time()
    N, ops, ap, am = build(n)
    kinds = [1 if k == "w" else 0 for k, _ in ops]
    idxs = [i for _, i in ops]
    (kp, vp), = ap.items()
    (km, vm), = am.items()
    vp, vm = int(vp), int(vm)

    if compare_ha:
        bad = compare_with_ha(n)
        check("n=%d: fast bitwise action agrees with HA.wedge_gen/"
              "HA.contract_gen on all %d monomials, on alpha_+ and alpha_-"
              % (n, 1 << N), bad == 0, "mismatches: %d" % bad)

    dimP = 2 * n
    pmask = (1 << dimP) - 1
    qmask = ((1 << N) - 1) ^ pmask

    # images of every monomial on alpha_+ and alpha_- (the whole computation)
    img_p = {}
    img_m = {}
    for mask in range(1 << N):
        r = fast_apply(kinds, idxs, N, mask, kp, vp)
        if r is not None:
            img_p[mask] = r
        r = fast_apply(kinds, idxs, N, mask, km, vm)
        if r is not None:
            img_m[mask] = r
    print("  images computed in %.1fs: %d monomials act nonzero on alpha_+, "
          "%d on alpha_-" % (time.time() - t0, len(img_p), len(img_m)),
          flush=True)

    # (A) degree one
    okA = (all((1 << t) not in img_p for t in range(dimP))
           and all((1 << t) not in img_m for t in range(dimP, N))
           and all((1 << t) in img_m for t in range(dimP))
           and all((1 << t) in img_p for t in range(dimP, N)))
    check("n=%d: P = Ann_{HH^1}(alpha_+), Q = Ann_{HH^1}(alpha_-) (on the "
          "basis operators)" % n, okA)

    # (C) mixed monomials kill both alpha_+ and alpha_-
    mixed_ok = all(not ((m & pmask) and (m & qmask)) for m in img_p) and \
        all(not ((m & pmask) and (m & qmask)) for m in img_m)
    n_mixed = sum(1 for m in range(1 << N) if (m & pmask) and (m & qmask))
    check("n=%d: every monomial meeting both P and Q kills alpha_+ and "
          "alpha_-; the ideal they span has codimension %d = 2^{2n+1}-1"
          % (n, (1 << N) - n_mixed),
          mixed_ok and (1 << N) - n_mixed == 2 ** (2 * n + 1) - 1)
    # nonzero actions: exactly wedge^*Q on alpha_+, wedge^*P on alpha_-
    okPQ = (set(img_p) == {m for m in range(1 << N) if not (m & pmask)}
            and set(img_m) == {m for m in range(1 << N) if not (m & qmask)})
    check("n=%d: the monomials acting nonzero on alpha_+ are exactly those "
          "of wedge^*Q, on alpha_- exactly those of wedge^*P" % n, okPQ)

    # (D) injectivity of the two contractions, and the meeting of the images
    imgsP = [img_m[m][0] for m in img_m]          # m in wedge^*P
    imgsQ = [img_p[m][0] for m in img_p]          # m in wedge^*Q
    injP = len(set(imgsP)) == len(imgsP)
    injQ = len(set(imgsQ)) == len(imgsQ)
    common = set(imgsP) & set(imgsQ)
    common_deg = sorted({bin(m).count("1") for m in common})
    # which HH monomials produce the common images
    srcP = [m for m in img_m if img_m[m][0] in common]
    srcQ = [m for m in img_p if img_p[m][0] in common]
    check("n=%d: contraction with alpha_- injective on wedge^*P and with "
          "alpha_+ on wedge^*Q (monomials go to distinct monomials)" % n,
          injP and injQ)
    check("n=%d: the two images share exactly one monomial, the generator of "
          "H^{0,2n}, reached from top(P) and top(Q) in HH-degree 2n = %d"
          % (n, 2 * n),
          len(common) == 1 and srcP == [pmask] and srcQ == [qmask]
          and list(common)[0] == ((1 << N) - 1) ^ ((1 << (2 * n)) - 1),
          "common image masks %s (cohomology degree %s), from HH monomials "
          "%s and %s" % ([bin(c) for c in common], common_deg,
                         [bin(m) for m in srcP], [bin(m) for m in srcQ]))

    # the rank in every degree, exactly, for each (a, b)
    for a, b in coeff_pairs:
        dims, ranks, maxlens = [], [], []
        for k in range(N + 1):
            rows = []
            # rows of the zero monomial images do not change the rank; the
            # images of all 2^{4n} monomials were computed above
            for m in sorted(set(img_p) | set(img_m)):
                if bin(m).count("1") != k:
                    continue
                row = {}
                if m in img_p:
                    key, s = img_p[m]
                    row[key] = row.get(key, 0) + s * a
                if m in img_m:
                    key, s = img_m[m]
                    row[key] = row.get(key, 0) + s * b
                if row:
                    rows.append(row)
            r, ml = sparse_rank(rows)
            ranks.append(r)
            maxlens.append(ml)
            dims.append(comb(N, k) - r)
        expected = []
        for k in range(N + 1):
            if k == 0:
                expected.append(0)
            else:
                expected.append(comb(N, k) - 2 * comb(2 * n, k)
                                + (1 if k == 2 * n else 0))
        check("n=%d, omega = %s alpha_+ + %s alpha_-: dim Ann_{HH^k}(omega) "
              "= binom(4n,k) - 2 binom(2n,k) + delta_{k,2n} for k = 1..%d, "
              "and 0 for k = 0" % (n, a, b, N), dims == expected,
              "ranks  %s\ndims   %s\nexpect %s\n(max nonzeros in a pivot "
              "row: %d; exact elimination over %s)"
              % (ranks, dims, expected, max(maxlens),
                 "Q(i)" if isinstance(a, GQ) else "Q"))
        # the literal formula at k = 0 gives -1
        if a == coeff_pairs[0][0] and b == coeff_pairs[0][1]:
            print("  note: at k = 0 the literal formula binom(4n,0) - "
                  "2 binom(2n,0) gives %d, the true annihilator is %d"
                  % (1 - 2, dims[0]))
        # degree 2: Ann = P ^ Q of dimension 4n^2, quotient 2n(2n-1)
        if n >= 2:
            check("n=%d: dim Ann_{HH^2} = 4n^2 = %d, rank 2n(2n-1) = %d"
                  % (n, 4 * n * n, 2 * n * (2 * n - 1)),
                  dims[2] == 4 * n * n and ranks[2] == 2 * n * (2 * n - 1))
    print("  n = %d done in %.1fs" % (n, time.time() - t0), flush=True)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    pairs = [(Fr(1), Fr(1)), (Fr(3), Fr(-5)), (Fr(1), Fr(2)),
             (GQ(2, 3), GQ(2, -3))]
    for n in range(1, nmax + 1):
        run_n(n, pairs if n <= 5 else pairs[:2], compare_ha=(n <= 4))
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
