#!/usr/bin/env python3
"""
t1_annihilator.py -- the (P2)/(P2') numbers for a quartic CM field at n = 2.

Eigen-model of H^1(A,C) for an abelian eightfold A of (F,2)-Weil type:
four embeddings sigma in {s1, s1bar, s2, s2bar} (s1bar = index 1, s2bar =
index 3), V_sigma = <x_{sigma,1}, x_{sigma,2}> (type (1,0)) + <y_{sigma,1},
y_{sigma,2}> (type (0,1)), complex conjugation x_{sigma,j} -> y_{sigmabar,j}.
Weil classes: alpha_sigma = x_{s,1} x_{s,2} y_{s,1} y_{s,2};
partial polarisations theta_tau = sum_{sigma | tau} sum_j x_{sigma,j} y_{sigmabar,j}
(after rescaling the y's, which only rescales the alpha_sigma); the
Lefschetz ring of a member with Hodge group Res SU(V,H) is C[theta_1, theta_2]
after complexification.

HT^2(A) = wedge^2 H^{0,1} + H^{0,1} (x) T + wedge^2 T, T = (H^{1,0})^dual,
of dimension 28 + 64 + 28 = 120, acting on H^*(A,C) by wedge, by
"wedge after contraction", and by double contraction.  For
gamma = omega + p(theta_1, theta_2) we compute exactly the rank r(gamma) of
xi -> xi |_ gamma and the dimension of the annihilator in each summand.

Upper bound for the generic rank: the tangent space of the polarised family
(dimension m n^2 = 8) always annihilates a flat family of Hodge classes
(Griffiths transversality), so r(gamma) <= 112; any exact evaluation giving
112 settles the generic value.  Evaluations at specific rational parameters
give exact values at those parameters (lower bounds for the generic rank).
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t1lib import *

SIG = 4          # embeddings
X = lambda s, j: 2 * s + j            # 0..7
Y = lambda s, j: 8 + 2 * s + j        # 8..15
BAR = {0: 1, 1: 0, 2: 3, 3: 2}
TAU = {0: 0, 1: 0, 2: 1, 3: 1}


def mono(*idx):
    sg, K = sort_sign(idx)
    return {K: Fr(sg)} if sg else {}


def contract(k, form):
    """odd derivation: contraction with the dual of generator k"""
    out = {}
    for I, c in form.items():
        if k in I:
            p = I.index(k)
            J = I[:p] + I[p + 1:]
            out[J] = out.get(J, Fr(0)) + (c if p % 2 == 0 else -c)
    return {K: v for K, v in out.items() if v != 0}


def alpha(s):
    return mono(X(s, 0), X(s, 1), Y(s, 0), Y(s, 1))


def theta(tau):
    f = {}
    for s in range(SIG):
        if TAU[s] == tau:
            for j in range(2):
                f = addf(f, mono(X(s, j), Y(BAR[s], j)))
    return f


def powf(f, k):
    out = {(): Fr(1)}
    for _ in range(k):
        out = wedge(out, f)
    return out


def ht2_ops():
    ops = []
    ys = [Y(s, j) for s in range(SIG) for j in range(2)]
    xs = [X(s, j) for s in range(SIG) for j in range(2)]
    for a, b in itertools.combinations(ys, 2):
        ops.append(("z", (a, b), lambda f, a=a, b=b: wedge(mono(a, b), f)))
    for b in ys:
        for k in xs:
            ops.append(("v", (b, k), lambda f, b=b, k=k: wedge(mono(b), contract(k, f))))
    for k, l in itertools.combinations(xs, 2):
        ops.append(("pi", (k, l), lambda f, k=k, l=l: contract(k, contract(l, f))))
    return ops


OPS = ht2_ops()


def annihilator(gamma):
    imgs = [op[2](gamma) for op in OPS]
    keys = sorted({K for f in imgs for K in f})
    pos = {K: i for i, K in enumerate(keys)}
    M = flint.fmpq_mat(len(keys) if keys else 1, len(OPS))
    for c, f in enumerate(imgs):
        for K, v in f.items():
            M[pos[K], c] = flint.fmpq(v.numerator, v.denominator)
    r = M.rank()
    # kernel, and its split by summand
    ker = nullspace_q([[Fr(int(M[i, j].p), int(M[i, j].q)) for j in range(len(OPS))] for i in range(M.nrows())],
                      len(OPS))
    kinds = {"z": 0, "v": 0, "pi": 0}
    # dimension of kernel intersected with each summand
    for kind in kinds:
        cols = [c for c, op in enumerate(OPS) if op[0] == kind]
        sub = flint.fmpq_mat(M.nrows(), len(cols))
        for i in range(M.nrows()):
            for jj, c in enumerate(cols):
                sub[i, jj] = M[i, c]
        kinds[kind] = len(cols) - sub.rank()
    return r, len(ker), kinds, ker


def classify_v_kernel(ker):
    """is every kernel vector with only v-components F-linear (blocks sigma -> sigma)?"""
    ok = True
    for v in ker:
        for c, op in enumerate(OPS):
            if v[c] != 0 and op[0] == "v":
                b, k = op[1]
                sb = (b - 8) // 2
                sk = k // 2
                if sb != sk:
                    ok = False
    return ok


def gamma_of(a, cpoly):
    g = {}
    for s in range(SIG):
        g = addf(g, scalf(Fr(a[s]), alpha(s)))
    th = [theta(0), theta(1)]
    for (i, j), c in cpoly.items():
        if c:
            g = addf(g, scalf(Fr(c), wedge(powf(th[0], i), powf(th[1], j))))
    return g


def main():
    rng = random.Random(11)
    print("HT^2 dimension:", len(OPS))
    check("dim HT^2 = 120 (28 + 64 + 28)", len(OPS) == 120)

    # (1) pure Weil class, generic coefficients
    a = [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(SIG)]
    r, k, kinds, ker = annihilator(gamma_of(a, {}))
    check("pure omega: Ann = 0 + 16 + 24 = 40, r = 80", k == 40 and kinds == {"z": 0, "v": 16, "pi": 24},
          "r = %d, dim Ann = %d, by summand %s" % (r, k, kinds))
    check("pure omega: the H^1(T)-part of Ann is exactly the F-linear maps", classify_v_kernel(ker))
    # one coefficient zero (a class that is not rational, for comparison)
    a0 = list(a); a0[3] = Fr(0)
    r0, k0, kinds0, _ = annihilator(gamma_of(a0, {}))
    print("    (omega with one component zero: r = %d, Ann %s -- not a rational class)" % (r0, kinds0))

    # (2) generic corrected character gamma = omega + p(theta_1, theta_2)
    results = []
    for trial in range(3):
        a = [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(SIG)]
        cp = {(i, j): Fr(rng.randint(-9, 9), rng.randint(1, 9)) for i in range(5) for j in range(5)}
        r, k, kinds, ker = annihilator(gamma_of(a, cp))
        results.append((r, k, kinds))
    check("generic gamma = omega + p(theta_1,theta_2): r = 112, Ann = tangent space (dim 8), all in H^1(T)",
          all(x[0] == 112 and x[1] == 8 and x[2] == {"z": 0, "v": 8, "pi": 0} for x in results),
          "\n".join("r = %d, dim Ann = %d, %s" % x for x in results))

    # (3) p a polynomial in the single polarisation theta = theta_1 + theta_2
    res3 = []
    for trial in range(3):
        a = [Fr(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(SIG)]
        cs = [Fr(rng.randint(-9, 9), rng.randint(1, 9)) for _ in range(9)]
        cp = {}
        from math import comb
        for kk in range(9):
            for i in range(0, kk + 1):
                j = kk - i
                if i <= 4 and j <= 4:
                    cp[(i, j)] = cp.get((i, j), Fr(0)) + cs[kk] * comb(kk, i)
        r, k, kinds, ker = annihilator(gamma_of(a, cp))
        res3.append((r, k, kinds))
    print("    p(theta) in the single polarisation theta_1+theta_2, generic coefficients:")
    for x in res3:
        print("      r = %d, dim Ann = %d, %s" % x)
    check("p in C[theta] only (generic): r = 112 as well", all(x[0] == 112 for x in res3))

    # (4) shapes with small rank: p = c e^{t theta_1 + t' theta_2}, and p = c theta^8-type top classes
    def expo(c, t1, t2):
        cp = {}
        fac = [1, 1, 2, 6, 24]
        for i in range(5):
            for j in range(5):
                cp[(i, j)] = Fr(c) * Fr(t1) ** i * Fr(t2) ** j / (fac[i] * fac[j])
        return cp
    a = [Fr(2), Fr(3), Fr(5), Fr(7)]
    for label, cp in [("c e^{t1 th1 + t2 th2}", expo(Fr(3, 2), Fr(1, 3), Fr(-2, 5))),
                      ("c e^{t (th1+th2)}", expo(Fr(3, 2), Fr(1, 3), Fr(1, 3))),
                      ("c th1^4 th2^4 (point class)", {(4, 4): Fr(5)}),
                      ("c (sum) 1 + point", {(0, 0): Fr(2), (4, 4): Fr(5)})]:
        r, k, kinds, ker = annihilator(gamma_of(a, cp))
        print("    shape %-30s: r = %3d, dim Ann = %2d, %s" % (label, r, k, kinds))
    return summary()


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
