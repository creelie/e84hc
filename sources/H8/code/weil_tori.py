#!/usr/bin/env python3
"""
weil_tori.py

Item (LI) of COMPUTATIONS.md: the Hodge classes of a very general
K-linear complex torus of Weil type, the input of the theorem that no perfect
complex whose Chern character is exactly a Weil class is semiregular.

Let V = H^1(A,Q) with the action of K = Q(sqrt(-d)) of the coordinate model of
explicit_weil.py, V (x) C = V_+ + V_- its eigenspaces.  A complex structure
commuting with K and of signature (n,n) is V^{1,0} = X + conj(Y) with X, Y
complementary n-dimensional subspaces of V_+; these form a connected family of
complex dimension 2n^2, the polarised Weil family being the sublocus of
dimension n^2 on which the polarisation is of type (1,1).  A rational class
that is of Hodge type at a very general member of the family is of Hodge type
at every member, so an upper bound for the Hodge classes of a very general
member is given by the classes that are Hodge at a few explicit members.

What is checked, for n = 2 and n = 3, at members X + conj(Y) with X, Y
spanned by explicit K-rational combinations of the eigenvectors:

  (A) the rational Weil classes omega_1, omega_2 are of type (n,n) at every
      member used, as they must be on the whole family;

  (B) the polarisation eta of the balanced member is of type (1,1) there and
      not at the members used, which therefore lie off the polarised family;

  (C) the rational classes of degree 2k that are of type (k,k) at all the
      members used: none for k = 1, and for n = 3 none for k = 2; exactly the
      Weil plane for k = n.  Hence a very general member has no Hodge classes
      in degree 2, none in degree 4 when n = 3, and exactly the Weil plane in
      degree 2n.  A class of degree 2k is of type (k,k) exactly when its
      wedge product with every product of 2n-k+1 vectors of V^{1,0} vanishes;
      the rank computations are made modulo a prime q < 2^31 in which -d is
      a square, delta being sent to both square roots of -d so that the
      conjugate conditions are imposed too, and reduction can only lower a
      rank, so the dimensions found are upper bounds, attained by the Weil
      classes (degrees above 2n are covered by the proof of the lemma and
      are not checked);

  (D) for a random element kappa of V_+ (x) V_-, the products
      alpha_+ ^ kappa^n and alpha_- ^ kappa^n vanish, so every Weil class has
      zero degree against a Kaehler class whose hermitian form is block
      diagonal for V^{1,0} = X + conj(Y), while an element with a component
      beta in wedge^2 V_- with beta^n != 0 does not have this property.

Needs numpy, for the dense elimination modulo q; every entry is an integer
residue and no step uses floating point.

Run:  python3 weil_tori.py
"""
import random
from fractions import Fraction as F
from itertools import combinations

import numpy as np

import explicit_weil as EW

PASS, FAIL = [], []
PRIME = 2 ** 31 - 1


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


def lin(M, coeffs, vecs):
    """sum of scalar * degree-one element"""
    out = {}
    for c, v in zip(coeffs, vecs):
        out = EW.eadd(out, EW.emulsc(v, c, M.d))
    return out


def conj_elem(u):
    return {k: EW.conj(c) for k, c in u.items()}


def member(M, rng):
    """V^{1,0} = X + conj(Y) with X, Y spanned by K-combinations of u^+"""
    m = M.m
    up = [M.eigvec(j, +1) for j in range(1, m + 1)]
    while True:
        rows = [[EW.sc(rng.randint(-3, 3), rng.randint(-3, 3))
                 for _ in range(m)] for _ in range(m)]
        X = [lin(M, r, up) for r in rows[:M.n]]
        Y = [lin(M, r, up) for r in rows[M.n:]]
        # transversality: the m vectors span V_+ (top wedge nonzero)
        top = {(): EW.sc(1)}
        for v in X + Y:
            top = EW.wedge(top, v, M.d)
        if top:
            return X + [conj_elem(y) for y in Y]


def balanced(M):
    """the balanced member of the coordinate model"""
    n, m = M.n, M.m
    return ([M.eigvec(j, +1) for j in range(1, n + 1)]
            + [M.eigvec(j, -1) for j in range(n + 1, m + 1)])


def wedge_list(M, vecs):
    out = {(): EW.sc(1)}
    for v in vecs:
        out = EW.wedge(out, v, M.d)
    return out


def is_type_kk(M, cls, k, hol):
    """cls of degree 2k is of type (k,k) iff cls ^ e_I = 0 for |I| = 2n-k+1"""
    for I in combinations(range(len(hol)), 2 * M.n - k + 1):
        if EW.wedge(cls, wedge_list(M, [hol[i] for i in I]), M.d):
            return False
    return True


def rank_mod_p(rows, ncols):
    """rank of sparse rows {column: residue} modulo PRIME, by Gaussian
    elimination on a dense integer array; PRIME < 2^31, so every product of
    two residues fits in a signed 64-bit integer"""
    A = np.zeros((len(rows), ncols), dtype=np.int64)
    for i, row in enumerate(rows):
        for j, x in row.items():
            A[i, j] = x % PRIME
    r = 0
    for c in range(ncols):
        if r == A.shape[0]:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        p = r + int(nz[0])
        if p != r:
            A[[r, p]] = A[[p, r]]
        inv = pow(int(A[r, c]), PRIME - 2, PRIME)
        A[r, c:] = A[r, c:] * inv % PRIME
        below = r + 1 + np.nonzero(A[r + 1:, c])[0]
        if len(below):
            A[below, c:] = (A[below, c:]
                            - np.outer(A[below, c], A[r, c:]) % PRIME) % PRIME
        r += 1
    return r


def fr_mod(x):
    return x.numerator % PRIME * pow(x.denominator % PRIME, PRIME - 2,
                                     PRIME) % PRIME


def is_prime(q):
    """deterministic Miller-Rabin for q < 3.3 * 10^24"""
    if q < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    for b in small:
        if q % b == 0:
            return q == b
    dd, r = q - 1, 0
    while dd % 2 == 0:
        dd //= 2
        r += 1
    for b in small:
        x = pow(b, dd, q)
        if x in (1, q - 1):
            continue
        for _ in range(r - 1):
            x = x * x % q
            if x == q - 1:
                break
        else:
            return False
    return True


def choose_prime(d):
    """the largest prime q < 2^31 in which -d is a square"""
    global PRIME
    q = 2 ** 31 - 1
    while not (is_prime(q) and pow((-d) % q, (q - 1) // 2, q) == 1):
        q -= 2
    PRIME = q
    return q


def sqrt_mod(a):
    """a square root of a modulo PRIME, by Tonelli-Shanks"""
    q = PRIME
    a %= q
    if a == 0:
        return 0
    if pow(a, (q - 1) // 2, q) != 1:
        return None
    Q, S = q - 1, 0
    while Q % 2 == 0:
        Q //= 2
        S += 1
    z = 2
    while pow(z, (q - 1) // 2, q) != q - 1:
        z += 1
    M, c, t, R = S, pow(z, Q, q), pow(a, Q, q), pow(a, (Q + 1) // 2, q)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % q
            i += 1
        b = pow(c, 1 << (M - i - 1), q)
        M, c, t, R = i, b * b % q, t * b * b % q, R * b % q
    return R


def to_fp(M, u, s):
    """a degree-one element over Q(delta) as a vector mod PRIME, delta -> s,
    on the bits 0..N-1 of the basis x_1..x_m, y_1..y_m"""
    out = {}
    for key, c in u.items():
        (i,) = key
        val = (fr_mod(c[0]) + fr_mod(c[1]) * s) % PRIME
        if val:
            out[1 << (i - 1)] = (out.get(1 << (i - 1), 0) + val) % PRIME
    return out


def popc(x):
    return bin(x).count("1")


def fp_wedge(u, v):
    out = {}
    for a, ca in u.items():
        for b, cb in v.items():
            if a & b:
                continue
            # sign of merging: count pairs (i in a, j in b) with i > j
            sgn = 0
            bb = b
            while bb:
                low = bb & -bb
                sgn += popc(a & ~((low << 1) - 1))
                bb ^= low
            val = ca * cb % PRIME
            if sgn & 1:
                val = PRIME - val
            key = a | b
            out[key] = (out.get(key, 0) + val) % PRIME
    return {k: x for k, x in out.items() if x}


def hodge_dimension(M, k, members):
    """dimension (an upper bound, from ranks modulo a prime) of the rational
    classes of degree 2k that are of type (k,k) at every member listed"""
    choose_prime(M.d)
    s = sqrt_mod(-M.d)
    assert s is not None
    N = M.N
    col = {}
    for mu in combinations(range(N), 2 * k):
        col[sum(1 << i for i in mu)] = len(col)
    rows = {}
    # a rational class is killed by e_I exactly when it is killed by its
    # conjugate as well; over F_q both conditions must be imposed, delta being
    # sent to s and to -s, so that the solutions are the reductions of the
    # rational solutions (the system is stable under conjugation)
    vecsets = []
    for hol in members:
        vecsets.append([to_fp(M, v, s) for v in hol])
        vecsets.append([to_fp(M, v, PRIME - s) for v in hol])
    for mi, hv in enumerate(vecsets):
        for I in combinations(range(len(hv)), 2 * M.n - k + 1):
            eI = {0: 1}
            for i in I:
                eI = fp_wedge(eI, hv[i])
            for tau, ct in eI.items():
                comp = [i for i in range(N) if not (tau >> i) & 1]
                tbits = [j for j in range(N) if (tau >> j) & 1]
                for mu_t in combinations(comp, 2 * k):
                    mu = 0
                    for i in mu_t:
                        mu |= 1 << i
                    sgn = 0
                    for j in tbits:
                        sgn += popc(mu >> (j + 1))
                    val = ct if not (sgn & 1) else PRIME - ct
                    r = rows.setdefault((mi, I, mu | tau), {})
                    c = col[mu]
                    r[c] = (r.get(c, 0) + val) % PRIME
    return len(col) - rank_mod_p(list(rows.values()), len(col))


def main():
    rng = random.Random(20260925)
    for n, d, count in ((2, 1, 3), (2, 3, 3), (3, 2, 5)):
        M = EW.Model(n, d)
        members = [member(M, rng) for _ in range(count)]
        w1, w2 = M.omega1(), M.omega2()

        # (A)
        okA = all(is_type_kk(M, w, n, hol) for w in (w1, w2)
                  for hol in members)
        check("n=%d, d=%d: omega_1 and omega_2 are of type (%d,%d) at %d "
              "members of the K-linear family" % (n, d, n, n, count), okA)

        # (C)
        eta = M.eta()
        bal = balanced(M)
        okC = is_type_kk(M, eta, 1, bal) and \
            not any(is_type_kk(M, eta, 1, hol) for hol in members)
        check("n=%d, d=%d: eta is of type (1,1) at the balanced member and at "
              "none of the members used, which lie off the polarised family"
              % (n, d), okC)

        # (B)
        dims = {}
        for k in range(1, n + 1):
            dims[k] = hodge_dimension(M, k, members)
        want = {k: (2 if k == n else 0) for k in range(1, n + 1)}
        check("n=%d, d=%d: rational classes of type (k,k) at all members "
              "used, k = 1..%d: dimensions %s, the Weil plane in degree 2n "
              "and nothing else" % (n, d, n, [dims[k] for k in sorted(dims)]),
              dims == want)

        # (D)
        vp = [M.eigvec(j, +1) for j in range(1, M.m + 1)]
        vm = [M.eigvec(j, -1) for j in range(1, M.m + 1)]
        kappa = {}
        for a in vp:
            for b in vm:
                c = EW.sc(rng.randint(-4, 4), rng.randint(-4, 4))
                kappa = EW.eadd(kappa, EW.emulsc(EW.wedge(a, b, d), c, d))
        kn = EW.ewedgepow(kappa, n, d)
        ap, am = M.omega(+1), M.omega(-1)
        mixed_zero = not EW.wedge(ap, kn, d) and not EW.wedge(am, kn, d)
        beta = {}
        for j in range(n):
            beta = EW.eadd(beta, EW.wedge(vm[2 * j], vm[2 * j + 1], d))
        kappa2 = EW.eadd(kappa, beta)
        kn2 = EW.ewedgepow(kappa2, n, d)
        other_nonzero = bool(EW.wedge(ap, kn2, d))
        check("n=%d, d=%d: alpha_+ ^ kappa^n = alpha_- ^ kappa^n = 0 for "
              "kappa in V_+ (x) V_-, and not once kappa has a wedge^2 V_- "
              "component" % (n, d), mixed_zero and other_nonzero)


if __name__ == "__main__":
    print("(LI) the Hodge classes of a very general Weil torus")
    main()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
