#!/usr/bin/env python3
"""
explicit_weil.py

The standard coordinate model of an abelian variety of (K,-1,n)-Weil type,
and the Weil classes written out in coordinates.

Everything is exact.  Scalars live in Q(delta) with delta^2 = -d, represented
as pairs (a,b) of Fractions meaning a + b*delta.  Exterior algebra elements
are dictionaries from frozensets of basis indices to such scalars.

Basis of V = H^1(A,Q):  x_1..x_{2n}, y_1..y_{2n} with y_j = S x_j and
S = iota(sqrt(-d)), so S y_j = -d x_j.  Index j of x_j is j; index of y_j is
j + 2n.

Checks performed, for every (n,d) in the table at the bottom:

  (W1)  u_j^pm are eigenvectors of S with eigenvalues +-delta
  (W2)  the plane spanned by omega_+ and omega_- is defined over Q, with
        rational basis omega_1, omega_2 given by the closed formula
  (W3)  iota(tau)^* omega_pm = tau^{2n} omega_pm resp. bar(tau)^{2n} omega_pm
  (W4)  omega_pm is of Hodge type (n,n) for the balanced complex structure,
        and of type (p, 2n-p) for the unbalanced one with p = dim V_+^{1,0}
  (W5)  eta is rational, of type (1,1), and satisfies
        iota(tau)^* eta = N(tau) eta
  (W6)  the Riemann relations Q(V^{1,0},V^{1,0}) = 0 and i Q(v, bar v) > 0
        hold exactly for the sign vector eps_j = -1 (j <= n), +1 (j > n)
  (W7)  eta^{2n} != 0
  (W8)  omega_1, omega_2, eta^n are linearly independent, and their supports
        are disjoint, so the Weil line meets Q eta^n in zero
"""

from fractions import Fraction as F
from itertools import combinations

# ----------------------------------------------------------------- scalars
# a scalar is a pair (a, b) meaning a + b*delta, with delta^2 = -d.

def sc(a=0, b=0):
    return (F(a), F(b))

def add(p, q):
    return (p[0] + q[0], p[1] + q[1])

def neg(p):
    return (-p[0], -p[1])

def mul(p, q, d):
    # (a+b D)(c+e D) = ac - d b e + (ae + bc) D
    return (p[0] * q[0] - d * p[1] * q[1], p[0] * q[1] + p[1] * q[0])

def conj(p):
    return (p[0], -p[1])

def iszero(p):
    return p[0] == 0 and p[1] == 0

def isrational(p):
    return p[1] == 0

def smul(c, p):
    return (c * p[0], c * p[1])

def powsc(p, k, d):
    r = sc(1, 0)
    for _ in range(k):
        r = mul(r, p, d)
    return r

# ------------------------------------------------------- exterior algebra
# an element is {tuple_of_sorted_indices: scalar}

def wedge(u, v, d):
    out = {}
    for su, cu in u.items():
        setu = set(su)
        for sv, cv in v.items():
            if setu & set(sv):
                continue
            merged = su + sv
            # sign of the sort
            sign = 1
            arr = list(merged)
            for i in range(len(arr)):
                for j in range(i + 1, len(arr)):
                    if arr[i] > arr[j]:
                        sign = -sign
            key = tuple(sorted(arr))
            out[key] = add(out.get(key, sc()), smul(F(sign), mul(cu, cv, d)))
    return {k: v for k, v in out.items() if not iszero(v)}

def escale(u, c):
    return {k: smul(c, v) for k, v in u.items()}

def eadd(u, v):
    out = dict(u)
    for k, c in v.items():
        out[k] = add(out.get(k, sc()), c)
    return {k: v for k, v in out.items() if not iszero(v)}

def emulsc(u, p, d):
    return {k: mul(p, v, d) for k, v in u.items()}

def ewedgepow(u, k, d):
    r = {(): sc(1, 0)}
    for _ in range(k):
        r = wedge(r, u, d)
    return r

# --------------------------------------------------------------- the model

class Model:
    def __init__(self, n, d):
        self.n = n
        self.d = d
        self.m = 2 * n                      # rank of V over K
        self.N = 4 * n                      # dim of V over Q
        # delta / d as a scalar
        self.dd = (F(0), F(1, d))           # delta/d

    def x(self, j):
        return j                            # 1 <= j <= 2n

    def y(self, j):
        return j + self.m

    def Smat(self):
        """S = iota(sqrt(-d)) on the basis x_1..x_m, y_1..y_m."""
        M = {}
        for j in range(1, self.m + 1):
            M[self.x(j)] = {self.y(j): sc(1)}
            M[self.y(j)] = {self.x(j): sc(-self.d)}
        return M

    def eigvec(self, j, s):
        """u_j^s = (1/2)(x_j - s*(delta/d) y_j), s = +1 or -1."""
        c = smul(F(s), self.dd)
        return {(self.x(j),): sc(F(1, 2)),
                (self.y(j),): smul(F(-1, 2), c)}

    def apply_linear(self, M, u):
        """Extend a map on generators to degree-1 elements."""
        out = {}
        for k, c in u.items():
            assert len(k) == 1
            for kk, cc in M[k[0]].items():
                out[(kk,)] = add(out.get((kk,), sc()), mul(c, cc, self.d))
        return {k: v for k, v in out.items() if not iszero(v)}

    def tau_action(self, a, b):
        """iota(a + b sqrt(-d)) on the basis:  x -> a x + b y,
                                               y -> -bd x + a y."""
        M = {}
        for j in range(1, self.m + 1):
            M[self.x(j)] = {self.x(j): sc(a), self.y(j): sc(b)}
            M[self.y(j)] = {self.x(j): sc(-b * self.d), self.y(j): sc(a)}
        return M

    def apply_to_top(self, M, u):
        """Apply a degree-1 map to a decomposable-free element of any degree,
        by multiplicativity.  We only ever use it on our explicit sums."""
        out = {}
        for k, c in u.items():
            piece = {(): sc(1)}
            for idx in k:
                g = {(idx,): sc(1)}
                piece = wedge(piece, self.apply_linear(M, g), self.d)
            piece = emulsc(piece, c, self.d)
            out = eadd(out, piece)
        return out

    def omega(self, s):
        """omega_s = u_1^s ^ ... ^ u_m^s."""
        r = {(): sc(1)}
        for j in range(1, self.m + 1):
            r = wedge(r, self.eigvec(j, s), self.d)
        return r

    def omega1(self):
        """Closed form:  sum over even |T| of (-1)^{|T|/2} d^{n-|T|/2} w^{(T)}."""
        n, m, d = self.n, self.m, self.d
        out = {}
        for k in range(0, m + 1, 2):
            coef = F((-1) ** (k // 2)) * F(d) ** (n - k // 2)
            for T in combinations(range(1, m + 1), k):
                Ts = set(T)
                key = tuple(self.y(j) if j in Ts else self.x(j)
                            for j in range(1, m + 1))
                # key is already increasing?  no: y indices are > x indices.
                arr = list(key)
                sign = 1
                for i in range(len(arr)):
                    for jj in range(i + 1, len(arr)):
                        if arr[i] > arr[jj]:
                            sign = -sign
                out[tuple(sorted(arr))] = sc(F(sign) * coef, 0)
        return out

    def omega2(self):
        """sum over odd |T| of (-1)^{(|T|-1)/2} d^{n-(|T|+1)/2} w^{(T)}."""
        n, m, d = self.n, self.m, self.d
        out = {}
        for k in range(1, m + 1, 2):
            coef = F((-1) ** ((k - 1) // 2)) * F(d) ** (n - (k + 1) // 2)
            for T in combinations(range(1, m + 1), k):
                Ts = set(T)
                arr = [self.y(j) if j in Ts else self.x(j)
                       for j in range(1, m + 1)]
                sign = 1
                for i in range(len(arr)):
                    for jj in range(i + 1, len(arr)):
                        if arr[i] > arr[jj]:
                            sign = -sign
                out[tuple(sorted(arr))] = sc(F(sign) * coef, 0)
        return out

    def eps(self, j):
        return -1 if j <= self.n else 1

    def eta(self):
        """eta = sum_j eps_j x_j ^ y_j."""
        out = {}
        for j in range(1, self.m + 1):
            out[(self.x(j), self.y(j))] = sc(self.eps(j))
        return out

    def hodge_bidegree(self, u, p_plus):
        """Bidegree of a monomial in the eigenbasis, for the complex
        structure with V_+^{1,0} spanned by u_1^+..u_{p}^+ and
        V_-^{1,0} by u_{p+1}^-..u_m^-.  Returns None if not homogeneous."""
        # u is expressed in the eigenbasis: keys are tuples of (j, s)
        degs = set()
        for k in u:
            a = 0
            for (j, s) in k:
                if s == +1:
                    hol = (j <= p_plus)
                else:
                    hol = (j > p_plus)
                a += 1 if hol else 0
            degs.add((a, len(k) - a))
        return degs.pop() if len(degs) == 1 else None


# ------------------------------------------------------------------ checks

def eq(u, v):
    keys = set(u) | set(v)
    for k in keys:
        if not iszero(add(u.get(k, sc()), neg(v.get(k, sc())))):
            return False
    return True


def run(n, d, verbose=False):
    M = Model(n, d)
    m, N = M.m, M.N
    res = []

    # (W1) eigenvectors
    S = M.Smat()
    ok = True
    for j in range(1, m + 1):
        for s in (+1, -1):
            u = M.eigvec(j, s)
            lhs = M.apply_linear(S, u)
            rhs = {k: mul(sc(0, s), c, d) for k, c in u.items()}
            if not eq(lhs, rhs):
                ok = False
    res.append(("W1 eigenvectors of S", ok))

    # omegas
    op = M.omega(+1)
    om = M.omega(-1)

    # (W2) rationality and the closed form
    w1 = eadd(op, om)
    # (omega_+ - omega_-)/delta :  divide by delta = (0,1);  1/delta = -delta/d
    diff = eadd(op, escale(om, F(-1)))
    invdelta = (F(0), F(-1, d))
    w2 = {k: mul(invdelta, c, d) for k, c in diff.items()}
    rat = all(isrational(c) for c in w1.values()) and \
          all(isrational(c) for c in w2.values())
    # compare with the closed form, up to the known positive scalar 2^{1-2n} d^{-n}
    lam = F(2) ** (1 - m) * F(d) ** (-n)
    cf1 = escale(M.omega1(), lam)
    cf2 = escale(M.omega2(), -lam)
    res.append(("W2 rational structure and closed form",
                rat and eq(w1, cf1) and eq(w2, cf2)))

    # (W3) the character
    charok = True
    for (a, b) in [(2, 1), (3, 1), (1, 2), (5, 3), (4, 1)]:
        T = M.tau_action(a, b)
        tau = sc(a, b)
        for s, om_s in ((+1, op), (-1, om)):
            lhs = M.apply_to_top(T, om_s)
            scal = powsc(tau if s == +1 else conj(tau), m, d)
            rhs = {k: mul(scal, c, d) for k, c in om_s.items()}
            if not eq(lhs, rhs):
                charok = False
    res.append(("W3 iota(tau)^* omega_pm = tau^{2n}, conj^{2n}", charok))

    # (W4) Hodge bidegree, in the eigenbasis
    # omega_+ = u_1^+ ^ ... ^ u_m^+ so its eigenbasis monomial is fixed
    keyp = tuple((j, +1) for j in range(1, m + 1))
    keym = tuple((j, -1) for j in range(1, m + 1))
    bal_p = M.hodge_bidegree({keyp: sc(1)}, n)
    bal_m = M.hodge_bidegree({keym: sc(1)}, n)
    unbal = []
    for p in range(0, m + 1):
        unbal.append((p, M.hodge_bidegree({keyp: sc(1)}, p)))
    okbal = (bal_p == (n, n) and bal_m == (n, n))
    okunbal = all(bd == (p, m - p) for p, bd in unbal)
    res.append(("W4 Hodge type (n,n) exactly when balanced", okbal and okunbal))

    # (W5) eta
    eta = M.eta()
    etarat = all(isrational(c) for c in eta.values())
    etachar = True
    for (a, b) in [(2, 1), (3, 1), (1, 2)]:
        T = M.tau_action(a, b)
        lhs = M.apply_to_top(T, eta)
        nm = a * a + d * b * b
        rhs = escale(eta, F(nm))
        if not eq(lhs, rhs):
            etachar = False
    # type (1,1):  x_j ^ y_j = (2d/delta) u_j^+ ^ u_j^-, one holomorphic factor
    etatype = True
    for j in range(1, m + 1):
        bd = M.hodge_bidegree({((j, +1), (j, -1)): sc(1)}, n)
        if bd != (1, 1):
            etatype = False
    res.append(("W5 eta rational, type (1,1), norm eigenclass",
                etarat and etachar and etatype))

    # (W6) the Riemann relations
    # Q(x_j, y_j) = eps_j, zero on other pairs.
    def Q(u, v):
        tot = sc()
        for ku, cu in u.items():
            for kv, cv in v.items():
                i, j = ku[0], kv[0]
                val = 0
                for t in range(1, m + 1):
                    if i == M.x(t) and j == M.y(t):
                        val = M.eps(t)
                    elif i == M.y(t) and j == M.x(t):
                        val = -M.eps(t)
                if val:
                    tot = add(tot, smul(F(val), mul(cu, cv, d)))
        return tot

    basis10 = [M.eigvec(j, +1) for j in range(1, n + 1)] + \
              [M.eigvec(j, -1) for j in range(n + 1, m + 1)]
    r1 = all(iszero(Q(u, v)) for u in basis10 for v in basis10)
    # i Q(v, bar v) > 0 :  bar swaps the eigenvector sign
    basis01 = [M.eigvec(j, -1) for j in range(1, n + 1)] + \
              [M.eigvec(j, +1) for j in range(n + 1, m + 1)]
    r2 = True
    for u, ub in zip(basis10, basis01):
        val = Q(u, ub)               # = a + b delta
        # multiply by i;  delta = i sqrt(d) so  i*(a + b i sqrt d)
        #              = -b sqrt d + i a ;  real and positive iff a = 0, b < 0
        if not (val[0] == 0 and val[1] < 0):
            r2 = False
    res.append(("W6 Riemann relations for eps = (-1^n, +1^n)", r1 and r2))

    # (W7) eta^{2n} != 0
    etatop = ewedgepow(eta, m, d)
    res.append(("W7 eta^{2n} nonzero", len(etatop) > 0))

    # (W8) independence and disjoint supports
    etan = ewedgepow(eta, n, d)
    W1 = M.omega1()
    W2 = M.omega2()
    supp_eta = set(etan)
    supp_w = set(W1) | set(W2)
    disjoint = len(supp_eta & supp_w) == 0
    # each monomial of omega_i contains exactly one of x_j, y_j for every j;
    # each monomial of eta^n contains both or neither.
    shape_w = all(
        all((M.x(j) in set(k)) != (M.y(j) in set(k)) for j in range(1, m + 1))
        for k in supp_w)
    shape_e = all(
        all((M.x(j) in set(k)) == (M.y(j) in set(k)) for j in range(1, m + 1))
        for k in supp_eta)
    res.append(("W8 Weil line and eta^n have disjoint supports",
                disjoint and shape_w and shape_e and len(supp_eta) > 0))

    if verbose:
        print("    omega_1 has %d terms, omega_2 has %d terms, eta^n has %d"
              % (len(W1), len(W2), len(etan)))
    return res


def show_n2_d1():
    """Print omega_1 and omega_2 in full for n=2, d=1."""
    M = Model(2, 1)
    names = {}
    for j in range(1, 5):
        names[M.x(j)] = "x%d" % j
        names[M.y(j)] = "y%d" % j

    def pr(u):
        items = []
        for k in sorted(u, key=lambda t: (sum(1 for i in t if i > 4), t)):
            c = u[k]
            s = "".join(names[i] for i in k)
            a = c[0]
            items.append(("+ " if a > 0 else "- ") +
                         (("%s " % abs(a)) if abs(a) != 1 else "") + s)
        return " ".join(items)

    print("  n=2, d=1")
    print("    omega_1 = " + pr(M.omega1()))
    print("    omega_2 = " + pr(M.omega2()))
    M3 = Model(2, 3)
    names = {}
    for j in range(1, 5):
        names[M3.x(j)] = "x%d" % j
        names[M3.y(j)] = "y%d" % j
    print("  n=2, d=3")
    print("    omega_1 = " + pr(M3.omega1()))
    print("    omega_2 = " + pr(M3.omega2()))


if __name__ == "__main__":
    print("explicit coordinate model of Weil type")
    npass = nfail = 0
    for (n, d) in [(1, 1), (2, 1), (2, 2), (2, 3), (2, 7), (3, 1), (3, 2),
                   (3, 5)]:
        print("  n=%d, d=%d" % (n, d))
        for name, ok in run(n, d):
            tag = "PASS" if ok else "FAIL"
            if ok:
                npass += 1
            else:
                nfail += 1
            print("    [%s] %s" % (tag, name))
    print()
    show_n2_d1()
    print()
    print("  %d checks passed, %d failed" % (npass, nfail))
    print("  overall: %s" % ("PASS" if nfail == 0 else "FAIL"))
