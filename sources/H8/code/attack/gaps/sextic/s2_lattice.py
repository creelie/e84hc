#!/usr/bin/env python3
"""
s2_lattice.py

The integral classes of the flat secant space S(0,q) of a sextic CM field
F = F_0(sqrt(-q)), and which of them the count of prop:sexticcount excludes.

Model.  F_0 is a totally real cubic field with ring of integers O = Z[a]
(true for the three fields used), real places tau_1, tau_2, tau_3, and
different d.  M = O e_1 + O e_2 + d^{-1} f_1 + d^{-1} f_2 with the O-bilinear
alternating form psi(e_a, f_b) = delta_ab; Tr psi is a principal polarisation
and O acts by real multiplication.  Integrality is local, and locally every
principally polarised lattice with real multiplication by O has this shape
(the argument of lem:quarticlattice), so the answer does not depend on the
model.  H^1(X, Z) = M^dual, with the Z-basis dual to nu_i e_a, nu*_k f_b
(nu the power basis of O, nu* its trace dual), and
    theta_j = sum_a sum_{i,k} tau_j(nu_i nu*_k) u_{ai} ^ w_{ak}.

The rational points of S(0,q) are the classes
    v(c_0, f, g, c_3) = c_0 B0_1 B0_2 B0_3
                      + sum_j tau_j(f) theta_j prod_{k != j} B0_k
                      + sum_j tau_j(g) B0_j prod_{k != j} theta_k
                      + c_3 theta_1 theta_2 theta_3,
    B0_j = 1 - tau_j(q) theta_j^2 / 2,
with c_0, c_3 in Q and f, g in F_0, because e^{+-s_j theta_j} =
B0_j +- s_j theta_j.  Their Euler form is
    chi(v, v) = -8 ( Nm(q) c_0^2 + Tr(Nm(q) f^2 / q) + Tr(q g^2) + c_3^2 ).

What is computed, exactly:
  (A) the 2048 x 8 matrix of coefficients of v in the monomial basis of
      wedge^even H^1(X, Z), by computing modulo three primes that split
      completely in F_0 and rational reconstruction, verified modulo a
      fourth prime and by the identity sum_j theta_j = standard form;
  (B) the lattice L of parameters (c_0, f, g, c_3) for which v is integral,
      as the dual of the Z-span of the rows;
  (C) the Gram matrix of chi on L, checked against the closed formula
      above and against the direct integral of v^dual v on random points;
  (D) every class of L with -chi <= 24, with its secant invariants
      N_w, A_{jj'}, rho_j, rk M^{(j;j')}_{+-} computed in exact arithmetic
      in the splitting field modulo a prime, and whether the profile
      condition chi <= -(r^3 - 2 r^2 + 22) of prop:sexticcount(iii) holds.

Run:  python3 s2_lattice.py
"""
from fractions import Fraction as Fr
from itertools import product, combinations
import random, sys

# ---------------------------------------------------------------- primes
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n-1, 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def roots_mod(poly, p):
    """roots of a monic integer polynomial (coeffs high to low) mod p, brute
    force is too slow for large p; use Cantor-Zassenhaus-free approach:
    gcd with x^p - x then equal-degree splitting."""
    # represent polys as lists low->high
    P = [c % p for c in reversed(poly)]
    def trim(a):
        while a and a[-1] == 0: a.pop()
        return a
    def mul(a, b):
        r = [0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b): r[i+j] = (r[i+j]+x*y) % p
        return trim(r)
    def divmod_(a, b):
        a = a[:]; q = [0]*max(1, len(a)-len(b)+1)
        inv = pow(b[-1], p-2, p)
        while len(trim(a)) >= len(b):
            c = a[-1]*inv % p; d = len(a)-len(b); q[d] = c
            for i,y in enumerate(b): a[i+d] = (a[i+d]-c*y) % p
            trim(a)
        return trim(q), a
    def pmod(a, m): return divmod_(a, m)[1]
    def powmod(base, e, m):
        r = [1]; b = pmod(base, m)
        while e:
            if e & 1: r = pmod(mul(r, b), m)
            b = pmod(mul(b, b), m); e >>= 1
        return r
    def gcd(a, b):
        a, b = trim(a[:]), trim(b[:])
        while b: a, b = b, pmod(a, b)
        inv = pow(a[-1], p-2, p); return [x*inv % p for x in a]
    xp = powmod([0,1], p, P)
    g = gcd(P, trim([(xp[i] if i < len(xp) else 0) - (1 if i == 1 else 0)
                     for i in range(max(len(xp), 2))]))
    roots = []
    def split(h):
        if len(h) == 2: roots.append((-h[0]) * pow(h[1], p-2, p) % p); return
        while True:
            a = random.randrange(p)
            t = powmod([a,1], (p-1)//2, h)
            t = trim([(t[i] if i < len(t) else 0) - (1 if i == 0 else 0)
                      for i in range(max(len(t),1))])
            d = gcd(h, t) if t else h
            if 1 < len(d) < len(h):
                split(d); split(divmod_(h, d)[0]); return
    if len(g) > 1: split(g)
    return sorted(roots)

# ---------------------------------------------------------------- fields
FIELDS = {
    "Q(zeta7)+ (disc 49)":  [1, 1, -2, -1],
    "Q(zeta9)+ (disc 81)":  [1, 0, -3, 1],
    "disc 229 (non-Galois)": [1, 0, -4, 1],
}

def field_data(poly):
    """power basis 1, a, a^2 of O = Z[a]; multiplication table; trace form."""
    _, c2, c1, c0 = poly          # a^3 = -c2 a^2 - c1 a - c0
    def mulv(x, y):
        r = [Fr(0)]*5
        for i in range(3):
            for j in range(3): r[i+j] += x[i]*y[j]
        for k in (4, 3):
            c = r[k]; r[k] = Fr(0)
            r[k-1] += -c2*c; r[k-2] += -c1*c; r[k-3] += -c0*c
        return r[:3]
    basis = [[Fr(1),Fr(0),Fr(0)],[Fr(0),Fr(1),Fr(0)],[Fr(0),Fr(0),Fr(1)]]
    # trace of a^k via Newton: p1 = -c2, p2 = c2^2 - 2 c1, p3 ...
    e1, e2, e3 = -c2, c1, -c0
    pw = [3, e1, e1*e1-2*e2, e1**3-3*e1*e2+3*e3, None]
    pw[4] = e1*pw[3]-e2*pw[2]+e3*pw[1]
    def tr(x): return x[0]*3 + x[1]*pw[1] + x[2]*pw[2]
    T = [[tr(mulv(basis[i], basis[k])) for k in range(3)] for i in range(3)]
    return mulv, tr, T, basis

def inv3(A):
    A = [row[:] for row in A]; n = 3
    I = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]; I[c], I[piv] = I[piv], I[c]
        iv = 1/A[c][c]
        A[c] = [x*iv for x in A[c]]; I[c] = [x*iv for x in I[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x-f*y for x,y in zip(A[r],A[c])]
                I[r] = [x-f*y for x,y in zip(I[r],I[c])]
    return I

# ------------------------------------------------ exterior algebra mod p
# generators: u_{a i} index 6*(a) + i ... we use 12 generators:
# index(a, i) = 6a + i for u (i=0..2), 6a + 3 + k for w (k=0..2), a=0,1
def ext_mul(A, B, p):
    R = {}
    for ma, ca in A.items():
        for mb, cb in B.items():
            if ma & mb: continue
            # sign: number of pairs (x in ma, y in mb) with x > y
            s = 0; m = mb
            while m:
                low = m & -m; y = low.bit_length()-1
                s += bin(ma >> (y+1)).count("1"); m ^= low
            c = ca*cb % p
            if s & 1: c = -c % p
            R[ma|mb] = (R.get(ma|mb, 0) + c) % p
    return {k: v for k, v in R.items() if v}

def ext_add(*terms_p):
    *terms, p = terms_p
    R = {}
    for coef, A in terms:
        for m, c in A.items(): R[m] = (R.get(m, 0) + coef*c) % p
    return {k: v for k, v in R.items() if v}

def classes_mod_p(poly, qvec, p):
    """the eight parameter classes of S(0,q) mod p, and theta_j, for each of
    the three identifications of tau_1, tau_2, tau_3 with roots mod p."""
    rts = roots_mod(poly, p)
    if len(rts) != 3: return None
    mulv, tr, T, basis = field_data(poly)
    Ti = inv3(T)
    # nu*_k = sum_i Ti[k][i] nu_i ; products nu_i nu*_k as vectors in power basis
    prodv = {}
    for i in range(3):
        for k in range(3):
            v = [Fr(0)]*3
            for l in range(3):
                pl = mulv(basis[i], basis[l])
                v = [x + Ti[k][l]*y for x, y in zip(v, pl)]
            prodv[i, k] = v
    def ev(vec, r):     # evaluate element in power basis at root r mod p
        s = 0
        for e, c in enumerate(vec):
            s = (s + (c.numerator * pow(c.denominator, p-2, p)) % p * pow(r, e, p)) % p
        return s
    theta = []
    for r in rts:
        th = {}
        for a in range(2):
            for i in range(3):
                for k in range(3):
                    c = ev(prodv[i, k], r)
                    if c:
                        m = (1 << (6*a+i)) | (1 << (6*a+3+k))
                        # u_{ai} ^ w_{ak}, u index < w index so sign +
                        th[m] = (th.get(m, 0) + c) % p
        theta.append(th)
    one = {0: 1}
    inv2 = pow(2, p-2, p)
    qj = [ev(qvec, r) for r in rts]
    B0 = [ext_add((1, one), ((-qj[j]*inv2) % p, ext_mul(theta[j], theta[j], p)), p)
          for j in range(3)]
    def prod3(xs):
        R = xs[0]
        for x in xs[1:]: R = ext_mul(R, x, p)
        return R
    params = []
    # c_0
    params.append(prod3(B0))
    # f = nu_l, l = 0..2 : sum_j tau_j(nu_l) theta_j prod_{k != j} B0_k
    for l in range(3):
        terms = []
        for j in range(3):
            xs = [theta[j] if k == j else B0[k] for k in range(3)]
            terms.append((pow(rts[j], l, p), prod3(xs)))
        params.append(ext_add(*terms, p))
    for l in range(3):
        terms = []
        for j in range(3):
            xs = [B0[j] if k == j else theta[k] for k in range(3)]
            terms.append((pow(rts[j], l, p), prod3(xs)))
        params.append(ext_add(*terms, p))
    params.append(prod3(theta))
    return params, theta, rts

def ratrec(a, m):
    """rational reconstruction of a mod m"""
    a %= m
    r0, r1, s0, s1 = m, a, 0, 1
    bound = int((m//2) ** 0.5)
    while r1 > bound:
        qq = r0 // r1
        r0, r1 = r1, r0 - qq*r1
        s0, s1 = s1, s0 - qq*s1
    if s1 == 0 or abs(s1) > bound: return None
    return Fr(r1, s1) if s1 > 0 else Fr(-r1, -s1)

def big_primes(poly, count, start):
    out = []; n = start
    while len(out) < count:
        n += 1
        if is_prime(n) and len(roots_mod(poly, n)) == 3: out.append(n)
    return out

def coefficient_matrix(poly, qvec):
    ps = big_primes(poly, 4, 2**40)
    per_p = []
    for p in ps:
        params, theta, rts = classes_mod_p(poly, qvec, p)
        per_p.append((p, params))
    # the classes are Galois-symmetric, so independent of the ordering of roots
    monos = sorted(set().union(*[set(P.keys()) for P in per_p[0][1]]) |
                   set().union(*[set(P.keys()) for P in per_p[1][1]]))
    M = 1
    for p, _ in per_p[:3]: M *= p
    A = []
    for m in monos:
        row = []
        for col in range(8):
            # CRT over first three primes
            x, mod = 0, 1
            for p, params in per_p[:3]:
                c = params[col].get(m, 0)
                # combine
                t = ((c - x) * pow(mod, p-2, p)) % p
                x += mod*t; mod *= p
            r = ratrec(x, mod)
            assert r is not None
            p4, params4 = per_p[3]
            assert (r.numerator - params4[col].get(m, 0)*r.denominator) % p4 == 0
            row.append(r)
        A.append(row)
    return monos, A

# ------------------------------------------------ lattices
def hnf_rows(rows):
    """Z-basis (echelon) of the lattice spanned by integer rows."""
    basis = []
    ncol = len(rows[0])
    piv_rows = {}
    for r in rows:
        r = r[:]
        for c in range(ncol):
            if r[c] == 0: continue
            if c not in piv_rows:
                if r[c] < 0: r = [-x for x in r]
                piv_rows[c] = r; break
            b = piv_rows[c]
            # extended gcd combine
            a0, b0 = r[c], b[c]
            g, x, y = egcd(b0, a0)
            newb = [x*bb + y*rr for bb, rr in zip(b, r)]
            newr = [(a0//g)*bb - (b0//g)*rr for bb, rr in zip(b, r)]
            if newb[c] < 0: newb = [-t for t in newb]
            piv_rows[c] = newb; r = newr
            assert r[c] == 0
        # reduce size
    B = [piv_rows[c] for c in sorted(piv_rows)]
    return B

def egcd(a, b):
    if b == 0: return (abs(a), (1 if a >= 0 else -1), 0)
    x0, x1, y0, y1 = 1, 0, 0, 1
    while b:
        q = a // b
        a, b = b, a - q*b
        x0, x1 = x1, x0 - q*x1
        y0, y1 = y1, y0 - q*y1
    if a < 0: a, x0, y0 = -a, -x0, -y0
    return a, x0, y0

def matinv(A):
    n = len(A)
    A = [[Fr(x) for x in row] for row in A]
    I = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]; I[c], I[piv] = I[piv], I[c]
        iv = 1/A[c][c]
        A[c] = [x*iv for x in A[c]]; I[c] = [x*iv for x in I[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x-f*y for x,y in zip(A[r],A[c])]
                I[r] = [x-f*y for x,y in zip(I[r],I[c])]
    return I

def lcm(a, b):
    from math import gcd
    return a*b // gcd(a, b)

def integral_lattice(A):
    """L = {x in Q^8 : A x in Z^N}: dual of the Z-span of the rows of A."""
    den = 1
    for row in A:
        for x in row: den = lcm(den, x.denominator)
    rows = [[int(x*den) for x in row] for row in A if any(row)]
    R = hnf_rows(rows)            # basis of den * (row lattice)
    assert len(R) == 8
    Rq = [[Fr(x, den) for x in r] for r in R]
    # L basis = columns of Rq^{-1}
    Ri = matinv(Rq)
    Lb = [[Ri[i][j] for i in range(8)] for j in range(8)]
    return Lb

# ------------------------------------------------ Euler form, closed formula
def chi_formula(poly, qvec, x):
    """x = (c0, f0, f1, f2, g0, g1, g2, c3), f = sum f_l a^l"""
    mulv, tr, T, basis = field_data(poly)
    f = [Fr(t) for t in x[1:4]]; g = [Fr(t) for t in x[4:7]]
    c0, c3 = Fr(x[0]), Fr(x[7])
    q = [Fr(t) for t in qvec]
    # Nm(q) = product of conjugates: compute via determinant of mult-by-q
    Mq = [mulv(q, b) for b in basis]
    detq = (Mq[0][0]*(Mq[1][1]*Mq[2][2]-Mq[1][2]*Mq[2][1])
            - Mq[0][1]*(Mq[1][0]*Mq[2][2]-Mq[1][2]*Mq[2][0])
            + Mq[0][2]*(Mq[1][0]*Mq[2][1]-Mq[1][1]*Mq[2][0]))
    # Nm(q)/q = q' q'' = adjugate element: q^2 - Tr(q) q + e2(q)
    trq = tr(q)
    q2 = mulv(q, q)
    e2 = (trq*trq - tr(q2)) / 2
    adjq = [q2[i] - trq*q[i] + (e2 if i == 0 else 0) for i in range(3)]
    val = (detq*c0*c0 + tr(mulv(adjq, mulv(f, f))) + tr(mulv(q, mulv(g, g)))
           + c3*c3)
    return -8*val

# ------------------------------------------------ direct integral (mod p)
def ext_dual(A):
    return {m: (c if (bin(m).count("1") % 4 == 0) else -c) for m, c in A.items()}

def check_chi_direct(poly, qvec, Lb, trials=4):
    p = big_primes(poly, 1, 2**45)[0]
    params, theta, rts = classes_mod_p(poly, qvec, p)
    top = (1 << 12) - 1
    # orientation: normalise so that the integral of theta^6 / 6! is 1
    th = ext_add(*[(1, t) for t in theta], p)
    t6 = {0: 1}
    for _ in range(6): t6 = ext_mul(t6, th, p)
    vol = t6.get(top, 0) * pow(720, p-2, p) % p
    ivol = pow(vol, p-2, p)
    for _ in range(trials):
        x = [random.randint(-3, 3) for _ in range(8)]
        coeffs = [sum(Fr(x[b])*Lb[b][i] for b in range(8)) for i in range(8)]
        v = ext_add(*[((c.numerator*pow(c.denominator, p-2, p)) % p, params[i])
                      for i, c in enumerate(coeffs)], p)
        val = ext_mul(ext_dual(v), v, p).get(top, 0) * ivol % p
        ref = chi_formula(poly, qvec, coeffs)
        assert (ref.numerator - val*ref.denominator) % p == 0, (ref, val)
    return True

# ------------------------------------------------ shapes, exactly mod p
def shape_invariants(poly, qvec, coeffs, p):
    """w_eps from C_a, over F_p with s_j = sqrt(-tau_j(q)) in F_p; returns
    N_w, sum A, sum rho, and the sum of ranks of the M slices."""
    rts = roots_mod(poly, p)
    mulv, tr, T, basis = field_data(poly)
    def ev(vec, r):
        s = 0
        for e, c in enumerate(vec):
            c = Fr(c)
            s = (s + (c.numerator*pow(c.denominator, p-2, p)) % p*pow(r, e, p)) % p
        return s
    s = []
    for r in rts:
        mq = (-ev(qvec, r)) % p
        sq = sqrt_mod(mq, p)
        if sq is None: return None
        s.append(sq)
    c0 = ev([coeffs[0]], 0); c3 = ev([coeffs[7]], 0)
    fj = [ev(coeffs[1:4], r) for r in rts]
    gj = [ev(coeffs[4:7], r) for r in rts]
    C = {}
    for a in product((0, 1), repeat=3):
        k = sum(a)
        if k == 0: C[a] = c0
        elif k == 3: C[a] = c3
        elif k == 1: C[a] = fj[a.index(1)]
        else: C[a] = gj[a.index(0)]
    inv8 = pow(8, p-2, p)
    w = {}
    for eps in product((1, -1), repeat=3):
        tot = 0
        for a in product((0, 1), repeat=3):
            term = C[a]
            for j in range(3):
                if a[j]: term = term * (eps[j] % p) * pow(s[j], p-2, p) % p
            tot += term
        w[eps] = tot*inv8 % p
    Nw = sum(1 for e in w if w[e])
    A = 0
    for j, jj in combinations(range(3), 2):
        A += sum(1 for sg in product((1, -1), repeat=2)
                 if any(w[e] for e in w if e[j] == sg[0] and e[jj] == sg[1]))
    def rank(Mx):
        Mx = [r[:] for r in Mx]; rk = 0; cols = len(Mx[0])
        for c in range(cols):
            piv = next((r for r in range(rk, len(Mx)) if Mx[r][c] % p), None)
            if piv is None: continue
            Mx[rk], Mx[piv] = Mx[piv], Mx[rk]
            iv = pow(Mx[rk][c], p-2, p)
            for r in range(len(Mx)):
                if r != rk and Mx[r][c] % p:
                    f = Mx[r][c]*iv % p
                    Mx[r] = [(x - f*y) % p for x, y in zip(Mx[r], Mx[rk])]
            rk += 1
        return rk
    rho = 0
    for j in range(3):
        others = [k for k in range(3) if k != j]
        Mx = [[w[tuple(sg if k == j else (o1 if k == others[0] else o2)
                        for k in range(3))]
               for o1 in (1, -1) for o2 in (1, -1)] for sg in (1, -1)]
        rho += rank(Mx)
    Msum = 0
    for j in range(3):
        for jp in range(3):
            if jp == j: continue
            jpp = 3 - j - jp
            for sgp in (1, -1):
                Mx = []
                for a in (1, -1):
                    row = []
                    for b in (1, -1):
                        e = [0]*3; e[j] = a; e[jpp] = b; e[jp] = sgp
                        row.append(w[tuple(e)])
                    Mx.append(row)
                Msum += rank(Mx)
    r2 = 4*A + rho
    r3 = 8*Nw + 2*Msum
    return Nw, A, rho, Msum, r2, r3

def sqrt_mod(a, p):
    a %= p
    if a == 0: return 0
    if pow(a, (p-1)//2, p) != 1: return None
    if p % 4 == 3: return pow(a, (p+1)//4, p)
    # Tonelli-Shanks
    q, s = p-1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p-1)//2, p) != p-1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q+1)//2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1: tt = tt*tt % p; i += 1
        b = pow(c, 1 << (m-i-1), p)
        m, c, t, r = i, b*b % p, t*b*b % p, r*b % p
    return r

def shape_prime(poly, qvec, start):
    n = start
    while True:
        n += 1
        if not is_prime(n): continue
        rts = roots_mod(poly, n)
        if len(rts) != 3: continue
        mulv, tr, T, basis = field_data(poly)
        ok = True
        for r in rts:
            qq = sum(Fr(c)*r**e for e, c in enumerate(qvec))
            val = (-(qq.numerator*pow(qq.denominator, n-2, n))) % n
            if val == 0 or pow(val, (n-1)//2, n) != 1: ok = False
        if ok: return n

# ------------------------------------------------ short vectors
def short_vectors(G, bound):
    """all nonzero x in Z^8 with x^T G x <= bound, G positive definite
    rational, by Fincke-Pohst on the Cholesky form (exact rationals)."""
    n = len(G)
    Q = [[Fr(G[i][j]) for j in range(n)] for i in range(n)]
    # Cholesky-type decomposition q_ii, q_ij
    q = [[Fr(0)]*n for _ in range(n)]
    A = [row[:] for row in Q]
    for i in range(n):
        q[i][i] = A[i][i]
        for j in range(i+1, n):
            q[i][j] = A[i][j]/A[i][i]
        for k in range(i+1, n):
            for l in range(k, n):
                A[k][l] -= q[i][k]*q[i][l]*q[i][i]
                A[l][k] = A[k][l]
    out = []
    x = [0]*n
    import math
    def rec(i, rem):
        # center
        c = -sum(q[i][j]*x[j] for j in range(i+1, n))
        r = math.isqrt(int(rem / q[i][i]) + 1) + 2
        lo = math.floor(c) - r; hi = math.ceil(c) + r
        for xi in range(lo, hi+1):
            d = q[i][i]*(xi - c)**2
            if d <= rem:
                x[i] = xi
                if i == 0:
                    if any(x): out.append(x[:])
                else:
                    rec(i-1, rem - d)
        x[i] = 0
    rec(n-1, Fr(bound))
    return out

def main():
    random.seed(20260928)
    QS = {
        "Q(zeta7)+ (disc 49)":  [[1, 0, 0], [2, 1, 0]],
        "Q(zeta9)+ (disc 81)":  [[1, 0, 0], [2, 1, 0]],
        "disc 229 (non-Galois)": [[1, 0, 0], [3, -1, 0]],
    }
    nchecks = 0
    summary = []
    for name, poly in FIELDS.items():
        mulv, tr, T, basis = field_data(poly)
        for qvec in QS[name]:
            # q totally positive: check sign at the three real roots numerically
            import cmath
            # real roots via numpy-free method: companion eigen by Durand-Kerner
            rr = durand_kerner(poly)
            qs = [sum(c*r**e for e, c in enumerate(qvec)) for r in rr]
            assert all(abs(z.imag) < 1e-9 and z.real > 0 for z in qs), qs
            monos, A = coefficient_matrix(poly, qvec)
            Lb = integral_lattice(A)
            # Gram matrix of -chi/8 on L
            G = [[None]*8 for _ in range(8)]
            for i in range(8):
                for j in range(8):
                    xi = Lb[i]; xj = Lb[j]
                    s = [a+b for a, b in zip(xi, xj)]
                    G[i][j] = (-(chi_formula(poly, qvec, s)
                                 - chi_formula(poly, qvec, xi)
                                 - chi_formula(poly, qvec, xj))/16)
            check_chi_direct(poly, qvec, Lb); nchecks += 1
            # the integral classes of S(0,q) with -chi <= 24, i.e. -chi/8 <= 3
            svs = short_vectors(G, 3)
            p = shape_prime(poly, qvec, 10**6)
            excluded = 0; generic_excluded = 0; tally = {}
            for x in svs:
                coeffs = [sum(Fr(x[b])*Lb[b][i] for b in range(8)) for i in range(8)]
                chi = chi_formula(poly, qvec, coeffs)
                inv = shape_invariants(poly, qvec, coeffs, p)
                Nw, Asum, rho, Msum, r2, r3 = inv
                need = -(r3 - 2*r2 + 22)
                ok = chi <= need
                key = (int(chi), r2, r3, ok)
                tally[key] = tally.get(key, 0) + 1
                if not ok:
                    excluded += 1
                    if (r2, r3) == (54, 112): generic_excluded += 1
            dens = sorted(set(x.denominator for row in Lb for x in row))
            summary.append((name, qvec, dens, len(svs), excluded,
                            generic_excluded, tally))
            print(f"{name}, q = {qvec}: lattice denominators {dens}; "
                  f"{len(svs)} classes with -chi <= 24; {excluded} violate the "
                  f"profile condition, {generic_excluded} of general shape")
            for key in sorted(tally):
                chi, r2, r3, ok = key
                print(f"    chi = {chi:4d}  (r2, r3) = ({r2}, {r3})  "
                      f"condition {'holds' if ok else 'FAILS'}: {tally[key]}")
            nchecks += 1
    return summary, nchecks

def durand_kerner(poly):
    a = [complex(c) for c in poly]
    n = len(a)-1
    roots = [complex(0.4, 0.9)**k for k in range(n)]
    for _ in range(500):
        new = []
        for i, r in enumerate(roots):
            num = sum(c*r**(n-k) for k, c in enumerate(a))
            den = 1
            for j, s in enumerate(roots):
                if j != i: den *= (r - s)
            new.append(r - num/den)
        roots = new
    return roots

if __name__ == "__main__":
    main()
