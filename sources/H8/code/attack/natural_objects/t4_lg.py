#!/usr/bin/env python3
"""
t4_lg.py -- verify the Veronese model of H_A at n = 4 (exact):

  (V1) there is ONE linear map Phi : Sym^4(Q^5) -> H^*(A,Q) with
       ch(F) = Phi( P(L_F)^4 ) for every natural object F tested:
       line bundles e^{D_S}, subtori [B_(p,q)], twisted subtori [B] e^{D_S},
       the point class; fitted on line bundles, tested on the others;
  (V2) the Weil classes are Phi(P(L_+-)^4) with L_+- = L_sub(1, -+delta),
       and e^{t eta} = Phi(P(L_{t diag(d,1)})^4);
  (V3) geometry in P^4: L_+- not in the plane P_theta spanned by the conic
       C_theta = {L_{t diag(d,1)}} u {point}; the line L_+ L_- misses P_theta;
       every point of C_theta is joined to L_+ by a line of Q^3
       (dim L_q cap L_+ = 1).
"""
import sys, random
from fractions import Fraction as Fr
from ext import *
from lg import *

n = 4
d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
S = Split(n, d)
b, bh, l = S.beta(), S.betahat(), S.ell()
random.seed(1)


def ch_lb(S11, S12, S22):
    return exp_class(add(add(scale(b, S11), scale(bh, S22)), scale(l, -S12)), 16)


def combined(P, ch):
    v = {(0, k): Fr(c) for k, c in mono4(P).items()}
    for k, c in ch.items():
        v[(1, k)] = -Fr(c)
    return v


E = Echelon()
pts = set()
while len(pts) < 90:
    pts.add(tuple(random.randint(-3, 3) for _ in range(3)))
for (a, c, e) in pts:
    E.add(combined(L_S(a, c, e), ch_lb(a, c, e)))
print("(V1) fitted on %d line bundles; rank of graph = %d (expect 55)" % (len(pts), E.rank()))


def test(P, ch):
    r = E.reduce(combined(P, ch))
    return not r


ok = True
# subtori, with both signs of the class allowed
for (p, q) in [(1, 0), (0, 1), (1, 1), (2, 1), (1, -3), (3, 2)]:
    B = S.subtorus(p, q)
    t1 = test(L_sub(p, q), B)
    t2 = test(L_sub(p, q), scale(B, -1))
    print("     subtorus (%d,%d): ch = +Phi: %s, = -Phi: %s" % (p, q, t1, t2))
    ok = ok and t1
# twisted subtori
for (p, q, s11, s12, s22) in [(1, 1, 1, 0, 0), (2, 1, 0, 1, 1), (1, -2, 2, -1, 1)]:
    B = S.subtorus(p, q)
    rows = twist_rows([(q, p, 0, 0), (0, 0, p, -q)], s11, s12, s22)
    P = pl_from_rows(*rows)
    chB = wedge(B, ch_lb(s11, s12, s22))
    t = test(P, chB)
    print("     twisted subtorus (%d,%d) by S=(%d,%d,%d): %s" % (p, q, s11, s12, s22, t))
    ok = ok and t
t = test(L_point(), S.point())
print("     point class: %s" % t)
ok = ok and t
print("(V1) overall:", ok)

# (V2) Weil classes: evaluate Phi at the conjugate points formally.
# P(L_sub(1, -delta)) = (0, 0, -delta^2, 1, -delta) = (0,0,d,1,-delta).
# P^4 = sum over monomials with delta powers; split into rational and delta parts.
def mono4_K(Pre, Pim):
    """P = Pre + delta*Pim with rational entries; return (Re, Im) monomial vectors
    of P^4 in the basis MONO4, delta^2 = -d."""
    re, im = {}, {}
    for idx, m in enumerate(MONO4):
        # product of (a_i + delta b_i)
        cur = (Fr(1), Fr(0))
        for i in m:
            a, bb = Fr(Pre[i]), Fr(Pim[i])
            cur = (cur[0] * a - d * cur[1] * bb, cur[0] * bb + cur[1] * a)
        if cur[0]:
            re[idx] = cur[0]
        if cur[1]:
            im[idx] = cur[1]
    return re, im


def apply_phi(mvec):
    """find the ch class with (mvec, ch) in the fitted graph: reduce (mvec, 0)
    and read off -residual on the ch coordinates"""
    v = {(0, k): Fr(c) for k, c in mvec.items()}
    r = E.reduce(v)
    assert all(key[0] == 1 for key in r), "monomial part not in span"
    return {key[1]: c for key, c in r.items()}


re, im = mono4_K((0, 0, d, 1, 0), (0, 0, 0, 0, -1))
WR, WI = apply_phi(re), apply_phi(im)
W1, W2 = S.weil_pair()
def prop(u, v):
    k0 = next(iter(u))
    r = Fr(u[k0]) / Fr(v[k0])
    return add(u, v, 1, -r) == {}, r
print("(V2) Phi(Re P(L_+)^4) prop W1:", prop(WR, W1), " Phi(Im) prop W2:", prop(WI, W2))
eta = S.eta()
for t in [1, 2, -1]:
    Pt = L_S(t * d, 0, t)
    et = exp_class(scale(eta, t), 16)
    print("     e^{%d eta} = Phi(P(L_{%d diag(d,1)})^4):" % (t, t), test(Pt, et))

# (V3) geometry
Pth = [(0, 1, 0, 0, 0), (0, 0, d, -1, 0), (d, 0, 0, 0, 0)]   # coefficients of 1, t, t^2
# check: L_S(t d, 0, t) = (t^2 d, 1, t d, -t, 0)
for t in [1, 2, 5]:
    assert L_S(t * d, 0, t) == (t * t * d, 1, t * d, -t, 0)
# rank of P_theta + Re L_+ + Im L_+
def rank_rows(rows):
    E2 = Echelon()
    for r in rows:
        E2.add({i: Fr(x) for i, x in enumerate(r) if x})
    return E2.rank()
ReL, ImL = (0, 0, d, 1, 0), (0, 0, 0, 0, 1)
print("(V3) rank [P_theta] = %d, rank [P_theta, Re L+] = %d, [P_theta, Im L+] = %d,"
      " [P_theta, Re, Im] = %d" % (rank_rows(Pth), rank_rows(Pth + [ReL]),
                                  rank_rows(Pth + [ImL]), rank_rows(Pth + [ReL, ImL])))
print("     => L_+- not in P_theta, line L_+L_- misses P_theta iff last rank is 5")
# lines through L_+ and points of C_theta: bilinear form of the quadric
def Bform(P, Q):
    p12, p34, p14, p23, p13 = P
    q12, q34, q14, q23, q13 = Q
    return Fr(p12 * q34 + p34 * q12, 2) + p13 * q13 + Fr(p14 * q23 + p23 * q14, 2)
# B(L_+, q) = 0 over K  <=>  B(ReL, q) = 0 and B(ImL, q) = 0
okline = True
for t in [Fr(1), Fr(2), Fr(-3), Fr(1, 2)]:
    q = L_S(t * d, 0, t)
    if Bform(ReL, q) != 0 or Bform(ImL, q) != 0:
        okline = False
q = L_point()
okline = okline and Bform(ReL, q) == 0 and Bform(ImL, q) == 0
print("     every tested point of C_theta is conjugate to L_+ (line in Q^3):", okline)
print("     (general t: B(ReL, L_t) = (t d - d t)/2 = 0 identically, B(ImL, L_t) = 0)")
