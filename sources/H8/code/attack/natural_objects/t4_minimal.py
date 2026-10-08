#!/usr/bin/env python3
"""
t4_minimal.py -- sanity checks of the minimal-configuration theorem at n = 4
in the Veronese model (relations among nu_4(p) computed on quartics of P^4,
which for points of Q^3 is the same as on H^0(Q^3, O(4)) = H_A^dual).

weil_relation(pts): True iff span(nu(pts) u nu(C_theta)) meets the Weil plane
span(Re nu(L_+), Im nu(L_+)) nontrivially.

  (M1) 8 subtori on C_sub: relation, pure (no C_theta part needed)
  (M2) 8 rational points on another conic Pi cap Q^3, Pi = <l_W, w>, w a line
       bundle point: relation, pure
  (M3) 7 of those 8 plus any other natural point: no relation
  (M4) random sets of 7 and of 8 natural points (small height): no relation
  (M5) 8 points on a conic through a point of C_theta is impossible (degenerate)
"""
import sys, random
from fractions import Fraction as Fr
from itertools import combinations
from ext import Echelon
from lg import L_S, L_sub, L_point, pl_from_rows, quadric, twist_rows, MONO4, mono4

d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
random.seed(7)

def monoK(Pre, Pim):
    re, im = {}, {}
    for idx, m in enumerate(MONO4):
        cur = (Fr(1), Fr(0))
        for i in m:
            a, bb = Fr(Pre[i]), Fr(Pim[i])
            cur = (cur[0] * a - d * cur[1] * bb, cur[0] * bb + cur[1] * a)
        if cur[0]: re[idx] = cur[0]
        if cur[1]: im[idx] = cur[1]
    return re, im
WRe, WIm = monoK((0, 0, d, 1, 0), (0, 0, 0, 0, -1))
Ctheta = [L_S(t * d, 0, t) for t in range(-4, 5)]
def rank(vs):
    E = Echelon()
    for v in vs:
        E.add({k: Fr(c) for k, c in v.items()})
    return E.rank()
def weil_relation(pts, with_theta=True):
    base = [mono4(p) for p in pts] + ([mono4(q) for q in Ctheta] if with_theta else [])
    r0 = rank(base)
    r1 = rank(base + [WRe, WIm])
    return r1 < r0 + 2

# (M1)
sub = [L_sub(p, q) for (p, q) in [(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1), (1, -2), (2, -1)]]
print("(M1) 8 subtori: relation %s, pure (without C_theta) %s"
      % (weil_relation(sub), weil_relation(sub, with_theta=False)))
print("     any 7 of them: relation", any(weil_relation(list(c)) for c in combinations(sub, 7)))

# (M2) conic through l_W and a line bundle point w = L_S(1, 0, 2) (say)
w = L_S(1, 1, 2)
ReL, ImL = (0, 0, d, 1, 0), (0, 0, 0, 0, 1)
def comb(a, bq, c):
    return tuple(a * x + bq * y + c * z for x, y, z in zip(ReL, ImL, w))
pts = []
for a in range(-3, 4):
    for bq in range(-3, 4):
        # solve quadric(a ReL + b ImL + c w) = 0 for c (linear in c since quadric(w)=0)
        # q(c) = A + c B, with A = quadric(a ReL + b ImL), B = 2 * bilinear
        A = quadric(comb(a, bq, 0))
        Bv = quadric(comb(a, bq, 1)) - A
        if Bv == 0 or (a, bq) == (0, 0):
            continue
        c = Fr(-A, Bv)
        Pv = comb(Fr(a), Fr(bq), c)
        assert quadric(Pv) == 0
        # normalise
        k = next(x for x in Pv if x != 0)
        Pv = tuple(x / k for x in Pv)
        if Pv not in pts:
            pts.append(Pv)
print("(M2) rational points found on the conic <l_W, w> cap Q^3:", len(pts))
C8 = pts[:8]
print("     8 of them: relation %s, pure %s" % (weil_relation(C8), weil_relation(C8, with_theta=False)))
# classify the 8 points by cell
cells = []
for Pv in C8:
    cells.append("line bundle/semi-hom." if Pv[1] != 0 else ("point" if Pv[0] != 0 and all(x == 0 for x in Pv[1:]) else "twisted subtorus"))
print("     cells of the 8 points:", cells)
# (M3)
others = [L_S(1, 0, 0), L_S(2, 1, -1), L_sub(3, 1), L_point(), L_S(0, 1, 3)]
bad = 0
for c7 in combinations(C8, 7):
    for o in others:
        if weil_relation(list(c7) + [o]):
            bad += 1
print("(M3) 7 conic points + 1 other point: relations found:", bad, "(expect 0)")
# (M4)
def rand_nat():
    t = random.random()
    if t < 0.6:
        return L_S(random.randint(-3, 3), random.randint(-3, 3), random.randint(-3, 3))
    p, q = random.choice([(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3)])
    rows = twist_rows([(q, p, 0, 0), (0, 0, p, -q)], random.randint(-2, 2), random.randint(-2, 2), random.randint(-2, 2))
    return pl_from_rows(*rows)
cnt7 = cnt8 = 0
for trial in range(200):
    S7 = []
    while len(S7) < 7:
        Pv = rand_nat()
        if Pv not in S7:
            S7.append(Pv)
    cnt7 += weil_relation(S7)
    S8 = S7 + [rand_nat()]
    cnt8 += weil_relation(S8)
print("(M4) random natural 7-sets with a Weil relation: %d/200; 8-sets: %d/200" % (cnt7, cnt8))
# (M5) plane through l_W and a point of C_theta
q = L_S(2 * d, 0, 2)
Aq = [quadric(tuple(a * x + bb * y + c * z for x, y, z in zip(ReL, ImL, q)))
      for (a, bb, c) in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 0)]]
print("(M5) quadratic form on <l_W, q>, q in C_theta: q(ReL)=%s q(ImL)=%s q(q)=%s, "
      "B(ReL,q)=%s B(ImL,q)=%s -> conic = {d a^2 + b^2 = 0}: two conjugate lines through q"
      % (Aq[0], Aq[1], Aq[2], Fr(Aq[3] - Aq[0] - Aq[2], 2), Fr(Aq[4] - Aq[1] - Aq[2], 2)))
