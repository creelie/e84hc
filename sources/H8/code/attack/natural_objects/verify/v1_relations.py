#!/usr/bin/env python3
"""
v1_relations.py d  -- independent checks (n = 4) of the T4 claims about
relations among natural Chern characters on A = X x Xhat.

(R0) H_A = span of monomials beta^a betahat^b ell^c: dims per degree.
(R1) Weil classes from the K-eigenspaces directly (alpha_pm = wedge of the
     8 eigen-1-forms u pm (delta/d) B u), versus (gamma - delta ell)^4.
(R2) subtori (track convention) in H_A; [B_(1,delta)] (formal) = alpha_- etc.
(R3) the explicit relation sum m_i [B_i] = 14 W2 (d = 1), and the closed form
     m_i ~ 1/((q_i^2 + d p_i^2) prod_{j != i} (p_i q_j - p_j q_i)) on random
     8-sets of subtori: pure Weil class.
(R4) the delicate configurations of the s = 8 case of the minimal-support
     proof, with points on several conics through l_W (twisted subtori
     O_B (x) O(t eta), whose Lagrangians lie on the conic e^{t eta} C_sub):
     4+4, 5+3, 6+2, 6+1+1, 7+1, 3+3+2, and 8 on one conic; plus 7-point sets.
"""
import sys, random, time
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd, factorial
from v4lib import *

d = int(sys.argv[1]) if len(sys.argv) > 1 else 1
n = 4
Mo = Model(n, d)
t0 = time.time()
b, bh, l, eta = Mo.beta(), Mo.betahat(), Mo.ell(), Mo.eta()

# ---------------- (R0) H_A with pivot coordinates per degree
pb = [pw(b, k) for k in range(n + 1)]
pbh = [pw(bh, k) for k in range(n + 1)]
pl = [pw(l, k) for k in range(2 * n + 1)]
HA = {}
for k in range(2 * n + 1):
    R = RREF()
    for a in range(0, min(k, n) + 1):
        for bb in range(0, min(k - a, n) + 1):
            c = k - a - bb
            if c > 2 * n:
                continue
            R.add(wedge(wedge(pb[a], pbh[bb]), pl[c]))
    HA[k] = R
dims = [HA[k].rank() for k in range(2 * n + 1)]
print("(R0) dim of span{beta^a betahat^b ell^c} in H^{2k}:", dims, "total", sum(dims))


def coords(u):
    """coordinates of u in H_A (pivot values), asserting membership"""
    out = []
    for k in range(2 * n + 1):
        uk = deg(u, 2 * k)
        rem = HA[k].reduce(uk)
        assert not rem, "class not in H_A (degree %d)" % (2 * k)
        for pk, row in HA[k].rows:
            out.append(Fr(uk.get(pk, 0)))
    return {i: c for i, c in enumerate(out) if c != 0}


# ---------------- (R1) Weil classes from eigenspaces
def eig_form(i, sign):
    # u + sign*(delta/d) B u for u = x_i, coefficients in Q(delta)
    out = {Mo.x(i): QD(1, 0, d)}
    for k, c in Mo.Bmap(i).items():
        out[k] = QD(0, Fr(sign * c, d), d)
    return out


def check_eigen(sign):
    # M^*: x -> -Bx, xi -> d B^{-1} xi ; B^{-1} xi_{n+j} = x_j, B^{-1} xi_j = -x_{n+j}
    ok = True
    for i in range(1, 2 * n + 1):
        f = eig_form(i, sign)
        Mf = {}
        for k, c in f.items():
            idx = k.bit_length() - 1
            if idx < 2 * n:  # x_{idx+1}
                for kk, cc in Mo.Bmap(idx + 1).items():
                    Mf[kk] = Mf.get(kk, QD(0, 0, d)) + c * (-cc)
            else:
                j = idx - 2 * n + 1
                if j <= n:
                    img = {Mo.x(n + j): -1}
                else:
                    img = {Mo.x(j - n): 1}
                for kk, cc in img.items():
                    Mf[kk] = Mf.get(kk, QD(0, 0, d)) + c * (d * cc)
        lam = QD(0, sign, d)
        for k in set(f) | set(Mf):
            if Mf.get(k, QD(0, 0, d)) != lam * f.get(k, QD(0, 0, d)):
                ok = False
    return ok


print("(R1) u + (delta/d)Bu is an M-eigenvector with eigenvalue +delta:", check_eigen(+1),
      "; u - (delta/d)Bu with -delta:", check_eigen(-1))
alpha = {}
for sgn in (+1, -1):
    r = {0: QD(1, 0, d)}
    for i in range(1, 2 * n + 1):
        r = wedge(r, eig_form(i, sgn))
    alpha[sgn] = r
aRe, aIm = re_im(alpha[+1])
gam = lin((d, b), (-1, bh))
# (gamma - delta ell)^4 over Q(delta)
gq = {k: QD(c, 0, d) for k, c in gam.items()}
lq = {k: QD(0, -c, d) for k, c in l.items()}
P4 = pw(lin((1, gq), (1, lq)), 4)
W1, W2 = re_im(P4)          # (gamma - delta ell)^4 = W1 + delta W2 : ext.py normalisation
print("     alpha_+ = Re + delta Im; Re, Im in H_A (degree 8):",
      not HA[4].reduce(aRe), not HA[4].reduce(aIm))
print("     eta ^ alpha_+ = 0:", not wedge(eta, aRe) and not wedge(eta, aIm))
# relation between (gamma - delta ell)^4 and alpha_+ / alpha_-
cW1, cW2, cRe, cIm = coords(W1), coords(W2), coords(aRe), coords(aIm)
print("     rank{W1, W2, Re alpha_+, Im alpha_+} =", rank([cW1, cW2, cRe, cIm]), "(expect 2)")
ker = nullspace([cW1, cW2, cRe, cIm])
print("     relations (W1, W2, Re a+, Im a+):", [[str(x) for x in k] for k in ker])

# ---------------- (R2) subtori and the formal points (1, -+delta)
def F_formal(p, q):
    """raw wedge of the track's conormal forms at (p,q) in Q(delta) (no sign fix)"""
    r = {0: QD(1, 0, d)}
    for j in range(1, n + 1):
        f1 = {Mo.xi(j): p, Mo.x(n + j): -q}
        f2 = {Mo.xi(n + j): p, Mo.x(j): q}
        r = wedge(r, {k: (c if isinstance(c, QD) else QD(c, 0, d)) for k, c in f1.items()})
        r = wedge(r, {k: (c if isinstance(c, QD) else QD(c, 0, d)) for k, c in f2.items()})
    return r


Fm = F_formal(QD(1, 0, d), QD(0, -1, d))   # (p,q) = (1, -delta)
FmRe, FmIm = re_im(Fm)
print("(R2) P(1,-delta) = Re + delta Im; rank{Re, Im, Re a+, Im a+} =",
      rank([coords(FmRe), coords(FmIm), cRe, cIm]))
kerP = nullspace([coords(FmRe), coords(FmIm), cW1, cW2])
print("     relations (Re P, Im P, W1, W2):", [[str(x) for x in k] for k in kerP])
# sign of the raw wedge vs normalised subtorus
raw_sign = {}
for (p, q) in [(1, 0), (0, 1), (1, 1), (2, -1), (3, 5)]:
    raw = {k: c.a for k, c in F_formal(QD(p, 0, d), QD(q, 0, d)).items() if c.a != 0}
    st = Mo.subtorus_track(p, q)
    raw_sign[(p, q)] = 1 if raw == st else (-1 if {k: -c for k, c in raw.items()} == st else 0)
print("     sign of raw wedge relative to normalised [B] at test points:", raw_sign)


def Bc(p, q):
    return coords(Mo.subtorus_track(p, q))


# ---------------- (R3) explicit relation
Wbasis = [cW1, cW2]
THETA = [coords(pw(eta, k)) for k in range(2 * n + 1)]


def weil_part(vecs, coeffs):
    tot = {}
    for v, c in zip(vecs, coeffs):
        for k, x in v.items():
            tot[k] = tot.get(k, 0) + c * x
    tot = {k: x for k, x in tot.items() if x != 0}
    ker = nullspace([tot, cW1, cW2])
    return ker


if d == 1:
    pts = [(1, -3), (1, -2), (1, 2), (1, 3), (2, -1), (2, 1), (3, -1), (3, 1)]
    m = [-1, 16, -16, 1, -16, 16, 1, -1]
    vecs = [Bc(p, q) for (p, q) in pts]
    tot = {}
    for v, c in zip(vecs, m):
        for k, x in v.items():
            tot[k] = tot.get(k, 0) + c * x
    tot = {k: x for k, x in tot.items() if x}
    diff = {k: tot.get(k, 0) - 14 * cW2.get(k, 0) for k in set(tot) | set(cW2)}
    print("(R3) d=1: sum m_i [B_i] == 14 W2 (W2 = Im(gamma - delta ell)^4/delta):",
          all(x == 0 for x in diff.values()))
    diff2 = {k: tot.get(k, 0) + 14 * cW2.get(k, 0) for k in set(tot) | set(cW2)}
    print("          sum m_i [B_i] == -14 W2:", all(x == 0 for x in diff2.values()))
    # with the other sign convention phi^* = +B^{-1}: B'_(p,q) = B_(p,-q)
    vecs2 = [Bc(p, -q) for (p, q) in pts]
    tot2 = {}
    for v, c in zip(vecs2, m):
        for k, x in v.items():
            tot2[k] = tot2.get(k, 0) + c * x
    ker = nullspace([{k: x for k, x in tot2.items() if x}, cW1, cW2])
    print("     with B'_(p,q) = B_(p,-q) (convention phi^* = +B^{-1}): relation (sum, W1, W2) =",
          [[str(x) for x in k] for k in ker])

random.seed(12345)


def closed_form(pts):
    out = []
    for i, (p, q) in enumerate(pts):
        den = Fr(q * q + d * p * p)
        for j, (pj, qj) in enumerate(pts):
            if j != i:
                den *= (p * qj - pj * q)
        out.append(1 / den)
    return out


cand = [(p, q) for p in range(0, 6) for q in range(-6, 7)
        if gcd(p, q) == 1 and not (p == 0 and q != 1)]
okc = 0
trials = 12
for t in range(trials):
    pts = random.sample(cand, 8)
    mm = closed_form(pts)
    vecs = [Bc(p, q) for (p, q) in pts]
    tot = {}
    for v, c in zip(vecs, mm):
        for k, x in v.items():
            tot[k] = tot.get(k, 0) + c * x
    tot = {k: x for k, x in tot.items() if x}
    # pure Weil class and nonzero?
    r = rank([tot, cW1, cW2])
    okc += (r == 2 and bool(tot))
print("(R3) closed-form m_i gives a nonzero pure Weil class on random 8-sets of subtori: %d/%d"
      % (okc, trials))

# ---------------- (R4) delicate configurations
eta_exp = {t: Mo.expo(lin((t, eta))) for t in (0, 1, 2, -1)}


def twisted(p, q, t):
    return coords(wedge(Mo.subtorus_track(p, q), eta_exp[t]))


def has_weil_relation(vecs, with_theta=True):
    base = vecs + (THETA if with_theta else [])
    r0 = rank(base)
    r1 = rank(base + [cW1, cW2])
    return r1 < r0 + 2


def conic_pts(t, k, rng):
    ps = rng.sample(cand, k)
    return [twisted(p, q, t) for (p, q) in ps]


rng = random.Random(99)
tests = [("8 on conic t=0", [(0, 8)]), ("8 on conic t=1", [(1, 8)]),
         ("7 on t=0", [(0, 7)]), ("7 on t=1", [(1, 7)]),
         ("4+4 (t=0,1)", [(0, 4), (1, 4)]), ("5+3 (t=0,1)", [(0, 5), (1, 3)]),
         ("6+2 (t=0,1)", [(0, 6), (1, 2)]), ("6+1+1 (t=0,1,2)", [(0, 6), (1, 1), (2, 1)]),
         ("7+1 (t=0,1)", [(0, 7), (1, 1)]), ("7+1 (t=0,-1)", [(0, 7), (-1, 1)]),
         ("3+3+2 (t=0,1,2)", [(0, 3), (1, 3), (2, 2)]),
         ("4+4 (t=1,2)", [(1, 4), (2, 4)]), ("6+2 (t=-1,2)", [(-1, 6), (2, 2)])]
for name, spec in tests:
    res = []
    for rep in range(3):
        vecs = []
        for (t, k) in spec:
            vecs += conic_pts(t, k, rng)
        res.append((has_weil_relation(vecs), has_weil_relation(vecs, with_theta=False)))
    print("(R4) %-18s relation-with-Q[theta] / pure relation over 3 draws: %s" % (name, res))

# line bundles e^{D_S}: random small S, and mixtures
def lb(a, bb, c):
    return coords(Mo.expo(lin((a, b), (bb, bh), (-c, l))))


mix = []
for rep in range(3):
    vecs = [lb(rng.randint(-3, 3), rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(4)]
    vecs += conic_pts(0, 4, rng)
    mix.append(has_weil_relation(vecs))
print("(R4) 4 random line bundles + 4 subtori: relation over 3 draws:", mix)
mix = []
for rep in range(3):
    vecs = [lb(rng.randint(-3, 3), rng.randint(-3, 3), rng.randint(-3, 3)) for _ in range(8)]
    mix.append(has_weil_relation(vecs))
print("(R4) 8 random line bundles: relation over 3 draws:", mix)
print("time %.1fs" % (time.time() - t0))
