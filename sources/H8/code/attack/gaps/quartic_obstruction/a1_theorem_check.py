"""a1_theorem_check.py -- exact checks of the ingredients of the obstruction theorem
(track A1, F0 = Q(sqrt5), O_0 = Z[phi], pi = sqrt5):

 (L) R_Z = { V in Herm_3(O_0) : V_11 = V_20 (mod pi) }   (V-coordinates, diag in Z).
 (1) rank V = 1:  chi(v) = 4 lambda^2 N(D) with lambda D = 0 mod pi, hence 20 | chi.
 (2) rank V = 2:  adj V = mu lbar l^T (mu in Z, l primitive), sigma_2(JVJVbar) = mu^2 N(Delta),
     chi^2 - 4 sigma_2 >= 0 with equality iff the Hochschild profile has r^2 = 12 (N_w = 2),
     and chi^2 = 4 mu^2 N(Delta) (mod 5).
 (3) consequently chi = 6 with r^2 = 20 would need mu^2 N(Delta) = 4, impossible since
     Delta = B^2 - 4AC is never -eps^2 or -2 eps^2 (eps a unit) modulo 4 O_0.
"""
import sys, time, random, itertools, pickle
from fractions import Fraction as Fr
import flint
from ealib import *
from a1model import RMModel, QS
import a1_secant as SEC
import a1_prodtype as PT

M = RMModel()
LAT = pickle.load(open("a1_lattice.pkl", "rb"))
RZ = LAT["RZ"]
J = [[0, 0, 1], [0, -2, 0], [1, 0, 0]]


def herm_class(r, h, g, c, k, m):
    return PT.class_from(r, h, g, c, k, m)


def Vmat(r, h, g, c, k, m):
    Z = QS(0, 0, 5)
    return [[QS(r, 0, 5), h.conj(), g.conj()], [h, QS(c, 0, 5), k.conj()], [g, k, QS(m, 0, 5)]]


def mm(A, B):
    return [[sum((A[i][l] * B[l][j] for l in range(3)), QS(0, 0, 5)) for j in range(3)] for i in range(3)]


def conjm(A):
    return [[x.conj() for x in r] for r in A]


def JQ():
    return [[QS(x, 0, 5) for x in r] for r in J]


def adj3(A):
    def cof(i, j):
        rows = [r for r in range(3) if r != i]
        cols = [c for c in range(3) if c != j]
        a, b = rows
        c_, d = cols
        return A[a][c_] * A[b][d] - A[a][d] * A[b][c_]
    return [[cof(j, i) * (1 if (i + j) % 2 == 0 else -1) for j in range(3)] for i in range(3)]


def is_int(x):
    return PT.is_int(x)


t0 = time.time()
# (L) lattice description: the congruence lattice has a Z-basis; compare with RZ (saturation)
gens = []
for (r, h, g, c, k, m) in [(1, 0, 0, 0, 0, 0), (0, (1, 0), 0, 0, 0, 0), (0, (0, 1), 0, 0, 0, 0),
                           (0, 0, 0, 0, (1, 0), 0), (0, 0, 0, 0, (0, 1), 0), (0, 0, 0, 0, 0, 1),
                           (0, 0, (1, 0), 1, 0, 0), (0, 0, (0, 1), 3, 0, 0), (0, 0, 0, 5, 0, 0)]:
    def el(x):
        return PT.oelt(*x) if isinstance(x, tuple) else PT.oelt(x, 0)
    gens.append(herm_class(r, el(h), el(g), c, el(k), m))
# each generator in RZ and each RZ basis vector in span_Z(gens)
ok1 = all(PT.in_RZ(v) for v in gens)
G2 = [[x for x in v.items()] for v in gens]
def in_span_Z(v, basis):
    keys = sorted(set(k for b in basis for k in b) | set(v))
    Mq = flint.fmpq_mat(len(keys), len(basis) + 1)
    for j, b in enumerate(basis):
        for i, kk in enumerate(keys):
            Mq[i, j] = flint.fmpq(int(b.get(kk, 0)), 1)
    for i, kk in enumerate(keys):
        x = Fr(v.get(kk, 0)); Mq[i, len(basis)] = flint.fmpq(x.numerator, x.denominator)
    R, rk = Mq.rref()
    sol = [Fr(0)] * len(basis)
    for i in range(rk):
        piv = next(j for j in range(len(basis) + 1) if R[i, j] != 0)
        if piv == len(basis):
            return False
        sol[piv] = Fr(int(R[i, len(basis)].p), int(R[i, len(basis)].q))
    return all(s.denominator == 1 for s in sol)
ok2 = all(in_span_Z(b, gens) for b in RZ)
check("(L) R_Z equals the congruence lattice {V in Herm_3(O_0): V_11 = V_20 mod sqrt5}", ok1 and ok2)

rng = random.Random(2026)
n1 = n2 = 0
bad = []
eq_cases = {"eq": 0, "strict": 0}
for trial in range(4000):
    # random rank <= 2 integral V: V = sum of 2 random 'norm' terms  lam_i N(alpha_i) plus congruence fix
    def rel():
        return PT.oelt(rng.randint(-3, 3), rng.randint(-3, 3))
    kind = rng.random()
    if kind < 0.3:
        # rank one: lam * alpha alphabar^T
        al = [rel(), rel(), rel()]
        lam = rng.randint(-3, 3)
        if lam == 0 or all(a == 0 for a in al):
            continue
        V = [[al[i] * al[j].conj() * lam for j in range(3)] for i in range(3)]
    else:
        al = [rel(), rel(), rel()]; be = [rel(), rel(), rel()]
        l1, l2 = rng.randint(-2, 2), rng.randint(-2, 2)
        cr = rel()
        V = [[al[i] * al[j].conj() * l1 + be[i] * be[j].conj() * l2 + cr * al[i] * be[j].conj()
              + cr.conj() * be[i] * al[j].conj() for j in range(3)] for i in range(3)]
    r_, c_, m_ = V[0][0], V[1][1], V[2][2]
    h_, g_, k_ = V[1][0], V[2][0], V[2][1]
    # integrality in R_Z requires c = g mod sqrt5: test
    cand = herm_class(r_.a, h_, g_, c_.a, k_, m_.a)
    if not cand or not PT.in_RZ(cand):
        continue
    rk = SEC.rankV(V)
    chi = M.chi(cand)
    if rk == 1:
        n1 += 1
        if chi % 20 != 0:
            bad.append(("rank1", chi))
    elif rk == 2:
        A_ = adj3(V)
        # l: a nonzero row of adj V (rows proportional to l)
        row = next(r for r in A_ if any(x != 0 for x in r))
        # primitive l: divide by gcd in O_0 -- use the left kernel via cross product of two columns
        # compute mu = adj V / (lbar l^T) with l primitive: find gcd via content of row entries
        # Simple approach: l = row / g where g = gcd of entries (O_0 is a PID; use Euclid on norms)
        def gcd_O(a, b):
            while b != 0:
                # division with remainder in Z[phi] (Euclidean for the norm)
                qv = a / b
                # round coordinates in basis 1, phi
                x0 = qv.a - qv.b; x1 = 2 * qv.b
                q0 = PT.oelt(round(x0), round(x1))
                a, b = b, a - q0 * b
            return a
        gg = QS(0, 0, 5)
        for x in row:
            gg = gcd_O(gg, x) if gg != 0 else x
        l = [x / gg for x in row]
        assert all(is_int(x) for x in l)
        # adj V = mu lbar l^T : mu = adj[i][j] / (lbar_i l_j)
        mu = None
        for i in range(3):
            for j in range(3):
                den = l[i].conj() * l[j]
                if den != 0:
                    mu = A_[i][j] / den
                    break
            if mu is not None:
                break
        okmu = all(A_[i][j] == mu * l[i].conj() * l[j] for i in range(3) for j in range(3))
        A0, B0, C0 = l
        Delta = B0 * B0 - 4 * A0 * C0
        T = mm(mm(JQ(), V), mm(JQ(), conjm(V)))
        sig2 = sum((T[i][i] * T[j][j] - T[i][j] * T[j][i] for i in range(3) for j in range(i + 1, 3)), QS(0, 0, 5))
        trT = T[0][0] + T[1][1] + T[2][2]
        cond = okmu and mu.b == 0 and mu.a.denominator == 1 and trT == chi and sig2 == mu * mu * Delta.norm()
        cond = cond and ((chi * chi - 4 * mu.a * mu.a * Delta.norm()) % 5 == 0)
        secant = Delta.val() < 0 and Delta.conj().val() < 0
        if secant:
            cond = cond and (chi * chi - 4 * sig2.a >= 0)
            prof = M.profile(cand, 2)
            eq = (chi * chi == 4 * sig2.a)
            cond = cond and (eq == (prof[2] == 12)) and prof[2] in (12, 20)
            eq_cases["eq" if eq else "strict"] += 1
        n2 += 1
        if not cond:
            bad.append(("rank2", chi, mu, Delta))
check("(1) rank-one integral V: 20 | chi  (%d random classes)" % n1, not any(b[0] == "rank1" for b in bad))
check("(2) rank-two integral V: adj V = mu lbar l^T, mu in Z, tr(JVJVbar) = chi, sigma_2(JVJVbar) = mu^2 N(Delta), "
      "chi^2 = 4 mu^2 N(Delta) mod 5; for complex-secant V also chi^2 >= 4 sigma_2 with equality iff r^2 = 12 "
      "(%d classes; complex-secant: %s)" % (n2, eq_cases),
      not any(b[0] == "rank2" for b in bad), detail=str(bad[:5]))
# (3) squares mod 4 in Z[phi]
sq = set()
for a in range(4):
    for b in range(4):
        x = PT.oelt(a, b) * PT.oelt(a, b)
        x0 = int(x.a - x.b) % 4; x1 = int(2 * x.b) % 4
        sq.add((x0, x1))
def mod4(x):
    return (int(x.a - x.b) % 4, int(2 * x.b) % 4)
units = [PT.PHI ** 0 if False else PT.oelt(1, 0)]
u = PT.oelt(1, 0)
bad3 = []
for kexp in range(0, 12):
    e2 = PT.oelt(1, 0)
    for _ in range(2 * kexp):
        e2 = e2 * PT.PHI
    for cand in (-e2, -2 * e2):
        if mod4(cand) in sq:
            bad3.append(cand)
check("(3) -phi^{2k} and -2 phi^{2k} are not squares modulo 4 Z[phi] (k = 0..11; phi^6 = 1 mod 4)",
      not bad3, detail="squares mod 4 (coords in 1,phi): %s" % sorted(sq))
print("time %.1fs" % (time.time() - t0))
summary()
