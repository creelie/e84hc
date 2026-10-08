#!/usr/bin/env python3
"""
Round 19, target f2-mumford, as rerun by the referee; packaged for
the paper with the floating-point steps replaced by exact ones and
without the self-written log (the transcript is transcripts/m2_weil_closure.log).
Item (LX), mumford_motivic.py, condenses these checks.

weil_closure.py -- exact checks for the Weil-closure obstruction (round 19,
target f2-mumford).

Split model: V = Q^2 (x) Q^2 (x) Q^2 with psi = eps(x)eps(x)eps, H^1(X x X) =
V (x) Q^2.  The field L = Q(i) acts on X x X through J = [[0,-1],[1,0]] in
M_2(Q) = End^0(X x X); the Weil classes of (X x X, L) are Re/Im of
alpha = /\_{a} (e_a (x) u), u = f_0 - i f_1, in H^8(X x X) = /\^8(V (x) Q^2).

Checks (exact integer arithmetic):
  1. the three divisor classes psi_00, psi_01, psi_11 are sp(V)-invariant;
     the 15 degree-4 monomials in them are linearly independent in H^8;
  2. Re(alpha), Im(alpha) are sl(V)-invariant (killed by all 63 elementary
     traceless matrices acting as derivations);
  3. Re(alpha), Im(alpha) lie in the span of the 15 monomials: the Weil
     classes of X x X for L are polynomials in divisor classes;
  4. mixed case (the key step of the Weil-closure theorem): for
     Y = X^2 x B with H^1(B) = H (x) Q^2, dim H = 2, and L acting diagonally
     through J on both Q^2's, the Weil class /\^{10}_L H^1(Y) is killed by
     sp(V) (indeed sl(V)) acting on the V-part only.
"""
import itertools
import numpy as np
from flint import fmpz_mat

LOG = []
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s); LOG.append(s)
def check(c, msg):
    if not c:
        raise AssertionError("FAILED: " + msg)
    log("  ok:", msg)

eps = np.array([[0, 1], [-1, 0]], dtype=np.int64)
psi = np.kron(np.kron(eps, eps), eps)
psi_inv = -psi                     # psi^2 = -1
assert (psi_inv @ psi == np.eye(8, dtype=np.int64)).all()

# ------------------------------------------------ exterior algebra (sparse)
def sort_sign(idx):
    idx = list(idx)
    if len(set(idx)) < len(idx):
        return None, 0
    sign = 1
    # bubble sort parity
    arr = idx[:]
    for i in range(len(arr)):
        for j in range(len(arr) - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                sign = -sign
    return tuple(arr), sign

def wedge(A, B):
    out = {}
    for ma, ca in A.items():
        for mb, cb in B.items():
            m, s = sort_sign(ma + mb)
            if s == 0:
                continue
            out[m] = out.get(m, 0) + s * ca * cb
    return {m: c for m, c in out.items() if c != 0}

def add(A, B, cb=1):
    out = dict(A)
    for m, c in B.items():
        out[m] = out.get(m, 0) + cb * c
    return {m: c for m, c in out.items() if c != 0}

def act(X, A, nV, ncopies, extra=0):
    """derivation action of X in gl(V) on the V-part of /\\(V (x) Q^ncopies (+) extra):
    basis index of e_a (x) f_j is a + nV*j; indices >= nV*ncopies are 'extra' (untouched)."""
    out = {}
    for m, c in A.items():
        for s, idx in enumerate(m):
            if idx >= nV * ncopies:
                continue
            a, j = idx % nV, idx // nV
            for d in range(nV):
                x = int(X[d, a])
                if x == 0:
                    continue
                new = list(m); new[s] = d + nV * j
                mm, sg = sort_sign(new)
                if sg == 0:
                    continue
                out[mm] = out.get(mm, 0) + sg * c * x
    return {m: c for m, c in out.items() if c != 0}

def rank_of(vectors):
    keys = sorted(set(k for v in vectors for k in v))
    pos = {k: i for i, k in enumerate(keys)}
    rows = []
    for v in vectors:
        r = [0] * len(keys)
        for k, c in v.items():
            r[pos[k]] = c
        rows.append(r)
    return fmpz_mat(rows).rank()

nV = 8
def psi_class(j, k):
    out = {}
    for a in range(nV):
        for b in range(nV):
            w = int(psi_inv[a, b])
            if w == 0:
                continue
            m, s = sort_sign((a + nV * j, b + nV * k))
            if s == 0:
                continue
            out[m] = out.get(m, 0) + s * w
    return {m: c for m, c in out.items() if c != 0}

P = {(0, 0): psi_class(0, 0), (0, 1): psi_class(0, 1), (1, 1): psi_class(1, 1)}

# sp(V) basis and sl(V) basis
sp_basis = []
for i in range(8):
    for j in range(i, 8):
        S = np.zeros((8, 8), dtype=np.int64); S[i, j] = 1; S[j, i] = 1
        sp_basis.append(psi_inv @ S)
sl_basis = []
for i in range(8):
    for j in range(8):
        if i != j:
            M = np.zeros((8, 8), dtype=np.int64); M[i, j] = 1; sl_basis.append(M)
for i in range(7):
    M = np.zeros((8, 8), dtype=np.int64); M[i, i] = 1; M[i + 1, i + 1] = -1; sl_basis.append(M)

for key, c in P.items():
    assert all(len(act(X, c, nV, 2)) == 0 for X in sp_basis)
check(True, "psi_00, psi_01, psi_11 are sp(V)-invariant")
check(any(len(act(X, P[(0, 0)], nV, 2)) for X in sl_basis),
      "psi_00 is not sl(V)-invariant (as expected: sl-invariants are smaller)")

# degree-4 monomials
monos = []
names = []
keys3 = [(0, 0), (0, 1), (1, 1)]
for combo in itertools.combinations_with_replacement(range(3), 4):
    v = {(): 1}
    for t in combo:
        v = wedge(v, P[keys3[t]])
    monos.append(v)
    names.append("*".join("psi" + "%d%d" % keys3[t] for t in combo))
r15 = rank_of(monos)
log("  rank of the 15 degree-4 monomials in psi_00, psi_01, psi_11 in H^8(XxX):", r15)
check(r15 == 15, "the 15 monomials are linearly independent (dimension 15 of thm:lefschetzclosure)")

# Weil classes for L = Q(i) via J on Q^2
Re, Im = {}, {}
for S in itertools.product((0, 1), repeat=nV):
    k = sum(S)
    m, s = sort_sign(tuple(a + nV * S[a] for a in range(nV)))
    if k % 4 == 0:
        Re[m] = Re.get(m, 0) + s
    elif k % 4 == 2:
        Re[m] = Re.get(m, 0) - s
    elif k % 4 == 1:
        Im[m] = Im.get(m, 0) - s
    else:
        Im[m] = Im.get(m, 0) + s
Re = {m: c for m, c in Re.items() if c}
Im = {m: c for m, c in Im.items() if c}
log("  Weil classes: |supp Re| = %d, |supp Im| = %d" % (len(Re), len(Im)))
# J-invariance of the Weil line: J acts on /\^8 as multiplication by det_L = i^8... check that
# (1 (x) J) maps alpha to i^8 alpha = alpha, i.e. Re, Im are fixed by J acting on all 16 vectors
def actJ(A):
    # group action (not derivation): x_{a,0} -> x_{a,1}, x_{a,1} -> -x_{a,0}
    out = {}
    for m, c in A.items():
        new = []; sign = 1
        for idx in m:
            a, j = idx % nV, idx // nV
            if j == 0:
                new.append(a + nV)
            else:
                new.append(a); sign = -sign
        mm, sg = sort_sign(new)
        out[mm] = out.get(mm, 0) + sg * sign * c
    return {m: c for m, c in out.items() if c}
check(actJ(Re) == Re and actJ(Im) == Im, "the Weil classes are fixed by the automorphism J of X x X")
check(all(len(act(X, Re, nV, 2)) == 0 and len(act(X, Im, nV, 2)) == 0 for X in sl_basis),
      "Re(alpha), Im(alpha) are sl(V)-invariant (all 63 traceless elementary matrices)")
check(rank_of(monos + [Re]) == 15 and rank_of(monos + [Im]) == 15,
      "Re(alpha), Im(alpha) lie in the span of the 15 products of divisor classes")
check(rank_of([Re, Im]) == 2, "the two rational Weil classes are independent")

# ---------------- mixed case Y = X^2 x B, B with H^1(B) = H (x) Q^2, dim H = 2
nH = 2
off = nV * 2           # indices of H (x) f_j : off + h + nH*j
ReY, ImY = {}, {}
for S in itertools.product((0, 1), repeat=nV + nH):
    k = sum(S)
    idx = [a + nV * S[a] for a in range(nV)] + [off + h + nH * S[nV + h] for h in range(nH)]
    m, s = sort_sign(tuple(idx))
    if k % 4 == 0:
        ReY[m] = ReY.get(m, 0) + s
    elif k % 4 == 2:
        ReY[m] = ReY.get(m, 0) - s
    elif k % 4 == 1:
        ImY[m] = ImY.get(m, 0) - s
    else:
        ImY[m] = ImY.get(m, 0) + s
ReY = {m: c for m, c in ReY.items() if c}
ImY = {m: c for m, c in ImY.items() if c}
check(all(len(act(X, ReY, nV, 2)) == 0 and len(act(X, ImY, nV, 2)) == 0 for X in sl_basis),
      "mixed Weil classes of Y = X^2 x B (L acting diagonally) are sl(V)-invariant on the V-part")

log("ALL CHECKS PASSED")
