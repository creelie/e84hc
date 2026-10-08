#!/usr/bin/env python3
"""
blocks_check.py  (attack13/A4)

Theorem E of the report (Hodge classes on powers are spanned by products of
pull-backs of Hodge classes on bounded powers) in the orthogonal case, checked
by exact linear algebra: in V^{(x)j} for SO(t), the invariants are spanned by
the products over set partitions of {1..j} into blocks of size 2 (pairings q)
and at most one block of size t (the determinant).  Checked for
(t, j) = (3, 5), (4, 6), (3, 6), (5, 7).
"""
import sys
from itertools import combinations, permutations, product
import flint
sys.path.insert(0, ".")
import importlib.util
spec = importlib.util.spec_from_file_location("inv", "invariants.py")
# import helpers without running the module's checks: exec selected defs
src = open("invariants.py").read()
cut = src.index('print("(1) SO(t) versus O(t)')
defs = src[:cut]
start2 = src.index("# ------------------------------------------------------------ explicit check")
end2 = src.index('print()\nprint("(2) explicit invariants')
ns = {}
exec(defs, ns)
exec(src[start2:end2], ns)

npass = nfail = 0
def check(name, ok, detail=""):
    global npass, nfail
    npass += bool(ok); nfail += (not ok)
    print(("[PASS] " if ok else "[FAIL] ") + name + ("  " + detail if detail else ""))

def q_tensor(names):
    out = []
    for a in names:
        for b in names:
            c = ns["q_orth"](a, b)
            if c:
                # inverse of q: for the split form q^{-1} has the same matrix
                out.append((a, b, c))
    return out

def product_tensor(blocks, j, names, D):
    """blocks: list of tuples of positions; size 2 -> q^{-1}, size t -> det"""
    parts = []
    qt = q_tensor(names)
    for B in blocks:
        if len(B) == 2:
            parts.append([((B[0], a), (B[1], b), c) for a, b, c in qt])
        else:
            parts.append(("det", B))
    vec = {}
    # expand
    def rec(i, word, coef):
        if i == len(parts):
            w = tuple(word[k] for k in range(j))
            vec[w] = vec.get(w, 0) + coef
            return
        P = parts[i]
        if isinstance(P, tuple) and P[0] == "det":
            B = P[1]
            for perm, c in D:
                for pos, b in zip(B, perm):
                    word[pos] = b
                rec(i + 1, word, coef * c)
        else:
            for (p1, a), (p2, b), c in P:
                word[p1] = a; word[p2] = b
                rec(i + 1, word, coef * c)
    rec(0, {}, 1)
    return {k: v for k, v in vec.items() if v}

def set_partitions_blocks(elems, t):
    """partitions of elems into blocks of size 2 and at most one of size t"""
    elems = list(elems)
    res = []
    def pairings(rest):
        if not rest:
            yield []
            return
        a = rest[0]
        for k in range(1, len(rest)):
            for m in pairings(rest[1:k] + rest[k+1:]):
                yield [(a, rest[k])] + m
    for m in pairings(elems):
        res.append(m)
    if len(elems) >= t:
        for B in combinations(elems, t):
            rest = [e for e in elems if e not in B]
            for m in pairings(rest):
                res.append([B] + m)
    return res

for t, j in [(3, 5), (3, 6), (4, 6), (5, 7)]:
    names, h, ops = ns["orth_simple_ops"](t)
    Z, idx, dk, basis = ns["invariant_space"](names, h, j, ops)
    D = []
    for p in permutations(range(t)):
        D.append((tuple(names[i] for i in p), ns["perm_sign"](p)))
    parts = set_partitions_blocks(list(range(j)), t)
    vecs = [product_tensor(bl, j, names, D) for bl in parts]
    allinv = all(not ns["apply_op"](op, v) for op in ops for v in vecs)
    M = flint.fmpz_mat(len(Z), len(vecs))
    for c, v in enumerate(vecs):
        for w, x in v.items():
            M[idx[w], c] = x
    r = M.rank()
    check("SO(%d), V^(x)%d: %d invariants; %d block products (pairs + <=1 det), all invariant, rank %d"
          % (t, j, dk, len(vecs), r), allinv and r == dk)
print("%d checks passed, %d failed" % (npass, nfail))
