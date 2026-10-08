#!/usr/bin/env python3
"""
invariants.py  (attack13/A4)

Exact checks of the invariant theory used in Theorems B and D of the report.

(1) SO(t), t = 3..8: dim (V^{(x)j})^{SO(t)} by the Weyl-character identity
      mult of the trivial rep in M = sum_{w in W} eps(w) dim M_{rho - w rho},
    with the weight multiplicities of V^{(x)j} computed by convolution, all in
    integers; and dim of the span of the pairing tensors (= O(t)-invariants,
    by the first fundamental theorem for O) as the rank of the Brauer Gram
    matrix <M1,M2> = t^{#loops(M1 u M2)} over perfect matchings.  The
    difference is the number of invariants that are not O(t)-invariant: it
    must be 0 for j < t and 1 at j = t (the determinant).

(2) Explicit linear algebra (exact, over Q via python-flint) for SO(3), SO(4),
    SO(5) and Sp(4), Sp(6) in V^{(x)j}, j <= 6: the invariants are the
    zero-weight vectors killed by the simple root vectors; the determinant
    tensor is invariant and changes sign under a reflection; for Sp the
    pairing tensors span the invariants (no determinant-type invariant).
"""
from itertools import permutations, product
from fractions import Fraction
import flint

npass = nfail = 0


def check(name, ok, detail=""):
    global npass, nfail
    npass += bool(ok)
    nfail += (not ok)
    print(("[PASS] " if ok else "[FAIL] ") + name + ("  " + detail if detail else ""))


# ------------------------------------------------------------ Weyl formula
def weyl_group_orth(t):
    """signed permutations for B_h (t=2h+1) or even sign changes for D_h"""
    h = t // 2
    out = []
    for perm in permutations(range(h)):
        # sign of permutation
        sgn = 1
        p = list(perm)
        for i in range(h):
            for j in range(i + 1, h):
                if p[i] > p[j]:
                    sgn = -sgn
        for signs in product([1, -1], repeat=h):
            if t % 2 == 0 and signs.count(-1) % 2 == 1:
                continue
            # det of signed permutation matrix, which is eps(w) on the
            # reflection representation
            eps = sgn
            for s in signs:
                eps *= s
            out.append((perm, signs, eps))
    return out


def rho_orth(t):
    h = t // 2
    if t % 2 == 1:
        return [Fraction(2 * (h - i) - 1, 2) for i in range(h)]
    return [Fraction(h - 1 - i) for i in range(h)]


def weights_V(t):
    h = t // 2
    ws = []
    for i in range(h):
        e = [0] * h
        e[i] = 1
        ws.append(tuple(e))
        e = [0] * h
        e[i] = -1
        ws.append(tuple(e))
    if t % 2 == 1:
        ws.append(tuple([0] * h))
    return ws


def tensor_weight_mults(t, j):
    mults = {tuple([0] * (t // 2)): 1}
    wv = weights_V(t)
    for _ in range(j):
        new = {}
        for w, m in mults.items():
            for u in wv:
                k = tuple(a + b for a, b in zip(w, u))
                new[k] = new.get(k, 0) + m
        mults = new
    return mults


def so_invariants(t, j):
    rho = rho_orth(t)
    mults = tensor_weight_mults(t, j)
    tot = 0
    for perm, signs, eps in weyl_group_orth(t):
        wrho = [signs[i] * rho[perm[i]] for i in range(len(rho))]
        mu = tuple(rho[i] - wrho[i] for i in range(len(rho)))
        if all(x.denominator == 1 for x in mu):
            key = tuple(int(x) for x in mu)
            tot += eps * mults.get(key, 0)
    return tot


def matchings(points):
    if not points:
        yield []
        return
    a = points[0]
    for k in range(1, len(points)):
        b = points[k]
        rest = points[1:k] + points[k + 1:]
        for m in matchings(rest):
            yield [(a, b)] + m


def loops(m1, m2, n):
    adj = {i: [] for i in range(n)}
    for a, b in m1 + m2:
        adj[a].append(b)
        adj[b].append(a)
    seen, c = set(), 0
    for s in range(n):
        if s in seen:
            continue
        c += 1
        stack = [s]
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack.extend(adj[x])
    return c


def o_invariants(t, j):
    if j % 2 == 1:
        return 0
    ms = list(matchings(list(range(j))))
    G = flint.fmpz_mat(len(ms), len(ms),
                       [t ** loops(a, b, j) for a in ms for b in ms])
    return G.rank()


print("(1) SO(t) versus O(t) invariants in V^{(x)j}")
for t in range(3, 9):
    row = []
    ok_below, at_t = True, None
    for j in range(0, t + 3):
        s = so_invariants(t, j)
        o = o_invariants(t, j)
        row.append((j, s, o, s - o))
        if j < t and s != o:
            ok_below = False
        if j == t:
            at_t = s - o
    print("  t=%d  (j, SO, O, SO-O):" % t, row)
    check("t=%d: no non-O(t) invariant below j=t, exactly one at j=t" % t,
          ok_below and at_t == 1)

# ------------------------------------------------------------ explicit check
def basis_orth(t):
    h = t // 2
    names = []
    for i in range(h):
        names += [("e", i), ("f", i)]
    if t % 2:
        names.append(("z", 0))
    return names


def q_orth(a, b):
    if a[0] == "e" and b[0] == "f" and a[1] == b[1]:
        return 1
    if a[0] == "f" and b[0] == "e" and a[1] == b[1]:
        return 1
    if a[0] == "z" and b[0] == "z":
        return 1
    return 0


def wedge_op(u, v, form, names):
    """x -> form(v,x) u - form(u,x) v  as dict x -> list of (coef, y)"""
    op = {}
    for x in names:
        terms = []
        c1 = form(v, x)
        if c1:
            terms.append((c1, u))
        c2 = form(u, x)
        if c2:
            terms.append((-c2, v))
        op[x] = terms
    return op


def sym_op(u, v, form, names):
    op = {}
    for x in names:
        terms = []
        c1 = form(u, x)
        if c1:
            terms.append((c1, v))
        c2 = form(v, x)
        if c2:
            terms.append((c2, u))
        op[x] = terms
    return op


def weight(b, h):
    w = [0] * h
    if b[0] == "e":
        w[b[1]] += 1
    elif b[0] == "f":
        w[b[1]] -= 1
    return w


def zero_weight_words(names, h, j):
    out = []
    for word in product(names, repeat=j):
        w = [0] * h
        for b in word:
            for i, x in enumerate(weight(b, h)):
                w[i] += x
        if all(x == 0 for x in w):
            out.append(word)
    return out


def apply_op(op, vec):
    """vec: dict word -> coef; op acts as derivation on tensors"""
    res = {}
    for word, c in vec.items():
        for pos, x in enumerate(word):
            for coef, y in op[x]:
                nw = word[:pos] + (y,) + word[pos + 1:]
                res[nw] = res.get(nw, 0) + c * coef
    return {k: v for k, v in res.items() if v}


def invariant_space(names, h, j, ops):
    Z = zero_weight_words(names, h, j)
    idx = {w: i for i, w in enumerate(Z)}
    rows = {}
    cols = len(Z)
    # build matrix of all ops restricted to zero-weight space
    entries = []
    rowkeys = {}
    for k, op in enumerate(ops):
        for ci, w in enumerate(Z):
            out = apply_op(op, {w: 1})
            for nw, c in out.items():
                rk = (k, nw)
                if rk not in rowkeys:
                    rowkeys[rk] = len(rowkeys)
                entries.append((rowkeys[rk], ci, c))
    acc = {}
    for r, ci, c in entries:
        acc[(r, ci)] = acc.get((r, ci), 0) + c
    M = flint.fmpz_mat(max(1, len(rowkeys)), cols)
    for (r, ci), c in acc.items():
        M[r, ci] = c
    K, nul = M.nullspace()
    rank = M.rank()
    dimker = cols - rank
    basis = []
    for c in range(K.ncols()):
        v = [K[r, c] for r in range(K.nrows())]
        if any(x != 0 for x in v):
            basis.append(v)
    assert len(basis) == dimker == nul
    return Z, idx, dimker, basis


def orth_simple_ops(t):
    names = basis_orth(t)
    h = t // 2
    ops = []
    for i in range(h - 1):
        ops.append(wedge_op(("e", i), ("f", i + 1), q_orth, names))
    if t % 2:
        ops.append(wedge_op(("e", h - 1), ("z", 0), q_orth, names))
    else:
        ops.append(wedge_op(("e", h - 2), ("e", h - 1), q_orth, names))
    return names, h, ops


def perm_sign(p):
    s = 1
    p = list(p)
    for i in range(len(p)):
        for k in range(i + 1, len(p)):
            if p[i] > p[k]:
                s = -s
    return s


def det_tensor(names):
    vec = {}
    for p in permutations(range(len(names))):
        word = tuple(names[i] for i in p)
        vec[word] = vec.get(word, 0) + perm_sign(p)
    return vec


def reflect_e0f0(vec):
    sw = {("e", 0): ("f", 0), ("f", 0): ("e", 0)}
    out = {}
    for word, c in vec.items():
        nw = tuple(sw.get(b, b) for b in word)
        out[nw] = out.get(nw, 0) + c
    return out


print()
print("(2) explicit invariants, SO(t) for t = 3,4,5")
for t in (3, 4, 5):
    names, h, ops = orth_simple_ops(t)
    # the operators must preserve q: check on basis
    okq = True
    for op in ops:
        for a in names:
            for b in names:
                s = 0
                for c, y in op[a]:
                    s += c * q_orth(y, b)
                for c, y in op[b]:
                    s += c * q_orth(a, y)
                if s != 0:
                    okq = False
    check("t=%d: the simple root vectors lie in so(q)" % t, okq)
    D = det_tensor(names)
    killed = all(not apply_op(op, D) for op in ops)
    anti = reflect_e0f0(D) == {k: -v for k, v in D.items()}
    check("t=%d: det tensor is so(q)-invariant and odd under the reflection "
          "e0<->f0" % t, killed and anti)
    for j in range(0, min(6, t + 2) + 1):
        Z, idx, dk, basis = invariant_space(names, h, j, ops)
        # reflection eigenvalues on the invariant space
        minus = 0
        if dk:
            # matrix of reflection on the kernel basis
            B = flint.fmpq_mat(len(Z), dk)
            for c, v in enumerate(basis):
                for r, x in enumerate(v):
                    B[r, c] = x
            RB = flint.fmpq_mat(len(Z), dk)
            for c, v in enumerate(basis):
                vec = {Z[r]: v[r] for r in range(len(Z)) if v[r] != 0}
                rv = reflect_e0f0(vec)
                for w, x in rv.items():
                    RB[idx[w], c] = x
            # dimension of (-1)-eigenspace = dk - rank(B + RB)/... compute
            S = B + RB
            plus = S.rank()
            minus = dk - plus
        weyl = so_invariants(t, j)
        check("t=%d j=%d: explicit dim %d = Weyl count %d; reflection-odd part %d"
              % (t, j, dk, weyl, minus),
              dk == weyl and (minus == (1 if j == t else 0) or j > t))

print()
print("(3) Sp(2h): the pairing tensors span the invariants (no det-type class)")


def basis_symp(h):
    names = []
    for i in range(h):
        names += [("e", i), ("f", i)]
    return names


def w_symp(a, b):
    if a[0] == "e" and b[0] == "f" and a[1] == b[1]:
        return 1
    if a[0] == "f" and b[0] == "e" and a[1] == b[1]:
        return -1
    return 0


def symp_simple_ops(h):
    names = basis_symp(h)
    ops = []
    for i in range(h - 1):
        ops.append(sym_op(("e", i), ("f", i + 1), w_symp, names))
    ops.append(sym_op(("e", h - 1), ("e", h - 1), w_symp, names))
    return names, ops


def pairing_tensor(match, names, j, form_inv):
    vec = {(): 1}
    # build full tensor as sum over assignments
    words = {}
    pairs = match
    for choice in product(form_inv, repeat=len(pairs)):
        word = [None] * j
        c = 1
        for (a, b), (x, y, coef) in zip(pairs, choice):
            word[a] = x
            word[b] = y
            c *= coef
        words[tuple(word)] = words.get(tuple(word), 0) + c
    return {k: v for k, v in words.items() if v}


for h in (2, 3):
    names, ops = symp_simple_ops(h)
    oksp = True
    for op in ops:
        for a in names:
            for b in names:
                s = 0
                for c, y in op[a]:
                    s += c * w_symp(y, b)
                for c, y in op[b]:
                    s += c * w_symp(a, y)
                if s != 0:
                    oksp = False
    check("h=%d: the simple root vectors lie in sp(omega)" % h, oksp)
    # inverse form tensor Omega = sum e_i (x) f_i - f_i (x) e_i
    form_inv = []
    for i in range(h):
        form_inv.append((("e", i), ("f", i), 1))
        form_inv.append((("f", i), ("e", i), -1))
    for j in range(0, 7):
        Z, idx, dk, basis = invariant_space(names, h, j, ops)
        if j % 2 == 1:
            check("h=%d j=%d: no invariants in odd degree" % (h, j), dk == 0)
            continue
        ms = list(matchings(list(range(j))))
        vecs = [pairing_tensor(m, names, j, form_inv) for m in ms]
        allinv = all(not apply_op(op, v) for op in ops for v in vecs)
        M = flint.fmpq_mat(len(Z), max(1, len(vecs)))
        for c, v in enumerate(vecs):
            for w, x in v.items():
                M[idx[w], c] = x
        r = M.rank() if vecs else 0
        check("h=%d j=%d: %d invariants, pairing tensors invariant and of rank %d"
              % (h, j, dk, r), allinv and r == dk)

print("%d checks passed, %d failed" % (npass, nfail))
