#!/usr/bin/env python3
# Supporting script for item (LXI), code/k3_hodge.py (round 19, (F3') through motives).
"""
Exact sanity checks of the first fundamental theorems used for K3 surfaces.

(SO) For V = Q^t with the standard form, the SO(t)-invariant polynomials on
     V^r of a given multidegree are spanned by monomials in the pairings
     q_ij = <v_i, v_j> when r < t; for r >= t the determinants are needed.
     (Hodge classes of Sym^{b_1}T (x) ... (x) Sym^{b_r}T when the Hodge group
     of T is SO(T), E = Q: the case of symmetric products of a K3 surface.)
(GL) For W = Q^m and GL(m) acting on W (+) W^*, the invariant polynomials on
     r copies of W (+) W^* are spanned by monomials in the pairings
     <w_i, w*_j>.  (E imaginary quadratic: the Hodge group is U(T), whose
     complexification is GL(T_sigma).)
Invariants are computed as the common kernel of the Lie algebra generators
acting by derivations on the space of polynomials of the given multidegree;
everything is exact (python-flint fmpq_mat ranks).
"""
import itertools
import flint
import sympy as sp

def monomials(varblocks, degs):
    """all monomials with degree degs[i] in the variables varblocks[i]."""
    per_block = []
    for vs, d in zip(varblocks, degs):
        per_block.append([sp.Mul(*c) for c in itertools.combinations_with_replacement(vs, d)])
    return [sp.Mul(*p) for p in itertools.product(*per_block)]

def coeff_matrix(polys, basis):
    idx = {m: i for i, m in enumerate(basis)}
    M = [[0]*len(basis) for _ in polys]
    for r, p in enumerate(polys):
        for mon, c in sp.Poly(sp.expand(p), *allvars).terms():
            m = sp.Mul(*[v**e for v, e in zip(allvars, mon)])
            M[r][idx[m]] = sp.Rational(c)
    return M

def rank(M):
    if not M:
        return 0
    A = flint.fmpq_mat(len(M), len(M[0]), [flint.fmpq(int(sp.Rational(x).p), int(sp.Rational(x).q)) for row in M for x in row])
    return A.rank()

def invariant_dim(derivs, basis):
    """dim of common kernel of the derivations on span(basis)."""
    rows = []
    # matrix of all derivations stacked: kernel of the linear map basis -> (images)
    images = []
    for D in derivs:
        images.append([sp.expand(D(b)) for b in basis])
    # build big matrix: columns = basis elements, rows = coefficients of all images
    allmons = set()
    for imgs in images:
        for p in imgs:
            if p != 0:
                for term in sp.Add.make_args(p):
                    c, m = term.as_coeff_Mul()
                    allmons.add(m)
    allmons = sorted(allmons, key=sp.default_sort_key)
    idx = {m: i for i, m in enumerate(allmons)}
    nrows = len(allmons)*len(derivs)
    Mat = [[0]*len(basis) for _ in range(nrows)]
    for k, imgs in enumerate(images):
        for j, p in enumerate(imgs):
            if p == 0:
                continue
            for term in sp.Add.make_args(p):
                c, m = term.as_coeff_Mul()
                Mat[k*len(allmons) + idx[m]][j] += c
    return len(basis) - rank(Mat) if nrows else len(basis)

def span_dim(polys, basis):
    return rank(coeff_matrix(polys, basis))

results = []
# ---------------- SO(t) ----------------
for t, r, degs in [(3, 2, (1, 1)), (3, 2, (2, 2)), (3, 2, (3, 1)), (3, 2, (4, 2)),
                   (3, 3, (1, 1, 1)), (3, 3, (2, 1, 1)), (3, 3, (2, 2, 2)),
                   (4, 3, (1, 1, 2)), (4, 3, (2, 2, 2)), (4, 4, (1, 1, 1, 1)),
                   (5, 4, (1, 1, 1, 1))]:
    X = [[sp.Symbol(f'x{i}_{a}') for a in range(t)] for i in range(r)]
    allvars = [v for row in X for v in row]
    basis = monomials(X, degs)
    derivs = []
    for a in range(t):
        for b in range(a+1, t):
            def D(f, a=a, b=b):
                return sum(X[i][b]*sp.diff(f, X[i][a]) - X[i][a]*sp.diff(f, X[i][b]) for i in range(r))
            derivs.append(D)
    inv = invariant_dim(derivs, basis)
    # pairing monomials of this multidegree
    q = {(i, j): sum(X[i][a]*X[j][a] for a in range(t)) for i in range(r) for j in range(i, r)}
    pair_polys = []
    keys = list(q.keys())
    # enumerate exponent vectors e_{ij} with sum_j e_ij (+2 e_ii) = degs[i]
    def rec(k, cur, remaining):
        if k == len(keys):
            if all(x == 0 for x in remaining):
                pair_polys.append(sp.Mul(*[q[keys[s]]**cur[s] for s in range(len(keys))]))
            return
        i, j = keys[k]
        for e in range(0, 5):
            need = [0]*r
            if i == j:
                need[i] = 2*e
            else:
                need[i] = e; need[j] = e
            if all(need[s] <= remaining[s] for s in range(r)):
                rec(k+1, cur+[e], [remaining[s]-need[s] for s in range(r)])
    rec(0, [], list(degs))
    pd = span_dim(pair_polys, basis) if pair_polys else 0
    # determinants (only if r >= t): det of t of the vectors, times pairings
    det_note = ""
    if r >= t:
        extra = []
        for I in itertools.combinations(range(r), t):
            D_ = sp.Matrix([X[i] for i in I]).det()
            rem = list(degs)
            for i in I:
                rem[i] -= 1
            if min(rem) < 0:
                continue
            # multiply by pairing monomials of the remaining multidegree
            sub = []
            def rec2(k, cur, remaining):
                if k == len(keys):
                    if all(x == 0 for x in remaining):
                        sub.append(sp.Mul(*[q[keys[s]]**cur[s] for s in range(len(keys))]))
                    return
                i2, j2 = keys[k]
                for e in range(0, 5):
                    need = [0]*r
                    if i2 == j2:
                        need[i2] = 2*e
                    else:
                        need[i2] = e; need[j2] = e
                    if all(need[s] <= remaining[s] for s in range(r)):
                        rec2(k+1, cur+[e], [remaining[s]-need[s] for s in range(r)])
            rec2(0, [], rem)
            extra += [D_*s for s in sub]
        pd_det = span_dim(pair_polys + extra, basis)
        det_note = f", pairings+dets span {pd_det}"
        ok = (pd_det == inv)
    else:
        ok = (pd == inv)
    results.append(ok)
    print(f"SO({t}) on V^{r}, multidegree {degs}: invariants {inv}, pairing monomials span {pd}{det_note}"
          f"  -> {'r<t: pairings suffice' if r < t else 'r>=t'}  {'OK' if ok else 'FAIL'}")

# ---------------- GL(m) on W + W^* ----------------
for m, r, degs in [(2, 2, (1, 1, 1, 1)), (2, 2, (2, 1, 1, 2)), (3, 2, (1, 1, 1, 1)), (2, 3, (1, 1, 1, 1, 1, 1))]:
    # r copies of W (vars w) and r copies of W^* (vars u); degs = (deg w_1..w_r, deg u_1..u_r)
    Wv = [[sp.Symbol(f'w{i}_{a}') for a in range(m)] for i in range(r)]
    Uv = [[sp.Symbol(f'u{i}_{a}') for a in range(m)] for i in range(r)]
    allvars = [v for row in Wv for v in row] + [v for row in Uv for v in row]
    basis = monomials(Wv + Uv, degs)
    derivs = []
    for a in range(m):
        for b in range(m):
            # E_ab acts on W by w_a -> w_b coordinates, and on W^* by -transpose
            def D(f, a=a, b=b):
                return sum(Wv[i][b]*sp.diff(f, Wv[i][a]) - Uv[i][a]*sp.diff(f, Uv[i][b]) for i in range(r))
            derivs.append(D)
    inv = invariant_dim(derivs, basis)
    pairs = {(i, j): sum(Wv[i][a]*Uv[j][a] for a in range(m)) for i in range(r) for j in range(r)}
    keys = list(pairs.keys())
    polys = []
    def rec3(k, cur, remw, remu):
        if k == len(keys):
            if all(x == 0 for x in remw) and all(x == 0 for x in remu):
                polys.append(sp.Mul(*[pairs[keys[s]]**cur[s] for s in range(len(keys))]))
            return
        i, j = keys[k]
        for e in range(0, 4):
            if remw[i] >= e and remu[j] >= e:
                rw = list(remw); ru = list(remu); rw[i] -= e; ru[j] -= e
                rec3(k+1, cur+[e], rw, ru)
    rec3(0, [], list(degs[:r]), list(degs[r:]))
    pd = span_dim(polys, basis) if polys else 0
    ok = (pd == inv)
    results.append(ok)
    print(f"GL({m}) on (W+W*)^{r}, degrees {degs}: invariants {inv}, pairing monomials span {pd}  {'OK' if ok else 'FAIL'}")

print("ALL OK" if all(results) else "SOME FAILED")
