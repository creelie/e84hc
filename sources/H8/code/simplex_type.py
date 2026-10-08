#!/usr/bin/env python3
"""
simplex_type.py

Item (LXVII) of the computations: hypersurfaces of simplex type, and the
smooth Delsarte hypersurfaces of every dimension.

A Laurent polynomial f = sum_{i=0}^{k} c_i chi^{u_i} on a torus with character
lattice M is of simplex type when the exponents u_i are affinely independent.
With L' the lattice spanned by the u_i - u_0 and L its saturation, e(f) is the
exponent of L/L'.  The isogeny dual to M c (1/e) L' (+ a complement) turns f
into c_0 + sum c_i z_i^e, and the paper shows that the closure of {f = 0} in
a projective toric variety, when smooth, lies in the class A of varieties
whose cohomology comes from abelian varieties, with Fermat varieties of
degree e as the only input.  For a Delsarte hypersurface X_A = {sum_i x^{a_i}
= 0} in P^{r+1} the lattice is M = {x in Z^{r+2} : sum x = 0} and L' is
spanned by the differences of the rows of A.

What is checked:

  (A) for the 29 sextic shapes of item (LXVI): the invariant factors of
      M / L' by the Smith normal form, the exponent e, and that e R^{-1} is
      integral and (e/p) R^{-1} is not for each prime p | e (R the matrix of
      the a_i - a_0); e divides the least d with d A^{-1} integral and equals
      it except for the chain C6 (e = 3125, d = 18750) and the loop L6
      (e = 2604, d = 15624); the index [M : L'] is |det A| / 6; e is 6 for
      the Fermat sextic, 24 or 30 for six shapes, and between 120 and 3750
      for the other twenty-two;

  (B) the Klein quartic x^3 y + y^3 z + z^3 x: det A = 28, [M : L'] = 7,
      e = 7, the kernel of the isogeny has order e^2 / 7 = 7, and its
      invariant holomorphic forms on the Fermat septic number 3, the genus:
      the classical presentation of the Klein quartic as a quotient of the
      Fermat septic by a group of order seven;

  (C) the Euler number through the orbits of P^{r+1}: on the orbit where the
      coordinates outside S vanish, X_A meets the torus in the zero set of the
      rows of A supported on S, of simplex type, whose Euler number is
      (-1)^{|S|} |det A_{R,S}| / m when there are |S| such rows, 1 on a
      coordinate point with no such row, and 0 otherwise (the lemma of the
      paper: an etale cover of degree [M_S : L'_S] of the complement of |S|
      general hyperplanes in P^{|S|-2}, times a torus).  The sum equals the
      Euler number ((1-m)^{r+2} - 1)/m + r + 2 of a smooth hypersurface of
      degree m, for the 29 sextic fourfolds and for the chains and loops of
      every length completed by Fermat terms in 3 to 6 variables and degrees
      3 to 8;

  (D) holomorphic forms: the characters of the Fermat variety of degree e
      trivial on the kernel K of the isogeny form the image of M in
      M~/eM~ = {alpha in (Z/e)^{r+2} : sum alpha = 0}, namely the
      e m A^{-1} mod e; those with every entry nonzero and entries (in
      1..e-1) summing to e number h^{r,0}(X_A) = binom(m-1, r+1), for the 29
      sextic shapes and for the chains and loops in 3 to 5 variables and
      degrees 3 to 7;

  (E) the same count for smooth cyclic covers y^k = F_A(x) in
      P(1, ..., 1, m/k), with the lattice {x : sum_j q_j x_j = 0} of the
      weighted torus: it equals the geometric genus
      sum_j binom(m (k-1-j)/k - 1, N - 1) of the cover, for the chains and
      loops in five variables of degrees 8 and 10 and every k | m, k >= 2,
      with a nonzero genus;

  (F) nondegeneracy: for random polynomials of simplex type in two and three
      variables, with random affinely independent exponents and random
      rational coefficients, the equations f = x_i df/dx_i = 0 have no
      solution on the torus (a Groebner basis equal to 1 after inverting the
      coordinates); a polynomial with five terms in two variables, singular
      at (1, 1), is correctly detected;

  (G) the smooth adapted fan of the Klein quartic in the plane: the rays of
      P^2, the inner normals of the Newton triangle and the rays inserted to
      make every cone unimodular; every cone lies in the normal cone of a
      vertex; the closure meets exactly the three divisors of the edges, in
      one point each (the lattice length of the edge); and the Euler number
      -7 + 3 = -4 = 2 - 2g gives the genus 3.

Everything is exact integer or rational arithmetic.

Run:  python3 simplex_type.py
"""
import itertools
import math
import random
from fractions import Fraction

import sympy
from sympy.matrices.normalforms import smith_normal_form

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("  (" + detail + ")") if detail else ""))


# ---------------------------------------------------------------- shapes

def kinds(total):
    return [("F", 1)] + [(t, k) for k in range(2, total + 1) for t in "CL"]


def multisets(total, ks, start=0):
    if total == 0:
        yield []
        return
    for i in range(start, len(ks)):
        t, k = ks[i]
        if k <= total:
            for rest in multisets(total - k, ks, i):
                yield [ks[i]] + rest


def shape_matrix(shape, m):
    """the exponent matrix of a sum of Fermat terms, chains and loops."""
    nv = sum(k for _, k in shape)
    rows = []
    pos = 0
    for t, k in shape:
        v = list(range(pos, pos + k))
        pos += k
        if t == "F":
            rows.append({v[0]: m})
        elif t == "C":
            for a in range(k - 1):
                rows.append({v[a]: m - 1, v[a + 1]: 1})
            rows.append({v[-1]: m})
        else:
            for a in range(k):
                rows.append({v[a]: m - 1, v[(a + 1) % k]: 1})
    return [[r.get(j, 0) for j in range(nv)] for r in rows]


def name(shape):
    return "".join(t + str(k) for t, k in shape)


def one_block(t, k, nv):
    return [(t, k)] + [("F", 1)] * (nv - k)


# ---------------------------------------------------------------- lattices

def lattice_basis(q):
    """a basis of {x in Z^N : sum_j q_j x_j = 0} for q = (1, ..., 1, w)."""
    N = len(q)
    assert all(x == 1 for x in q[:-1])
    basis = []
    for j in range(1, N - 1):
        v = [0] * N
        v[0], v[j] = -1, 1
        basis.append(v)
    v = [0] * N
    v[0], v[N - 1] = -q[N - 1], 1
    basis.append(v)
    return basis


def coords(vec, q):
    """coordinates of vec in lattice_basis(q) (entries 1..N-1 of vec)."""
    return list(vec[1:])


def invariants(U, q):
    """invariant factors, index and exponent of M / L', L' spanned by the
    differences of the rows of U, M = {sum q_j x_j = 0}."""
    N = len(U)
    R = [coords([U[i][j] - U[0][j] for j in range(N)], q) for i in
         range(1, N)]
    S = smith_normal_form(sympy.Matrix(R), domain=sympy.ZZ)
    inv = [abs(int(S[i, i])) for i in range(N - 1)]
    e = 1
    for x in inv:
        e = math.lcm(e, x)
    return inv, math.prod(inv), e, sympy.Matrix(R)


def exponent_direct(R, e):
    """e R^{-1} integral and (e/p) R^{-1} not, for each prime p | e."""
    Rinv = R.inv()
    ok = all((e * x).is_integer for x in Rinv)
    for p in sympy.primefactors(e):
        ok &= not all(((e // p) * x).is_integer for x in Rinv)
    return ok


def least_d(A):
    Ainv = sympy.Matrix(A).inv()
    d = 1
    for x in Ainv:
        d = math.lcm(d, int(sympy.fraction(x)[1]))
    return d


# ---------------------------------------------------------------- (C)

def euler_strata(A, m):
    N = len(A)
    total = Fraction(0)
    for s in range(1, N + 1):
        for S in itertools.combinations(range(N), s):
            Sset = set(S)
            rows = [i for i in range(N)
                    if all(A[i][j] == 0 for j in range(N) if j not in Sset)]
            if s == 1:
                total += 1 if not rows else 0
            elif len(rows) == s:
                sub = sympy.Matrix([[A[i][j] for j in S] for i in rows])
                total += Fraction((-1) ** s * abs(int(sub.det())), m)
    return total


def euler_hypersurface(N, m):
    return Fraction((1 - m) ** N - 1, m) + N


# ---------------------------------------------------------------- (D), (E)

def invariant_characters(U, q, e):
    """the subgroup of (Z/e)^N image of M = {sum q_j x_j = 0} under
    x -> e x U^{-1} mod e."""
    Uinv = sympy.Matrix(U).inv()
    gens = []
    for b in lattice_basis(q):
        lam = sympy.Matrix([b]) * Uinv
        g = tuple(int((e * x) % e) for x in lam)
        assert all((e * x).is_integer for x in lam)
        gens.append(g)
    N = len(U)
    seen = {tuple([0] * N)}
    frontier = [tuple([0] * N)]
    while frontier:
        new = []
        for a in frontier:
            for g in gens:
                b = tuple((x + y) % e for x, y in zip(a, g))
                if b not in seen:
                    seen.add(b)
                    new.append(b)
        frontier = new
    return seen


def top_forms(H, e):
    return sum(1 for a in H if all(a) and sum(a) == e)


def cyclic_pg(N, m, k):
    total = 0
    for j in range(k):
        t = m * (k - 1 - j) // k - N
        if t >= 0:
            total += math.comb(t + N - 1, N - 1)
    return total


# ---------------------------------------------------------------- (F)

def nondegenerate(expos, coeffs, xs):
    t = sympy.Symbol("t")
    f = sum(c * sympy.Mul(*[x ** a for x, a in zip(xs, u)])
            for c, u in zip(coeffs, expos))
    eqs = [f] + [sympy.expand(x * sympy.diff(f, x)) for x in xs]
    eqs.append(1 - t * sympy.Mul(*xs))
    G = sympy.groebner(eqs, *xs, t, order="grevlex", domain=sympy.QQ)
    return G.exprs == [1]


def affinely_independent(expos):
    M = sympy.Matrix([[1] + list(u) for u in expos])
    return M.rank() == len(expos)


# ---------------------------------------------------------------- (G)

def det2(v, w):
    return v[0] * w[1] - v[1] * w[0]


def angle_key(v):
    return math.atan2(v[1], v[0]) % (2 * math.pi)


def primitive(v):
    g = math.gcd(abs(v[0]), abs(v[1]))
    return (v[0] // g, v[1] // g)


def inner_normals(vertices):
    """inner normals of the edges of a lattice triangle."""
    out = []
    for i in range(3):
        a, b, c = vertices[i], vertices[(i + 1) % 3], vertices[(i + 2) % 3]
        d = (b[0] - a[0], b[1] - a[1])
        n = primitive((-d[1], d[0]))
        if n[0] * (c[0] - a[0]) + n[1] * (c[1] - a[1]) < 0:
            n = (-n[0], -n[1])
        out.append(n)
    return out


def smooth_refinement(rays):
    rays = sorted(set(rays), key=angle_key)
    changed = True
    while changed:
        changed = False
        for i in range(len(rays)):
            v, w = rays[i], rays[(i + 1) % len(rays)]
            if det2(v, w) > 1:
                best = None
                for a in range(-30, 31):
                    for b in range(-30, 31):
                        u = (a, b)
                        if math.gcd(a, b) != 1:
                            continue
                        if det2(v, u) == 1 and det2(u, w) > 0:
                            if best is None or a * a + b * b < \
                                    best[0] ** 2 + best[1] ** 2:
                                best = u
                rays.append(best)
                rays = sorted(set(rays), key=angle_key)
                changed = True
                break
    return rays


def main():
    shapes = list(multisets(6, kinds(6)))

    print("(A) the lattice degree e of the 29 sextic shapes")
    ok_direct = True
    table = []
    for sh in shapes:
        A = shape_matrix(sh, 6)
        inv, index, e, R = invariants(A, [1] * 6)
        d = least_d(A)
        det = abs(int(sympy.Matrix(A).det()))
        ok_direct &= exponent_direct(R, e) and index * 6 == det
        table.append((name(sh), e, d, index))
    check("for each of the 29: e R^{-1} integral, (e/p) R^{-1} not for "
          "p | e, and [M : L'] = |det A| / 6", ok_direct and len(table) == 29)
    diff = sorted((n, e, d) for n, e, d, _ in table if e != d)
    check("e divides the least d with d A^{-1} integral, with equality "
          "except C6 (3125 against 18750) and L6 (2604 against 15624)",
          all(d % e == 0 for _, e, d, _ in table)
          and diff == [("C6", 3125, 18750), ("L6", 2604, 15624)])
    es = sorted(e for _, e, _, _ in table)
    small = sorted(n for n, e, _, _ in table if e in (24, 30))
    check("e = 6 for the Fermat sextic, 24 or 30 for six shapes, and from "
          "120 to 3750 for the other twenty-two",
          es[0] == 6 and es.count(6) == 1 and len(small) == 6
          and min(e for e in es if e > 30) == 120 and max(es) == 3750
          and all(e in (6, 24, 30) or 120 <= e <= 3750 for e in es),
          "e = 24 or 30: " + ", ".join(small))

    print("(B) the Klein quartic")
    K4 = [[3, 1, 0], [0, 3, 1], [1, 0, 3]]
    inv, index, e, R = invariants(K4, [1, 1, 1])
    H = invariant_characters(K4, [1, 1, 1], e)
    check("x^3y + y^3z + z^3x: det 28, [M : L'] = 7, e = 7, kernel of order "
          "e^2/7 = 7, and 3 invariant holomorphic forms on the Fermat septic",
          abs(sympy.Matrix(K4).det()) == 28 and index == 7 and e == 7
          and len(H) == 7 and e ** 2 // index == 7 and top_forms(H, e) == 3)

    print("(C) Euler numbers through the orbits")
    ok = all(euler_strata(shape_matrix(sh, 6), 6) == euler_hypersurface(6, 6)
             for sh in shapes)
    check("for the 29 sextic fourfolds the orbit sum is 2610, the Euler "
          "number of a smooth sextic fourfold", ok
          and euler_hypersurface(6, 6) == 2610)
    ok = True
    ntest = 0
    for nv in range(3, 7):
        for m in range(3, 9):
            for k in range(2, nv + 1):
                for t in "CL":
                    A = shape_matrix(one_block(t, k, nv), m)
                    ok &= euler_strata(A, m) == euler_hypersurface(nv, m)
                    ntest += 1
    check("the chains and loops of every length, completed by Fermat terms, "
          "in 3 to 6 variables and degrees 3 to 8", ok,
          "%d hypersurfaces" % ntest)

    print("(D) holomorphic forms from the Fermat variety of degree e")
    ok = True
    for sh in shapes:
        A = shape_matrix(sh, 6)
        _, _, e, _ = invariants(A, [1] * 6)
        H = invariant_characters(A, [1] * 6, e)
        _, index, _, _ = invariants(A, [1] * 6)
        ok &= len(H) == index and top_forms(H, e) == 1
    check("for the 29 sextic shapes the invariant characters form a group "
          "of order [M : L'] and exactly one has type (4,0): h^{4,0} = 1", ok)
    ok = True
    ntest = 0
    for nv in range(3, 6):
        for m in range(3, 8):
            for k in range(2, nv + 1):
                for t in "CL":
                    A = shape_matrix(one_block(t, k, nv), m)
                    _, index, e, _ = invariants(A, [1] * nv)
                    H = invariant_characters(A, [1] * nv, e)
                    ok &= len(H) == index
                    ok &= top_forms(H, e) == math.comb(m - 1, nv - 1)
                    ntest += 1
    check("the chains and loops in 3 to 5 variables and degrees 3 to 7: "
          "the invariant characters of top type number binom(m-1, r+1)",
          ok, "%d hypersurfaces" % ntest)

    print("(E) cyclic covers y^k = F_A(x)")
    ok = True
    ntest = 0
    for m in (8, 10):
        for kk in [x for x in range(2, m + 1) if m % x == 0]:
            pg = cyclic_pg(5, m, kk)
            if pg == 0:
                continue
            for k in range(2, 6):
                for t in "CL":
                    A = shape_matrix(one_block(t, k, 5), m)
                    U = [row + [0] for row in A] + [[0] * 5 + [kk]]
                    q = [1] * 5 + [m // kk]
                    _, index, e, _ = invariants(U, q)
                    H = invariant_characters(U, q, e)
                    ok &= len(H) == index and top_forms(H, e) == pg
                    ntest += 1
    check("the invariant characters of top type number the geometric genus "
          "of the cover, for chains and loops in five variables, degrees 8 "
          "and 10 and every k | m with a nonzero genus", ok,
          "%d covers" % ntest)

    print("(F) nondegeneracy of polynomials of simplex type")
    rng = random.Random(22)
    ok = True
    ntest = 0
    for n, trials in ((2, 12), (3, 4)):
        xs = sympy.symbols("x0:%d" % n)
        done = 0
        while done < trials:
            k = rng.randint(1, n)
            expos = [tuple(rng.randint(0, 3 if n == 3 else 5)
                           for _ in range(n)) for _ in range(k + 1)]
            if not affinely_independent(expos):
                continue
            coeffs = [sympy.Rational(rng.choice([-1, 1]) * rng.randint(1, 9),
                                     rng.randint(1, 9)) for _ in expos]
            ok &= nondegenerate(expos, coeffs, xs)
            done += 1
            ntest += 1
    x, y = sympy.symbols("x0:2")
    bad = [(2, 0), (1, 0), (0, 2), (0, 1), (0, 0)]
    control = not nondegenerate(bad, [1, -2, 1, -2, 2], (x, y))
    check("random polynomials of simplex type have no singular zero on the "
          "torus, and (x-1)^2 + (y-1)^2 is detected as singular",
          ok and control, "%d polynomials" % ntest)

    print("(G) the smooth adapted fan of the Klein quartic")
    verts = [(3, 1), (0, 3), (1, 0)]
    normals = inner_normals(verts)
    p2 = [(1, 0), (0, 1), (-1, -1)]
    rays = smooth_refinement(p2 + normals)
    cones = [(rays[i], rays[(i + 1) % len(rays)]) for i in range(len(rays))]
    unimod = all(det2(v, w) == 1 for v, w in cones)

    def argmin(v):
        vals = [u[0] * v[0] + u[1] * v[1] for u in verts]
        return {i for i, x in enumerate(vals) if x == min(vals)}
    adapted = all(argmin(v) & argmin(w) for v, w in cones)
    meets = {}
    for rho in rays:
        idx = sorted(argmin(rho))
        if len(idx) == 2:
            a, b = verts[idx[0]], verts[idx[1]]
            meets[rho] = math.gcd(abs(a[0] - b[0]), abs(a[1] - b[1]))
    area2 = abs(det2((verts[1][0] - verts[0][0], verts[1][1] - verts[0][1]),
                     (verts[2][0] - verts[0][0], verts[2][1] - verts[0][1])))
    chi = -area2 + sum(meets.values())
    check("%d rays, every cone unimodular and inside the normal cone of a "
          "vertex; the closure meets only the three edge divisors, one point "
          "each, and chi = -7 + 3 = -4 = 2 - 2 * 3" % len(rays),
          unimod and adapted and sorted(meets) == sorted(normals)
          and set(meets.values()) == {1} and area2 == 7 and chi == -4)

    print()
    print("%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    raise SystemExit(main())
