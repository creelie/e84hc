#!/usr/bin/env python3
"""
A2 / euler.py -- numerics of the Orlov template E = Phi(F1 x F2^vee).

(1) chi(F,F) = int ch(F)^vee ch(F) for ch(F) = a u_t + b v_t, computed exactly
    in Q[t] with int t^n/n! = D (D = deg t), symbolic in a, b, d, D; compared
    with 2^{n-1} (-1)^{n/2} d^{n/2-1} (a^2 d + b^2) D (n even), 0 (n odd).
(2) Hochschild lower bounds r_k(ch F) (0 <= k <= n): 1, 2C(n,k), 1.
(3) Theorem A: dim Ext^2(E,E) = sum_k e_k e'_{2-k} >= R := r0 r2' + r1 r1' + r2 r0',
    with R = 6n^2 - 2n (n >= 3), 18 (n = 2).  Equality <=> e_{0,1,2} = e'_{0,1,2}
    = (1, 2n, n(n-1)) [(1,4,1) at n = 2] and e_{-j} e'_{2+j} = e_{2+j} e'_{-j} = 0.
(4) For F1 = F2 = F: admissible negative-Ext supports S = {j >= 1 : e_{-j} != 0}
    (j in S => j >= n-1 and j-(n-2) not in S); Euler characteristic
    chi = sum_{k=0}^n (-1)^k e_k + 2 sum_{j in S} (-1)^j e_{-j}  (n even),
    and the solvability of chi = chi(ch F) with the free middle Ext groups.
"""
import sympy as sp
from math import comb

a, b, d, D = sp.symbols('a b d D', positive=True)


def gamma(k):
    return a * (-d) ** (k // 2) if k % 2 == 0 else b * (-d) ** ((k - 1) // 2)


def chi_secant(n):
    # ch = sum gamma_k t^k/k!, ch^vee = sum (-1)^k gamma_k t^k/k!
    s = 0
    for i in range(n + 1):
        j = n - i
        s += (-1) ** i * gamma(i) * gamma(j) / (sp.factorial(i) * sp.factorial(j))
    return sp.expand(s * sp.factorial(n) * D)


def r(n, k):
    if k == 0 or k == n:
        return 1
    if 1 <= k <= n - 1:
        return 2 * comb(n, k)
    return 0


def R(n):
    return sum(r(n, i) * r(n, 2 - i) for i in range(0, 3))


print("=" * 78)
print("(1) chi(F,F) for ch(F) = a u_t + b v_t   (D = int t^n/n!)")
for n in range(2, 13):
    c = chi_secant(n)
    if n % 2 == 0:
        pred = 2 ** (n - 1) * (-1) ** (n // 2) * d ** (n // 2 - 1) * (a ** 2 * d + b ** 2) * D
    else:
        pred = 0
    ok = sp.simplify(c - pred) == 0
    print(f"  n={n:2d}: chi = {sp.factor(c)}    matches closed form: {ok}")

print("=" * 78)
print("(2),(3) Hochschild profile of a secant class and the Orlov number R")
for n in range(2, 13):
    prof = [r(n, k) for k in range(n + 1)]
    Rn = R(n)
    formula = 6 * n * n - 2 * n if n >= 3 else 18
    print(f"  n={n:2d}: r_k = {prof}   R = {Rn}  (6n^2-2n = {6*n*n-2*n}; check {Rn == formula})")

print("=" * 78)
print("(4) Equality profile (1,2n,n(n-1)) + Serre; Euler characteristic constraints")
for n in range(2, 13):
    fixed = {}
    fixed[0] = 1
    fixed[1] = 2 * n
    fixed[2] = n * (n - 1) if n >= 3 else 1
    e = {}
    for k in range(n + 1):
        if k in fixed:
            e[k] = fixed[k]
        if (n - k) in fixed:
            val = fixed[n - k]
            if k in e and e[k] != val:
                e[k] = None  # inconsistent (does not happen for n>=2)
            e[k] = val
    free = [k for k in range(n + 1) if k not in e]
    base = sum((-1) ** k * e[k] for k in e)
    target = chi_secant(n)
    if n % 2 == 1:
        concl = "n odd: chi = 0 identically on both sides; no constraint"
    elif not free:
        concl = (f"no free Ext^k in [0,n]: with Ext^<0 = 0, chi = {base} forced; "
                 f"need {sp.factor(target)} = {base}")
    else:
        # free middle degrees: k in [3, n-3]
        mids = sorted(set(min(k, n - k) for k in free))
        terms = []
        for k in mids:
            mult = 1 if k == n - k else 2
            terms.append(f"{'+' if (-1)**k*mult>0 else '-'}{mult if mult>1 else ''}e_{k}(>= {r(n,k)})")
        concl = f"free: chi = {base} {' '.join(terms)} ; any integer reachable -> no obstruction"
    print(f"  n={n:2d}: fixed e_k (Serre-completed) = {[e.get(k,'*') for k in range(n+1)]}")
    print(f"         {concl}")

print("=" * 78)
print("(5) n = 2: equality forces (a^2 d + b^2) D = 1")
print("    chi_needed = ", sp.factor(chi_secant(2)), " must equal 1 - 4 + 1 = -2")
print("    with t principal (D = 1), a, b integers (rank, c1 = b theta): a^2 d + b^2 = 1,")
sols = [(aa, bb, dd) for dd in range(1, 50) for aa in range(-3, 4) for bb in range(-3, 4)
        if aa * aa * dd + bb * bb == 1]
print("    solutions (a,b,d) with d < 50:", sorted(set(sols)))

print("=" * 78)
print("(6) n = 4 with negative Ext: base = -2, so")
print("    2 * sum_{j in S} (-1)^j e_{-j} = chi(F,F) + 2 = ", sp.factor(chi_secant(4) + 2))
print("    i.e. sum_{j in S} (-1)^j e_{-j} = 4 d (a^2 d + b^2) D + 1  >= 5 for D = 1.")


def admissible_S(n, jmax):
    import itertools
    cand = list(range(max(1, n - 1), jmax + 1))
    out = []
    for m in range(0, len(cand) + 1):
        for S in itertools.combinations(cand, m):
            Sset = set(S)
            if all((j - (n - 2)) not in Sset for j in S):
                out.append(S)
    return out


for n in (3, 4, 5, 6):
    Ss = admissible_S(n, n + 4)
    print(f"  n={n}: admissible negative-Ext supports S within [1,{n+4}]: {len(Ss)} sets; "
          f"minimal allowed degree -(n-1) = {-(n-1)}; examples {Ss[:6]}")
S4 = [S for S in admissible_S(4, 12) if any(j % 2 == 0 for j in S)]
print(f"  n=4: supports containing an even j (needed for chi > -2): smallest ones {S4[:6]}")
print("done")
