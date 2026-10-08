"""Exact checks of the finite steps of paper/main.tex.

Each check prints one line per verified quantity, in the form

    <item> <key> <value>

so that the Julia and C versions can be compared with this one line by line
(verification/shell/run_all.sh does the comparison).  Nothing here is used in
a proof; every statement checked is proved in the paper.

Items
  F  Fermat varieties X^n_m, n = 2, 4: characters, Hodge numbers, Hodge
     classes, Picard numbers of Fermat surfaces, Aoki-Shioda values.
  J  Fermat curves: every Galois orbit of characters has a CM type
     (the type function is odd).
  S  The switch lemma (Lemma 4.1): exhaustive for small sizes.
  G  The signs (-1)^(p(p-1)/2) of the permutations that regroup a product of
     2p classes of degree one between interleaved and blocked order.
  W  Weil families: Prym locus 3n against n^2, and the count of Remark 5.13.
  L  The logical skeleton of Theorem B: a valuation in which every rule
     and (CM) hold and the Hodge conjecture fails, the four closed sets of
     the proof, the minimal sets of statements that give the conjecture,
     and the routes around (F2), (F3') and Schoen's subvariety.
"""

from fractions import Fraction
from itertools import combinations, product
from math import gcd
import sys

OUT = []


def emit(item, key, value):
    line = f"{item} {key} {value}"
    OUT.append(line)
    print(line)


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


# ---------------------------------------------------------------------------
# F: Fermat varieties
# ---------------------------------------------------------------------------

def characters(n, m):
    """a in (Z/m - 0)^(n+2) with sum 0 mod m."""
    k = n + 2
    out = []
    for a in product(range(1, m), repeat=k - 1):
        last = (-sum(a)) % m
        if last != 0:
            out.append(a + (last,))
    return out


def bracket(a, m):
    """<a> = sum of fractional parts a_i / m, an integer for a character."""
    s = sum(x % m for x in a)
    assert s % m == 0
    return s // m


def pair_type(a, m):
    """a splits into pairs (a_i, a_j) with a_i + a_j = 0 mod m."""
    a = list(a)
    if not a:
        return True
    x = a[0]
    for j in range(1, len(a)):
        if (x + a[j]) % m == 0:
            rest = a[1:j] + a[j + 1:]
            if pair_type(rest, m):
                return True
    return False


def fermat(n, m):
    chars = characters(n, m)
    U = units(m)
    mid = (n + 2) // 2
    b_prim = len(chars)
    h_mid = sum(1 for a in chars if bracket(a, m) == mid)
    hodge = [a for a in chars
             if all(bracket(tuple((t * x) % m for x in a), m) == mid for t in U)]
    odd_ok = all(bracket(tuple((t * x) % m for x in a), m)
                 + bracket(tuple((-t * x) % m for x in a), m) == n + 2
                 for a in chars for t in U)
    pairs = sum(1 for a in hodge if pair_type(a, m))
    return b_prim, h_mid, len(hodge), pairs, odd_ok


def check_fermat():
    for n, mmax in ((2, 12), (4, 8)):
        for m in range(2, mmax + 1):
            b_prim, h_mid, hdg, pairs, odd_ok = fermat(n, m)
            closed = ((m - 1) ** (n + 2) + (-1) ** n * (m - 1)) // m
            assert b_prim == closed, (n, m)
            assert odd_ok
            emit("F", f"n={n},m={m},b_prim", b_prim)
            emit("F", f"n={n},m={m},h_mid_prim", h_mid)
            emit("F", f"n={n},m={m},hodge_prim", hdg)
            emit("F", f"n={n},m={m},pair_type", pairs)
            if n == 2:
                rho = hdg + 1
                h11 = h_mid + 1
                assert 3 * h11 == 2 * m ** 3 - 6 * m ** 2 + 7 * m, m
                emit("F", f"n=2,m={m},rho", rho)
                if gcd(m, 6) == 1:
                    assert rho == 3 * (m - 1) * (m - 2) + 1, m
                    assert pairs == hdg, m
    # values in the literature: the Fermat quartic, quintic and sextic surfaces
    assert fermat(2, 4)[2] + 1 == 20
    assert fermat(2, 5)[2] + 1 == 37
    assert fermat(2, 6)[2] + 1 == 86
    emit("F", "aoki_shioda_values", "20,37,86")


# ---------------------------------------------------------------------------
# J: Fermat curves have CM Jacobians, orbit by orbit
# ---------------------------------------------------------------------------

def check_fermat_curves():
    worst = 0
    for m in range(3, 31):
        U = units(m)
        chars = characters(1, m)
        seen = set()
        orbits = 0
        for a in chars:
            if a in seen:
                continue
            orb = {tuple((t * x) % m for x in a) for t in U}
            seen |= orb
            orbits += 1
            hol = sum(1 for b in orb if bracket(b, m) == 1)
            assert all(bracket(b, m) in (1, 2) for b in orb)
            # odd type function: exactly one of b, -b is holomorphic
            for b in orb:
                nb = tuple((-x) % m for x in b)
                assert (bracket(b, m) == 1) != (bracket(nb, m) == 1)
            assert 2 * hol == len(orb)
            worst = max(worst, len(orb))
        genus = (m - 1) * (m - 2) // 2
        assert len(chars) == 2 * genus
        emit("J", f"m={m},orbits", orbits)
    emit("J", "largest_orbit_up_to_30", worst)


# ---------------------------------------------------------------------------
# S: the switch lemma
# ---------------------------------------------------------------------------

def switch_sequence(x, y):
    """Column correction of Lemma 4.1.  x, y: lists of p rows, each a tuple of
    s signs.  Returns the list of intermediate lists, ending at y."""
    x = [list(r) for r in x]
    p = len(x)
    s = len(x[0]) if p else 0
    seq = [tuple(tuple(r) for r in x)]
    for col in range(s):
        plus = [i for i in range(p) if x[i][col] == 1 and y[i][col] == -1]
        minus = [i for i in range(p) if x[i][col] == -1 and y[i][col] == 1]
        assert len(plus) == len(minus)
        for i, j in zip(plus, minus):
            x[i][col], x[j][col] = x[j][col], x[i][col]
            seq.append(tuple(tuple(r) for r in x))
    assert [tuple(r) for r in x] == [tuple(r) for r in y]
    return seq


def check_switch():
    total_pairs = 0
    total_steps = 0
    for p in range(1, 5):
        for s in range(1, 4):
            rows = list(product((1, -1), repeat=s))
            lists = list(product(rows, repeat=p))
            by_sum = {}
            for L in lists:
                key = tuple(sum(r[c] for r in L) for c in range(s))
                by_sum.setdefault(key, []).append(L)
            pairs = 0
            maxsteps = 0
            for group in by_sum.values():
                for x in group:
                    for y in group:
                        seq = switch_sequence(x, y)
                        for u, v in zip(seq, seq[1:]):
                            changed = [i for i in range(p) if u[i] != v[i]]
                            assert len(changed) == 2
                            i, j = changed
                            for c in range(s):
                                assert u[i][c] + u[j][c] == v[i][c] + v[j][c]
                        pairs += 1
                        maxsteps = max(maxsteps, len(seq) - 1)
            bound = s * (p // 2)
            assert maxsteps <= bound
            total_pairs += pairs
            total_steps = max(total_steps, maxsteps)
            emit("S", f"p={p},s={s},pairs", pairs)
            emit("S", f"p={p},s={s},max_switches", maxsteps)
    emit("S", "all_pairs", total_pairs)


# ---------------------------------------------------------------------------
# G: signs
# ---------------------------------------------------------------------------

def perm_sign(perm):
    sign = 1
    perm = list(perm)
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                sign = -sign
    return sign


def check_signs():
    for p in range(1, 11):
        # degree-one classes b_1..b_p g_1..g_p regrouped as b_1 g_1 ... b_p g_p
        target = []
        for i in range(p):
            target += [i, p + i]
        sgn = perm_sign(target)
        assert sgn == (-1) ** (p * (p - 1) // 2)
        emit("G", f"regroup_p={p}", sgn)
    for k in range(1, 9):
        # a_1 b_1 a_2 b_2 ... a_k b_k  ->  a_1 ... a_k b_1 ... b_k
        order = []
        for i in range(k):
            order += [i, k + i]
        sgn = perm_sign(order)
        assert sgn == (-1) ** (k * (k - 1) // 2)
        emit("G", f"kernel_k={k}", sgn)


# ---------------------------------------------------------------------------
# W: Weil families
# ---------------------------------------------------------------------------

def check_weil():
    for n in range(2, 13):
        emit("W", f"n={n},prym,weil", f"{3 * n},{n * n}")
    for m in range(2, 13):
        ks = [k for k in range(0, 13) if 3 * (m + k) + 3 * k >= (m + k) ** 2]
        emit("W", f"m={m},k_passing", ",".join(map(str, ks)) or "none")
    ks2 = [k for k in range(13) if 3 * (2 + k) + 3 * k >= (2 + k) ** 2]
    assert ks2 == [0, 1, 2]
    assert [k for k in range(13) if 3 * (3 + k) + 3 * k >= (3 + k) ** 2] == [0]
    for m in range(4, 60):
        assert all(3 * (m + k) + 3 * k < (m + k) ** 2 for k in range(0, 200))


# ---------------------------------------------------------------------------
# L: the logical skeleton
# ---------------------------------------------------------------------------

# Statements.  F2 is the Hodge conjecture for abelian varieties; F3P is
# (F3'); L, M, V are the Lefschetz standard conjecture for every variety,
# "every Hodge class is motivated" and the variational Hodge conjecture; IP
# is propagation from CM points in abelian schemes; CM is the Hodge
# conjecture for abelian varieties of CM type (claimed in [OAI26], not
# refereed); SR is the semiregularity of Schoen's subvariety Y; W3 is the
# algebraicity of the Weil classes of the split Weil families of Q(sqrt -3)
# in every dimension; FER is the Hodge conjecture for every Fermat
# variety.
OPEN = ["F2", "F3P", "L", "M", "V", "IP", "CM", "SR"]
DERIVED = ["HC", "FER", "W3"]
ATOMS = OPEN + DERIVED

# (premises, conclusion); every rule is proved in the paper or cited there.
RULES = [
    (["F2", "F3P"], "HC"),                      # Theorem A, (ii) => (i)
    (["HC"], "F2"), (["HC"], "F3P"),            # Lemma 2.11
    (["HC"], "L"), (["HC"], "M"), (["HC"], "V"),  # Lemma 2.11
    (["L", "M"], "HC"),                         # Proposition 2.8
    (["L"], "F2"),                              # [Mil20, Theorem 4]
    (["V"], "F2"),                              # [Mil20, Theorem 3]
    (["V"], "IP"),                              # IP is a case of V
    (["F3P"], "M"),                             # Proposition 2.9
    (["CM", "IP"], "F2"),                       # Proposition 4.4
    (["F2"], "IP"), (["F2"], "CM"),             # Proposition 4.4
    (["CM"], "FER"), (["HC"], "FER"),           # Theorem C
    (["SR"], "W3"),                             # Cor 5.8; Thm 2.3, [Sch88, Sch98]
    (["F2"], "W3"),                             # W3 is a case of F2
]

# the closed sets of the proof of Theorem B: everything except these
CLOSED_COMPLEMENTS = [
    ["HC", "M", "F3P"],
    ["HC", "L", "F3P"],
    ["HC", "F2", "L", "V", "IP"],
    ["HC", "F2", "L", "V", "CM"],
]


def closure(start):
    have = set(start)
    changed = True
    while changed:
        changed = False
        for prem, concl in RULES:
            if concl not in have and all(p in have for p in prem):
                have.add(concl)
                changed = True
    return have


def minimal_sets(base, pool):
    found = []
    for r in range(1, len(pool) + 1):
        for S in combinations(pool, r):
            if any(set(M) <= set(S) for M in found):
                continue
            if "HC" in closure(base | set(S)):
                found.append(S)
    return found


def is_closed(T):
    return all(concl in T for prem, concl in RULES
               if all(p in T for p in prem))


def check_logic():
    # (CM) alone gives the Fermat varieties and nothing else
    cl = closure({"CM"})
    assert cl == {"CM", "FER"}
    emit("L", "closure_of_CM", ",".join(sorted(cl - {"CM"})))
    # a valuation in which every rule holds, (CM) holds and HC fails
    val = {a: (a in cl) for a in ATOMS}
    for prem, concl in RULES:
        assert (not all(val[p] for p in prem)) or val[concl]
    emit("L", "countermodel_HC", str(val["HC"]).lower())
    # the four closed sets of the proof of Theorem B
    for out in CLOSED_COMPLEMENTS:
        T = set(ATOMS) - set(out)
        assert is_closed(T) and "HC" not in T
        emit("L", "closed_without", "+".join(out[1:]))
    # Schoen's question, with (CM), does not reach HC
    assert "HC" not in closure({"SR", "CM"})
    # minimal sufficient sets of open statements
    mins = minimal_sets(set(), OPEN)
    for S in mins:
        emit("L", "minimal_set", "+".join(S))
    emit("L", "minimal_sets", len(mins))
    # the same, granting (CM)
    mins_cm = minimal_sets({"CM"}, [a for a in OPEN if a != "CM"])
    for S in mins_cm:
        emit("L", "minimal_set_given_CM", "+".join(S))
    # every sufficient set contains M or F3P, and implies all of them
    for S in mins:
        assert "M" in S or "F3P" in S
        assert set(OPEN) - {"SR"} <= closure(set(S))
    # the routes that avoid F2, F3P, IP, CM and SR
    avoid = {"F2", "F3P", "IP", "CM", "SR"}
    bypass = [S for S in mins if not avoid & set(S)]
    for S in bypass:
        emit("L", "bypass_F2_F3P_SR", "+".join(S))
    assert bypass == [("L", "M")]


def main():
    check_fermat()
    check_fermat_curves()
    check_switch()
    check_signs()
    check_weil()
    check_logic()
    print()
    print(f"{len(OUT)} lines, all checks passed")


if __name__ == "__main__":
    main()
