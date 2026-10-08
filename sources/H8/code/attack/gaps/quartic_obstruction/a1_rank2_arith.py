"""a1_rank2_arith.py -- the arithmetic of the rank-two case of prop:quarticother,
for every real quadratic field F0 = Q(sqrt D), D > 1 squarefree.

Setting (proof of thm:quarticobstruction and prop:quarticother): a rank-two
integral secant class with chi = 6 and N_w = 4 has an invariant
m = mu^2 N(Delta) in [1, 8], where l is primitive with l^T V = 0,
adj V = mu lbar l^T and Delta = l_1^2 - 4 l_0 l_2, and
 (a) 4m = 36 modulo d cap Z, the different d being (sqrt D) for D = 1 mod 4
     and (2 sqrt D) otherwise; for D squarefree this says m = 9 modulo the odd
     part D_o of D;
 (b) m = 0 or 1 modulo 4: localising at 2, l is primitive, mu lies in Z_(2),
     and N(Delta) = N(l_1^2 + 4w) = N(l_1)^2 modulo 4;
 (c) m is odd when D = 2 mod 4: at the prime p above 2, v_p(d) = 3 and
     v_p(6) = 2, so the unsquared congruence 6 = +-2 mu Delta modulo d makes
     mu and Delta units at p.
This script checks exactly:
 1. the identity N(x + 4w) - N(x) = 0 mod 4 and N(x^2) = N(x)^2 in the rings
    Z[sqrt D] and Z[(1 + sqrt D)/2], with D a symbol (this is (b));
 2. for D = 2 mod 4, that a + b sqrt D is a unit at the prime above 2 iff a is
    odd iff its norm is odd (residues modulo 4);
 3. for every squarefree D < 200000, that (a), (b), (c) have no common solution
    m in [1, 8] unless D = 2 (m = 1, 5) or D = 5 (m = 4), the two fields treated
    in thm:quarticobstruction; and that without (b) and (c) the fields
    D = 3, 6, 7, 10, 14 would survive, so (b) and (c) are needed.
"""
import sympy as sp

PASS, FAIL = [], []


def check(name, ok):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s" % ("PASS" if ok else "FAIL", name), flush=True)


def ring_identities():
    D = sp.Symbol("D")
    a, b, c, e = sp.symbols("a b c e", integer=True)
    for name, half in (("Z[sqrt D]", False), ("Z[(1 + sqrt D)/2]", True)):
        # an element x = a + b w, w = sqrt D or (1 + sqrt D)/2; multiplication and norm
        if half:
            # w^2 = w + (D - 1)/4 ; put D = 4t + 1 so that coefficients are integral
            t = sp.Symbol("t")

            def mul(x, y):
                return (sp.expand(x[0] * y[0] + t * x[1] * y[1]),
                        sp.expand(x[0] * y[1] + x[1] * y[0] + x[1] * y[1]))

            def nrm(x):
                return sp.expand(x[0] ** 2 + x[0] * x[1] - t * x[1] ** 2)
        else:
            def mul(x, y):
                return (sp.expand(x[0] * y[0] + D * x[1] * y[1]),
                        sp.expand(x[0] * y[1] + x[1] * y[0]))

            def nrm(x):
                return sp.expand(x[0] ** 2 - D * x[1] ** 2)
        x = (a, b)
        w = (c, e)
        y = (x[0] + 4 * w[0], x[1] + 4 * w[1])
        gensym = (a, b, c, e, t if half else D)
        diff = sp.Poly(sp.expand(nrm(y) - nrm(x)), *gensym)
        ok1 = all(int(q) % 4 == 0 for q in diff.coeffs())
        check("%s: N(x + 4w) - N(x) has all coefficients divisible by 4 (D a symbol)" % name, ok1)
        ok2 = sp.expand(nrm(mul(x, x)) - nrm(x) ** 2) == 0
        check("%s: N(x^2) = N(x)^2" % name, ok2)
    ok = all((n * n) % 4 in (0, 1) for n in range(4))
    check("a square is 0 or 1 modulo 4", ok)


def parity_at_two():
    for D in (2, 6, 10, 14, 22, 26, 30):
        ok = True
        for a in range(4):
            for b in range(4):
                n = (a * a - D * b * b) % 2
                ok = ok and ((a % 2 == 1) == (n == 1))
        check("D = %d: a + b sqrt D is a unit at the prime above 2 iff a is odd iff "
              "its norm is odd" % D, ok)


def squarefree(n):
    i = 2
    while i * i <= n:
        if n % (i * i) == 0:
            return False
        i += 1
    return True


def survivors(D, two_adic=True):
    Do = D // 2 if D % 2 == 0 else D
    ms = [m for m in range(1, 9) if (m - 9) % Do == 0]
    if two_adic:
        ms = [m for m in ms if m % 4 in (0, 1)]
        if D % 4 == 2:
            ms = [m for m in ms if m % 2 == 1]
    return ms


def sweep(N):
    bad = {}
    naive = {}
    count = 0
    # the congruence (a) directly in the form 4m = 36 mod (d cap Z), to cross-check the reduction
    for D in range(2, N):
        if not squarefree(D):
            continue
        count += 1
        dz = D if D % 4 == 1 else 2 * D
        direct = [m for m in range(1, 9) if (4 * m - 36) % dz == 0]
        Do = D // 2 if D % 2 == 0 else D
        if direct != [m for m in range(1, 9) if (m - 9) % Do == 0]:
            bad[("reduction", D)] = direct
        s = survivors(D)
        if s:
            bad[D] = s
        s0 = survivors(D, two_adic=False)
        if s0:
            naive[D] = s0
    check("the congruence 4m = 36 mod (d cap Z) is m = 9 modulo the odd part of D, "
          "for all %d squarefree D < %d" % (count, N), not any(isinstance(k, tuple) for k in bad))
    check("for squarefree D < %d the conditions (a), (b), (c) have a solution in [1,8] "
          "only for D = 2 (m = 1, 5) and D = 5 (m = 4): %s" % (N, bad),
          bad == {2: [1, 5], 5: [4]})
    check("without (b) and (c) the survivors would be %s" % naive,
          naive == {2: list(range(1, 9)), 3: [3, 6], 5: [4], 6: [3, 6], 7: [2], 10: [4], 14: [2]})


def main():
    ring_identities()
    parity_at_two()
    sweep(200000)
    print()
    print("%d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)


if __name__ == "__main__":
    main()
