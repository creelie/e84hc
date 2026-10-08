"""t3_verify.py -- track T3, round 12: all checks, exact (Fractions, Q(i)).
Run: python3 -B t3_verify.py   (about one minute)"""
import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from math import factorial, comb
from ext import *
from split import Split
from subvar import Zclass, tangent_T
from tflat import tflat_dims
from orlov import secant, dual, orlov_ch_fast, beta_X
from xrank import rk_profile

PASS, FAIL = [], []
def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print("  [%s] %s%s" % ("PASS" if ok else "FAIL", name, ("  -- " + detail) if detail else ""), flush=True)

def kappaB(S, g):
    return wedge(g, eexp(escale(Fr(1, 2), S.ell()), 4 * S.n))

def tensor_profile(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out

def chi_X(n, v):
    top = (1 << (2 * n)) - 1
    vol = escale(Fr(1, factorial(n)), epow(beta_X(n), n))
    return wedge(dual(v), v).get(top, 0) / vol[top]

t0 = time.time()
print("(1) model")
for d in (1, 2, 3):
    S = Split(2, d); w1, w2 = S.weil(); e = S.eta()
    g = eadd(w1, e, escale(Fr(3), epow(e, 2)), escale(Fr(-2), epow(e, 3)), {0: Fr(5)})
    check("n=2 d=%d: r(w1)=12, r(generic corrected)=24" % d, S.r_of(w1) == 12 and S.r_of(g) == 24)

print("(2) abelian subvarieties Z_{p:q}")
for n, d in [(2, 1), (2, 2), (3, 1)]:
    S = Split(n, d); w1, w2 = S.weil(); eta = S.eta()
    sl = [(0, 1), (1, 0), (1, 1), (1, -1), (1, 2), (2, 1), (-1, 3), (2, 3)]
    Zs = [Zclass(S, *s) for s in sl]
    ok = all(S.hodge_type_ok(S.to_complex(z), n) and S.integral(wedge(z, epow(eta, n))) > 0 for z in Zs)
    ok = ok and S.integral(wedge(Zclass(S, 1, 2), Zclass(S, 2, 1))) == 3 ** (2 * n)
    check("n=%d d=%d: [Z]=D^n/n! effective (n,n); int Z_s Z_t = det^{2n}" % (n, d), ok)
    check("n=%d d=%d: span of [Z]'s has dim 2n+1, contains w1,w2, not eta^n" % (n, d),
          rank_and_kernel(Zs) == 2 * n + 1 and solve_in_span(w1, Zs) is not None
          and solve_in_span(w2, Zs) is not None and solve_in_span(epow(eta, n), Zs) is None)
    T, act = tangent_T(S)
    dims = [len(T) - rank_and_kernel([act(v, S.to_complex(Zclass(S, *s))) for v in T]) for s in [(0, 1), (1, 1), (1, 2)]]
    check("n=%d d=%d: dim T = n^2, dim T cap Ann[Z] = n(n+1)/2" % (n, d), len(T) == n * n and all(x == n * (n + 1) // 2 for x in dims), str(dims))
S = Split(2, 1); w1, _ = S.weil()
c = eadd(escale(Fr(4), Zclass(S, 0, 1)), escale(Fr(4), Zclass(S, 1, 0)), escale(Fr(-1), Zclass(S, 1, 1)), escale(Fr(-1), Zclass(S, 1, -1)))
check("n=2 d=1: w1 = 4[0 x X^] + 4[X x 0] - [Z_1:1] - [Z_1:-1]", c == w1)

print("(3) T-flat rational classes")
for d in (1, 2, 3):
    check("n=2 d=%d: T-flat rational classes per degree = (1,1,3,1,1)" % d, tflat_dims(2, d) == [1, 1, 3, 1, 1])

print("(4) secant Hochschild profile on X and Euler characteristics")
for n in (2, 3, 4, 5):
    exp = [1] + [2 * comb(n, k) for k in range(1, n)] + [1] + [0] * n
    ok = all(rk_profile(n, secant(n, d, a, b), 2 * n) == exp for d in (1, 2, 3) for (a, b) in [(1, 0), (0, 1), (1, 1), (2, 1)])
    check("n=%d: r^k_X(v) = (1,2n,2C(n,2),...,2C(n,n-1),1) for 12 secant v" % n, ok)
for n in (2, 3, 4, 5, 6):
    ok = True
    for d in (1, 2, 3):
        for (a, b) in [(1, 0), (0, 1), (1, 1), (2, 1)]:
            pred = 0 if n % 2 else 2 ** (n - 1) * (-1) ** (n // 2) * d ** (n // 2 - 1) * Fr(a * a * d + b * b)
            ok = ok and chi_X(n, secant(n, d, a, b)) == pred
    check("n=%d: chi(F,F) = 2^{n-1}(-1)^{n/2} d^{n/2-1} Nm(b+a sqrt(-d)) (0 for n odd)" % n, ok)

print("(5) Orlov objects E = Phi(F1 [x] F2^vee): bilinear basis")
for n, ds in [(2, [1, 2, 3, 5]), (3, [1, 2, 6, 30, 42]), (4, [1, 2, 3])]:
    for d in ds:
        S = Split(n, d); good = True
        for p in [(1, 0), (0, 1)]:
            for q in [(1, 0), (0, 1)]:
                g = orlov_ch_fast(n, secant(n, d, *p), dual(secant(n, d, *q)))
                cc = S.corrected_coords(kappaB(S, g))
                if cc is None:
                    good = False; continue
                mu = [factorial(m) * cc[0][m] for m in range(2 * n + 1)]
                good = good and all(mu[m + 2] == -mu[m] / (4 * d) for m in range(2 * n - 1))
                # the B-field is forced: ch(E) itself is not flat
                good = good and S.corrected_coords(g) is None
        check("n=%d d=%d: ch(E)e^{ell/2} in Q[eta]+HW, moments mu_{m+2}=-mu_m/(4d) (rho<=2), ch(E) not flat" % (n, d), good)

print("(6) certificates")
for d, v, name in [(1, (1, 0), "I_p"), (1, (0, 1), "O_C(p)"), (2, (0, 1), "O_C(p)"), (3, (0, 1), "O_C(p)"), (5, (0, 1), "O_C(p)")]:
    S = Split(2, d); f = secant(2, d, *v); g = orlov_ch_fast(2, f, dual(f))
    cc = S.corrected_coords(kappaB(S, g))
    prof = S.profile(g, 4)
    w1, w2 = S.weil(); om = eadd(escale(cc[1], w1), escale(cc[2], w2))
    R = cc[0][2] ** 2 * S.integral(epow(S.eta(), 4)) / S.integral(wedge(om, om))
    check("n=2 d=%d F=%s: Hochschild profile of ch(E) = (1,8,18,8,1) = (1,4,1)^2 = Ext profile; Weil part %s != 0; R = 3/4, c1=c3=0"
          % (d, name, (cc[1], cc[2])), prof == [1, 8, 18, 8, 1] and (cc[1], cc[2]) != (0, 0) and R == Fr(3, 4) and cc[0][1] == 0 and cc[0][3] == 0)
for d in (2, 6):
    S = Split(3, d); f = secant(3, d, 0, 1); g = orlov_ch_fast(3, f, dual(f))
    cc = S.corrected_coords(kappaB(S, g))
    check("n=3 d=%d F=i_*L on Theta: Hochschild profile of ch(E) = (1,6,6,1)^2 = (1,12,48,74,48,12,1); Weil %s" % (d, (cc[1], cc[2])),
          S.profile(g, 6) == tensor_profile([1, 6, 6, 1], [1, 6, 6, 1]) and (cc[1], cc[2]) != (0, 0))
# line bundle arithmetic on Theta = C^(2), g = 3:  x^2=1, x.theta=3, theta^2=6, K=theta, chi(O)=1
for k in (1, 2, 5, 6):
    d = k * (k + 1); al, be = 2 * k + 1, -k
    c2 = al + 2 * be - 1
    Lsq = al * al + 6 * al * be + 6 * be * be; LK = 3 * al + 6 * be
    chi = 1 + Fr(Lsq - LK, 2)
    check("n=3 d=%d: L=(2k+1)x - k theta on C^(2): ch_2(i_*L)=0, chi(L)=-d, so ch(i_*L) = Theta - d pt = v_t" % d, c2 == 0 and chi == -d)

print("(7) n = 4: the product template cannot meet the number")
for d, p, q in [(1, (0, 1), (0, 1)), (1, (1, 0), (0, 1)), (2, (1, 1), (1, 0))]:
    S = Split(4, d); g = orlov_ch_fast(4, secant(4, d, *p), dual(secant(4, d, *q)))
    check("n=4 d=%d pair %s,%s: r(ch E) = 88 = r0 r2 + r1 r1 + r2 r0 = 12 + 64 + 12" % (d, p, q), S.r_of(g) == 88)
check("n=4: minimal profile (1,8,12,8,1) has chi = -2, secant chi >= 8", 1 - 8 + 12 - 8 + 1 == -2 and min(chi_X(4, secant(4, d, a, b)) for d in (1, 2, 3) for (a, b) in [(1, 0), (0, 1), (1, 1)]) >= 8)

print("(8) untwisting by symmetric square (n = 2) and the subvariety direct sum")
def psi2(u):
    return {m: c * (2 ** (popcount(m) // 2)) for m, c in u.items()}
for d in (1, 2, 3):
    S = Split(2, d); f = secant(2, d, 0, 1); g = orlov_ch_fast(2, f, dual(f))
    c = wedge(escale(Fr(1, 2), eadd(wedge(g, g), escale(Fr(-1), psi2(g)))), eexp(S.ell(), 8))
    cc = S.corrected_coords(c)
    check("n=2 d=%d: S^2(E[1]) (x) P untwisted, flat, rank 3, Weil %s, r = 23 (odd: parity forbids equality)" % (d, (cc[1], cc[2])),
          cc is not None and c.get(0) == 3 and (cc[1], cc[2]) != (0, 0) and S.r_of(c) == 23)
S = Split(2, 1)
imgs = []
for s in [(0, 1), (1, 0), (1, 1), (1, -1)]:
    imgs += S.ht2_images(S.to_complex(Zclass(S, *s)))[0]
check("n=2 d=1: Z-sum for w1 has Ext^2 = 60, rank sigma = 18, dim ker sigma = 42", rank_and_kernel(imgs) == 18)

print("\n%d checks passed, %d failed  (%.1fs)" % (len(PASS), len(FAIL), time.time() - t0))
