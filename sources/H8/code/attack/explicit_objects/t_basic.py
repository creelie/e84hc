import sys, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from split import Split
from ext import *
for n, d in [(2,1),(2,2),(2,3)]:
    S = Split(n, d)
    eta = S.eta(); w1, w2 = S.weil()
    print("n,d", n, d)
    print(" eta (1,1):", S.hodge_type_ok(S.to_complex(eta), 1))
    print(" w1,w2 (n,n):", S.hodge_type_ok(S.to_complex(w1), n), S.hodge_type_ok(S.to_complex(w2), n))
    print(" eta*w1 = 0:", wedge(eta, w1) == {}, " int eta^4n:", S.integral(epow(eta, 2*n)))
    print(" int w1^2, w1w2, w2^2:", S.integral(wedge(w1,w1)), S.integral(wedge(w1,w2)), S.integral(wedge(w2,w2)))
    t0=time.time()
    print(" r(w1) pure =", S.r_of(w1), "(expect 2n(2n-1) =", 2*n*(2*n-1), ")")
    g = eadd(w1, eta, escale(Fr(3), epow(eta,2)), escale(Fr(-2), epow(eta,3)), escale(Fr(5),{0:Fr(1)}))
    print(" r(generic) =", S.r_of(g), "(expect 7n^2-2n =", 7*n*n-2*n, ")", time.time()-t0)
