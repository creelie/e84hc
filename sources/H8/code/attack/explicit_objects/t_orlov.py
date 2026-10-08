import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
from split import Split
from orlov import *
from ext import *
n = 2
# sanity: Phi(O_Delta) = k(0)[-n]: K = O_Delta has ch = class of diagonal;
# instead test Phi(O_X [x] O_0^vee) etc. quickly: F1 = O_X, F2 = O_x (point)
one = {0: Fr(1)}
for d in [1, 2, 3]:
    S = Split(n, d)
    chF = eadd(one, escale(Fr(-d), pt_X(n)))   # I_W, |W| = d
    g = orlov_ch(n, chF, dual(chF))
    print("d =", d, " rank =", g.get(0, 0), " int ch_top =", S.integral(g))
    cc = S.corrected_coords(g)
    print("   corrected form?", cc is not None)
    if cc:
        c, a, b = cc
        print("   c_k =", c, " weil coords (w1,w2) =", a, b)
    else:
        # find which degrees fail
        for k in range(0, 4 * n + 1, 2):
            gk = degree_part(g, k)
            if not gk: continue
            fb = [degree_part(u, k) for u in S.flat_basis()]
            fb = [u for u in fb if u]
            print("   degree", k, "in flat span:", solve_in_span(gk, fb) is not None)
