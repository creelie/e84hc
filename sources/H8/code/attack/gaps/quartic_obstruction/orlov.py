"""orlov.py -- cohomological Orlov transform (track A1), bitmask version.

Phi(K) = (1 x Phi_P)(mu_* K), mu(a,b) = (a-b, b), c_1(P) = sum_i y_i xi_i.
For K = F1 [x] F2' on X x X (X of dimension g, H^1 generators x_0..x_{2g-1}):
  ch(Phi K)(x, xi) = int_y ch(F1)(x+y) ch(F2')(y) exp(sum_i y_i xi_i)
with generator order x (0..2g-1), xi (2g..4g-1), y (4g..6g-1) and
int_X y_0...y_{2g-1} = (-1)^{g(g-1)/2}.  Same conventions as the round-12 T3
verification (orl.py there), against which this is validated at g = 2.
Output: dict over 4g-bit masks (x bits 0..2g-1, xi bits 2g..4g-1).
"""
from fractions import Fraction as Fr
from ealib import pc, wsign, clean


def orlov(g, c1, c2):
    m = 2 * g
    full = (1 << m) - 1
    s0 = -1 if (g * (g - 1) // 2) % 2 else 1
    out = {}
    # precompute for each subset L of y's: sign of prod_{i in L} (y_i xi_i) = (-1)^{|L|(|L|-1)/2} y_L xi_L
    for I, a in c1.items():
        # iterate over J subset of I (the y-part of prod_{i in I}(x_i + y_i))
        Ibits = [i for i in range(m) if I >> i & 1]
        J = I
        while True:
            # interleave sign: pairs i < i' in I with i in J and i' not in J
            s_int = 0
            for i in Ibits:
                if J >> i & 1:
                    s_int += pc((I & ~J) >> (i + 1))
            P = I & ~J
            for K, b in c2.items():
                if K & J:
                    continue
                L = full & ~(J | K)
                s = s_int
                s += 0 if wsign(J, K) > 0 else 1
                JK = J | K
                s += 0 if wsign(JK, L) > 0 else 1
                l = pc(L)
                s += l * (l - 1) // 2
                # x_P y_all xi_L -> x_P xi_L y_all: move xi_L past y_all (m elements): (-1)^{m l}
                s += m * l
                key = P | (L << m)
                val = a * b
                if (s & 1):
                    val = -val
                if s0 < 0:
                    val = -val
                out[key] = out.get(key, 0) + val
            if J == 0:
                break
            J = (J - 1) & I
    return clean(out)
