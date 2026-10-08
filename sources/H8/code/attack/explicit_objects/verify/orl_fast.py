"""orl_fast.py -- the same transform as orl.orlov, integrating exp(sum y_i xi_i) term by term
(validated against orl.orlov at n=2,3 before use at n=4)."""
from fractions import Fraction as F
from ea import *
def orlov_fast(n, c1, c2):
    m = 2 * n; Y = 4 * n
    a = linsub(c1, {i: add(g(i), g(Y + i)) for i in range(m)})
    b = linsub(c2, {i: g(Y + i) for i in range(m)})
    A = mul(a, b)
    s0 = (-1) ** (n * (n - 1) // 2)
    out = {}
    for mono, c in A.items():
        xs = tuple(i for i in mono if i < Y)
        yB = tuple(i - Y for i in mono if i >= Y)
        Bc = tuple(i for i in range(m) if i not in yB)
        k = len(Bc)
        s1 = (-1) ** (k * (k - 1) // 2)
        s2, _ = merge_sign(yB, Bc)
        key = xs + tuple(m + i for i in Bc)
        s, key2 = merge_sign(xs, tuple(m + i for i in Bc))
        # xs has only x indices (< m) and xi indices are >= m, so s == 1
        val = c * (s0 * s1 * s2 * s)
        out[key2] = out.get(key2, 0) + val
    return clean(out)
