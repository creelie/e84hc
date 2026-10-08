"""
emit.py

Helpers shared by the generators in this directory: they turn exact vectors
over Q or Q(i), computed by the programs of code/, into Lean literals with
integer or Gaussian integer entries.  A vector is scaled by the least common
multiple of its denominators, which changes neither its span nor whether it
lies in a kernel.
"""
from fractions import Fraction as Fr
from math import gcd


def lcm(a, b):
    return a * b // gcd(a, b)


def parts(x):
    """(re, im) of an element of Q(i) given as an object with .a, .b, as a
    pair, as a Fraction or as an int."""
    if hasattr(x, "a") and hasattr(x, "b"):
        return Fr(x.a), Fr(x.b)
    if isinstance(x, tuple):
        return Fr(x[0]), Fr(x[1])
    return Fr(x), Fr(0)


def gauss_int(vec):
    """scale a list of elements of Q(i) to Gaussian integers, primitive"""
    ps = [parts(x) for x in vec]
    den = 1
    for a, b in ps:
        den = lcm(den, a.denominator)
        den = lcm(den, b.denominator)
    out = [(int(a * den), int(b * den)) for a, b in ps]
    g = 0
    for a, b in out:
        g = gcd(g, gcd(abs(a), abs(b)))
    g = g or 1
    return [(a // g, b // g) for a, b in out]


def int_vec(vec):
    """scale a list of rationals to integers, primitive"""
    den = 1
    for x in vec:
        den = lcm(den, Fr(x).denominator)
    out = [int(Fr(x) * den) for x in vec]
    g = 0
    for a in out:
        g = gcd(g, abs(a))
    g = g or 1
    return [a // g for a in out]


def lean_gvec(v):
    return "[" + ", ".join("(%d, %d)" % (a, b) for a, b in v) + "]"


def lean_gmat(rows, indent="  "):
    return "[\n" + ",\n".join(indent + lean_gvec(r) for r in rows) + "]"


def lean_ivec(v):
    return "[" + ", ".join("%d" % a for a in v) + "]"


def lean_imat(rows, indent="  "):
    return "[\n" + ",\n".join(indent + lean_ivec(r) for r in rows) + "]"


def lean_sparse_gcombo(v):
    """a Gaussian integer vector as a sparse list (index, re, im)"""
    return "[" + ", ".join("(%d, %d, %d)" % (k, a, b)
                           for k, (a, b) in enumerate(v) if a or b) + "]"
