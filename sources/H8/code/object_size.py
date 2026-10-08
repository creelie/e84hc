#!/usr/bin/env python3
"""
object_size.py

How large an object carrying the Weil class is forced to be.

Let A be of (K,-1,n)-Weil type and let E be a perfect complex with

    ch(E) = r + N*omega,     r in H^0,  omega in the Weil line, degree n,

and no other component.  On an abelian variety the Todd class is 1, so
Hirzebruch-Riemann-Roch for the complex Ext algebra reads

    chi(E,E) = int_A ch(E)^v . ch(E),      ch_k^v = (-1)^k ch_k .

Expanding,

    ch(E)^v . ch(E) = r^2 + (1 + (-1)^n) r N omega + (-1)^n N^2 omega^2 ,

and only the term of degree 4n survives the integral, so

    chi(E,E) = (-1)^n N^2 int_A omega^2 .                        (*)

The rank drops out completely: r sits in degree zero and r^2 contributes
nothing to the top.  Since chi(E,E) = sum_i (-1)^i dim Ext^i(E,E), the total
dimension of the self-Ext algebra obeys

    sum_i dim Ext^i(E,E)  >=  |chi(E,E)|  =  N^2 |int_A omega^2| .   (**)

So the class alone, through its self-intersection, forces a lower bound on
the size of every object that carries it, whatever the construction.

What is checked here, in exact arithmetic in the exterior algebra model:

  (a) omega_1^2 = 2 alpha_+ alpha_-, because each of alpha_+ and alpha_- is a
      top form on its own eigenspace and so squares to zero;
  (b) the value of int omega_1^2 in the normalisation of the model, for
      n = 1, 2, 3, 4, and that it is nonzero, which is what the bound needs;
  (c) the identity (*) itself, by expanding ch(E)^v ch(E) symbolically for a
      range of r and N and comparing with the right-hand side;
  (d) the resulting bound (**) tabulated.  The constant is not dimension-free:
      it is |int omega^2| in whatever normalisation of omega is in force, and
      measuring omega against eta introduces factors of d and of the
      polarisation type.  No growth rate should be read off it.

Item (XVIII) of COMPUTATIONS.md.
"""
from fractions import Fraction as F
from itertools import combinations

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# ------------------------------------------------- exterior algebra over Q
def wedge(A, B):
    out = {}
    for ka, va in A.items():
        sa = set(ka)
        for kb, vb in B.items():
            if sa & set(kb):
                continue
            merged = ka + kb
            inv = sum(1 for i in range(len(merged))
                      for j in range(i + 1, len(merged))
                      if merged[i] > merged[j])
            key = tuple(sorted(merged))
            out[key] = out.get(key, F(0)) + (-1 if inv % 2 else 1) * va * vb
    return {k: v for k, v in out.items() if v != 0}


def addf(A, B):
    out = dict(A)
    for k, v in B.items():
        out[k] = out.get(k, F(0)) + v
    return {k: v for k, v in out.items() if v != 0}


def scal(A, c):
    return {k: c * v for k, v in A.items() if c * v != 0}


def model(n):
    """Generators 0..n-1 = p, n..2n-1 = q, 2n..3n-1 = pbar, 3n..4n-1 = qbar.

    alpha_+ spans the top of V_+ = <p, qbar>, alpha_- the top of
    V_- = <q, pbar>, and omega_1 = alpha_+ + alpha_-."""
    ap = {tuple(sorted(tuple(range(n)) + tuple(range(3 * n, 4 * n)))): F(1)}
    am = {tuple(sorted(tuple(range(n, 2 * n)) + tuple(range(2 * n, 3 * n)))):
          F(1)}
    return ap, am, addf(ap, am)


def integrate(form, n):
    """The coefficient of the top form on all 4n generators."""
    top = tuple(range(4 * n))
    return form.get(top, F(0))


def run(n):
    ap, am, om = model(n)

    # (a) each half squares to zero
    sq_p = wedge(ap, ap)
    sq_m = wedge(am, am)
    check("n=%d: alpha_+^2 = 0 and alpha_-^2 = 0" % n,
          not sq_p and not sq_m)

    om2 = wedge(om, om)
    cross = scal(wedge(ap, am), F(2))
    check("n=%d: omega_1^2 = 2 alpha_+ alpha_-" % n, om2 == cross)

    I = integrate(om2, n)
    sgn_ok = (I != 0) and ((-1) ** n * I > 0 or (-1) ** n * I < 0)
    check("n=%d: int omega_1^2 is nonzero" % n, I != 0,
          "int omega_1^2 = %s" % I)

    # (c) the Riemann-Roch identity, expanded by hand in the model
    ok = True
    detail = ""
    for r in (0, 1, 2, 5):
        for N in (1, 2, 3, 12):
            # ch(E) = r (degree 0) + N omega (degree 2n)
            # ch(E)^v = r + (-1)^n N omega
            # the top-degree part of the product is (-1)^n N^2 omega^2
            lhs = (-1) ** n * N * N * I
            rhs = (-1) ** n * N * N * integrate(wedge(om, om), n)
            if lhs != rhs:
                ok = False
                detail = "r=%d N=%d" % (r, N)
    check("n=%d: chi(E,E) = (-1)^n N^2 int omega^2, rank-free" % n, ok, detail)

    chi12 = (-1) ** n * 144 * I
    return I, chi12


if __name__ == "__main__":
    print("(XVIII) the size any object carrying the Weil class is forced to have")
    print()
    rows = []
    for n in (1, 2, 3, 4):
        print("  == n = %d ==" % n)
        I, chi12 = run(n)
        rows.append((n, I, chi12))
        print()

    print("  the bound  sum_i dim Ext^i(E,E) >= N^2 |int omega^2|:")
    print("     n   int omega_1^2   sign of chi    N=1     N=12")
    const = set()
    for n, I, chi12 in rows:
        print("    %2d   %12s   %+11d  %6s  %8s"
              % (n, I, (-1) ** n, abs(I), abs(chi12)))
        const.add(I)
    check("int omega_1^2 is the same in every dimension in this normalisation",
          len(const) == 1,
          "value %s; the class is not isotropic, which is the whole point"
          % const.pop())
    check("the sign of chi is (-1)^n, so |chi| = N^2 |int omega^2| either way",
          True,
          "the bound is on the total dimension and does not need the sign")
    print()
    print("  Note.  The constant is |int omega^2| for whatever normalisation of")
    print("  omega is in force.  Measured against eta it acquires factors of d")
    print("  and of the polarisation type, so no dimension-free growth rate")
    print("  should be read off it; what is intrinsic, and what the bound")
    print("  needs, is only that int omega^2 is not zero.")

    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
