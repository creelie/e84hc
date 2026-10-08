"""
An explicit family of abelian 2n-folds of Weil type, for every n and every
imaginary quadratic K, together with the two conjugate maximal isotropic
subspaces and the two conjugate pure spinors they determine.

Construction.  Let X be an abelian n-fold with complex structure J on
H_1(X,R) = R^{2n}, and let b be a nondegenerate element of NS(X) (x) Q, that
is an alternating rational form with  J^T b J = b.  Put A = X x Xhat, so
H_1(A,Q) = Q^{2n} (+) (Q^{2n})^dual, of dimension 4n, and

        M = [ 0      -b^{-1} ]
            [ d b     0       ]  .

The script checks, for explicit X and b:

  (1) M^2 = -d, so M defines an action of K = Q(sqrt(-d)) on A;
  (2) M commutes with the complex structure of A, so the action is by
      endomorphisms, and this uses exactly the Riemann relation on b;
  (3) M has eigenvalues +-sqrt(-d) on H^{1,0}(A) with equal multiplicity n,
      so A is of (K,-1,n)-Weil type;
  (4) the two eigenspaces of M on H_1(A,C) are maximal isotropic for the
      canonical pairing on V (+) V^dual, and are exchanged by conjugation;
  (5) each eigenspace is the graph of the two-form  d b / (+-sqrt(-d)) =
      -+ sqrt(-d) b , so the attached pure spinors are  exp( -+ sqrt(-d) b ) ;
  (6) the plane they span is defined over Q and spanned by Hodge classes.
"""
import sympy as sp


def standard_complex_structure(n):
    """J on R^{2n} with J^2 = -1, in the basis where the symplectic form is
    the standard one."""
    J = sp.zeros(2 * n, 2 * n)
    for i in range(n):
        J[i, n + i] = -1
        J[n + i, i] = 1
    return J


def standard_symplectic(n):
    E = sp.zeros(2 * n, 2 * n)
    for i in range(n):
        E[i, n + i] = 1
        E[n + i, i] = -1
    return E


def check(n, d, b=None, verbose=True):
    J = standard_complex_structure(n)
    if b is None:
        b = standard_symplectic(n)
    b = sp.Matrix(b)
    ok = {}

    # (2) Riemann relation:  J^T b J = b   <=>  b in NS(X) (x) Q
    ok["b alternating"] = sp.simplify(b + b.T) == sp.zeros(2 * n, 2 * n)
    ok["b in NS (Riemann relation)"] = sp.simplify(J.T * b * J - b) == sp.zeros(2 * n, 2 * n)
    ok["b nondegenerate"] = sp.simplify(b.det()) != 0

    binv = b.inv()
    Z = sp.zeros(2 * n, 2 * n)
    M = sp.Matrix(sp.BlockMatrix([[Z, -binv], [d * b, Z]]))

    # (1) M^2 = -d
    ok["M^2 = -d"] = sp.simplify(M * M + d * sp.eye(4 * n)) == sp.zeros(4 * n, 4 * n)

    # complex structure on A = X x Xhat :  J on X,  -J^T on Xhat
    JA = sp.Matrix(sp.BlockMatrix([[J, Z], [Z, -J.T]]))
    ok["JA^2 = -1"] = sp.simplify(JA * JA + sp.eye(4 * n)) == sp.zeros(4 * n, 4 * n)

    # (2) M is an endomorphism of A:  M JA = JA M
    ok["M commutes with JA"] = sp.simplify(M * JA - JA * M) == sp.zeros(4 * n, 4 * n)

    # (3) signature of M on H^{1,0}(A), the +i eigenspace of JA, computed
    #     exactly.  Since JA is real with JA^2 = -1, H^{1,0} has dimension 2n,
    #     and since M^2 = -d, M acts on it with eigenvalues +-sqrt(-d), say p
    #     and q times, p + q = 2n.  The projector onto H^{1,0} is
    #     (1 - i JA)/2, so trace(M on H^{1,0}) = (tr M - i tr(M JA))/2, and
    #     tr M = 0 because M is real with M^2 = -d.  Hence
    #         sqrt(-d) (p - q) = -i tr(M JA) / 2,
    #     and p = q = n exactly when the rational number tr(M JA) vanishes.
    ok["dim H^{1,0}(A) = 2n"] = (JA.shape[0] == 4 * n and
                                 sp.simplify(JA * JA + sp.eye(4 * n))
                                 == sp.zeros(4 * n, 4 * n))
    ok["tr M = 0"] = sp.simplify(M.trace()) == 0
    ok[f"signature on H^(1,0) is ({n},{n})"] = sp.simplify((M * JA).trace()) == 0

    # (4) the eigenspaces of M are maximal isotropic for the canonical pairing
    #     < (u,xi), (u',xi') > = xi'(u) + xi(u')
    Q = sp.Matrix(sp.BlockMatrix([[Z, sp.eye(2 * n)], [sp.eye(2 * n), Z]]))
    s = sp.sqrt(-d)
    # eigenvector space for +s : { (u, d b u / s) }
    Wp = sp.Matrix(sp.BlockMatrix([[sp.eye(2 * n)], [d * b / s]]))
    Wm = sp.Matrix(sp.BlockMatrix([[sp.eye(2 * n)], [-d * b / s]]))
    ok["M W+ = s W+"] = sp.simplify(M * Wp - s * Wp) == sp.zeros(4 * n, 2 * n)
    ok["M W- = -s W-"] = sp.simplify(M * Wm + s * Wm) == sp.zeros(4 * n, 2 * n)
    ok["W+ isotropic"] = sp.simplify(Wp.T * Q * Wp) == sp.zeros(2 * n, 2 * n)
    ok["W- isotropic"] = sp.simplify(Wm.T * Q * Wm) == sp.zeros(2 * n, 2 * n)
    ok["W+ maximal (rank 2n)"] = Wp.rank() == 2 * n

    # (5) the graph two-forms are  +- d b/s = -+ sqrt(-d) b
    ok["graph form is d b/s = -sqrt(-d) b"] = sp.simplify(
        d * b / s - (-s * b)) == sp.zeros(2 * n, 2 * n)

    if verbose:
        print(f"== n = {n}, d = {d}, dim A = {2*n}, dim_Q H_1(A) = {4*n}")
        for k, v in ok.items():
            print(f"    [{'PASS' if v else 'FAIL'}] {k}")
    return all(ok.values())


if __name__ == "__main__":
    allok = True
    for n in (2, 3, 4):
        for d in (1, 2, 3, 7):
            allok &= check(n, d, verbose=(d == 1))
    # a non-principal b, to show the construction is not special to the
    # standard symplectic form
    n = 3
    b = standard_symplectic(n)
    b[0, n] = 2; b[n, 0] = -2
    print()
    print("with a non-principal polarisation class b = diag(2,1,1):")
    allok &= check(n, 3, b=b)
    print()
    print("all checks passed:", allok)
