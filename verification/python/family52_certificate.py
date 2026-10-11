"""Interval certificates for the two block families of degree 52 (Propositions "prop:family52a"
and "prop:family52b"), in ball arithmetic (python-flint / Arb).  The same code works for any
block family; the family and the point are read from family52a_point.json and family52b_point.json.

A family is given by m, the character alpha (entries in 1..m-1, sum 2m), and blocks
(name, exponents e_0..e_4, kind, data):
  kind 'inf'    the block t (the point at infinity); in the coordinate s it is 1;
  kind 'fixed'  a fixed polynomial in s, data = coefficients from s^0 up;
  kind 'monic'  s^d + (unknown lower coefficients), data = d;
  kind 'monic1' s^d + (unknowns at s^1..s^(d-1)) + 1, data = d.
The coefficients c_k are unknowns except c_knorm = 1.  The unknown vector is
(block coefficients in the order of the blocks, then the c_k), and the coordinate with index
'par' is the parameter kappa, held fixed.  E(x, kappa) is the list of coefficients of
sum_k u_k(s, 1) in degrees 0..D.

Checks at kappa0:
  (1) Krawczyk: a unique zero x* of E(., kappa0) in a box of radius 1e-95, with J_x invertible;
  (2) on the box: every c_k is nonzero, and the blocks are pairwise coprime (resultants of the
      finite blocks, and leading coefficients for the block t);                         [(B1)]
  (3) with v = (xdot, kappadot = 1), xdot = -J_x^{-1} dE/dkappa, the sum of the residues of eta_v
      over C, which is I_ij for the chart (i, j) when the pole condition below holds, is enclosed
      in a ball not containing 0.  It is [w^1] f(1/w) for eta_v = f(s) ds, computed by exact
      series division.
The exact (integer) conditions (B2), the chart condition and the pole condition of
Lemma etapoles(a) are checked first.
"""
import json
import os
import sys
from fractions import Fraction
from flint import acb, arb, acb_poly, acb_mat, ctx

S_ = acb_poly([0, 1])


class Family:
    def __init__(self, spec):
        self.m = spec["m"]; self.alpha = spec["alpha"]; self.knorm = spec["knorm"]
        self.blocks = spec["blocks"]; self.chart = tuple(spec["chart"])
        self.slots = []                       # (block index, power of s) for each block unknown
        for bi, (name, e, kind, data) in enumerate(self.blocks):
            if kind == "monic":
                self.slots += [(bi, n) for n in range(data)]
            elif kind == "monic1":
                self.slots += [(bi, n) for n in range(1, data)]
        self.nb = len(self.slots)
        self.cidx = [k for k in range(5) if k != self.knorm]
        self.nall = self.nb + len(self.cidx)
        self.par = spec["par"]
        self.D = self.degree()
        self.N = self.D + 1
        assert self.nall - 1 == self.N, (self.nall, self.N)

    def bdeg(self, bi):
        name, e, kind, data = self.blocks[bi]
        if kind == "inf":
            return 1
        if kind == "fixed":
            return len(data) - 1
        return data

    def degree(self):
        degs = [sum(e[k] * self.bdeg(bi) for bi, (_, e, _, _) in enumerate(self.blocks)) for k in range(5)]
        assert len(set(degs)) == 1, degs
        return degs[0]

    def exact_checks(self):
        """(B2), the chart condition and the pole condition, all in integers."""
        m, al = self.m, self.alpha
        assert sum(al) == 2 * m and all(0 < a < m for a in al)
        out = []
        for name, e, kind, data in self.blocks:
            w = sum(a * x for a, x in zip(al, e))
            assert w % m == 0, name
            assert any(e) and not all(e), name
            out.append((name, tuple(e), w))
        i, j = self.chart
        for name, e, kind, data in self.blocks:
            assert not (e[i] and e[j]), "chart: block %s in u_i and u_j" % name
            if e[i]:
                assert kind != "inf", "chart: block of u_i vanishes at infinity"
            if kind != "inf" and not e[i]:
                w = sum(a * x for a, x in zip(al, e))
                assert w // m - 1 - e[j] >= 0, "pole at a zero of %s" % name
        return out

    def split(self, z):
        """z: full vector of all unknowns (parameter included), as acb."""
        polys = []
        pos = 0
        for bi, (name, e, kind, data) in enumerate(self.blocks):
            if kind == "inf":
                polys.append(acb_poly([1]))
            elif kind == "fixed":
                polys.append(acb_poly([acb(c) for c in data]))
            elif kind == "monic":
                polys.append(acb_poly(list(z[pos:pos + data]) + [acb(1)])); pos += data
            else:
                polys.append(acb_poly([acb(1)] + list(z[pos:pos + data - 1]) + [acb(1)])); pos += data - 1
        c = [acb(1)] * 5
        for n, k in enumerate(self.cidx):
            c[k] = z[self.nb + n]
        return polys, c

    def full(self, x, kappa):
        return list(x[:self.par]) + [kappa] + list(x[self.par:])

    def us(self, polys, c):
        out = []
        for k in range(5):
            f = acb_poly([c[k]])
            for bi, (_, e, _, _) in enumerate(self.blocks):
                if e[k]:
                    f = f * polys[bi] ** e[k]
            out.append(f)
        return out

    def coeffs(self, p, n):
        cs = p.coeffs()
        return [cs[i] if i < len(cs) else acb(0) for i in range(n)]

    def E(self, x, kappa):
        polys, c = self.split(self.full(x, kappa))
        return self.coeffs(sum(self.us(polys, c), acb_poly([0])), self.N)

    def dpolys(self, polys, c):
        """For every unknown of the full vector, the list (du_0, ..., du_4) of partial derivatives."""
        cols = []
        for (bi, n) in self.slots:
            d = []
            for k in range(5):
                ek = self.blocks[bi][1][k]
                if ek == 0:
                    d.append(acb_poly([0])); continue
                f = acb_poly([c[k] * ek]) * polys[bi] ** (ek - 1) * S_ ** n
                for bj, (_, e, _, _) in enumerate(self.blocks):
                    if bj != bi and e[k]:
                        f = f * polys[bj] ** e[k]
                d.append(f)
            cols.append(d)
        for k0 in self.cidx:
            d = []
            for k in range(5):
                if k != k0:
                    d.append(acb_poly([0])); continue
                f = acb_poly([1])
                for bj, (_, e, _, _) in enumerate(self.blocks):
                    if e[k]:
                        f = f * polys[bj] ** e[k]
                d.append(f)
            cols.append(d)
        return cols

    def jac(self, x, kappa):
        """N x N Jacobian in the unknowns other than kappa, and the column d/dkappa."""
        polys, c = self.split(self.full(x, kappa))
        cols = self.dpolys(polys, c)
        J = acb_mat(self.N, self.N); jk = None
        col = 0
        for idx, d in enumerate(cols):
            cs = self.coeffs(sum(d, acb_poly([0])), self.N)
            if idx == self.par:
                jk = cs; continue
            for r in range(self.N):
                J[r, col] = cs[r]
            col += 1
        return J, jk

    def residue_sum(self, x, kappa):
        J, jk = self.jac(x, kappa)
        xd = J.solve(acb_mat([[-v] for v in jk]))
        xd = [xd[k, 0] for k in range(self.N)]
        vd = self.full(xd, acb(1))
        z = self.full(x, kappa)
        polys, c = self.split(z)
        u = self.us(polys, c)
        cols = self.dpolys(polys, c)
        ud = [sum((cols[n][k] * vd[n] for n in range(self.nall)), acb_poly([0])) for k in range(5)]
        i, j = self.chart
        a, b, cc = [k for k in range(5) if k not in (i, j)]
        d = [p.derivative() for p in u]
        Nv = (u[a] * (ud[b] * d[cc] - ud[cc] * d[b]) - u[b] * (ud[a] * d[cc] - ud[cc] * d[a])
              + u[cc] * (ud[a] * d[b] - ud[b] * d[a]))
        # eta_v = A N_v / (u_0 ... u_4) ds; collect the block powers.
        num = Nv; den = acb_poly([c[0] * c[1] * c[2] * c[3] * c[4]])
        for bi, (name, e, kind, data) in enumerate(self.blocks):
            if kind == "inf":
                continue
            w = sum(al * x_ for al, x_ in zip(self.alpha, e)) // self.m
            n = sum(e) - w
            if n > 0:
                den = den * polys[bi] ** n
            elif n < 0:
                num = num * polys[bi] ** (-n)
        dn = num.degree(); dd = den.degree()
        revN = list(reversed(self.coeffs(num, dn + 1)))
        revD = list(reversed(self.coeffs(den, dd + 1)))
        k = 1 + dn - dd
        if k < 0:
            return acb(0), xd
        return series_div(revN, revD, k + 1)[k], xd


def sylvester(p, q):
    p = p.coeffs(); q = q.coeffs(); m, n = len(p) - 1, len(q) - 1
    if m == 0 or n == 0:
        return (p[0] ** n) * (q[0] ** m)
    M = acb_mat(m + n, m + n)
    for i in range(n):
        for j, c in enumerate(reversed(p)):
            M[i, i + j] = c
    for i in range(m):
        for j, c in enumerate(reversed(q)):
            M[n + i, i + j] = c
    return M.det()


def series_div(a, b, n):
    a = a + [acb(0)] * max(0, n - len(a)); b = b + [acb(0)] * max(0, n - len(b))
    out = []
    inv = 1 / b[0]
    for k in range(n):
        t = a[k] - sum((b[j] * out[k - j] for j in range(1, k + 1)), acb(0))
        out.append(t * inv)
    return out


def load_point(path):
    d = json.load(open(path))
    kr, ki = (Fraction(t) for t in d["kappa0"])
    kappa = acb(arb(kr.numerator) / kr.denominator, arb(ki.numerator) / ki.denominator)
    xt = [acb(arb(re), arb(im)) for re, im in d["x"]]
    return d["spec"], kappa, xt


def certify(path, prec=1000, rad="1e-95"):
    ctx.prec = prec
    spec, kappa, xt = load_point(path)
    F = Family(spec)
    print("family:", spec["name"], " m =", F.m, " alpha =", tuple(F.alpha), " D =", F.D,
          " unknowns:", F.N, " chart:", F.chart)
    for name, e, w in F.exact_checks():
        print("    block %-3s exponents %s weight %d = %d m" % (name, e, w, w // F.m))
    print("(0) (B2), chart and pole conditions: exact, passed")
    N = F.N
    r = arb(rad)
    X = [z + acb(arb(0, r), arb(0, r)) for z in xt]
    Jm, _ = F.jac(xt, kappa)
    Y = acb_mat([[Jm[i, k].mid() for k in range(N)] for i in range(N)]).inv()
    Y = acb_mat([[Y[i, k].mid() for k in range(N)] for i in range(N)])
    Ex = acb_mat([[e] for e in F.E(xt, kappa)])
    JX, _ = F.jac(X, kappa)
    Id = acb_mat([[1 if i == k else 0 for k in range(N)] for i in range(N)])
    dX = acb_mat([[X[k] - xt[k]] for k in range(N)])
    Kx = acb_mat([[xt[k]] for k in range(N)]) - Y * Ex + (Id - Y * JX) * dX
    inside = True
    for k in range(N):
        for part in ("real", "imag"):
            kk = getattr(Kx[k, 0], part); xx = getattr(X[k], part)
            if not (kk.lower() > xx.lower() and kk.upper() < xx.upper()):
                inside = False
    krad = max(max(float(Kx[k, 0].real.rad()), float(Kx[k, 0].imag.rad())) for k in range(N))
    print("(1) Krawczyk K(X) inside X:", inside, "  max radius of K(X): %.2e (box radius %s)" % (krad, rad))
    assert inside
    polys, c = F.split(F.full(X, kappa))
    vals = {}
    for k in range(5):
        vals["c%d" % k] = c[k]
    fin = [(F.blocks[bi][0], p) for bi, p in enumerate(polys) if F.blocks[bi][2] != "inf"]
    for a in range(len(fin)):
        for b in range(a + 1, len(fin)):
            vals["Res(%s,%s)" % (fin[a][0], fin[b][0])] = sylvester(fin[a][1], fin[b][1])
    for name, p in fin:                       # the block t is coprime to a block of exact degree
        vals["lead(%s)" % name] = p.coeffs()[-1]
    for name, v in vals.items():
        ok = not v.contains(0)
        print("(2) %-12s nonzero: %s   |.| >= %s" % (name, ok, abs(v).lower().str(5, radius=False) if ok else "?"))
        assert ok
    I, xd = F.residue_sum(X, kappa)
    i, j = F.chart
    im = I.imag.mid().str(15, radius=False)
    print("(3) I_%d%d = %s %s %s i, radius of the real and imaginary parts < %.1e" % (
        i, j, I.real.mid().str(15, radius=False), "-" if im.startswith("-") else "+", im.lstrip("-"),
        max(float(I.real.rad()), float(I.imag.rad()))))
    print("    0 in I:", I.contains(0), "   |I| >=", abs(I).lower().str(8, radius=False))
    assert not I.contains(0)
    print("ALL CHECKS PASSED")
    return I


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    paths = sys.argv[1:] or [os.path.join(here, f) for f in ("family52a_point.json", "family52b_point.json")]
    for path in paths:
        certify(path, int(os.environ.get("FAMILY52_PREC", "1000")))
        print()
