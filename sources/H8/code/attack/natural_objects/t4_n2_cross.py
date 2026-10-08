#!/usr/bin/env python3
"""
t4_n2_cross.py -- cross-check of the minimal-configuration bound against the
paper's exhaustive n = 2 search (code/semiregularity.py, signed_search, item
XIII): every signed tuple of <= 4 line bundles a beta + b betahat + c ell,
|a|,|b|,|c| <= 3, with flat Chern character and nonzero Weil part.
Prediction (s >= 2n): no tuple with < 4 Lagrangians off C_theta.  Also
recorded: whether the 4 Pluecker points span a plane through l_W (conic
through L_+-), and whether the Chern character is a pure Weil class.

Usage: t4_n2_cross.py [box [d ...]].  The default, box 3 and d = 1, 2, is the
run of transcripts/n2_cross.log (about four minutes); attack_checks.py runs
the smaller box 2 (about half a minute).
"""
import sys, os
sys.dont_write_bytecode = True
# the repository's code/ directory, two levels above this file
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
import io, contextlib
import semiregularity as SR
from fractions import Fraction as Fr
from ext import Split, exp_class, add, scale, power, Echelon, wedge
from lg import L_S

BOX = int(sys.argv[1]) if len(sys.argv) > 1 else 3
DS = [int(a) for a in sys.argv[2:]] or [1, 2]

for d in DS:
    with contextlib.redirect_stdout(io.StringIO()):
        mod, eta, w1, w2, found = SR.signed_search(2, d, box=BOX, smax=4, verbose=False, cap=2000000)
    weil = []
    for c in found:
        wp = SR.signed_weil_part(mod, eta, w1, w2, c)
        if wp is not None and (wp[1] != 0 or wp[2] != 0):
            weil.append(c)
    S = Split(2, d)
    b, bh, l = S.beta(), S.betahat(), S.ell()
    etaS = S.eta()
    ReL, ImL = (0, 0, d, 1, 0), (0, 0, 0, 0, 1)
    sizes = {}
    onconic = 0
    pure = 0
    offCtheta = 0
    for c in weil:
        pts = [L_S(t[0], -t[2], t[1]) for (t, e) in c]
        # points on C_theta: S proportional to diag(d,1): a = d*b, c = 0
        nth = sum(1 for (t, e) in c if t[2] == 0 and t[0] == d * t[1])
        offCtheta += (len(c) - nth == 4)
        E = Echelon()
        for pv in pts + [ReL, ImL]:
            E.add({i: Fr(x) for i, x in enumerate(pv) if x})
        if E.rank() == 3:
            onconic += 1
        ch = {}
        for (t, e) in c:
            D = add(add(scale(b, t[0]), scale(bh, t[1])), scale(l, t[2]))
            ch = add(ch, exp_class(D, 8), 1, e)
        # pure Weil: all components outside degree 4 vanish and degree-4 part has no eta^2
        others = {k: v for k, v in ch.items() if bin(k).count('1') != 4}
        W1, W2 = S.weil_pair()
        E4 = Echelon()
        for v in (W1, W2):
            E4.add(v)
        deg4 = {k: v for k, v in ch.items() if bin(k).count('1') == 4}
        if not others and not E4.reduce(deg4):
            pure += 1
        sizes[len(c)] = sizes.get(len(c), 0) + 1
    tag = "n=2 d=%d" % d if BOX == 3 else "n=2 d=%d (box %d)" % (d, BOX)
    print("%s: %d Weil tuples, sizes %s; all four Lagrangians off C_theta: %d;"
          " on a conic through l_W: %d; pure Weil character: %d"
          % (tag, len(weil), sizes, offCtheta, onconic, pure))
