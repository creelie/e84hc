"""Independent check of the residues in Propositions "prop:family51a" and "prop:family51b".

The same computation as family52_contour.py, at the points of family51a_point.json and
family51b_point.json: in 40-digit arithmetic (mpmath), the integral of eta_v / (2 pi i) over a
large circle (the sum of all residues in C) and the sum of the integrals over small circles
around the zeros of u_i only (which is I_ij) agree, and they agree with the certificate.
"""
import os

import mpmath as mp

from family52_contour import run

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    for f in ("family51a_point.json", "family51b_point.json"):
        big, small = run(os.path.join(here, f))
        assert abs(big - small) < mp.mpf("1e-20") * (1 + abs(big))
