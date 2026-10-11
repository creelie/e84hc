"""Interval certificates for the two block families of degree 51 (Propositions "prop:family51a"
and "prop:family51b"), in ball arithmetic (python-flint / Arb).  The code is that of
family52_certificate.py, which works for any block family; the families and the points are read
from family51a_point.json and family51b_point.json.  The checks are the same: Krawczyk on a box of
radius 1e-95, (B1) on the box, and an enclosure of the residue functional that excludes 0.
"""
import os
import sys

from family52_certificate import certify

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    paths = sys.argv[1:] or [os.path.join(here, f) for f in ("family51a_point.json", "family51b_point.json")]
    for path in paths:
        certify(path, int(os.environ.get("FAMILY51_PREC", "1000")))
        print()
