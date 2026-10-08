#!/usr/bin/env python3
"""v_binomial_9296.py -- the binomial shapes of rank 92 and 96 (T1 claim 9(iii)).

Reconstructed when the round-12 scripts were packaged: the verifier produced
transcripts/v_binomial_9296.log with a command that was not saved.  This
script prints the same lines.  It uses the verifier's model v_ann.py
unchanged.

For omega = 2 vol_0 + 3 vol_1 + 5 vol_2 + 7 vol_3 (the coefficients of
t1_shapes_explore.py and v_binomial.py) it lists the pairs of monomials
m1 < m2 in theta_0^i theta_1^j (0 <= i, j <= 4) for which
r(omega + m1 + m2) is 92 or 96 (12 of the 300 pairs), and then recomputes
r(omega + theta_1^2 + theta_0^2) and r(omega + theta_1 + theta_0^2) for a
second coefficient vector of omega.  Exact over Q."""
import itertools
from fractions import Fraction as Fr
from v_ann import gamma_of, rank, THP

cs = [Fr(2), Fr(3), Fr(5), Fr(7)]
for m1, m2 in itertools.combinations(sorted(THP), 2):
    r = rank(gamma_of(cs, {m1: Fr(1), m2: Fr(1)}))
    if r in (92, 96):
        print(m1, m2, r)
cs2 = [Fr(2), Fr(-3), Fr(5, 7), Fr(11)]
r96 = rank(gamma_of(cs2, {(0, 2): Fr(1), (2, 0): Fr(1)}))
r92 = rank(gamma_of(cs2, {(0, 1): Fr(1), (2, 0): Fr(1)}))
print("generic omega coeffs:", r96, r92)
