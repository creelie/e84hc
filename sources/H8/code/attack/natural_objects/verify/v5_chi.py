#!/usr/bin/env python3
"""v5_chi.py -- intersection numbers used in the T4 example (n=4):
int [B_i][B_j] = (p_i q_j - p_j q_i)^8, int [B] eta^4/4! = (d p^2 + q^2)^4,
int eta^8/8! = d^4 (so chi(O(t eta)) = t^8 d^4)."""
from itertools import combinations
from math import factorial
from v4lib import Model, wedge, pw
for d in (1, 2):
    Mo = Model(4, d)
    eta = Mo.eta()
    pts = [(1, -3), (1, -2), (1, 2), (1, 3), (2, -1), (2, 1), (3, -1), (3, 1)]
    Bs = {pq: Mo.subtorus_track(*pq) for pq in pts}
    ok1 = all(abs(Mo.integral(wedge(Bs[a], Bs[b]))) == abs(a[0]*b[1]-a[1]*b[0])**8 for a, b in combinations(pts, 2))
    e4 = pw(eta, 4)
    ok2 = all(Mo.integral(wedge(Bs[a], e4)) == factorial(4) * (d*a[0]**2 + a[1]**2)**4 for a in pts)
    ok3 = Mo.integral(pw(eta, 8)) == factorial(8) * d**4
    print("d=%d: |int B_i B_j| = |det|^8: %s ; int B eta^4 = 4!(dp^2+q^2)^4: %s ; int eta^8 = 8! d^4: %s" % (d, ok1, ok2, ok3))
