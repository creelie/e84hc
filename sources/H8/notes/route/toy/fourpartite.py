"""
Reduced unions of coordinate abelian surfaces in X = E_1 x E_2 x E_3 x E_4.

A configuration is a 4-partite graph G on parts C_1..C_4 (fibre sets, |C_i| = k_i):
an edge (c_i, c_j) between parts i and j is the abelian surface
    P_{ij}(c_i, c_j) = { x_i = c_i, x_j = c_j } = pr_i^{-1}(c_i) cap pr_j^{-1}(c_j),
of class theta_i theta_j.  Z = union of all these surfaces (reduced).

Facts used (all elementary, proved in the note):
 * Mayer-Vietoris for the primary components is exact (monomial ideals distribute),
   so ch(O_Z) = sum over nonempty compatible sets T of planes of (-1)^{|T|+1} nu_T theta_{supp T},
   and for reduced planes nu_T = 1.  Hence, with e_ij = #edges between parts i and j,
     ch_2(O_Z) = sum_{i<j} e_ij theta_i theta_j,
     ch_3(O_Z) = - sum_{ijk} T_ijk theta_i theta_j theta_k,
       T_ijk = sum over transversal triples (c_i,c_j,c_k) of g(#edges), g(2)=1, g(3)=2, g(0)=g(1)=0
             = #cherries spanning parts {i,j,k} - #transversal triangles,
     chi(O_Z) = sum over transversal 4-tuples of chi_loc(induced graph),
       chi_loc(H) = - sum_{I independent in H} (-1)^{|I|}   (H on the 4 chosen vertices).
 * Z is Cohen-Macaulay at the point (c_1,..,c_4) iff the induced graph on these four vertices,
   restricted to its non-isolated vertices, is connected (Reisner for the 1-dimensional
   Stanley-Reisner complex of free coordinate pairs; the edge-complement bijection on K_4
   preserves connectivity).  Elsewhere Z is CM automatically (localisation).
 * Target (secant object I_Z(b Theta) with ch = u + b v, N = (b^2+d)/2, Theta = sum theta_i):
     e_ij = 2N for all six pairs,   T_ijk = 4 b N for all four triples,
     chi = 4 N (2 b^2 - N),   d = 2N - b^2 > 0.
   (Theta^2 = 2 sum theta_i theta_j, Theta^3 = 6 sum theta_i theta_j theta_k, Theta^4 = 24 pt.)
"""
import numpy as np
import itertools, sys, random, time

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
TRIPLES = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]

def cm_table():
    """pattern (6 bits, bit p = edge PAIRS[p] present) -> True iff induced graph on 4 vertices
    has at most one nontrivial connected component."""
    tab = np.zeros(64, dtype=bool)
    for pat in range(64):
        edges = [PAIRS[p] for p in range(6) if pat >> p & 1]
        verts = set(v for e in edges for v in e)
        if not verts:
            tab[pat] = True; continue
        # union-find on verts
        parent = {v: v for v in verts}
        def find(v):
            while parent[v] != v:
                parent[v] = parent[parent[v]]; v = parent[v]
            return v
        for a, b in edges:
            parent[find(a)] = find(b)
        tab[pat] = len({find(v) for v in verts}) == 1
    return tab

def chiloc_table():
    """pattern -> chi_loc = -sum_{I independent} (-1)^|I| over the 4 vertices."""
    tab = np.zeros(64, dtype=np.int64)
    for pat in range(64):
        edges = {PAIRS[p] for p in range(6) if pat >> p & 1}
        s = 0
        for r in range(5):
            for I in itertools.combinations(range(4), r):
                if all((a, b) not in edges for a, b in itertools.combinations(I, 2)):
                    s += (-1) ** r
        tab[pat] = -s
    return tab

CM = cm_table()
CHILOC = chiloc_table()

class Config:
    def __init__(self, k, A=None):
        self.k = list(k)
        self.A = A if A is not None else {p: np.zeros((k[p[0]], k[p[1]]), dtype=np.int64) for p in PAIRS}

    def pattern_tensor(self):
        """64-pattern index for every transversal 4-tuple, shape (k1,k2,k3,k4)."""
        k = self.k
        pat = np.zeros(tuple(k), dtype=np.int64)
        for p, (i, j) in enumerate(PAIRS):
            shape = [1, 1, 1, 1]; shape[i] = k[i]; shape[j] = k[j]
            pat += (self.A[(i, j)].reshape(shape) << p)
        return pat

    def invariants(self):
        k = self.k
        e = {p: int(self.A[p].sum()) for p in PAIRS}
        T = {}
        for (i, j, l) in TRIPLES:
            Aij, Ail, Ajl = self.A[(i, j)], self.A[(i, l)], self.A[(j, l)]
            cherries = (Aij.sum(1) * Ail.sum(1)).sum() + (Aij.sum(0) * Ajl.sum(1)).sum() + (Ail.sum(0) * Ajl.sum(0)).sum()
            tri = ((Aij @ Ajl) * Ail).sum()
            T[(i, j, l)] = int(cherries - tri)
        pat = self.pattern_tensor()
        chi = int(CHILOC[pat].sum())
        bad = int((~CM[pat]).sum())
        return e, T, chi, bad

def target(N, b):
    return 2 * N, 4 * b * N, 4 * N * (2 * b * b - N)

def score(cfg, N, b, w_cm=50):
    e, T, chi, bad = cfg.invariants()
    E, TT, CHI = target(N, b)
    s = sum(abs(e[p] - E) for p in PAIRS) * 5 + sum(abs(T[t] - TT) for t in TRIPLES) + abs(chi - CHI) + w_cm * bad
    return s, (e, T, chi, bad)

def random_config(k, E, rng):
    cfg = Config(k)
    for (i, j) in PAIRS:
        cells = [(a, b) for a in range(k[i]) for b in range(k[j])]
        for a, b in rng.sample(cells, E):
            cfg.A[(i, j)][a, b] = 1
    return cfg

def anneal(k, N, b, iters, rng, T0=3.0, T1=0.05, seed_cfg=None, verbose=False):
    E, TT, CHI = target(N, b)
    cfg = seed_cfg if seed_cfg is not None else random_config(k, E, rng)
    cur, info = score(cfg, N, b)
    best, bestcfg, bestinfo = cur, {p: cfg.A[p].copy() for p in PAIRS}, info
    for it in range(iters):
        temp = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        p = rng.choice(PAIRS)
        M = cfg.A[p]
        ones = np.argwhere(M == 1); zeros = np.argwhere(M == 0)
        if len(ones) == 0 or len(zeros) == 0: continue
        o = tuple(ones[rng.randrange(len(ones))]); z = tuple(zeros[rng.randrange(len(zeros))])
        M[o] = 0; M[z] = 1
        new, ninfo = score(cfg, N, b)
        if new <= cur or rng.random() < np.exp((cur - new) / temp):
            cur, info = new, ninfo
            if cur < best:
                best, bestcfg, bestinfo = cur, {q: cfg.A[q].copy() for q in PAIRS}, info
                if verbose: print(f"  it={it} best={best} info={bestinfo}")
                if best == 0: break
        else:
            M[o] = 1; M[z] = 0
    return best, Config(k, bestcfg), bestinfo

if __name__ == "__main__":
    # usage: fourpartite.py N b k1 k2 k3 k4 [restarts] [iters]
    N, b = int(sys.argv[1]), int(sys.argv[2])
    k = [int(x) for x in sys.argv[3:7]]
    restarts = int(sys.argv[7]) if len(sys.argv) > 7 else 20
    iters = int(sys.argv[8]) if len(sys.argv) > 8 else 20000
    d = 2 * N - b * b
    print(f"target: N={N} b={b} d={d}  e_ij={2*N} T_ijk={4*b*N} chi={4*N*(2*b*b-N)}  parts={k}")
    rng = random.Random(1)
    t0 = time.time()
    overall = None
    for r in range(restarts):
        best, cfg, info = anneal(k, N, b, iters, rng)
        print(f"restart {r}: best score {best}  (e,T,chi,badCM) = {info}   [{time.time()-t0:.0f}s]")
        if overall is None or best < overall[0]:
            overall = (best, cfg, info)
        if best == 0:
            print("EXACT SOLUTION FOUND")
            for p in PAIRS:
                print(p); print(cfg.A[p])
            break
    print("best overall:", overall[0], overall[2])
