import sys, random, time, numpy as np
import fourpartite as fp

def affine_violations(cfg):
    """Necessary condition for first-order extension along all polarised deformations:
    for every plane (edge u-w between parts i,j) and each other part k, u or w must have
    a neighbour in part k (then the smooth part of the plane is affine)."""
    k = cfg.k; A = cfg.A
    def nbrs(part, v, other):
        i, j = min(part, other), max(part, other)
        M = A[(i, j)]
        row = M[v, :] if part == i else M[:, v]
        return row.sum() > 0
    bad = 0
    for (i, j) in fp.PAIRS:
        others = [t for t in range(4) if t not in (i, j)]
        for u, w in np.argwhere(A[(i, j)] == 1):
            for t in others:
                if not (nbrs(i, u, t) or nbrs(j, w, t)):
                    bad += 1
    return bad

def target_E(E, b):
    return E, 2*b*E, E*(4*b*b - E)

def score_E(cfg, E, b, w_cm=50, w_aff=0):
    e, T, chi, bad = cfg.invariants()
    EE, TT, CHI = target_E(E, b)
    s = sum(abs(e[p]-EE) for p in fp.PAIRS)*5 + sum(abs(T[t]-TT) for t in fp.TRIPLES) + abs(chi-CHI) + w_cm*bad
    aff = affine_violations(cfg) if w_aff else 0
    return s + w_aff*aff, (e, T, chi, bad, aff)

def anneal_E(k, E, b, iters, rng, w_aff, T0=3.0, T1=0.05):
    cfg = fp.random_config(k, E, rng)
    cur, info = score_E(cfg, E, b, w_aff=w_aff)
    best, bestA, bestinfo = cur, {p: cfg.A[p].copy() for p in fp.PAIRS}, info
    for it in range(iters):
        temp = T0*(T1/T0)**(it/max(1,iters-1))
        p = rng.choice(fp.PAIRS); M = cfg.A[p]
        ones = np.argwhere(M==1); zeros = np.argwhere(M==0)
        if len(ones)==0 or len(zeros)==0: continue
        o = tuple(ones[rng.randrange(len(ones))]); z = tuple(zeros[rng.randrange(len(zeros))])
        M[o]=0; M[z]=1
        new, ninfo = score_E(cfg, E, b, w_aff=w_aff)
        if new <= cur or rng.random() < np.exp((cur-new)/temp):
            cur, info = new, ninfo
            if cur < best:
                best, bestA, bestinfo = cur, {q: cfg.A[q].copy() for q in fp.PAIRS}, info
                if best == 0: break
        else:
            M[o]=1; M[z]=0
    return best, fp.Config(k, bestA), bestinfo

if __name__ == "__main__":
    b = int(sys.argv[1]); d = int(sys.argv[2]); E = b*b + d
    ks = [tuple(int(x) for x in s.split(',')) for s in sys.argv[3].split(';')]
    restarts = int(sys.argv[4]); iters = int(sys.argv[5]); w_aff = int(sys.argv[6])
    rng = random.Random(int(sys.argv[7]) if len(sys.argv)>7 else 0)
    print(f"b={b} d={d}: E={E} T={2*b*E} chi={E*(4*b*b-E)}  (affine weight {w_aff})")
    for k in ks:
        if any(k[i]*k[j] < E for i,j in fp.PAIRS):
            print(" parts", k, "too small"); continue
        t0=time.time(); best=None
        for r in range(restarts):
            s, cfg, info = anneal_E(list(k), E, b, iters, rng, w_aff)
            if best is None or s < best[0]: best=(s,cfg,info)
            if s == 0: break
        print(f" parts {k}: best score {best[0]} info(e,T,chi,badCM,aff) {best[2]}  [{time.time()-t0:.0f}s]", flush=True)
        if best[0]==0:
            print(" EXACT SOLUTION:")
            for p in fp.PAIRS: print(p, best[1].A[p].tolist())
