"""EXACT certificate of (H*) for every connected graph M<=7, 1<=N<=M/2, U in {0,1}:
find an integer potential v such that, for every configuration c, gcd(charpoly H(v), charpoly H(v) with row/col c
deleted) = 1 modulo a prime P. Since both polys are monic with integer coefficients, gcd=1 mod P => resultant != 0 mod P
=> resultant != 0 over Z => H(v) and its minor share no eigenvalue (over C)."""
import numpy as np, networkx as nx, hk_census as h, flint
from multiprocessing import Pool
P = 2305843009213693951  # 2^61 - 1, prime
def cert(job):
    gid, N, U = job; G = nx.graph_atlas(gid); basis, H0, occ = h.many_body(G, N, U); L = len(basis)
    rng = np.random.default_rng(gid*100 + N*10 + int(U))
    for attempt in range(10):
        v = rng.integers(-1000, 1001, size=G.number_of_nodes())
        H = np.rint(H0 + np.diag(occ.T @ v)).astype(np.int64)
        M = flint.nmod_mat(L, L, [int(x) % P for x in H.ravel()], P); p = M.charpoly()
        ok = True
        for c in range(L):
            keep = [i for i in range(L) if i != c]
            if not keep: continue
            Hc = H[np.ix_(keep, keep)]
            pc = flint.nmod_mat(L-1, L-1, [int(x) % P for x in Hc.ravel()], P).charpoly()
            if p.gcd(pc).degree() > 0: ok = False; break
        if ok: return gid, N, U, L, True, [int(x) for x in v]
    return gid, N, U, L, False, None
if __name__ == '__main__':
    import json
    jobs = [(g, N, U) for g in range(1, 1253) if nx.graph_atlas(g).number_of_nodes() >= 2 and nx.is_connected(nx.graph_atlas(g))
            for N in range(nx.graph_atlas(g).number_of_nodes()//2 + 1, nx.graph_atlas(g).number_of_nodes()) for U in (0.0, 1.0)]
    with Pool(8) as p: R = p.map(cert, jobs, chunksize=20)
    json.dump(R, open('data/hstar_certificates_upper.json', 'w'))
    bad = [r[:4] for r in R if not r[4]]
    print(len(R), 'cases;', len(R) - len(bad), 'certified exactly;', 'uncertified:', bad[:30])
