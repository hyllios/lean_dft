"""Hypothesis (H*): there is a potential v* at which H(v*) has simple spectrum and EVERY eigenvector is nonzero on
EVERY configuration. Test with random v on all connected graphs M<=7, all 1<=N<=M/2, U in {0,1}."""
import numpy as np, networkx as nx, hk_census as h
from multiprocessing import Pool
def test(job):
    gid, N, U = job; G = nx.graph_atlas(gid); basis, H0, occ = h.many_body(G, N, U); rng = np.random.default_rng(gid*10+N)
    best = (0, 0)
    for _ in range(5):
        v = rng.normal(size=G.number_of_nodes()); e, Uv = np.linalg.eigh(H0 + np.diag(occ.T @ v))
        q = (np.min(np.diff(e)) if len(e) > 1 else 1, np.min(np.abs(Uv)))
        if min(q) > min(best): best = q
    return gid, N, U, G.number_of_nodes(), len(basis), best
if __name__ == '__main__':
    jobs = [(g, N, U) for g in range(1, 1253) if nx.graph_atlas(g).number_of_nodes() >= 2 and nx.is_connected(nx.graph_atlas(g))
            for N in range(1, nx.graph_atlas(g).number_of_nodes()//2 + 1) for U in (0.0, 1.0)]
    with Pool(8) as p: R = p.map(test, jobs, chunksize=20)
    bad = [r for r in R if min(r[5]) < 1e-7]
    print(len(R), 'cases tested;', len(bad), 'fail (H*) numerically')
    for r in bad[:40]: print(r[:5], 'gap %.2e  min|psi| %.2e' % r[5], sorted(nx.graph_atlas(r[0]).edges()))
    print('weakest passing case:', min((min(r[5]), r[:5]) for r in R if min(r[5]) >= 1e-7))
