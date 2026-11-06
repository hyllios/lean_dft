"""Leading strong-potential amplitude A_xc(u) = sum over shortest config-graph paths x->c of
prod(hoppings)/prod_{y on path, y != x}(d_x - d_y), d_y = n(y).u. Check whether it can vanish identically."""
import numpy as np, networkx as nx, hk_census as h
from multiprocessing import Pool
def analyse(job):
    gid, N = job; G = nx.graph_atlas(gid); basis, H0, occ = h.many_body(G, N, 0.0); L = len(basis)
    CG = nx.Graph(); CG.add_nodes_from(range(L))
    CG.add_edges_from((a, b) for a in range(L) for b in range(a+1, L) if H0[a, b] != 0)
    rng = np.random.default_rng(gid); U = [rng.normal(size=G.number_of_nodes()) for _ in range(3)]
    zero = []
    for x in range(L):
        dist = nx.single_source_shortest_path_length(CG, x)
        for c in range(L):
            if c == x: continue
            vals = []
            for u in U:
                d = occ.T @ u; amp = {x: 1.0}       # dynamic programming over distance layers
                for layer in range(1, dist[c] + 1):
                    for y in [z for z in range(L) if dist[z] == layer]:
                        amp[y] = sum(amp[p]*H0[y, p] for p in CG[y] if dist[p] == layer - 1)/(d[x] - d[y])
                vals.append(amp[c]*np.prod([1.0]))  # normalised enough
            if max(abs(v) for v in vals) < 1e-12: zero.append((basis[x], basis[c], dist[c]))
    return gid, N, sorted(G.edges()), zero
if __name__ == '__main__':
    jobs = [(g, N) for g in range(1, 1253) if 2 <= nx.graph_atlas(g).number_of_nodes() <= 6 and nx.is_connected(nx.graph_atlas(g))
            for N in range(1, nx.graph_atlas(g).number_of_nodes())]
    with Pool(8) as p: R = p.map(analyse, jobs, chunksize=10)
    bad = [r for r in R if r[3]]
    print(len(R), 'cases;', len(bad), 'with identically-vanishing leading amplitude')
    for r in bad[:15]: print(r[0], 'N', r[1], r[2], 'e.g.', r[3][:3], '(#', len(r[3]), ')')
