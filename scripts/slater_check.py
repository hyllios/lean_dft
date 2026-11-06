"""Check: many-body leading path sum A_xc(u) == sum_{optimal bijections pi} sign(pi) prod_i a(x_i -> c_pi(i))(u)
(up to overall sign), with a(.,.) the single-particle leading path sum."""
import numpy as np, networkx as nx, itertools, hk_census as h
def sp_sum(G, a, b, u):
    if a == b: return 1.0, 0
    dist = nx.single_source_shortest_path_length(G, a); amp = {a: 1.0}
    for layer in range(1, dist[b] + 1):
        for y in [z for z in G if dist[z] == layer]:
            amp[y] = sum(amp[p]*(-1.0) for p in G[y] if dist[p] == layer - 1)/(u[a] - u[y])
    return amp[b], dist[b]
def mb_sum(G, N, x, c, u):
    basis, H0, occ = h.many_body(G, N, 0.0); L = len(basis); X, Cc = basis.index(x), basis.index(c)
    CG = nx.Graph(); CG.add_edges_from((p, q) for p in range(L) for q in range(p+1, L) if H0[p, q] != 0)
    d = occ.T @ u; dist = nx.single_source_shortest_path_length(CG, X); amp = {X: 1.0}
    for layer in range(1, dist[Cc] + 1):
        for y in [z for z in range(L) if dist[z] == layer]:
            amp[y] = sum(amp[p]*H0[y, p] for p in CG[y] if dist[p] == layer - 1)/(d[X] - d[y])
    return amp[Cc], dist[Cc]
def perm_sign(p):
    s = 1; p = list(p)
    for i in range(len(p)):
        while p[i] != i: j = p[i]; p[i], p[j] = p[j], p[i]; s = -s
    return s
def slater_sum(G, x, c, u):
    best = None; tot = 0.0
    for p in itertools.permutations(range(len(x))):
        vals = [sp_sum(G, x[i], c[p[i]], u) for i in range(len(x))]; cost = sum(v[1] for v in vals)
        if best is None or cost < best: best, tot = cost, 0.0
        if cost == best: tot += perm_sign(p)*np.prod([v[0] for v in vals])
    return tot, best
rng = np.random.default_rng(3); worst = 0; n = 0
for gid in [16, 18, 50, 52] + list(rng.choice(range(53, 208), 25, replace=False)):
    G = nx.graph_atlas(int(gid)); M = G.number_of_nodes()
    if not nx.is_connected(G): continue
    for N in range(2, M - 1 if M > 3 else M):
        cfgs = list(itertools.combinations(range(M), N))
        for _ in range(6):
            x, c = [cfgs[k] for k in rng.choice(len(cfgs), 2, replace=False)]; u = rng.normal(size=M)
            A, k = mb_sum(G, N, x, c, u); D, m = slater_sum(G, x, c, u)
            worst = max(worst, abs(abs(A) - abs(D))/abs(A), abs(k - m)); n += 1
print(n, 'pairs; max relative mismatch |A| vs |D| and distance mismatch:', worst)
