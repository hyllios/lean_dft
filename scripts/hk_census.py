"""Census of Hohenberg-Kohn failures on small graphs (spinless fermions, hopping -1 on edges, optional
nearest-neighbour repulsion U).  HK fails at potential v iff the ground state psi of H(v) has support S whose
occupation vectors {n(c): c in S} have rank < M (then v + eps*w, w non-constant with n(c).w = const on S, shares psi).
Construction: for each support S with rank < M (and every site sometimes occupied & sometimes empty in S):
  psi supported on S must satisfy (H0 psi)_c = 0 for c not in S (potential is diagonal) -> psi in a linear space K;
  then (H0 psi)_c + (n(c).v) psi_c = E psi_c on S -> solve for (psi in K, v, E) by least squares (random starts);
  keep solutions where psi is the NON-DEGENERATE ground state and 0 < rho_i < 1 for all sites ("nontrivial")."""
import numpy as np, networkx as nx, itertools, json, sys
from multiprocessing import Pool
from scipy.linalg import null_space
from scipy.optimize import least_squares

def many_body(G, N, U):
    M = G.number_of_nodes(); basis = list(itertools.combinations(range(M), N)); idx = {b: k for k, b in enumerate(basis)}
    H0 = np.zeros((len(basis), len(basis)))
    for col, cfg in enumerate(basis):
        H0[col, col] += U*sum(1 for a, b in itertools.combinations(cfg, 2) if G.has_edge(a, b))
        for pos, a in enumerate(cfg):
            for b in G[a]:
                if b in cfg: continue
                new = list(cfg); new[pos] = b
                perm_sign = (-1)**sum(1 for x in new if (x - b)*(x - a) < 0 and x != b)   # crossing count
                tgt = tuple(sorted(new)); H0[idx[tgt], col] += -1.0*perm_sign
    occ = np.array([[1.0 if i in cfg else 0.0 for cfg in basis] for i in range(M)])
    return basis, H0, occ

def search(G, N, U, starts=30, seed=0):
    M = G.number_of_nodes(); basis, H0, occ = many_body(G, N, U); L = len(basis); rng = np.random.default_rng(seed)
    found = []
    for r in range(2, L):
        for S in itertools.combinations(range(L), r):
            nS = occ[:, S]
            if np.linalg.matrix_rank(nS) >= M: continue
            if not all(0 < nS[i].sum() < r for i in range(M)): continue       # each site sometimes in, sometimes out
            notS = [c for c in range(L) if c not in S]
            K = null_space(H0[np.ix_(notS, S)]) if notS else np.eye(r)
            if K.shape[1] == 0: continue
            d = K.shape[1]
            def res(x):
                a = x[:d]; v = x[d:d+M]; E = x[-1]; psi = K @ a
                return np.concatenate([(H0[np.ix_(S, S)] @ psi) + (occ[:, S].T @ v)*psi - E*psi, [a @ a - 1]])
            for _ in range(starts):
                sol = least_squares(res, rng.normal(size=d + M + 1), xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=2000)
                if np.abs(sol.fun).max() > 1e-9: continue
                a = sol.x[:d]; v = sol.x[d:d+M]; psi_S = K @ a
                if np.min(np.abs(psi_S)) < 1e-6: continue
                psi = np.zeros(L); psi[list(S)] = psi_S
                H = H0 + np.diag(occ.T @ v); w = np.linalg.eigvalsh(H)
                E = psi @ H @ psi / (psi @ psi)
                if abs(E - w[0]) > 1e-8 or w[1] - w[0] < 1e-6: continue     # non-degenerate ground state
                rho = occ @ psi**2 / (psi @ psi)
                if not np.all((rho > 1e-6) & (rho < 1 - 1e-6)): continue
                found.append(dict(S=[basis[c] for c in S], v=list(np.round(v - v.mean(), 6)), rho=list(np.round(rho, 6)),
                                  gap=float(w[1] - w[0])))
                break
            if found and len(found) >= 3: return found
    return found

def run(job):
    gid, N, U = job; G = nx.graph_atlas(gid)
    return gid, N, U, G.number_of_nodes(), sorted(G.edges()), search(G, N, U)

if __name__ == '__main__':
    gids = [i for i in range(len(nx.graph_atlas_g())) if 4 <= nx.graph_atlas(i).number_of_nodes() <= 5
            and nx.is_connected(nx.graph_atlas(i))]
    jobs = [(g, 2, U) for g in gids for U in (0.0, 1.0)]
    res = []
    with Pool(8) as p:
        for gid, N, U, M, E, f in p.imap_unordered(run, jobs):
            res.append(dict(gid=gid, N=N, U=U, M=M, edges=E, examples=f))
            print(f'graph {gid:3d} (M={M}, edges={len(E)}) U={U}: {len(f)} nontrivial HK failure(s)', flush=True)
    json.dump(res, open('data/hk_census_M45.json', 'w'), indent=1)
