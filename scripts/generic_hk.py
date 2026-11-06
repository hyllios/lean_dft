"""How big is the set of 'bad' potentials (HK failure) on the 2-fermion square?
Bad set for family X = {v : ground state psi(v) vanishes on the two 'same-half' configurations}.
We (1) find many bad points by solving F(v)=0 from random starts, (2) compute the Jacobian rank of F there
(kernel dimension = local dimension of the bad set, modulo the trivial constant shift), (3) sample random v."""
import numpy as np, networkx as nx, hk_census as h
from scipy.optimize import least_squares
G = nx.cycle_graph(4)
fam = {'A': [(0, 3), (1, 2)], 'B': [(0, 1), (2, 3)]}
def gs(v, H0, occ):
    e, U = np.linalg.eigh(H0 + np.diag(occ.T @ v)); p = U[:, 0]
    return p*np.sign(p[np.argmax(abs(p))]), e[1] - e[0]
for Uint in (0.0, 1.0):
    basis, H0, occ = h.many_body(G, 2, Uint)
    for name, zs in fam.items():
        zi = [basis.index(z) for z in zs]
        F = lambda x: gs(np.r_[x, 0.0], H0, occ)[0][zi]           # fix v3 = 0 (removes constant)
        rng = np.random.default_rng(1); pts = []
        for _ in range(300):
            s = least_squares(F, rng.normal(scale=2, size=3), xtol=1e-15, ftol=1e-15, gtol=1e-15)
            if np.abs(s.fun).max() < 1e-10 and gs(np.r_[s.x, 0], H0, occ)[1] > 1e-4: pts.append(s.x)
        pts = np.array(pts)
        ranks = []
        for x in pts[:20]:
            J = np.array([(F(x + 1e-6*e) - F(x - 1e-6*e))/2e-6 for e in np.eye(3)]).T
            ranks.append(np.linalg.matrix_rank(J, tol=1e-6))
        # dimension of the cloud of bad points (local PCA via SVD of centred points)
        sv = np.linalg.svd(pts - pts.mean(0), compute_uv=False) if len(pts) > 3 else []
        print(f'U={Uint} family {name}: {len(pts)} bad points found; Jacobian ranks {sorted(set(ranks))} '
              f'(local dim = 3 - rank); point-cloud singular values {np.round(sv, 3)}')
        np.save(f'data/bad_{name}_U{int(Uint)}.npy', pts)
    # random sampling: smallest |psi_c| over all configurations
    rng = np.random.default_rng(2); m = [np.min(abs(gs(rng.normal(scale=2, size=4), H0, occ)[0])) for _ in range(100000)]
    m = np.array(m); print(f'U={Uint}: 1e5 random v -> min_c|psi_c|: smallest {m.min():.2e}; '
                           f'fraction below 1e-2: {np.mean(m<1e-2):.4f}, below 1e-3: {np.mean(m<1e-3):.5f}')
