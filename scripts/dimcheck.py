import numpy as np, networkx as nx, json, hk_census as h
from scipy.optimize import least_squares
R = json.load(open('data/hk_census_M45.json'))
for r in R:
    if r['gid'] != 50: continue
    G = nx.graph_atlas(50); M = 5; basis, H0, occ = h.many_body(G, r['N'], r['U']); L = len(basis)
    print('graph 50 edges', sorted(G.edges()), 'U', r['U'])
    def gs(v):
        e, U = np.linalg.eigh(H0 + np.diag(occ.T @ v)); p = U[:, 0]; return p*np.sign(p[np.argmax(abs(p))]), e[1]-e[0]
    for ex in r['examples']:
        S = set(map(tuple, ex['S'])); Z = [basis.index(c) for c in basis if c not in S]
        v0 = np.array(ex['v'])
        F = lambda x: gs(np.r_[x, 0.0])[0][Z]
        # sample the bad set near v0 and globally
        rng = np.random.default_rng(0); pts = []
        for k in range(200):
            x0 = (v0 - v0[-1])[:4] + rng.normal(scale=0.5 if k < 100 else 3, size=4)
            s = least_squares(F, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15)
            if np.abs(s.fun).max() < 1e-10 and gs(np.r_[s.x, 0])[1] > 1e-4: pts.append(s.x)
        pts = np.array(pts)
        J = lambda x: np.array([(F(x + 1e-6*e) - F(x - 1e-6*e))/2e-6 for e in np.eye(4)]).T
        rk = sorted({np.linalg.matrix_rank(J(x), tol=1e-5) for x in pts[:15]})
        # density image dimension: tangent space of bad set = kernel of J; push through d rho
        def rho(x): p, _ = gs(np.r_[x, 0]); return occ @ p**2
        dims = set()
        for x in pts[:15]:
            K = np.linalg.svd(J(x))[2][np.linalg.matrix_rank(J(x), tol=1e-5):]
            D = np.array([(rho(x + 1e-6*k) - rho(x - 1e-6*k))/2e-6 for k in K])
            dims.add(np.linalg.matrix_rank(D, tol=1e-5))
        # naive count k_min: number of zeros
        print(f"  zeros on {[basis[z] for z in Z]} (#zeros={len(Z)}); bad pts {len(pts)}; "
              f"Jacobian rank {rk} -> bad-v dim {[4-x for x in rk]} of 4 (codim {rk}); bad-rho dim {sorted(dims)} of 4")
