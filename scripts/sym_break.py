import numpy as np, networkx as nx
from hk_census import many_body
G = nx.cycle_graph(4); basis, H0, occ = many_body(G, 2, 0.0)
# hopping matrix elements belonging to bond (0,1): rebuild with a weight on that bond
def H0_eps(eps):
    Gw = nx.cycle_graph(4); B = np.zeros_like(H0)
    b, Hb, _ = many_body(nx.Graph([(0, 1)] + [(2, 3)]*0), 2, 0.0) if False else (None, None, None)
    # matrix elements of the single bond (0,1): take full square minus square-without-that-bond
    G2 = nx.Graph(); G2.add_nodes_from(range(4)); G2.add_edges_from([(1, 2), (2, 3), (3, 0)])
    _, H0_rest, _ = many_body(G2, 2, 0.0)
    return H0 + eps*(H0 - H0_rest)
v0 = np.array([0.75, -0.75, -0.75, 0.75])
def response(eps):
    H = H0_eps(eps) + np.diag(occ.T @ v0); E, U = np.linalg.eigh(H); psi = U[:, 0]
    N = occ  # site density operators are diagonal: <m|n_i|0> = U[c,m] occ[i,c] U[c,0]
    A = np.einsum('ic,cm,c->im', occ, U, psi)          # <m| n_i |0>
    chi = 2*np.einsum('im,jm,m->ij', A[:, 1:], A[:, 1:], 1/(E[0] - E[1:]))
    return psi, E[1] - E[0], chi
# invisible direction at eps = 0: null vector of chi orthogonal to constants
psi0, gap0, chi0 = response(0.0)
s0, V0 = np.linalg.eigh(chi0)
one = np.ones(4)/2
cands = [V0[:, k] for k in range(4) if abs(s0[k]) < 1e-10 and abs(V0[:, k] @ one) < 0.9]
w = cands[0] - (cands[0] @ one)*one; w /= np.linalg.norm(w)
print('eps=0: gap', round(gap0, 4), '| chi eigenvalues', np.round(s0, 6), '| invisible direction w =', np.round(w, 3))
print(f"{'eps':>8} {'min|psi_c|':>12} {'|chi w|':>12} {'2nd-smallest |eig chi|':>24}")
rows = []
for eps in [1e-1, 3e-2, 1e-2, 3e-3, 1e-3, 3e-4, 1e-4]:
    psi, gap, chi = response(eps)
    ev = np.sort(np.abs(np.linalg.eigvalsh(chi)))
    rows.append((eps, np.min(np.abs(psi)), np.linalg.norm(chi @ w), ev[1]))
    print(f'{eps:8.0e} {rows[-1][1]:12.3e} {rows[-1][2]:12.3e} {rows[-1][3]:24.3e}')
r = np.array(rows)
for k, name in ((1, 'min|psi|'), (2, '|chi w|'), (3, 'smallest nontrivial eig')):
    p = np.polyfit(np.log(r[:, 0]), np.log(r[:, k]), 1)[0]
    print(f'scaling of {name:24s} ~ eps^{p:.2f}')
