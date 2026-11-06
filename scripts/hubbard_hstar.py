"""Spinful Hubbard version of (H*), sector by sector.
H = -sum_<ij>,s (c+_is c_js + h.c.) + U sum_i n_i^ n_iv + sum_i v_i (n_i^ + n_iv), fixed (N_up, N_dn).
Total spin S is conserved for every v and commutes with all n_i, so eigenvectors of spin S vanish on configurations
c with (P_S)_cc = 0 ("forced zeros", e.g. triplets on doubly-occupied configs).  Exact certificate (integer v, mod prime):
  (1) charpoly of H in the sector is squarefree  -> simple spectrum (so different-S levels do not cross generically);
  (2) for every configuration c: deg gcd(charpoly H, charpoly H^(c)) == sum_{S : c not in A_S} d_S  (only forced zeros),
      where A_S = {c : (P_S)_cc != 0}, d_S = # spin-S states in the sector.  deg gcd mod P >= deg gcd over Q >= forced,
      so equality mod P is a proof.
  (3) for each S: W(c) = n(c).w constant on A_S forces w constant (so a non-uv state needs a NON-forced zero)."""
import numpy as np, networkx as nx, itertools, flint, json, sys
from multiprocessing import Pool
P = 2305843009213693951
def sector_basis(M, Nu, Nd):
    return [tuple(sorted(u + tuple(M + i for i in d))) for u in itertools.combinations(range(M), Nu)
            for d in itertools.combinations(range(M), Nd)]
def apply(ops, state):
    """ops: list of (dagger, mode) applied right-to-left; state: sorted tuple of occupied modes. returns (sign, state)"""
    s = list(state); sign = 1
    for dag, a in reversed(ops):
        if dag:
            if a in s: return 0, None
            k = sum(1 for x in s if x < a); sign *= (-1)**k; s.insert(k, a)
        else:
            if a not in s: return 0, None
            k = s.index(a); sign *= (-1)**k; s.pop(k)
    return sign, tuple(s)
def op_matrix(terms, basis_in, basis_out, coeff=1.0):
    idx = {b: k for k, b in enumerate(basis_out)}; A = np.zeros((len(basis_out), len(basis_in)))
    for col, b in enumerate(basis_in):
        for ops, c in terms:
            sg, nb = apply(ops, b)
            if sg: A[idx[nb], col] += c*sg
    return A
def build(G, Nu, Nd, U):
    M = G.number_of_nodes(); B = sector_basis(M, Nu, Nd)
    hop = [([(1, M*s + i), (0, M*s + j)], -1.0) for s in (0, 1) for i, j in G.edges()] + \
          [([(1, M*s + j), (0, M*s + i)], -1.0) for s in (0, 1) for i, j in G.edges()]
    H0 = op_matrix(hop, B, B)
    occ = np.array([[(i in b) + ((M + i) in b) for b in B] for i in range(M)], float)
    dbl = np.array([sum(1 for i in range(M) if i in b and M + i in b) for b in B], float)
    H0 = H0 + U*np.diag(dbl)
    # S^2 = Sz^2 + (S+S- + S-S+)/2
    Sz = (Nu - Nd)/2
    Splus = [([(1, i), (0, M + i)], 1.0) for i in range(M)]; Sminus = [([(1, M + i), (0, i)], 1.0) for i in range(M)]
    S2 = Sz**2*np.eye(len(B))
    if Nd > 0:
        Bm = sector_basis(M, Nu + 1, Nd - 1); S2 += 0.5*op_matrix(Sminus, Bm, B) @ op_matrix(Splus, B, Bm)
    if Nu > 0:
        Bp = sector_basis(M, Nu - 1, Nd + 1); S2 += 0.5*op_matrix(Splus, Bp, B) @ op_matrix(Sminus, B, Bp)
    return B, H0, occ, S2
def charpoly_mod(A):
    n = A.shape[0]
    return flint.nmod_mat(n, n, [int(x) % P for x in A.ravel()], P).charpoly()
def cert(job):
    gid, Nu, Nd, U = job; G = nx.graph_atlas(gid); M = G.number_of_nodes()
    B, H0, occ, S2 = build(G, Nu, Nd, U); L = len(B)
    e, Q = np.linalg.eigh(S2); Svals = np.rint((-1 + np.sqrt(1 + 4*e))/2*2)/2
    sectors = {}
    for S in sorted(set(Svals)):
        cols = Q[:, Svals == S]; Pd = np.einsum('ij,ij->i', cols, cols)
        sectors[S] = dict(d=cols.shape[1], A=Pd > 1e-9)
    # (3) W constant on A_S forces w constant?
    rigid = {}
    for S, sd in sectors.items():
        Aidx = np.where(sd['A'])[0]
        Mx = np.c_[occ[:, Aidx].T, -np.ones(len(Aidx))]
        rigid[S] = bool((Mx.shape[1] - np.linalg.matrix_rank(Mx)) == 1)
    rng = np.random.default_rng(gid*1000 + Nu*31 + Nd*7 + int(U))
    for attempt in range(6):
        v = rng.integers(-1000, 1001, size=M)
        H = np.rint(H0 + np.diag(occ.T @ v)).astype(np.int64)
        p = charpoly_mod(H)
        if p.gcd(p.derivative()).degree() > 0: continue
        ok = True
        for c in range(L):
            keep = [i for i in range(L) if i != c]
            if not keep: break
            pc = charpoly_mod(H[np.ix_(keep, keep)])
            forced = sum(sd['d'] for S, sd in sectors.items() if not sd['A'][c])
            if p.gcd(pc).degree() != forced: ok = False; break
        if ok: return gid, Nu, Nd, U, L, True, {str(S): (sd['d'], int(sd['A'].sum()), rigid[S]) for S, sd in sectors.items()}
    return gid, Nu, Nd, U, L, False, {str(S): (sd['d'], int(sd['A'].sum()), rigid[S]) for S, sd in sectors.items()}
if __name__ == '__main__':
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    jobs = [(g, Nu, Nd, U) for g in range(1, 1253) if (2 if Mmax < 6 else Mmax) <= nx.graph_atlas(g).number_of_nodes() <= Mmax
            and nx.is_connected(nx.graph_atlas(g))
            for Nu in range(1, nx.graph_atlas(g).number_of_nodes() + 1) for Nd in range(1, Nu + 1)
            if len(sector_basis(nx.graph_atlas(g).number_of_nodes(), Nu, Nd)) > 1 for U in (1.0, 4.0)]
    with Pool(8) as pool: R = pool.map(cert, jobs, chunksize=4)
    json.dump(R, open(f'data/hubbard_hstar_M{Mmax}.json', 'w'))
    bad = [r[:5] for r in R if not r[5]]; nonrigid = [(r[:4], S) for r in R for S, t in r[6].items() if not t[2]]
    print(len(R), 'sector cases;', len(R) - len(bad), 'certified;', 'uncertified:', bad[:20])
    print('non-rigid (W const on A_S with non-constant w):', len(nonrigid), nonrigid[:20])
