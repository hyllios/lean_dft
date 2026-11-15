"""Exact sum-of-squares certificates for the gaps of the HK counterexamples (Lean file
`DFT/Lattice/HK/Nondegenerate.lean`).

For a ground state psi of H with energy E0 and a gap bound g, the Lean goal is
    for all phi with psi . phi = 0:  (E0 + g) * (phi . phi) <= qf H phi.
Certificate: M = H - (E0 + g) I + mu * psi psi^T (mu chosen by hand per case) is positive semidefinite,
written exactly as
    phi^T M phi = sum_k d_k (L_k . phi)^2,  d_k >= 0  (LDL^T, no pivoting),
so on psi . phi = 0 the goal follows. In Lean the hint list also gets `mul_self_eq_zero.mpr h0'` (the
orthogonality, written by hand), which removes the mu term. The script checks every identity with exact
rationals and prints the `nlinarith` hint lists, plus the test vectors that bound the two square gaps from
above. "Gap" means the variational gap (minimum Rayleigh quotient on psi-perp minus E0).
Run from the repository root: python scripts/gen_nondegenerate.py   (needs sympy and numpy)
"""
import numpy as np
import sympy as sp

R = sp.Rational
OCC4 = [[1, 1, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1, 1]]
H0SQ = [[4, -1, 0, 0, 1, 0], [-1, 4, -1, -1, 0, 1], [0, -1, 4, 0, -1, 0],
        [0, -1, 0, 4, -1, 0], [1, 0, -1, -1, 4, -1], [0, 1, 0, 0, -1, 4]]
OCC3 = [[1, 1, 0], [1, 0, 1], [0, 1, 1]]
H0TRI = [[4, -1, 1], [-1, 4, -1], [1, -1, 4]]


def ham_n(h0, occ, v):
    """hamN H0 occ v = H0 + diag(sum_i v_i occ_i c)."""
    H = sp.Matrix(h0)
    for c in range(H.shape[0]):
        H[c, c] += sum(v[i] * occ[i][c] for i in range(len(v)))
    return H


def ham_frustrated(v):
    """ham (complete graph on 3) (t = -1) v = diag v + A."""
    return sp.diag(*v) + sp.Matrix([[0, 1, 1], [1, 0, 1], [1, 1, 0]])


def ldl(M):
    """Exact LDL^T without pivoting. Returns (L, D); a zero pivot is allowed only with a zero column."""
    n = M.shape[0]
    A = M.copy()
    L = sp.eye(n)
    D = [R(0)] * n
    for k in range(n):
        D[k] = A[k, k]
        for i in range(k + 1, n):
            if D[k] == 0:
                assert A[i, k] == 0, f"zero pivot {k} with nonzero entry at {i}"
            else:
                L[i, k] = A[i, k] / D[k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i, j] -= L[i, k] * D[k] * L[j, k]
    return L, D


def lean_num(q):
    q = sp.Rational(q)
    if q.q == 1:
        return f"({q.p})" if q.p < 0 else f"{q.p}"
    return f"({q.p}/{q.q})"


def lean_lin(coeffs, var="φ"):
    """Lean text for sum_c coeffs[c] * var c (coeffs exact rationals)."""
    terms = []
    for c, a in enumerate(coeffs):
        if a == 0:
            continue
        terms.append(f"{lean_num(a)} * {var} {c}")
    return " + ".join(terms) if terms else "0"


def certificate(H, psi, g, mu):
    """Check H psi = E0 psi, build the LDL certificate of M, verify the identity; return (E0, hints)."""
    n = H.shape[0]
    E0 = (psi.T * H * psi)[0] / (psi.T * psi)[0]
    assert H * psi == E0 * psi, "psi is not an eigenvector"
    M = H - (E0 + g) * sp.eye(n) + mu * psi * psi.T
    L, D = ldl(M)
    assert all(d >= 0 for d in D), f"negative pivot: {D}"
    x = sp.symbols(f"x0:{n}")
    xv = sp.Matrix(x)
    lhs = sp.expand((xv.T * M * xv)[0])
    rows = [[L[i, k] for i in range(n)] for k in range(n)]  # (L^T x)_k = sum_i L[i,k] x_i
    rhs = sp.expand(sum(D[k] * sum(rows[k][i] * x[i] for i in range(n)) ** 2 for k in range(n)))
    assert sp.simplify(lhs - rhs) == 0, "LDL identity fails"
    hints = [f"mul_nonneg (by norm_num : (0:ℝ) ≤ {lean_num(D[k])}) (sq_nonneg ({lean_lin(rows[k])}))"
             for k in range(n) if D[k] != 0]
    return E0, hints


def rayleigh_above(H, psi, E0, chi):
    """Assert chi . psi = 0 and return qf(chi)/|chi|^2 - E0 (an upper bound for the gap above E0)."""
    chi = sp.Matrix(chi)
    assert (psi.T * chi)[0] == 0, "test vector not orthogonal to the ground state"
    rq = (chi.T * H * chi)[0] / (chi.T * chi)[0]
    return rq - E0


# name: (H, psi, g, mu). Rule for g: the exact gap rounded down to 1/100, except "sq1", certified to 0.2635 so
# that, with the upper bound 0.264 below, the gap provably rounds to 0.264 (the value printed in the paper).
CASES = {
    "sq0": (ham_n(H0SQ, OCC4, [R(3, 4), -R(3, 4), -R(3, 4), R(3, 4)]), [0, 2, 1, 4, 2, 0], R(1, 2), R(1, 25)),
    "sq1": (ham_n(H0SQ, OCC4, [R(5, 4), -R(1, 4), -R(5, 4), R(1, 4)]), [0, 2, 1, 4, 2, 0], R(2635, 10000),
            R(1, 25)),
    "tri1": (ham_n(H0TRI, OCC3, [0, -1, 0]), [1, 0, -1], R(58, 100), R(1, 2)),
    "tri2": (ham_n(H0TRI, OCC3, [0, -2, 0]), [1, 0, -1], R(1), R(1, 2)),
    "fr1": (ham_frustrated([0, 0, 1]), [1, -1, 0], R(58, 100), R(1, 2)),
    "fr2": (ham_frustrated([0, 0, 2]), [1, -1, 0], R(1), R(1, 2)),
}


def main():
    for name, (H, psi_list, g, mu) in CASES.items():
        psi = sp.Matrix(psi_list)
        w = sorted(H.eigenvals(multiple=True), key=lambda z: float(z))
        E0 = (psi.T * H * psi)[0] / (psi.T * psi)[0]
        gap = sp.nsimplify(w[1] - w[0])
        assert sp.simplify(w[0] - E0) == 0 and g <= gap, (name, w[0], E0, g, gap)
        Ecert, hints = certificate(H, psi, g, mu)
        print(f"== {name}: E0 = {E0}, exact gap = {gap} ≈ {float(gap):.6f}, certified g = {g}")
        print("  hints: [" + ",\n    ".join(hints) + "]")
    # upper bounds for the square gaps
    H0, psi = CASES["sq0"][0], sp.Matrix([0, 2, 1, 4, 2, 0])
    ev2 = (H0 - 2 * sp.eye(6)).nullspace()
    assert len(ev2) == 1
    chi0 = ev2[0] / sp.gcd(list(ev2[0]))
    d0 = rayleigh_above(H0, psi, R(3, 2), chi0)
    assert d0 == R(1, 2)
    print("== sq0 eigenvector at E = 2:", list(chi0), "| Rayleigh - E0 =", d0, "(gap exactly 1/2)")
    H1 = CASES["sq1"][0]
    vals, vecs = np.linalg.eigh(np.array(H1, dtype=float))
    k = int(np.argmax(np.abs(vecs[:, 1])))
    ev = -vecs[:, 1] / vecs[k, 1]  # eigenvector at 4 - sqrt 5; sign fixed: largest entry -1, as in Lean
    chi1 = sp.Matrix([R(round(c * 1000), 1000) for c in ev])
    chi1 = chi1 - ((psi.T * chi1)[0] / (psi.T * psi)[0]) * psi  # project out psi exactly
    chi1 = chi1 * sp.ilcm(*[sp.fraction(c)[1] for c in chi1])
    d = rayleigh_above(H1, psi, R(3, 2), chi1)
    assert d < R(264, 1000)
    print("== sq1 test vector:", list(chi1), "| Rayleigh - E0 =", d, "≈", float(d), "< 0.264")


if __name__ == "__main__":
    main()
