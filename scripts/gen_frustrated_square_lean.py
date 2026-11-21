"""Generate DFT/Lattice/Bridge/FrustratedSquareCertificates.lean.

N spinless fermions (N = 1, 2, 3) on the 4-cycle 0 - 1 - 2 - 3 - 0 with symmetric hopping
t01 = -p, t12 = q, t23 = r, t30 = s (p, q, r, s > 0: one negative bond).

Conventions are those of the Lean library: configurations are listed in lexicographic order, the
many-body hopping matrix is Gamma(-hopM sqG t), with entry (s, s') = sum_k sum_b h(tau_s k, b)
amp(s', update(tau_s, k, b)), where tau_s is the sorted tuple of occupied sites and amp is the
determinant of the overlap matrix.

For every configuration c the script picks d = hop distance from c in the configuration graph and
searches potentials u among the permutations of (0, 1, 3, 7) (then a wider range) for which the
table T of top coefficients,
    T[i][0] = [i = c],
    T[i][k+1] = w_i T[i][k] + sum_{j != i, d_j + 1 = d_i} A[i][j] T[j][k],   w_i = sum_{x in i} u_x,
has a determinant that is a polynomial in p, q, r, s with coefficients of one sign. It also checks
that T agrees with the coefficient of lam^(k - d_i) in ((A + lam W)^k)[i, c].

Requires sympy.
Usage:  python scripts/gen_frustrated_square_lean.py > DFT/Lattice/Bridge/FrustratedSquareCertificates.lean
With --only N i it emits only the certificate for configuration i of the N-fermion basis; with
--controls it prints sanity controls instead of Lean code.
"""
import itertools
import sys

import sympy as sp

p, q, r, s = sp.symbols("p q r s", positive=True)
lam = sp.Symbol("lam")
EDGES = {(0, 1), (1, 2), (2, 3), (0, 3)}
TSYM = {(a, b): sp.Symbol(f"t_{a}_{b}") for a in range(4) for b in range(4)}


def adj(a, b):
    return (min(a, b), max(a, b)) in EDGES


def sq_hop(a, b):
    """The symmetric hopping sqHop (-p) q r s."""
    return {(0, 1): -p, (1, 2): q, (2, 3): r, (0, 3): s}[(min(a, b), max(a, b))]


def configs(N):
    return [tuple(c) for c in itertools.combinations(range(4), N)]


def gamma(N, t):
    """Gamma(-hopM sqG t) in the lexicographic basis, for a hopping function t(a, b)."""
    cs = configs(N)
    n = len(cs)
    A = sp.zeros(n, n)
    for i, si in enumerate(cs):
        for j, sj in enumerate(cs):
            tot = 0
            for k in range(N):
                for b in range(4):
                    a = si[k]
                    if not adj(a, b):
                        continue
                    tau = list(si)
                    tau[k] = b
                    ov = sp.Matrix(N, N, lambda kk, jj: 1 if tau[kk] == sj[jj] else 0)
                    tot += -t(a, b) * ov.det()
            A[i, j] = sp.expand(tot)
    return cs, A


def bfs(A, ic):
    n = A.shape[0]
    d = [None] * n
    d[ic] = 0
    front = [ic]
    while front:
        nxt = []
        for x in front:
            for y in range(n):
                if y != x and A[x, y] != 0 and d[y] is None:
                    d[y] = d[x] + 1
                    nxt.append(y)
        front = nxt
    return d


def t_table(A, w, d, ic):
    n = A.shape[0]
    T = sp.zeros(n, n)
    T[ic, 0] = 1
    for k in range(n - 1):
        for i in range(n):
            T[i, k + 1] = sp.expand(w[i] * T[i, k] + sum(
                A[i, j] * T[j, k] for j in range(n) if j != i and d[j] + 1 == d[i]))
    return T


def t_from_powers(A, w, d, ic):
    """Top coefficients read off the powers of A + lam W (independent check of t_table)."""
    n = A.shape[0]
    H = A + lam * sp.diag(*w)
    T = sp.zeros(n, n)
    P = sp.eye(n)
    for k in range(n):
        for y in range(n):
            if k >= d[y]:
                T[y, k] = sp.Poly(sp.expand(P[y, ic]), lam).coeff_monomial(lam ** (k - d[y]))
        P = sp.expand(H * P)
    return T


def sign_of(det):
    if det == 0:
        return 0
    cs = sp.Poly(det, p, q, r, s).coeffs()
    if all(x > 0 for x in cs):
        return 1
    if all(x < 0 for x in cs):
        return -1
    return 0


def candidates():
    yield from itertools.permutations((0, 1, 3, 7))
    yield from itertools.product(range(-4, 5), repeat=4)


def certificate(N, ic):
    cs, A = gamma(N, sq_hop)
    d = bfs(A, ic)
    for u in candidates():
        w = [sum(u[x] for x in c) for c in cs]
        T = t_table(A, w, d, ic)
        det = sp.expand(T.det(method="berkowitz"))
        sg = sign_of(det)
        if sg:
            assert T == t_from_powers(A, w, d, ic)
            return dict(u=u, d=d, w=w, T=T, det=det, sign=sg)
    raise RuntimeError(f"no certificate for N={N}, c={cs[ic]}")


# ---------------------------------------------------------------- Lean output

def lean_poly(e):
    e = sp.expand(e)
    if e == 0:
        return "0"
    out = str(e).replace("**", "^")
    return f"({out})" if out.startswith("-") or " " in out else out


def lean_matrix(T):
    n = T.shape[0]
    rows = [", ".join(lean_poly(T[i, j]) for j in range(n)) for i in range(n)]
    return "!![" + ";\n      ".join(rows) + "]"


def lean_hop_entry(e):
    """An entry of the general-t hopping table: 0 or +-t a b."""
    if e == 0:
        return "0"
    for (a, b), x in TSYM.items():
        if e == -x:
            return f"-t {a} {b}"
        if e == x:
            return f"t {a} {b}"
    raise ValueError(e)


def lean_conf(c):
    return "⟨{" + ", ".join(map(str, c)) + "}, by decide⟩"


NAMES = {1: "one", 2: "two", 3: "three"}


def emit_basis(N):
    """cfg, pos, τs lemma, hopping table and Γ lemma for N = 1 and N = 3 (N = 2 exists)."""
    cs, At = gamma(N, lambda a, b: TSYM[(a, b)])
    n = len(cs)
    k = N
    rows = [", ".join(lean_hop_entry(At[i, j]) for j in range(n)) for i in range(n)]
    hop = "!![" + ";\n     ".join(rows) + "]"
    det_lemma = {1: "Matrix.det_fin_one", 3: "Matrix.det_fin_three"}[N]
    names = ", ".join("".join(map(str, c)) for c in cs)
    return f"""
/-! ### {NAMES[N].capitalize()} fermion{'s' if N > 1 else ''} -/

/-- The configurations of {N} fermion{'s' if N > 1 else ''} on the square, in the order `{names}`. -/
def cfg{N} : Fin {n} → Conf 4 {N} :=
  ![{', '.join(lean_conf(c) for c in cs)}]

lemma cfg{N}_bijective : Function.Bijective cfg{N} := by decide

/-- The basis `cfg{N}` as an equivalence. -/
noncomputable def e{N} : Fin {n} ≃ Conf 4 {N} := Equiv.ofBijective cfg{N} cfg{N}_bijective

/-- The occupied sites of `cfg{N} i`, in increasing order. -/
def pos{N} : Fin {n} → Fin {k} → Fin 4 :=
  ![{', '.join('![' + ', '.join(map(str, c)) + ']' for c in cs)}]

lemma pos{N}_strictMono (i : Fin {n}) : StrictMono (pos{N} i) := by
  fin_cases i <;> (rw [Fin.strictMono_iff_lt_succ]; decide)

lemma τs_cfg{N} (i : Fin {n}) : τs (cfg{N} i) = pos{N} i := by
  unfold τs
  have h := Finset.orderEmbOfFin_unique (cfg{N} i).2 (f := pos{N} i)
    (by fin_cases i <;> decide) (pos{N}_strictMono i)
  exact (congrArg (fun f : Fin {k} → Fin 4 => f) h).symm ▸ rfl

/-- The hopping part of `H0Fw sqG t 0` for {N} fermion{'s' if N > 1 else ''} in the basis `cfg{N}`. -/
def hop{N} (t : Fin 4 → Fin 4 → ℝ) : Matrix (Fin {n}) (Fin {n}) ℝ :=
  {hop}

theorem gamma_cfg{N} (t : Fin 4 → Fin 4 → ℝ) (i j : Fin {n}) :
    (Γ (-hopM sqG t) : Matrix (Conf 4 {N}) (Conf 4 {N}) ℝ) (cfg{N} i) (cfg{N} j) = hop{N} t i j := by
  simp only [Γ, amp, slater, τs_cfg{N}]
  fin_cases i <;> fin_cases j <;>
    simp +decide [Fin.sum_univ_succ, {det_lemma}, Function.update, hopM, sqG, pos{N}, hop{N}]

lemma sum_occF_cfg{N} (u : Fin 4 → ℝ) (i : Fin {n}) :
    ∑ x, u x * occF x (cfg{N} i) = ![{', '.join(' + '.join(f'u {x}' for x in c) for c in cs)}] i := by
  fin_cases i <;> simp [occF, cfg{N}, Fin.sum_univ_four]
"""


def basis_names(N):
    if N == 2:
        return dict(e="e", cfg="cfg", hop="hopSq", gamma="gamma_cfg2", occ="sum_occF_cfg2")
    return dict(e=f"e{N}", cfg=f"cfg{N}", hop=f"hop{N}", gamma=f"gamma_cfg{N}",
                occ=f"sum_occF_cfg{N}")


def emit_cert(N, ic, cert):
    cs = configs(N)
    n = len(cs)
    b = basis_names(N)
    u = "![" + ", ".join(map(str, cert["u"])) + "]"
    dh = "![" + ", ".join(map(str, cert["d"])) + "]"
    det = cert["det"]
    if cert["sign"] > 0:
        detstr, close = lean_poly(det), "positivity"
    else:
        detstr, close = f"-{lean_poly(-det)}", "exact neg_ne_zero.mpr (by positivity)"
    if not (detstr.startswith("(") or detstr.startswith("-(")):
        detstr = f"({detstr})"
    conf = "{" + ", ".join(map(str, cs[ic])) + "}"
    return f"""
/-- (H*) for `N = {N}` at `{conf}`: `u = ({', '.join(map(str, cert['u']))})`, hop distances
`({', '.join(map(str, cert['d']))})`, determinant of the table
`{detstr}`. -/
theorem hstar_sqHop_{N}_{ic} {{p q r s : ℝ}} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (Vint : Conf 4 {N} → ℝ) :
    krylovPoly (H0Fw sqG (sqHop (-p) q r s) Vint) occF ({b['e']} {ic})
      (fun j => (Fintype.equivFin (Conf 4 {N}) j : ℕ)) ≠ 0 := by
  refine krylovPoly_ne_zero_of_table {b['e']} (Ah := {b['hop']} (sqHop (-p) q r s))
    (fun i j => {b['gamma']} _ i j) occF {u} (fun i => {b['occ']} _ i) (dh := {dh}) ?_
    (ic := {ic}) rfl
    (Tm := {lean_matrix(cert['T'])}) ?_ ?_ ?_ Vint
  · intro i j _ h
    fin_cases i <;> fin_cases j <;> first | decide | (exfalso; apply h; simp [{b['hop']}, sqHop])
  · intro i k hk
    obtain rfl : k = 0 := Fin.ext hk
    fin_cases i <;> simp
  · intro i k k' hk
    fin_cases k <;> fin_cases k' <;> (try simp at hk) <;> fin_cases i <;>
      simp [Fin.sum_univ_succ, {b['hop']}, sqHop] <;> ring
  · have hdet : Matrix.det (n := Fin {n}) {lean_matrix(cert['T'])} =
        {detstr} := by
      simp +decide [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.succAbove]
      ring
    rw [hdet]
    {close}
"""


HEADER = """/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.Bridge.SquareHopping
import DFT.Lattice.StrongPotential.TopTable

/-!
# The square with one negative bond: exact leading-coefficient certificates

Generated by `scripts/gen_frustrated_square_lean.py`. `N` spinless fermions (`N = 1, 2, 3`) on
the 4-cycle `sqG` with symmetric hopping `sqHop (-p) q r s`
(`t₀₁ = −p`, `t₁₂ = q`, `t₂₃ = r`, `t₃₀ = s`, all of `p, q, r, s` positive). For every
configuration `c` the file gives a potential direction `u`, the hop distances `d` from `c`, the
table of top coefficients `T k (y)` (`T 0 = e_c`,
`T (k + 1) y = w y · T k y + Σ_{d z + 1 = d y} A y z · T k z`) and its determinant, a polynomial
in `p, q, r, s` with coefficients of one sign; `krylovPoly_ne_zero_of_table` turns this into (H*)
at `c` for every configuration-diagonal interaction.

* `sqHop`; bases `cfg1`, `cfg3` with `gamma_cfg1`, `gamma_cfg3` (the two-fermion basis `cfg`, `e`
  are in `Bridge.Square`, its hopping table `hopSq` in `Bridge.SquareHopping`); `gamma_cfg2`,
  `sum_occF_cfg1/2/3`;
* `hstar_sqHop_N_i`: (H*) at the configuration `i` of the basis, for `N` fermions;
* `hstar_sqHop_one`, `hstar_sqHop_two`, `hstar_sqHop_three`: (H*) at every configuration.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

namespace DFT

open Matrix

namespace Bridge.Square

/-- Symmetric hopping on the square with `t₀₁ = a`, `t₁₂ = b`, `t₂₃ = c`, `t₃₀ = d` (zero on the
diagonals `0 2`, `1 3` and on the sites). -/
def sqHop (a b c d : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun x y => (!![0, a, 0, d; a, 0, b, 0; 0, b, 0, c; d, 0, c, 0] : Matrix (Fin 4) (Fin 4) ℝ) x y
"""

TWO = """
/-! ### Two fermions (basis `cfg`, hopping table `hopSq`) -/

theorem gamma_cfg2 (t : Fin 4 → Fin 4 → ℝ) (i j : Fin 6) :
    (Γ (-hopM sqG t) : Matrix (Conf 4 2) (Conf 4 2) ℝ) (cfg i) (cfg j) = hopSq t i j := by
  have h := H0Fw_square t 0 i j
  simpa [H0Fw] using h

lemma sum_occF_cfg2 (u : Fin 4 → ℝ) (i : Fin 6) :
    ∑ x, u x * occF x (cfg i) =
      ![u 0 + u 1, u 0 + u 2, u 0 + u 3, u 1 + u 2, u 1 + u 3, u 2 + u 3] i := by
  fin_cases i <;> simp [occF, cfg, Fin.sum_univ_four]
"""


def emit_all(only=None):
    out = [HEADER]
    for N in (1, 2, 3):
        if only and N != only[0]:
            continue
        out.append(emit_basis(N) if N != 2 else TWO)
        cs = configs(N)
        b = basis_names(N)
        out.append(f"\n/-! ### Certificates, {N} fermion{'s' if N > 1 else ''} -/\n")
        for ic in range(len(cs)):
            if only and ic != only[1]:
                continue
            out.append(emit_cert(N, ic, certificate(N, ic)))
        if only:
            continue
        cases = ",\n    ".join(f"hstar_sqHop_{N}_{ic} hp hq hr hs Vint" for ic in range(len(cs)))
        out.append(f"""
/-- (H*) for {N} fermion{'s' if N > 1 else ''} on the square with one negative bond, at every
configuration. -/
theorem hstar_sqHop_{NAMES[N]} {{p q r s : ℝ}} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (c : Conf 4 {N}) (Vint : Conf 4 {N} → ℝ) :
    krylovPoly (H0Fw sqG (sqHop (-p) q r s) Vint) occF c
      (fun j => (Fintype.equivFin (Conf 4 {N}) j : ℕ)) ≠ 0 := by
  obtain ⟨i, rfl⟩ := {b['e']}.surjective c
  fin_cases i
  exacts [{cases}]
""")
    out.append("\nend Bridge.Square\n\nend DFT\n")
    return "".join(out)


def main():
    if "--controls" in sys.argv:
        controls()
        return
    only = None
    if "--only" in sys.argv:
        k = sys.argv.index("--only")
        only = (int(sys.argv[k + 1]), int(sys.argv[k + 2]))
    sys.stdout.write(emit_all(only))


def controls():
    """Mutation controls: the certificate must fail where it should."""
    us = list(itertools.permutations((0, 1, 3, 7)))
    for N in (1, 2, 3):
        cs, A = gamma(N, sq_hop)
        for ic in range(len(cs)):
            cert = certificate(N, ic)
            d, w = cert["d"], cert["w"]
            # 1. other directions u: how many of the 24 permutations give a zero or mixed-sign det
            tally = {"zero": 0, "mixed": 0, "one-signed": 0}
            for u in us:
                wu = [sum(u[x] for x in c) for c in cs]
                det = sp.expand(t_table(A, wu, d, ic).det(method="berkowitz"))
                tally["zero" if det == 0 else ("one-signed" if sign_of(det) else "mixed")] += 1
            # 2. bonds 1 2 and 3 0 removed (q = s = 0): the square falls apart, det T must vanish
            A0 = A.subs({q: 0, s: 0})
            det_cut = sp.expand(t_table(A0, w, d, ic).det(method="berkowitz"))
            # 3. d = 0 everywhere (valid but too small): coefficient above the top power, zero
            det_d0 = sp.expand(t_table(A, w, [0] * len(cs), ic).det(method="berkowitz"))
            # 4. the same determinant with t01 = +p: no longer of one sign (the signs are used)
            det_pos = sp.expand(cert["det"].subs(p, -p))
            print(f"N={N} c={cs[ic]} u={cert['u']}: perms {tally}; cut q=s=0: det={det_cut}; "
                  f"d=0: det={det_d0}; with t01 = +p one-signed: {bool(sign_of(det_pos))}")


if __name__ == "__main__":
    main()
