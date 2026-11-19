/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.RDMFT.Stabilizer

/-!
# Universal failure of the RDMFT Hohenberg–Kohn theorem by dimension counting

Fix a nonzero state `ψ` of `N` spinless fermions on `M` sites. The map `d ↦ Γ(d) ψ` sends the
symmetric `M × M` matrices, a space of dimension `M (M + 1) / 2 = C(M + 1, 2)`, into the space of
states, of dimension `C(M, N)`. Modulo the line `ℝ ψ` the target has dimension `C(M, N) - 1`. So the
symmetric `d` with `Γ(d) ψ ∈ ℝ ψ` form a subspace of dimension at least `C(M + 1, 2) - C(M, N) + 1`.
It contains the identity. When `C(M, N) + 1 ≤ C(M + 1, 2)` it has dimension at least 2 and so
contains a non-scalar `d` (`exists_stab`).

In that case **every** state has a nontrivial one-body stabilizer. So for every interaction `W` and
every `h` with a gapped ground state, the one-body reduced density matrix does not determine `h`
(`not_rdmDetermines_of_card`). The inequality holds for `N ∈ {1, 2, M - 2, M - 1}` and for
`(M, N) = (6, 3)` (`count_of_cases`). The last case is the Borland–Dennis setting, where
`λ₁ + λ₆ = λ₂ + λ₅ = λ₃ + λ₄ = 1` for every pure state. Numerically, a generic interacting ground
state for `(M, N) = (7, 3), (7, 4), (8, 4)` has trivial stabilizer.

Symmetric matrices are parametrised by functions on `Sym2 (Fin M)` (`symOf`), whose dimension
Mathlib knows (`Sym2.card`).

* `symOf`, `symOf_isSymm`, `symOf_e1`, `eq_smul_e1_of_symOf`.
* `exists_stab`: **every nonzero state has a non-scalar one-body stabilizer** when
  `C(M, N) + 1 ≤ C(M + 1, 2)`.
* `not_rdmDetermines_of_card`: **universal failure of RDMFT-HK**.
* `card_conf`, `count_of_cases`, `not_rdmDetermines_of_cases`: the cases
  `N ∈ {1, 2, M - 2, M - 1}` and `(M, N) = (6, 3)`.
-/

namespace DFT

section

open Matrix Module

variable {M N : ℕ}

/-- The symmetric matrix `d_ij = x {i, j}`. -/
def symOf (x : Sym2 (Fin M) → ℝ) : Matrix (Fin M) (Fin M) ℝ := fun i j => x s(i, j)

lemma symOf_isSymm (x : Sym2 (Fin M) → ℝ) : (symOf x).IsSymm := by
  ext i j; simp only [symOf, Matrix.transpose_apply]; rw [Sym2.eq_swap]

/-- The function on `Sym2` that corresponds to the identity matrix. -/
def e1 : Sym2 (Fin M) → ℝ := fun e => if e.IsDiag then 1 else 0

lemma symOf_e1 : symOf (e1 (M := M)) = 1 := by
  ext i j; simp [symOf, e1, Matrix.one_apply]

lemma eq_smul_e1_of_symOf {x : Sym2 (Fin M) → ℝ} {c : ℝ} (hx : symOf x = c • 1) : x = c • e1 := by
  funext e
  induction e using Sym2.ind with
  | _ i j =>
    have := congrFun (congrFun hx i) j
    simpa [symOf, e1, Matrix.one_apply] using this

/-- **Dimension counting.** If `C(M, N) + 1 ≤ C(M + 1, 2)`, every nonzero state is an eigenvector of
a symmetric one-body operator that is not a multiple of the identity. -/
theorem exists_stab (hcount : Fintype.card (Conf M N) + 1 ≤ (M + 1).choose 2)
    {ψ : Conf M N → ℝ} (hψ : ψ ≠ 0) :
    ∃ d : Matrix (Fin M) (Fin M) ℝ, d.IsSymm ∧ (∀ c : ℝ, d ≠ c • 1) ∧
      ∃ c : ℝ, (Γ d : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ = c • ψ := by
  classical
  set S : Submodule ℝ (Conf M N → ℝ) := ℝ ∙ ψ
  let f : (Sym2 (Fin M) → ℝ) →ₗ[ℝ] (Conf M N → ℝ) :=
    { toFun := fun x => (Γ (symOf x) : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ
      map_add' := fun x y => by
        rw [show symOf (x + y) = symOf x + symOf y from rfl, gamma_add, Matrix.add_mulVec]
      map_smul' := fun a x => by
        rw [show symOf (a • x) = a • symOf x from rfl, gamma_smul, Matrix.smul_mulVec,
          RingHom.id_apply] }
  let g := S.mkQ ∘ₗ f
  have hS : finrank ℝ S = 1 := finrank_span_singleton hψ
  have hq : finrank ℝ ((Conf M N → ℝ) ⧸ S) + 1 = Fintype.card (Conf M N) := by
    rw [← hS, Submodule.finrank_quotient_add_finrank, Module.finrank_fintype_fun_eq_card]
  have hr : finrank ℝ (LinearMap.range g) ≤ finrank ℝ ((Conf M N → ℝ) ⧸ S) :=
    Submodule.finrank_le _
  have hk := LinearMap.finrank_range_add_finrank_ker g
  rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin] at hk
  have h2 : 2 ≤ finrank ℝ (LinearMap.ker g) := by omega
  obtain ⟨x, hxK, hx1⟩ : ∃ x ∈ LinearMap.ker g, x ∉ ℝ ∙ (e1 : Sym2 (Fin M) → ℝ) := by
    by_contra hc
    push Not at hc
    have hle := Submodule.finrank_mono (show LinearMap.ker g ≤ ℝ ∙ e1 from hc)
    have h1 : finrank ℝ (ℝ ∙ (e1 : Sym2 (Fin M) → ℝ)) ≤ 1 := by
      have := finrank_span_le_card (R := ℝ) ({e1} : Set (Sym2 (Fin M) → ℝ))
      simpa using this
    omega
  refine ⟨symOf x, symOf_isSymm x, fun c hc => hx1 ?_, ?_⟩
  · rw [eq_smul_e1_of_symOf hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have hfx : f x ∈ S := by
      have := LinearMap.mem_ker.mp hxK
      simpa [g, Submodule.Quotient.mk_eq_zero] using this
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hfx
    exact ⟨a, ha.symm⟩

/-- **Universal failure of the RDMFT Hohenberg–Kohn theorem.** If `C(M, N) + 1 ≤ C(M + 1, 2)`,
then for every interaction `W` and every `h` with a gapped ground state, the one-body reduced
density matrix does not determine `h` up to a constant. -/
theorem not_rdmDetermines_of_card (hcount : Fintype.card (Conf M N) + 1 ≤ (M + 1).choose 2)
    {W : Matrix (Conf M N) (Conf M N) ℝ} (hW : W.IsSymm)
    {h : Matrix (Fin M) (Fin M) ℝ} (hh : h.IsSymm) {ψ : Conf M N → ℝ}
    (hψ : IsGroundState (hamR W h) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamR W h) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamR W h) χ) :
    ¬ RDMDetermines W h := by
  obtain ⟨d, hd, hns, c, hc⟩ := exists_stab hcount hψ.1
  exact not_rdmDetermines_of_stab hW hh hψ hN hg hgap hd hns hc

lemma card_conf (M N : ℕ) : Fintype.card (Conf M N) = M.choose N := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

lemma choose_succ_two (M : ℕ) : (M + 1).choose 2 = M + M.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

/-- The counting inequality holds for `N ∈ {1, 2, M - 2, M - 1}` and `(M, N) = (6, 3)`. -/
theorem count_of_cases (h0 : 0 < N) (hNM : N < M)
    (hcase : N = 1 ∨ N = 2 ∨ N + 2 = M ∨ N + 1 = M ∨ (M = 6 ∧ N = 3)) :
    Fintype.card (Conf M N) + 1 ≤ (M + 1).choose 2 := by
  rw [card_conf, choose_succ_two]
  rcases hcase with rfl | rfl | rfl | rfl | ⟨rfl, rfl⟩
  · have := Nat.choose_pos (show 2 ≤ M by omega)
    rw [Nat.choose_one_right]; omega
  · omega
  · rw [Nat.choose_symm_add]; omega
  · rw [Nat.choose_succ_self_right]
    have := Nat.choose_pos (show 2 ≤ N + 1 by omega)
    omega
  · decide

/-- **RDMFT-HK fails for every interaction** for `N ∈ {1, 2, M - 2, M - 1}` spinless fermions on `M`
sites, and for three fermions on six sites. -/
theorem not_rdmDetermines_of_cases (h0 : 0 < N) (hNM : N < M)
    (hcase : N = 1 ∨ N = 2 ∨ N + 2 = M ∨ N + 1 = M ∨ (M = 6 ∧ N = 3))
    {W : Matrix (Conf M N) (Conf M N) ℝ} (hW : W.IsSymm)
    {h : Matrix (Fin M) (Fin M) ℝ} (hh : h.IsSymm) {ψ : Conf M N → ℝ}
    (hψ : IsGroundState (hamR W h) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamR W h) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamR W h) χ) :
    ¬ RDMDetermines W h :=
  not_rdmDetermines_of_card (count_of_cases h0 hNM hcase) hW hh hψ hN hg hgap

end

end DFT
