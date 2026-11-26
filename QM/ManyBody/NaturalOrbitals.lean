/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Matrix.PosDef
import QM.ManyBody.ModeRotation

/-!
# Natural orbitals

The natural orbitals of a state are the eigenvectors of its one-body matrix `γ`, and the natural
occupation numbers are its eigenvalues. If `γ = W diag(n) W†`, the mode rotation `U(Wᵀ)` takes the
state to one whose one-body matrix is `diag(n)` (`QM.ManyBody.rdm1_modeRotOp`). The Pauli principle
`0 ≤ γ ≤ 1` and `tr γ = N` give `0 ≤ n_k ≤ 1` and `Σ_k n_k = N`.

## Main results

* `transpose_mem_unitaryGroup`: the transpose of a unitary matrix is unitary.
* `exists_diag_conj`: a Hermitian matrix is diagonalized as `ū γ uᵀ` with a unitary `u`.
* `natural_orbitals` (**natural orbitals**) and `natural_orbitals_ens` (ensembles).
-/

namespace QM.ManyBody

open Matrix
open scoped ComplexOrder

variable {M : ℕ}

/-- The transpose of a unitary matrix is unitary. -/
lemma transpose_mem_unitaryGroup {W : Matrix (Fin M) (Fin M) ℂ}
    (hW : W ∈ unitaryGroup (Fin M) ℂ) : Wᵀ ∈ unitaryGroup (Fin M) ℂ := by
  rw [mem_unitaryGroup_iff]
  have hW' := (mem_unitaryGroup_iff').mp hW
  ext i j
  have h := congrFun (congrFun hW' j) i
  rw [Matrix.mul_apply, Matrix.one_apply] at h ⊢
  simp only [transpose_apply, star_apply] at h ⊢
  rw [show (if i = j then (1 : ℂ) else 0) = if j = i then 1 else 0 by simp [eq_comm], ← h]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **Diagonalization by a mode rotation**: for a Hermitian `γ` there is a unitary `u` with
`ū γ uᵀ = diag(n)`, where `n` are the eigenvalues of `γ`. -/
theorem exists_diag_conj {γ : Matrix (Fin M) (Fin M) ℂ} (hγ : γ.IsHermitian) :
    ∃ u ∈ unitaryGroup (Fin M) ℂ,
      u.map star * γ * uᵀ = diagonal fun k => (hγ.eigenvalues k : ℂ) := by
  set W : Matrix (Fin M) (Fin M) ℂ := (hγ.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)
  have hWu : W ∈ unitaryGroup (Fin M) ℂ := hγ.eigenvectorUnitary.2
  have hWW : star W * W = 1 := (mem_unitaryGroup_iff').mp hWu
  have hspec : γ = W * diagonal (fun k => (hγ.eigenvalues k : ℂ)) * star W := by
    have h := hγ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  refine ⟨Wᵀ, transpose_mem_unitaryGroup hWu, ?_⟩
  have h1 : (Wᵀ).map star = star W := by ext i j; simp [star_apply]
  rw [h1, transpose_transpose]
  conv_lhs => rw [hspec]
  simp only [← Matrix.mul_assoc, hWW, Matrix.one_mul]
  rw [Matrix.mul_assoc, hWW, Matrix.mul_one]

/-- The occupation numbers of a diagonal one-body matrix with `0 ≤ γ ≤ 1` and `tr γ = N`. -/
lemma occupations_of_diag {n : Fin M → ℝ} {N : ℕ}
    (h0 : (diagonal fun k => (n k : ℂ)).PosSemidef)
    (h1 : (1 - diagonal fun k => (n k : ℂ)).PosSemidef)
    (htr : (diagonal fun k => (n k : ℂ)).trace = N) :
    (∀ k, 0 ≤ n k ∧ n k ≤ 1) ∧ ∑ k, n k = N := by
  refine ⟨fun k => ⟨?_, ?_⟩, ?_⟩
  · have h := h0.diag_nonneg (i := k)
    rw [diagonal_apply_eq] at h
    exact_mod_cast h
  · have h := h1.diag_nonneg (i := k)
    rw [Matrix.sub_apply, Matrix.one_apply_eq, diagonal_apply_eq] at h
    have h' := (Complex.nonneg_iff.mp h).1
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at h'
    linarith
  · rw [trace_diagonal] at htr
    exact_mod_cast htr

/-- **Natural orbitals**: for an `N`-particle state `Ψ` there is a mode rotation `U(u)` such that
the one-body matrix of `U(u)Ψ` is `diag(n_1, …, n_M)`, with `0 ≤ n_k ≤ 1` and `Σ_k n_k = N`. -/
theorem natural_orbitals {N : ℕ} {Ψ : Fock M} (hΨ : IsNState N Ψ) :
    ∃ u ∈ unitaryGroup (Fin M) ℂ, ∃ n : Fin M → ℝ,
      rdm1 (modeRotOp u Ψ) = diagonal (fun k => (n k : ℂ)) ∧
      (∀ k, 0 ≤ n k ∧ n k ≤ 1) ∧ ∑ k, n k = N := by
  obtain ⟨u, hu, hd⟩ := exists_diag_conj (rdm1_isHermitian Ψ)
  have hγ : rdm1 (modeRotOp u Ψ) = diagonal fun k => ((rdm1_isHermitian Ψ).eigenvalues k : ℂ) := by
    rw [rdm1_modeRotOp hu, hd]
  have hN := hΨ.modeRotOp hu
  refine ⟨u, hu, _, hγ, occupations_of_diag ?_ ?_ ?_⟩
  · rw [← hγ]; exact rdm1_posSemidef _
  · rw [← hγ]; exact one_sub_rdm1_posSemidef hN.1
  · rw [← hγ]; exact trace_rdm1 hN

/-- The one-body matrix of an ensemble transforms like that of a state. -/
lemma rdm1Ens_modeRotOp {ι : Type*} [Fintype ι] {u : Matrix (Fin M) (Fin M) ℂ}
    (hu : u ∈ unitaryGroup (Fin M) ℂ) (w : ι → ℝ) (Ψ : ι → Fock M) :
    rdm1Ens w (fun k => modeRotOp u (Ψ k)) = u.map star * rdm1Ens w Ψ * uᵀ := by
  simp only [rdm1Ens, rdm1_modeRotOp hu, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- **Natural orbitals of an ensemble.** -/
theorem natural_orbitals_ens {ι : Type*} [Fintype ι] {N : ℕ} {w : ι → ℝ} {Ψ : ι → Fock M}
    (hE : IsNEnsemble N w Ψ) :
    ∃ u ∈ unitaryGroup (Fin M) ℂ, ∃ n : Fin M → ℝ,
      rdm1Ens w (fun k => modeRotOp u (Ψ k)) = diagonal (fun k => (n k : ℂ)) ∧
      (∀ k, 0 ≤ n k ∧ n k ≤ 1) ∧ ∑ k, n k = N := by
  obtain ⟨u, hu, hd⟩ := exists_diag_conj (rdm1Ens_isHermitian w Ψ)
  have hγ : rdm1Ens w (fun k => modeRotOp u (Ψ k)) =
      diagonal fun k => ((rdm1Ens_isHermitian w Ψ).eigenvalues k : ℂ) := by
    rw [rdm1Ens_modeRotOp hu, hd]
  have hE' : IsNEnsemble N w (fun k => modeRotOp u (Ψ k)) :=
    ⟨hE.1, hE.2.1, fun k => (hE.2.2 k).modeRotOp hu⟩
  refine ⟨u, hu, _, hγ, occupations_of_diag ?_ ?_ ?_⟩
  · rw [← hγ]; exact rdm1Ens_posSemidef hE.1 _
  · rw [← hγ]; exact one_sub_rdm1Ens_posSemidef hE'
  · rw [← hγ]; exact trace_rdm1Ens hE'

end QM.ManyBody
