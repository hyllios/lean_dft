/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Matrix.PosDef
import DFT.Lattice.KohnSham.Hypersimplex
import QM.ManyBody.ModeRotation

/-!
# Coleman's theorem

A complex `M × M` matrix `γ` is the one-body reduced density matrix of an `N`-particle ensemble if
and only if it is Hermitian, `0 ≤ γ ≤ 1` and `tr γ = N`. Necessity is the Pauli principle
(`QM.ManyBody.rdm1Ens_posSemidef`, `QM.ManyBody.one_sub_rdm1Ens_posSemidef`). For sufficiency,
diagonalize `γ = W diag(λ) W†`. The eigenvalues lie in the hypersimplex, so
`λ = Σ_s μ_s occ(s)` (`DFT.hypersimplex_mixture`). The configurations `|s⟩` with weights `μ_s`
have the one-body matrix `diag(λ)`, and the mode rotation `U(W̄)` turns it into `γ`
(`QM.ManyBody.rdm1_modeRotOp`).

## Main results

* `coleman`: **Coleman's theorem**, the ensemble `N`-representability of the one-body matrix.
-/

namespace DFT.Lattice.RDMFT

open Matrix QM.ManyBody
open scoped ComplexOrder

variable {M N : ℕ}

/-- The entrywise conjugate of a unitary matrix is unitary. -/
lemma map_star_mem_unitaryGroup {W : Matrix (Fin M) (Fin M) ℂ} (hW : W ∈ unitaryGroup (Fin M) ℂ) :
    W.map star ∈ unitaryGroup (Fin M) ℂ := by
  rw [mem_unitaryGroup_iff]
  have hW' := (mem_unitaryGroup_iff).mp hW
  ext i j
  have h := congrFun (congrFun hW' j) i
  rw [Matrix.mul_apply, Matrix.one_apply] at h ⊢
  simp only [map_apply, star_apply, star_star] at h ⊢
  rw [show (if i = j then (1 : ℂ) else 0) = if j = i then 1 else 0 by simp [eq_comm], ← h]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **Coleman's theorem.** A complex matrix `γ` is the one-body reduced density matrix of an
`N`-particle ensemble if and only if `γ` is Hermitian, `0 ≤ γ ≤ 1` and `tr γ = N`. -/
theorem coleman (γ : Matrix (Fin M) (Fin M) ℂ) :
    (∃ (k : ℕ) (w : Fin k → ℝ) (Ψ : Fin k → Fock M), IsNEnsemble N w Ψ ∧ rdm1Ens w Ψ = γ) ↔
      γ.IsHermitian ∧ γ.PosSemidef ∧ (1 - γ).PosSemidef ∧ γ.trace = N := by
  constructor
  · rintro ⟨k, w, Ψ, hE, rfl⟩
    exact ⟨rdm1Ens_isHermitian w Ψ, rdm1Ens_posSemidef hE.1 Ψ, one_sub_rdm1Ens_posSemidef hE,
      trace_rdm1Ens hE⟩
  rintro ⟨hH, hP, hQ, htr⟩
  -- diagonalize `γ = W diag(d) W†`
  set W : Matrix (Fin M) (Fin M) ℂ := (hH.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ) with hWdef
  set d : Fin M → ℝ := hH.eigenvalues with hddef
  have hWu : W ∈ unitaryGroup (Fin M) ℂ := hH.eigenvectorUnitary.2
  have hWW : star W * W = 1 := (mem_unitaryGroup_iff').mp hWu
  have hspec : γ = W * diagonal (fun i => (d i : ℂ)) * star W := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hD : star W * γ * W = diagonal (fun i => (d i : ℂ)) := by
    rw [hspec]
    simp only [← mul_assoc, hWW, one_mul]
    rw [mul_assoc, hWW, mul_one]
  -- the eigenvalues lie in the hypersimplex
  have hbox : ∀ i, 0 ≤ d i ∧ d i ≤ 1 := by
    intro i
    refine ⟨Matrix.PosSemidef.eigenvalues_nonneg hP i, ?_⟩
    have h := (hQ.conjTranspose_mul_mul_same W).diag_nonneg (i := i)
    rw [← star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, mul_one, hWW, hD, Matrix.sub_apply,
      Matrix.one_apply_eq, diagonal_apply_eq] at h
    have h' := (Complex.nonneg_iff.mp h).1
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at h'
    linarith
  have hsum : ∑ i, d i = N := by
    have h := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at h
    simp only [Complex.natCast_re] at h
    exact h.symm
  obtain ⟨μ, hμ0, hμ1, hμd⟩ := hypersimplex_mixture (N := N) (nfrac d) d rfl hbox hsum
  -- the ensemble of rotated configurations
  set u := W.map star with hudef
  have hu : u ∈ unitaryGroup (Fin M) ℂ := map_star_mem_unitaryGroup hWu
  have hubar : u.map star = W := by ext i j; simp [hudef]
  have hut : uᵀ = star W := by ext i j; simp [hudef, star_apply]
  set e := (Fintype.equivFin (Conf M N)).symm
  refine ⟨Fintype.card (Conf M N), fun j => μ (e j),
    fun j => modeRotOp u (EuclideanSpace.single (e j).1 1), ⟨fun j => hμ0 _, ?_, fun j => ?_⟩, ?_⟩
  · rw [Equiv.sum_comp e μ, hμ1]
  · have h := isNState_single (M := M) (e j).1
    rw [(e j).2] at h
    exact h.modeRotOp hu
  · rw [rdm1Ens, Equiv.sum_comp e (fun s => ((μ s : ℝ) : ℂ) •
      rdm1 (modeRotOp u (EuclideanSpace.single s.1 1)))]
    simp_rw [rdm1_modeRotOp hu, rdm1_single, hubar, hut]
    have hdiag : ∑ s : Conf M N,
        ((μ s : ℝ) : ℂ) • diagonal (fun i => if i ∈ s.1 then (1 : ℂ) else 0) =
          diagonal (fun i => (d i : ℂ)) := by
      ext i j
      rw [Matrix.sum_apply, diagonal_apply]
      simp only [Matrix.smul_apply, diagonal_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        simp only [ite_true]
        rw [congrFun hμd i]
        push_cast
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [occF]
        split_ifs <;> simp
      · simp [hij]
    rw [hspec, ← hdiag, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]

end DFT.Lattice.RDMFT
