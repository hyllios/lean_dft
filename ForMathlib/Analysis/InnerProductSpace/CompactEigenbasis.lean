/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# An eigenbasis for a compact symmetric injective operator

For a compact, symmetric, injective operator `T` on a real Hilbert space, choose an orthonormal
basis of each (finite-dimensional) eigenspace; together they form a Hilbert basis (the spectral
theorem `orthogonalComplement_iSup_eigenspaces_eq_bot`). Only finitely many basis vectors have
eigenvalue at least `δ > 0`: orthonormal eigenvectors with eigenvalues `≥ δ` have images at mutual
distance `≥ √2 δ`, which compactness forbids for infinitely many of them.

* `EIdx T`: the index type, pairs (eigenvalue, index in its eigenspace).
* `eigenBasis`: the Hilbert basis; `eigenBasis_apply`: `T eᵢ = μᵢ eᵢ`.
* `finite_ge`: `{i | δ ≤ μᵢ}` is finite for `δ > 0`.
-/

namespace DFT.Continuum.Spectral

open Module End Submodule Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {T : E →L[ℝ] E}

/-- The eigenvalues of `T`. -/
abbrev EVal (T : E →L[ℝ] E) := {μ : ℝ // HasEigenvalue (T : End ℝ E) μ}

omit [CompleteSpace E] in
lemma eval_ne_zero (hinj : ∀ f, T f = 0 → f = 0) (μ : EVal T) : (μ : ℝ) ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := μ.2.exists_hasEigenvector
  rw [h0, mem_genEigenspace_one, zero_smul] at hv
  exact hv0 (hinj v hv)

/-- Eigenspaces of a compact operator for nonzero eigenvalues are finite-dimensional. -/
lemma instFDEigen (hT : IsCompactOperator T) (hinj : ∀ f, T f = 0 → f = 0)
    (μ : EVal T) : FiniteDimensional ℝ (eigenspace (T : End ℝ E) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hT μ (eval_ne_zero hinj μ)

/-- The index type of the eigenbasis. -/
abbrev EIdx (T : E →L[ℝ] E) :=
  Σ μ : EVal T, Fin (finrank ℝ (eigenspace (T : End ℝ E) (μ : ℝ)))

/-- The orthonormal basis of each eigenspace. -/
noncomputable def eigOB (hT : IsCompactOperator T) (hinj : ∀ f, T f = 0 → f = 0) (μ : EVal T) :
    OrthonormalBasis (Fin (finrank ℝ (eigenspace (T : End ℝ E) (μ : ℝ)))) ℝ
      (eigenspace (T : End ℝ E) (μ : ℝ)) :=
  haveI := instFDEigen hT hinj μ
  stdOrthonormalBasis ℝ _ |>.reindex (finCongr (by rfl))

/-- The eigenvectors. -/
noncomputable def eigVec (hT : IsCompactOperator T) (hinj : ∀ f, T f = 0 → f = 0) (i : EIdx T) :
    E := (eigOB hT hinj i.1 i.2 : E)

variable (hT : IsCompactOperator T) (hS : (T : E →ₗ[ℝ] E).IsSymmetric)
  (hinj : ∀ f, T f = 0 → f = 0)

lemma eigVec_apply (i : EIdx T) : T (eigVec hT hinj i) = (i.1 : ℝ) • eigVec hT hinj i := by
  have h := (eigOB hT hinj i.1 i.2).2
  rw [mem_eigenspace_iff] at h
  exact h

include hS in
lemma orthonormal_eigVec : Orthonormal ℝ (eigVec hT hinj) := by
  have hfam := (hS.orthogonalFamily_eigenspaces).comp (Subtype.val_injective (p := fun μ : ℝ =>
    HasEigenvalue (T : End ℝ E) μ))
  exact hfam.orthonormal_sigma_orthonormal fun μ => (eigOB hT hinj μ).orthonormal

include hS in
lemma span_eigVec_orthogonal : (span ℝ (Set.range (eigVec hT hinj)))ᗮ = ⊥ := by
  have hle : (⨆ μ, eigenspace (T : End ℝ E) μ) ≤ span ℝ (Set.range (eigVec hT hinj)) := by
    refine iSup_le fun μ => ?_
    by_cases hμ : HasEigenvalue (T : End ℝ E) μ
    · intro v hv
      set μ' : EVal T := ⟨μ, hμ⟩
      have hv' : (⟨v, hv⟩ : eigenspace (T : End ℝ E) μ) =
          ∑ j, (eigOB hT hinj μ').repr ⟨v, hv⟩ j • eigOB hT hinj μ' j :=
        ((eigOB hT hinj μ').sum_repr ⟨v, hv⟩).symm
      have : v = ∑ j, (eigOB hT hinj μ').repr ⟨v, hv⟩ j • eigVec hT hinj ⟨μ', j⟩ := by
        have := congrArg Subtype.val hv'
        simpa [eigVec] using this
      rw [this]
      exact sum_mem fun j _ => smul_mem _ _ (subset_span ⟨⟨μ', j⟩, rfl⟩)
    · rw [hasEigenvalue_iff, not_not] at hμ
      rw [hμ]; exact bot_le
  exact eq_bot_iff.2 ((orthogonal_le hle).trans
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hS).le)

/-- **The eigenbasis** of a compact symmetric injective operator. -/
noncomputable def eigenBasis : HilbertBasis (EIdx T) ℝ E :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_eigVec hT hS hinj)
    (span_eigVec_orthogonal hT hS hinj)

lemma eigenBasis_coe : ⇑(eigenBasis hT hS hinj) = eigVec hT hinj :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

include hT hS hinj in
/-- **Only finitely many basis vectors have eigenvalue at least `δ > 0`.** -/
theorem finite_ge {δ : ℝ} (hδ : 0 < δ) : {i : EIdx T | δ ≤ (i.1 : ℝ)}.Finite := by
  by_contra hinf
  obtain ⟨K, hK, hKn⟩ := id hT
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hKn
  set s : ℕ → EIdx T := fun n => (Set.Infinite.natEmbedding _ hinf n : EIdx T)
  have hs_inj : Function.Injective s := fun a b h =>
    (Set.Infinite.natEmbedding _ hinf).injective (Subtype.ext h)
  have hs_ge : ∀ n, δ ≤ ((s n).1 : ℝ) := fun n => (Set.Infinite.natEmbedding _ hinf n).2
  set y : ℕ → E := fun n => T ((r / 2) • eigVec hT hinj (s n))
  have hyK : ∀ n, y n ∈ K := fun n => hball (by
    rw [mem_ball, dist_zero_right, norm_smul, (orthonormal_eigVec hT hS hinj).1, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  obtain ⟨z, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hyK
  have hcau := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcau
  obtain ⟨N, hN⟩ := hcau (r / 2 * δ) (by positivity)
  have hlt := hN (N + 1) (Nat.le_succ N)
  -- but distinct orthonormal eigenvectors have far-apart images
  set a := s (φ (N + 1))
  set b := s (φ N)
  have hab : a ≠ b := fun h => (hφ (Nat.lt_succ_self N)).ne' (hs_inj h)
  have horth := orthonormal_eigVec hT hS hinj
  have hy : ∀ n, y n = (r / 2 * ((s n).1 : ℝ)) • eigVec hT hinj (s n) := fun n => by
    simp only [y, map_smul, eigVec_apply, smul_smul]
  have hdist : (r / 2 * δ) ^ 2 * 2 ≤ dist (y (φ (N + 1))) (y (φ N)) ^ 2 := by
    rw [dist_eq_norm, hy, hy, @norm_sub_sq_real, norm_smul, norm_smul, horth.1, horth.1,
      inner_smul_left, inner_smul_right, horth.2 hab]
    simp only [mul_one, Real.norm_eq_abs, mul_zero, sub_zero, RCLike.conj_to_real]
    have ha := hs_ge (φ (N + 1))
    have hb := hs_ge (φ N)
    have h1 : r / 2 * δ ≤ |r / 2 * ((a).1 : ℝ)| := by
      rw [abs_of_pos (mul_pos (by positivity) (hδ.trans_le ha))]
      exact mul_le_mul_of_nonneg_left ha (by positivity)
    have h2 : r / 2 * δ ≤ |r / 2 * ((b).1 : ℝ)| := by
      rw [abs_of_pos (mul_pos (by positivity) (hδ.trans_le hb))]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    nlinarith [mul_self_le_mul_self (by positivity) h1, mul_self_le_mul_self (by positivity) h2]
  have hpos : 0 < r / 2 * δ := by positivity
  have : dist (y (φ (N + 1))) (y (φ N)) ^ 2 < (r / 2 * δ) ^ 2 :=
    pow_lt_pow_left₀ hlt dist_nonneg two_ne_zero
  nlinarith

end DFT.Continuum.Spectral
