/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Joint orthonormal eigenbases of commuting Hermitian matrices

* `Matrix.exists_jointEigenbasis`: a commuting family of Hermitian matrices has an orthonormal
  basis of joint eigenvectors (with real eigenvalues), indexed like the matrices.
* `Matrix.re_star_dotProduct_mulVec_eq_sum`: in an eigenbasis of `A`,
  `Re⟨x, A x⟩ = Σ_k λ_k |⟨b_k, x⟩|²`.

Mathlib decomposes the space into joint eigenspaces indexed by all of `ι → 𝕜`
(`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`); only finitely many of them are
nonzero, and their standard orthonormal bases are collected and reindexed.
-/

namespace Matrix

open Module RCLike
open scoped InnerProductSpace

variable {𝕜 n ι : Type*} [RCLike 𝕜] [Fintype n]

/-- **Joint eigenbasis** of commuting Hermitian matrices. -/
theorem exists_jointEigenbasis {A : ι → Matrix n n 𝕜} (hA : ∀ i, (A i).IsHermitian)
    (hc : ∀ i j, Commute (A i) (A j)) :
    ∃ (b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (lam : n → ι → ℝ),
      ∀ k i, A i *ᵥ ⇑(b k) = (lam k i : 𝕜) • ⇑(b k) := by
  classical
  set T : ι → EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n := fun i => toEuclideanLin (A i)
  have hT : ∀ i, (T i).IsSymmetric := fun i => isSymmetric_toEuclideanLin_iff.mpr (hA i)
  have hC : Pairwise fun i j => Commute (T i) (T j) := fun i j _ => by
    refine LinearMap.ext fun x => ?_
    simp only [T, mul_apply_eq_comp]
    ext1
    simp only [toLpLin_apply, mulVec_mulVec, (hc i j).eq]
  set V : (ι → 𝕜) → Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
    fun χ => ⨅ j, Module.End.eigenspace (T j) (χ j)
  have hInt : DirectSum.IsInternal V :=
    LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hC
  have hOrth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have hInt' := DirectSum.isInternal_ne_bot_iff.2 hInt
  let _ : Fintype {χ // V χ ≠ ⊥} := hInt.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hOrth' : OrthogonalFamily 𝕜 (fun χ : {χ // V χ ≠ ⊥} => V χ)
      fun χ => (V χ).subtypeₗᵢ := hOrth.comp Subtype.val_injective
  set b₀ := hInt'.collectedOrthonormalBasis hOrth' fun χ => stdOrthonormalBasis 𝕜 (V χ.1)
  have hcard : Fintype.card (Σ χ : {χ // V χ ≠ ⊥}, Fin (finrank 𝕜 (V χ.1))) = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b₀.toBasis, finrank_euclideanSpace]
  set e := Fintype.equivOfCardEq hcard
  refine ⟨b₀.reindex e, fun k i => re ((e.symm k).1.1 i), fun k i => ?_⟩
  have hmem := hInt'.collectedOrthonormalBasis_mem hOrth' (fun χ => stdOrthonormalBasis 𝕜 (V χ.1))
    (e.symm k)
  have hmemi : b₀ (e.symm k) ∈ Module.End.eigenspace (T i) ((e.symm k).1.1 i) :=
    (Submodule.mem_iInf _).1 hmem i
  have hne : b₀ (e.symm k) ≠ 0 := b₀.orthonormal.ne_zero _
  have hreal : (((e.symm k).1.1 i : 𝕜)) = (re ((e.symm k).1.1 i) : 𝕜) :=
    (RCLike.conj_eq_iff_re.1 ((hT i).conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨hmemi, hne⟩))).symm
  have h := Module.End.mem_eigenspace_iff.1 hmemi
  rw [OrthonormalBasis.reindex_apply]
  have h' := congrArg WithLp.ofLp h
  simp only [T, toLpLin_apply, WithLp.ofLp_smul] at h'
  rw [h', ← hreal]

/-- `Re⟨x, A x⟩ = Σ_k λ_k |⟨b_k, x⟩|²` in an orthonormal eigenbasis of `A`. -/
theorem re_star_dotProduct_mulVec_eq_sum (b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n))
    {A : Matrix n n 𝕜} {lam : n → ℝ} (hb : ∀ k, A *ᵥ ⇑(b k) = (lam k : 𝕜) • ⇑(b k))
    (x : EuclideanSpace 𝕜 n) :
    re (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)) = ∑ k, lam k * ‖⟪b k, x⟫_𝕜‖ ^ 2 := by
  have hx : WithLp.ofLp x = ∑ k, ⟪b k, x⟫_𝕜 • ⇑(b k) := by
    conv_lhs => rw [← b.sum_repr' x]
    simp [WithLp.ofLp_sum, WithLp.ofLp_smul]
  have hAx : A *ᵥ WithLp.ofLp x = ∑ k, (⟪b k, x⟫_𝕜 * lam k) • ⇑(b k) := by
    rw [hx, mulVec_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mulVec_smul, hb, smul_smul]
  rw [hAx, dotProduct_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hinner : star (WithLp.ofLp x) ⬝ᵥ ⇑(b k) = ⟪x, b k⟫_𝕜 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [dotProduct_smul, hinner, smul_eq_mul, ← inner_conj_symm, mul_right_comm, RCLike.conj_mul,
    norm_conj, ← ofReal_pow, ← ofReal_mul, ofReal_re, mul_comm]

end Matrix
