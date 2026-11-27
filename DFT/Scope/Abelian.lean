/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.Analysis.Matrix.JointEigenbasis
import DFT.Scope.Ranges

/-!
# The ranges of an abelian scope

If the observables commute, they have a joint orthonormal eigenbasis `b_k` with joint eigenvalues
`λ_k ∈ ℝ^m`. The density of `ψ` is then `Σ_k |⟨b_k, ψ⟩|² λ_k`, a convex combination of the finitely
many joint-eigenvalue densities, and every convex combination `Σ_k q_k λ_k` is the density of the
pure state `Σ_k √q_k b_k`.

* `densPure_eq_sum`: `ρ_ψ = Σ_k |⟨b_k, ψ⟩|² λ_k`.
* `Bp_eq_Be_of_abelian`: **in an abelian scope `B_p = B_e`, and both are the convex hull of the
  finitely many joint-eigenvalue densities `λ_k`** (densities of the joint eigenvectors `b_k`).
-/

namespace DFT.Scope

open Matrix RCLike Set
open scoped ComplexOrder InnerProductSpace

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] (S : Scope 𝕜 d m)

omit [Fintype m] in
/-- In a joint eigenbasis, `ρ_ψ = Σ_k |⟨b_k, ψ⟩|² λ_k`. -/
lemma densPure_eq_sum (b : OrthonormalBasis d 𝕜 (EuclideanSpace 𝕜 d))
    {lam : d → m → ℝ} (hb : ∀ k i, S.B i *ᵥ ⇑(b k) = (lam k i : 𝕜) • ⇑(b k)) (ψ : d → 𝕜) :
    S.densPure ψ = ∑ k, ‖⟪b k, WithLp.toLp 2 ψ⟫_𝕜‖ ^ 2 • lam k := by
  funext i
  have h := re_star_dotProduct_mulVec_eq_sum b (A := S.B i) (fun k => hb k i) (WithLp.toLp 2 ψ)
  simp only [densPure, expv, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

omit [Fintype m] in
lemma sum_norm_inner_sq (b : OrthonormalBasis d 𝕜 (EuclideanSpace 𝕜 d))
    {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) : ∑ k, ‖⟪b k, WithLp.toLp 2 ψ⟫_𝕜‖ ^ 2 = 1 := by
  rw [b.sum_sq_norm_inner_right, EuclideanSpace.norm_sq_eq]
  exact sum_norm_sq_eq_one hψ

omit [Fintype m] in
/-- **The ranges of an abelian scope**: `B_p = B_e`, and both are the convex hull of the finitely
many joint-eigenvalue densities of a joint orthonormal eigenbasis. -/
theorem Bp_eq_Be_of_abelian (hS : S.IsAbelian) :
    ∃ (b : OrthonormalBasis d 𝕜 (EuclideanSpace 𝕜 d)) (lam : d → m → ℝ),
      (∀ k i, S.B i *ᵥ ⇑(b k) = (lam k i : 𝕜) • ⇑(b k)) ∧
      S.Bp = convexHull ℝ (range lam) ∧ S.Be = S.Bp := by
  obtain ⟨b, lam, hb⟩ := exists_jointEigenbasis S.isHermitian_B hS
  refine ⟨b, lam, hb, ?_⟩
  have hbu : ∀ k, (⇑(b k) : d → 𝕜) ∈ unitVecs := fun k => by
    have h := b.orthonormal.1 k
    rw [unitVecs, mem_ofPred_eq, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, h]
    simp
  have hlam : ∀ k, S.densPure (b k) = lam k := fun k => by
    funext i
    simp only [densPure, expv, hb, dotProduct_smul, smul_eq_mul]
    rw [show star (⇑(b k) : d → 𝕜) ⬝ᵥ ⇑(b k) = 1 from hbu k, mul_one, ofReal_re]
  have hsub : range lam ⊆ S.Bp := by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hbu k, hlam k⟩
  have hBp : S.Bp ⊆ convexHull ℝ (range lam) := by
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [S.densPure_eq_sum b hb]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => by positivity) (sum_norm_inner_sq b hψ)
      fun k _ => subset_convexHull ℝ _ ⟨k, rfl⟩
  -- every mixed density is a pure density
  have hBe : S.Be ⊆ S.Bp := by
    rintro _ ⟨Γ, hΓ, rfl⟩
    obtain ⟨p, u, hp, hp1, hu, -, htr⟩ := exists_decomp hΓ
    set q : d → ℝ := fun k => ∑ j, p j * ‖⟪b k, WithLp.toLp 2 (u j)⟫_𝕜‖ ^ 2
    have hq0 : ∀ k, 0 ≤ q k := fun k => Finset.sum_nonneg fun j _ => by
      have := hp j; positivity
    have hq1 : ∑ k, q k = 1 := by
      simp only [q]
      rw [Finset.sum_comm, ← hp1]
      exact Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, sum_norm_inner_sq b (hu j),
        mul_one]
    have hdens : S.dens Γ = ∑ k, q k • lam k := by
      rw [S.dens_eq_sum htr]
      simp only [S.densPure_eq_sum b hb, Finset.smul_sum, smul_smul, q, Finset.sum_smul]
      exact Finset.sum_comm
    set y : EuclideanSpace 𝕜 d :=
      b.repr.symm (WithLp.toLp 2 fun k => ((Real.sqrt (q k) : ℝ) : 𝕜))
    have hy : ∀ k, ⟪b k, y⟫_𝕜 = ((Real.sqrt (q k) : ℝ) : 𝕜) := fun k => by
      rw [← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    refine ⟨WithLp.ofLp y, ?_, ?_⟩
    · change star (WithLp.ofLp y) ⬝ᵥ WithLp.ofLp y = 1
      rw [star_dotProduct_self_eq, ← EuclideanSpace.norm_sq_eq, ← b.sum_sq_norm_inner_right]
      simp only [hy, norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hq0 _), hq1,
        ofReal_one]
    · rw [S.densPure_eq_sum b hb, hdens]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [WithLp.toLp_ofLp, hy, norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hq0 _)]
  have hBpBe : S.Bp = S.Be := le_antisymm S.Bp_subset_Be hBe
  refine ⟨le_antisymm hBp (convexHull_min hsub (hBpBe ▸ S.convex_Be)), hBpBe.symm⟩

end DFT.Scope
