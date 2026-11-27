/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Convex.Continuous
import ForMathlib.Analysis.Convex.DualAttained
import DFT.Scope.Duality

/-!
# Ensemble `v`-representability for a scope

* `E_sub_le_Fe`: `E(v) - ρ·v ≤ F_e(ρ)` on `B_e`.
* `ensemble_vrep`: every `ρ` in the intrinsic (relative) interior of `B_e` is the density of an
  ensemble ground state of some `H(v)`, and `-v` is a subgradient of `F_e` at `ρ`.
* `continuousOn_Fe`: `F_e` is continuous on the intrinsic interior of `B_e`.
* `Fp_eq_Fe_of_isGS`: at the density of a pure ground state, `F_p = F_e`
  (Wang–Liebert–Penz–Schilling, Lemma 5.7).
-/

namespace DFT.Scope

open Matrix RCLike Set
open scoped ComplexOrder

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] (S : Scope 𝕜 d m)

lemma E_sub_le_Fe [Nonempty d] {ρ : m → ℝ} (hρ : ρ ∈ S.Be) (v : m → ℝ) :
    S.E v - ρ ⬝ᵥ v ≤ (S.Fe ρ).toReal := by
  have h := S.Fe_eq_iSup hρ
  rw [S.Fe_eq_toReal hρ] at h
  exact EReal.coe_le_coe_iff.1 (h ▸ le_iSup (fun v : m → ℝ => ((S.E v - ρ ⬝ᵥ v : ℝ) : EReal)) v)

/-- `E(v) - ρ·v = min_Γ (tr(H₀ Γ) + (ρ_Γ - ρ)·v)`. -/
lemma E_sub_eq_sInf [Nonempty d] (v ρ : m → ℝ) :
    S.E v - ρ ⬝ᵥ v = sInf ((fun Γ => trv S.H0 Γ + (S.dens Γ - ρ) ⬝ᵥ v) '' densMats) := by
  obtain ⟨ψ, hψ, hE⟩ := S.exists_isGS v
  refine le_antisymm (le_csInf ⟨_, _, pure_mem_densMats hψ, rfl⟩ ?_) (csInf_le ?_ ?_)
  · rintro _ ⟨Γ, hΓ, rfl⟩
    have := S.E_le_trv v hΓ
    rw [trv_ham] at this
    simp only [sub_dotProduct]
    linarith
  · exact (isCompact_densMats.image ((continuous_trv _).add
      ((S.continuous_dens.sub continuous_const).dotProduct continuous_const))).bddBelow
  · refine ⟨_, pure_mem_densMats hψ, ?_⟩
    simp only [S.dens_pure, trv_pure, sub_dotProduct, ← hE, expv_ham]
    ring

/-- **Ensemble `v`-representability**: every density in the intrinsic interior of `B_e` is the
density of an ensemble ground state of some `H(v)`, and `-v` is a subgradient of `F_e` there. -/
theorem ensemble_vrep [Nonempty d] {ρ : m → ℝ} (hρ : ρ ∈ intrinsicInterior ℝ S.Be) :
    ∃ (v : m → ℝ) (Γ : Matrix d d 𝕜), S.IsEnsGS v Γ ∧ S.dens Γ = ρ ∧
      ∀ ρ' ∈ S.Be, (S.Fe ρ).toReal + (ρ' - ρ) ⬝ᵥ (-v) ≤ (S.Fe ρ').toReal := by
  classical
  have hρB : ρ ∈ S.Be := intrinsicInterior_subset hρ
  obtain ⟨v, hv⟩ := isCompact_densMats.exists_isMaxOn_sInf_affine
    ⟨_, pure_mem_densMats (single_mem_unitVecs (𝕜 := 𝕜) (Classical.arbitrary d))⟩
    (a := fun Γ => S.dens Γ - ρ) (b := trv S.H0) (S.continuous_dens.sub continuous_const)
    (continuous_trv _) fun Γ hΓ => by
      obtain ⟨ε, hε, hmem⟩ := exists_add_smul_sub_mem_of_mem_intrinsicInterior hρ ⟨Γ, hΓ, rfl⟩
      obtain ⟨Γ', hΓ', he⟩ := hmem
      exact ⟨ε, hε, Γ', hΓ', by rw [he]; module⟩
  simp only [← E_sub_eq_sInf] at hv
  have hF : (S.Fe ρ).toReal = S.E v - ρ ⬝ᵥ v := by
    refine le_antisymm ?_ (S.E_sub_le_Fe hρB v)
    have h := S.Fe_eq_iSup hρB
    rw [S.Fe_eq_toReal hρB] at h
    exact EReal.coe_le_coe_iff.1 (h ▸ iSup_le fun v' => EReal.coe_le_coe_iff.2 (hv v'))
  obtain ⟨Γ, hΓ, hρΓ, he⟩ := S.Fe_attained hρB
  refine ⟨v, Γ, ⟨hΓ, ?_⟩, hρΓ, fun ρ' hρ' => ?_⟩
  · rw [trv_ham, hρΓ]
    rw [he, EReal.toReal_coe] at hF
    linarith
  · have := S.E_sub_le_Fe hρ' v
    rw [hF, dotProduct_neg, sub_dotProduct]
    linarith

set_option linter.unusedFintypeInType false in
-- `[Fintype m]` is used only for the finite-dimensionality of `ℝ^m`.
/-- `F_e` is continuous on the intrinsic interior of `B_e`. -/
theorem continuousOn_Fe :
    ContinuousOn (fun ρ => (S.Fe ρ).toReal) (intrinsicInterior ℝ S.Be) :=
  S.convexOn_Fe.continuousOn_intrinsicInterior

/-- At the density of a pure ground state, `F_p = F_e`. -/
theorem Fp_eq_Fe_of_isGS [Nonempty d] {v : m → ℝ} {ψ : d → 𝕜} (h : S.IsGS v ψ) :
    S.Fp (S.densPure ψ) = S.Fe (S.densPure ψ) := by
  have hρ : S.densPure ψ ∈ S.Be := S.Bp_subset_Be ⟨ψ, h.1, rfl⟩
  refine le_antisymm ((S.Fp_le h.1).trans ?_) (S.Fe_le_Fp _)
  rw [S.Fe_eq_toReal hρ, EReal.coe_le_coe_iff]
  have := S.E_sub_le_Fe hρ v
  rw [← h.2, expv_ham] at this
  linarith

end DFT.Scope
