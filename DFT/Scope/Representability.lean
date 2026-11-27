/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Convex.Continuous
import ForMathlib.Analysis.Convex.DualAttained
import DFT.Scope.Duality
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Ensemble `v`-representability for a scope

* `E_sub_le_Fe`: `E(v) - ρ·v ≤ F_e(ρ)` on `B_e`.
* `mem_Be_of_isMax`, `exists_isEnsGS_of_isMax`: a maximiser `v` of `E(·) - ρ·(·)` forces `ρ ∈ B_e`
  and makes `ρ` the density of an ensemble ground state of `H(v)`.
* `ensemble_vrep_of_extend`, `ensemble_vrep`: every `ρ` in the relative interior of `B_e` (in the
  algebraic form, or the intrinsic interior) is the density of an ensemble ground state of some
  `H(v)`, and `-v` is a subgradient of `F_e` at `ρ`.
* `IsEnsGS.ham_mul`: an ensemble ground state satisfies `H(v) Γ = E(v) Γ`.
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

omit [Fintype m] in
/-- A linear functional on `ℝ^m` is a dot product. -/
lemma clm_eq_dotProduct (f : StrongDual ℝ (m → ℝ)) [Fintype m] [DecidableEq m] (x : m → ℝ) :
    f x = x ⬝ᵥ fun i => f fun j => if i = j then 1 else 0 := by
  have h := LinearMap.pi_apply_eq_sum_univ (f : (m → ℝ) →ₗ[ℝ] ℝ) x
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h, dotProduct]

/-- If `v` maximises `E(·) - ρ·(·)`, then `ρ ∈ B_e`: off `B_e` the potential can always be
improved in a direction separating `ρ` from `B_e`. -/
lemma mem_Be_of_isMax [Nonempty d] {ρ v : m → ℝ}
    (hmax : ∀ v', S.E v' - ρ ⬝ᵥ v' ≤ S.E v - ρ ⬝ᵥ v) : ρ ∈ S.Be := by
  classical
  by_contra hρ
  obtain ⟨f, u, hfρ, hfB⟩ :=
    geometric_hahn_banach_point_closed S.convex_Be S.isCompact_Be.isClosed hρ
  set w : m → ℝ := fun i => f fun j => if i = j then 1 else 0
  obtain ⟨ψ, hψ, hE⟩ := S.exists_isGS (v + w)
  have h1 := hmax (v + w)
  have hEv := S.E_le v hψ
  have hu := hfB _ (S.Bp_subset_Be ⟨ψ, hψ, rfl⟩)
  rw [clm_eq_dotProduct] at hu hfρ
  rw [← hE, expv_ham, dotProduct_add, dotProduct_add] at h1
  rw [expv_ham] at hEv
  linarith

/-- **A maximiser of `E(·) - ρ·(·)` is a potential for `ρ`**: `ρ` is the density of an ensemble
ground state of `H(v)`, and `F_e(ρ) = E(v) - ρ·v`. -/
theorem exists_isEnsGS_of_isMax [Nonempty d] {ρ v : m → ℝ}
    (hmax : ∀ v', S.E v' - ρ ⬝ᵥ v' ≤ S.E v - ρ ⬝ᵥ v) :
    ∃ Γ : Matrix d d 𝕜, S.IsEnsGS v Γ ∧ S.dens Γ = ρ ∧ (S.Fe ρ).toReal = S.E v - ρ ⬝ᵥ v := by
  have hρB := S.mem_Be_of_isMax hmax
  have hF : (S.Fe ρ).toReal = S.E v - ρ ⬝ᵥ v := by
    refine le_antisymm ?_ (S.E_sub_le_Fe hρB v)
    have h := S.Fe_eq_iSup hρB
    rw [S.Fe_eq_toReal hρB] at h
    exact EReal.coe_le_coe_iff.1 (h ▸ iSup_le fun v' => EReal.coe_le_coe_iff.2 (hmax v'))
  obtain ⟨Γ, hΓ, hρΓ, he⟩ := S.Fe_attained hρB
  refine ⟨Γ, ⟨hΓ, ?_⟩, hρΓ, hF⟩
  rw [trv_ham, hρΓ]
  rw [he, EReal.toReal_coe] at hF
  linarith

/-- **Ensemble `v`-representability**, algebraic form: if one can step a little beyond `ρ` away
from every point of `B_e` and stay in `B_e` (so `ρ` is in the relative interior), then `ρ` is the
density of an ensemble ground state of some `H(v)`, and `-v` is a subgradient of `F_e` at `ρ`. -/
theorem ensemble_vrep_of_extend [Nonempty d] {ρ : m → ℝ}
    (hext : ∀ ρ' ∈ S.Be, ∃ ε > (0 : ℝ), ρ + ε • (ρ - ρ') ∈ S.Be) :
    ∃ (v : m → ℝ) (Γ : Matrix d d 𝕜), S.IsEnsGS v Γ ∧ S.dens Γ = ρ ∧
      ∀ ρ' ∈ S.Be, (S.Fe ρ).toReal + (ρ' - ρ) ⬝ᵥ (-v) ≤ (S.Fe ρ').toReal := by
  classical
  obtain ⟨v, hv⟩ := isCompact_densMats.exists_isMaxOn_sInf_affine
    ⟨_, pure_mem_densMats (single_mem_unitVecs (𝕜 := 𝕜) (Classical.arbitrary d))⟩
    (a := fun Γ => S.dens Γ - ρ) (b := trv S.H0) (S.continuous_dens.sub continuous_const)
    (continuous_trv _) fun Γ hΓ => by
      obtain ⟨ε, hε, hmem⟩ := hext _ ⟨Γ, hΓ, rfl⟩
      obtain ⟨Γ', hΓ', he⟩ := hmem
      exact ⟨ε, hε, Γ', hΓ', by rw [he]; module⟩
  simp only [← E_sub_eq_sInf] at hv
  obtain ⟨Γ, hΓ, hρΓ, hF⟩ := S.exists_isEnsGS_of_isMax hv
  refine ⟨v, Γ, hΓ, hρΓ, fun ρ' hρ' => ?_⟩
  have := S.E_sub_le_Fe hρ' v
  rw [hF, dotProduct_neg, sub_dotProduct]
  linarith

/-- **Ensemble `v`-representability**: every density in the intrinsic interior of `B_e` is the
density of an ensemble ground state of some `H(v)`, and `-v` is a subgradient of `F_e` there. -/
theorem ensemble_vrep [Nonempty d] {ρ : m → ℝ} (hρ : ρ ∈ intrinsicInterior ℝ S.Be) :
    ∃ (v : m → ℝ) (Γ : Matrix d d 𝕜), S.IsEnsGS v Γ ∧ S.dens Γ = ρ ∧
      ∀ ρ' ∈ S.Be, (S.Fe ρ).toReal + (ρ' - ρ) ⬝ᵥ (-v) ≤ (S.Fe ρ').toReal :=
  S.ensemble_vrep_of_extend fun _ hρ' =>
    exists_add_smul_sub_mem_of_mem_intrinsicInterior hρ hρ'

/-- An ensemble ground state is supported on the ground-state space: `H(v) Γ = E(v) Γ`. -/
theorem IsEnsGS.ham_mul {v : m → ℝ} {Γ : Matrix d d 𝕜} (h : S.IsEnsGS v Γ) :
    S.ham v * Γ = (S.E v : 𝕜) • Γ := by
  classical
  obtain ⟨p, u, hp, hp1, hu, hΓe, htr⟩ := exists_decomp h.1
  -- every spectral component with positive weight is a ground state
  have hzero : ∀ k, p k * (expv (S.ham v) (u k) - S.E v) = 0 := by
    have hsum : ∑ k, p k * (expv (S.ham v) (u k) - S.E v) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, ← htr, h.2,
        sub_self]
    exact fun k => (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (hp k) (sub_nonneg.2 (S.E_le v (hu k)))).1 hsum k (Finset.mem_univ _)
  have heig : ∀ k, p k ≠ 0 → S.ham v *ᵥ u k = (S.E v : 𝕜) • u k := fun k hk =>
    (S.isHermitian_ham v).mulVec_eq_of_le (fun _ hφ => S.E_le v hφ) (hu k)
      (by have := hzero k; rw [mul_eq_zero] at this
          exact sub_eq_zero.1 (this.resolve_left hk))
  rw [hΓe, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : p k = 0
  · simp [hk]
  · rw [Matrix.mul_smul, mul_vecMulVec, heig k hk, smul_vecMulVec, smul_comm]

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
