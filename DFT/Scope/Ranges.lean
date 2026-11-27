/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Convex.Combination
import DFT.Scope.Basic

/-!
# The pure and the ensemble ranges of a scope

* `isCompact_Bp`, `isCompact_Be`: both ranges are compact.
* `convex_densMats`, `convex_Be`: density matrices, and hence ensemble densities, form convex sets.
* `dens_eq_sum`: the density of a mixed state is the convex combination of the densities of its
  spectral components.
* `Be_eq_convexHull_Bp`: `B_e = conv B_p` (Wang–Liebert–Penz–Schilling, §III).
-/

namespace DFT.Scope

open Matrix RCLike Set
open scoped ComplexOrder

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] (S : Scope 𝕜 d m)

omit [Fintype m] in
lemma isCompact_Bp : IsCompact S.Bp := isCompact_unitVecs.image S.continuous_densPure

omit [Fintype m] in
lemma isCompact_Be : IsCompact S.Be := by
  classical
  exact isCompact_densMats.image S.continuous_dens

omit [Fintype m] in
lemma Bp_subset_Be : S.Bp ⊆ S.Be := by
  rintro _ ⟨ψ, hψ, rfl⟩
  exact ⟨_, pure_mem_densMats hψ, S.dens_pure ψ⟩

lemma convex_densMats : Convex ℝ (densMats : Set (Matrix d d 𝕜)) := by
  intro Γ₁ h₁ Γ₂ h₂ a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) a, RCLike.real_smul_eq_coe_smul (K := 𝕜) b]
    exact (h₁.1.smul (by exact_mod_cast ha)).add (h₂.1.smul (by exact_mod_cast hb))
  · rw [trace_add, trace_smul, trace_smul, h₁.2, h₂.2, ← add_smul, hab, one_smul]

omit [Fintype m] in
lemma convex_Be : Convex ℝ S.Be := by
  rintro _ ⟨Γ₁, h₁, rfl⟩ _ ⟨Γ₂, h₂, rfl⟩ a b ha hb hab
  exact ⟨a • Γ₁ + b • Γ₂, convex_densMats h₁ h₂ ha hb hab, by
    rw [S.dens_add, S.dens_smul, S.dens_smul]⟩

omit [Fintype m] in
/-- The density of a mixed state is the convex combination of the densities of its spectral
components. -/
lemma dens_eq_sum {Γ : Matrix d d 𝕜} {p : d → ℝ} {u : d → d → 𝕜}
    (htr : ∀ A : Matrix d d 𝕜, trv A Γ = ∑ k, p k * expv A (u k)) :
    S.dens Γ = ∑ k, p k • S.densPure (u k) := by
  funext i
  simp only [dens, htr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, densPure]

omit [Fintype m] in
/-- **The ensemble range is the convex hull of the pure range.** -/
theorem Be_eq_convexHull_Bp : S.Be = convexHull ℝ S.Bp := by
  classical
  refine le_antisymm ?_ (convexHull_min S.Bp_subset_Be S.convex_Be)
  rintro _ ⟨Γ, hΓ, rfl⟩
  obtain ⟨p, u, hp, hp1, hu, -, htr⟩ := exists_decomp hΓ
  rw [S.dens_eq_sum htr]
  exact (convex_convexHull ℝ _).sum_mem (fun k _ => hp k) hp1
    fun k _ => subset_convexHull ℝ _ ⟨u k, hu k, rfl⟩

end DFT.Scope
