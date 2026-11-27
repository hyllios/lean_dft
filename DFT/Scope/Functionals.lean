/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.Topology.Semicontinuity.FiberInf
import DFT.Scope.Ranges

/-!
# The constrained-search functionals of a scope

* `Fp_eq_top`, `Fe_eq_top`: `⊤` off the ranges; `Fp_attained`, `Fe_attained`: on the ranges the
  infima are minima.
* `lowerSemicontinuous_Fp`, `lowerSemicontinuous_Fe`.
* `Fe_le_Fp`.
* `E_eq_iInf_Fp`, `E_eq_iInf_Fe`: `E(v) = inf_ρ (F(ρ) + ρ·v)` for both functionals.
* `convexOn_Fe`: `F_e` is convex on `B_e`.
* `le_Fe_of_convexOn`: every convex function below `F_p` on `B_p` is below `F_e` on `B_e`, so
  `F_e` (convex, lower semicontinuous, `≤ F_p`) is the greatest convex lower semicontinuous minorant
  of `F_p`.
-/

namespace DFT.Scope

open Matrix RCLike Set
open scoped ComplexOrder

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] (S : Scope 𝕜 d m)

omit [Fintype m] in
lemma Fp_eq_top {ρ : m → ℝ} (hρ : ρ ∉ S.Bp) : S.Fp ρ = ⊤ := iInf_fiber_eq_top hρ

omit [Fintype m] in
lemma Fe_eq_top {ρ : m → ℝ} (hρ : ρ ∉ S.Be) : S.Fe ρ = ⊤ := iInf_fiber_eq_top hρ

omit [Fintype m] in
/-- On `B_p` the pure constrained search is a minimum. -/
theorem Fp_attained {ρ : m → ℝ} (hρ : ρ ∈ S.Bp) :
    ∃ ψ ∈ unitVecs, S.densPure ψ = ρ ∧ S.Fp ρ = expv S.H0 ψ :=
  isCompact_unitVecs.exists_eq_iInf_fiber S.continuous_densPure.continuousOn
    (continuous_expv _).continuousOn hρ

omit [Fintype m] in
/-- On `B_e` the ensemble constrained search is a minimum. -/
theorem Fe_attained {ρ : m → ℝ} (hρ : ρ ∈ S.Be) :
    ∃ Γ ∈ densMats, S.dens Γ = ρ ∧ S.Fe ρ = trv S.H0 Γ := by
  classical
  exact isCompact_densMats.exists_eq_iInf_fiber S.continuous_dens.continuousOn
    (continuous_trv _).continuousOn hρ

omit [Fintype m] in
theorem lowerSemicontinuous_Fp : LowerSemicontinuous S.Fp :=
  isCompact_unitVecs.lowerSemicontinuous_iInf_fiber S.continuous_densPure.continuousOn
    (continuous_expv _).continuousOn

omit [Fintype m] in
theorem lowerSemicontinuous_Fe : LowerSemicontinuous S.Fe := by
  classical
  exact isCompact_densMats.lowerSemicontinuous_iInf_fiber S.continuous_dens.continuousOn
    (continuous_trv _).continuousOn

omit [Fintype m] in
lemma Fp_le {ψ : d → 𝕜} (hψ : ψ ∈ unitVecs) : S.Fp (S.densPure ψ) ≤ expv S.H0 ψ :=
  iInf₂_le (f := fun ψ' (_ : ψ' ∈ {ψ' ∈ unitVecs | S.densPure ψ' = S.densPure ψ}) =>
    (expv S.H0 ψ' : EReal)) ψ ⟨hψ, rfl⟩

omit [Fintype m] in
lemma Fe_le {Γ : Matrix d d 𝕜} (hΓ : Γ ∈ densMats) : S.Fe (S.dens Γ) ≤ trv S.H0 Γ :=
  iInf₂_le (f := fun Γ' (_ : Γ' ∈ {Γ' ∈ densMats | S.dens Γ' = S.dens Γ}) =>
    (trv S.H0 Γ' : EReal)) Γ ⟨hΓ, rfl⟩

omit [Fintype m] in
theorem Fe_le_Fp (ρ : m → ℝ) : S.Fe ρ ≤ S.Fp ρ := by
  refine le_iInf₂ fun ψ hψ => ?_
  have h := S.Fe_le (pure_mem_densMats hψ.1)
  rwa [S.dens_pure, hψ.2, trv_pure] at h

omit [Fintype m] in
/-- On `B_e`, `F_e` is real: its real part is below `tr(H₀ Γ)` for every `Γ` with density `ρ`. -/
lemma Fe_toReal_le {Γ : Matrix d d 𝕜} (hΓ : Γ ∈ densMats) :
    (S.Fe (S.dens Γ)).toReal ≤ trv S.H0 Γ := by
  obtain ⟨Γ₀, -, -, he⟩ := S.Fe_attained ⟨Γ, hΓ, rfl⟩
  have h := S.Fe_le hΓ
  rw [he, EReal.coe_le_coe_iff] at h
  rwa [he, EReal.toReal_coe]

omit [Fintype m] in
lemma Fe_eq_toReal {ρ : m → ℝ} (hρ : ρ ∈ S.Be) : S.Fe ρ = (S.Fe ρ).toReal := by
  obtain ⟨Γ₀, -, -, he⟩ := S.Fe_attained hρ
  rw [he, EReal.toReal_coe]

omit [Fintype m] in
lemma Fp_eq_toReal {ρ : m → ℝ} (hρ : ρ ∈ S.Bp) : S.Fp ρ = (S.Fp ρ).toReal := by
  obtain ⟨ψ, -, -, he⟩ := S.Fp_attained hρ
  rw [he, EReal.toReal_coe]

/-- **`E(v) = inf_ρ (F_p(ρ) + ρ·v)`.** -/
theorem E_eq_iInf_Fp [Nonempty d] (v : m → ℝ) :
    (S.E v : EReal) = ⨅ ρ, S.Fp ρ + ((ρ ⬝ᵥ v : ℝ) : EReal) := by
  classical
  refine le_antisymm (le_iInf fun ρ => ?_) ?_
  · by_cases hρ : ρ ∈ S.Bp
    · obtain ⟨ψ, hψ, rfl, he⟩ := S.Fp_attained hρ
      rw [he, ← EReal.coe_add, EReal.coe_le_coe_iff, ← expv_ham]
      exact S.E_le v hψ
    · rw [S.Fp_eq_top hρ, EReal.top_add_coe]
      exact le_top
  · obtain ⟨ψ, hψ, he⟩ := S.exists_isGS v
    refine (iInf_le _ (S.densPure ψ)).trans ?_
    rw [← he, expv_ham, EReal.coe_add]
    exact add_le_add_left (S.Fp_le hψ) _

/-- **`E(v) = inf_ρ (F_e(ρ) + ρ·v)`.** -/
theorem E_eq_iInf_Fe [Nonempty d] (v : m → ℝ) :
    (S.E v : EReal) = ⨅ ρ, S.Fe ρ + ((ρ ⬝ᵥ v : ℝ) : EReal) := by
  refine le_antisymm (le_iInf fun ρ => ?_) ?_
  · by_cases hρ : ρ ∈ S.Be
    · obtain ⟨Γ, hΓ, rfl, he⟩ := S.Fe_attained hρ
      rw [he, ← EReal.coe_add, EReal.coe_le_coe_iff, ← trv_ham]
      exact S.E_le_trv v hΓ
    · rw [S.Fe_eq_top hρ, EReal.top_add_coe]
      exact le_top
  · rw [S.E_eq_iInf_Fp v]
    exact iInf_mono fun ρ => add_le_add_left (S.Fe_le_Fp ρ) _

omit [Fintype m] in
/-- **`F_e` is convex** on `B_e`. -/
theorem convexOn_Fe : ConvexOn ℝ S.Be fun ρ => (S.Fe ρ).toReal := by
  refine ⟨S.convex_Be, ?_⟩
  rintro _ hρ₁ _ hρ₂ a b ha hb hab
  obtain ⟨Γ₁, h₁, rfl, he₁⟩ := S.Fe_attained hρ₁
  obtain ⟨Γ₂, h₂, rfl, he₂⟩ := S.Fe_attained hρ₂
  have h := S.Fe_toReal_le (convex_densMats h₁ h₂ ha hb hab)
  rw [S.dens_add, S.dens_smul, S.dens_smul, trv_add_right, trv_smul_right, trv_smul_right] at h
  simpa only [he₁, he₂, EReal.toReal_coe, smul_eq_mul] using h

omit [Fintype m] in
/-- **`F_e` is the greatest convex minorant of `F_p`**: a convex function on `B_e` that is below
`F_p` on `B_p` is below `F_e` on `B_e`. -/
theorem le_Fe_of_convexOn {G : (m → ℝ) → ℝ} (hG : ConvexOn ℝ S.Be G)
    (hle : ∀ ρ ∈ S.Bp, (G ρ : EReal) ≤ S.Fp ρ) {ρ : m → ℝ} (hρ : ρ ∈ S.Be) :
    (G ρ : EReal) ≤ S.Fe ρ := by
  obtain ⟨Γ, hΓ, rfl, he⟩ := S.Fe_attained hρ
  obtain ⟨p, u, hp, hp1, hu, -, htr⟩ := exists_decomp hΓ
  rw [he, EReal.coe_le_coe_iff, htr, S.dens_eq_sum htr]
  refine (hG.map_sum_le (fun k _ => hp k) hp1
    fun k _ => S.Bp_subset_Be ⟨u k, hu k, rfl⟩).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hp k)
  have h := (hle _ ⟨u k, hu k, rfl⟩).trans (S.Fp_le (hu k))
  exact EReal.coe_le_coe_iff.1 h

end DFT.Scope
