/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DFT.Scope.Functionals

/-!
# Lieb duality for a scope

**`Fe_eq_iSup`**: on `B_e`, `F_e(ρ) = sup_v (E(v) - ρ·v)`: the ensemble functional is the Legendre
transform of the ground-state energy (Lieb's functional).

The proof separates the point `(ρ, c)`, `c < F_e(ρ)`, from the closed convex set
`{(ρ_Γ, tr(H₀Γ))} + {0} × [0, ∞)` (the epigraph of `F_e`) by a hyperplane; the hyperplane is not
vertical because `ρ ∈ B_e`, and its slope is the potential `v`.
-/

namespace DFT.Scope

open Matrix RCLike Set
open scoped ComplexOrder Pointwise

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] (S : Scope 𝕜 d m)

omit [Fintype d] [Fintype m] in
/-- A continuous linear functional on `ℝ^m × ℝ`, split into its two parts. -/
lemma clm_prod_apply (f : StrongDual ℝ ((m → ℝ) × ℝ)) (x : m → ℝ) (t : ℝ) :
    f (x, t) = f (x, 0) + t * f (0, 1) := by
  have : ((x, t) : (m → ℝ) × ℝ) = (x, 0) + t • ((0 : m → ℝ), (1 : ℝ)) := by simp
  rw [this, map_add, map_smul, smul_eq_mul]

omit [Fintype d] in
lemma clm_fst_apply [DecidableEq m] (f : StrongDual ℝ ((m → ℝ) × ℝ)) (x : m → ℝ) :
    f (x, 0) = x ⬝ᵥ fun i => f (fun j => if i = j then 1 else 0, 0) := by
  have h := LinearMap.pi_apply_eq_sum_univ
    ((f : (m → ℝ) × ℝ →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ (m → ℝ) ℝ)) x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
    ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h, dotProduct]

/-- The separation step: below `F_e(ρ)` there is an affine minorant `E(v) - ρ·v`. -/
lemma exists_lt_E_sub [Nonempty d] {ρ : m → ℝ} (hρ : ρ ∈ S.Be) {c : ℝ}
    (hc : c < (S.Fe ρ).toReal) : ∃ v : m → ℝ, c < S.E v - ρ ⬝ᵥ v := by
  classical
  set φ : Matrix d d 𝕜 → (m → ℝ) × ℝ := fun Γ => (S.dens Γ, trv S.H0 Γ) with hφ
  have hlin : IsLinearMap ℝ φ :=
    ⟨fun Γ₁ Γ₂ => by simp [hφ, S.dens_add, trv_add_right],
      fun r Γ => by simp [hφ, S.dens_smul, trv_smul_right]⟩
  set K := φ '' densMats
  set C : Set ((m → ℝ) × ℝ) := ({0} : Set (m → ℝ)) ×ˢ Ici (0 : ℝ)
  have hKc : IsCompact K :=
    isCompact_densMats.image (S.continuous_dens.prodMk (continuous_trv _))
  have hconv : Convex ℝ (K + C) :=
    (convex_densMats.is_linear_image hlin).add ((convex_singleton _).prod (convex_Ici _))
  have hclosed : IsClosed (K + C) :=
    (isClosed_singleton.prod isClosed_Ici).add_left_of_isCompact hKc
  have hnot : (ρ, c) ∉ K + C := by
    rintro ⟨_, ⟨Γ, hΓ, rfl⟩, ⟨x, s⟩, ⟨hx, hs⟩, heq⟩
    simp only [mem_singleton_iff] at hx
    simp only [mem_Ici] at hs
    subst hx
    simp only [hφ, Prod.mk_add_mk, add_zero, Prod.mk.injEq] at heq
    obtain ⟨rfl, hcs⟩ := heq
    have := S.Fe_toReal_le hΓ
    linarith
  obtain ⟨f, u, hfu, hfK⟩ := geometric_hahn_banach_point_closed hconv hclosed hnot
  set a := f (0, 1)
  set w : m → ℝ := fun i => f (fun j => if i = j then 1 else 0, 0)
  have hf : ∀ x t, f (x, t) = x ⬝ᵥ w + t * a := fun x t => by
    rw [clm_prod_apply, clm_fst_apply]
  have hmemK : ∀ Γ ∈ densMats, u < S.dens Γ ⬝ᵥ w + trv S.H0 Γ * a := fun Γ hΓ => by
    have := hfK (φ Γ + (0, 0)) (Set.add_mem_add ⟨Γ, hΓ, rfl⟩ ⟨rfl, le_refl (0 : ℝ)⟩)
    simpa [hφ, hf] using this
  obtain ⟨Γ₀, hΓ₀, hρ₀, he₀⟩ := S.Fe_attained hρ
  have hc₀ : c < trv S.H0 Γ₀ := by rwa [he₀, EReal.toReal_coe] at hc
  have h₀ := hmemK Γ₀ hΓ₀
  rw [hf] at hfu
  rw [hρ₀] at h₀
  -- the hyperplane is not vertical
  have ha : 0 < a := by
    by_contra ha
    have ha := not_lt.1 ha
    nlinarith
  refine ⟨(1 / a) • w, ?_⟩
  obtain ⟨ψ, hψ, hE⟩ := S.exists_isGS ((1 / a) • w)
  have hψK := hmemK _ (pure_mem_densMats hψ)
  rw [S.dens_pure, trv_pure] at hψK
  have hEψ : S.E ((1 / a) • w) * a = S.densPure ψ ⬝ᵥ w + expv S.H0 ψ * a := by
    rw [← hE, expv_ham, dotProduct_smul, smul_eq_mul]
    field_simp
    ring
  have hρv : ρ ⬝ᵥ ((1 / a) • w) * a = ρ ⬝ᵥ w := by
    rw [dotProduct_smul, smul_eq_mul]
    field_simp
  have : (c + ρ ⬝ᵥ ((1 / a) • w)) * a < S.E ((1 / a) • w) * a := by
    rw [add_mul, hρv, hEψ]; linarith
  have := lt_of_mul_lt_mul_right this ha.le
  linarith

/-- **Lieb duality**: on `B_e`, `F_e(ρ) = sup_v (E(v) - ρ·v)`. -/
theorem Fe_eq_iSup [Nonempty d] {ρ : m → ℝ} (hρ : ρ ∈ S.Be) :
    S.Fe ρ = ⨆ v : m → ℝ, ((S.E v - ρ ⬝ᵥ v : ℝ) : EReal) := by
  rw [S.Fe_eq_toReal hρ]
  refine le_antisymm ?_ (iSup_le fun v => ?_)
  · by_contra h
    have h := not_le.1 h
    obtain ⟨c, hc₁, hc₂⟩ := EReal.lt_iff_exists_real_btwn.1 h
    obtain ⟨v, hv⟩ := S.exists_lt_E_sub hρ (EReal.coe_lt_coe_iff.1 hc₂)
    exact absurd (hc₁.trans_le (le_iSup_of_le v (EReal.coe_le_coe_iff.2 hv.le))) (lt_irrefl _)
  · have h := (S.E_eq_iInf_Fe v).le.trans (iInf_le _ ρ)
    rw [S.Fe_eq_toReal hρ, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff]
    linarith

end DFT.Scope
