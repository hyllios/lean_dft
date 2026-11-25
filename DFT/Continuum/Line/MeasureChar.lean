/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasureHK

/-!
# Measure-`v`-representable densities, explicitly (one particle)

`vrepMeas_iff` characterises the ground-state densities of measure potentials through a weak
equation. Here the condition is made explicit, without test functions: `g''/g` is a finite measure.

* `Gρ_add`, `Gρ_smul`: `G_ρ` is additive in `ρ`.
* `weak_of_deriv`: if `g' = c + G₊ - G₋` a.e. (`G_ρ(t) = ∫_{x<t} g dρ`), then
  `-g'' + (μ₊ - μ₋) g = 0` weakly (Fubini backwards).
* **`vrepMeas_iff_explicit`**: `ρ` is the ground-state density of a measure potential iff
  `ρ = g²` with `g ∈ H¹₀` continuous, normalised, positive on `(0, 1)`, and
  `g'(t) = c + ∫_{[0,t)} g d(μ₊ - μ₋)` a.e. for some finite measures `μ±` on `[0, 1]`, that is,
  `g'' = g (μ₊ - μ₋)`: `g''/g` is a finite signed measure (`∫ d|g''|/g < ∞`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

instance (μ ν : Measure ℝ) [IsMeas01 μ] [IsMeas01 ν] : IsMeas01 (μ + ν) where
  compl_zero := by
    rw [Measure.add_apply, IsMeas01.compl_zero (ρ := μ), IsMeas01.compl_zero (ρ := ν), add_zero]

instance (r : NNReal) (μ : Measure ℝ) [IsMeas01 μ] : IsMeas01 (r • μ) where
  compl_zero := by rw [Measure.smul_apply, IsMeas01.compl_zero (ρ := μ), smul_zero]

lemma Gρ_add (μ ν : Measure ℝ) [IsMeas01 μ] [IsMeas01 ν] {ψ : ℝ → ℝ} (hψc : Continuous ψ)
    (t : ℝ) : Gρ (μ + ν) ψ t = Gρ μ ψ t + Gρ ν ψ t := by
  rw [Gρ, Measure.restrict_add, integral_add_measure (integrable_of_meas01 μ hψc).integrableOn
    (integrable_of_meas01 ν hψc).integrableOn]
  rfl

lemma Gρ_smul (r : NNReal) (μ : Measure ℝ) (ψ : ℝ → ℝ) (t : ℝ) :
    Gρ (r • μ) ψ t = r * Gρ μ ψ t := by
  rw [Gρ, Measure.restrict_smul, integral_smul_nnreal_measure]
  rfl

/-- **Fubini backwards**: `g' = c + G₊ - G₋` a.e. gives the weak equation with `E = 0`. -/
theorem weak_of_deriv {μp μm : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] {g : ℝ → ℝ} (hg : H10 g)
    (hgc : Continuous g) {c : ℝ}
    (hd : deriv g =ᵐ[μ1] fun t => c + Gρ μp g t - Gρ μm g t) (φ : ℝ → ℝ) (hφ : H10 φ) :
    ∫ t, deriv g t * deriv φ t ∂μ1 + nuOf μp μm (mulP hg hφ) = 0 * ∫ t, g t * φ t ∂μ1 := by
  have i0 := integrable_deriv_mu1 hφ
  have i1 := integrable_dG μp hgc hφ
  have i2 := integrable_dG μm hgc hφ
  have hφ0 : ∫ t, deriv φ t ∂μ1 = 0 := by
    rw [integral_mu1, (hφ.1).integral_deriv_eq_sub, hφ.2.2.1, hφ.2.1, sub_zero]
  have e : ∫ t, deriv g t * deriv φ t ∂μ1 =
      c * ∫ t, deriv φ t ∂μ1 + ∫ t, deriv φ t * Gρ μp g t ∂μ1 -
        ∫ t, deriv φ t * Gρ μm g t ∂μ1 := by
    have ic : Integrable (fun t => c * deriv φ t) μ1 := i0.const_mul c
    have icp : Integrable (fun t => c * deriv φ t + deriv φ t * Gρ μp g t) μ1 := ic.add i1
    rw [integral_congr_ae (hd.mono fun t ht => by
      simp only [ht]
      exact (show (c + Gρ μp g t - Gρ μm g t) * deriv φ t = c * deriv φ t +
        deriv φ t * Gρ μp g t - deriv φ t * Gρ μm g t by ring)),
      integral_sub icp i2, integral_add ic i1, integral_const_mul]
  rw [e, hφ0, nuOf, sub_apply, intCLM_mulP, intCLM_mulP, integral_mul_eq_neg μp hgc hφ,
    integral_mul_eq_neg μm hgc hφ]
  ring

/-- **Measure-`v`-representability, explicitly**: `ρ` is the ground-state density of a measure
potential iff `ρ = g²`, `g ∈ H¹₀` continuous, normalised, positive on `(0, 1)`, with
`g'(t) = c + ∫_{x<t} g dμ₊ - ∫_{x<t} g dμ₋` a.e. for finite measures `μ±` on `[0, 1]`. -/
theorem vrepMeas_iff_explicit (ρ : Pot) : VRepMeas ρ ↔
    ∃ g : ℝ → ℝ, H10 g ∧ Continuous g ∧ ∫ t, g t ^ 2 ∂μ1 = 1 ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) ∧ (∀ t : Icc (0 : ℝ) 1, ρ t = g t ^ 2) ∧
      ∃ (μp μm : Measure ℝ) (_ : IsMeas01 μp) (_ : IsMeas01 μm) (c : ℝ),
        deriv g =ᵐ[μ1] fun t => c + Gρ μp g t - Gρ μm g t := by
  constructor
  · intro h
    obtain ⟨g, hg, hn, hpos, hρ, μp, μm, _, _, E, hE⟩ := (vrepMeas_iff ρ).1 h
    obtain ⟨gc, hgc, hgcc, hval⟩ : ∃ gc : ℝ → ℝ, H10 gc ∧ Continuous gc ∧
        ∀ t ∈ Icc (0 : ℝ) 1, gc t = g t :=
      ⟨_, H10.clamp_H10 hg, H10.continuous_clamp hg, fun t ht => H10.clamp_eq ht⟩
    have hder : deriv gc =ᵐ[μ1] deriv g := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have : gc =ᶠ[𝓝 t] g := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
        fun s hs => hval s (Ioo_subset_Icc_self hs)
      exact this.deriv_eq
    have hint : ∀ f : ℝ → ℝ → ℝ, ∫ t, f t (gc t) ∂μ1 = ∫ t, f t (g t) ∂μ1 := fun f =>
      setIntegral_congr_fun measurableSet_Ioo fun t ht => by
        simp only [hval t (Ioo_subset_Icc_self ht)]
    -- the weak equation for the continuous representative
    have hEc : ∀ φ (hφ : H10 φ), ∫ t, deriv gc t * deriv φ t ∂μ1 + nuOf μp μm (mulP hgc hφ) =
        E * ∫ t, gc t * φ t ∂μ1 := fun φ hφ => by
      have hm : mulP hgc hφ = mulP hg hφ := by ext t; rw [mulP_apply, mulP_apply, hval t t.2]
      have h1 : ∫ t, deriv gc t * deriv φ t ∂μ1 = ∫ t, deriv g t * deriv φ t ∂μ1 :=
        integral_congr_ae (hder.mono fun t ht => by simp only [ht])
      have h2 : ∫ t, gc t * φ t ∂μ1 = ∫ t, g t * φ t ∂μ1 :=
        setIntegral_congr_fun measurableSet_Ioo fun t ht => by
          simp only [hval t (Ioo_subset_Icc_self ht)]
      rw [hm, h1, h2]; exact hE φ hφ
    obtain ⟨c, hR⟩ := deriv_ae_eq_R hgc hgcc hEc
    refine ⟨gc, hgc, hgcc, by rw [hint fun _ y => y ^ 2]; exact hn,
      fun t ht => by rw [hval t (Ioo_subset_Icc_self ht)]; exact hpos t ht,
      fun t => by rw [hρ t, hval t t.2],
      μp + (max (-E) 0).toNNReal • μ1, μm + (max E 0).toNNReal • μ1, inferInstance, inferInstance,
      c, hR.mono fun t ht => ?_⟩
    rw [ht, Rψ]
    beta_reduce
    rw [Gρ_add _ _ hgcc, Gρ_add _ _ hgcc, Gρ_smul, Gρ_smul,
      Real.coe_toNNReal _ (le_max_right _ _), Real.coe_toNNReal _ (le_max_right _ _)]
    rcases le_total E 0 with hE0 | hE0
    · rw [max_eq_left (by linarith : 0 ≤ -E), max_eq_right hE0]; ring
    · rw [max_eq_right (by linarith : -E ≤ 0), max_eq_left hE0]; ring
  · rintro ⟨g, hg, hgc, hn, hpos, hρ, μp, μm, _, _, c, hd⟩
    exact (vrepMeas_iff ρ).2 ⟨g, hg, hn, hpos, hρ, μp, μm, inferInstance, inferInstance, 0,
      weak_of_deriv hg hgc hd⟩

end DFT.Continuum.Line
