/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box

/-!
# The Picone inequality in the box

Let `ψ'' = W ψ` with `ψ > 0` on `(0, 1)`, `ψ(0) = ψ(1) = 0`, `ψ'(0) > 0` and `ψ'(1) < 0`. Then for
every `φ` in the form domain, `∫₀¹ (φ'² + W φ²) ≥ 0`.

On `[a, b] ⊂ (0, 1)`, with `F = φ² ψ'/ψ`, one has `φ'² + W φ² - F' = (φ' - φ ψ'/ψ)² ≥ 0`, so
`∫_a^b (φ'² + W φ²) ≥ F(b) - F(a)`. Near the walls `|φ| ≤ C·dist`, `ψ ≥ c·dist` and `|ψ'| ≤ M`, so
the boundary terms vanish as `a → 0`, `b = 1 - a → 1`.

* `picone_interior`: the inequality on `[a, b] ⊂ (0, 1)`.
* `tendsto_zero_of_abs_le_mul`: a function bounded by `K a` tends to `0` as `a → 0⁺`.
* `picone`: the inequality on `(0, 1)`.
-/

namespace DFT

namespace Continuum

namespace Box

open MeasureTheory Set Filter Topology

/-- A function bounded by `K a` near `0⁺` tends to `0` there. -/
lemma tendsto_zero_of_abs_le_mul {f : ℝ → ℝ} {K δ : ℝ} (hδ : 0 < δ)
    (h : ∀ a ∈ Ioo 0 δ, |f a| ≤ K * a) : Tendsto f (𝓝[>] 0) (𝓝 0) := by
  have hK : Tendsto (fun a : ℝ => K * a) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => K * a) (𝓝 0) (𝓝 (K * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [Ioo_mem_nhdsGT hδ] with a ha
  simpa [Real.norm_eq_abs] using h a ha

/-- **Picone inequality on an interior interval.** -/
lemma picone_interior {W : ℝ → ℝ} (hW : Continuous W) {ψ ψ' : ℝ → ℝ}
    (hψd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ (ψ' t) t)
    (hψ'd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ' (W t * ψ t) t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t) {φ : ℝ → ℝ} (hφ : φ ∈ Dom) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    φ b ^ 2 * ψ' b / ψ b - φ a ^ 2 * ψ' a / ψ a ≤
      ∫ x in a..b, (deriv φ x ^ 2 + W x * φ x ^ 2) := by
  have hφd := diff_of_mem hφ
  have hφc := cont_deriv_of_mem hφ
  have hin : ∀ x ∈ Icc a b, x ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hin2 : ∀ x ∈ Icc a b, x ∈ Ioo (-1 : ℝ) 2 := fun x hx =>
    ⟨by linarith [(hin x hx).1], by linarith [(hin x hx).2]⟩
  set F' : ℝ → ℝ := fun x => ((2 * φ x * deriv φ x) * ψ' x + φ x ^ 2 * (W x * ψ x)) / ψ x -
    φ x ^ 2 * ψ' x * ψ' x / ψ x ^ 2
  have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun y => φ y ^ 2 * ψ' y / ψ y) (F' x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hψx : ψ x ≠ 0 := (hpos x (hin x hx)).ne'
    have h1 := (((hφd x).hasDerivAt.pow 2).mul (hψ'd x (hin2 x hx))).div (hψd x (hin2 x hx)) hψx
    convert h1 using 1
    simp only [F', Pi.pow_apply, Pi.mul_apply]
    field_simp
    ring
  have hψc : ContinuousOn ψ (Icc a b) := fun x hx =>
    (hψd x (hin2 x hx)).continuousAt.continuousWithinAt
  have hψ'c : ContinuousOn ψ' (Icc a b) := fun x hx =>
    (hψ'd x (hin2 x hx)).continuousAt.continuousWithinAt
  have hψne : ∀ x ∈ Icc a b, ψ x ≠ 0 := fun x hx => (hpos x (hin x hx)).ne'
  have hF'c : ContinuousOn F' (Icc a b) := by
    have hφcon := hφ.1.continuous
    refine ContinuousOn.sub (ContinuousOn.div ?_ hψc hψne) (ContinuousOn.div ?_ ?_ ?_)
    · exact ((continuous_const.mul hφcon).mul hφc).continuousOn.mul hψ'c |>.add
        ((hφcon.pow 2).continuousOn.mul (hW.continuousOn.mul hψc))
    · exact ((hφcon.pow 2).continuousOn.mul hψ'c).mul hψ'c
    · exact hψc.pow 2
    · intro x hx; exact pow_ne_zero 2 (hψne x hx)
  have hG : Continuous fun x => deriv φ x ^ 2 + W x * φ x ^ 2 :=
    (hφc.pow 2).add (hW.mul (hφ.1.continuous.pow 2))
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((uIcc_of_le hab).symm ▸ hF'c).intervalIntegrable]
  refine intervalIntegral.integral_mono_on hab
    ((uIcc_of_le hab).symm ▸ hF'c).intervalIntegrable (hG.intervalIntegrable _ _) ?_
  intro x hx
  have hψx := hpos x (hin x hx)
  have key : deriv φ x ^ 2 + W x * φ x ^ 2 - F' x =
      (deriv φ x * ψ x - φ x * ψ' x) ^ 2 / ψ x ^ 2 := by
    simp only [F']
    field_simp
    ring
  have : 0 ≤ (deriv φ x * ψ x - φ x * ψ' x) ^ 2 / ψ x ^ 2 := by positivity
  linarith

/-- **Picone inequality in the box.** If `ψ'' = W ψ`, `ψ > 0` on `(0, 1)`, `ψ` vanishes at the
walls with nonzero slopes, then `∫ (φ'² + W φ²) ≥ 0` for every `φ` in the form domain. -/
theorem picone {W : ℝ → ℝ} (hW : Continuous W) {ψ ψ' : ℝ → ℝ}
    (hψd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ (ψ' t) t)
    (hψ'd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ' (W t * ψ t) t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t) (h0 : ψ 0 = 0) (h1 : ψ 1 = 0)
    (hd0 : 0 < ψ' 0) (hd1 : ψ' 1 < 0) {φ : ℝ → ℝ} (hφ : φ ∈ Dom) :
    0 ≤ ∫ x, (deriv φ x ^ 2 + W x * φ x ^ 2) ∂μ1 := by
  have hφd := diff_of_mem hφ
  have hφc := cont_deriv_of_mem hφ
  have hI : ∀ x ∈ Icc (0 : ℝ) 1, x ∈ Ioo (-1 : ℝ) 2 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hψc : ContinuousOn ψ (Icc 0 1) := fun x hx =>
    (hψd x (hI x hx)).continuousAt.continuousWithinAt
  have hψ'c : ContinuousOn ψ' (Icc 0 1) := fun x hx =>
    (hψ'd x (hI x hx)).continuousAt.continuousWithinAt
  -- bounds on `[0, 1]`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφc.continuousOn (s := Icc 0 1))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ'c
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  -- `|φ x - φ y| ≤ C |x - y|` on `[0, 1]`
  have hφlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x ≤ y → |φ y - φ x| ≤ C * (y - x) := by
    intro x hx y hy hxy
    have hup := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
      hφ.1.continuous.continuousOn hφd.differentiableOn
      (fun z hz => le_trans (le_abs_self _)
        (by simpa [Real.norm_eq_abs] using hC z (interior_subset hz))) x hx y hy hxy
    have hlo := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
      hφ.1.continuous.continuousOn hφd.differentiableOn
      (fun z hz => neg_le_of_abs_le
        (by simpa [Real.norm_eq_abs] using hC z (interior_subset hz))) x hx y hy hxy
    rw [abs_le]; constructor <;> linarith
  -- `ψ'` stays away from zero near the walls
  obtain ⟨δ0, hδ0, hδ0'⟩ : ∃ δ > 0, ∀ x, |x - 0| < δ → ψ' 0 / 2 < ψ' x := by
    have hc := (hψ'd 0 (hI 0 ⟨le_rfl, zero_le_one⟩)).continuousAt
    have := hc.eventually (lt_mem_nhds (show ψ' 0 / 2 < ψ' 0 by linarith))
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp this
    exact ⟨δ, hδ, fun x hx => h (by simpa [Real.dist_eq] using hx)⟩
  obtain ⟨δ1, hδ1, hδ1'⟩ : ∃ δ > 0, ∀ x, |x - 1| < δ → ψ' x < ψ' 1 / 2 := by
    have hc := (hψ'd 1 (hI 1 ⟨zero_le_one, le_rfl⟩)).continuousAt
    have := hc.eventually (gt_mem_nhds (show ψ' 1 < ψ' 1 / 2 by linarith))
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp this
    exact ⟨δ, hδ, fun x hx => h (by simpa [Real.dist_eq] using hx)⟩
  set δ := min (min δ0 δ1) (1 / 2)
  have hδ : 0 < δ := lt_min (lt_min hδ0 hδ1) (by norm_num)
  have hδ0le : δ ≤ δ0 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1le : δ ≤ δ1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδh : δ ≤ 1 / 2 := min_le_right _ _
  set c0 := ψ' 0 / 2
  set c1 := -(ψ' 1 / 2)
  have hc0 : 0 < c0 := by simp only [c0]; linarith
  have hc1 : 0 < c1 := by simp only [c1]; linarith
  -- lower bounds for `ψ` near the walls
  have hψlow0 : ∀ a ∈ Ioo 0 δ, c0 * a ≤ ψ a := by
    intro a ha
    have hD : Icc (0 : ℝ) a ⊆ Icc 0 1 := Icc_subset_Icc le_rfl (by linarith [ha.2])
    have := (convex_Icc (0 : ℝ) a).mul_sub_le_image_sub_of_le_deriv (hψc.mono hD)
      (fun z hz => by
        rw [interior_Icc] at hz
        exact (hψd z (hI z (hD (Ioo_subset_Icc_self hz)))).differentiableAt.differentiableWithinAt)
      (fun z hz => by
        rw [interior_Icc] at hz
        rw [(hψd z (hI z (hD (Ioo_subset_Icc_self hz)))).deriv]
        exact (hδ0' z (by rw [sub_zero, abs_of_pos hz.1]; linarith [hz.2, ha.2])).le)
      0 ⟨le_rfl, ha.1.le⟩ a ⟨ha.1.le, le_rfl⟩ ha.1.le
    rw [h0] at this; linarith
  have hψlow1 : ∀ a ∈ Ioo 0 δ, c1 * a ≤ ψ (1 - a) := by
    intro a ha
    have hD : Icc (1 - a) 1 ⊆ Icc 0 1 := Icc_subset_Icc (by linarith [ha.2]) le_rfl
    have := (convex_Icc (1 - a) 1).image_sub_le_mul_sub_of_deriv_le (hψc.mono hD)
      (fun z hz => by
        rw [interior_Icc] at hz
        exact (hψd z (hI z (hD (Ioo_subset_Icc_self hz)))).differentiableAt.differentiableWithinAt)
      (C := -c1) (fun z hz => by
        rw [interior_Icc] at hz
        rw [(hψd z (hI z (hD (Ioo_subset_Icc_self hz)))).deriv]
        have := hδ1' z (by rw [abs_sub_lt_iff]; constructor <;> linarith [hz.1, hz.2, ha.2])
        simp only [c1]; linarith)
      (1 - a) ⟨le_rfl, by linarith [ha.1]⟩ 1 ⟨by linarith [ha.1], le_rfl⟩ (by linarith [ha.1])
    rw [h1] at this; linarith
  -- the boundary terms vanish
  have hb0 : Tendsto (fun a => φ a ^ 2 * ψ' a / ψ a) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_of_abs_le_mul (K := C ^ 2 * M / c0) hδ fun a ha => ?_
    have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, by linarith [ha.2]⟩
    have hψa : 0 < c0 * a := mul_pos hc0 ha.1
    have hψpos : 0 < ψ a := lt_of_lt_of_le hψa (hψlow0 a ha)
    have hφa : |φ a| ≤ C * a := by
      have := hφlip 0 ⟨le_rfl, zero_le_one⟩ a haI ha.1.le
      rwa [hφ.2.1, sub_zero, sub_zero] at this
    have hMa : |ψ' a| ≤ M := by simpa [Real.norm_eq_abs] using hM a haI
    rw [abs_div, abs_mul, abs_of_pos hψpos, abs_pow]
    calc |φ a| ^ 2 * |ψ' a| / ψ a ≤ (C * a) ^ 2 * M / (c0 * a) := by
          apply div_le_div₀ (by positivity) _ hψa (hψlow0 a ha)
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hφa 2) hMa (abs_nonneg _)
            (by positivity)
      _ = C ^ 2 * M / c0 * a := by field_simp
  have hb1 : Tendsto (fun a => φ (1 - a) ^ 2 * ψ' (1 - a) / ψ (1 - a)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_of_abs_le_mul (K := C ^ 2 * M / c1) hδ fun a ha => ?_
    have haI : 1 - a ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
    have hψa : 0 < c1 * a := mul_pos hc1 ha.1
    have hψpos : 0 < ψ (1 - a) := lt_of_lt_of_le hψa (hψlow1 a ha)
    have hφa : |φ (1 - a)| ≤ C * a := by
      have := hφlip (1 - a) haI 1 ⟨zero_le_one, le_rfl⟩ (by linarith [ha.1])
      rw [hφ.2.2, zero_sub, abs_neg] at this
      linarith
    have hMa : |ψ' (1 - a)| ≤ M := by simpa [Real.norm_eq_abs] using hM (1 - a) haI
    rw [abs_div, abs_mul, abs_of_pos hψpos, abs_pow]
    calc |φ (1 - a)| ^ 2 * |ψ' (1 - a)| / ψ (1 - a) ≤ (C * a) ^ 2 * M / (c1 * a) := by
          apply div_le_div₀ (by positivity) _ hψa (hψlow1 a ha)
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hφa 2) hMa (abs_nonneg _)
            (by positivity)
      _ = C ^ 2 * M / c1 * a := by field_simp
  -- the integrals over `[a, 1 - a]` converge
  have hG : Continuous fun x => deriv φ x ^ 2 + W x * φ x ^ 2 :=
    (hφc.pow 2).add (hW.mul (hφ.1.continuous.pow 2))
  set P : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u, (deriv φ x ^ 2 + W x * φ x ^ 2)
  have hP : Continuous P := continuous_iff_continuousAt.2 fun u =>
    (hG.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hint : ∀ a, ∫ x in a..(1 - a), (deriv φ x ^ 2 + W x * φ x ^ 2) = P (1 - a) - P a :=
    fun a => (intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)).symm
  have hPl : Tendsto (fun a => P (1 - a) - P a) (𝓝[>] 0) (𝓝 (P 1 - P 0)) := by
    have : Continuous fun a => P (1 - a) - P a :=
      (hP.comp (continuous_const.sub continuous_id)).sub hP
    have h := this.tendsto 0
    simp only [sub_zero] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  have hlim := (hPl.sub (hb1.sub hb0))
  simp only [sub_zero] at hlim
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 ≤ (P (1 - a) - P a) -
      (φ (1 - a) ^ 2 * ψ' (1 - a) / ψ (1 - a) - φ a ^ 2 * ψ' a / ψ a) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with a ha
    rw [← hint]
    have := picone_interior (a := a) (b := 1 - a) hW hψd hψ'd hpos hφ ha.1
      (by linarith [ha.2, hδh])
      (by linarith [ha.1])
    linarith
  have h0P : P 0 = 0 := by simp [P]
  have hfin := ge_of_tendsto hlim hev
  rw [h0P, sub_zero] at hfin
  have hP1 : P 1 = ∫ x, (deriv φ x ^ 2 + W x * φ x ^ 2) ∂μ1 := by
    simp only [P]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [← hP1]
  exact hfin

end Box

end Continuum

end DFT
