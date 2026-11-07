/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Picone

/-!
# The equality case of the Picone inequality

If `ψ'' = W ψ`, `ψ > 0` on `(0, 1)`, `ψ` vanishes at the walls with nonzero slopes, and
`∫ (φ'² + W φ²) = 0` for some `φ` in the form domain, then `φ` is a multiple of `ψ` on `(0, 1)`.

On `[a, b] ⊂ (0, 1)`, `∫_a^b (φ'² + W φ²) = F(b) - F(a) + ∫_a^b R` with `F = φ² ψ'/ψ` and
`R = (φ' ψ - φ ψ')² / ψ² ≥ 0`. Along `[a, 1 - a]` the left side minus the boundary terms tends to
`∫₀¹ (φ'² + W φ²) = 0`, so `∫_a^b R = 0` on every interior interval, `R = 0` on `(0, 1)`, and
`(φ/ψ)' = 0` there.

* `picone_interior_eq`: the exact identity on `[a, b] ⊂ (0, 1)`.
* `picone_tendsto`: the integral over `[a, 1 - a]` minus the boundary terms tends to the integral
  over `(0, 1)`.
* `picone_eq`: the equality case.
-/

namespace DFT

namespace Continuum

namespace Box

open MeasureTheory Set Filter Topology

/-- **Picone identity on an interior interval.** -/
lemma picone_interior_eq {W : ℝ → ℝ} (hW : Continuous W) {ψ ψ' : ℝ → ℝ}
    (hψd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ (ψ' t) t)
    (hψ'd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ' (W t * ψ t) t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t) {φ : ℝ → ℝ} (hφ : φ ∈ Dom) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ x in a..b, (deriv φ x * ψ x - φ x * ψ' x) ^ 2 / ψ x ^ 2 =
      (∫ x in a..b, (deriv φ x ^ 2 + W x * φ x ^ 2)) -
        (φ b ^ 2 * ψ' b / ψ b - φ a ^ 2 * ψ' a / ψ a) := by
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
  have hF'i : IntervalIntegrable F' volume a b := ((uIcc_of_le hab).symm ▸ hF'c).intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hF hF'i,
    ← intervalIntegral.integral_sub (f := fun x => deriv φ x ^ 2 + W x * φ x ^ 2) (g := F')
      (hG.intervalIntegrable _ _) hF'i]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hab] at hx
  have hψx := hpos x (hin x hx)
  simp only [F']
  field_simp
  ring

/-- The integral over `[a, 1 - a]` minus the boundary terms tends to the integral over `(0, 1)`. -/
lemma picone_tendsto {W : ℝ → ℝ} (hW : Continuous W) {ψ ψ' : ℝ → ℝ}
    (hψd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ (ψ' t) t)
    (hψ'd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ' (W t * ψ t) t)
    (h0 : ψ 0 = 0) (h1 : ψ 1 = 0)
    (hd0 : 0 < ψ' 0) (hd1 : ψ' 1 < 0) {φ : ℝ → ℝ} (hφ : φ ∈ Dom) :
    Tendsto (fun a => (∫ x in a..(1 - a), (deriv φ x ^ 2 + W x * φ x ^ 2)) -
      (φ (1 - a) ^ 2 * ψ' (1 - a) / ψ (1 - a) - φ a ^ 2 * ψ' a / ψ a)) (𝓝[>] 0)
      (𝓝 (∫ x, (deriv φ x ^ 2 + W x * φ x ^ 2) ∂μ1)) := by
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
  have h0P : P 0 = 0 := by simp [P]
  have hP1 : P 1 = ∫ x, (deriv φ x ^ 2 + W x * φ x ^ 2) ∂μ1 := by
    simp only [P]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [h0P, sub_zero, hP1] at hlim
  refine hlim.congr fun a => ?_
  rw [hint]

/-- **Equality case of the Picone inequality.** If `∫ (φ'² + W φ²) = 0`, then `φ = c ψ` on
`(0, 1)`. -/
theorem picone_eq {W : ℝ → ℝ} (hW : Continuous W) {ψ ψ' : ℝ → ℝ}
    (hψd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ (ψ' t) t)
    (hψ'd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt ψ' (W t * ψ t) t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t) (h0 : ψ 0 = 0) (h1 : ψ 1 = 0)
    (hd0 : 0 < ψ' 0) (hd1 : ψ' 1 < 0) {φ : ℝ → ℝ} (hφ : φ ∈ Dom)
    (heq : ∫ x, (deriv φ x ^ 2 + W x * φ x ^ 2) ∂μ1 = 0) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, φ x = c * ψ x := by
  have hφd := diff_of_mem hφ
  have hφc := cont_deriv_of_mem hφ
  set R : ℝ → ℝ := fun x => (deriv φ x * ψ x - φ x * ψ' x) ^ 2 / ψ x ^ 2
  have hI2 : ∀ x ∈ Ioo (0 : ℝ) 1, x ∈ Ioo (-1 : ℝ) 2 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hRc : ContinuousOn R (Ioo 0 1) := by
    have hψc : ContinuousOn ψ (Ioo 0 1) := fun x hx =>
      (hψd x (hI2 x hx)).continuousAt.continuousWithinAt
    have hψ'c : ContinuousOn ψ' (Ioo 0 1) := fun x hx =>
      (hψ'd x (hI2 x hx)).continuousAt.continuousWithinAt
    refine ContinuousOn.div ?_ (hψc.pow 2) fun x hx => pow_ne_zero 2 (hpos x hx).ne'
    exact ((hφc.continuousOn.mul hψc).sub (hφ.1.continuous.continuousOn.mul hψ'c)).pow 2
  have hR0 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ R x := fun x _ => by positivity
  have hT := picone_tendsto hW hψd hψ'd h0 h1 hd0 hd1 hφ
  rw [heq] at hT
  -- `∫_a^b R = 0` on every interior interval
  have hzero : ∀ a b, 0 < a → a ≤ b → b < 1 → ∫ x in a..b, R x = 0 := by
    intro a b ha hab hb
    refine le_antisymm ?_ (intervalIntegral.integral_nonneg hab fun x hx =>
      hR0 x ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min a (1 - b) from lt_min ha (by linarith))]
      with e he
    have he1 : e < a := lt_of_lt_of_le he.2 (min_le_left _ _)
    have he2 : e < 1 - b := lt_of_lt_of_le he.2 (min_le_right _ _)
    have hle : e ≤ 1 - e := by linarith
    have hlt : 1 - e < 1 := by linarith [he.1]
    rw [← picone_interior_eq (a := e) (b := 1 - e) hW hψd hψ'd hpos hφ he.1 hle hlt]
    refine intervalIntegral.integral_mono_interval he1.le hab (by linarith) ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
      exact hR0 x ⟨lt_trans he.1 hx.1, by linarith [hx.2, he.1]⟩
    · refine ContinuousOn.intervalIntegrable (hRc.mono ?_)
      rw [uIcc_of_le (by linarith)]
      intro x hx; exact ⟨lt_of_lt_of_le he.1 hx.1, by linarith [hx.2, he.1]⟩
  -- so `R = 0` on `(0, 1)`
  have hRz : ∀ x ∈ Ioo (0 : ℝ) 1, R x = 0 := by
    intro x hx
    by_contra hne
    have hRx : 0 < R x := lt_of_le_of_ne (hR0 x hx) (Ne.symm hne)
    have hev : ∀ᶠ y in 𝓝 x, 0 < R y :=
      (hRc.continuousAt (Ioo_mem_nhds hx.1 hx.2)).eventually (lt_mem_nhds hRx)
    have hev2 := hev.and (Ioo_mem_nhds hx.1 hx.2)
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev2
    have hin : ∀ y ∈ Icc (x - η / 2) (x + η / 2), 0 < R y ∧ y ∈ Ioo (0 : ℝ) 1 := fun y hy =>
      hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])
    have ha : 0 < x - η / 2 := (hin _ ⟨le_rfl, by linarith⟩).2.1
    have hb : x + η / 2 < 1 := (hin _ ⟨by linarith, le_rfl⟩).2.2
    have hpos' := intervalIntegral.intervalIntegral_pos_of_pos_on
      (f := R) (a := x - η / 2) (b := x + η / 2)
      (ContinuousOn.intervalIntegrable (hRc.mono (by
        rw [uIcc_of_le (by linarith)]; exact fun y hy => (hin y hy).2)))
      (fun y hy => (hin y (Ioo_subset_Icc_self hy)).1) (by linarith)
    rw [hzero _ _ ha (by linarith) hb] at hpos'
    exact lt_irrefl _ hpos'
  -- hence `(φ/ψ)' = 0` on `(0, 1)`
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y => φ y / ψ y) ((deriv φ x * ψ x - φ x * ψ' x) / ψ x ^ 2) x :=
    fun x hx => ((hφd x).hasDerivAt.div (hψd x (hI2 x hx)) (hpos x hx).ne')
  have hnum : ∀ x ∈ Ioo (0 : ℝ) 1, deriv φ x * ψ x - φ x * ψ' x = 0 := by
    intro x hx
    have h := hRz x hx
    have hψ2 : ψ x ^ 2 ≠ 0 := pow_ne_zero 2 (hpos x hx).ne'
    simp only [R, div_eq_zero_iff, hψ2, or_false] at h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨φ (1 / 2) / ψ (1 / 2), fun x hx => ?_⟩
  have := isOpen_Ioo.is_const_of_deriv_eq_zero (𝕜 := ℝ) (f := fun y => φ y / ψ y)
    isPreconnected_Ioo (fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => by rw [(hderiv y hy).deriv, hnum y hy, zero_div]; rfl) hx hhalf
  change φ x / ψ x = φ (1 / 2) / ψ (1 / 2) at this
  rw [← this]
  field_simp [(hpos x hx).ne']

end Box

end Continuum

end DFT
