/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Spectral.Green

/-!
# The Green kernel

The Green operator of `Green` written as an integral operator on `(0, 1)`:

`Gk f (x) = ∫ K(x, y) f(y) dy`,  `K(x, y) = u(min x y) w(max x y) / ω`.

The kernel is continuous and symmetric on the closed square, so `Gk` makes sense for every
integrable `f`, is bounded by a constant times `∫ |f|`, and the family of functions `Gk f` with
`∫ |f| ≤ 1` is uniformly equicontinuous on `[0, 1]`: the inputs of the Arzelà–Ascoli argument for
compactness.

* `Kg`, `continuousOn_Kg`, `Kg_symm`, `exists_Kg_bound`: the kernel.
* `Gk`: the integral operator; `Gk_eq_Gf`: for continuous `f` it is the Green operator of `Green`.
* `abs_Gk_le`, `Gk_equicont`: the uniform bound and the equicontinuity estimate.
* `continuousOn_Gk`: `Gk f` is continuous on `[0, 1]` for integrable `f`.
-/

namespace DFT.Continuum.Spectral

open MeasureTheory Set Filter Topology Box

variable {W : ℝ → ℝ} (hWc : Continuous W)

/-- The Green kernel `K(x, y) = u(min x y) w(max x y) / ω`. -/
noncomputable def Kg (x y : ℝ) : ℝ := uS hWc (min x y) * wS hWc (max x y) / wS hWc 0

lemma Kg_symm (x y : ℝ) : Kg hWc x y = Kg hWc y x := by
  simp only [Kg, min_comm, max_comm]

lemma Icc_sub_Ioo' : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun t ht =>
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma continuousOn_Kg : ContinuousOn (fun p : ℝ × ℝ => Kg hWc p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hmin : MapsTo (fun p : ℝ × ℝ => min p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) (Ioo (-1 : ℝ) 2) :=
    fun p hp => Icc_sub_Ioo' ⟨le_min hp.1.1 hp.2.1, (min_le_left _ _).trans hp.1.2⟩
  have hmax : MapsTo (fun p : ℝ × ℝ => max p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) (Ioo (-1 : ℝ) 2) :=
    fun p hp => Icc_sub_Ioo' ⟨hp.1.1.trans (le_max_left _ _), max_le hp.1.2 hp.2.2⟩
  exact (((continuousOn_uS hWc).comp (continuous_fst.min continuous_snd).continuousOn hmin).mul
    ((continuousOn_wS hWc).comp (continuous_fst.max continuous_snd).continuousOn hmax)).div_const _

/-- The kernel is bounded on the closed square. -/
lemma exists_Kg_bound :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |Kg hWc x y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuousOn_Kg hWc)
  exact ⟨max C 0, le_max_right _ _, fun x hx y hy =>
    ((hC (x, y) ⟨hx, hy⟩).trans (le_max_left _ _))⟩

/-- The kernel is uniformly continuous in `x`, uniformly in `y`. -/
lemma Kg_unif (ε : ℝ) (hε : 0 < ε) : ∃ δ, 0 < δ ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1,
    |x - x'| < δ → ∀ y ∈ Icc (0 : ℝ) 1, |Kg hWc x y - Kg hWc x' y| < ε := by
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (continuousOn_Kg hWc)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, h⟩ := huc ε hε
  refine ⟨δ, hδ, fun x hx x' hx' hxx y hy => ?_⟩
  have := h (x, y) ⟨hx, hy⟩ (x', y) ⟨hx', hy⟩ (by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero]
    exact max_lt hxx hδ)
  rwa [Real.dist_eq] at this

/-! ### The integral operator -/

/-- The Green operator as an integral operator over `(0, 1)`. -/
noncomputable def Gk (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, Kg hWc x y * f y ∂μ1

lemma ae_mem_Icc : ∀ᵐ y ∂μ1, y ∈ Icc (0 : ℝ) 1 :=
  (ae_restrict_mem measurableSet_Ioo).mono fun _ hy => Ioo_subset_Icc_self hy

lemma aestronglyMeasurable_Kg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    AEStronglyMeasurable (fun y => Kg hWc x y) μ1 := by
  have hc : ContinuousOn (fun y => Kg hWc x y) (Icc 0 1) :=
    (continuousOn_Kg hWc).comp (continuousOn_const.prodMk continuousOn_id)
      fun y hy => ⟨hx, hy⟩
  exact (hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo

lemma integrable_Kg_mul {f : ℝ → ℝ} (hf : Integrable f μ1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun y => Kg hWc x y * f y) μ1 := by
  obtain ⟨C, -, hC⟩ := exists_Kg_bound hWc
  exact hf.bdd_mul (aestronglyMeasurable_Kg hWc hx)
    ((ae_mem_Icc).mono fun y hy => by rw [Real.norm_eq_abs]; exact hC x hx y hy)

/-- **The uniform bound**: `|Gk f x| ≤ C ∫ |f|`. -/
lemma exists_Gk_bound : ∃ C, 0 ≤ C ∧ ∀ f : ℝ → ℝ, Integrable f μ1 → ∀ x ∈ Icc (0 : ℝ) 1,
    |Gk hWc f x| ≤ C * ∫ y, |f y| ∂μ1 := by
  obtain ⟨C, hC0, hC⟩ := exists_Kg_bound hWc
  refine ⟨C, hC0, fun f hf x hx => ?_⟩
  calc |Gk hWc f x| ≤ ∫ y, |Kg hWc x y * f y| ∂μ1 := abs_integral_le_integral_abs
    _ ≤ ∫ y, C * |f y| ∂μ1 := by
        refine integral_mono_ae (integrable_Kg_mul hWc hf hx).abs (hf.abs.const_mul C) ?_
        filter_upwards [ae_mem_Icc] with y hy
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hC x hx y hy) (abs_nonneg _)
    _ = C * ∫ y, |f y| ∂μ1 := integral_const_mul _ _

/-- **Equicontinuity**: `|Gk f x - Gk f x'| ≤ ε ∫ |f|` when `|x - x'| < δ`, uniformly in `f`. -/
lemma Gk_equicont (ε : ℝ) (hε : 0 < ε) : ∃ δ, 0 < δ ∧ ∀ f : ℝ → ℝ, Integrable f μ1 →
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, |x - x'| < δ →
      |Gk hWc f x - Gk hWc f x'| ≤ ε * ∫ y, |f y| ∂μ1 := by
  obtain ⟨δ, hδ, h⟩ := Kg_unif hWc ε hε
  refine ⟨δ, hδ, fun f hf x hx x' hx' hxx => ?_⟩
  have hsub : Gk hWc f x - Gk hWc f x' = ∫ y, (Kg hWc x y - Kg hWc x' y) * f y ∂μ1 := by
    rw [Gk, Gk, ← integral_sub (integrable_Kg_mul hWc hf hx) (integrable_Kg_mul hWc hf hx')]
    congr 1; funext y; ring
  rw [hsub]
  calc |∫ y, (Kg hWc x y - Kg hWc x' y) * f y ∂μ1|
      ≤ ∫ y, |(Kg hWc x y - Kg hWc x' y) * f y| ∂μ1 := abs_integral_le_integral_abs
    _ ≤ ∫ y, ε * |f y| ∂μ1 := by
        have hi : Integrable (fun y => (Kg hWc x y - Kg hWc x' y) * f y) μ1 := by
          have := (integrable_Kg_mul hWc hf hx).sub (integrable_Kg_mul hWc hf hx')
          refine this.congr (ae_of_all _ fun y => ?_)
          simp only [Pi.sub_apply]; ring
        refine integral_mono_ae hi.abs (hf.abs.const_mul ε) ?_
        filter_upwards [ae_mem_Icc] with y hy
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h x hx x' hx' hxx y hy).le (abs_nonneg _)
    _ = ε * ∫ y, |f y| ∂μ1 := integral_const_mul _ _

/-- `Gk f` is continuous on `[0, 1]` for integrable `f`. -/
lemma continuousOn_Gk {f : ℝ → ℝ} (hf : Integrable f μ1) : ContinuousOn (Gk hWc f) (Icc 0 1) := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set I := ∫ y, |f y| ∂μ1
  have hI : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  obtain ⟨δ, hδ, h⟩ := Gk_equicont hWc (ε / (I + 1)) (by positivity)
  refine ⟨δ, hδ, fun x' hx' hd => ?_⟩
  rw [Real.dist_eq] at hd ⊢
  have := h f hf x' hx' x hx hd
  calc |Gk hWc f x' - Gk hWc f x| ≤ ε / (I + 1) * I := this
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-! ### Comparison with the Green operator of `Green` -/

/-- For continuous `f`, the integral operator is the Green operator of `Green`. -/
lemma Gk_eq_Gf {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Gk hWc f x = Gf hWc f x := by
  have hcK : ContinuousOn (fun y => Kg hWc x y * f y) (Icc 0 1) :=
    ((continuousOn_Kg hWc).comp (continuousOn_const.prodMk continuousOn_id)
      fun y hy => ⟨hx, hy⟩).mul hf.continuousOn
  have hsub1 : uIcc 0 x ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
  have hsub2 : uIcc x 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.2]; exact Icc_subset_Icc hx.1 le_rfl
  have h01 : Gk hWc f x = ∫ y in (0 : ℝ)..1, Kg hWc x y * f y := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]; rfl
  rw [h01, ← intervalIntegral.integral_add_adjacent_intervals
    ((hcK.mono hsub1).intervalIntegrable) ((hcK.mono hsub2).intervalIntegrable)]
  have e1 : ∫ y in (0 : ℝ)..x, Kg hWc x y * f y =
      wS hWc x / wS hWc 0 * ∫ y in (0 : ℝ)..x, uS hWc y * f y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hx.1] at hy
    simp only [Kg, min_eq_right hy.2, max_eq_left hy.2]
    ring
  have e2 : ∫ y in x..(1 : ℝ), Kg hWc x y * f y =
      uS hWc x / wS hWc 0 * ∫ y in x..(1 : ℝ), wS hWc y * f y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hx.2] at hy
    simp only [Kg, min_eq_left hy.1, max_eq_right hy.1]
    ring
  rw [e1, e2, Gf]
  ring

end DFT.Continuum.Spectral
