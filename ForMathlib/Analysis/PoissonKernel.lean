/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral

/-!
# The Poisson kernel of the upper half-plane is an approximate identity

`P_η(x) = η / (π (x² + η²))` is the Poisson kernel of the upper half-plane (the Cauchy
distribution of width `η`). It is integrable with integral `1`, and for a bounded continuous `f`,
`∫ P_η(x - a) f(x) dx → f(a)` as `η → 0⁺`. This is the analytic content of the Stieltjes inversion
`-π⁻¹ Im (ω + iη - a)⁻¹ → δ(ω - a)`.

## Main results

* `poissonKernel`, `integrable_poissonKernel`, `integral_poissonKernel_smul`: integrability and the
  change of variables `x = a + η s`.
* `tendsto_integral_poissonKernel`: the Poisson kernel is an approximate identity.
-/

namespace ForMathlib

open MeasureTheory Filter Topology Real

/-- The Poisson kernel of the upper half-plane, `P_η(x) = η / (π (x² + η²))`. -/
noncomputable def poissonKernel (η x : ℝ) : ℝ := η / (π * (x ^ 2 + η ^ 2))

lemma poissonKernel_eq {η : ℝ} (hη : 0 < η) (x : ℝ) :
    poissonKernel η x = (π * η)⁻¹ * (1 + (η⁻¹ * x) ^ 2)⁻¹ := by
  rw [poissonKernel]
  field_simp
  ring

lemma poissonKernel_nonneg {η : ℝ} (hη : 0 < η) (x : ℝ) : 0 ≤ poissonKernel η x := by
  rw [poissonKernel]; positivity

lemma integrable_poissonKernel {η : ℝ} (hη : 0 < η) (a : ℝ) :
    Integrable fun x => poissonKernel η (x - a) := by
  simp_rw [poissonKernel_eq hη]
  exact ((integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hη.ne')).comp_sub_right a).const_mul
    _

/-- A bounded continuous function against the Poisson kernel is integrable. -/
lemma integrable_poissonKernel_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {η : ℝ} (hη : 0 < η) (a : ℝ) :
    Integrable fun x => poissonKernel η (x - a) • f x := by
  refine ((integrable_poissonKernel hη a).mul_const C).mono'
    ((Continuous.aestronglyMeasurable (by
      unfold poissonKernel; fun_prop (disch := intros; positivity))).smul
      hf.aestronglyMeasurable) ?_
  refine Eventually.of_forall fun x => ?_
  rw [norm_smul, Real.norm_of_nonneg (poissonKernel_nonneg hη _)]
  exact mul_le_mul_of_nonneg_left (hC x) (poissonKernel_nonneg hη _)

/-- The change of variables `x = a + η s`:
`∫ P_η(x - a) f(x) dx = ∫ π⁻¹ (1 + s²)⁻¹ f(a + η s) ds`. -/
lemma integral_poissonKernel_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {η : ℝ} (hη : 0 < η) (a : ℝ) :
    ∫ x, poissonKernel η (x - a) • f x = ∫ s, (π⁻¹ * (1 + s ^ 2)⁻¹) • f (a + η * s) := by
  have h1 := Measure.integral_comp_mul_left (fun y => poissonKernel η (a + y - a) • f (a + y)) η
  rw [integral_add_left_eq_self (fun x => poissonKernel η (x - a) • f x) a] at h1
  simp only [add_sub_cancel_left] at h1
  rw [abs_inv, abs_of_pos hη] at h1
  have h2 : ∫ x, poissonKernel η (x - a) • f x =
      η • ∫ s, poissonKernel η (η * s) • f (a + η * s) := by
    rw [h1, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
  rw [h2, ← integral_smul]
  congr 1
  funext s
  rw [smul_smul, poissonKernel_eq hη]
  congr 1
  field_simp

/-- **The Poisson kernel is an approximate identity**: for a bounded continuous `f`,
`∫ P_η(x - a) f(x) dx → f(a)` as `η → 0⁺`. -/
theorem tendsto_integral_poissonKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (a : ℝ) :
    Tendsto (fun η => ∫ x, poissonKernel η (x - a) • f x) (𝓝[>] 0) (𝓝 (f a)) := by
  have hlim : Tendsto (fun η => ∫ s, (π⁻¹ * (1 + s ^ 2)⁻¹) • f (a + η * s)) (𝓝[>] 0)
      (𝓝 (∫ s, (π⁻¹ * (1 + s ^ 2)⁻¹) • f a)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => π⁻¹ * (1 + s ^ 2)⁻¹ * C)
      (Eventually.of_forall fun η => ?_) (Eventually.of_forall fun η => ?_)
      ((integrable_inv_one_add_sq.const_mul π⁻¹).mul_const C) ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop (disch := intros; positivity))).smul
        (hf.comp (by fun_prop)).aestronglyMeasurable
    · refine Eventually.of_forall fun s => ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
    · refine Eventually.of_forall fun s => ?_
      refine Tendsto.const_smul ?_ _
      have : Tendsto (fun η : ℝ => a + η * s) (𝓝[>] 0) (𝓝 a) := by
        have h : Tendsto (fun η : ℝ => a + η * s) (𝓝 0) (𝓝 (a + 0 * s)) := by
          exact tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
        rw [zero_mul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact (hf.tendsto a).comp this
  rw [integral_smul_const, integral_const_mul, integral_univ_inv_one_add_sq,
    inv_mul_cancel₀ pi_ne_zero, one_smul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (integral_poissonKernel_smul f hη a).symm

end ForMathlib
