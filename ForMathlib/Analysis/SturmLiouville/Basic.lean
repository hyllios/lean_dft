/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Dirichlet problem on `[0, 1]`: basic definitions

Shared setting for the second-order linear ODE `y'' = W y` on `[0, 1]` with Dirichlet conditions
(Sturm–Liouville theory in `ForMathlib/Analysis/SturmLiouville/`).

* `vol01`: Lebesgue measure on `(0, 1)`.
* `Dom`: `C²` functions on `ℝ` vanishing at `0` and `1`.
* `C01`, `iccExt`: continuous functions on `[0, 1]` and their constant extension to `ℝ`
  (`Set.IccExtend` for a `C01`); `iccExt_add`, `iccExt_smul`.
* `eq_zero_of_integral`: the fundamental lemma of the calculus of variations on `(0, 1)`.
* `deriv_eq_zero_of_accPt`: the derivative vanishes at an accumulation point of zeros.
* `field`, `lipschitz_field`: the vector field `(y, y') ↦ (y', W y)` and its Lipschitz bound.
-/

namespace SturmLiouville

open MeasureTheory Set Filter Topology

/-- Lebesgue measure on `(0, 1)`. -/
noncomputable abbrev vol01 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

lemma integral_vol01 {f : ℝ → ℝ} : ∫ t, f t ∂vol01 = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- The form domain: `C²` functions vanishing at the walls. -/
def Dom : Submodule ℝ (ℝ → ℝ) where
  carrier := {ψ | ContDiff ℝ 2 ψ ∧ ψ 0 = 0 ∧ ψ 1 = 0}
  add_mem' ha hb := ⟨ha.1.add hb.1, by simp [ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨contDiff_const, rfl, rfl⟩
  smul_mem' r _ ha := ⟨ha.1.const_smul r, by simp [ha.2.1], by simp [ha.2.2]⟩

lemma mem_Dom {ψ : ℝ → ℝ} : ψ ∈ Dom ↔ ContDiff ℝ 2 ψ ∧ ψ 0 = 0 ∧ ψ 1 = 0 := Iff.rfl

/-- Continuous real functions on `[0, 1]` (coefficients of the ODE). -/
abbrev C01 := C(Icc (0 : ℝ) 1, ℝ)

/-- A function in `C01` extended to `ℝ`, constant outside `[0, 1]`. -/
noncomputable def iccExt (w : C01) (x : ℝ) : ℝ := w (projIcc 0 1 zero_le_one x)

lemma continuous_iccExt (w : C01) : Continuous (iccExt w) := w.continuous.comp continuous_projIcc

lemma iccExt_add (f g : C01) (x : ℝ) : iccExt (f + g) x = iccExt f x + iccExt g x := rfl

lemma iccExt_smul (c : ℝ) (f : C01) (x : ℝ) : iccExt (c • f) x = c * iccExt f x := rfl

lemma integrable_of_continuous {F : ℝ → ℝ} (hF : Continuous F) : Integrable F vol01 :=
  (hF.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self

lemma two_ge_one : (1 : WithTop ℕ∞) ≤ 2 := by norm_cast

lemma diff_of_mem {ψ : ℝ → ℝ} (h : ψ ∈ Dom) : Differentiable ℝ ψ := h.1.differentiable (by norm_num)

lemma cont_deriv_of_mem {ψ : ℝ → ℝ} (h : ψ ∈ Dom) : Continuous (deriv ψ) :=
  h.1.continuous_deriv two_ge_one

/-- **Fundamental lemma** on `(0, 1)`, for continuous functions and test functions in `Dom`. -/
lemma eq_zero_of_integral {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ φ ∈ Dom, ∫ x, g x * φ x ∂vol01 = 0) : ∀ x ∈ Ioo (0 : ℝ) 1, g x = 0 := by
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Ioo (0 : ℝ) 1)
    (μ := volume) (f := g) isOpen_Ioo (hg.locallyIntegrable.locallyIntegrableOn _)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Ioo (0 : ℝ) 1) => ?_)
  · have h' : g =ᵐ[vol01] 0 := (ae_restrict_iff' measurableSet_Ioo).2 hae
    exact Measure.eqOn_open_of_ae_eq h' isOpen_Ioo hg.continuousOn continuousOn_const
  · have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h0 => (lt_irrefl _ (hsub h0).1)
    have h1 : φ 1 = 0 := image_eq_zero_of_notMem_tsupport fun h1 => (lt_irrefl _ (hsub h1).2)
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have hφD : φ ∈ Dom := ⟨hφ.of_le h2, h0, h1⟩
    have := h φ hφD
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (0 : ℝ) 1)]
    · simpa [smul_eq_mul, mul_comm] using this
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hsub h'), zero_smul]

/-- If `f` is differentiable at an accumulation point `x₀` of its zeros, then `f'(x₀) = 0`. -/
lemma deriv_eq_zero_of_accPt {f : ℝ → ℝ} {f' x0 : ℝ} (hf : HasDerivAt f f' x0)
    (hacc : AccPt x0 (𝓟 {x | f x = 0})) (h0 : f x0 = 0) : f' = 0 := by
  have hT := hasDerivAt_iff_tendsto_slope.mp hf
  have : NeBot (𝓝[≠] x0 ⊓ 𝓟 {x | f x = 0}) := hacc
  have h1 : Tendsto (slope f x0) (𝓝[≠] x0 ⊓ 𝓟 {x | f x = 0}) (𝓝 f') := hT.mono_left inf_le_left
  have h2 : Tendsto (slope f x0) (𝓝[≠] x0 ⊓ 𝓟 {x | f x = 0}) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with y hy
    simp [slope_def_field, hy, h0]
  exact tendsto_nhds_unique h1 h2

/-- The ODE vector field `(ψ, ψ') ↦ (ψ', V ψ)`. -/
def field (V : ℝ → ℝ) (t : ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (y.2, V t * y.1)

lemma lipschitz_field {V : ℝ → ℝ} {B : ℝ} (hB : ∀ t ∈ Icc (0 : ℝ) 1, |V t| ≤ B) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    LipschitzOnWith (Real.toNNReal (1 + B)) (field V t) univ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB t ht)
  refine (LipschitzWith.of_dist_le_mul fun y z => ?_).lipschitzOnWith
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [field, Prod.dist_eq, Real.dist_eq]
  have hy1 : |y.1 - z.1| ≤ max |y.1 - z.1| |y.2 - z.2| := le_max_left _ _
  have hy2 : |y.2 - z.2| ≤ max |y.1 - z.1| |y.2 - z.2| := le_max_right _ _
  have hm : 0 ≤ max |y.1 - z.1| |y.2 - z.2| := le_max_of_le_left (abs_nonneg _)
  have hV : |V t * y.1 - V t * z.1| ≤ B * max |y.1 - z.1| |y.2 - z.2| := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (hB t ht) hy1 (abs_nonneg _) hB0
  apply max_le <;> nlinarith

end SturmLiouville
