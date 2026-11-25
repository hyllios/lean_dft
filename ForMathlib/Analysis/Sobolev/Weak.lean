/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak derivatives in the plane

A first layer of Sobolev theory on open subsets `U` of `ℝ × ℝ`, real-valued and elementary
(Mathlib's Sobolev spaces live on the whole space, via the Fourier transform).

* `HasWeakDeriv U m f g`: `g` is the weak derivative of `f` in direction `m` on `U`:
  `∫ f ∂_m φ = -∫ g φ` for every smooth `φ` with compact support in `U`.
* `HasWeakDeriv.ae_eq`: weak derivatives are unique almost everywhere on `U`.
* `hasWeakDeriv_of_contDiff`: classical derivatives of `C¹` functions are weak derivatives.
* `HasWeakDeriv.add`, `HasWeakDeriv.const_mul`, `hasWeakDeriv_of_tendsto`.
* `hasWeakDeriv_abs`: **the chain rule for `|f|`**: for `C¹` `f`, `|f|` has weak derivative
  `sgn(f) ∂_m f` (smoothing `|f|` by `√(f² + ε²)` and dominated convergence).
* `sq_weak_abs_le`, `kato_energy`: **Kato's inequality** `|∂_m |f|| ≤ |∂_m f|`, so the kinetic
  energy of `|f|` is at most that of `f`: the first step of the Perron–Frobenius argument for
  bosons.
-/

namespace DFT

namespace Continuum

namespace Sobolev

open MeasureTheory Set Filter Topology

instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- Smooth test functions with compact support in `U`. -/
def IsTest (U : Set (ℝ × ℝ)) (φ : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- `g` is the weak derivative of `f` in direction `m` on `U`. -/
def HasWeakDeriv (U : Set (ℝ × ℝ)) (m : ℝ × ℝ) (f g : ℝ × ℝ → ℝ) : Prop :=
  LocallyIntegrableOn f U ∧ LocallyIntegrableOn g U ∧
    ∀ φ, IsTest U φ → ∫ p, f p * fderiv ℝ φ p m = -∫ p, g p * φ p

/-- The sign function. -/
noncomputable def sgn (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

lemma sgn_mul_self (x : ℝ) : sgn x * x = |x| := by
  unfold sgn
  split_ifs with h1 h2
  · rw [one_mul, abs_of_pos h1]
  · rw [abs_of_neg h2]; ring
  · have : x = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2); simp [this]

lemma abs_sgn_le (x : ℝ) : |sgn x| ≤ 1 := by
  unfold sgn; split_ifs <;> simp

lemma measurable_sgn : Measurable sgn := by
  unfold sgn
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      measurable_const)

section integrability

variable {U : Set (ℝ × ℝ)} {φ : ℝ × ℝ → ℝ}

lemma IsTest.continuous (h : IsTest U φ) : Continuous φ := h.1.continuous

lemma IsTest.continuous_fderiv (h : IsTest U φ) (m : ℝ × ℝ) :
    Continuous fun p => fderiv ℝ φ p m :=
  (h.1.continuous_fderiv (by simp)).clm_apply continuous_const

/-- A locally integrable function times a continuous function supported in a compact subset of `U`
is integrable. -/
lemma integrable_mul_of_support {f ψ : ℝ × ℝ → ℝ} (hf : LocallyIntegrableOn f U)
    (hψ : Continuous ψ) {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupp : ∀ p, p ∉ K → ψ p = 0) : Integrable (fun p => f p * ψ p) := by
  have h1 : IntegrableOn f K := hf.integrableOn_compact_subset hKU hK
  exact (h1.mul_continuousOn hψ.continuousOn hK).integrable_of_forall_notMem_eq_zero
    (fun p hp => by simp [hsupp p hp])

lemma notMem_tsupport {ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∉ tsupport ψ) : ψ p = 0 :=
  image_eq_zero_of_notMem_tsupport hp

lemma integrable_mul_test {f : ℝ × ℝ → ℝ} (hf : LocallyIntegrableOn f U) (h : IsTest U φ) :
    Integrable (fun p => f p * φ p) :=
  integrable_mul_of_support hf h.continuous h.2.1 h.2.2 (fun _ hp => notMem_tsupport hp)

lemma integrable_mul_dtest {f : ℝ × ℝ → ℝ} (hf : LocallyIntegrableOn f U) (h : IsTest U φ)
    (m : ℝ × ℝ) : Integrable (fun p => f p * fderiv ℝ φ p m) := by
  refine integrable_mul_of_support hf (h.continuous_fderiv m) h.2.1 h.2.2 (fun p hp => ?_)
  have : p ∉ tsupport (fderiv ℝ φ) := fun h' => hp (tsupport_fderiv_subset ℝ h')
  rw [image_eq_zero_of_notMem_tsupport this]; rfl

end integrability

variable {U : Set (ℝ × ℝ)} {m : ℝ × ℝ}

/-- **Uniqueness of weak derivatives**, almost everywhere on the open set `U`. -/
theorem HasWeakDeriv.ae_eq (hU : IsOpen U) {f g g' : ℝ × ℝ → ℝ} (h : HasWeakDeriv U m f g)
    (h' : HasWeakDeriv U m f g') : ∀ᵐ p, p ∈ U → g p = g' p := by
  have hloc : LocallyIntegrableOn (fun p => g p - g' p) U := h.2.1.sub h'.2.1
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc
    (fun φ hφ hc hsub => ?_)
  · filter_upwards [hae] with p hp hpU
    exact sub_eq_zero.mp (hp hpU)
  · have ht : IsTest U φ := ⟨hφ, hc, hsub⟩
    have e1 := h.2.2 φ ht
    have e2 := h'.2.2 φ ht
    have i1 := integrable_mul_test h.2.1 ht
    have i2 := integrable_mul_test h'.2.1 ht
    have : ∫ p, φ p • (g p - g' p) = ∫ p, (g p * φ p - g' p * φ p) := by
      congr 1; funext p; simp only [smul_eq_mul]; ring
    rw [this, integral_sub i1 i2]; linarith

/-- **Classical derivatives are weak derivatives.** -/
theorem hasWeakDeriv_of_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (m : ℝ × ℝ) :
    HasWeakDeriv U m f (fun p => fderiv ℝ f p m) := by
  have hfd : Continuous fun p => fderiv ℝ f p m :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn _,
    hfd.locallyIntegrable.locallyIntegrableOn _, fun φ hφ => ?_⟩
  have hfloc : LocallyIntegrableOn f U := hf.continuous.locallyIntegrable.locallyIntegrableOn _
  have hdloc : LocallyIntegrableOn (fun p => fderiv ℝ f p m) U :=
    hfd.locallyIntegrable.locallyIntegrableOn _
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_test hdloc hφ) (integrable_mul_dtest hfloc hφ m)
    (integrable_mul_test hfloc hφ) (fun p _ => (hf.differentiable one_ne_zero) p)
    (fun p _ => (hφ.1.differentiable (by simp)) p)

theorem HasWeakDeriv.add {f₁ f₂ g₁ g₂ : ℝ × ℝ → ℝ} (h₁ : HasWeakDeriv U m f₁ g₁)
    (h₂ : HasWeakDeriv U m f₂ g₂) : HasWeakDeriv U m (f₁ + f₂) (g₁ + g₂) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun φ hφ => ?_⟩
  have e1 := h₁.2.2 φ hφ
  have e2 := h₂.2.2 φ hφ
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (integrable_mul_dtest h₁.1 hφ m) (integrable_mul_dtest h₂.1 hφ m),
    integral_add (integrable_mul_test h₁.2.1 hφ) (integrable_mul_test h₂.2.1 hφ), e1, e2]
  ring

/-- **Weak derivatives pass to limits.** -/
theorem hasWeakDeriv_of_tendsto {F G : ℕ → ℝ × ℝ → ℝ} {f g : ℝ × ℝ → ℝ}
    (hFG : ∀ n, HasWeakDeriv U m (F n) (G n)) (hf : LocallyIntegrableOn f U)
    (hg : LocallyIntegrableOn g U)
    (hF : ∀ φ, IsTest U φ → Tendsto (fun n => ∫ p, F n p * fderiv ℝ φ p m) atTop
      (𝓝 (∫ p, f p * fderiv ℝ φ p m)))
    (hG : ∀ φ, IsTest U φ → Tendsto (fun n => ∫ p, G n p * φ p) atTop (𝓝 (∫ p, g p * φ p))) :
    HasWeakDeriv U m f g := by
  refine ⟨hf, hg, fun φ hφ => ?_⟩
  have h1 := hF φ hφ
  have h2 : Tendsto (fun n => ∫ p, F n p * fderiv ℝ φ p m) atTop (𝓝 (-∫ p, g p * φ p)) := by
    have := (hG φ hφ).neg
    refine this.congr fun n => ?_
    exact ((hFG n).2.2 φ hφ).symm
  exact tendsto_nhds_unique h1 h2

/-- The smoothing `√(f² + ε²)` of `|f|`. -/
lemma hasFDerivAt_smooth_abs {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) :
    HasFDerivAt (fun q => √(f q ^ 2 + ε ^ 2))
      ((1 / (2 * √(f p ^ 2 + ε ^ 2))) • ((2 * f p) • fderiv ℝ f p)) p := by
  have hd : HasFDerivAt f (fderiv ℝ f p) p :=
    ((hf.differentiable one_ne_zero) p).hasFDerivAt
  have h2 : HasFDerivAt (fun q => f q ^ 2 + ε ^ 2) ((2 * f p) • fderiv ℝ f p) p := by
    have := (hd.pow 2).add_const (ε ^ 2)
    convert this using 1
    simp [two_mul]
  exact h2.sqrt (by positivity)

lemma contDiff_smooth_abs {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 fun q => √(f q ^ 2 + ε ^ 2) :=
  ((hf.pow 2).add contDiff_const).sqrt fun q => by positivity

lemma fderiv_smooth_abs {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ε : ℝ} (hε : 0 < ε)
    (p m : ℝ × ℝ) :
    fderiv ℝ (fun q => √(f q ^ 2 + ε ^ 2)) p m = f p / √(f p ^ 2 + ε ^ 2) * fderiv ℝ f p m := by
  rw [(hasFDerivAt_smooth_abs hf hε p).fderiv]
  have : 0 < √(f p ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  simp only [smul_apply, smul_eq_mul]
  field_simp

lemma tendsto_sqrt_eps (x : ℝ) :
    Tendsto (fun n : ℕ => √(x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 |x|) := by
  have h : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := ((h.pow 2).const_add (x ^ 2)).sqrt
  simpa [Real.sqrt_sq_eq_abs] using h2

lemma sgn_eq_div {x : ℝ} (hx : x ≠ 0) : sgn x = x / |x| := by
  rcases lt_or_gt_of_ne hx with h | h
  · have h1 : ¬ 0 < x := not_lt.mpr h.le
    simp only [abs_of_neg h, sgn, h1, h, ↓reduceIte, div_neg, div_self hx]
  · simp only [abs_of_pos h, sgn, h, ↓reduceIte, div_self hx]

lemma tendsto_ratio_eps (x : ℝ) :
    Tendsto (fun n : ℕ => x / √(x ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 (sgn x)) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have : sgn 0 = 0 := by simp [sgn]
    rw [this]
    simp only [zero_div]
    exact tendsto_const_nhds
  · rw [sgn_eq_div hx]
    exact tendsto_const_nhds.div (tendsto_sqrt_eps x) (abs_ne_zero.mpr hx)

lemma abs_ratio_le (x ε : ℝ) (hε : 0 < ε) : |x / √(x ^ 2 + ε ^ 2)| ≤ 1 := by
  have hs : 0 < √(x ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hs, div_le_one hs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma sqrt_le_abs_add (x ε : ℝ) (hε : 0 < ε) : √(x ^ 2 + ε ^ 2) ≤ |x| + ε := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg x, sq_abs x]

/-- **Chain rule for `|f|`.** For `C¹` `f`, `|f|` has weak derivative `sgn(f) ∂_m f`. -/
theorem hasWeakDeriv_abs {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (m : ℝ × ℝ) :
    HasWeakDeriv U m (fun p => |f p|) (fun p => sgn (f p) * fderiv ℝ f p m) := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by simp only [ε]; positivity
  have hfd : Continuous fun p => fderiv ℝ f p m :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine hasWeakDeriv_of_tendsto (F := fun n q => √(f q ^ 2 + ε n ^ 2))
    (G := fun n q => f q / √(f q ^ 2 + ε n ^ 2) * fderiv ℝ f q m)
    (fun n => ?_) ((continuous_abs.comp hf.continuous).locallyIntegrable.locallyIntegrableOn _)
    ?_ (fun φ hφ => ?_) (fun φ hφ => ?_)
  · have := hasWeakDeriv_of_contDiff (U := U) (contDiff_smooth_abs hf (hε n)) m
    simpa only [fderiv_smooth_abs hf (hε n)] using this
  · -- `sgn(f) ∂f` is locally integrable on `U`: bounded by `|∂f|` and measurable
    refine (hfd.locallyIntegrable.locallyIntegrableOn U).mono
      (((measurable_sgn.comp hf.continuous.measurable).mul hfd.measurable).aestronglyMeasurable)
      (ae_of_all _ fun p => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_sgn_le _)
  · -- dominated convergence for `∫ F_n ∂φ`
    have hloc : LocallyIntegrableOn (fun p => |f p| + 1) U :=
      ((continuous_abs.comp hf.continuous).add continuous_const).locallyIntegrable
        |>.locallyIntegrableOn _
    refine tendsto_integral_of_dominated_convergence
      (fun p => ‖(|f p| + 1) * fderiv ℝ φ p m‖)
      (fun n => (((contDiff_smooth_abs hf (hε n)).continuous).mul
        (hφ.continuous_fderiv m)).aestronglyMeasurable)
      (integrable_mul_dtest hloc hφ m).norm (fun n => ae_of_all _ fun p => ?_)
      (ae_of_all _ fun p => (tendsto_sqrt_eps (f p)).mul_const _)
    have h1 := sqrt_le_abs_add (f p) (ε n) (hε n)
    have h2 : ε n ≤ 1 := by
      simp only [ε]; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h3 : |(|f p| + 1)| = |f p| + 1 := abs_of_nonneg (by positivity)
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  · -- dominated convergence for `∫ G_n φ`
    have hloc : LocallyIntegrableOn (fun p => fderiv ℝ f p m) U :=
      hfd.locallyIntegrable.locallyIntegrableOn _
    refine tendsto_integral_of_dominated_convergence
      (fun p => ‖fderiv ℝ f p m * φ p‖)
      (fun n => ((((hf.continuous).div (contDiff_smooth_abs hf (hε n)).continuous
        (fun q => (Real.sqrt_pos.mpr (by positivity)).ne')).mul hfd).mul
          hφ.continuous).aestronglyMeasurable)
      (integrable_mul_test hloc hφ).norm (fun n => ae_of_all _ fun p => ?_)
      (ae_of_all _ fun p => ((tendsto_ratio_eps (f p)).mul_const _).mul_const _)
    have h1 := abs_ratio_le (f p) (ε n) (hε n)
    simp only [Real.norm_eq_abs, abs_mul]
    have h4 : 0 ≤ |fderiv ℝ f p m| * |φ p| := by positivity
    nlinarith [abs_nonneg (f p / √(f p ^ 2 + ε n ^ 2)), abs_nonneg (fderiv ℝ f p m),
      abs_nonneg (φ p)]

/-- **Kato's inequality**: the weak derivative of `|f|` is pointwise bounded by `|∂f|`. -/
theorem sq_weak_abs_le (f : ℝ × ℝ → ℝ) (m : ℝ × ℝ) (p : ℝ × ℝ) :
    (sgn (f p) * fderiv ℝ f p m) ^ 2 ≤ (fderiv ℝ f p m) ^ 2 := by
  rw [mul_pow]
  have h := abs_sgn_le (f p)
  have h2 : sgn (f p) ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (sgn (f p))]
  nlinarith [sq_nonneg (fderiv ℝ f p m)]

/-- **Kato's inequality, integrated**: on any compact set, the kinetic energy of `|f|` (through its
weak derivative) is at most that of `f`. -/
theorem kato_energy {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (m : ℝ × ℝ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) :
    ∫ p in K, (sgn (f p) * fderiv ℝ f p m) ^ 2 ≤ ∫ p in K, (fderiv ℝ f p m) ^ 2 := by
  have hfd : Continuous fun p => fderiv ℝ f p m :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact integral_mono_of_nonneg (ae_of_all _ fun p => sq_nonneg _)
    ((hfd.pow 2).continuousOn.integrableOn_compact hK)
    (ae_of_all _ fun p => sq_weak_abs_le f m p)

end Sobolev

end Continuum

end DFT
