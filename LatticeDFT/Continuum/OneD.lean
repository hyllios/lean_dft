/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.Continuum.HK
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# An unconditional continuum Hohenberg–Kohn theorem: one particle in a box

One particle on `[0, 1]` with hard walls (`ψ(0) = ψ(1) = 0`), kinetic energy `∫ ψ'²` and a
continuous potential `v`. States in the form domain are `C²`. Every hypothesis of `hk_of_ucp` is proved:

* `sep_box`: separation, from the fundamental lemma of the calculus of variations.
* `rigidL_box`: a continuous potential that is a.e. constant on `(0, 1)` is constant on `[0, 1]`.
* `ode_of_isGS`: a ground state solves `ψ'' = (v - E) ψ` on `(0, 1)` (integration by parts and the
  fundamental lemma).
* `ucp_of_isGS`: **unique continuation.** A ground state vanishes only on a null set. If its zeros
  accumulated inside `(0, 1)`, then `ψ = ψ' = 0` there, and uniqueness for the ODE would force
  `ψ ≡ 0`; so its zeros are countable.
* `hk_box`: **Hohenberg–Kohn in a box.** Two continuous potentials whose ground states have the same
  density `ψ²` differ by a constant.
-/

namespace LatticeDFT

namespace Continuum

namespace Box

open MeasureTheory Set Filter Topology

/-- Lebesgue measure on `(0, 1)`. -/
noncomputable abbrev μ1 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- The form domain: `C²` functions vanishing at the walls. -/
def Dom : Submodule ℝ (ℝ → ℝ) where
  carrier := {ψ | ContDiff ℝ 2 ψ ∧ ψ 0 = 0 ∧ ψ 1 = 0}
  add_mem' ha hb := ⟨ha.1.add hb.1, by simp [ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨contDiff_const, rfl, rfl⟩
  smul_mem' r _ ha := ⟨ha.1.const_smul r, by simp [ha.2.1], by simp [ha.2.2]⟩

lemma mem_Dom {ψ : ℝ → ℝ} : ψ ∈ Dom ↔ ContDiff ℝ 2 ψ ∧ ψ 0 = 0 ∧ ψ 1 = 0 := Iff.rfl

/-- Potentials: continuous functions on `[0, 1]`. -/
abbrev Pot := C(Icc (0 : ℝ) 1, ℝ)

/-- A potential extended to `ℝ` (constant outside `[0, 1]`). -/
noncomputable def ext (w : Pot) (x : ℝ) : ℝ := w (projIcc 0 1 zero_le_one x)

lemma continuous_ext (w : Pot) : Continuous (ext w) := w.continuous.comp continuous_projIcc

/-- The coupling of potentials: multiplication by the extended potential. -/
noncomputable def Lbox : Pot →ₗ[ℝ] (ℝ → ℝ) where
  toFun := ext
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma integrable_of_continuous {F : ℝ → ℝ} (hF : Continuous F) : Integrable F μ1 :=
  (hF.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self

/-- The kinetic energy form `∫ ψ' φ'`. -/
noncomputable def kin (ψ φ : ℝ → ℝ) : ℝ := ∫ x, deriv ψ x * deriv φ x ∂μ1

lemma two_ge_one : (1 : WithTop ℕ∞) ≤ 2 := by norm_cast

lemma diff_of_mem {ψ : ℝ → ℝ} (h : ψ ∈ Dom) : Differentiable ℝ ψ := h.1.differentiable (by norm_num)

lemma cont_deriv_of_mem {ψ : ℝ → ℝ} (h : ψ ∈ Dom) : Continuous (deriv ψ) :=
  h.1.continuous_deriv two_ge_one

/-- One particle in a box as a Hohenberg–Kohn setting. -/
noncomputable def setting : Setting μ1 Pot where
  D := Dom
  h0 := kin
  h0_add a ha b hb c hc := by
    simp only [kin, deriv_add (diff_of_mem ha _) (diff_of_mem hb _), add_mul]
    exact integral_add
      (integrable_of_continuous ((cont_deriv_of_mem ha).mul (cont_deriv_of_mem hc)))
      (integrable_of_continuous ((cont_deriv_of_mem hb).mul (cont_deriv_of_mem hc)))
  h0_smul r a ha c hc := by
    simp only [kin, deriv_const_smul r (diff_of_mem ha _), smul_eq_mul, mul_assoc]
    exact integral_const_mul r _
  h0_symm ψ _ φ _ := by simp only [kin, mul_comm]
  L := Lbox
  int_L w ψ φ hψ hφ := integrable_of_continuous
    ((continuous_ext w).mul (hψ.1.continuous.mul hφ.1.continuous))
  int_sq ψ φ hψ hφ := integrable_of_continuous (hψ.1.continuous.mul hφ.1.continuous)

/-- **Fundamental lemma** on `(0, 1)`, for continuous functions and test functions in `Dom`. -/
lemma eq_zero_of_integral {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ φ ∈ Dom, ∫ x, g x * φ x ∂μ1 = 0) : ∀ x ∈ Ioo (0 : ℝ) 1, g x = 0 := by
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Ioo (0 : ℝ) 1)
    (μ := volume) (f := g) isOpen_Ioo (hg.locallyIntegrable.locallyIntegrableOn _)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Ioo (0 : ℝ) 1) => ?_)
  · have h' : g =ᵐ[μ1] 0 := (ae_restrict_iff' measurableSet_Ioo).2 hae
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

/-- Separation holds in the box. -/
theorem sep_box : Sep setting := by
  intro w c ψ hψ h
  have hc : Continuous fun x => (ext w x - c) * ψ x :=
    ((continuous_ext w).sub continuous_const).mul hψ.1.continuous
  have := eq_zero_of_integral hc h
  exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ this)

/-- The constant potential `1`. -/
def one : Pot := ContinuousMap.const _ 1

/-- Rigidity in the box: a continuous potential that is a.e. constant on `(0, 1)` is constant. -/
theorem rigidL_box : RigidL setting one := by
  intro w c h
  have hO : EqOn (ext w) (fun _ => c) (Ioo 0 1) :=
    Measure.eqOn_open_of_ae_eq h isOpen_Ioo (continuous_ext w).continuousOn continuousOn_const
  have hC : EqOn (ext w) (fun _ => c) (Icc 0 1) :=
    hO.of_subset_closure (continuous_ext w).continuousOn continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  refine ⟨c, ?_⟩
  ext t
  have := hC t.2
  simp only [ext, projIcc_val] at this
  simp [one, this]

/-- The ground-state energy. -/
noncomputable def energy (v : Pot) (ψ : ℝ → ℝ) : ℝ := Q setting v ψ / ip (μ := μ1) ψ ψ

/-- **A ground state solves the Schrödinger equation** `ψ'' = (v - E) ψ` on `(0, 1)`. -/
theorem ode_of_isGS {v : Pot} {ψ : ℝ → ℝ} (hψ : IsGS setting v ψ) :
    ∀ x ∈ Ioo (0 : ℝ) 1, deriv (deriv ψ) x = (ext v x - energy v ψ) * ψ x := by
  have hD : ψ ∈ Dom := hψ.1
  have hd1 : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hD.1).2.2
  have hdd : Continuous (deriv (deriv ψ)) := hd1.continuous_deriv le_rfl
  set E := energy v ψ
  have hg : Continuous fun x => -deriv (deriv ψ) x + (ext v x - E) * ψ x :=
    hdd.neg.add (((continuous_ext v).sub continuous_const).mul hD.1.continuous)
  have key := eq_zero_of_integral hg (fun φ hφ => ?_)
  · intro x hx
    have := key x hx
    linarith
  -- integration by parts: `∫ ψ' φ' = -∫ ψ'' φ`
  have hφd := diff_of_mem hφ
  have hibp : kin ψ φ = -∫ x, deriv (deriv ψ) x * φ x ∂μ1 := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
      (u := deriv ψ) (u' := deriv (deriv ψ)) (v := φ) (v' := deriv φ)
      (fun x _ => (hd1.differentiable one_ne_zero x).hasDerivAt) (fun x _ => (hφd x).hasDerivAt)
      (hdd.intervalIntegrable _ _) ((cont_deriv_of_mem hφ).intervalIntegrable _ _)
    rw [hφ.2.1, hφ.2.2, mul_zero, mul_zero, sub_zero, zero_sub,
      intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
    exact h
  have hel := euler_lagrange hψ hφ
  change kin ψ φ + ∫ x, ext v x * (ψ x * φ x) ∂μ1 = E * ∫ x, ψ x * φ x ∂μ1 at hel
  rw [hibp] at hel
  have i1 := integrable_of_continuous (hdd.mul hφ.1.continuous)
  have i2 := integrable_of_continuous ((continuous_ext v).mul (hD.1.continuous.mul hφ.1.continuous))
  have i3 := integrable_of_continuous (hD.1.continuous.mul hφ.1.continuous)
  have hsplit : ∫ x, (-deriv (deriv ψ) x + (ext v x - E) * ψ x) * φ x ∂μ1 =
      -∫ x, deriv (deriv ψ) x * φ x ∂μ1 + ∫ x, ext v x * (ψ x * φ x) ∂μ1 -
        E * ∫ x, ψ x * φ x ∂μ1 := by
    have hpt : (fun x => (-deriv (deriv ψ) x + (ext v x - E) * ψ x) * φ x) = fun x =>
        (-(deriv (deriv ψ) x * φ x) + ext v x * (ψ x * φ x)) - E * (ψ x * φ x) := by
      funext x; ring
    rw [hpt, integral_sub (f := fun x => -(deriv (deriv ψ) x * φ x) + ext v x * (ψ x * φ x))
      (g := fun x => E * (ψ x * φ x)) (i1.neg.add i2) (i3.const_mul E),
      integral_add (f := fun x => -(deriv (deriv ψ) x * φ x))
        (g := fun x => ext v x * (ψ x * φ x)) i1.neg i2, integral_neg,
      integral_const_mul]
  rw [hsplit]
  linarith

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

/-- **Isolated zeros.** If the zeros of a ground state accumulate at a point of `(0, 1)`, the
ground state vanishes on all of `(0, 1)`. -/
theorem eq_zero_of_accPt {v : Pot} {ψ : ℝ → ℝ} (hψ : IsGS setting v ψ) {x0 : ℝ}
    (hx0 : x0 ∈ Ioo (0 : ℝ) 1) (hacc : AccPt x0 (𝓟 {x | ψ x = 0})) :
    ∀ t ∈ Ioo (0 : ℝ) 1, ψ t = 0 := by
  have hD : ψ ∈ Dom := hψ.1
  have hd1 : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hD.1).2.2
  have hode := ode_of_isGS hψ
  set V : ℝ → ℝ := fun x => ext v x - energy v ψ
  -- `ψ(x₀) = 0` and `ψ'(x₀) = 0`
  have hcl : IsClosed {x | ψ x = 0} := isClosed_eq hD.1.continuous continuous_const
  have hψ0 : ψ x0 = 0 := hcl.closure_subset (hacc.clusterPt.mem_closure)
  have hdψ0 : deriv ψ x0 = 0 :=
    deriv_eq_zero_of_accPt ((diff_of_mem hD x0).hasDerivAt) hacc hψ0
  -- a bound for `V` on `[0, 1]`
  obtain ⟨B, hB⟩ : ∃ B, ∀ t ∈ Icc (0 : ℝ) 1, |V t| ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((continuous_ext v).sub continuous_const).continuousOn
    exact ⟨B, fun t ht => by simpa [Real.norm_eq_abs] using hB t ht⟩
  intro t ht
  set ε := min (min x0 t) (min (1 - x0) (1 - t)) / 2
  have hε : 0 < ε := by
    simp only [ε]
    have := hx0.1; have := hx0.2; have := ht.1; have := ht.2
    positivity
  have hm : 0 < min (min x0 t) (min (1 - x0) (1 - t)) := by
    have := hx0.1; have := hx0.2; have := ht.1; have := ht.2
    simp only [lt_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hεx : ε < min (min x0 t) (min (1 - x0) (1 - t)) := half_lt_self hm
  have h1 : ε < x0 := lt_of_lt_of_le hεx ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ε < t := lt_of_lt_of_le hεx ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ε < 1 - x0 := lt_of_lt_of_le hεx ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : ε < 1 - t := lt_of_lt_of_le hεx ((min_le_right _ _).trans (min_le_right _ _))
  have hsub : Ioo ε (1 - ε) ⊆ Ioo (0 : ℝ) 1 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set Y : ℝ → ℝ × ℝ := fun s => (ψ s, deriv ψ s)
  have hY : ContinuousOn Y (Icc ε (1 - ε)) :=
    (hD.1.continuous.prodMk (cont_deriv_of_mem hD)).continuousOn
  have hY' : ∀ s ∈ Ioo ε (1 - ε), HasDerivAt Y (field V s (Y s)) s := by
    intro s hs
    have e1 := (diff_of_mem hD s).hasDerivAt
    have e2 := (hd1.differentiable one_ne_zero s).hasDerivAt
    rw [hode s (hsub hs)] at e2
    exact e1.prodMk e2
  have heq := ODE_solution_unique_of_mem_Icc (v := field V) (s := fun _ => univ)
    (K := Real.toNNReal (1 + B)) (f := Y) (g := fun _ => (0, 0))
    (fun s hs => lipschitz_field hB ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    ⟨h1, by linarith⟩ hY hY' (fun _ _ => mem_univ _) continuousOn_const
    (fun s _ => by
      have := hasDerivAt_const s ((0 : ℝ), (0 : ℝ))
      convert this using 1
      simp [field])
    (fun _ _ => mem_univ _) (by simp [Y, hψ0, hdψ0])
  have := heq ⟨h2.le, by linarith⟩
  simpa [Y] using congrArg Prod.fst this

/-- **Unique continuation in the box.** A ground state vanishes only on a null set. -/
theorem ucp_of_isGS {v : Pot} {ψ : ℝ → ℝ} (hψ : IsGS setting v ψ) : ∀ᵐ x ∂μ1, ψ x ≠ 0 := by
  have hD : ψ ∈ Dom := hψ.1
  -- `ψ` does not vanish on all of `(0, 1)`
  have hne : ¬ ∀ t ∈ Ioo (0 : ℝ) 1, ψ t = 0 := by
    intro h
    have hpos := hψ.2.1
    have : ip (μ := μ1) ψ ψ = 0 := by
      simp only [ip]
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        (fun x hx => by simp [h x hx])]
      simp
    linarith
  -- so its zeros in each `[1/(k+2), 1 - 1/(k+2)]` are finite
  have hfin : ∀ k : ℕ,
      ({x | ψ x = 0} ∩ Icc (1 / ((k : ℝ) + 2)) (1 - 1 / ((k : ℝ) + 2))).Finite := by
    intro k
    by_contra hinf
    obtain ⟨x0, hx0, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc
      inter_subset_right
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    have hx0' : x0 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx0.1], by linarith [hx0.2]⟩
    exact hne (eq_zero_of_accPt hψ hx0' (hacc.mono (principal_mono.2 inter_subset_left)))
  have hcount : ({x | ψ x = 0} ∩ Ioo (0 : ℝ) 1).Countable := by
    refine (countable_iUnion fun k => (hfin k).countable).mono ?_
    rintro x ⟨hx, hx0, hx1⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (max (1 / x) (1 / (1 - x)))
    refine mem_iUnion.mpr ⟨k, hx, ?_, ?_⟩
    · have h1 : 1 / x < (k : ℝ) + 2 := by linarith [le_max_left (1 / x) (1 / (1 - x))]
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hx0] at h1
      linarith
    · have h1 : 1 / (1 - x) < (k : ℝ) + 2 := by linarith [le_max_right (1 / x) (1 / (1 - x))]
      have hpos : 0 < 1 - x := by linarith
      rw [div_lt_iff₀ hpos] at h1
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have : 1 / ((k : ℝ) + 2) < 1 - x := by rw [div_lt_iff₀ hk2]; linarith
      linarith
  rw [ae_restrict_iff' measurableSet_Ioo]
  have h0 : volume ({x | ψ x = 0} ∩ Ioo (0 : ℝ) 1) = 0 := hcount.measure_zero _
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  simp only [Set.mem_ofPred_eq, Classical.not_imp, not_not] at hx
  exact ⟨hx.2, hx.1⟩

/-- **Hohenberg–Kohn for one particle in a box.** Let `ψ` and `ψ'` be ground states (in the `C²`
form domain with hard walls) of continuous potentials `v` and `v'` with the same density
`ψ² = ψ'²` on `(0, 1)`. Then `v - v'` is constant. -/
theorem hk_box {v v' : Pot} {ψ ψ' : ℝ → ℝ} (hψ : IsGS setting v ψ) (hψ' : IsGS setting v' ψ')
    (hρ : ∀ x ∈ Ioo (0 : ℝ) 1, ψ x ^ 2 = ψ' x ^ 2) : ∃ k : ℝ, v - v' = k • one := by
  have hρ' : ∀ x ∈ Ioo (0 : ℝ) 1, ψ x * ψ x = ψ' x * ψ' x := fun x hx => by
    simpa [sq] using hρ x hx
  have hn : ip (μ := μ1) ψ ψ = ip (μ := μ1) ψ' ψ' :=
    setIntegral_congr_fun measurableSet_Ioo hρ'
  have hd : dens setting ψ = dens setting ψ' := by
    funext w
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by
      rw [hρ' x hx]
  exact hk_of_ucp sep_box rigidL_box hψ hψ' hn hd (ucp_of_isGS hψ)

end Box

end Continuum

end LatticeDFT
