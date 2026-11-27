/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import DFT.Continuum.Line.MeasurePotential.MeasureGS

/-!
# Neumann walls and `H⁻¹` potentials: one particle, the form bound

This file starts Corso's setting (Lett. Math. Phys. 2026, arXiv:2504.05501): particles on `[0, 1]`
with Neumann walls, in potentials from the dual of `H¹(0, 1)`.

* `H1N g`: `g` is absolutely continuous on `[0, 1]` with `g' ∈ L²`; no boundary values. This is
  `H¹(0, 1)`.
* `H1E := WithLp 2 (ℝ × L²(0, 1))`. The map `g ↦ (g(0), g')` (`toE`) identifies `H¹(0, 1)` with
  `H1E`, and its norm `g(0)² + ∫ g'²` is equivalent to the `H¹` norm.
* `PotH := StrongDual ℝ H1E`: the `H⁻¹` potentials. Every `v` is `v(ρ) = α ρ(0) + ∫ β ρ'` with
  `β ∈ L²` (Riesz). The δ-function at `x` is `α = 1`, `β = 1_{[0,x]}` (`deltaH`, `deltaH_apply`).
* `sq_le_H1N`: `ψ(t)² ≤ (1 + a) ∫ ψ² + (∫ ψ'²) / a` for `a > 0`.
* `sqE ψ = toE (ψ²) = (ψ(0)², 2ψψ')`; `norm_sqE_sq_le`: `‖ψ²‖_E² ≤ ‖ψ‖_∞⁴ + 4 ‖ψ‖_∞² ∫ ψ'²`.
* **`abs_v_sq_le`**: `|v(ψ²)| ≤ ½ ∫ ψ'² + C_v ∫ ψ²`: `H⁻¹` potentials are infinitesimally form
  bounded on `H¹(0, 1)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology Interval

/-! ### `H¹(0, 1)` -/

/-- `g ∈ H¹(0, 1)`: absolutely continuous on `[0, 1]`, `g' ∈ L²`. No boundary conditions. -/
def H1N (g : ℝ → ℝ) : Prop :=
  AbsolutelyContinuousOnInterval g 0 1 ∧ IntegrableOn (fun t => deriv g t ^ 2) (Ioo (0 : ℝ) 1)

namespace H1N

variable {g h : ℝ → ℝ}

lemma continuousOn (hg : H1N g) : ContinuousOn g (Icc 0 1) := by
  simpa [uIcc01] using hg.1.continuousOn

lemma of_H10 (hg : H10 g) : H1N g := ⟨hg.1, hg.2.2.2⟩

lemma int_sq (hg : H1N g) : Integrable (fun t => g t ^ 2) vol01 :=
  H10.int_sq_of_contOn hg.continuousOn

lemma int_dsq (hg : H1N g) : Integrable (fun t => deriv g t ^ 2) vol01 := hg.2

lemma memLp_deriv (hg : H1N g) : MemLp (deriv g) 2 vol01 :=
  (memLp_two_iff_integrable_sq (measurable_deriv g).aestronglyMeasurable).2 hg.2

lemma ac_mono (hg : H1N g) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval g a b :=
  hg.1.mono (by rw [uIcc01]; exact uIcc_subset_Icc ha hb)

/-- The fundamental theorem of calculus on `[0, 1]`. -/
lemma integral_deriv (hg : H1N g) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ∫ s in a..b, deriv g s = g b - g a :=
  (hg.ac_mono ha hb).integral_deriv_eq_sub

lemma ae_deriv_mul (hg : H1N g) (hh : H1N h) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) 1 →
      deriv (fun t => g t * h t) s = deriv g s * h s + g s * deriv h s := by
  have hdg := hg.1.ae_differentiableAt
  have hdh := hh.1.ae_differentiableAt
  rw [uIcc01] at hdg hdh
  filter_upwards [hdg, hdh] with s hs hs' hsI
  exact ((hs hsI).hasDerivAt.mul (hs' hsI).hasDerivAt).deriv

end H1N

/-! ### The sup bound without boundary conditions -/

/-- `ψ(t)² ≤ (1 + a) ∫ ψ² + (∫ ψ'²) / a` for `ψ ∈ H¹(0, 1)`, `a > 0`, `t ∈ [0, 1]`. -/
theorem sq_le_H1N {ψ : ℝ → ℝ} (hψ : H1N ψ) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ψ t ^ 2 ≤ (1 + a) * ∫ s, ψ s ^ 2 ∂vol01 + kinM ψ / a := by
  set g : ℝ → ℝ := fun s => a * ψ s ^ 2 + deriv ψ s ^ 2 / a
  have hg : Integrable g vol01 := (hψ.int_sq.const_mul a).add (hψ.int_dsq.div_const a)
  have hg0 : ∀ s, 0 ≤ g s := fun s => by simp only [g]; positivity
  have hG : ∫ s, g s ∂vol01 = a * ∫ s, ψ s ^ 2 ∂vol01 + kinM ψ / a := by
    rw [integral_add (hψ.int_sq.const_mul a) (hψ.int_dsq.div_const a), integral_const_mul,
      integral_div, kinM]
  have hpt : ∀ s, |2 * ψ s * deriv ψ s| ≤ g s := fun s => by
    simp only [g]
    rw [abs_le]; constructor
    · have e : a * ψ s ^ 2 + deriv ψ s ^ 2 / a + 2 * ψ s * deriv ψ s =
          (a * ψ s + deriv ψ s) ^ 2 / a := by field_simp; ring
      have : 0 ≤ (a * ψ s + deriv ψ s) ^ 2 / a := by positivity
      linarith
    · have e : a * ψ s ^ 2 + deriv ψ s ^ 2 / a - 2 * ψ s * deriv ψ s =
          (a * ψ s - deriv ψ s) ^ 2 / a := by field_simp; ring
      have : 0 ≤ (a * ψ s - deriv ψ s) ^ 2 / a := by positivity
      linarith
  have hD := H1N.ae_deriv_mul hψ hψ
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ψ t ^ 2 ≤ ψ s ^ 2 + ∫ x, g x ∂vol01 := fun s hs => by
    have hac : AbsolutelyContinuousOnInterval (fun x => ψ x * ψ x) s t :=
      (hψ.1.fun_mul hψ.1).mono (by rw [uIcc01]; exact uIcc_subset_Icc hs ht)
    have hFTC := hac.integral_deriv_eq_sub
    have hsub : Ι s t ⊆ Ioc (0 : ℝ) 1 := fun x hx => by
      rw [mem_uIoc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hs.1.trans_lt h1, h2.trans ht.2⟩
      · exact ⟨ht.1.trans_lt h1, h2.trans hs.2⟩
    have hgI : IntegrableOn g (Ioc (0 : ℝ) 1) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo (f := g)).2 hg
    have h1 : |∫ x in s..t, deriv (fun x => ψ x * ψ x) x| ≤ ∫ x in Ι s t, g x := by
      refine (intervalIntegral.norm_integral_le_integral_norm_uIoc (μ := volume)
        (f := fun x => deriv (fun x => ψ x * ψ x) x)).trans ?_
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hgI.mono_set hsub) ?_
      filter_upwards [ae_restrict_of_ae hD, ae_restrict_mem measurableSet_uIoc] with x hx hxI
      have hxI' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (hsub hxI)
      rw [hx hxI', Real.norm_eq_abs]
      have := hpt x
      rwa [show deriv ψ x * ψ x + ψ x * deriv ψ x = 2 * ψ x * deriv ψ x by ring]
    have h2 : ∫ x in Ι s t, g x ≤ ∫ x, g x ∂vol01 :=
      setIntegral_mono_set hg (ae_of_all _ hg0)
        ((LE.le.eventuallySubset hsub).congr .rfl Ioo_ae_eq_Ioc.symm)
    have h3 := le_abs_self (∫ x in s..t, deriv (fun x => ψ x * ψ x) x)
    rw [hFTC] at h1 h3
    nlinarith
  have hm : ∫ s, ψ t ^ 2 ∂vol01 ≤ ∫ s, (ψ s ^ 2 + ∫ x, g x ∂vol01) ∂vol01 :=
    integral_mono_ae (integrable_const _) (hψ.int_sq.add (integrable_const _))
      ((ae_restrict_mem measurableSet_Ioo).mono fun s hs => key s (Ioo_subset_Icc_self hs))
  rw [integral_const, integral_add hψ.int_sq (integrable_const _), integral_const, hG] at hm
  have : (vol01.real univ) = 1 := by simp
  rw [this, one_smul, one_smul] at hm
  linarith

/-- A uniform bound for `ψ ∈ H¹(0, 1)`: `ψ(t)² ≤ M` on `[0, 1]`. -/
lemma H1N.exists_sq_bound {ψ : ℝ → ℝ} (hψ : H1N ψ) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ψ t ^ 2 ≤ M :=
  ⟨2 * ∫ s, ψ s ^ 2 ∂vol01 + kinM ψ, by
    have : 0 ≤ ∫ s, ψ s ^ 2 ∂vol01 := integral_nonneg fun s => sq_nonneg (ψ s)
    have : 0 ≤ kinM ψ := integral_nonneg fun _ => sq_nonneg _
    positivity, fun t ht => by simpa [one_add_one_eq_two] using sq_le_H1N hψ one_pos ht⟩

/-- Products: `ψ φ ∈ H¹(0, 1)`, with `(ψ φ)' = ψ' φ + ψ φ'` a.e. -/
lemma H1N.mul {ψ φ : ℝ → ℝ} (hψ : H1N ψ) (hφ : H1N φ) : H1N fun t => ψ t * φ t := by
  refine ⟨hψ.1.fun_mul hφ.1, ?_⟩
  obtain ⟨M, hM0, hM⟩ := hψ.exists_sq_bound
  obtain ⟨M', hM0', hM'⟩ := hφ.exists_sq_bound
  have hi : Integrable (fun t => 2 * (M' * deriv ψ t ^ 2) + 2 * (M * deriv φ t ^ 2)) vol01 :=
    ((hψ.int_dsq.const_mul M').const_mul 2).add ((hφ.int_dsq.const_mul M).const_mul 2)
  refine hi.mono' ((measurable_deriv _).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae (H1N.ae_deriv_mul hψ hφ), ae_restrict_mem measurableSet_Ioo]
    with t ht htI
  have htI' := Ioo_subset_Icc_self htI
  rw [ht htI', Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := hM t htI'
  have h2 := hM' t htI'
  nlinarith [sq_nonneg (deriv ψ t * φ t - ψ t * deriv φ t), sq_nonneg (deriv ψ t),
    sq_nonneg (deriv φ t), mul_le_mul_of_nonneg_left h2 (sq_nonneg (deriv ψ t)),
    mul_le_mul_of_nonneg_left h1 (sq_nonneg (deriv φ t))]

/-! ### `H¹(0, 1) ≅ ℝ × L²` and the `H⁻¹` potentials -/

/-- `ℝ × L²(0, 1)` with the Hilbert norm: the model of `H¹(0, 1)` via `g ↦ (g(0), g')`. -/
abbrev H1E : Type := WithLp 2 (ℝ × L2I)

/-- The `H⁻¹(0, 1)` potentials: continuous linear functionals on `H¹(0, 1)`. -/
abbrev PotH : Type := StrongDual ℝ H1E

/-- The derivative of `g ∈ H¹(0, 1)` as an element of `L²(0, 1)`. -/
noncomputable def dN {g : ℝ → ℝ} (hg : H1N g) : L2I := hg.memLp_deriv.toLp (deriv g)

lemma dN_ae {g : ℝ → ℝ} (hg : H1N g) : (dN hg : ℝ → ℝ) =ᵐ[vol01] deriv g :=
  MemLp.coeFn_toLp _

lemma norm_dN_sq {g : ℝ → ℝ} (hg : H1N g) : ‖dN hg‖ ^ 2 = kinM g := by
  rw [norm_sq_L2I, kinM]
  refine integral_congr_ae ?_
  filter_upwards [dN_ae hg] with t ht
  simp only [ht]

/-- `g ∈ H¹(0, 1)` as the pair `(g(0), g') ∈ H1E`. -/
noncomputable def toE {g : ℝ → ℝ} (hg : H1N g) : H1E := WithLp.toLp 2 (g 0, dN hg)

lemma norm_toE_sq {g : ℝ → ℝ} (hg : H1N g) : ‖toE hg‖ ^ 2 = g 0 ^ 2 + kinM g := by
  rw [WithLp.prod_norm_sq_eq_of_L2, toE, WithLp.toLp_fst, WithLp.toLp_snd, norm_dN_sq,
    Real.norm_eq_abs, sq_abs]

/-- `g` is recovered from `toE g`: `g(t) = g(0) + ∫₀ᵗ g'`. -/
lemma eq_toE {g : ℝ → ℝ} (hg : H1N g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g t = (toE hg).fst + prim (toE hg).snd t := by
  simp only [toE, WithLp.toLp_fst, WithLp.toLp_snd, prim, dN]
  rw [integral_congr_mu1 (MemLp.coeFn_toLp hg.memLp_deriv) ht,
    hg.integral_deriv ⟨le_rfl, zero_le_one⟩ ht]
  ring

/-- The density `ψ²` of `ψ ∈ H¹(0, 1)`, as an element of `H1E`. -/
noncomputable def sqE {ψ : ℝ → ℝ} (hψ : H1N ψ) : H1E := toE (hψ.mul hψ)

/-- `‖ψ²‖_E² ≤ M² + 4 M ∫ ψ'²` when `ψ² ≤ M` on `[0, 1]`. -/
lemma norm_sqE_sq_le {ψ : ℝ → ℝ} (hψ : H1N ψ) {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ψ t ^ 2 ≤ M) :
    ‖sqE hψ‖ ^ 2 ≤ M ^ 2 + 4 * M * kinM ψ := by
  have h0 := hM 0 ⟨le_rfl, zero_le_one⟩
  have hM0 : 0 ≤ M := (sq_nonneg _).trans h0
  rw [sqE, norm_toE_sq]
  have hk : kinM (fun t => ψ t * ψ t) ≤ 4 * M * kinM ψ := by
    rw [kinM, kinM, ← integral_const_mul]
    refine integral_mono_ae (hψ.mul hψ).int_dsq (hψ.int_dsq.const_mul _) ?_
    filter_upwards [ae_restrict_of_ae (H1N.ae_deriv_mul hψ hψ), ae_restrict_mem measurableSet_Ioo]
      with t ht htI
    rw [ht (Ioo_subset_Icc_self htI)]
    have := hM t (Ioo_subset_Icc_self htI)
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg (deriv ψ t))]
  have : (ψ 0 * ψ 0) ^ 2 ≤ M ^ 2 := by
    rw [← sq]; exact pow_le_pow_left₀ (sq_nonneg _) h0 2
  linarith

/-- The form-bound constant of an `H⁻¹` potential. -/
noncomputable def cH (v : PotH) : ℝ :=
  (‖v‖ + 4 * ‖v‖ ^ 2) * (2 + 4 * (‖v‖ + 4 * ‖v‖ ^ 2))

lemma cH_nonneg (v : PotH) : 0 ≤ cH v := by unfold cH; positivity

/-- **Form boundedness**: `|v(ψ²)| ≤ ½ ∫ ψ'² + C_v ∫ ψ²` for `ψ ∈ H¹(0, 1)` and `v ∈ H⁻¹`. -/
theorem abs_v_sq_le (v : PotH) {ψ : ℝ → ℝ} (hψ : H1N ψ) :
    |v (sqE hψ)| ≤ kinM ψ / 2 + cH v * ∫ s, ψ s ^ 2 ∂vol01 := by
  set c := ‖v‖ + 4 * ‖v‖ ^ 2 with hc
  set a := 4 * c + 1
  have hc0 : 0 ≤ c := by positivity
  have ha : 0 < a := by positivity
  set m := ∫ s, ψ s ^ 2 ∂vol01
  set k := kinM ψ
  have hm0 : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  have hk0 : 0 ≤ k := integral_nonneg fun _ => sq_nonneg _
  set M := (1 + a) * m + k / a
  have hM : ∀ t ∈ Icc (0 : ℝ) 1, ψ t ^ 2 ≤ M := fun t ht => sq_le_H1N hψ ha ht
  have hM0 : 0 ≤ M := by positivity
  have hE : ‖sqE hψ‖ ^ 2 ≤ M ^ 2 + 4 * M * k := norm_sqE_sq_le hψ hM
  -- `‖ψ²‖_E ≤ M + 2 √M √k`
  have hE' : ‖sqE hψ‖ ≤ M + 2 * √M * √k := by
    have h1 : ‖sqE hψ‖ ^ 2 ≤ (M + 2 * √M * √k) ^ 2 := by
      have e : (M + 2 * √M * √k) ^ 2 = M ^ 2 + 4 * M * k + 4 * M * √M * √k := by
        have := Real.sq_sqrt hM0; have := Real.sq_sqrt hk0; nlinarith
      rw [e]
      have : 0 ≤ 4 * M * √M * √k := by positivity
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
  have h1 : |v (sqE hψ)| ≤ ‖v‖ * (M + 2 * √M * √k) := by
    rw [← Real.norm_eq_abs]
    exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left hE' (norm_nonneg v))
  -- `2 ‖v‖ √M √k ≤ k / 4 + 4 ‖v‖² M`
  have h2 : ‖v‖ * (2 * √M * √k) ≤ k / 4 + 4 * ‖v‖ ^ 2 * M := by
    have := Real.sq_sqrt hM0; have := Real.sq_sqrt hk0
    nlinarith [sq_nonneg (4 * ‖v‖ * √M - √k)]
  have h3 : c * M ≤ c * (1 + a) * m + k / 4 := by
    have : c * (k / a) ≤ k / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ ha (by norm_num)]; nlinarith
    simp only [M]; nlinarith
  have h4 : c * (1 + a) = cH v := by simp only [cH, a, c]; ring
  rw [← h4]
  nlinarith

/-! ### Measure potentials are `H⁻¹` potentials -/

lemma norm_fst_le (e : H1E) : |e.fst| ≤ ‖e‖ := by
  have := WithLp.prod_norm_sq_eq_of_L2 e
  rw [Real.norm_eq_abs] at this
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [norm_nonneg e.snd])

lemma norm_snd_le (e : H1E) : ‖e.snd‖ ≤ ‖e‖ := by
  have := WithLp.prod_norm_sq_eq_of_L2 e
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [norm_nonneg e.fst])

/-- The function `t ↦ e.fst + ∫₀ᵗ e.snd` on `[0, 1]` represented by `e ∈ H1E`. -/
noncomputable def evE : H1E →L[ℝ] C01 :=
  LinearMap.mkContinuous
    { toFun := fun e => ContinuousMap.const _ e.fst + primP e.snd
      map_add' := fun e e' => by
        ext t
        simp [prim_add _ _ t.2]; ring
      map_smul' := fun c e => by
        ext t
        simp [prim_smul _ _ t.2] } 2
    fun e => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.add_apply,
        ContinuousMap.const_apply, primP_apply, Real.norm_eq_abs]
      have := abs_prim_le e.snd t.2
      have := norm_fst_le e
      have := norm_snd_le e
      calc |e.fst + prim e.snd t| ≤ |e.fst| + |prim e.snd t| := abs_add_le _ _
        _ ≤ 2 * ‖e‖ := by linarith

lemma evE_toE {g : ℝ → ℝ} (hg : H1N g) (t : Icc (0 : ℝ) 1) : evE (toE hg) t = g t := by
  simp only [evE, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousMap.add_apply, ContinuousMap.const_apply, primP_apply]
  exact (eq_toE hg t.2).symm

/-- A measure potential as an `H⁻¹` potential. -/
noncomputable def ofM (ν : PotM) : PotH := ν.comp evE

lemma ofM_toE (ν : PotM) {g : ℝ → ℝ} (hg : H1N g) (hgc : ContinuousOn g (Icc 0 1)) :
    ofM ν (toE hg) = ν ⟨fun t => g t, hgc.domRestrict⟩ := by
  rw [ofM, ContinuousLinearMap.comp_apply]
  congr 1; ext t; exact evE_toE hg t

/-- On densities, `ofM ν` is `ν`: `(ofM ν)(ψ²) = ν(ψ²)` for `ψ ∈ H¹₀`. -/
lemma ofM_sqE (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) :
    ofM ν (sqE (H1N.of_H10 hψ)) = ν (sqP hψ) := by
  rw [sqE, ofM_toE ν _ ((H1N.of_H10 hψ).mul (H1N.of_H10 hψ)).continuousOn]
  congr 1; ext t; simp [sq]; rfl

/-- The δ-function at `x ∈ [0, 1]` as an `H⁻¹` potential. -/
noncomputable def deltaH (x : Icc (0 : ℝ) 1) : PotH := ofM (deltaM x)

lemma deltaH_toE (x : Icc (0 : ℝ) 1) {g : ℝ → ℝ} (hg : H1N g) : deltaH x (toE hg) = g x := by
  rw [deltaH, ofM, ContinuousLinearMap.comp_apply, deltaM, ContinuousMap.evalCLM_apply,
    evE_toE hg x]

end DFT.Continuum.Line
