/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NotVRepDense

/-!
# The space of `N`-representable densities as a complete metric space

On a line, `ρ` is `N`-representable iff `ρ = g²` with `g ∈ H¹₀(0, 1)`, `∫ g² = N`
(`lieb_characterisation`). We parametrise `g` by its derivative `f = g' ∈ L²(0, 1)`:
`g(t) = ∫₀ᵗ f`, with `∫₀¹ f = 0` and `∫ g² = N`. These conditions are closed, so

  `SN n = {f ∈ L²(0, 1) | ∫₀¹ f = 0, ∫ (∫₀ᵗ f)² = N}`

is a complete metric space, and `f ↦ ρ_f = (∫₀ᵗ f)²` maps it onto the `N`-representable densities.

* `L2I`, `prim f t = ∫₀ᵗ f`; `abs_prim_sub_le`: `|prim f t - prim f' t| ≤ ‖f - f'‖`.
* `h10_prim`: `prim f ∈ H¹₀` when `∫₀¹ f = 0`.
* `SN`, `isClosed_SN`: the parameter space, closed in `L²`.
* `rhoF`; **`nrep_iff_SN`**: `ρ` is `N`-representable iff `ρ = ρ_f` for some `f ∈ SN n`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

/-- `L²(0, 1)`. -/
abbrev L2I : Type := Lp ℝ 2 μ1

/-- The primitive `∫₀ᵗ f`. -/
noncomputable def prim (f : L2I) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, (f : ℝ → ℝ) s

section basic

lemma integrable_L2I (f : L2I) : Integrable (f : ℝ → ℝ) μ1 := (Lp.memLp f).integrable one_le_two

lemma intervalIntegrable_of_mu1 {h : ℝ → ℝ} (hh : Integrable h μ1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : IntervalIntegrable h volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).2
    ((show IntegrableOn h (Ioo (0 : ℝ) 1) volume from hh).mono_set (Ioo_subset_Ioo_right ht.2))

lemma ae_ne_one : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
  rw [ae_iff]; simp

/-- `μ1`-a.e. equal functions have the same primitive on `[0, 1]`. -/
lemma integral_congr_mu1 {h k : ℝ → ℝ} (hhk : h =ᵐ[μ1] k) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..t, h s = ∫ s in (0 : ℝ)..t, k s := by
  refine intervalIntegral.integral_congr_ae ?_
  have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hhk
  filter_upwards [h1, ae_ne_one] with x hx hx1 hxI
  rw [uIoc_of_le ht.1] at hxI
  exact hx ⟨hxI.1, lt_of_le_of_ne (hxI.2.trans ht.2) hx1⟩

lemma abs_integral_le_mu1 {h : ℝ → ℝ} (hh : Integrable h μ1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |∫ s in (0 : ℝ)..t, h s| ≤ ∫ s, |h s| ∂μ1 := by
  rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
  calc |∫ x in Ioo (0 : ℝ) t, h x| = ‖∫ x in Ioo (0 : ℝ) t, h x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in Ioo (0 : ℝ) t, ‖h x‖ := norm_integral_le_integral_norm _
    _ = ∫ x in Ioo (0 : ℝ) t, |h x| := by simp_rw [Real.norm_eq_abs]
    _ ≤ ∫ s, |h s| ∂μ1 := setIntegral_mono_set
        (show IntegrableOn (fun x => |h x|) (Ioo (0 : ℝ) 1) volume from hh.abs)
        (ae_of_all _ fun x => abs_nonneg _) (LE.le.eventuallySubset (Ioo_subset_Ioo_right ht.2))

lemma norm_sq_L2I (f : L2I) : ‖f‖ ^ 2 = ∫ t, (f : ℝ → ℝ) t ^ 2 ∂μ1 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun x => by simp [sq])

lemma integrable_sq_L2I (f : L2I) : Integrable (fun t => (f : ℝ → ℝ) t ^ 2) μ1 :=
  (memLp_two_iff_integrable_sq (Lp.memLp f).aestronglyMeasurable).1 (Lp.memLp f)

/-- `∫ |f| ≤ ‖f‖₂` on the probability space `(0, 1)`. -/
lemma integral_abs_le_norm (f : L2I) : ∫ t, |(f : ℝ → ℝ) t| ∂μ1 ≤ ‖f‖ := by
  set m := ∫ t, |(f : ℝ → ℝ) t| ∂μ1
  have hf := integrable_L2I f
  have hsq := integrable_sq_L2I f
  have h0 : 0 ≤ ∫ t, (|(f : ℝ → ℝ) t| - m) ^ 2 ∂μ1 := integral_nonneg fun t => sq_nonneg _
  have e : ∫ t, (|(f : ℝ → ℝ) t| - m) ^ 2 ∂μ1 = ∫ t, (f : ℝ → ℝ) t ^ 2 ∂μ1 - m ^ 2 := by
    have i1 : Integrable (fun t => (f : ℝ → ℝ) t ^ 2 - 2 * m * |(f : ℝ → ℝ) t|) μ1 :=
      hsq.sub (hf.abs.const_mul (2 * m))
    have : (fun t => (|(f : ℝ → ℝ) t| - m) ^ 2) =
        fun t => ((f : ℝ → ℝ) t ^ 2 - 2 * m * |(f : ℝ → ℝ) t|) + m ^ 2 := by
      funext t; rw [sub_sq, sq_abs]; ring
    rw [this, integral_add i1 (integrable_const _),
      integral_sub hsq (hf.abs.const_mul (2 * m)), integral_const_mul]
    simp; ring
  have hm0 : 0 ≤ m := integral_nonneg fun t => abs_nonneg _
  rw [e, ← norm_sq_L2I] at h0
  nlinarith [norm_nonneg f]

end basic

section prim

lemma prim_zero (f : L2I) : prim f 0 = 0 := by simp [prim]

lemma prim_add (f f' : L2I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    prim (f + f') t = prim f t + prim f' t := by
  rw [prim, integral_congr_mu1 (Lp.coeFn_add f f') ht, Pi.add_def,
    intervalIntegral.integral_add (intervalIntegrable_of_mu1 (integrable_L2I f) ht)
      (intervalIntegrable_of_mu1 (integrable_L2I f') ht)]
  rfl

lemma prim_smul (c : ℝ) (f : L2I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    prim (c • f) t = c * prim f t := by
  rw [prim, integral_congr_mu1 (Lp.coeFn_smul c f) ht]
  simp only [Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
  rfl

lemma prim_sub (f f' : L2I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    prim (f - f') t = prim f t - prim f' t := by
  rw [prim, integral_congr_mu1 (Lp.coeFn_sub f f') ht, Pi.sub_def,
    intervalIntegral.integral_sub (intervalIntegrable_of_mu1 (integrable_L2I f) ht)
      (intervalIntegrable_of_mu1 (integrable_L2I f') ht)]
  rfl

lemma abs_prim_le (f : L2I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |prim f t| ≤ ‖f‖ :=
  (abs_integral_le_mu1 (integrable_L2I f) ht).trans (integral_abs_le_norm f)

lemma abs_prim_sub_le (f f' : L2I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |prim f t - prim f' t| ≤ ‖f - f'‖ := by
  rw [← prim_sub f f' ht]; exact abs_prim_le _ ht

lemma ac_prim (f : L2I) : AbsolutelyContinuousOnInterval (prim f) 0 1 :=
  IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (intervalIntegrable_of_mu1 (integrable_L2I f) ⟨zero_le_one, le_rfl⟩) (by simp)

lemma continuousOn_prim (f : L2I) : ContinuousOn (prim f) (Icc 0 1) := by
  simpa [uIcc01] using (ac_prim f).continuousOn

lemma integrable_prim_sq (f : L2I) : Integrable (fun t => prim f t ^ 2) μ1 :=
  H10.int_sq_of_contOn (continuousOn_prim f)

/-- `prim f ∈ H¹₀` when `∫₀¹ f = 0`. -/
theorem h10_prim {f : L2I} (h1 : prim f 1 = 0) : H10 (prim f) := by
  refine ⟨ac_prim f, prim_zero f, h1, ?_⟩
  have hd := (intervalIntegrable_of_mu1 (integrable_L2I f)
    ⟨zero_le_one, le_rfl⟩).ae_hasDerivAt_integral
  refine (integrable_sq_L2I f).congr ?_
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t h ht
  have := (h (by rw [uIcc01]; exact Ioo_subset_Icc_self ht) 0 (by simp)).deriv
  change (f : ℝ → ℝ) t ^ 2 = deriv (prim f) t ^ 2
  rw [show prim f = fun x => ∫ s in (0 : ℝ)..x, (f : ℝ → ℝ) s from rfl, this]

end prim

/-! ### The parameter space -/

/-- `f ∈ L²(0, 1)` with `∫₀¹ f = 0` and `∫ (∫₀ᵗ f)² = N`. -/
def SN (n : ℕ) : Set L2I := {f | prim f 1 = 0 ∧ ∫ t, prim f t ^ 2 ∂μ1 = n + 1}

lemma continuous_prim_one : Continuous fun f : L2I => prim f 1 :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun f f' => by
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact abs_prim_sub_le f f' ⟨zero_le_one, le_rfl⟩).continuous

lemma continuous_int_prim_sq : Continuous fun f : L2I => ∫ t, prim f t ^ 2 ∂μ1 := by
  rw [Metric.continuous_iff]
  intro f ε hε
  set M := 2 * ‖f‖ + 1
  have hM : 0 < M := by positivity
  refine ⟨min 1 (ε / (2 * M)), lt_min one_pos (by positivity), fun f' hf' => ?_⟩
  rw [dist_eq_norm] at hf'
  have h1 : ‖f' - f‖ < 1 := lt_of_lt_of_le hf' (min_le_left _ _)
  have h2 : ‖f' - f‖ < ε / (2 * M) := lt_of_lt_of_le hf' (min_le_right _ _)
  have hf'n : ‖f'‖ ≤ ‖f‖ + 1 := by
    have := norm_sub_norm_le f' f
    linarith
  rw [Real.dist_eq, ← integral_sub (integrable_prim_sq f') (integrable_prim_sq f)]
  calc |∫ t, (prim f' t ^ 2 - prim f t ^ 2) ∂μ1|
      ≤ ∫ t, ‖f' - f‖ * M ∂μ1 := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (integrable_const _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have hti : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
        have a1 := abs_prim_sub_le f' f hti
        have a2 := abs_prim_le f' hti
        have a3 := abs_prim_le f hti
        rw [Real.norm_eq_abs, show prim f' t ^ 2 - prim f t ^ 2 =
          (prim f' t - prim f t) * (prim f' t + prim f t) by ring, abs_mul]
        refine mul_le_mul a1 ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
          (norm_nonneg _)
    _ = ‖f' - f‖ * M := by simp
    _ < ε := by
        have := mul_lt_mul_of_pos_right h2 hM
        have e : ε / (2 * M) * M = ε / 2 := by field_simp
        linarith

theorem isClosed_SN (n : ℕ) : IsClosed (SN n) :=
  (isClosed_eq continuous_prim_one continuous_const).inter
    (isClosed_eq continuous_int_prim_sq continuous_const)

/-- The density of `f ∈ SN n`: `u ↦ ∫ u (∫₀ᵗ f)²`. -/
noncomputable def rhoF (f : L2I) (u : Pot) : ℝ := ∫ t, ext u t * prim f t ^ 2 ∂μ1

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-- **`SN n` parametrises the `N`-representable densities**: `ρ` is the density of a normalised
`H¹₀` state iff `ρ = ρ_f` for some `f ∈ SN n`. -/
theorem nrep_iff_SN (ρ : Pot → ℝ) :
    (∃ ψ ∈ Nst (settingW τ n w hw), dens (settingW τ n w hw) ψ = ρ) ↔
      ∃ f ∈ SN n, ρ = rhoF f := by
  rw [lieb_characterisation]
  constructor
  · rintro ⟨g, hg, hgN, rfl⟩
    have hd2 : MemLp (deriv g) 2 μ1 :=
      (memLp_two_iff_integrable_sq (measurable_deriv g).aestronglyMeasurable).2 hg.2.2.2
    set f : L2I := hd2.toLp (deriv g)
    have hpf : ∀ t ∈ Icc (0 : ℝ) 1, prim f t = g t := fun t ht => by
      have hac : AbsolutelyContinuousOnInterval g 0 t :=
        hg.1.mono (by rw [uIcc01, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
      rw [prim, integral_congr_mu1 (MemLp.coeFn_toLp hd2) ht, hac.integral_deriv_eq_sub,
        hg.2.1, sub_zero]
    have hint : ∀ F : ℝ → ℝ → ℝ, ∫ t, F t (prim f t) ∂μ1 = ∫ t, F t (g t) ∂μ1 := fun F =>
      setIntegral_congr_fun measurableSet_Ioo fun t ht => by
        rw [hpf t (Ioo_subset_Icc_self ht)]
    refine ⟨f, ⟨by rw [hpf 1 ⟨zero_le_one, le_rfl⟩, hg.2.2.1], ?_⟩, ?_⟩
    · rw [hint fun _ x => x ^ 2, hgN]
    · funext u; exact (hint fun t x => ext u t * x ^ 2).symm
  · rintro ⟨f, ⟨h1, hN⟩, rfl⟩
    exact ⟨prim f, h10_prim h1, hN, rfl⟩

end DFT.Continuum.Line
