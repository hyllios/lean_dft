/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Regularity.H2Bos

/-!
# A kinked density is not `v`-representable, for any number of particles

Every interacting ground-state density has a `C¹` profile (`gs_dens_C1_stat`). A density whose
profile has a kink, `|K(t₀ + h) - 2K(t₀) + K(t₀ - h)| > h` for all small `h`, therefore is not
`v`-representable. The square of a tent is such a density, and it is `N`-representable since the
tent is Lipschitz and vanishes at the walls.

* `not_C1Dens_of_kink`: a kink rules out a `C¹` profile.
* `tentG = 1 - 2|t - ½|`, `rhoKink`.
* **`kink_nrep_not_vrep`**: `ρ ∝ (1 - 2|t - ½|)²` is `N`-representable but not (ensemble)
  `v`-representable, for `N` bosons or fermions, continuous `v`, continuous relabelling-invariant
  `w`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

/-- **A kink rules out a `C¹` profile.** -/
theorem not_C1Dens_of_kink {f : ℝ → ℝ} (hf : Continuous f) {t0 δ : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 < δ) (hδt : δ ≤ t0) (hδs : δ ≤ 1 - t0)
    (hkink : ∀ h, 0 < h → h ≤ δ → h < |D2 f t0 h|) :
    ¬ C1Dens fun u => ∫ t, ext u t * f t ∂μ1 := by
  rintro ⟨K, K', hK', hK, -, -, hρ⟩
  obtain ⟨k, hk⟩ := D2_le_of_C1 hK' hK
  have hKc : ContinuousOn K (Icc 0 1) := fun t ht => (hK t ht).continuousWithinAt
  set Kc : ℝ → ℝ := fun t => K (projIcc (0 : ℝ) 1 zero_le_one t)
  have hKcc : Continuous Kc :=
    hKc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun t => (projIcc _ _ _ t).2
  have he := eqOn_of_integral_pot (f := Kc) (g := f) hKcc hf fun u => by
    have h1 := congrFun hρ u
    change ∫ t, ext u t * f t ∂μ1 = ∫ t, ext u t * K t ∂μ1 at h1
    rw [show ∫ t in Ioo (0 : ℝ) 1, ext u t * Kc t = ∫ t, ext u t * K t ∂μ1 from
      setIntegral_congr_fun measurableSet_Ioo fun t ht => by
        simp only [Kc, projIcc_of_mem _ (Ioo_subset_Icc_self ht)]]
    exact h1.symm
  have hKf : ∀ t ∈ Ioo (0 : ℝ) 1, K t = f t := fun t ht => by
    have := he ht
    simp only [Kc, projIcc_of_mem _ (Ioo_subset_Icc_self ht)] at this
    exact this
  set h := min δ (1 / ((k : ℝ) + 1)) / 2
  have hm : 0 < min δ (1 / ((k : ℝ) + 1)) := lt_min hδ (by positivity)
  have hh0 : 0 < h := by positivity
  have hhδ : h < δ := by have := min_le_left δ (1 / ((k : ℝ) + 1)); simp only [h]; linarith
  have hhk : h ≤ 1 / ((k : ℝ) + 1) := by
    have := min_le_right δ (1 / ((k : ℝ) + 1)); simp only [h]; linarith
  have m1 : t0 + h ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht0.1], by linarith⟩
  have m3 : t0 - h ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht0.2]⟩
  have hb := hk t0 h hh0.le hhk (by linarith) (by linarith)
  have e : D2 K t0 h = D2 f t0 h := by
    simp only [D2]; rw [hKf _ m1, hKf _ ht0, hKf _ m3]
  rw [e] at hb
  linarith [hkink h hh0 hhδ.le]

/-! ### The tent -/

/-- `1 - 2|t - ½|` on `[0, 1]` (zero outside). -/
noncomputable def tentG (t : ℝ) : ℝ := tentF (1 / 2) (1 / 2) t

lemma lipschitz_tentG : LipschitzWith ⟨1 / (1 / 2), by positivity⟩ tentG :=
  lipschitz_tent (t0 := 1 / 2) (by norm_num)

lemma continuous_tentG : Continuous tentG := lipschitz_tentG.continuous

lemma h10_tentG : H10 tentG := by
  refine ⟨(lipschitz_tentG.lipschitzOnWith).absolutelyContinuousOnInterval, ?_, ?_, ?_⟩
  · exact tent_far (by norm_num) (by norm_num)
  · exact tent_far (by norm_num) (by norm_num)
  · refine Integrable.of_bound ((measurable_deriv tentG).pow_const 2).aestronglyMeasurable
      ((1 / (1 / 2)) ^ 2) (ae_of_all _ fun t => ?_)
    have hd : ‖deriv tentG t‖ ≤ 1 / (1 / 2) := norm_deriv_le_of_lipschitz lipschitz_tentG
    rw [Real.norm_eq_abs] at hd
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2

lemma tentG_side {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1 / 2) :
    tentG (1 / 2 + h) = 1 - 2 * h ∧ tentG (1 / 2 - h) = 1 - 2 * h := by
  obtain ⟨a, b⟩ := tent_side (t0 := 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) h0 h1
  refine ⟨?_, ?_⟩
  · simp only [tentG, a]; ring
  · simp only [tentG, b]; ring

lemma integral_tentG_sq_pos : 0 < ∫ t, tentG t ^ 2 ∂μ1 := by
  have hint : Integrable (fun t => tentG t ^ 2) μ1 :=
    ((continuous_tentG.pow 2).integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  rw [integral_pos_iff_support_of_nonneg (fun t => sq_nonneg _) hint]
  have hsub : Ioo (1 / 4 : ℝ) (3 / 4) ⊆ Function.support fun t => tentG t ^ 2 := by
    intro t ht
    have hpos : 0 < tentG t := by
      simp only [tentG, tentF]
      refine lt_max_of_lt_right ?_
      have : |t - 1 / 2| < 1 / 4 := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
      have : |t - 1 / 2| / (1 / 2) < 1 / 2 := by rw [div_lt_iff₀ (by norm_num)]; linarith
      linarith
    exact (pow_pos hpos 2).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioo]
  norm_num

lemma integral_tentG_sq_le : ∫ t, tentG t ^ 2 ∂μ1 ≤ 1 := by
  have h : ∀ t, tentG t ^ 2 ≤ 1 := fun t => by
    have h0 := tentF_nonneg (1 / 2) (1 / 2) t
    have h1 := tentF_le_one (t0 := 1 / 2) (t := t) (by norm_num : (0 : ℝ) < 1 / 2)
    simp only [tentG]; nlinarith
  calc ∫ t, tentG t ^ 2 ∂μ1 ≤ ∫ _t, (1 : ℝ) ∂μ1 :=
        integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) (integrable_const _)
          (ae_of_all _ h)
    _ = 1 := by simp

/-- `c` with `∫ (c tentG)² = N`. -/
noncomputable def cKink (n : ℕ) : ℝ := √((n + 1) / ∫ t, tentG t ^ 2 ∂μ1)

/-- The kinked density `ρ = (c tentG)²`. -/
noncomputable def rhoKink (n : ℕ) (v : Pot) : ℝ := ∫ t, ext v t * (cKink n * tentG t) ^ 2 ∂μ1

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-- **A kinked density is `N`-representable but not `v`-representable**, for any number of bosons
or fermions, continuous `v` and continuous relabelling-invariant `w`. -/
theorem kink_nrep_not_vrep (hws : ∀ σ x, w (pm σ x) = w x) :
    (∃ ψ ∈ Nst (settingW τ n w hw), dens (settingW τ n w hw) ψ = rhoKink n) ∧
      ¬ EnsVRep (settingW τ n w hw) (rhoKink n) := by
  have hI := integral_tentG_sq_pos
  have hI1 := integral_tentG_sq_le
  have hN : (0 : ℝ) ≤ (n + 1) / ∫ t, tentG t ^ 2 ∂μ1 := by positivity
  have hc2 : cKink n ^ 2 = (n + 1) / ∫ t, tentG t ^ 2 ∂μ1 := Real.sq_sqrt hN
  have hc1 : 1 ≤ cKink n ^ 2 := by
    rw [hc2, le_div_iff₀ hI]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  refine ⟨(lieb_characterisation (rhoKink n)).2 ⟨fun t => cKink n * tentG t,
    h10_tentG.const_mul _, ?_, rfl⟩, ?_⟩
  · simp only [mul_pow]
    rw [integral_const_mul, hc2, div_mul_cancel₀ _ hI.ne']
  · intro h
    obtain ⟨v, ψ, hψ, -, hd⟩ := (ensVRep_iff_W_cont _).1 h
    have hC1 := gs_dens_C1_stat hws hψ
    rw [hd] at hC1
    refine not_C1Dens_of_kink (f := fun t => (cKink n * tentG t) ^ 2)
      ((continuous_const.mul continuous_tentG).pow 2) (t0 := 1 / 2) (δ := 1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun h h0 hδ => ?_) hC1
    obtain ⟨a, b⟩ := tentG_side h0.le (by linarith)
    have c0 : tentG (1 / 2) = 1 := tent_center _ _
    simp only [D2]
    rw [a, b, c0]
    have e : (cKink n * (1 - 2 * h)) ^ 2 - 2 * (cKink n * 1) ^ 2 + (cKink n * (1 - 2 * h)) ^ 2 =
        -(cKink n ^ 2 * (8 * h * (1 - h))) := by ring
    have h8 : 0 ≤ 8 * h * (1 - h) := mul_nonneg (by positivity) (by linarith)
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (by positivity) h8)]
    have h1 : 6 * h ≤ 8 * h * (1 - h) := by nlinarith only [h0, hδ]
    have h2 : 1 * (8 * h * (1 - h)) ≤ cKink n ^ 2 * (8 * h * (1 - h)) :=
      mul_le_mul_of_nonneg_right hc1 h8
    linarith

end DFT.Continuum.Line
