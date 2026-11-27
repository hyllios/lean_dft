/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.MeasureTheory.Integral.Pi
import DFT.Continuum.Sine.OneD

/-!
# The sine basis of the cube

On the cube `(0, 1)^d`, with the product measure `piM d`, the products
`s_m(x) = Π_j √2 sin(π (m_j + 1) x_j)` are orthonormal, and Parseval holds for continuous functions:
`Σ_m ⟨s_m, f⟩² = ∫ f²`. The proof is an induction on `d`: split off the first coordinate (Fubini),
apply the induction hypothesis to each slice, exchange the sum and the integral (Tonelli in
`ℝ≥0∞`) and use one-dimensional Parseval for each coefficient function.

* `piM`, `smd`, `piM_eq_Icc`, `integrable_piM`.
* `smd_orthonormal`: orthonormality.
* `parseval`: **Parseval** for continuous functions, in `ℝ≥0∞`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology SturmLiouville

/-- The product of `d` copies of Lebesgue measure on `(0, 1)`. -/
noncomputable abbrev piM (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ => μ1

/-- The product sine `Π_j √2 sin(π (m_j + 1) x_j)`. -/
noncomputable def smd {d : ℕ} (m : Fin d → ℕ) (x : Fin d → ℝ) : ℝ := ∏ j, sn (m j + 1) (x j)

lemma continuous_smd {d : ℕ} (m : Fin d → ℕ) : Continuous (smd m) :=
  continuous_finsetProd _ fun j _ => (continuous_sn _).comp (continuous_apply j)

lemma mu1_eq_Icc : μ1 = volume.restrict (Icc (0 : ℝ) 1) := Measure.restrict_congr_set Ioo_ae_eq_Icc

lemma piM_eq_Icc (d : ℕ) : piM d = volume.restrict (univ.pi fun _ : Fin d => Icc (0 : ℝ) 1) := by
  rw [volume_pi, Measure.restrict_pi_pi, piM, mu1_eq_Icc]

lemma isCompact_cubeIcc (d : ℕ) : IsCompact (univ.pi fun _ : Fin d => Icc (0 : ℝ) 1) :=
  isCompact_univ_pi fun _ => isCompact_Icc

lemma integrable_piM {d : ℕ} {F : (Fin d → ℝ) → ℝ} (hF : Continuous F) : Integrable F (piM d) := by
  rw [piM_eq_Icc]
  exact hF.continuousOn.integrableOn_compact (isCompact_cubeIcc d)

/-- A parametric integral over the cube is continuous. -/
lemma continuous_param {d : ℕ} {G : ℝ → (Fin d → ℝ) → ℝ} (hG : Continuous (Function.uncurry G)) :
    Continuous fun t => ∫ y, G t y ∂piM d := by
  rw [piM_eq_Icc]
  exact continuous_parametric_integral_of_continuous hG (isCompact_cubeIcc d)

/-- **Orthonormality.** -/
lemma smd_orthonormal {d : ℕ} (m m' : Fin d → ℕ) :
    ∫ x, smd m x * smd m' x ∂piM d = if m = m' then 1 else 0 := by
  have e : (fun x => smd m x * smd m' x) =
      fun x => ∏ j, (sn (m j + 1) (x j) * sn (m' j + 1) (x j)) := by
    funext x; simp only [smd, Finset.prod_mul_distrib]
  rw [e, integral_fintype_prod_eq_prod (f := fun j t => sn (m j + 1) t * sn (m' j + 1) t)]
  simp only [sn_orthonormal (Nat.succ_pos _) (Nat.succ_pos _)]
  by_cases h : m = m'
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right fun h => hj (Nat.succ_injective h))

/-! ### Parseval -/

lemma smd_cons {d : ℕ} (k : ℕ) (m : Fin d → ℕ) (t : ℝ) (y : Fin d → ℝ) :
    smd (Fin.cons k m : Fin (d + 1) → ℕ) (Fin.cons t y) = sn (k + 1) t * smd m y := by
  simp only [smd, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **Parseval** for continuous functions on the cube: `Σ_m ⟨s_m, f⟩² = ∫ f²`. -/
theorem parseval : ∀ (d : ℕ) {f : (Fin d → ℝ) → ℝ}, Continuous f →
    ∑' m : Fin d → ℕ, ENNReal.ofReal ((∫ x, smd m x * f x ∂piM d) ^ 2) =
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂piM d := by
  intro d
  induction d with
  | zero =>
    intro f _
    have hpi : piM 0 = Measure.dirac (isEmptyElim : Fin 0 → ℝ) := Measure.pi_of_empty _ _
    rw [hpi, tsum_fintype, Finset.univ_unique, Finset.sum_singleton, lintegral_dirac,
      integral_dirac]
    simp [smd]
  | succ d ih =>
    intro f hf
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hmp : MeasurePreserving e (piM (d + 1)) (μ1.prod (piM d)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ1) 0
    have hsymm : ∀ p : ℝ × (Fin d → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    set F : ℝ → (Fin d → ℝ) → ℝ := fun t y => f (Fin.cons t y)
    have hFc : Continuous (Function.uncurry F) :=
      hf.comp (Continuous.finCons (A := fun _ : Fin (d + 1) => ℝ) continuous_fst continuous_snd)
    have hFt : ∀ t, Continuous (F t) := fun t => hFc.comp (continuous_const.prodMk continuous_id)
    -- the coefficient functions
    set a : (Fin d → ℕ) → ℝ → ℝ := fun m t => ∫ y, smd m y * F t y ∂piM d
    have ha : ∀ m, Continuous (a m) := fun m =>
      continuous_param (G := fun t y => smd m y * F t y)
        (((continuous_smd m).comp continuous_snd).mul hFc)
    -- integrals over the cube as iterated integrals
    have hint : ∀ G : (Fin (d + 1) → ℝ) → ℝ, Continuous G →
        ∫ x, G x ∂piM (d + 1) = ∫ t, ∫ y, G (Fin.cons t y) ∂piM d ∂μ1 := by
      intro G hG
      rw [← hmp.symm.integral_comp' (f := e.symm) (g := G)]
      have hi : Integrable (fun p : ℝ × (Fin d → ℝ) => G (e.symm p)) (μ1.prod (piM d)) :=
        (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 (integrable_piM hG)
      rw [integral_prod _ hi]
      simp only [hsymm]
    have hlint : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂piM (d + 1) =
        ∫⁻ t, ∫⁻ y, ENNReal.ofReal (F t y ^ 2) ∂piM d ∂μ1 := by
      rw [← hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding, lintegral_prod]
      · simp only [hsymm, F]
      · exact ((hf.measurable.comp e.symm.measurable).pow_const 2).ennreal_ofReal.aemeasurable
    rw [hlint]
    have hslice : ∀ t, ∫⁻ y, ENNReal.ofReal (F t y ^ 2) ∂piM d =
        ∑' m, ENNReal.ofReal ((a m t) ^ 2) := fun t => (ih (hFt t)).symm
    simp only [hslice]
    rw [lintegral_tsum (f := fun m t => ENNReal.ofReal (a m t ^ 2))
      fun m => ((ha m).measurable.pow_const 2).ennreal_ofReal.aemeasurable]
    have h1 : ∀ m, ∫⁻ t, ENNReal.ofReal ((a m t) ^ 2) ∂μ1 =
        ∑' k, ENNReal.ofReal ((∫ t, sn (k + 1) t * a m t ∂μ1) ^ 2) := fun m =>
      (parseval1 (ha m)).symm
    simp only [h1]
    -- reassemble the double sum
    have hcoef : ∀ k m, ∫ t, sn (k + 1) t * a m t ∂μ1 =
        ∫ x, smd (Fin.cons k m : Fin (d + 1) → ℕ) x * f x ∂piM (d + 1) := by
      intro k m
      rw [hint (fun x => smd (Fin.cons k m : Fin (d + 1) → ℕ) x * f x)
        ((continuous_smd _).mul hf)]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [a, smd_cons, ← integral_const_mul, F, mul_assoc]
    simp only [hcoef]
    set g : (Fin (d + 1) → ℕ) → ENNReal :=
      fun m => ENNReal.ofReal ((∫ x, smd m x * f x ∂piM (d + 1)) ^ 2)
    rw [tsum_comm, ← tsum_prod' (f := fun p : ℕ × (Fin d → ℕ) =>
      g (Fin.cons p.1 p.2))]
    exact ((Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)).tsum_eq g).symm

/-- The coefficient `⟨s_m, f⟩`. -/
noncomputable def cf {d : ℕ} (m : Fin d → ℕ) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, smd m x * f x ∂piM d

/-- **Parseval**, real form: `Σ_m ⟨s_m, f⟩² = ∫ f²`. -/
theorem hasSum_sq_cube {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    HasSum (fun m => cf m f ^ 2) (∫ x, f x * f x ∂piM d) := by
  have hP := parseval d hf
  have hI : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂piM d = ENNReal.ofReal (∫ x, f x * f x ∂piM d) := by
    rw [ofReal_integral_eq_lintegral_ofReal (f := fun x => f x * f x)
      (integrable_piM (hf.mul hf)) (ae_of_all _ fun x => mul_self_nonneg _)]
    simp only [sq]
  rw [hI] at hP
  have hne : ∑' m, ENNReal.ofReal (cf m f ^ 2) ≠ ⊤ := by
    simp only [cf]; rw [hP]; exact ENNReal.ofReal_ne_top
  have hs := ENNReal.summable_toReal hne
  have e : ∀ m, (ENNReal.ofReal (cf m f ^ 2)).toReal = cf m f ^ 2 := fun m =>
    ENNReal.toReal_ofReal (sq_nonneg _)
  simp only [e] at hs
  convert hs.hasSum using 1
  rw [← ENNReal.toReal_ofReal (integral_nonneg fun x => mul_self_nonneg (f x)), ← hP,
    ENNReal.tsum_toReal_eq fun m => ENNReal.ofReal_ne_top]
  congr 1; funext m; exact ENNReal.toReal_ofReal (sq_nonneg _)

lemma cf_add {d : ℕ} (m : Fin d → ℕ) {f g : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) : cf m (fun x => f x + g x) = cf m f + cf m g := by
  simp only [cf, mul_add]
  exact integral_add (integrable_piM ((continuous_smd m).mul hf))
    (integrable_piM ((continuous_smd m).mul hg))

lemma cf_sub {d : ℕ} (m : Fin d → ℕ) {f g : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) : cf m (fun x => f x - g x) = cf m f - cf m g := by
  simp only [cf, mul_sub]
  exact integral_sub (integrable_piM ((continuous_smd m).mul hf))
    (integrable_piM ((continuous_smd m).mul hg))

/-- **Parseval for pairs**: `Σ_m ⟨s_m, f⟩ ⟨s_m, g⟩ = ∫ f g`. -/
theorem hasSum_pair_cube {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) : HasSum (fun m => cf m f * cf m g) (∫ x, f x * g x ∂piM d) := by
  have h1 := hasSum_sq_cube (f := fun x => f x + g x) (hf.add hg)
  have h2 := hasSum_sq_cube (f := fun x => f x - g x) (hf.sub hg)
  have h := (h1.sub h2).div_const 4
  convert h using 1
  · funext m
    rw [cf_add m hf hg, cf_sub m hf hg]; ring
  · rw [← integral_sub (f := fun x => (f x + g x) * (f x + g x))
      (g := fun x => (f x - g x) * (f x - g x)) (integrable_piM ((hf.add hg).mul (hf.add hg)))
      (integrable_piM ((hf.sub hg).mul (hf.sub hg))), ← integral_div]
    congr 1; funext x; ring

end DFT.Continuum.Sine
