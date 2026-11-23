/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.LogEst

/-!
# Translations of weakly differentiable functions

If `H` is the weak `k`-th derivative of `F` on `ℝᴺ` (tested against smooth compactly supported
functions), then for every `t ≥ 0`

`F(x + t eₖ) - F(x) = ∫₀ᵗ H(x + s eₖ) ds`   for a.e. `x`   (`translate_identity`).

Proof by duality: pair both sides with a test function `g`, move the translation onto `g`, write
`g(y - t eₖ) - g(y) = -∫₀ᵗ ∂ₖg(y - s eₖ) ds`, swap the integrals (Fubini), and use the weak
derivative with the translated test functions `g(· - s eₖ)`; conclude with the fundamental lemma.

This replaces mollification in the positivity argument: with Cauchy–Schwarz it bounds the
translation differences of `F` by the local `L²` norm of `H`.

* `ek`: the unit vector `eₖ`.
* `hasDerivAt_translate`: `d/ds g(y - s eₖ) = -∂ₖg(y - s eₖ)`.
* **`translate_identity`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology
open scoped ContDiff

variable {n : ℕ}

/-- The unit vector in direction `k`. -/
def ek (k : Fin (n + 1)) : Cfg n := Pi.single k 1

lemma hasDerivAt_translate {g : Cfg n → ℝ} (hg : Differentiable ℝ g) (k : Fin (n + 1)) (y : Cfg n)
    (s : ℝ) : HasDerivAt (fun s => g (y - s • ek k)) (-dk k g (y - s • ek k)) s := by
  have hin : HasDerivAt (fun s : ℝ => y - s • ek k) (-(ek k)) s := by
    simpa using ((hasDerivAt_id s).smul_const (ek k)).const_sub y
  have h := (hg (y - s • ek k)).hasFDerivAt.comp_hasDerivAt s hin
  simpa [dk, ek, Function.comp_def] using h

lemma dk_translate {g : Cfg n → ℝ} (k : Fin (n + 1)) (c y : Cfg n) :
    dk k (fun y => g (y - c)) y = dk k g (y - c) := by
  simp only [dk, fderiv_comp_sub]

/-- **The translation identity** for weak derivatives on `ℝᴺ`. -/
theorem translate_identity {F H : Cfg n → ℝ} (hFm : StronglyMeasurable F)
    (hHm : StronglyMeasurable H) (hF : Integrable F) (hH : Integrable H) {k : Fin (n + 1)}
    (hw : ∀ g : Cfg n → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, F x * dk k g x = -∫ x, H x * g x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x, F (x + t • ek k) - F x = ∫ s in Ioc 0 t, H (x + s • ek k) := by
  set e := ek (n := n) k
  set ν : Measure ℝ := volume.restrict (Ioc 0 t)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by simp)
  -- joint integrability of `(s, x) ↦ H (x + s e)`
  have hHjm : StronglyMeasurable (fun p : ℝ × Cfg n => H (p.2 + p.1 • e)) :=
    hHm.comp_measurable (measurable_snd.add (measurable_fst.smul_const e))
  have hHj : Integrable (fun p : ℝ × Cfg n => H (p.2 + p.1 • e)) (ν.prod volume) := by
    refine (integrable_prod_iff hHjm.aestronglyMeasurable).2 ⟨ae_of_all _ fun s =>
      hH.comp_add_right (s • e), ?_⟩
    have : (fun s : ℝ => ∫ x, ‖H (x + s • e)‖) = fun _ => ∫ x, ‖H x‖ := funext fun s =>
      integral_add_right_eq_self (fun x => ‖H x‖) (s • e)
    simp only [this]
    exact integrable_const _
  have hint : Integrable (fun x => ∫ s in Ioc 0 t, H (x + s • e)) := by
    have := (integrable_prod_iff' hHjm.aestronglyMeasurable).1 hHj
    exact hHj.integral_prod_right
  -- the difference is a.e. zero
  have hD : ∀ᵐ x, (F (x + t • e) - F x - ∫ s in Ioc 0 t, H (x + s • e)) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((hF.comp_add_right (t • e)).sub hF).sub hint).locallyIntegrable fun g hg hgs => ?_
    obtain ⟨M, hM⟩ := hgs.exists_bound_of_continuous hg.continuous
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
    have hdg := continuous_dk_of_C1 hg1 k
    obtain ⟨M', hM'⟩ := (hgs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      ((hg.continuous_fderiv (by simp)))
    have hdgb : ∀ y, |dk k g y| ≤ M' := fun y => by
      have := (fderiv ℝ g y).le_opNorm (Pi.single k 1)
      rw [Pi.norm_single, norm_one, mul_one] at this
      exact (Real.norm_eq_abs _ ▸ this).trans (hM' y)
    have hgb : ∀ y, |g y| ≤ M := fun y => Real.norm_eq_abs _ ▸ hM y
    -- integrability of the pieces
    have i1 : Integrable (fun x => g x * F (x + t • e)) :=
      (hF.comp_add_right (t • e)).bdd_mul hg.continuous.aestronglyMeasurable
        (ae_of_all _ fun x => (hM x))
    have i2 : Integrable (fun x => g x * F x) :=
      hF.bdd_mul hg.continuous.aestronglyMeasurable (ae_of_all _ fun x => hM x)
    have i3 : Integrable (fun x => g x * ∫ s in Ioc 0 t, H (x + s • e)) :=
      hint.bdd_mul hg.continuous.aestronglyMeasurable (ae_of_all _ fun x => hM x)
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub (f := fun x => g x * F (x + t • e) - g x * F x)
      (g := fun x => g x * ∫ s in Ioc 0 t, H (x + s • e)) (i1.sub i2) i3,
      integral_sub (f := fun x => g x * F (x + t • e)) (g := fun x => g x * F x) i1 i2]
    -- first term: move the translation onto `g`
    have T1 : ∫ x, g x * F (x + t • e) = ∫ y, g (y - t • e) * F y := by
      rw [← integral_add_right_eq_self (fun y => g (y - t • e) * F y) (t • e)]
      simp
    -- third term: Fubini, translation, weak derivative, Fubini, FTC
    have hgs' : ∀ s : ℝ, ContDiff ℝ ∞ (fun y => g (y - s • e)) ∧
        HasCompactSupport (fun y => g (y - s • e)) := fun s =>
      ⟨hg.comp (contDiff_id.sub contDiff_const),
        hgs.comp_homeomorph (Homeomorph.subRight (s • e))⟩
    have hJ1 : Integrable (fun p : ℝ × Cfg n => g p.2 * H (p.2 + p.1 • e)) (ν.prod volume) :=
      hHj.bdd_mul (hg.continuous.comp continuous_snd).aestronglyMeasurable
        (ae_of_all _ fun p => hM p.2)
    have hFjm : AEStronglyMeasurable (fun p : ℝ × Cfg n => F p.2 * dk k g (p.2 - p.1 • e))
        (ν.prod volume) :=
      (hFm.comp_measurable measurable_snd).aestronglyMeasurable.mul
        (hdg.comp (continuous_snd.sub (continuous_fst.smul continuous_const))).aestronglyMeasurable
    have hJ2 : Integrable (fun p : ℝ × Cfg n => F p.2 * dk k g (p.2 - p.1 • e))
        (ν.prod volume) := by
      refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod (hF.norm.mul_const M')) hFjm
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, one_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hdgb _) (abs_nonneg _)
    have T3 : ∫ x, g x * ∫ s in Ioc 0 t, H (x + s • e) =
        ∫ y, F y * (g (y - t • e) - g y) := by
      calc ∫ x, g x * ∫ s in Ioc 0 t, H (x + s • e)
          = ∫ x, ∫ s in Ioc 0 t, g x * H (x + s • e) := by
            congr 1; funext x; rw [integral_const_mul]
        _ = ∫ s in Ioc 0 t, ∫ x, g x * H (x + s • e) := by
            exact integral_integral_swap (f := fun x s => g x * H (x + s • e)) hJ1.swap
        _ = ∫ s in Ioc 0 t, ∫ y, g (y - s • e) * H y := by
            congr 1; funext s
            rw [← integral_add_right_eq_self (fun y => g (y - s • e) * H y) (s • e)]
            simp
        _ = ∫ s in Ioc 0 t, -∫ y, F y * dk k g (y - s • e) := by
            congr 1; funext s
            have h := hw _ (hgs' s).1 (hgs' s).2
            simp only [dk_translate] at h
            rw [h, neg_neg]
            exact integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
        _ = -∫ y, ∫ s in Ioc 0 t, F y * dk k g (y - s • e) := by
            rw [integral_neg, integral_integral_swap (f := fun s y => F y * dk k g (y - s • e))
              hJ2]
        _ = ∫ y, F y * (g (y - t • e) - g y) := by
            rw [← integral_neg]
            congr 1; funext y
            rw [integral_const_mul, ← intervalIntegral.integral_of_le ht]
            have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
              (f := fun s => g (y - s • e)) (f' := fun s => -dk k g (y - s • e))
              (fun s _ => hasDerivAt_translate (hg.differentiable (by simp)) k y s)
              ((hdg.comp (continuous_const.sub (continuous_id.smul continuous_const))).neg
                |>.intervalIntegrable 0 t)
            rw [intervalIntegral.integral_neg] at hftc
            simp only [zero_smul, sub_zero] at hftc
            rw [show (∫ s in (0 : ℝ)..t, dk k g (y - s • e)) = g y - g (y - t • e) by linarith]
            ring
    have i1' : Integrable (fun y => g (y - t • e) * F y) := by
      simpa [mul_comm] using hF.bdd_mul (hg.continuous.comp (continuous_id.sub
        continuous_const)).aestronglyMeasurable (ae_of_all _ fun y => hM (y - t • e))
    have hlast : ∫ y, F y * (g (y - t • e) - g y) =
        (∫ y, g (y - t • e) * F y) - ∫ y, g y * F y := by
      have h := integral_sub i1' i2
      rw [← h]
      exact integral_congr_ae (ae_of_all _ fun y => by ring)
    linarith [T1, T3, hlast]
  filter_upwards [hD] with x hx
  linarith

end DFT.Continuum.Line
