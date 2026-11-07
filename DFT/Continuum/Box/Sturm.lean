/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Sturm-type facts for the shooting solution in the box

Let `α = (y, y')` solve `y'' = W y` on `(-1, 2)` with `y(0) = 0`, `y'(0) = 1`.

* `pos_near_zero`: `y > 0` on some `(0, δ]`.
* `exists_first_zero`: if `y` vanishes somewhere in `(0, 1]`, it has a first zero there, and `y > 0`
  before it.
* `pos_of_nonneg`: if `W ≥ 0` on `[0, 1]`, then `y > 0` on `(0, 1]`.
* `exists_zero_of_le`: if `W ≤ -16` on `[0, 1]`, then `y` vanishes in `(0, 1)` (Sturm comparison
  with `sin 4t` through the Wronskian).
-/

namespace DFT

namespace Continuum

namespace Box

open Set Filter Topology

section sturm

variable {W : ℝ → ℝ} {α : ℝ → ℝ × ℝ}

lemma hasDerivAt_fst_of (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 2) : HasDerivAt (fun s => (α s).1) (α t).2 t := by
  have := hasFDerivAt_fst.comp_hasDerivAt t (hd t ht)
  simpa [field, Function.comp_def] using this

lemma hasDerivAt_snd_of (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 2) : HasDerivAt (fun s => (α s).2) (W t * (α t).1) t := by
  have := hasFDerivAt_snd.comp_hasDerivAt t (hd t ht)
  simpa [field, Function.comp_def] using this

lemma continuousOn_of_hd (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t)
    {a b : ℝ} (ha : -1 < a) (hb : b < 2) : ContinuousOn α (Icc a b) := fun t ht =>
  (hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt

/-- Near `0` the solution is positive. -/
lemma pos_near_zero (h0 : α 0 = (0, 1))
    (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t) :
    ∃ δ, 0 < δ ∧ δ ≤ 1 ∧ ∀ s ∈ Ioc 0 δ, 0 < (α s).1 := by
  have h0m : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hc : ContinuousAt (fun s => (α s).2) 0 :=
    (hasDerivAt_snd_of hd h0m).continuousAt
  obtain ⟨ε, hε, hεb⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  set δ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  refine ⟨δ, hδ, by linarith, fun s hs => ?_⟩
  have hmono : StrictMonoOn (fun s => (α s).1) (Icc 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
    · exact (continuous_fst.comp_continuousOn
        (continuousOn_of_hd hd (by norm_num) (by linarith)))
    · intro x hx
      rw [interior_Icc] at hx
      have hxm : x ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [(hasDerivAt_fst_of hd hxm).deriv]
      have hdist : dist x 0 < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2]
      have := hεb hdist
      rw [Real.dist_eq, h0] at this
      have h' := (abs_lt.mp this).1
      simp only at h'
      linarith
  have := hmono ⟨le_refl 0, hδ.le⟩ ⟨hs.1.le, hs.2⟩ hs.1
  simpa [h0] using this

/-- A non-positive value at `t ∈ (0, 1]` forces a zero in `(0, t]`. -/
lemma exists_zero_of_nonpos (h0 : α 0 = (0, 1))
    (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) (hneg : (α t).1 ≤ 0) : ∃ r ∈ Ioc (0 : ℝ) t, (α r).1 = 0 := by
  obtain ⟨δ, hδ, -, hpos⟩ := pos_near_zero h0 hd
  have htδ : δ < t := by
    by_contra h
    push Not at h
    have := hpos t ⟨ht.1, h⟩
    linarith
  have hcont : ContinuousOn (fun s => (α s).1) (Icc δ t) :=
    continuous_fst.comp_continuousOn (continuousOn_of_hd hd (by linarith) (by linarith [ht.2]))
  have hδpos := hpos δ ⟨hδ, le_refl δ⟩
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' htδ.le hcont ⟨hneg, hδpos.le⟩
  exact ⟨r, ⟨by linarith [hr.1], hr.2⟩, hr0⟩

/-- **First zero.** If the solution vanishes in `(0, 1]`, it has a first zero there and is positive
before it. -/
theorem exists_first_zero (h0 : α 0 = (0, 1))
    (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t) {z : ℝ}
    (hz : z ∈ Ioc (0 : ℝ) 1) (hz0 : (α z).1 = 0) :
    ∃ z₀ ∈ Ioc (0 : ℝ) 1, (α z₀).1 = 0 ∧ ∀ s ∈ Ioo 0 z₀, 0 < (α s).1 := by
  obtain ⟨δ, hδ, hδ1, hpos⟩ := pos_near_zero h0 hd
  set Z := Icc δ 1 ∩ (fun s => (α s).1) ⁻¹' {0}
  have hcl : IsClosed Z :=
    (continuous_fst.comp_continuousOn (continuousOn_of_hd hd (by linarith) (by norm_num))
      ).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcpt : IsCompact Z := isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  have hzδ : δ < z := by
    by_contra h
    push Not at h
    have := hpos z ⟨hz.1, h⟩
    linarith
  have hzZ : z ∈ Z := ⟨⟨hzδ.le, hz.2⟩, hz0⟩
  have hne : Z.Nonempty := ⟨z, hzZ⟩
  have hmem := hcpt.sInf_mem hne
  set z₀ := sInf Z
  have hbdd : BddBelow Z := hcpt.bddBelow
  refine ⟨z₀, ⟨by linarith [hmem.1.1], hmem.1.2⟩, hmem.2, fun s hs => ?_⟩
  by_cases hsδ : s ≤ δ
  · exact hpos s ⟨hs.1, hsδ⟩
  push Not at hsδ
  by_contra hns
  push Not at hns
  have hs1 : s ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2, hmem.1.2]⟩
  -- a zero in `[δ, s]` would precede `z₀`
  have hcont : ContinuousOn (fun s => (α s).1) (Icc δ s) :=
    continuous_fst.comp_continuousOn (continuousOn_of_hd hd (by linarith) (by linarith [hs1.2]))
  obtain ⟨r, hr, hr0⟩ :=
    intermediate_value_Icc' hsδ.le hcont ⟨hns, (hpos δ ⟨hδ, le_refl δ⟩).le⟩
  have hrZ : r ∈ Z := ⟨⟨hr.1, by linarith [hr.2, hs1.2]⟩, hr0⟩
  have := csInf_le hbdd hrZ
  linarith [hr.2, hs.2]

/-- **Nonnegative `W`.** The solution stays positive on `(0, 1]`. -/
theorem pos_of_nonneg (h0 : α 0 = (0, 1))
    (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t)
    (hWn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t) : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (α t).1 := by
  intro t ht
  by_contra hneg
  push Not at hneg
  obtain ⟨r, hr, hr0⟩ := exists_zero_of_nonpos h0 hd ht hneg
  obtain ⟨z₀, hz₀, hz0, hpos⟩ :=
    exists_first_zero h0 hd ⟨hr.1, le_trans hr.2 ht.2⟩ hr0
  have hcont := continuousOn_of_hd hd (a := 0) (b := z₀) (by norm_num) (by linarith [hz₀.2])
  -- `y'` is nondecreasing on `[0, z₀]`, hence `≥ 1`
  have hmono : MonotoneOn (fun s => (α s).2) (Icc 0 z₀) := by
    apply monotoneOn_of_deriv_nonneg (f := fun s => (α s).2) (convex_Icc 0 z₀)
      (continuous_snd.comp_continuousOn hcont)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_snd_of hd ⟨by linarith [hx.1], by linarith [hx.2, hz₀.2]⟩
        ).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_snd_of hd ⟨by linarith [hx.1], by linarith [hx.2, hz₀.2]⟩).deriv]
      exact mul_nonneg (hWn x ⟨hx.1.le, by linarith [hx.2, hz₀.2]⟩) (hpos x hx).le
  have hge : ∀ x ∈ Icc 0 z₀, 1 ≤ (α x).2 := fun x hx => by
    have := hmono ⟨le_refl 0, hz₀.1.le⟩ hx hx.1
    simpa [h0] using this
  -- so `y` is strictly increasing on `[0, z₀]`
  have hsm : StrictMonoOn (fun s => (α s).1) (Icc 0 z₀) := by
    apply strictMonoOn_of_deriv_pos (f := fun s => (α s).1) (convex_Icc 0 z₀)
      (continuous_fst.comp_continuousOn hcont)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_fst_of hd ⟨by linarith [hx.1], by linarith [hx.2, hz₀.2]⟩).deriv]
    linarith [hge x ⟨hx.1.le, hx.2.le⟩]
  have := hsm ⟨le_refl 0, hz₀.1.le⟩ ⟨hz₀.1.le, le_refl z₀⟩ hz₀.1
  simp only [h0] at this
  linarith

/-- **Sturm comparison.** If `W ≤ -16` on `[0, 1]`, the solution vanishes in `(0, 1)`. -/
theorem exists_zero_of_le (h0 : α 0 = (0, 1))
    (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t)
    (hWn : ∀ t ∈ Icc (0 : ℝ) 1, W t ≤ -16) : ∃ t ∈ Ioo (0 : ℝ) 1, (α t).1 = 0 := by
  by_contra hno
  push Not at hno
  have hp0 : 0 < Real.pi / 4 := by positivity
  have hp1 : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
  -- `y > 0` on `(0, 1)`
  have hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < (α t).1 := by
    intro t ht
    by_contra hneg
    push Not at hneg
    obtain ⟨r, hr, hr0⟩ := exists_zero_of_nonpos h0 hd ⟨ht.1, ht.2.le⟩ hneg
    exact hno r ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩ hr0
  -- the Wronskian with `sin 4t`
  set w : ℝ → ℝ := fun t => (α t).1 * (4 * Real.cos (4 * t)) - (α t).2 * Real.sin (4 * t)
  have h4 : ∀ t : ℝ, HasDerivAt (fun x => 4 * x) 4 t := fun t => by
    simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
  have hw : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt w
      (-(16 + W t) * (α t).1 * Real.sin (4 * t)) t := by
    intro t ht
    have e1 := hasDerivAt_fst_of hd ht
    have e2 := hasDerivAt_snd_of hd ht
    have ec := (h4 t).cos
    have es := (h4 t).sin
    have := (e1.mul (ec.const_mul 4)).sub (e2.mul es)
    convert this using 1
    ring
  have hcw : ContinuousOn w (Icc 0 (Real.pi / 4)) := fun t ht =>
    (hw t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  have hmono : MonotoneOn w (Icc 0 (Real.pi / 4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 4)) hcw
    · intro x hx
      rw [interior_Icc] at hx
      exact (hw x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hw x ⟨by linarith [hx.1], by linarith [hx.2]⟩).deriv]
      have hs : 0 < Real.sin (4 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
      have hy := hpos x ⟨hx.1, by linarith [hx.2]⟩
      have hW := hWn x ⟨hx.1.le, by linarith [hx.2]⟩
      have : 0 ≤ -(16 + W x) := by linarith
      positivity
  have hle := hmono ⟨le_refl 0, hp0.le⟩ ⟨hp0.le, le_refl _⟩ hp0.le
  have hw0 : w 0 = 0 := by simp [w, h0]
  have hwp : w (Real.pi / 4) = -4 * (α (Real.pi / 4)).1 := by
    simp only [w]
    rw [show 4 * (Real.pi / 4) = Real.pi by ring, Real.cos_pi, Real.sin_pi]
    ring
  have hyp := hpos (Real.pi / 4) ⟨hp0, hp1⟩
  rw [hw0, hwp] at hle
  linarith

end sturm

end Box

end Continuum

end DFT
