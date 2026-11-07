/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Basic

/-!
# Solving the Schrödinger equation in the box

Global existence, uniqueness and continuous dependence for the linear system
`(y, y')' = (y', W y)` (the vector field `field W`) on `(-1, 2) ⊇ [0, 1]`, for continuous `W`.

* `exists_sol`: a solution with `(y, y')(0) = (0, 1)`. Mathlib's Picard–Lindelöf needs a bounded
  vector field, so we first solve the problem with the state clamped to a large box, then show by
  Grönwall that the solution never reaches the clamp.
* `sol_eq_zero_of_eq_zero`: a solution vanishing at one point vanishes everywhere.
* `sol_dist_le`: two solutions with the same initial data and nearby `W` stay close on `[0, 1]`.
-/

namespace DFT

namespace Continuum

namespace Box

open MeasureTheory Set Filter Topology

/-- `field` is Lipschitz in the state with constant `1 + B` whenever `|V t| ≤ B`. -/
lemma lipschitz_field' {V : ℝ → ℝ} {B t : ℝ} (hB : |V t| ≤ B) :
    LipschitzOnWith (Real.toNNReal (1 + B)) (field V t) univ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  refine (LipschitzWith.of_dist_le_mul fun y z => ?_).lipschitzOnWith
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [field, Prod.dist_eq, Real.dist_eq]
  have hy1 : |y.1 - z.1| ≤ max |y.1 - z.1| |y.2 - z.2| := le_max_left _ _
  have hy2 : |y.2 - z.2| ≤ max |y.1 - z.1| |y.2 - z.2| := le_max_right _ _
  have hm : 0 ≤ max |y.1 - z.1| |y.2 - z.2| := le_max_of_le_left (abs_nonneg _)
  have hV : |V t * y.1 - V t * z.1| ≤ B * max |y.1 - z.1| |y.2 - z.2| := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul hB hy1 (abs_nonneg _) hB0
  apply max_le <;> nlinarith

/-- A bound for a continuous function on `[-1, 2]`. -/
lemma exists_bound_W {W : ℝ → ℝ} (hW : Continuous W) :
    ∃ B, 0 ≤ B ∧ ∀ t ∈ Icc (-1 : ℝ) 2, |W t| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)).exists_bound_of_continuousOn
    hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht => ?_⟩
  exact (by simpa [Real.norm_eq_abs] using hB t ht : |W t| ≤ B).trans (le_max_left _ _)

/-- **Uniqueness.** A solution vanishing at one point of `(-1, 2)` vanishes on all of `(-1, 2)`. -/
theorem sol_eq_zero_of_eq_zero {W : ℝ → ℝ} (hW : Continuous W) {α : ℝ → ℝ × ℝ}
    (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t) {z : ℝ}
    (hz : z ∈ Ioo (-1 : ℝ) 2) (h0 : α z = 0) : ∀ t ∈ Ioo (-1 : ℝ) 2, α t = 0 := by
  obtain ⟨B, -, hB⟩ := exists_bound_W hW
  intro t ht
  set a := (-1 + min z t) / 2
  set b := (2 + max z t) / 2
  have hz1 := hz.1; have hz2 := hz.2; have ht1 := ht.1; have ht2 := ht.2
  have hmin1 : -1 < min z t := lt_min hz1 ht1
  have hmax2 : max z t < 2 := max_lt hz2 ht2
  have ha1 : -1 < a := by simp only [a]; linarith
  have hb2 : b < 2 := by simp only [b]; linarith
  have haz : a < z := by simp only [a]; linarith [min_le_left z t]
  have hat : a < t := by simp only [a]; linarith [min_le_right z t]
  have hzb : z < b := by simp only [b]; linarith [le_max_left z t]
  have htb : t < b := by simp only [b]; linarith [le_max_right z t]
  have hsub : Icc a b ⊆ Ioo (-1 : ℝ) 2 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have heq := ODE_solution_unique_of_mem_Icc (v := field W) (s := fun _ => univ)
    (K := Real.toNNReal (1 + B)) (f := α) (g := fun _ => (0 : ℝ × ℝ))
    (fun s hs => lipschitz_field' (hB s ⟨by linarith [hs.1], by linarith [hs.2]⟩))
    ⟨haz, hzb⟩ (fun s hs => (hd s (hsub hs)).continuousAt.continuousWithinAt)
    (fun s hs => hd s (hsub (Ioo_subset_Icc_self hs))) (fun _ _ => mem_univ _)
    continuousOn_const
    (fun s _ => by
      have := hasDerivAt_const s (0 : ℝ × ℝ)
      convert this using 1
      simp [field])
    (fun _ _ => mem_univ _) h0
  exact heq ⟨hat.le, htb.le⟩

/-- **Continuous dependence.** Two solutions with the same initial data, for coefficients `W1`, `W2`
that differ by at most `ε` on `[0, 1]`, differ by at most a Grönwall bound that tends to `0` with
`ε`. -/
theorem sol_dist_le {W1 W2 : ℝ → ℝ} {α1 α2 : ℝ → ℝ × ℝ} (h0 : α1 0 = α2 0)
    (hd1 : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α1 (field W1 t (α1 t)) t)
    (hd2 : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α2 (field W2 t (α2 t)) t)
    {B M ε : ℝ} (hB : ∀ t ∈ Icc (0 : ℝ) 1, |W1 t| ≤ B) (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖α2 t‖ ≤ M)
    (hε : ∀ t ∈ Icc (0 : ℝ) 1, |W1 t - W2 t| ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖α1 t - α2 t‖ ≤ gronwallBound 0 (1 + B) (ε * M) t := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 h01)
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := field W1) (s := fun _ => univ)
    (K := Real.toNNReal (1 + B)) (f := α1) (g := α2) (f' := fun t => field W1 t (α1 t))
    (g' := fun t => field W2 t (α2 t)) (εf := 0) (εg := ε * M) (δ := 0)
    (fun s hs => lipschitz_field' (hB s (Ico_subset_Icc_self hs)))
    (fun s hs => (hd1 s (hsub hs)).continuousAt.continuousWithinAt)
    (fun s hs => (hd1 s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (fun _ _ => by simp) (fun _ _ => mem_univ _)
    (fun s hs => (hd2 s (hsub hs)).continuousAt.continuousWithinAt)
    (fun s hs => (hd2 s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε s hs')
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s hs')
      have h1 : |(α2 s).1| ≤ M := (norm_fst_le (α2 s)).trans (hM s hs')
      simp only [field, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
      refine max_le (by positivity) ?_
      rw [← sub_mul, abs_mul, abs_sub_comm]
      exact mul_le_mul (hε s hs') h1 (abs_nonneg _) hε0)
    (fun _ _ => mem_univ _) (by simp [h0])
  intro t ht
  have := key t ht
  rw [dist_eq_norm, Real.coe_toNNReal _ (by linarith), zero_add, sub_zero] at this
  exact this

/-! ### Existence, via a clamped vector field -/

/-- Clamping a real number to `[-R, R]`. -/
def cl (R x : ℝ) : ℝ := max (-R) (min R x)

lemma cl_lip (R x y : ℝ) : |cl R x - cl R y| ≤ |x - y| := by
  simp only [cl]
  rw [max_comm (-R), max_comm (-R)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

lemma cl_abs_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |cl R x| ≤ |x| := by
  simp only [cl]
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact le_max_of_le_right (le_min (by linarith [abs_nonneg x]) (neg_abs_le x))
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

lemma cl_abs_le_R {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |cl R x| ≤ R := by
  simp only [cl]
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma cl_eq {R x : ℝ} (h : |x| ≤ R) : cl R x = x := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  simp only [cl, min_eq_right h2, max_eq_right h1]

/-- Clamping a state to the sup-norm ball of radius `R`. -/
def clamp (R : ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (cl R y.1, cl R y.2)

lemma lipschitz_clamp (R : ℝ) : LipschitzWith 1 (clamp R) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  simp only [clamp, Prod.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  exact max_le_max (cl_lip R _ _) (cl_lip R _ _)

/-- The clamped vector field. -/
def tfield (W : ℝ → ℝ) (R t : ℝ) (y : ℝ × ℝ) : ℝ × ℝ := field W t (clamp R y)

lemma norm_tfield_le_R {W : ℝ → ℝ} {B R t : ℝ} (hB : |W t| ≤ B) (hR : 0 ≤ R) (y : ℝ × ℝ) :
    ‖tfield W R t y‖ ≤ (1 + B) * R := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have h1 := cl_abs_le_R hR y.1
  have h2 := cl_abs_le_R hR y.2
  simp only [tfield, field, clamp, Prod.norm_def, Real.norm_eq_abs, abs_mul]
  refine max_le (by nlinarith) ?_
  nlinarith [mul_le_mul hB h1 (abs_nonneg _) hB0]

lemma norm_tfield_le {W : ℝ → ℝ} {B R t : ℝ} (hB : |W t| ≤ B) (hR : 0 ≤ R) (y : ℝ × ℝ) :
    ‖tfield W R t y‖ ≤ (1 + B) * ‖y‖ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have h1 : |cl R y.1| ≤ ‖y‖ := (cl_abs_le hR _).trans (by simpa using norm_fst_le y)
  have h2 : |cl R y.2| ≤ ‖y‖ := (cl_abs_le hR _).trans (by simpa using norm_snd_le y)
  have hy : 0 ≤ ‖y‖ := norm_nonneg _
  rw [show ‖tfield W R t y‖ = max |cl R y.2| (|W t| * |cl R y.1|) by
    simp [tfield, field, clamp, Prod.norm_def]]
  refine max_le (by nlinarith) ?_
  nlinarith [mul_le_mul hB h1 (abs_nonneg _) hB0]

lemma lipschitz_tfield {W : ℝ → ℝ} {B R t : ℝ} (hB : |W t| ≤ B) :
    LipschitzWith (Real.toNNReal (1 + B)) (tfield W R t) := by
  have h := (lipschitzOnWith_univ.mp (lipschitz_field' (V := W) hB)).comp (lipschitz_clamp R)
  rw [mul_one] at h
  exact h

/-- **Global existence** of the solution with `(y, y')(0) = (0, 1)` on `(-1, 2)`. -/
theorem exists_sol {W : ℝ → ℝ} (hW : Continuous W) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = (0, 1) ∧ ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_W hW
  set R := Real.exp ((1 + B) * 2)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hL : 0 ≤ (1 + B) * R := by positivity
  set t₀ : Icc (-1 : ℝ) 2 := ⟨0, by norm_num, by norm_num⟩
  have hPL : IsPicardLindelof (tfield W R) t₀ ((0 : ℝ), (1 : ℝ))
      (Real.toNNReal (2 * ((1 + B) * R))) 0 (Real.toNNReal ((1 + B) * R))
      (Real.toNNReal (1 + B)) := by
    refine ⟨fun t ht => (lipschitz_tfield (hB t ht)).lipschitzOnWith, fun x _ => ?_,
      fun t ht x _ => ?_, ?_⟩
    · simp only [tfield, field]
      exact (continuous_const.prodMk (hW.mul continuous_const)).continuousOn
    · rw [Real.coe_toNNReal _ hL]
      exact norm_tfield_le_R (hB t ht) hR x
    · simp only [t₀, NNReal.coe_zero, sub_zero]
      rw [Real.coe_toNNReal _ hL, Real.coe_toNNReal _ (by positivity)]
      norm_num
      linarith
  obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α 0 = (0, 1) := hα0
  have hint : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (tfield W R t (α t)) t := fun t ht =>
    (hαd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcont : ContinuousOn α (Icc (-1 : ℝ) 2) := fun t ht => (hαd t ht).continuousWithinAt
  have hnorm0 : ‖α 0‖ ≤ 1 := by simp [hα0', Prod.norm_def]
  have hexp : ∀ s ∈ Icc (0 : ℝ) 2, Real.exp ((1 + B) * s) ≤ R := fun s hs =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (by linarith))
  -- forward bound on `[0, 2]`
  have hfwd : ∀ t ∈ Icc (0 : ℝ) 2, ‖α t‖ ≤ R := by
    have g := norm_le_gronwallBound_of_norm_deriv_right_le (f := α)
      (f' := fun t => tfield W R t (α t)) (δ := 1) (K := 1 + B) (ε := 0) (a := 0) (b := 2)
      (hcont.mono (Icc_subset_Icc (by norm_num) le_rfl))
      (fun x hx => (hint x ⟨by linarith [hx.1], hx.2⟩).hasDerivWithinAt) hnorm0
      (fun x hx => by
        rw [add_zero]
        exact norm_tfield_le (hB x ⟨by linarith [hx.1], hx.2.le⟩) hR _)
    intro t ht
    have := g t ht
    rw [gronwallBound_ε0, sub_zero, one_mul] at this
    exact this.trans (hexp t ht)
  -- backward bound on `[-1, 0]`
  have hbwd : ∀ s ∈ Icc (0 : ℝ) 1, ‖α (-s)‖ ≤ R := by
    have g := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => α (-s))
      (f' := fun s => (-1 : ℝ) • tfield W R (-s) (α (-s))) (δ := 1) (K := 1 + B) (ε := 0)
      (a := 0) (b := 1)
      (hcont.comp continuousOn_neg fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (fun x hx => by
        have h := (hint (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩).scomp x
          (hasDerivAt_neg x)
        exact h.hasDerivWithinAt)
      (by simpa using hnorm0)
      (fun x hx => by
        rw [add_zero, norm_smul, norm_neg, norm_one, one_mul]
        exact norm_tfield_le (hB (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩) hR _)
    intro s hs
    have := g s hs
    rw [gronwallBound_ε0, sub_zero, one_mul] at this
    exact this.trans (hexp s ⟨hs.1, by linarith [hs.2]⟩)
  refine ⟨α, hα0', fun t ht => ?_⟩
  have hbd : ‖α t‖ ≤ R := by
    rcases le_or_gt 0 t with h | h
    · exact hfwd t ⟨h, ht.2.le⟩
    · simpa using hbwd (-t) ⟨by linarith, by linarith [ht.1]⟩
  have hc : clamp R (α t) = α t := by
    have h1 : |(α t).1| ≤ R := le_trans (by simpa using norm_fst_le (α t)) hbd
    have h2 : |(α t).2| ≤ R := le_trans (by simpa using norm_snd_le (α t)) hbd
    simp only [clamp, cl_eq h1, cl_eq h2]
  have := hint t ht
  simp only [tfield, hc] at this
  exact this

end Box

end Continuum

end DFT
