/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Sturm
import DFT.Continuum.Box.Extend
import DFT.Continuum.Box.Solve

/-!
# The Green function of `-d²/dx² + W` on `[0, 1]`

For a continuous coefficient `W ≥ 0` on `[0, 1]`, the Dirichlet problem `-y'' + W y = f`,
`y(0) = y(1) = 0`, has the explicit solution

`G f (x) = (w(x) ∫₀ˣ u f + u(x) ∫ₓ¹ w f) / ω`,

where `u` solves `u'' = W u` from the left wall (`u(0) = 0`, `u'(0) = 1`), `w` solves it from the
right wall (`w(1) = 0`, `w'(1) = -1`), both are positive inside, and `ω = u' w - u w' = w(0) > 0` is
their (constant) Wronskian. This is the first step towards the spectral decomposition of the
one-particle Hamiltonian.

* `uS`, `wS`: the left and right solutions; `uS_pos`, `wS_pos`: positivity.
* `wronskian_eq`: the Wronskian is constant, equal to `ω = wS 0 > 0`.
* `Gf`, `hasDerivAt_Gf`, `hasDerivAt_dGf`: for continuous `f`, `Gf` is twice differentiable with
  `(Gf)'' = W · Gf - f`, and `Gf 0 = Gf 1 = 0`.
* `eq_zero_of_dirichlet`: uniqueness, a solution of `y'' = W y` vanishing at both walls is zero.
-/

namespace DFT.Continuum.Spectral

open MeasureTheory Set Filter Topology Box

variable {W : ℝ → ℝ} (hWc : Continuous W)

/-! ### The left and right solutions -/

/-- The left solution as a pair `(u, u')`: `u'' = W u`, `u(0) = 0`, `u'(0) = 1`. -/
noncomputable def solL (hWc : Continuous W) : ℝ → ℝ × ℝ := Classical.choose (exists_sol hWc)

lemma solL_zero : solL hWc 0 = (0, 1) := (Classical.choose_spec (exists_sol hWc)).1

lemma solL_deriv : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt (solL hWc) (field W t (solL hWc t)) t :=
  (Classical.choose_spec (exists_sol hWc)).2

/-- The reflected coefficient `W(1 - t)`. -/
def Wr (W : ℝ → ℝ) (t : ℝ) : ℝ := W (1 - t)

lemma continuous_Wr (h : Continuous W) : Continuous (Wr W) :=
  h.comp (continuous_const.sub continuous_id)

/-- The right solution, shot from `1` for the reflected coefficient. -/
noncomputable def solR (hWc : Continuous W) : ℝ → ℝ × ℝ :=
  Classical.choose (exists_sol (continuous_Wr hWc))

lemma solR_zero : solR hWc 0 = (0, 1) := (Classical.choose_spec (exists_sol (continuous_Wr hWc))).1

lemma solR_deriv : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt (solR hWc) (field (Wr W) t (solR hWc t)) t :=
  (Classical.choose_spec (exists_sol (continuous_Wr hWc))).2

/-- `u`, `u'`, `w`, `w'`. -/
noncomputable def uS (x : ℝ) : ℝ := (solL hWc x).1
noncomputable def duS (x : ℝ) : ℝ := (solL hWc x).2
noncomputable def wS (x : ℝ) : ℝ := (solR hWc (1 - x)).1
noncomputable def dwS (x : ℝ) : ℝ := -(solR hWc (1 - x)).2

lemma mem_reflect {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) : 1 - x ∈ Ioo (-1 : ℝ) 2 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

lemma hasDerivAt_uS {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) : HasDerivAt (uS hWc) (duS hWc x) x :=
  hasDerivAt_fst_of (solL_deriv hWc) hx

lemma hasDerivAt_duS {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) :
    HasDerivAt (duS hWc) (W x * uS hWc x) x :=
  hasDerivAt_snd_of (solL_deriv hWc) hx

lemma hasDerivAt_wS {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) : HasDerivAt (wS hWc) (dwS hWc x) x := by
  have h := (hasDerivAt_fst_of (solR_deriv hWc) (mem_reflect hx)).comp x
    ((hasDerivAt_id x).const_sub 1)
  change HasDerivAt (fun x => (solR hWc (1 - x)).1) (-(solR hWc (1 - x)).2) x
  simpa [Function.comp_def] using h

lemma hasDerivAt_dwS {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) :
    HasDerivAt (dwS hWc) (W x * wS hWc x) x := by
  have h := ((hasDerivAt_snd_of (solR_deriv hWc) (mem_reflect hx)).comp x
    ((hasDerivAt_id x).const_sub 1)).neg
  change HasDerivAt (fun x => -(solR hWc (1 - x)).2) (W x * (solR hWc (1 - x)).1) x
  simp only [Wr, sub_sub_cancel, Function.comp_def, mul_neg, mul_one, neg_neg] at h
  exact h

lemma uS_zero : uS hWc 0 = 0 := by simp [uS, solL_zero]
lemma duS_zero : duS hWc 0 = 1 := by simp [duS, solL_zero]
lemma wS_one : wS hWc 1 = 0 := by simp [wS, solR_zero]
lemma dwS_one : dwS hWc 1 = -1 := by simp [dwS, solR_zero]

variable (hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t)
include hW0

lemma uS_pos : ∀ x ∈ Ioc (0 : ℝ) 1, 0 < uS hWc x :=
  pos_of_nonneg (solL_zero hWc) (solL_deriv hWc) hW0

lemma wS_pos : ∀ x ∈ Ico (0 : ℝ) 1, 0 < wS hWc x := by
  intro x hx
  have hWr : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ Wr W t := fun t ht =>
    hW0 (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  exact pos_of_nonneg (solR_zero hWc) (solR_deriv hWc) hWr (1 - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩

omit hW0 in
/-- The Wronskian `u' w - u w'` is constant on `(-1, 2)`. -/
lemma wronskian_const {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) :
    duS hWc x * wS hWc x - uS hWc x * dwS hWc x = wS hWc 0 := by
  set F : ℝ → ℝ := fun t => duS hWc t * wS hWc t - uS hWc t * dwS hWc t
  have hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt F 0 t := by
    intro t ht
    have h := ((hasDerivAt_duS hWc ht).mul (hasDerivAt_wS hWc ht)).sub
      ((hasDerivAt_uS hWc ht).mul (hasDerivAt_dwS hWc ht))
    convert h using 1; ring
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (isPreconnected_Ioo)
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hx (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 by norm_num)
  simp only [F, uS_zero hWc, duS_zero hWc, one_mul, zero_mul, sub_zero] at hc
  exact hc

/-- The Wronskian `ω = w(0)` is positive. -/
lemma omega_pos : 0 < wS hWc 0 := wS_pos hWc hW0 0 ⟨le_rfl, one_pos⟩

omit hW0

/-! ### The Green operator on functions -/

/-- The Green operator: `G f (x) = (w(x) ∫₀ˣ u f + u(x) ∫ₓ¹ w f) / ω`. -/
noncomputable def Gf (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (wS hWc x * (∫ y in (0 : ℝ)..x, uS hWc y * f y) +
    uS hWc x * (∫ y in x..(1 : ℝ), wS hWc y * f y)) / wS hWc 0

/-- Its derivative: `(w'(x) ∫₀ˣ u f + u'(x) ∫ₓ¹ w f) / ω`. -/
noncomputable def dGf (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (dwS hWc x * (∫ y in (0 : ℝ)..x, uS hWc y * f y) +
    duS hWc x * (∫ y in x..(1 : ℝ), wS hWc y * f y)) / wS hWc 0

lemma continuousOn_uS : ContinuousOn (uS hWc) (Ioo (-1 : ℝ) 2) := fun _ ht =>
  (hasDerivAt_uS hWc ht).continuousAt.continuousWithinAt

lemma continuousOn_wS : ContinuousOn (wS hWc) (Ioo (-1 : ℝ) 2) := fun _ ht =>
  (hasDerivAt_wS hWc ht).continuousAt.continuousWithinAt

lemma Icc_sub_Ioo {a b : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 2) (hb : b ∈ Ioo (-1 : ℝ) 2) :
    uIcc a b ⊆ Ioo (-1 : ℝ) 2 := by
  intro t ht
  rw [mem_uIcc] at ht
  rcases ht with h | h
  · exact ⟨by linarith [ha.1, h.1], by linarith [hb.2, h.2]⟩
  · exact ⟨by linarith [hb.1, h.1], by linarith [ha.2, h.2]⟩

section deriv

variable {f : ℝ → ℝ} (hf : Continuous f)
include hf

lemma hasDerivAt_intL {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) :
    HasDerivAt (fun x => ∫ y in (0 : ℝ)..x, uS hWc y * f y) (uS hWc x * f x) x := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
  have hcont : ContinuousOn (fun y => uS hWc y * f y) (Ioo (-1 : ℝ) 2) :=
    (continuousOn_uS hWc).mul hf.continuousOn
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · exact (hcont.mono (Icc_sub_Ioo h0 hx)).intervalIntegrable
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcont x hx
  · exact hcont.continuousAt (isOpen_Ioo.mem_nhds hx)

lemma hasDerivAt_intR {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) :
    HasDerivAt (fun x => ∫ y in x..(1 : ℝ), wS hWc y * f y) (-(wS hWc x * f x)) x := by
  have h1 : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
  have hcont : ContinuousOn (fun y => wS hWc y * f y) (Ioo (-1 : ℝ) 2) :=
    (continuousOn_wS hWc).mul hf.continuousOn
  refine intervalIntegral.integral_hasDerivAt_left ?_ ?_ ?_
  · exact (hcont.mono (Icc_sub_Ioo hx h1)).intervalIntegrable
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcont x hx
  · exact hcont.continuousAt (isOpen_Ioo.mem_nhds hx)

/-- `(G f)' = dGf`. -/
lemma hasDerivAt_Gf {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) :
    HasDerivAt (Gf hWc f) (dGf hWc f x) x := by
  have h := (((hasDerivAt_wS hWc hx).mul (hasDerivAt_intL hWc hf hx)).add
    ((hasDerivAt_uS hWc hx).mul (hasDerivAt_intR hWc hf hx))).div_const (wS hWc 0)
  have h' := h.congr_deriv (show _ = dGf hWc f x by simp only [dGf]; ring)
  exact h' 

/-- `(G f)'' = W · G f - f`. -/
lemma hasDerivAt_dGf (hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 2) :
    HasDerivAt (dGf hWc f) (W x * Gf hWc f x - f x) x := by
  have h := (((hasDerivAt_dwS hWc hx).mul (hasDerivAt_intL hWc hf hx)).add
    ((hasDerivAt_duS hWc hx).mul (hasDerivAt_intR hWc hf hx))).div_const (wS hWc 0)
  have hω := wronskian_const hWc hx
  have hω0 : wS hWc 0 ≠ 0 := (omega_pos hWc hW0).ne'
  have h' := h.congr_deriv (show _ = W x * Gf hWc f x - f x by
    simp only [Gf]
    field_simp
    linear_combination (-(f x)) * hω)
  exact h' 

end deriv

lemma Gf_zero (f : ℝ → ℝ) : Gf hWc f 0 = 0 := by
  simp [Gf, uS_zero hWc]

lemma Gf_one (f : ℝ → ℝ) : Gf hWc f 1 = 0 := by
  simp [Gf, wS_one hWc]

/-! ### Uniqueness for the Dirichlet problem -/

include hWc hW0 in
/-- **Uniqueness**: a solution of `y'' = W y` on `(-1, 2)` vanishing at `0` and `1` is zero. -/
theorem eq_zero_of_dirichlet {y dy : ℝ → ℝ}
    (hy : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt y (dy t) t)
    (hdy : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt dy (W t * y t) t) (h0 : y 0 = 0) (h1 : y 1 = 0) :
    ∀ t ∈ Ioo (-1 : ℝ) 2, y t = 0 := by
  set a := dy 0
  set β : ℝ → ℝ × ℝ := fun t => (y t - a * uS hWc t, dy t - a * duS hWc t)
  have hβ : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt β (field W t (β t)) t := by
    intro t ht
    have h := ((hy t ht).sub ((hasDerivAt_uS hWc ht).const_mul a)).prodMk
      ((hdy t ht).sub ((hasDerivAt_duS hWc ht).const_mul a))
    refine h.congr_deriv ?_
    ext
    · simp only [field, β]
    · simp only [field, β]; ring
  have hβ0 : β 0 = 0 := by
    simp only [β, h0, uS_zero hWc, duS_zero hWc, a]; ext <;> simp
  have hz := sol_eq_zero_of_eq_zero hWc hβ (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 by norm_num) hβ0
  have hyu : ∀ t ∈ Ioo (-1 : ℝ) 2, y t = a * uS hWc t := fun t ht => by
    have := congrArg Prod.fst (hz t ht); simp only [β, Prod.fst_zero] at this; linarith
  have ha : a = 0 := by
    have := hyu 1 (by norm_num)
    rw [h1] at this
    have hu1 := uS_pos hWc hW0 1 ⟨one_pos, le_rfl⟩
    rcases mul_eq_zero.1 this.symm with h | h
    · exact h
    · exact absurd h hu1.ne'
  intro t ht
  rw [hyu t ht, ha, zero_mul]

include hW0 in
/-- **`G f` is the solution of the Dirichlet problem**: any `y` with `-y'' + W y = f` on `(-1, 2)`
and `y(0) = y(1) = 0` equals `G f` there. -/
theorem eq_Gf {f : ℝ → ℝ} (hf : Continuous f) {y dy : ℝ → ℝ}
    (hy : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt y (dy t) t)
    (hdy : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt dy (W t * y t - f t) t) (h0 : y 0 = 0) (h1 : y 1 = 0) :
    ∀ t ∈ Ioo (-1 : ℝ) 2, y t = Gf hWc f t := by
  have hz := eq_zero_of_dirichlet hWc hW0 (y := fun t => y t - Gf hWc f t)
    (dy := fun t => dy t - dGf hWc f t)
    (fun t ht => (hy t ht).sub (hasDerivAt_Gf hWc hf ht))
    (fun t ht => by
      have h := (hdy t ht).sub (hasDerivAt_dGf hWc hf hW0 ht)
      refine h.congr_deriv ?_; ring)
    (by simp [h0, Gf_zero]) (by simp [h1, Gf_one])
  intro t ht
  linarith [hz t ht]

end DFT.Continuum.Spectral
