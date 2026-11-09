/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Basic

/-!
# One-variable tools for the nodal arguments

* The smoothed absolute value `h_ε(s) = √(s² + ε²) - ε`, its derivative `k_ε` and second derivative
  `k₂`, with the bounds used to compare `h_ε(Φ)` with `|Φ|`.
* `discr_le`: a nonnegative quadratic polynomial has nonpositive discriminant.
* `slice_lower`: a lower bound on the derivative gives a lower bound on the increment.
* `final_arith`: the closing inequality of the nodal arguments.
* `deriv2_nonneg_of_isLocalMin`: the second-derivative test in one variable.
-/

namespace DFT.Continuum.Line

open Set Filter Topology

/-! ### The smoothed absolute value -/

section smooth

/-- `h_ε(s) = √(s² + ε²) - ε`. -/
noncomputable def hε (ε s : ℝ) : ℝ := √(s ^ 2 + ε ^ 2) - ε
/-- `k_ε = h_ε'`. -/
noncomputable def kε (ε s : ℝ) : ℝ := s / √(s ^ 2 + ε ^ 2)
/-- `k₂ = k_ε'`. -/
noncomputable def k2 (ε s : ℝ) : ℝ := ε ^ 2 / √(s ^ 2 + ε ^ 2) ^ 3

variable {ε : ℝ} (hε0 : 0 < ε)
include hε0

lemma sqrt_pos_eps (s : ℝ) : 0 < √(s ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)

lemma sq_sqrt_eps (s : ℝ) : √(s ^ 2 + ε ^ 2) ^ 2 = s ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma hasDerivAt_sq_eps (s : ℝ) :
    HasDerivAt (fun s => √(s ^ 2 + ε ^ 2)) (s / √(s ^ 2 + ε ^ 2)) s := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ε ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (ε ^ 2)
  have h2 := h1.sqrt (sqrt_pos_eps hε0 s |> fun h => by positivity)
  convert h2 using 1
  have := sqrt_pos_eps hε0 s
  field_simp

lemma hasDerivAt_hε (s : ℝ) : HasDerivAt (hε ε) (kε ε s) s :=
  (hasDerivAt_sq_eps hε0 s).sub_const ε

lemma hasDerivAt_kε (s : ℝ) : HasDerivAt (kε ε) (k2 ε s) s := by
  have h : HasDerivAt (kε ε) ((1 * √(s ^ 2 + ε ^ 2) - s * (s / √(s ^ 2 + ε ^ 2))) /
      √(s ^ 2 + ε ^ 2) ^ 2) s :=
    (hasDerivAt_id s).div (hasDerivAt_sq_eps hε0 s) (sqrt_pos_eps hε0 s).ne'
  convert h using 1
  have hp := sqrt_pos_eps hε0 s
  have hs := sq_sqrt_eps hε0 s
  unfold k2
  field_simp
  nlinarith [hs]

lemma contDiff_sq_eps : ContDiff ℝ 2 (fun s : ℝ => √(s ^ 2 + ε ^ 2)) :=
  ((contDiff_id.pow 2).add contDiff_const).sqrt fun s => (sqrt_pos_eps hε0 s |> fun _ => by
    positivity)

lemma contDiff_hε : ContDiff ℝ 2 (hε ε) := (contDiff_sq_eps hε0).sub contDiff_const

lemma contDiff_kε : ContDiff ℝ 2 (kε ε) :=
  contDiff_id.div (contDiff_sq_eps hε0) fun s => (sqrt_pos_eps hε0 s).ne'

lemma hε_zero : hε ε 0 = 0 := by
  simp [hε, Real.sqrt_sq hε0.le]

lemma k2_pos (s : ℝ) : 0 < k2 ε s := by
  have := sqrt_pos_eps hε0 s
  unfold k2; positivity

lemma continuous_k2 : Continuous (k2 ε) := by
  unfold k2
  exact continuous_const.div ((((continuous_id.pow 2).add continuous_const).sqrt).pow 3)
    fun s => by have := sqrt_pos_eps hε0 s; positivity

omit hε0 in
lemma abs_le_sqrt_eps (s : ℝ) : |s| ≤ √(s ^ 2 + ε ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma eps_le_sqrt_eps (s : ℝ) : ε ≤ √(s ^ 2 + ε ^ 2) := by
  conv_lhs => rw [← Real.sqrt_sq hε0.le]
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma sqrt_eps_le (s : ℝ) : √(s ^ 2 + ε ^ 2) ≤ |s| + ε := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg s, sq_abs s]

lemma abs_kε_le (s : ℝ) : |kε ε s| ≤ 1 := by
  have hp := sqrt_pos_eps hε0 s
  unfold kε
  rw [abs_div, abs_of_pos hp, div_le_one hp]
  exact abs_le_sqrt_eps s

lemma kε_sq_le (s : ℝ) : kε ε s ^ 2 ≤ 1 := by
  have := abs_kε_le hε0 s
  rw [← sq_abs]; nlinarith [abs_nonneg (kε ε s)]

lemma kε_ge_half {s : ℝ} (hs : ε ≤ s) : 1 / 2 ≤ kε ε s := by
  have hp := sqrt_pos_eps hε0 s
  have h1 : √(s ^ 2 + ε ^ 2) ≤ 2 * s := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  unfold kε
  rw [le_div_iff₀ hp]; linarith

lemma kε_le_neg_half {s : ℝ} (hs : s ≤ -ε) : kε ε s ≤ -1 / 2 := by
  have h := kε_ge_half hε0 (s := -s) (by linarith)
  have hneg : kε ε (-s) = -kε ε s := by simp [kε, neg_div]
  rw [hneg] at h; linarith

lemma abs_hε_sq_sub (s : ℝ) : |hε ε s ^ 2 - s ^ 2| ≤ 2 * ε * |s| := by
  have h1 := abs_le_sqrt_eps (ε := ε) s
  have h2 := sqrt_eps_le hε0 s
  have h3 := eps_le_sqrt_eps hε0 s
  have hs := sq_abs s
  unfold hε
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg s]

lemma abs_hε_sub (s : ℝ) : |hε ε s - s * kε ε s| ≤ ε := by
  have hp := sqrt_pos_eps hε0 s
  have hs := sq_sqrt_eps hε0 s
  have h3 := eps_le_sqrt_eps hε0 s
  have e : hε ε s - s * kε ε s = ε ^ 2 / √(s ^ 2 + ε ^ 2) - ε := by
    unfold hε kε; field_simp; nlinarith [hs]
  rw [e, abs_le]
  constructor
  · have : 0 ≤ ε ^ 2 / √(s ^ 2 + ε ^ 2) := by positivity
    linarith
  · have : ε ^ 2 / √(s ^ 2 + ε ^ 2) ≤ ε := by
      rw [div_le_iff₀ hp]; nlinarith
    linarith

end smooth

/-! ### The smoothed absolute value: parity and bounds -/

lemma hε_neg (ε s : ℝ) : hε ε (-s) = hε ε s := by simp [hε]

lemma kε_neg (ε s : ℝ) : kε ε (-s) = -kε ε s := by simp [kε, neg_div]

lemma abs_hε_le {ε : ℝ} (hε0 : 0 < ε) (s : ℝ) : |hε ε s| ≤ |s| := by
  have h1 := eps_le_sqrt_eps hε0 s
  have h2 := sqrt_eps_le hε0 s
  rw [abs_of_nonneg (by simp only [hε]; linarith)]
  simp only [hε]; linarith

lemma ar_X {V x p ε : ℝ} (h : |x| ≤ ε) (hp : 0 ≤ p) : |V| * |x| * p ≤ ε * (|V| * p) := by
  have := mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg V) hp)
  nlinarith

/-! ### Inequalities -/

/-- A nonnegative quadratic polynomial has nonpositive discriminant. -/
lemma discr_le {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  have ha : 0 ≤ a := by simpa using h 0
  rcases hc.lt_or_eq with hc | hc
  · have := h (-b / c)
    have e : a + 2 * (-b / c) * b + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hc] at this
    linarith
  · subst hc
    by_contra hb
    have hb0 : b ≠ 0 := fun h0 => by simp [h0] at hb
    have := h (-(a + 1) / (2 * b))
    have e : a + 2 * (-(a + 1) / (2 * b)) * b + (-(a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
      field_simp; ring
    rw [e] at this
    linarith

lemma slice_lower {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {c x0 x1 : ℝ}
    (hx : x0 ≤ x1) (hc : ∀ x ∈ Icc x0 x1, c ≤ f' x) : c * (x1 - x0) ≤ f x1 - f x0 :=
  Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc x0 x1) (f := f) (C := c)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hf x).deriv]; exact hc x ⟨hx.1.le, hx.2.le⟩)
    x0 ⟨le_rfl, hx⟩ x1 ⟨hx, le_rfl⟩ hx

lemma final_arith {L K1 K2 C ε B R : ℝ} (hL : 0 < L) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hC : 0 ≤ C) (hε0 : 0 < ε) (hε1 : ε ≤ L / (4 * (K2 + 1)))
    (hε2 : ε ≤ L ^ 2 / (16 * (K1 * C + 1))) (hA : L ≤ ε * K2 + |B|) (hB2 : R ≤ 2 * ε * K1)
    (hB3 : B ^ 2 ≤ R * C) : False := by
  rw [le_div_iff₀ (by positivity)] at hε1 hε2
  have hεK2 : ε * K2 ≤ L / 4 := by nlinarith
  have hBsq : B ^ 2 ≤ L ^ 2 / 8 := by
    calc B ^ 2 ≤ R * C := hB3
      _ ≤ 2 * ε * K1 * C := mul_le_mul_of_nonneg_right hB2 hC
      _ ≤ L ^ 2 / 8 := by nlinarith [mul_nonneg hK1 hC]
  have hB34 : 3 * L / 4 ≤ |B| := by linarith
  have : (3 * L / 4) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs B]; exact pow_le_pow_left₀ (by positivity) hB34 2
  nlinarith [sq_pos_of_pos hL]

/-- **Second-derivative test** in one variable. -/
lemma deriv2_nonneg_of_isLocalMin {f f' f'' : ℝ → ℝ} {x0 : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hc : ContinuousAt f'' x0) (hmin : IsLocalMin f x0) : 0 ≤ f'' x0 := by
  by_contra hneg
  push Not at hneg
  have h0 : f' x0 = 0 := by
    have := hmin.deriv_eq_zero; rwa [(hf x0).deriv] at this
  -- `f'' < 0` near `x0`
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc (-(f'' x0)) (by linarith)
  have hneg' : ∀ x, |x - x0| < δ → f'' x < 0 := by
    intro x hx
    have := hδc (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    linarith [(abs_lt.mp this).2]
  -- local minimum: `f x ≥ f x0` near `x0`
  obtain ⟨ε, hε, hεm⟩ := Metric.eventually_nhds_iff.mp hmin
  set s := min (δ / 2) (ε / 2)
  have hs : 0 < s := lt_min (by linarith) (by linarith)
  have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsε : s < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- `f' > 0` on `(x0 - s, x0)`
  have hpos : ∀ x ∈ Ioo (x0 - s) x0, 0 < f' x := by
    intro x hx
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope f' f'' hx.2
      (fun y _ => (hf' y).continuousAt.continuousWithinAt) (fun y _ => hf' y)
    have hξn := hneg' ξ (by rw [abs_lt]; constructor <;> linarith [hξ.1, hξ.2, hx.1])
    rw [h0, eq_div_iff (by linarith [hx.2])] at hξe
    nlinarith [hx.2]
  -- so `f (x0 - s) < f x0`
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope f f' (show x0 - s < x0 by linarith)
    (fun y _ => (hf y).continuousAt.continuousWithinAt) (fun y _ => hf y)
  have hfp := hpos ξ hξ
  rw [eq_div_iff (by linarith)] at hξe
  have hle := hεm (show dist (x0 - s) x0 < ε by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  nlinarith

end DFT.Continuum.Line
