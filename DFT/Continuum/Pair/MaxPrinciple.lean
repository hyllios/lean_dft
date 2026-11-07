/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Pair.Basic

/-!
# Hopf's strong maximum principle on the square

A nonnegative `C²` supersolution of `-Δ + c` (with `c ≥ 0` continuous) on the open square that
vanishes at one interior point vanishes on the whole square.

* `deriv2_nonneg_of_isLocalMin`, `d11_nonneg_of_isLocalMin`, `d22_nonneg_of_isLocalMin`: the
  second-derivative test.
* `barrier`, `lap_barrier`: the Hopf barrier `e^{-α|x - y|²} - e^{-αR²}` and its Laplacian.
* `local_zero`: near a zero of `u` the function vanishes identically (Hopf's lemma on the largest
  Euclidean ball inside `{u > 0}`, plus weak comparison on an annulus).
* `strong_max_principle`: the global statement, by connectedness of the square.
-/

namespace DFT

namespace Continuum

namespace Pair

open Set Filter Topology Metric

/-! ### Slices and second derivatives -/

section slices

variable {ψ : ℝ × ℝ → ℝ}

lemma hasDerivAt_s1 (hψ : Differentiable ℝ ψ) (t y : ℝ) :
    HasDerivAt (fun t => ψ (t, y)) (d1 ψ (t, y)) t := by
  have h := ((hψ (t, y)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact h

lemma hasDerivAt_s2 (hψ : Differentiable ℝ ψ) (x t : ℝ) :
    HasDerivAt (fun t => ψ (x, t)) (d2 ψ (x, t)) t := by
  have h := ((hψ (x, t)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  exact h

lemma d1_eq_of_hasDerivAt (hψ : Differentiable ℝ ψ) {p : ℝ × ℝ} {a : ℝ}
    (h : HasDerivAt (fun t => ψ (t, p.2)) a p.1) : d1 ψ p = a :=
  (hasDerivAt_s1 hψ p.1 p.2).unique h

lemma d2_eq_of_hasDerivAt (hψ : Differentiable ℝ ψ) {p : ℝ × ℝ} {a : ℝ}
    (h : HasDerivAt (fun t => ψ (p.1, t)) a p.2) : d2 ψ p = a :=
  (hasDerivAt_s2 hψ p.1 p.2).unique h

lemma d11_eq_d1 (ψ : ℝ × ℝ → ℝ) : d11 ψ = d1 (d1 ψ) := rfl
lemma d22_eq_d2 (ψ : ℝ × ℝ → ℝ) : d22 ψ = d2 (d2 ψ) := rfl

end slices

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

lemma d11_nonneg_of_isLocalMin {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) {q : ℝ × ℝ}
    (hq : IsLocalMin ψ q) : 0 ≤ d11 ψ q := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (d1 ψ) := (contDiff_d1 hψ).differentiable one_ne_zero
  have := deriv2_nonneg_of_isLocalMin (f := fun t => ψ (t, q.2)) (f' := fun t => d1 ψ (t, q.2))
    (f'' := fun t => d11 ψ (t, q.2)) (x0 := q.1) (fun t => hasDerivAt_s1 hd t q.2)
    (fun t => hasDerivAt_s1 hd1 t q.2)
    ((continuous_d11 hψ).comp (continuous_id.prodMk continuous_const)).continuousAt
    (hq.comp_continuous (g := fun t => (t, q.2)) (by fun_prop))
  simpa using this

lemma d22_nonneg_of_isLocalMin {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) {q : ℝ × ℝ}
    (hq : IsLocalMin ψ q) : 0 ≤ d22 ψ q := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (d2 ψ) := (contDiff_d2 hψ).differentiable one_ne_zero
  have := deriv2_nonneg_of_isLocalMin (f := fun t => ψ (q.1, t)) (f' := fun t => d2 ψ (q.1, t))
    (f'' := fun t => d22 ψ (q.1, t)) (x0 := q.2) (fun t => hasDerivAt_s2 hd q.1 t)
    (fun t => hasDerivAt_s2 hd2 q.1 t)
    ((continuous_d22 hψ).comp (continuous_const.prodMk continuous_id)).continuousAt
    (hq.comp_continuous (g := fun t => (q.1, t)) (by fun_prop))
  simpa using this

/-! ### Linearity -/

section linear

variable {ψ φ : ℝ × ℝ → ℝ}

lemma d1_sub_mul (hψ : Differentiable ℝ ψ) (hφ : Differentiable ℝ φ) (ε : ℝ) :
    d1 (fun p => ψ p - ε * φ p) = fun p => d1 ψ p - ε * d1 φ p := by
  funext p
  exact d1_eq_of_hasDerivAt (hψ.sub (hφ.const_mul ε))
    ((hasDerivAt_s1 hψ p.1 p.2).sub ((hasDerivAt_s1 hφ p.1 p.2).const_mul ε))

lemma d2_sub_mul (hψ : Differentiable ℝ ψ) (hφ : Differentiable ℝ φ) (ε : ℝ) :
    d2 (fun p => ψ p - ε * φ p) = fun p => d2 ψ p - ε * d2 φ p := by
  funext p
  exact d2_eq_of_hasDerivAt (hψ.sub (hφ.const_mul ε))
    ((hasDerivAt_s2 hψ p.1 p.2).sub ((hasDerivAt_s2 hφ p.1 p.2).const_mul ε))

lemma lap_sub_mul (hψ : Differentiable ℝ ψ) (hφ : Differentiable ℝ φ)
    (hψ1 : Differentiable ℝ (d1 ψ)) (hφ1 : Differentiable ℝ (d1 φ))
    (hψ2 : Differentiable ℝ (d2 ψ)) (hφ2 : Differentiable ℝ (d2 φ)) (ε : ℝ) (p : ℝ × ℝ) :
    lap (fun p => ψ p - ε * φ p) p = lap ψ p - ε * lap φ p := by
  simp only [lap, d11_eq_d1, d22_eq_d2, d1_sub_mul hψ hφ, d2_sub_mul hψ hφ,
    d1_sub_mul hψ1 hφ1, d2_sub_mul hψ2 hφ2]
  ring

end linear

/-! ### The barrier -/

/-- The squared Euclidean distance to `y`. -/
def eu (y p : ℝ × ℝ) : ℝ := (p.1 - y.1) ^ 2 + (p.2 - y.2) ^ 2

lemma continuous_eu (y : ℝ × ℝ) : Continuous (eu y) := by unfold eu; fun_prop

/-- The Hopf barrier `e^{-α|p - y|²} - K`. -/
noncomputable def barrier (α : ℝ) (y : ℝ × ℝ) (K : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-α * eu y p) - K

noncomputable def bar1 (α : ℝ) (y p : ℝ × ℝ) : ℝ := -2 * α * (p.1 - y.1) * Real.exp (-α * eu y p)
noncomputable def bar2 (α : ℝ) (y p : ℝ × ℝ) : ℝ := -2 * α * (p.2 - y.2) * Real.exp (-α * eu y p)

lemma differentiable_barrier (α : ℝ) (y : ℝ × ℝ) (K : ℝ) : Differentiable ℝ (barrier α y K) := by
  unfold barrier eu; fun_prop

lemma differentiable_bar1 (α : ℝ) (y : ℝ × ℝ) : Differentiable ℝ (bar1 α y) := by
  unfold bar1 eu; fun_prop

lemma differentiable_bar2 (α : ℝ) (y : ℝ × ℝ) : Differentiable ℝ (bar2 α y) := by
  unfold bar2 eu; fun_prop

lemma d1_barrier (α : ℝ) (y : ℝ × ℝ) (K : ℝ) : d1 (barrier α y K) = bar1 α y := by
  funext p
  refine d1_eq_of_hasDerivAt (differentiable_barrier α y K) ?_
  have h : HasDerivAt (fun t => -α * ((t - y.1) ^ 2 + (p.2 - y.2) ^ 2))
      (-α * (2 * (p.1 - y.1))) p.1 := by
    have := (((hasDerivAt_id p.1).sub_const y.1).pow 2).add_const ((p.2 - y.2) ^ 2)
    simpa using this.const_mul (-α)
  have := (h.exp).sub_const K
  convert this using 1
  · funext t; simp only [barrier, eu]
  · simp only [bar1, eu]; ring

lemma d2_barrier (α : ℝ) (y : ℝ × ℝ) (K : ℝ) : d2 (barrier α y K) = bar2 α y := by
  funext p
  refine d2_eq_of_hasDerivAt (differentiable_barrier α y K) ?_
  have h : HasDerivAt (fun t => -α * ((p.1 - y.1) ^ 2 + (t - y.2) ^ 2))
      (-α * (2 * (p.2 - y.2))) p.2 := by
    have := (((hasDerivAt_id p.2).sub_const y.2).pow 2).const_add ((p.1 - y.1) ^ 2)
    simpa using this.const_mul (-α)
  have := (h.exp).sub_const K
  convert this using 1
  · funext t; simp only [barrier, eu]
  · simp only [bar2, eu]; ring

lemma d1_bar1 (α : ℝ) (y p : ℝ × ℝ) :
    d1 (bar1 α y) p = (4 * α ^ 2 * (p.1 - y.1) ^ 2 - 2 * α) * Real.exp (-α * eu y p) := by
  refine d1_eq_of_hasDerivAt (differentiable_bar1 α y) ?_
  have h : HasDerivAt (fun t => -α * ((t - y.1) ^ 2 + (p.2 - y.2) ^ 2))
      (-α * (2 * (p.1 - y.1))) p.1 := by
    have := (((hasDerivAt_id p.1).sub_const y.1).pow 2).add_const ((p.2 - y.2) ^ 2)
    simpa using this.const_mul (-α)
  have h2 : HasDerivAt (fun t => -2 * α * (t - y.1)) (-2 * α) p.1 := by
    simpa using ((hasDerivAt_id p.1).sub_const y.1).const_mul (-2 * α)
  have := h2.mul h.exp
  convert this using 1
  · funext t; simp only [bar1, eu, Pi.mul_apply]
  · simp only [eu]; ring

lemma d2_bar2 (α : ℝ) (y p : ℝ × ℝ) :
    d2 (bar2 α y) p = (4 * α ^ 2 * (p.2 - y.2) ^ 2 - 2 * α) * Real.exp (-α * eu y p) := by
  refine d2_eq_of_hasDerivAt (differentiable_bar2 α y) ?_
  have h : HasDerivAt (fun t => -α * ((p.1 - y.1) ^ 2 + (t - y.2) ^ 2))
      (-α * (2 * (p.2 - y.2))) p.2 := by
    have := (((hasDerivAt_id p.2).sub_const y.2).pow 2).const_add ((p.1 - y.1) ^ 2)
    simpa using this.const_mul (-α)
  have h2 : HasDerivAt (fun t => -2 * α * (t - y.2)) (-2 * α) p.2 := by
    simpa using ((hasDerivAt_id p.2).sub_const y.2).const_mul (-2 * α)
  have := h2.mul h.exp
  convert this using 1
  · funext t; simp only [bar2, eu, Pi.mul_apply]
  · simp only [eu]; ring

lemma lap_barrier (α : ℝ) (y : ℝ × ℝ) (K : ℝ) (p : ℝ × ℝ) :
    lap (barrier α y K) p = (4 * α ^ 2 * eu y p - 4 * α) * Real.exp (-α * eu y p) := by
  simp only [lap, d11_eq_d1, d22_eq_d2, d1_barrier, d2_barrier, d1_bar1, d2_bar2]
  simp only [eu]; ring

lemma contDiff_barrier (α : ℝ) (y : ℝ × ℝ) (K : ℝ) : ContDiff ℝ 2 (barrier α y K) := by
  unfold barrier eu; fun_prop

lemma dist_sq_le_eu (p q : ℝ × ℝ) : dist p q ^ 2 ≤ eu q p := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  unfold eu
  rcases le_total |p.1 - q.1| |p.2 - q.2| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg (p.1 - q.1)]
  · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg (p.2 - q.2)]

lemma eu_le_dist_sq (p q : ℝ × ℝ) : eu q p ≤ 2 * dist p q ^ 2 := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  unfold eu
  have h1 : (p.1 - q.1) ^ 2 ≤ max |p.1 - q.1| |p.2 - q.2| ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
  have h2 : (p.2 - q.2) ^ 2 ≤ max |p.1 - q.1| |p.2 - q.2| ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
  linarith

lemma dist_lt_of_eu_lt {p q : ℝ × ℝ} {s : ℝ} (hs : 0 ≤ s) (h : eu q p < s ^ 2) : dist p q < s := by
  have h1 := dist_sq_le_eu p q
  by_contra h2
  push Not at h2
  nlinarith [dist_nonneg (x := p) (y := q)]

/-- The barrier inequality: `-Δh + c h < 0` on the annulus. -/
lemma barrier_neg {α R2 C e c : ℝ} (hα1 : 1 ≤ α) (hαR : 8 + 2 * C ≤ α * R2) (hC : 0 ≤ C)
    (he : R2 / 4 ≤ e) (hc0 : 0 ≤ c) (hcC : c ≤ C) :
    -((4 * α ^ 2 * e - 4 * α) * Real.exp (-α * e)) +
      c * (Real.exp (-α * e) - Real.exp (-α * R2)) < 0 := by
  have hE := Real.exp_pos (-α * e)
  have hK := Real.exp_pos (-α * R2)
  have hkey : -4 * α ^ 2 * e + 4 * α + c < 0 := by nlinarith
  nlinarith [mul_pos hE (show 0 < -(-4 * α ^ 2 * e + 4 * α + c) by linarith), mul_nonneg hc0 hK.le]

/-- **Local strong maximum principle** (Hopf). -/
theorem local_zero {u c : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hc : Continuous c)
    (hc0 : ∀ p, 0 ≤ c p) (hsup : ∀ p ∈ Sq, 0 ≤ -lap u p + c p * u p)
    (hnn : ∀ p ∈ Sq, 0 ≤ u p) {z : ℝ × ℝ} (hz : z ∈ Sq) (h0 : u z = 0) :
    u =ᶠ[𝓝 z] 0 := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  obtain ⟨r0, hr0, hr0s⟩ := Metric.isOpen_iff.mp (isOpen_Ioo.prod isOpen_Ioo) z hz
  set r := r0 / 2
  have hr : 0 < r := by positivity
  have hB : closedBall z r ⊆ Sq := (closedBall_subset_ball (by simp only [r]; linarith)).trans hr0s
  by_contra hne
  obtain ⟨y, hyu, hyb⟩ := ((Filter.not_eventually.mp hne).and_eventually
    (ball_mem_nhds z (show 0 < r / 4 by positivity))).exists
  have hyz : dist y z < r / 4 := hyb
  have hySq : y ∈ Sq := hB (mem_closedBall.mpr (by linarith))
  have hypos : 0 < u y := lt_of_le_of_ne (hnn y hySq) (Ne.symm hyu)
  -- the closest zero of `u` to `y`
  set Z' := closedBall z r ∩ {p | u p = 0}
  have hZc : IsCompact Z' :=
    (isCompact_closedBall z r).inter_right (isClosed_eq hu.continuous continuous_const)
  have hZn : Z'.Nonempty := ⟨z, mem_closedBall_self hr.le, h0⟩
  obtain ⟨x1, hx1Z, hx1min⟩ := hZc.exists_isMinOn hZn (continuous_eu y).continuousOn
  set R2 := eu y x1
  have hx1u : u x1 = 0 := hx1Z.2
  have hR2z : R2 ≤ eu y z := hx1min ⟨mem_closedBall_self hr.le, h0⟩
  have hR2small : R2 < (r / 2) ^ 2 := by
    have := eu_le_dist_sq z y
    rw [dist_comm] at hyz
    nlinarith [dist_nonneg (x := z) (y := y)]
  have hR2pos : 0 < R2 := by
    rcases (show 0 ≤ R2 by simp only [R2, eu]; positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      have : dist x1 y ^ 2 ≤ R2 := dist_sq_le_eu x1 y
      rw [← h] at this
      have hd : dist x1 y = 0 := by nlinarith [dist_nonneg (x := x1) (y := y)]
      rw [dist_eq_zero.mp hd] at hx1u
      linarith
  -- points closer to `y` than `R` lie in the small ball around `z`
  have hnear : ∀ p, eu y p ≤ R2 → dist p z < 3 * r / 4 := by
    intro p hp
    have := dist_lt_of_eu_lt (s := r / 2) (by positivity) (lt_of_le_of_lt hp hR2small)
    linarith [dist_triangle p y z]
  have hinSq : ∀ p, eu y p ≤ R2 → p ∈ Sq := fun p hp =>
    hB (mem_closedBall.mpr (by linarith [hnear p hp]))
  have hposin : ∀ p, eu y p < R2 → 0 < u p := by
    intro p hp
    refine lt_of_le_of_ne (hnn p (hinSq p hp.le)) (fun h => ?_)
    have := hx1min ⟨mem_closedBall.mpr (by linarith [hnear p hp.le]), h.symm⟩
    exact absurd this (not_le.mpr hp)
  -- `x1` is an interior minimum of `u`, so its gradient vanishes
  have hx1ball : x1 ∈ ball z r := mem_ball.mpr (by linarith [hnear x1 le_rfl])
  have hmin1 : IsLocalMin u x1 :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hx1ball) fun p hp => by
      rw [hx1u]; exact hnn p (hB (ball_subset_closedBall hp))
  have hgrad := hmin1.hasFDerivAt_eq_zero (hud x1).hasFDerivAt
  -- the annulus
  set Abar := {p | R2 / 4 ≤ eu y p ∧ eu y p ≤ R2}
  have hAc : IsCompact Abar := by
    refine (isCompact_closedBall y r).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_eu y)).inter
        (isClosed_le (continuous_eu y) continuous_const)) fun p hp => ?_
    have hd := dist_lt_of_eu_lt (s := r / 2) (by positivity) (lt_of_le_of_lt hp.2 hR2small)
    exact mem_closedBall.mpr (by linarith)
  -- the inner circle and the minimum of `u` on it
  set Cin := {p | eu y p = R2 / 4}
  have hCc : IsCompact Cin :=
    hAc.of_isClosed_subset (isClosed_eq (continuous_eu y) continuous_const)
      fun p hp => ⟨hp.ge, by rw [mem_ofPred_eq] at hp; linarith⟩
  have hCn : Cin.Nonempty := by
    refine ⟨(y.1 + Real.sqrt (R2 / 4), y.2), ?_⟩
    simp only [Cin, mem_ofPred_eq, eu, add_sub_cancel_left, sub_self]
    rw [Real.sq_sqrt (by positivity)]; ring
  obtain ⟨pm, hpmC, hpmmin⟩ := hCc.exists_isMinOn hCn hu.continuous.continuousOn
  set m := u pm
  have hm : 0 < m := hposin pm (by rw [hpmC]; linarith)
  set ε := m / 2
  have hε : 0 < ε := by positivity
  -- the bound on `c`
  obtain ⟨C0, hC0⟩ := hAc.exists_bound_of_continuousOn hc.continuousOn
  set C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hcC : ∀ p ∈ Abar, c p ≤ C := fun p hp =>
    ((le_abs_self (c p)).trans (by simpa [Real.norm_eq_abs] using hC0 p hp)).trans
      (le_max_left _ _)
  set α := max 1 ((8 + 2 * C) / R2)
  have hα1 : 1 ≤ α := le_max_left _ _
  have hαR : 8 + 2 * C ≤ α * R2 := by
    have := le_max_right 1 ((8 + 2 * C) / R2)
    rw [div_le_iff₀ hR2pos] at this
    exact this
  set K := Real.exp (-α * R2)
  set h := barrier α y K
  set w : ℝ × ℝ → ℝ := fun p => u p - ε * h p
  have hw : ContDiff ℝ 2 w := hu.sub (contDiff_const.mul (contDiff_barrier α y K))
  have hlapw : ∀ p, lap w p = lap u p - ε * lap h p := fun p =>
    lap_sub_mul hud (differentiable_barrier α y K)
      ((contDiff_d1 hu).differentiable one_ne_zero)
      (by rw [d1_barrier]; exact differentiable_bar1 α y)
      ((contDiff_d2 hu).differentiable one_ne_zero)
      (by rw [d2_barrier]; exact differentiable_bar2 α y) ε p
  have hh1 : ∀ p, h p ≤ 1 := by
    intro p
    have : Real.exp (-α * eu y p) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ eu y p := by simp only [eu]; positivity
      nlinarith
    simp only [h, barrier]; linarith [Real.exp_pos (-α * R2)]
  -- weak comparison on the annulus
  have hcomp : ∀ p ∈ Abar, 0 ≤ w p := by
    obtain ⟨q, hqA, hqmin⟩ := hAc.exists_isMinOn ⟨pm, by rw [mem_ofPred_eq, hpmC]; constructor <;>
      linarith⟩ hw.continuous.continuousOn
    intro p hp
    refine le_trans ?_ (hqmin hp)
    by_contra hneg
    push Not at hneg
    rcases hqA.1.lt_or_eq with hlo | hlo
    · rcases hqA.2.lt_or_eq with hhi | hhi
      · -- interior point: a local minimum of `w`
        have hopen : IsOpen {p | R2 / 4 < eu y p ∧ eu y p < R2} :=
          (isOpen_lt continuous_const (continuous_eu y)).inter
            (isOpen_lt (continuous_eu y) continuous_const)
        have hlmin : IsLocalMin w q :=
          Filter.eventually_of_mem (hopen.mem_nhds ⟨hlo, hhi⟩) fun p hp =>
            hqmin ⟨hp.1.le, hp.2.le⟩
        have h11 := d11_nonneg_of_isLocalMin hw hlmin
        have h22 := d22_nonneg_of_isLocalMin hw hlmin
        have hqSq := hinSq q hqA.2
        have hLu := hsup q hqSq
        have hbar := barrier_neg (c := c q) (e := eu y q) hα1 hαR hC hqA.1 (hc0 q) (hcC q hqA)
        rw [← lap_barrier α y K q] at hbar
        have hlap : lap w q = d11 w q + d22 w q := rfl
        rw [hlapw q] at hlap
        have hwq : w q = u q - ε * h q := rfl
        have hhq : h q = Real.exp (-α * eu y q) - Real.exp (-α * R2) := rfl
        rw [← hhq] at hbar
        nlinarith [hc0 q]
      · -- outer circle: `h = 0`
        have : h q = 0 := by simp only [h, barrier, K, hhi, sub_self]
        have := hnn q (hinSq q hqA.2)
        simp only [w] at hneg
        rw [‹h q = 0›] at hneg
        linarith
    · -- inner circle: `u ≥ m > ε ≥ ε h`
      have hq' : q ∈ Cin := hlo.symm
      have := hpmmin hq'
      have := hh1 q
      simp only [w] at hneg
      have e2 : m ≤ u q := ‹u pm ≤ u q›
      have e1 : ε * h q ≤ ε := mul_le_of_le_one_right hε.le (hh1 q)
      have e3 : ε = m / 2 := rfl
      linarith
  -- Hopf: `u` grows linearly from `x1` towards `y`, contradicting `∇u(x1) = 0`
  set d := y - x1
  set κ := ε * K * (α * R2)
  have hκ : 0 < κ := by positivity
  have hlin : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), κ * t ≤ u (x1 + t • d) := by
    intro t ht
    have heu : eu y (x1 + t • d) = (1 - t) ^ 2 * R2 := by
      simp only [eu, R2, d, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      ring
    have hA : x1 + t • d ∈ Abar := by
      rw [mem_ofPred_eq, heu]
      have ha : 1 / 4 ≤ (1 - t) ^ 2 := by nlinarith [ht.1, ht.2]
      have hb : (1 - t) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right ha hR2pos.le]
      · nlinarith [mul_le_mul_of_nonneg_right hb hR2pos.le]
    have hwge := hcomp _ hA
    simp only [w, h, barrier] at hwge
    rw [heu] at hwge
    -- `e^a - e^b ≥ e^b (a - b)`
    have hexp : K * (α * R2 * t) ≤ Real.exp (-α * ((1 - t) ^ 2 * R2)) - K := by
      have h1 := Real.add_one_le_exp (-α * ((1 - t) ^ 2 * R2) - -α * R2)
      have h2 : Real.exp (-α * ((1 - t) ^ 2 * R2)) =
          K * Real.exp (-α * ((1 - t) ^ 2 * R2) - -α * R2) := by
        simp only [K]; rw [← Real.exp_add]; ring_nf
      rw [h2]
      have hK : 0 < K := Real.exp_pos _
      have hge : α * R2 * t ≤ -α * ((1 - t) ^ 2 * R2) - -α * R2 := by
        have key : -α * ((1 - t) ^ 2 * R2) - -α * R2 - α * R2 * t =
            α * R2 * (t * (1 - t)) := by ring
        have hnn' : 0 ≤ α * R2 * (t * (1 - t)) :=
          mul_nonneg (mul_nonneg (by linarith) hR2pos.le)
            (mul_nonneg ht.1.le (by linarith [ht.2]))
        linarith
      nlinarith
    nlinarith
  -- little-o at `x1`
  have hfd : HasFDerivAt u (0 : ℝ × ℝ →L[ℝ] ℝ) x1 := by
    rw [← hgrad]; exact (hud x1).hasFDerivAt
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hfd
  set η := κ / (2 * (‖d‖ + 1))
  have hη : 0 < η := by positivity
  have hev := hlo.def hη
  have htend : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 ((0 : ℝ) • d)) :=
      (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const d
    rwa [zero_smul] at h
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hev)
  set t := min (δ / 2) (1 / 2)
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb := hδb htδ
  simp only [hx1u, zero_apply, sub_zero, Real.norm_eq_abs] at hb
  have hl := hlin t ⟨ht0, min_le_right _ _⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
  have hu_le : u (x1 + t • d) ≤ η * (t * ‖d‖) := (le_abs_self _).trans hb
  have : η * (t * ‖d‖) < κ * t := by
    simp only [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg d, mul_pos hκ ht0, mul_nonneg (mul_pos hκ ht0).le (norm_nonneg d)]
  linarith

/-- **Hopf's strong maximum principle on the square.** A nonnegative `C²` supersolution of
`-Δ + c` (`c ≥ 0` continuous) on the open square that vanishes at one interior point vanishes on
the whole square. -/
theorem strong_max_principle {u c : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hc : Continuous c)
    (hc0 : ∀ p, 0 ≤ c p) (hsup : ∀ p ∈ Sq, 0 ≤ -lap u p + c p * u p)
    (hnn : ∀ p ∈ Sq, 0 ≤ u p) {p0 : ℝ × ℝ} (hp0 : p0 ∈ Sq) (h0 : u p0 = 0) :
    ∀ p ∈ Sq, u p = 0 := by
  set A := {p | u =ᶠ[𝓝 p] 0}
  set B := {p | u p ≠ 0}
  have hA : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hBo : IsOpen B := isOpen_ne_fun hu.continuous continuous_const
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro p ⟨hpA, hpB⟩
    exact hpB hpA.self_of_nhds
  have hcover : Sq ⊆ A ∪ B := by
    intro p hp
    by_cases hz : u p = 0
    · exact Or.inl (local_zero hu hc hc0 hsup hnn hp hz)
    · exact Or.inr hz
  have hconn : IsPreconnected Sq := ((convex_Ioo 0 1).prod (convex_Ioo 0 1)).isPreconnected
  have hsub := hconn.subset_left_of_subset_union hA hBo hdisj hcover
    ⟨p0, hp0, local_zero hu hc hc0 hsup hnn hp0 h0⟩
  exact fun p hp => (hsub hp).self_of_nhds

end Pair

end Continuum

end DFT
