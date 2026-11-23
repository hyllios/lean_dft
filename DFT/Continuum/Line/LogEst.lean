/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.AbsW

/-!
# The logarithmic estimate for nonnegative ground states

Let `u ≥ 0` be a bosonic `H¹₀` ground state with energy `E`, and `|V - E| ≤ C` a.e.
(`V = Σ v(x_k) + w`). For every exchange-symmetric `C¹` cutoff `η` vanishing on the walls and every
`ε > 0`,

`Σ_k ∫ η² (∂ₖu / (u + ε))² ≤ 4 Σ_k ∫ (∂ₖη)² + 2C ∫ η²`   (`log_estimate`),

uniformly in `ε`: the gradient of `log(u + ε)` is locally bounded in `L²`. This is Moser's
estimate, obtained by testing the weak Schrödinger equation with `η²/(u + ε)`.

* `dk_mul`, `IsWD.mul_C1`: the product rule with a `C¹` function.
* `oddExt`, `hasDerivAt_oddExt`: odd extensions of functions on `[0, ∞)`, used to apply the chain
  rule to `1/(u + ε)` (and later `log(1 + u/ε)`) with bounded derivatives.
* `Gr`: `Gr ε t = 1/ε - 1/(t + ε)` for `t ≥ 0`.
* **`log_estimate`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat}

/-! ### The product rule -/

lemma dk_mul {a b : Cfg n → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (k : Fin (n + 1)) (x : Cfg n) :
    dk k (fun y => a y * b y) x = a x * dk k b x + dk k a x * b x := by
  have h := fderiv_mul (ha x) (hb x)
  simp only [dk]
  rw [show (fun y => a y * b y) = a * b from rfl, h]
  simp [mul_comm]

/-- **The product rule** with a `C¹` function. -/
lemma IsWD.mul_C1 {k : Fin (n + 1)} {f G : Cfg n → ℝ} (h : IsWD k f G) (hf : MemLp f 2 (μN n))
    {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ) :
    IsWD k (fun x => ζ x * f x) (fun x => ζ x * G x + dk k ζ x * f x) := by
  have hdζ := continuous_dk_of_C1 hζ k
  refine ⟨(memLp_mul_cont hζ.continuous h.1).add (memLp_mul_cont hdζ hf), fun φ hφ => ?_⟩
  have hd := continuous_dk_of_C1 hφ k
  have hζφ : ContDiff ℝ 1 (fun x => ζ x * φ x) := hζ.mul hφ
  have h1 := h.2 _ hζφ
  have hprod : ∀ x, dk k (fun y => ζ y * φ y) x = ζ x * dk k φ x + dk k ζ x * φ x :=
    dk_mul (hζ.differentiable one_ne_zero) (hφ.differentiable one_ne_zero) k
  simp only [hprod] at h1
  have i1 : Integrable (fun x => f x * (ζ x * dk k φ x)) (μN n) :=
    int_mul_cont hf (hζ.continuous.mul hd)
  have i2 : Integrable (fun x => f x * (dk k ζ x * φ x)) (μN n) :=
    int_mul_cont hf (hdζ.mul hφ.continuous)
  have i3 : Integrable (fun x => G x * (ζ x * φ x)) (μN n) := int_mul_cont h.1 hζφ.continuous
  have e1 : ∫ x, f x * (ζ x * dk k φ x + dk k ζ x * φ x) ∂μN n =
      ∫ x, f x * (ζ x * dk k φ x) ∂μN n + ∫ x, f x * (dk k ζ x * φ x) ∂μN n := by
    rw [← integral_add i1 i2]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e1] at h1
  have e2 : ∫ x, ζ x * f x * dk k φ x ∂μN n = ∫ x, f x * (ζ x * dk k φ x) ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have e3 : ∫ x, (ζ x * G x + dk k ζ x * f x) * φ x ∂μN n =
      ∫ x, G x * (ζ x * φ x) ∂μN n + ∫ x, f x * (dk k ζ x * φ x) ∂μN n := by
    rw [← integral_add i3 i2]; exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e2, e3]
  linarith

/-! ### Odd extensions -/

/-- The odd extension of `g` from `[0, ∞)`. -/
noncomputable def oddExt (g : ℝ → ℝ) (t : ℝ) : ℝ := if 0 ≤ t then g t else -g (-t)

lemma oddExt_of_nonneg (g : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) : oddExt g t = g t := by
  simp [oddExt, ht]

/-- The odd extension of a function with `g 0 = 0`, differentiable on a neighbourhood of
`[0, ∞)`, has derivative `g'(|t|)` everywhere. -/
lemma hasDerivAt_oddExt {g g' : ℝ → ℝ} (hg0 : g 0 = 0)
    (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t) (t : ℝ) : HasDerivAt (oddExt g) (g' |t|) t := by
  have hneg : ∀ s, 0 ≤ s → HasDerivAt (fun r => -g (-r)) (g' s) (-s) := fun s hs => by
    have h := (HasDerivAt.comp_of_eq (-s) (hg s hs) (hasDerivAt_neg (-s)) (by simp)).neg
    convert h using 1
    · funext r; simp
    · ring
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have h := hneg (-t) (by linarith)
    rw [neg_neg] at h
    rw [abs_of_neg ht]
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp [oddExt, not_le.2 (show s < 0 from hs)]
  · subst ht
    rw [abs_zero, ← hasDerivWithinAt_univ, ← Iic_union_Ici (a := (0 : ℝ))]
    refine HasDerivWithinAt.union ?_ ?_
    · have h := (hneg 0 le_rfl).hasDerivWithinAt (s := Iic 0)
      rw [neg_zero] at h
      refine h.congr (fun s hs => ?_) (by simp [oddExt, hg0])
      by_cases h0 : s = 0
      · subst h0; simp [oddExt, hg0]
      · simp [oddExt, not_le.2 (lt_of_le_of_ne hs h0)]
    · exact (hg 0 le_rfl).hasDerivWithinAt.congr (fun s hs => oddExt_of_nonneg g hs)
        (oddExt_of_nonneg g le_rfl)
  · rw [abs_of_pos ht]
    refine (hg t ht.le).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact oddExt_of_nonneg g (le_of_lt hs)

/-- `Gr ε t = 1/ε - 1/(t + ε)` on `[0, ∞)`, extended oddly. -/
noncomputable def Gr (ε : ℝ) : ℝ → ℝ := oddExt fun t => 1 / ε - 1 / (t + ε)

section Gr

variable {ε : ℝ} (hε : 0 < ε)
include hε

lemma hasDerivAt_Gr (t : ℝ) : HasDerivAt (Gr ε) (1 / (|t| + ε) ^ 2) t := by
  refine hasDerivAt_oddExt (g' := fun s => 1 / (s + ε) ^ 2) (by simp) (fun s hs => ?_) t
  have hne : s + ε ≠ 0 := by positivity
  have h := ((hasDerivAt_id s).add_const ε).inv hne
  have h2 := (h.const_sub (1 / ε))
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun r => by simp)
  simp [id]; field_simp

lemma continuous_Gr' : Continuous fun t : ℝ => 1 / (|t| + ε) ^ 2 :=
  continuous_const.div ((continuous_abs.add continuous_const).pow 2) fun t => by positivity

lemma Gr'_le (t : ℝ) : |1 / (|t| + ε) ^ 2| ≤ 1 / ε ^ 2 := by
  rw [abs_of_pos (by positivity)]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ hε.le (by linarith [abs_nonneg t]) 2)

omit hε in
lemma Gr_zero : Gr ε 0 = 0 := by simp [Gr, oddExt]

omit hε in
lemma Gr_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Gr ε t = 1 / ε - 1 / (t + ε) :=
  oddExt_of_nonneg _ ht

lemma abs_Gr_le (t : ℝ) : |Gr ε t| ≤ 1 / ε := by
  have key : ∀ s, 0 ≤ s → 0 ≤ 1 / ε - 1 / (s + ε) ∧ 1 / ε - 1 / (s + ε) ≤ 1 / ε := fun s hs =>
    ⟨sub_nonneg.2 (one_div_le_one_div_of_le hε (by linarith)),
      sub_le_self _ (by positivity)⟩
  simp only [Gr, oddExt]
  split_ifs with h
  · rw [abs_of_nonneg (key t h).1]; exact (key t h).2
  · rw [abs_neg, abs_of_nonneg (key (-t) (by linarith)).1]; exact (key (-t) (by linarith)).2

end Gr

/-! ### The estimate -/

section estimate

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {u : Cfg n → ℝ}

/-- The test function of the logarithmic estimate, `η² (1/ε - Gr_ε(u))` (`= η²/(u+ε)` where
`u ≥ 0`). -/
noncomputable def logTest (η u : Cfg n → ℝ) (ε : ℝ) (x : Cfg n) : ℝ :=
  ε⁻¹ * (η x * η x) + (-1) * (η x * η x * Gr ε (u x))

/-- **The logarithmic estimate, from the weak equation.** Let `u ≥ 0` be a symmetric `H¹₀`
function satisfying the weak Schrödinger equation with eigenvalue `E` against the single test
function `logTest η u ε`, where `|E - V| ≤ C` a.e. and `η ∈ C¹` vanishes on the walls. Then
`Σ_k ∫ η² (∂ₖu/(u+ε))² ≤ 4 Σ_k ∫ (∂ₖη)² + 2C ∫ η²`. -/
theorem log_estimate_of_eq (hw : Continuous w) (hD : H1W u)
    (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η)
    (hηw : ∀ x k, (x k = 0 ∨ x k = 1) → η x = 0) {ε : ℝ} (hε : 0 < ε) {E C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂μN n, |E - (LN n v x + w x)| ≤ C)
    (hel : h0W n w u (logTest η u ε) + ∫ x, LN n v x * (u x * logTest η u ε x) ∂μN n =
      E * ∫ x, u x * logTest η u ε x ∂μN n) :
    ∑ k, ∫ x, (η x * (dW k u x / (u x + ε))) ^ 2 ∂μN n ≤
      4 * ∑ k, ∫ x, dk k η x ^ 2 ∂μN n + 2 * C * ∫ x, η x ^ 2 ∂μN n := by
  have hum := hD.1
  set ζ : Cfg n → ℝ := fun x => η x * η x with hζdef
  have hζ : ContDiff ℝ 1 ζ := hη.mul hη
  have hζw : ∀ x k, (x k = 0 ∨ x k = 1) → ζ x = 0 := fun x k h => by simp [ζ, hηw x k h]
  have hdζ : ∀ k x, dk k ζ x = 2 * η x * dk k η x := fun k x => by
    rw [dk_mul (hη.differentiable one_ne_zero) (hη.differentiable one_ne_zero)]; ring
  have hGc : Continuous (Gr ε) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_Gr hε t).continuousAt
  set g : Cfg n → ℝ := fun x => Gr ε (u x)
  have hgL : MemLp g 2 (μN n) := MemLp.of_bound (hGc.comp_aestronglyMeasurable
    hum.aestronglyMeasurable) (1 / ε) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact abs_Gr_le hε _)
  have hg : ∀ k, IsWD k g (fun x => 1 / (|u x| + ε) ^ 2 * dW k u x) := fun k =>
    isWD_comp hD (hasDerivAt_Gr hε) (continuous_Gr' hε) (Gr'_le hε) Gr_zero k
  set φ : Cfg n → ℝ := fun x => ε⁻¹ * ζ x + (-1) * (ζ x * g x)
  have hφe : logTest η u ε = φ := rfl
  rw [hφe] at hel
  have hL1 : MemLp (fun x => ε⁻¹ * ζ x) 2 (μN n) := memLp_cont (continuous_const.mul hζ.continuous)
  have hL2 : MemLp (fun x => -1 * (ζ x * g x)) 2 (μN n) :=
    (memLp_mul_cont hζ.continuous hgL).const_mul (-1)
  have hφL : MemLp φ 2 (μN n) := hL1.add hL2
  have hφWD : ∀ k, IsWD k φ (fun x => ε⁻¹ * dk k ζ x +
      (-1) * (ζ x * (1 / (|u x| + ε) ^ 2 * dW k u x) + dk k ζ x * g x)) := fun k =>
    IsWD.add hL1 hL2 ((isWD_of_C1 hζ hζw k).const_mul ε⁻¹)
      (((hg k).mul_C1 hgL hζ).const_mul (-1))
  simp only [h0W] at hel
  -- bounds
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  set A : Fin (n + 1) → Cfg n → ℝ := fun k x => η x * (dW k u x / (u x + ε))
  have hAL : ∀ k, MemLp (A k) 2 (μN n) := fun k => by
    refine (dW_spec (hD.2 k)).1.of_le_mul (c := Bη / ε) (hη.continuous.aemeasurable.mul
      ((dW_spec (hD.2 k)).1.aestronglyMeasurable.aemeasurable.div
        (hum.aestronglyMeasurable.aemeasurable.add_const ε))).aestronglyMeasurable ?_
    filter_upwards [hBη, hu0] with x hx h0
    have hp : 0 < u x + ε := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at *
    simp only [A, abs_mul, abs_div, abs_of_pos hp]
    rw [mul_div_assoc', div_le_iff₀ hp]
    have h1 : |η x| * |dW k u x| ≤ Bη * |dW k u x| :=
      mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have h2 : Bη / ε * |dW k u x| * ε ≤ Bη / ε * |dW k u x| * (u x + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (div_nonneg ((abs_nonneg _).trans hx)
        hε.le) (abs_nonneg _))
    have h3 : Bη / ε * |dW k u x| * ε = Bη * |dW k u x| := by field_simp
    linarith
  have hdη : ∀ k, Continuous (dk k η) := fun k => continuous_dk_of_C1 hη k
  -- the pointwise identity
  have hpt : ∀ k, ∀ᵐ x ∂μN n, dW k u x * dW k φ x = 2 * (A k x * dk k η x) - A k x ^ 2 := by
    intro k
    filter_upwards [dW_ae_eq (hφWD k), hu0] with x hx h0
    have hp : 0 < u x + ε := by linarith
    rw [hx]
    simp only [A, hdζ, g, ζ, Gr_of_nonneg h0, abs_of_nonneg h0]
    field_simp
    ring
  have hk : ∀ k, ∫ x, dW k u x * dW k φ x ∂μN n =
      2 * ∫ x, A k x * dk k η x ∂μN n - ∫ x, A k x ^ 2 ∂μN n := fun k => by
    rw [integral_congr_ae (hpt k), integral_sub ((int_mul_cont (hAL k) (hdη k)).const_mul 2)
      (hAL k).integrable_sq, integral_const_mul]
  -- the right side of the equation
  have huφ : MemLp (fun x => u x * φ x) 2 (μN n) := by
    obtain ⟨Bφ, hBφ⟩ : ∃ B, ∀ᵐ x ∂μN n, |φ x| ≤ B := by
      refine ⟨2 * Bη ^ 2 / ε, ?_⟩
      filter_upwards [hBη] with x hx
      rw [Real.norm_eq_abs] at hx
      have hz : |ζ x| ≤ Bη ^ 2 := by
        simp only [ζ, abs_mul]; nlinarith [abs_nonneg (η x)]
      have hgb := abs_Gr_le hε (u x)
      have e : φ x = ζ x * (ε⁻¹ - g x) := by simp only [φ]; ring
      rw [e, abs_mul]
      calc |ζ x| * |ε⁻¹ - g x| ≤ Bη ^ 2 * (2 / ε) := by
            refine mul_le_mul hz ?_ (abs_nonneg _) ((abs_nonneg _).trans hz)
            calc |ε⁻¹ - g x| ≤ |ε⁻¹| + |g x| := abs_sub _ _
              _ ≤ 2 / ε := by
                rw [abs_of_pos (inv_pos.2 hε)]
                have : (1 : ℝ) / ε = ε⁻¹ := one_div ε
                rw [this] at hgb
                change |g x| ≤ ε⁻¹ at hgb
                have h2 : 2 / ε = 2 * ε⁻¹ := by ring
                linarith
        _ = 2 * Bη ^ 2 / ε := by ring
    exact hum.of_le_mul (c := Bφ) (hum.aestronglyMeasurable.mul hφL.aestronglyMeasurable)
      (by filter_upwards [hBφ] with x hx
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  have hR : ∑ k, ∫ x, dW k u x * dW k φ x ∂μN n =
      ∫ x, (E - (LN n v x + w x)) * (u x * φ x) ∂μN n := by
    have i1 : Integrable (fun x => u x * φ x) (μN n) := int_mul_L2 hum hφL
    have i2 : Integrable (fun x => w x * (u x * φ x)) (μN n) := by
      simpa only [mul_comm] using int_mul_cont huφ hw
    have i3 : Integrable (fun x => LN n v x * (u x * φ x)) (μN n) := by
      simpa only [mul_comm] using int_mul_cont huφ (continuous_LN v)
    have e : ∫ x, (E - (LN n v x + w x)) * (u x * φ x) ∂μN n =
        E * ∫ x, u x * φ x ∂μN n - ∫ x, w x * (u x * φ x) ∂μN n -
          ∫ x, LN n v x * (u x * φ x) ∂μN n := by
      have e1 : ∫ x, (E - (LN n v x + w x)) * (u x * φ x) ∂μN n =
          ∫ x, (E * (u x * φ x) - w x * (u x * φ x)) - LN n v x * (u x * φ x) ∂μN n :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
      rw [e1, integral_sub (f := fun x => E * (u x * φ x) - w x * (u x * φ x))
        (g := fun x => LN n v x * (u x * φ x)) ((i1.const_mul E).sub i2) i3,
        integral_sub (f := fun x => E * (u x * φ x)) (g := fun x => w x * (u x * φ x))
        (i1.const_mul E) i2, integral_const_mul]
    rw [e]; linarith
  have hRlow : -(C * ∫ x, η x ^ 2 ∂μN n) ≤ ∫ x, (E - (LN n v x + w x)) * (u x * φ x) ∂μN n := by
    have hiR : Integrable (fun x => (E - (LN n v x + w x)) * (u x * φ x)) (μN n) := by
      have hc : Continuous fun x => E - (LN n v x + w x) :=
        continuous_const.sub ((continuous_LN v).add hw)
      simpa only [mul_comm] using int_mul_cont huφ hc
    rw [← integral_const_mul, ← integral_neg]
    refine integral_mono_ae ((integrableN (hη.continuous.pow 2)).const_mul C).neg hiR ?_
    filter_upwards [hC, hu0] with x hx h0
    have hp : 0 < u x + ε := by linarith
    have hφx : φ x = ζ x / (u x + ε) := by
      simp only [φ, g, ζ, Gr_of_nonneg h0]
      field_simp; ring
    have hb1 : 0 ≤ u x * φ x := by
      rw [hφx]; exact mul_nonneg h0 (div_nonneg (mul_self_nonneg _) hp.le)
    have hb2 : u x * φ x ≤ η x ^ 2 := by
      rw [hφx, mul_div_assoc', div_le_iff₀ hp]
      have : 0 ≤ ζ x := mul_self_nonneg _
      simp only [ζ] at this ⊢; nlinarith
    have h3 := neg_abs_le (E - (LN n v x + w x))
    nlinarith [mul_le_mul_of_nonneg_right hx hb1]
  have hAB : ∀ k, ∫ x, A k x * dk k η x ∂μN n ≤
      (1 / 4) * ∫ x, A k x ^ 2 ∂μN n + ∫ x, dk k η x ^ 2 ∂μN n := fun k => by
    rw [← integral_const_mul, ← integral_add (f := fun x => 1 / 4 * A k x ^ 2)
      (g := fun x => dk k η x ^ 2) ((hAL k).integrable_sq.const_mul _)
      (integrableN ((hdη k).pow 2))]
    refine integral_mono (int_mul_cont (hAL k) (hdη k))
      (((hAL k).integrable_sq.const_mul _).add (integrableN ((hdη k).pow 2))) fun x => ?_
    nlinarith [sq_nonneg (A k x - 2 * dk k η x)]
  -- combine
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hAB k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hid : ∑ k, ∫ x, dW k u x * dW k φ x ∂μN n =
      2 * ∑ k, ∫ x, A k x * dk k η x ∂μN n - ∑ k, ∫ x, A k x ^ 2 ∂μN n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hk k
  change ∑ k, ∫ x, A k x ^ 2 ∂μN n ≤ _
  linarith

omit hw in
/-- The test function `logTest η u ε` is in `H¹`. -/
lemma h1W_logTest (hD : H1W u) {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η)
    (hηw : ∀ x k, (x k = 0 ∨ x k = 1) → η x = 0) {ε : ℝ} (hε : 0 < ε) :
    H1W (logTest η u ε) := by
  have hζ : ContDiff ℝ 1 fun x => η x * η x := hη.mul hη
  have hζw : ∀ x k, (x k = 0 ∨ x k = 1) → η x * η x = 0 := fun x k h => by simp [hηw x k h]
  have hGc : Continuous (Gr ε) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_Gr hε t).continuousAt
  have hgL : MemLp (fun x => Gr ε (u x)) 2 (μN n) := MemLp.of_bound
    (hGc.comp_aestronglyMeasurable hD.1.aestronglyMeasurable) (1 / ε)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_Gr_le hε _)
  have hL1 : MemLp (fun x => ε⁻¹ * (η x * η x)) 2 (μN n) :=
    memLp_cont (continuous_const.mul hζ.continuous)
  have hL2 : MemLp (fun x => -1 * (η x * η x * Gr ε (u x))) 2 (μN n) :=
    (memLp_mul_cont hζ.continuous hgL).const_mul (-1)
  exact ⟨hL1.add hL2, fun k => ⟨_, IsWD.add hL1 hL2 ((isWD_of_C1 hζ hζw k).const_mul ε⁻¹)
    (((isWD_comp hD (hasDerivAt_Gr hε) (continuous_Gr' hε) (Gr'_le hε) Gr_zero
      k).mul_C1 hgL hζ).const_mul (-1))⟩⟩

/-- **The logarithmic estimate.** For a nonnegative bosonic `H¹₀` ground state `u`, with
`|E - V| ≤ C` a.e., and a symmetric `C¹` cutoff `η` vanishing on the walls,
`Σ_k ∫ η² (∂ₖu/(u+ε))² ≤ 4 Σ_k ∫ (∂ₖη)² + 2C ∫ η²` for every `ε > 0`. -/
theorem log_estimate (hu : IsGS (settingW .bos n w hw) v u) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η) (hηs : ∀ σ x, η (pm σ x) = η x)
    (hηw : ∀ x k, (x k = 0 ∨ x k = 1) → η x = 0) {ε : ℝ} (hε : 0 < ε) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂μN n,
      |Q (settingW .bos n w hw) v u / ip (μ := μN n) u u - (LN n v x + w x)| ≤ C) :
    ∑ k, ∫ x, (η x * (dW k u x / (u x + ε))) ^ 2 ∂μN n ≤
      4 * ∑ k, ∫ x, dk k η x ^ 2 ∂μN n + 2 * C * ∫ x, η x ^ 2 ∂μN n := by
  have hD : u ∈ DomW .bos n := hu.1
  have hφD : logTest η u ε ∈ DomW .bos n := by
    refine ⟨(h1W_logTest (h1W_of_mem hD) hη hηw hε).1, (h1W_logTest (h1W_of_mem hD) hη hηw hε).2,
      fun σ => ?_⟩
    filter_upwards [hD.2.2 σ] with x hx
    simp only [ch_bos, one_mul] at hx ⊢
    simp only [logTest, hηs, hx]
  exact log_estimate_of_eq hw (h1W_of_mem hD) hu0 hη hηw hε hC0 hC (euler_lagrange hu hφD)

end estimate

end DFT.Continuum.Line
