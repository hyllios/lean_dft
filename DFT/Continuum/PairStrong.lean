/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.PairFree

/-!
# Ground states of two interacting bosons are classical solutions

For two bosons in the box with a symmetric continuous interaction `w`, every ground state `Φ` of
the potential `v` solves the Schrödinger equation pointwise on the open square:
`-ΔΦ + (w + v(x₁) + v(x₂) - E) Φ = 0`, with `E = ⟨Φ, HΦ⟩ / ⟨Φ, Φ⟩`.

* `eq_zero_of_integral_sym`: fundamental lemma for symmetric continuous functions, tested against
  the symmetric form domain.
* `ibp1`, `ibp2`: integration by parts, slice by slice: `∫ ∂₁Φ ∂₁φ = -∫ ∂₁₁Φ φ` (and for `x₂`).
* `d11_swap`, `d22_swap`: for symmetric `Φ`, `∂₁₁Φ(x, y) = ∂₂₂Φ(y, x)`.
* `strong_eq`: the strong Schrödinger equation.
-/

namespace DFT

namespace Continuum

namespace Pair

open MeasureTheory Set Filter Topology Box

/-- **Fundamental lemma with symmetric test functions.** -/
lemma eq_zero_of_integral_sym {g : ℝ × ℝ → ℝ} (hg : Continuous g) (hgs : ∀ p, g p.swap = g p)
    (h : ∀ φ ∈ Dom2 1, ∫ p, g p * φ p ∂μ2 = 0) : ∀ p ∈ Sq, g p = 0 := by
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Sq) (μ := volume)
    (f := g) (isOpen_Ioo.prod isOpen_Ioo) (hg.locallyIntegrable.locallyIntegrableOn _)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Sq) => ?_)
  · have h' : g =ᵐ[μ2] 0 := (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 hae
    exact Measure.eqOn_open_of_ae_eq h' (isOpen_Ioo.prod isOpen_Ioo) hg.continuousOn
      continuousOn_const
  have hout : ∀ p, p ∉ Sq → φ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport fun h' => hp (hsub h')
  set φs : ℝ × ℝ → ℝ := fun p => φ p + 1 * φ p.swap
  have hφs : φs ∈ Dom2 1 := by
    refine ⟨(hφ.of_le (WithTop.coe_le_coe.mpr le_top)).add
      (contDiff_const.mul ((hφ.of_le (WithTop.coe_le_coe.mpr le_top)).comp
        (contDiff_snd.prodMk contDiff_fst))),
      fun p => ?_, fun y => ?_, fun y => ?_⟩
    · simp only [φs, Prod.swap_swap]; ring
    · simp only [φs, Prod.swap_prod_mk]
      rw [hout (0, y) (fun h => lt_irrefl _ h.1.1), hout (y, 0) (fun h => lt_irrefl _ h.2.1)]
      ring
    · simp only [φs, Prod.swap_prod_mk]
      rw [hout (1, y) (fun h => lt_irrefl _ h.1.2), hout (y, 1) (fun h => lt_irrefl _ h.2.2)]
      ring
  have h1 := h φs hφs
  have ig := integrable2 (hg.mul (hφ.continuous))
  have ig' := integrable2 (hg.mul (hφ.continuous.comp continuous_swap))
  have hsw : ∫ p, g p * φ p.swap ∂μ2 = ∫ p, g p * φ p ∂μ2 := by
    have := integral_swap (fun p => g p.swap * φ p)
    simp only [Prod.swap_swap] at this
    rw [this]
    congr 1; funext p; rw [hgs p]
  have hsplit : ∫ p, g p * φs p ∂μ2 = ∫ p, g p * φ p ∂μ2 + ∫ p, g p * φ p.swap ∂μ2 := by
    rw [← integral_add (f := fun p => g p * φ p) (g := fun p => g p * φ p.swap) ig ig']
    congr 1; funext p; simp only [φs]; ring
  rw [hsplit, hsw] at h1
  have hμ : ∫ p, g p * φ p ∂μ2 = 0 := by linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Sq)]
  · simpa [smul_eq_mul, mul_comm] using hμ
  · intro p hp; rw [hout p hp, zero_smul]

section derivs

variable {Φ : ℝ × ℝ → ℝ}

lemma hasDerivAt_d1_slice (h : ContDiff ℝ 2 Φ) (x y : ℝ) :
    HasDerivAt (fun x => d1 Φ (x, y)) (d11 Φ (x, y)) x := by
  have h' := ((contDiff_d1 h).differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  exact h'

lemma hasDerivAt_d2_slice (h : ContDiff ℝ 2 Φ) (x y : ℝ) :
    HasDerivAt (fun y => d2 Φ (x, y)) (d22 Φ (x, y)) y := by
  have h' := ((contDiff_d2 h).differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  exact h'

lemma hasDerivAt_slice1 (h : Φ ∈ Dom2 1) (x y : ℝ) :
    HasDerivAt (fun x => Φ (x, y)) (d1 Φ (x, y)) x := by
  have h' := (diff2 h (x, y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  exact h'

lemma hasDerivAt_slice2 (h : Φ ∈ Dom2 1) (x y : ℝ) :
    HasDerivAt (fun y => Φ (x, y)) (d2 Φ (x, y)) y := by
  have h' := (diff2 h (x, y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  exact h'

/-- For symmetric `Φ`, `∂₁Φ(x, y) = ∂₂Φ(y, x)`. -/
lemma d1_swap (h : Φ ∈ Dom2 1) (x y : ℝ) : d1 Φ (x, y) = d2 Φ (y, x) := by
  have he : (fun t => Φ (t, y)) = fun t => Φ (y, t) := by
    funext t; have := h.2.1 (y, t); simp only [Prod.swap_prod_mk, one_mul] at this; exact this
  rw [← (hasDerivAt_slice1 h x y).deriv, ← (hasDerivAt_slice2 h y x).deriv, he]

/-- For symmetric `Φ`, `∂₁₁Φ(x, y) = ∂₂₂Φ(y, x)`. -/
lemma d11_swap (h : Φ ∈ Dom2 1) (x y : ℝ) : d11 Φ (x, y) = d22 Φ (y, x) := by
  have he : (fun t => d1 Φ (t, y)) = fun t => d2 Φ (y, t) := by
    funext t; exact d1_swap h t y
  rw [← (hasDerivAt_d1_slice h.1 x y).deriv, ← (hasDerivAt_d2_slice h.1 y x).deriv, he]

lemma d22_swap (h : Φ ∈ Dom2 1) (x y : ℝ) : d22 Φ (x, y) = d11 Φ (y, x) :=
  (d11_swap h y x).symm

end derivs

lemma integral_unit {f : ℝ → ℝ} : ∫ x in (0 : ℝ)..1, f x = ∫ x, f x ∂μ1 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- **Integration by parts along `x₁`.** -/
lemma ibp1 {Φ φ : ℝ × ℝ → ℝ} (hΦ : Φ ∈ Dom2 1) (hφ : φ ∈ Dom2 1) :
    ∫ p, d1 Φ p * d1 φ p ∂μ2 = -∫ p, d11 Φ p * φ p ∂μ2 := by
  rw [fub1 (F := fun p => d1 Φ p * d1 φ p) ((cont_d1 hΦ).mul (cont_d1 hφ)),
    fub1 (F := fun p => d11 Φ p * φ p) ((continuous_d11 hΦ.1).mul hφ.1.continuous),
    ← integral_neg]
  congr 1; funext y
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun x => d1 Φ (x, y)) (u' := fun x => d11 Φ (x, y))
    (v := fun x => φ (x, y)) (v' := fun x => d1 φ (x, y))
    (fun x _ => hasDerivAt_d1_slice hΦ.1 x y) (fun x _ => hasDerivAt_slice1 hφ x y)
    (((continuous_d11 hΦ.1).comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
    (((cont_d1 hφ).comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  rw [hφ.2.2.1 y, hφ.2.2.2 y, mul_zero, mul_zero, sub_zero, zero_sub, integral_unit,
    integral_unit] at h
  exact h

/-- **Integration by parts along `x₂`.** -/
lemma ibp2 {Φ φ : ℝ × ℝ → ℝ} (hΦ : Φ ∈ Dom2 1) (hφ : φ ∈ Dom2 1) :
    ∫ p, d2 Φ p * d2 φ p ∂μ2 = -∫ p, d22 Φ p * φ p ∂μ2 := by
  rw [fub2 (F := fun p => d2 Φ p * d2 φ p) ((cont_d2 hΦ).mul (cont_d2 hφ)),
    fub2 (F := fun p => d22 Φ p * φ p) ((continuous_d22 hΦ.1).mul hφ.1.continuous),
    ← integral_neg]
  congr 1; funext x
  have hs := slice2_mem hφ x
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun y => d2 Φ (x, y)) (u' := fun y => d22 Φ (x, y))
    (v := fun y => φ (x, y)) (v' := fun y => d2 φ (x, y))
    (fun y _ => hasDerivAt_d2_slice hΦ.1 x y) (fun y _ => hasDerivAt_slice2 hφ x y)
    (((continuous_d22 hΦ.1).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    (((cont_d2 hφ).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  have h0 : φ (x, 0) = 0 := hs.2.1
  have h1 : φ (x, 1) = 0 := hs.2.2
  rw [h0, h1, mul_zero, mul_zero, sub_zero, zero_sub, integral_unit, integral_unit] at h
  exact h

/-- **Ground states of interacting bosons are classical solutions** of
`-ΔΦ + (w + v(x₁) + v(x₂) - E) Φ = 0` on the open square. -/
theorem strong_eq {w : ℝ × ℝ → ℝ} {hw : Continuous w} (hws : ∀ p, w p.swap = w p) {v : Pot}
    {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ) :
    ∀ p ∈ Sq, -lap Φ p + (w p + L2 v p - Q (setting2 1 w hw) v Φ / ip (μ := μ2) Φ Φ) * Φ p = 0 := by
  have hD : Φ ∈ Dom2 1 := hΦ.1
  set E := Q (setting2 1 w hw) v Φ / ip (μ := μ2) Φ Φ
  set g : ℝ × ℝ → ℝ := fun p => -lap Φ p + (w p + L2 v p - E) * Φ p
  have hc := hD.1.continuous
  have hg : Continuous g :=
    (continuous_lap hD.1).neg.add (((hw.add (continuous_L2 v)).sub continuous_const).mul hc)
  have hgs : ∀ p, g p.swap = g p := by
    rintro ⟨x, y⟩
    have hΦs : Φ (y, x) = Φ (x, y) := by
      have := hD.2.1 (x, y); simpa using this
    have hwxy : w (y, x) = w (x, y) := hws (x, y)
    simp only [g, lap, Prod.swap_prod_mk, d11_swap hD y x, d22_swap hD y x, hΦs, hwxy, L2,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring
  refine eq_zero_of_integral_sym hg hgs fun φ hφ => ?_
  have hel := euler_lagrange hΦ hφ
  change h02 w Φ φ + ∫ p, L2 v p * (Φ p * φ p) ∂μ2 = E * ∫ p, Φ p * φ p ∂μ2 at hel
  simp only [h02] at hel
  have hφc := hφ.1.continuous
  have i11 := integrable2 ((cont_d1 hD).mul (cont_d1 hφ))
  have i22 := integrable2 ((cont_d2 hD).mul (cont_d2 hφ))
  have j11 := integrable2 ((continuous_d11 hD.1).mul hφc)
  have j22 := integrable2 ((continuous_d22 hD.1).mul hφc)
  have iw := integrable2 (hw.mul (hc.mul hφc))
  have iL := integrable2 ((continuous_L2 v).mul (hc.mul hφc))
  have iP := integrable2 (hc.mul hφc)
  have hkin : ∫ p, (d1 Φ p * d1 φ p + d2 Φ p * d2 φ p) ∂μ2 =
      -∫ p, d11 Φ p * φ p ∂μ2 - ∫ p, d22 Φ p * φ p ∂μ2 := by
    rw [integral_add (f := fun p => d1 Φ p * d1 φ p) (g := fun p => d2 Φ p * d2 φ p) i11 i22,
      ibp1 hD hφ, ibp2 hD hφ]
    ring
  have hpt : (fun p => g p * φ p) = fun p =>
      ((-(d11 Φ p * φ p) + -(d22 Φ p * φ p)) + (w p * (Φ p * φ p) + L2 v p * (Φ p * φ p))) -
        E * (Φ p * φ p) := by
    funext p; simp only [g, lap]; ring
  rw [hpt,
    integral_sub (f := fun p => (-(d11 Φ p * φ p) + -(d22 Φ p * φ p)) +
      (w p * (Φ p * φ p) + L2 v p * (Φ p * φ p))) (g := fun p => E * (Φ p * φ p))
      ((j11.neg.add j22.neg).add (iw.add iL)) (iP.const_mul E),
    integral_add (f := fun p => -(d11 Φ p * φ p) + -(d22 Φ p * φ p))
      (g := fun p => w p * (Φ p * φ p) + L2 v p * (Φ p * φ p)) (j11.neg.add j22.neg) (iw.add iL),
    integral_add (f := fun p => -(d11 Φ p * φ p)) (g := fun p => -(d22 Φ p * φ p))
      j11.neg j22.neg,
    integral_add (f := fun p => w p * (Φ p * φ p)) (g := fun p => L2 v p * (Φ p * φ p)) iw iL,
    integral_neg, integral_neg, integral_const_mul]
  rw [hkin] at hel
  linarith

end Pair

end Continuum

end DFT
