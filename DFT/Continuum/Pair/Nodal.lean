/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Pair.Strong
import DFT.Continuum.General.Lieb
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Ground states of interacting bosons have critical zeros

For two bosons in the box with a continuous symmetric interaction, a ground state `Φ` has vanishing
gradient wherever it vanishes in the open square (`grad_zero_at_zero`). Everything is done in the
`C²` form domain, without Sobolev spaces.

Idea: with the smoothed absolute value `h_ε(s) = √(s² + ε²) - ε` (derivative `k_ε(s) = s/√(s²+ε²)`,
second derivative `k₂(s) = ε²/(s²+ε²)^{3/2}`), the state `h_ε(Φ)` is admissible and has energy at
most `E` up to `O(ε)` (`Rf_h_le`). Testing the ground-state inequality on `h_ε(Φ) + t φ` bounds the
cross term by `O(√ε)`; the Euler–Lagrange equation tested on `k_ε(Φ) φ` turns this cross term into
`-∫ k₂(Φ) |∇Φ|² φ + O(ε)`. If `∂₁Φ ≠ 0` at a zero, `Φ` changes sign across a small box and
`∫ k₂(Φ) ∂₁Φ dx₁ = k_ε(Φ(right)) - k_ε(Φ(left)) ≥ 1` on every horizontal segment of the box, a
lower bound independent of `ε`. Contradiction for small `ε`.
-/

namespace DFT

namespace Continuum

namespace Pair

open MeasureTheory Set Filter Topology Box Metric

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

/-! ### Derivatives of compositions and products -/

lemma fderiv_comp_apply {F F' : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (F' s) s) {Φ : ℝ × ℝ → ℝ}
    (hΦ : Differentiable ℝ Φ) (p m : ℝ × ℝ) :
    fderiv ℝ (fun q => F (Φ q)) p m = F' (Φ p) * fderiv ℝ Φ p m := by
  have h := (hF (Φ p)).comp_hasFDerivAt p (hΦ p).hasFDerivAt
  rw [show (fun q => F (Φ q)) = F ∘ Φ from rfl, h.fderiv]
  simp [smul_eq_mul]

lemma fderiv_mul_apply {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (p m : ℝ × ℝ) :
    fderiv ℝ (fun q => f q * g q) p m = fderiv ℝ f p m * g p + f p * fderiv ℝ g p m := by
  have h : HasFDerivAt (fun q => f q * g q) (f p • fderiv ℝ g p + g p • fderiv ℝ f p) p :=
    (hf p).hasFDerivAt.mul (hg p).hasFDerivAt
  rw [h.fderiv]
  simp [smul_eq_mul]
  ring

/-! ### The shifted energy form `Q - E · ip` -/

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

variable {σ : ℝ} {w : ℝ × ℝ → ℝ} {hw : Continuous w} {v : Pot}

/-- The shifted energy form `h₀ + ⟨v·,·⟩ - E ⟨·,·⟩`. -/
noncomputable def Rf (σ : ℝ) (w : ℝ × ℝ → ℝ) (hw : Continuous w) (v : Pot) (E : ℝ)
    (ψ φ : ℝ × ℝ → ℝ) : ℝ :=
  (setting2 σ w hw).h0 ψ φ + pf (setting2 σ w hw) v ψ φ - E * ip (μ := μ2) ψ φ

lemma Rf_eq (E : ℝ) {ψ φ : ℝ × ℝ → ℝ} (hψ : ψ ∈ Dom2 σ) (hφ : φ ∈ Dom2 σ) :
    Rf σ w hw v E ψ φ = ∫ p, (d1 ψ p * d1 φ p + d2 ψ p * d2 φ p +
      (w p + L2 v p - E) * (ψ p * φ p)) ∂μ2 := by
  have i1 := integrable2 (((cont_d1 hψ).mul (cont_d1 hφ)).add ((cont_d2 hψ).mul (cont_d2 hφ)))
  have i2 := integrable2 (hw.mul (hψ.1.continuous.mul hφ.1.continuous))
  have i3 := integrable2 ((continuous_L2 v).mul (hψ.1.continuous.mul hφ.1.continuous))
  have i4 := integrable2 (hψ.1.continuous.mul hφ.1.continuous)
  have hpt : (fun p => d1 ψ p * d1 φ p + d2 ψ p * d2 φ p + (w p + L2 v p - E) * (ψ p * φ p)) =
      fun p => ((d1 ψ p * d1 φ p + d2 ψ p * d2 φ p) + w p * (ψ p * φ p) +
        L2 v p * (ψ p * φ p)) - E * (ψ p * φ p) := by
    funext p; ring
  rw [hpt, integral_sub (f := fun p => (d1 ψ p * d1 φ p + d2 ψ p * d2 φ p) + w p * (ψ p * φ p) +
      L2 v p * (ψ p * φ p)) (g := fun p => E * (ψ p * φ p)) ((i1.add i2).add i3) (i4.const_mul E),
    integral_add (f := fun p => (d1 ψ p * d1 φ p + d2 ψ p * d2 φ p) + w p * (ψ p * φ p))
      (g := fun p => L2 v p * (ψ p * φ p)) (i1.add i2) i3,
    integral_add (f := fun p => d1 ψ p * d1 φ p + d2 ψ p * d2 φ p)
      (g := fun p => w p * (ψ p * φ p)) i1 i2, integral_const_mul]
  rfl

lemma Rf_nonneg {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 σ w hw) v Φ) {ψ : ℝ × ℝ → ℝ}
    (hψ : ψ ∈ Dom2 σ) :
    0 ≤ Rf σ w hw v (Q (setting2 σ w hw) v Φ / ip (μ := μ2) Φ Φ) ψ ψ := by
  have h := hΦ.2.2 ψ hψ
  have hp := hΦ.2.1
  have : Q (setting2 σ w hw) v Φ / ip (μ := μ2) Φ Φ * ip (μ := μ2) ψ ψ ≤
      Q (setting2 σ w hw) v ψ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]; linarith
  have e : Q (setting2 σ w hw) v ψ =
      (setting2 σ w hw).h0 ψ ψ + pf (setting2 σ w hw) v ψ ψ := rfl
  rw [e] at this
  unfold Rf
  linarith

lemma Rf_expand (E : ℝ) {ψ φ : ℝ × ℝ → ℝ} (hψ : ψ ∈ Dom2 σ) (hφ : φ ∈ Dom2 σ) (t : ℝ) :
    Rf σ w hw v E (ψ + t • φ) (ψ + t • φ) =
      Rf σ w hw v E ψ ψ + 2 * t * Rf σ w hw v E ψ φ + t ^ 2 * Rf σ w hw v E φ φ := by
  unfold Rf
  rw [h0_expand (S := setting2 σ w hw) hψ hφ, pf_expand (S := setting2 σ w hw) v hψ hφ,
    ip_expand (S := setting2 σ w hw) hψ hφ]
  ring

lemma Rf_self {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 σ w hw) v Φ) :
    Rf σ w hw v (Q (setting2 σ w hw) v Φ / ip (μ := μ2) Φ Φ) Φ Φ = 0 := by
  have hp := hΦ.2.1
  have e : Rf σ w hw v (Q (setting2 σ w hw) v Φ / ip (μ := μ2) Φ Φ) Φ Φ =
      Q (setting2 σ w hw) v Φ -
        Q (setting2 σ w hw) v Φ / ip (μ := μ2) Φ Φ * ip (μ := μ2) Φ Φ := rfl
  rw [e, div_mul_cancel₀ _ hp.ne', sub_self]

lemma Rf_EL {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 σ w hw) v Φ) {g : ℝ × ℝ → ℝ}
    (hg : g ∈ Dom2 σ) : Rf σ w hw v (Q (setting2 σ w hw) v Φ / ip (μ := μ2) Φ Φ) Φ g = 0 := by
  have h := euler_lagrange hΦ (φ := g) hg
  unfold Rf
  linarith

/-! ### Admissible functions built from `Φ` -/

section members

variable {Φ : ℝ × ℝ → ℝ} (hD : Φ ∈ Dom2 1) {ε : ℝ} (hε0 : 0 < ε)
include hD hε0

lemma hΦ_mem : (fun q => hε ε (Φ q)) ∈ Dom2 1 :=
  ⟨(contDiff_hε hε0).comp hD.1, fun p => by simp [hD.2.1 p],
    fun y => by simp [hD.2.2.1 y, hε_zero hε0], fun y => by simp [hD.2.2.2 y, hε_zero hε0]⟩

lemma g_mem {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) : (fun q => kε ε (Φ q) * φ q) ∈ Dom2 1 :=
  ⟨((contDiff_kε hε0).comp hD.1).mul hφ.1, fun p => by simp [hD.2.1 p, hφ.2.1 p],
    fun y => by simp [hφ.2.2.1 y], fun y => by simp [hφ.2.2.2 y]⟩

lemma fderiv_hΦ (p m : ℝ × ℝ) :
    fderiv ℝ (fun q => hε ε (Φ q)) p m = kε ε (Φ p) * fderiv ℝ Φ p m :=
  fderiv_comp_apply (hasDerivAt_hε hε0) (diff2 hD) p m

lemma fderiv_g {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) (p m : ℝ × ℝ) :
    fderiv ℝ (fun q => kε ε (Φ q) * φ q) p m =
      k2 ε (Φ p) * fderiv ℝ Φ p m * φ p + kε ε (Φ p) * fderiv ℝ φ p m := by
  rw [fderiv_mul_apply (f := fun q => kε ε (Φ q)) (g := φ)
      (((contDiff_kε hε0).comp hD.1).differentiable (by norm_num)) (diff2 hφ),
    fderiv_comp_apply (hasDerivAt_kε hε0) (diff2 hD)]

end members

/-! ### Geometry near a zero with `∂₁Φ > 0` -/

lemma slice_lower {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {c x0 x1 : ℝ}
    (hx : x0 ≤ x1) (hc : ∀ x ∈ Icc x0 x1, c ≤ f' x) : c * (x1 - x0) ≤ f x1 - f x0 :=
  Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc x0 x1) (f := f) (C := c)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hf x).deriv]; exact hc x ⟨hx.1.le, hx.2.le⟩)
    x0 ⟨le_rfl, hx⟩ x1 ⟨hx, le_rfl⟩ hx

lemma dist_le_of_abs {q : ℝ × ℝ} {a b r : ℝ} (h1 : |q.1 - a| ≤ r) (h2 : |q.2 - b| ≤ r) :
    dist q (a, b) ≤ r := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact max_le h1 h2

/-- Around a zero with `∂₁Φ > 0`: a box inside the square where `∂₁Φ > ∂₁Φ(a,b)/2`, across which
`Φ` changes sign uniformly. -/
lemma box_data_on {Φ : ℝ × ℝ → ℝ} (hD : Φ ∈ Dom2 σ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b : ℝ} (hab : (a, b) ∈ Sq ∩ U)
    (h0 : Φ (a, b) = 0) (hpos : 0 < d1 Φ (a, b)) :
    ∃ r r' δ : ℝ, 0 < r ∧ 0 < r' ∧ r' ≤ r ∧ 0 < δ ∧
      (∀ q : ℝ × ℝ, dist q (a, b) ≤ 2 * r → q ∈ Sq ∩ U ∧ d1 Φ (a, b) / 2 < d1 Φ q) ∧
      ∀ y, |y - b| ≤ r' → δ < Φ (a + r, y) ∧ Φ (a - r, y) < -δ := by
  set s0 := d1 Φ (a, b)
  have hO : IsOpen ((Sq ∩ U) ∩ {q | s0 / 2 < d1 Φ q}) :=
    ((isOpen_Ioo.prod isOpen_Ioo).inter hU).inter (isOpen_lt continuous_const (cont_d1 hD))
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hO (a, b) ⟨hab, by simp only [mem_ofPred_eq]; linarith⟩
  set r := ε / 4
  have hr : 0 < r := by positivity
  have hin : ∀ q : ℝ × ℝ, dist q (a, b) ≤ 2 * r → q ∈ Sq ∩ U ∧ s0 / 2 < d1 Φ q := fun q hq =>
    hball (show dist q (a, b) < ε by simp only [r] at hq; linarith)
  have hslice : ∀ x ∈ Icc (a - r) (a + r), s0 / 2 ≤ d1 Φ (x, b) := fun x hx =>
    (hin (x, b) (dist_le_of_abs (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (by simp; linarith))).2.le
  have hR := slice_lower (fun x => hasDerivAt_slice1 hD x b) (c := s0 / 2) (x0 := a) (x1 := a + r)
    (by linarith) (fun x hx => hslice x ⟨by linarith [hx.1], hx.2⟩)
  have hL := slice_lower (fun x => hasDerivAt_slice1 hD x b) (c := s0 / 2) (x0 := a - r) (x1 := a)
    (by linarith) (fun x hx => hslice x ⟨hx.1, by linarith [hx.2]⟩)
  simp only [h0] at hR hL
  have hR' : r * s0 / 2 ≤ Φ (a + r, b) := by
    have e : s0 / 2 * (a + r - a) = r * s0 / 2 := by ring
    linarith
  have hL' : Φ (a - r, b) ≤ -(r * s0 / 2) := by
    have e : s0 / 2 * (a - (a - r)) = r * s0 / 2 := by ring
    linarith
  set δ := r * s0 / 4 with hδe
  have hδ : 0 < δ := by positivity
  have c1 : ContinuousAt (fun y => Φ (a + r, y)) b :=
    (hD.1.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
  have c2 : ContinuousAt (fun y => Φ (a - r, y)) b :=
    (hD.1.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
  obtain ⟨η1, hη1, h1⟩ := Metric.continuousAt_iff.mp c1 δ hδ
  obtain ⟨η2, hη2, h2⟩ := Metric.continuousAt_iff.mp c2 δ hδ
  refine ⟨r, min r (min η1 η2 / 2), δ, hr, lt_min hr (by positivity), min_le_left _ _, hδ, hin,
    fun y hy => ?_⟩
  have hy1 : dist y b < η1 := by
    rw [Real.dist_eq]
    linarith [min_le_right r (min η1 η2 / 2), min_le_left η1 η2]
  have hy2 : dist y b < η2 := by
    rw [Real.dist_eq]
    linarith [min_le_right r (min η1 η2 / 2), min_le_right η1 η2]
  have e1 := h1 hy1
  have e2 := h2 hy2
  rw [Real.dist_eq] at e1 e2
  constructor
  · have := (abs_lt.mp e1).1; linarith
  · have := (abs_lt.mp e2).2; linarith

lemma box_data {Φ : ℝ × ℝ → ℝ} (hD : Φ ∈ Dom2 1) {a b : ℝ} (hab : (a, b) ∈ Sq)
    (h0 : Φ (a, b) = 0) (hpos : 0 < d1 Φ (a, b)) :
    ∃ r r' δ : ℝ, 0 < r ∧ 0 < r' ∧ r' ≤ r ∧ 0 < δ ∧
      (∀ q : ℝ × ℝ, dist q (a, b) ≤ 2 * r → q ∈ Sq ∧ d1 Φ (a, b) / 2 < d1 Φ q) ∧
      ∀ y, |y - b| ≤ r' → δ < Φ (a + r, y) ∧ Φ (a - r, y) < -δ := by
  obtain ⟨r, r', δ, h1, h2, h3, h4, hin, h5⟩ := box_data_on hD isOpen_univ ⟨hab, mem_univ _⟩ h0 hpos
  exact ⟨r, r', δ, h1, h2, h3, h4, fun q hq => ⟨(hin q hq).1.1, (hin q hq).2⟩, h5⟩

/-- Across the box, the integral of `k₂(Φ) ∂₁Φ` is at least the height of the box. -/
lemma box_integral {Φ : ℝ × ℝ → ℝ} (hD : Φ ∈ Dom2 σ) {ε : ℝ} (hε0 : 0 < ε) {a b r r' δ : ℝ}
    (hr : 0 < r) (hr' : 0 < r') (hεδ : ε ≤ δ)
    (hsign : ∀ y, |y - b| ≤ r' → δ < Φ (a + r, y) ∧ Φ (a - r, y) < -δ) :
    2 * r' ≤ ∫ q in Icc (a - r) (a + r) ×ˢ Icc (b - r') (b + r'), k2 ε (Φ q) * d1 Φ q := by
  have hk2c : Continuous (k2 ε) := continuous_k2 hε0
  have hkc : Continuous (kε ε) := (contDiff_kε hε0).continuous
  set F : ℝ × ℝ → ℝ := fun q => k2 ε (Φ q) * d1 Φ q
  have hF : Continuous F := (hk2c.comp hD.1.continuous).mul (cont_d1 hD)
  have hint : Integrable F ((volume.restrict (Icc (a - r) (a + r))).prod
      (volume.restrict (Icc (b - r') (b + r')))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have inner : ∀ y, ∫ x in Icc (a - r) (a + r), F (x, y) =
      kε ε (Φ (a + r, y)) - kε ε (Φ (a - r, y)) := by
    intro y
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => kε ε (Φ (x, y)))
      (fun x _ => by
        have h := (hasDerivAt_kε hε0 (Φ (x, y))).comp x (hasDerivAt_slice1 hD x y)
        exact h)
      ((hF.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm F hint]
  simp only [inner]
  have hcont : Continuous fun y => kε ε (Φ (a + r, y)) - kε ε (Φ (a - r, y)) :=
    (hkc.comp (hD.1.continuous.comp (continuous_const.prodMk continuous_id))).sub
      (hkc.comp (hD.1.continuous.comp (continuous_const.prodMk continuous_id)))
  have hmono : ∫ y in Icc (b - r') (b + r'), (1 : ℝ) ≤
      ∫ y in Icc (b - r') (b + r'), (kε ε (Φ (a + r, y)) - kε ε (Φ (a - r, y))) := by
    refine setIntegral_mono_on (integrableOn_const (by simp)) 
      (hcont.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc fun y hy => ?_
    have hy' : |y - b| ≤ r' := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    obtain ⟨h1, h2⟩ := hsign y hy'
    have k1 := kε_ge_half hε0 (s := Φ (a + r, y)) (by linarith)
    have k2' := kε_le_neg_half hε0 (s := Φ (a - r, y)) (by linarith)
    linarith
  refine le_trans (le_of_eq ?_) hmono
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-! ### The contradiction -/

lemma isGS_neg_pair {Φ : ℝ × ℝ → ℝ} (h : IsGS (setting2 σ w hw) v Φ) :
    IsGS (setting2 σ w hw) v (-Φ) := by
  have hn : -Φ = (-1 : ℝ) • Φ := by simp
  obtain ⟨hD, hpos, hmin⟩ := h
  refine ⟨(setting2 σ w hw).D.neg_mem hD, ?_, fun φ hφ => ?_⟩
  · rw [hn, ip_smul_self]; linarith
  · rw [hn, ip_smul_self, Q_smul_self v _ hD]
    have := hmin φ hφ
    linarith

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

/-- A ground state cannot vanish at an interior point where `∂₁Φ > 0`. -/
lemma no_pos_d1 {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ) {a b : ℝ}
    (hab : (a, b) ∈ Sq) (h0 : Φ (a, b) = 0) (hpos : 0 < d1 Φ (a, b)) : False := by
  have hD : Φ ∈ Dom2 1 := hΦ.1
  set s0 := d1 Φ (a, b) with hs0
  obtain ⟨r, r', δ, hr, hr', hrr, hδ, hin, hsign⟩ := box_data hD hab h0 hpos
  -- a symmetric bump, equal to `1` on the box
  let β : ContDiffBump ((a, b) : ℝ × ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  have hβout : ∀ q, q ∉ Sq → β q = 0 := by
    intro q hq
    apply image_eq_zero_of_notMem_tsupport
    intro h
    rw [β.tsupport_eq] at h
    exact hq (hin q (mem_closedBall.mp h)).1
  set φs : ℝ × ℝ → ℝ := fun q => β q + β q.swap with hφsdef
  have hφs : φs ∈ Dom2 1 := by
    refine ⟨β.contDiff.add (β.contDiff.comp (contDiff_snd.prodMk contDiff_fst)),
      fun q => ?_, fun y => ?_, fun y => ?_⟩
    · simp only [φs, Prod.swap_swap]; ring
    · simp only [φs, Prod.swap_prod_mk]
      rw [hβout (0, y) (fun h => lt_irrefl _ h.1.1), hβout (y, 0) (fun h => lt_irrefl _ h.2.1)]
      ring
    · simp only [φs, Prod.swap_prod_mk]
      rw [hβout (1, y) (fun h => lt_irrefl _ h.1.2), hβout (y, 1) (fun h => lt_irrefl _ h.2.2)]
      ring
  have hφs0 : ∀ q, 0 ≤ φs q := fun q => add_nonneg (β.nonneg' q) (β.nonneg' q.swap)
  set Bx := Icc (a - r) (a + r) ×ˢ Icc (b - r') (b + r') with hBx
  have hBxd : ∀ q ∈ Bx, dist q (a, b) ≤ r := fun q hq =>
    dist_le_of_abs (abs_le.mpr ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩)
      (abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩)
  have hφs1 : ∀ q ∈ Bx, 1 ≤ φs q := fun q hq => by
    have : β q = 1 := β.one_of_mem_closedBall (mem_closedBall.mpr (hBxd q hq))
    simp only [φs, this]; linarith [β.nonneg' q.swap]
  have hBxS : Bx ⊆ Sq := fun q hq => (hin q (by linarith [hBxd q hq])).1
  have hBxd1 : ∀ q ∈ Bx, s0 / 2 < d1 Φ q := fun q hq => (hin q (by linarith [hBxd q hq])).2
  -- constants independent of `ε`
  set E := Q (setting2 1 w hw) v Φ / ip (μ := μ2) Φ Φ with hE
  set V : ℝ × ℝ → ℝ := fun q => w q + L2 v q - E with hV
  have hVc : Continuous V := (hw.add (continuous_L2 v)).sub continuous_const
  have hφc : Continuous φs := hφs.1.continuous
  have hΦc : Continuous Φ := hD.1.continuous
  set K1 := ∫ q, |V q| * |Φ q| ∂μ2 with hK1d
  set K2 := ∫ q, |V q| * φs q ∂μ2 with hK2d
  have hK1 : 0 ≤ K1 := integral_nonneg fun q => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hK2 : 0 ≤ K2 := integral_nonneg fun q => mul_nonneg (abs_nonneg _) (hφs0 q)
  set C := Rf 1 w hw v E φs φs with hCd
  have hC : 0 ≤ C := Rf_nonneg hΦ hφs
  set L := s0 * r' with hLd
  have hL : 0 < L := mul_pos hpos hr'
  set ε := min δ (min (L / (4 * (K2 + 1))) (L ^ 2 / (16 * (K1 * C + 1)))) with hεd
  have hε0 : 0 < ε := lt_min hδ (lt_min (by positivity) (by positivity))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ L / (4 * (K2 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ L ^ 2 / (16 * (K1 * C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  -- the admissible functions `h_ε(Φ)` and `k_ε(Φ) φ`
  set hΦε : ℝ × ℝ → ℝ := fun q => hε ε (Φ q) with hhd
  have hhm : hΦε ∈ Dom2 1 := hΦ_mem hD hε0
  set g : ℝ × ℝ → ℝ := fun q => kε ε (Φ q) * φs q with hgd
  have hgm : g ∈ Dom2 1 := g_mem hD hε0 hφs
  have dh1 : ∀ q, d1 hΦε q = kε ε (Φ q) * d1 Φ q := fun q => fderiv_hΦ hD hε0 q (1, 0)
  have dh2 : ∀ q, d2 hΦε q = kε ε (Φ q) * d2 Φ q := fun q => fderiv_hΦ hD hε0 q (0, 1)
  have dg1 : ∀ q, d1 g q = k2 ε (Φ q) * d1 Φ q * φs q + kε ε (Φ q) * d1 φs q :=
    fun q => fderiv_g hD hε0 hφs q (1, 0)
  have dg2 : ∀ q, d2 g q = k2 ε (Φ q) * d2 Φ q * φs q + kε ε (Φ q) * d2 φs q :=
    fun q => fderiv_g hD hε0 hφs q (0, 1)
  have hk2c : Continuous (k2 ε) := continuous_k2 hε0
  have hkc : Continuous (kε ε) := (contDiff_kε hε0).continuous
  have hhc : Continuous (hε ε) := (contDiff_hε hε0).continuous
  set G : ℝ × ℝ → ℝ := fun q => k2 ε (Φ q) * (d1 Φ q ^ 2 + d2 Φ q ^ 2) * φs q with hGd
  have hGc : Continuous G :=
    ((hk2c.comp hΦc).mul (((cont_d1 hD).pow 2).add ((cont_d2 hD).pow 2))).mul hφc
  -- lower bound: `∫ G ≥ L`
  have hlow : L ≤ ∫ q, G q ∂μ2 := by
    have hcpt : IsCompact Bx := isCompact_Icc.prod isCompact_Icc
    have h1 : ∫ q in Bx, G q ≤ ∫ q, G q ∂μ2 :=
      setIntegral_mono_set (integrable2 hGc)
        (ae_of_all _ fun q => mul_nonneg (mul_nonneg (k2_pos hε0 _).le (by positivity))
          (hφs0 q)) hBxS.eventuallyLE
    have hFc : Continuous fun q => k2 ε (Φ q) * d1 Φ q := (hk2c.comp hΦc).mul (cont_d1 hD)
    have h2 : ∫ q in Bx, s0 / 2 * (k2 ε (Φ q) * d1 Φ q) ≤ ∫ q in Bx, G q := by
      refine setIntegral_mono_on ((continuous_const.mul hFc).continuousOn.integrableOn_compact hcpt)
        (hGc.continuousOn.integrableOn_compact hcpt) (measurableSet_Icc.prod measurableSet_Icc)
        fun q hq => ?_
      have hK := k2_pos hε0 (Φ q)
      have hd := hBxd1 q hq
      have hP := hφs1 q hq
      have hD1 : 0 < d1 Φ q := by linarith
      have e1 : s0 / 2 * (k2 ε (Φ q) * d1 Φ q) ≤ k2 ε (Φ q) * d1 Φ q * d1 Φ q :=
        by nlinarith [mul_pos hK hD1]
      have e2 : k2 ε (Φ q) * d1 Φ q * d1 Φ q ≤ k2 ε (Φ q) * (d1 Φ q ^ 2 + d2 Φ q ^ 2) :=
        by nlinarith [sq_nonneg (d2 Φ q)]
      have e3 : k2 ε (Φ q) * (d1 Φ q ^ 2 + d2 Φ q ^ 2) ≤ G q := by
        simp only [G]
        have : 0 ≤ k2 ε (Φ q) * (d1 Φ q ^ 2 + d2 Φ q ^ 2) := by positivity
        nlinarith
      linarith
    have h3 := box_integral hD hε0 hr hr' hεδ hsign
    rw [integral_const_mul] at h2
    calc L = s0 / 2 * (2 * r') := by simp only [L]; ring
      _ ≤ s0 / 2 * ∫ q in Bx, k2 ε (Φ q) * d1 Φ q :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ ≤ _ := h2
      _ ≤ _ := h1
  -- the cross term
  set X : ℝ × ℝ → ℝ := fun q => V q * (hε ε (Φ q) - Φ q * kε ε (Φ q)) * φs q with hXd
  have hXc : Continuous X := (hVc.mul ((hhc.comp hΦc).sub (hΦc.mul (hkc.comp hΦc)))).mul hφc
  set B := Rf 1 w hw v E hΦε φs with hBd
  have hU : ∫ q, G q ∂μ2 = ∫ q, X q ∂μ2 - B := by
    have hEL := Rf_EL hΦ hgm
    rw [Rf_eq E hD hgm] at hEL
    rw [hBd, Rf_eq E hhm hφs]
    have iA : Integrable (fun q => d1 Φ q * d1 g q + d2 Φ q * d2 g q +
        (w q + L2 v q - E) * (Φ q * g q)) μ2 :=
      integrable2 ((((cont_d1 hD).mul (cont_d1 hgm)).add ((cont_d2 hD).mul
        (cont_d2 hgm))).add (hVc.mul (hΦc.mul hgm.1.continuous)))
    have iXG : Integrable (fun q => X q - G q) μ2 := integrable2 (hXc.sub hGc)
    have key : ∫ q, (d1 hΦε q * d1 φs q + d2 hΦε q * d2 φs q +
        (w q + L2 v q - E) * (hΦε q * φs q)) ∂μ2 =
        ∫ q, (d1 Φ q * d1 g q + d2 Φ q * d2 g q + (w q + L2 v q - E) * (Φ q * g q)) ∂μ2 +
          ∫ q, (X q - G q) ∂μ2 := by
      rw [← integral_add iA iXG]
      congr 1; funext q
      rw [dh1 q, dh2 q, dg1 q, dg2 q]
      simp only [X, G, V, hΦε, g]
      ring
    rw [key, hEL, zero_add, integral_sub (integrable2 hXc) (integrable2 hGc)]
    ring
  have hB1 : |∫ q, X q ∂μ2| ≤ ε * K2 := by
    calc |∫ q, X q ∂μ2| ≤ ∫ q, |X q| ∂μ2 := abs_integral_le_integral_abs
      _ ≤ ∫ q, ε * (|V q| * φs q) ∂μ2 := by
          refine integral_mono (integrable2 hXc.abs)
            (integrable2 (continuous_const.mul (hVc.abs.mul hφc))) fun q => ?_
          simp only [X, abs_mul, abs_of_nonneg (hφs0 q)]
          have := abs_hε_sub hε0 (Φ q)
          have h0' : 0 ≤ |V q| * φs q := mul_nonneg (abs_nonneg _) (hφs0 q)
          nlinarith [abs_nonneg (V q)]
      _ = ε * K2 := integral_const_mul _ _
  have hB2 : Rf 1 w hw v E hΦε hΦε ≤ 2 * ε * K1 := by
    have hself := Rf_self hΦ
    rw [Rf_eq E hD hD] at hself
    rw [Rf_eq E hhm hhm]
    have iΦ : Integrable (fun q => d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q +
        (w q + L2 v q - E) * (Φ q * Φ q)) μ2 :=
      integrable2 ((((cont_d1 hD).mul (cont_d1 hD)).add ((cont_d2 hD).mul
        (cont_d2 hD))).add (hVc.mul (hΦc.mul hΦc)))
    have ih : Integrable (fun q => d1 hΦε q * d1 hΦε q + d2 hΦε q * d2 hΦε q +
        (w q + L2 v q - E) * (hΦε q * hΦε q)) μ2 :=
      integrable2 ((((cont_d1 hhm).mul (cont_d1 hhm)).add ((cont_d2 hhm).mul
        (cont_d2 hhm))).add (hVc.mul (hhm.1.continuous.mul hhm.1.continuous)))
    have e : ∫ q, (d1 hΦε q * d1 hΦε q + d2 hΦε q * d2 hΦε q +
        (w q + L2 v q - E) * (hΦε q * hΦε q)) ∂μ2 =
        ∫ q, (d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q + (w q + L2 v q - E) * (Φ q * Φ q)) ∂μ2 +
          ∫ q, ((d1 hΦε q * d1 hΦε q + d2 hΦε q * d2 hΦε q +
            (w q + L2 v q - E) * (hΦε q * hΦε q)) - (d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q +
              (w q + L2 v q - E) * (Φ q * Φ q))) ∂μ2 := by
      have ihΦ : Integrable (fun q => (d1 hΦε q * d1 hΦε q + d2 hΦε q * d2 hΦε q +
          (w q + L2 v q - E) * (hΦε q * hΦε q)) - (d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q +
            (w q + L2 v q - E) * (Φ q * Φ q))) μ2 := ih.sub iΦ
      rw [← integral_add iΦ ihΦ]
      congr 1; funext q; ring
    rw [e, hself, zero_add]
    calc _ ≤ ∫ q, (2 * ε) * (|V q| * |Φ q|) ∂μ2 := by
          refine integral_mono (ih.sub iΦ)
            (integrable2 (continuous_const.mul (hVc.abs.mul hΦc.abs))) fun q => ?_
          simp only
          rw [dh1 q, dh2 q]
          have hk := kε_sq_le hε0 (Φ q)
          have hsq := abs_hε_sq_sub hε0 (Φ q)
          have hVle : (w q + L2 v q - E) * (hε ε (Φ q) ^ 2 - Φ q ^ 2) ≤
              |V q| * (2 * ε * |Φ q|) := by
            calc (w q + L2 v q - E) * (hε ε (Φ q) ^ 2 - Φ q ^ 2)
                ≤ |(w q + L2 v q - E) * (hε ε (Φ q) ^ 2 - Φ q ^ 2)| := le_abs_self _
              _ = |V q| * |hε ε (Φ q) ^ 2 - Φ q ^ 2| := by rw [abs_mul]
              _ ≤ |V q| * (2 * ε * |Φ q|) :=
                  mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
          have hg2 : 0 ≤ d1 Φ q ^ 2 + d2 Φ q ^ 2 := by positivity
          have hkk : (kε ε (Φ q) ^ 2 - 1) * (d1 Φ q ^ 2 + d2 Φ q ^ 2) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) hg2
          simp only [hΦε]
          nlinarith [hVle, hkk]
      _ = 2 * ε * K1 := integral_const_mul _ _
  have hB3 : B ^ 2 ≤ Rf 1 w hw v E hΦε hΦε * C := by
    refine discr_le hC fun t => ?_
    have h := Rf_nonneg hΦ ((Dom2 1).add_mem hhm ((Dom2 1).smul_mem t hφs))
    rw [Rf_expand E hhm hφs t] at h
    linarith
  -- conclusion
  have hA : L ≤ ε * K2 + |B| := by
    have h1 := hlow
    rw [hU] at h1
    have h2 := (abs_le.mp hB1).2
    have h3 := le_abs_self (∫ q, X q ∂μ2)
    linarith [neg_abs_le B]
  exact final_arith hL hK1 hK2 hC hε0 hε1 hε2 hA hB2 hB3

/-- **Ground states of interacting bosons have critical zeros**: at every zero of a ground state
inside the square, its gradient vanishes. -/
theorem grad_zero_at_zero {w : ℝ × ℝ → ℝ} {hw : Continuous w} (_hws : ∀ p, w p.swap = w p)
    {v : Pot} {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ) :
    ∀ p ∈ Sq, Φ p = 0 → d1 Φ p = 0 ∧ d2 Φ p = 0 := by
  have hD : Φ ∈ Dom2 1 := hΦ.1
  have key : ∀ a b, (a, b) ∈ Sq → Φ (a, b) = 0 → d1 Φ (a, b) = 0 := by
    intro a b hab h0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hN := isGS_neg_pair hΦ
      have hd : d1 (-Φ) (a, b) = -d1 Φ (a, b) := by
        simp only [d1]
        rw [fderiv_neg]
        rfl
      exact no_pos_d1 hN hab (by simp [h0]) (by rw [hd]; linarith)
    · exact no_pos_d1 hΦ hab h0 hpos
  intro p hp h0
  obtain ⟨a, b⟩ := p
  refine ⟨key a b hp h0, ?_⟩
  have hsw : Φ (b, a) = Φ (a, b) := by simpa using hD.2.1 (a, b)
  rw [← d1_swap hD b a]
  exact key b a ⟨hp.2, hp.1⟩ (hsw.trans h0)

end Pair

end Continuum

end DFT
