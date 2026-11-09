/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Chamber
import DFT.Continuum.Line.Smooth
import DFT.Continuum.General.Lieb
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# `N` fermions: critical zeros away from collisions

A ground state `Φ` of `n + 1` interacting fermions on `[0, 1]` has vanishing gradient at each zero
`a` in the open cube with no collision (`aᵢ ≠ aⱼ` for `i ≠ j`). The argument is the one for two
bosons, made antisymmetric and run in `n + 1` dimensions: the competitor `h_ε(Φ)`
(a smoothed `|Φ|`) becomes `Sgn ε · h_ε(Φ)`, where `Sgn ε` is the smooth sign of the ordering
(`Chamber`), and the test function is `Sgn η₀ · sym β`, with `β` a bump at `a`. On the
near-collision set the competitor costs `O(1)` energy per unit volume, and that set has volume
`O(ε)`.

* `RfL`: the shifted energy form `h₀ + ⟨v·,·⟩ - E ⟨·,·⟩` and its properties (both statistics).
* `box_data_line`, `box_integral_line` (both statistics): near a zero with `∂ₖΦ > 0`, `Φ` changes
  sign across a box, so `∫ k₂(Φ) ∂ₖΦ` over the box is at least the box's cross-section.
* `no_pos_dk`, `grad_zero_at_zero_line`: zeros away from collisions are critical.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box Metric

variable {n : ℕ}

/-! ### The shifted energy form -/

section Rf

variable {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

/-- The shifted energy form `h₀ + ⟨v·,·⟩ - E ⟨·,·⟩`. -/
noncomputable def RfL (τ : Stat) (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot) (E : ℝ)
    (ψ φ : Cfg n → ℝ) : ℝ :=
  (setting τ n w hw).h0 ψ φ + pf (setting τ n w hw) v ψ φ - E * ip (μ := μN n) ψ φ

lemma RfL_eq (E : ℝ) {ψ φ : Cfg n → ℝ} (hψ : ψ ∈ Dom τ n) (hφ : φ ∈ Dom τ n) :
    RfL τ w hw v E ψ φ = ∫ x, (∑ k, dk k ψ x * dk k φ x +
      (w x + LN n v x - E) * (ψ x * φ x)) ∂μN n := by
  have i1 := integrableN (cont_kin hψ hφ)
  have i2 := integrableN (hw.mul (hψ.1.continuous.mul hφ.1.continuous))
  have i3 := integrableN ((continuous_LN v).mul (hψ.1.continuous.mul hφ.1.continuous))
  have i4 := integrableN (hψ.1.continuous.mul hφ.1.continuous)
  have hpt : (fun x => ∑ k, dk k ψ x * dk k φ x + (w x + LN n v x - E) * (ψ x * φ x)) =
      fun x => ((∑ k, dk k ψ x * dk k φ x) + w x * (ψ x * φ x) +
        LN n v x * (ψ x * φ x)) - E * (ψ x * φ x) := by
    funext x; ring
  rw [hpt, integral_sub (f := fun x => (∑ k, dk k ψ x * dk k φ x) + w x * (ψ x * φ x) +
      LN n v x * (ψ x * φ x)) (g := fun x => E * (ψ x * φ x)) ((i1.add i2).add i3)
      (i4.const_mul E),
    integral_add (f := fun x => (∑ k, dk k ψ x * dk k φ x) + w x * (ψ x * φ x))
      (g := fun x => LN n v x * (ψ x * φ x)) (i1.add i2) i3,
    integral_add (f := fun x => ∑ k, dk k ψ x * dk k φ x)
      (g := fun x => w x * (ψ x * φ x)) i1 i2, integral_const_mul]
  rfl

lemma RfL_nonneg {Φ : Cfg n → ℝ} (hΦ : IsGS (setting τ n w hw) v Φ) {ψ : Cfg n → ℝ}
    (hψ : ψ ∈ Dom τ n) :
    0 ≤ RfL τ w hw v (Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ) ψ ψ := by
  have h := hΦ.2.2 ψ hψ
  have hp := hΦ.2.1
  have : Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ * ip (μ := μN n) ψ ψ ≤
      Q (setting τ n w hw) v ψ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]; linarith
  have e : Q (setting τ n w hw) v ψ =
      (setting τ n w hw).h0 ψ ψ + pf (setting τ n w hw) v ψ ψ := rfl
  rw [e] at this
  unfold RfL
  linarith

lemma RfL_expand (E : ℝ) {ψ φ : Cfg n → ℝ} (hψ : ψ ∈ Dom τ n) (hφ : φ ∈ Dom τ n) (t : ℝ) :
    RfL τ w hw v E (ψ + t • φ) (ψ + t • φ) =
      RfL τ w hw v E ψ ψ + 2 * t * RfL τ w hw v E ψ φ + t ^ 2 * RfL τ w hw v E φ φ := by
  unfold RfL
  rw [h0_expand (S := setting τ n w hw) hψ hφ, pf_expand (S := setting τ n w hw) v hψ hφ,
    ip_expand (S := setting τ n w hw) hψ hφ]
  ring

lemma RfL_self {Φ : Cfg n → ℝ} (hΦ : IsGS (setting τ n w hw) v Φ) :
    RfL τ w hw v (Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ) Φ Φ = 0 := by
  have hp := hΦ.2.1
  have e : RfL τ w hw v (Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ) Φ Φ =
      Q (setting τ n w hw) v Φ -
        Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ * ip (μ := μN n) Φ Φ := rfl
  rw [e, div_mul_cancel₀ _ hp.ne', sub_self]

lemma RfL_EL {Φ : Cfg n → ℝ} (hΦ : IsGS (setting τ n w hw) v Φ) {g : Cfg n → ℝ}
    (hg : g ∈ Dom τ n) : RfL τ w hw v (Q (setting τ n w hw) v Φ / ip (μ := μN n) Φ Φ) Φ g = 0 := by
  have h := euler_lagrange hΦ (φ := g) hg
  unfold RfL
  linarith

lemma isGS_neg_line {Φ : Cfg n → ℝ} (h : IsGS (setting τ n w hw) v Φ) :
    IsGS (setting τ n w hw) v (-Φ) := by
  have hn : -Φ = (-1 : ℝ) • Φ := by simp
  obtain ⟨hD, hpos, hmin⟩ := h
  refine ⟨(setting τ n w hw).D.neg_mem hD, ?_, fun φ hφ => ?_⟩
  · rw [hn, ip_smul_self]; linarith
  · rw [hn, ip_smul_self, Q_smul_self v _ hD]
    have := hmin φ hφ
    linarith

end Rf

/-! ### Admissible functions -/

lemma hε_sgn_mul {ε : ℝ} (σ : Equiv.Perm (Fin (n + 1))) (s : ℝ) :
    hε ε (sgn σ * s) = hε ε s := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [sgn, h]
  · simp [sgn, h, hε_neg]

lemma kε_sgn_mul {ε : ℝ} (σ : Equiv.Perm (Fin (n + 1))) (s : ℝ) :
    kε ε (sgn σ * s) = sgn σ * kε ε s := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [sgn, h]
  · simp [sgn, h, kε_neg]

/-- `Sgn η · f` lies in the domain, for `f` symmetric, `C²` and vanishing on the walls. -/
lemma Sgn_mul_mem {f : Cfg n → ℝ} (hf : ContDiff ℝ 2 f) (hfs : ∀ σ x, f (pm σ x) = f x)
    (hfw : ∀ x k, (x k = 0 ∨ x k = 1) → f x = 0) (η : ℝ) :
    (fun x => Sgn η x * f x) ∈ DomF n :=
  ⟨(contDiff_Sgn η).mul hf, fun σ x => by
    change Sgn η (pm σ x) * f (pm σ x) = sgn σ * (Sgn η x * f x)
    rw [Sgn_pm, hfs]; ring,
    fun x k hk => by change Sgn η x * f x = 0; rw [hfw x k hk, mul_zero]⟩

lemma hε_comp_sym {Φ : Cfg n → ℝ} (hD : Φ ∈ DomF n) {ε : ℝ} (σ : Equiv.Perm (Fin (n + 1)))
    (x : Cfg n) : hε ε (Φ (pm σ x)) = hε ε (Φ x) := by
  rw [anti hD σ x, hε_sgn_mul]

lemma kε_mul_mem_line {Φ φ : Cfg n → ℝ} (hD : Φ ∈ DomF n) (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ σ x, φ (pm σ x) = φ x) (hφw : ∀ x k, (x k = 0 ∨ x k = 1) → φ x = 0) {ε : ℝ}
    (hε0 : 0 < ε) : (fun x => kε ε (Φ x) * φ x) ∈ DomF n :=
  ⟨((contDiff_kε hε0).comp hD.1).mul hφ, fun σ x => by
    change kε ε (Φ (pm σ x)) * φ (pm σ x) = sgn σ * (kε ε (Φ x) * φ x)
    rw [anti hD σ x, kε_sgn_mul, hφs]; ring,
    fun x k hk => by change kε ε (Φ x) * φ x = 0; rw [hφw x k hk, mul_zero]⟩

/-! ### Geometry near a zero with `∂ₖΦ > 0` -/

/-- Around a zero with `∂ₖΦ > 0`: a ball inside `Cube ∩ U` where `∂ₖΦ > ∂ₖΦ(a)/2`, across which
`Φ` changes sign uniformly along coordinate `k`. -/
lemma box_data_line {τ : Stat} {Φ : Cfg n → ℝ} (hD : Φ ∈ Dom τ n) {U : Set (Cfg n)} (hU : IsOpen U)
    {a : Cfg n} (ha : a ∈ Cube n ∩ U) {k : Fin (n + 1)} (h0 : Φ a = 0) (hpos : 0 < dk k Φ a) :
    ∃ r r' δ : ℝ, 0 < r ∧ 0 < r' ∧ r' ≤ r ∧ 0 < δ ∧
      (∀ x : Cfg n, dist x a ≤ 2 * r → x ∈ Cube n ∩ U ∧ dk k Φ a / 2 < dk k Φ x) ∧
      ∀ y : Cfg n, dist y a ≤ r' →
        δ < Φ (Function.update y k (a k + r)) ∧ Φ (Function.update y k (a k - r)) < -δ := by
  set s0 := dk k Φ a
  have hO : IsOpen ((Cube n ∩ U) ∩ {x | s0 / 2 < dk k Φ x}) :=
    (isOpen_cube.inter hU).inter (isOpen_lt continuous_const (cont_dk hD k))
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hO a ⟨ha, by simp only [mem_ofPred_eq]; linarith⟩
  set r := ε / 4
  have hr : 0 < r := by positivity
  have hin : ∀ x : Cfg n, dist x a ≤ 2 * r → x ∈ Cube n ∩ U ∧ s0 / 2 < dk k Φ x := fun x hx =>
    hball (show dist x a < ε by simp only [r] at hx; linarith)
  have hupd : ∀ s, dist (Function.update a k s) a = |s - a k| := by
    intro s
    refine le_antisymm ((dist_pi_le_iff (abs_nonneg _)).2 fun l => ?_) ?_
    · by_cases hl : l = k
      · subst hl; simp [Real.dist_eq]
      · simp [Function.update_of_ne hl]
    · have := dist_le_pi_dist (Function.update a k s) a k
      simpa [Real.dist_eq] using this
  have hslice : ∀ s ∈ Icc (a k - r) (a k + r), s0 / 2 ≤ dk k Φ (Function.update a k s) := by
    intro s hs
    have hd : dist (Function.update a k s) a ≤ 2 * r := by
      rw [hupd]
      have : |s - a k| ≤ r := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      linarith
    exact (hin _ hd).2.le
  have hR := slice_lower (fun s => hasDerivAt_slice (diffF hD) a k s) (c := s0 / 2)
    (x0 := a k) (x1 := a k + r) (by linarith) (fun s hs => hslice s ⟨by linarith [hs.1], hs.2⟩)
  have hL := slice_lower (fun s => hasDerivAt_slice (diffF hD) a k s) (c := s0 / 2)
    (x0 := a k - r) (x1 := a k) (by linarith) (fun s hs => hslice s ⟨hs.1, by linarith [hs.2]⟩)
  simp only [Function.update_eq_self, h0] at hR hL
  have hR' : r * s0 / 2 ≤ Φ (Function.update a k (a k + r)) := by
    have e : s0 / 2 * (a k + r - a k) = r * s0 / 2 := by ring
    linarith
  have hL' : Φ (Function.update a k (a k - r)) ≤ -(r * s0 / 2) := by
    have e : s0 / 2 * (a k - (a k - r)) = r * s0 / 2 := by ring
    linarith
  set δ := r * s0 / 4 with hδd
  have hδ : 0 < δ := by positivity
  have c1 : ContinuousAt (fun y : Cfg n => Φ (Function.update y k (a k + r))) a :=
    (hD.1.continuous.comp (continuous_id.update k continuous_const)).continuousAt
  have c2 : ContinuousAt (fun y : Cfg n => Φ (Function.update y k (a k - r))) a :=
    (hD.1.continuous.comp (continuous_id.update k continuous_const)).continuousAt
  obtain ⟨η1, hη1, h1⟩ := Metric.continuousAt_iff.mp c1 δ hδ
  obtain ⟨η2, hη2, h2⟩ := Metric.continuousAt_iff.mp c2 δ hδ
  refine ⟨r, min r (min η1 η2 / 2), δ, hr, lt_min hr (by positivity), min_le_left _ _, hδ, hin,
    fun y hy => ?_⟩
  have hy1 : dist y a < η1 := by
    linarith [min_le_right r (min η1 η2 / 2), min_le_left η1 η2]
  have hy2 : dist y a < η2 := by
    linarith [min_le_right r (min η1 η2 / 2), min_le_right η1 η2]
  have e1 := h1 hy1
  have e2 := h2 hy2
  rw [Real.dist_eq] at e1 e2
  constructor
  · have := (abs_lt.mp e1).1; linarith
  · have := (abs_lt.mp e2).2; linarith

/-- The box `|xₖ - aₖ| ≤ r`, `|xₗ - aₗ| ≤ r'` (`l ≠ k`). -/
def boxL (a : Cfg n) (k : Fin (n + 1)) (r r' : ℝ) : Set (Cfg n) :=
  Set.pi univ fun l => Icc (a l - if l = k then r else r') (a l + if l = k then r else r')

lemma isCompact_boxL (a : Cfg n) (k : Fin (n + 1)) (r r' : ℝ) : IsCompact (boxL a k r r') :=
  isCompact_univ_pi fun _ => isCompact_Icc

lemma measurableSet_boxL (a : Cfg n) (k : Fin (n + 1)) (r r' : ℝ) :
    MeasurableSet (boxL a k r r') := MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma dist_le_of_boxL {a : Cfg n} {k : Fin (n + 1)} {r r' : ℝ} (hrr : r' ≤ r) (hr' : 0 ≤ r')
    {x : Cfg n} (hx : x ∈ boxL a k r r') : dist x a ≤ r := by
  refine (dist_pi_le_iff (hr'.trans hrr)).2 fun l => ?_
  have := hx l (mem_univ _)
  rw [Real.dist_eq, abs_le]
  by_cases hl : l = k
  · subst hl; simp only [ite_true] at this; constructor <;> linarith [this.1, this.2]
  · simp only [hl, ite_false] at this; constructor <;> linarith [this.1, this.2]

/-- Across the box, the integral of `k₂(Φ) ∂ₖΦ` is at least the box's cross-section `(2r')ⁿ`. -/
lemma box_integral_line {τ : Stat} {Φ : Cfg n → ℝ} (hD : Φ ∈ Dom τ n) {ε : ℝ} (hε0 : 0 < ε)
    {a : Cfg n}
    {k : Fin (n + 1)} {r r' δ : ℝ} (hr : 0 < r) (hr' : 0 < r') (hεδ : ε ≤ δ)
    (hsign : ∀ y : Cfg n, dist y a ≤ r' →
      δ < Φ (Function.update y k (a k + r)) ∧ Φ (Function.update y k (a k - r)) < -δ) :
    (2 * r') ^ n ≤ ∫ x in boxL a k r r', k2 ε (Φ x) * dk k Φ x := by
  have hk2c : Continuous (k2 ε) := continuous_k2 hε0
  have hkc : Continuous (kε ε) := (contDiff_kε hε0).continuous
  set F : Cfg n → ℝ := fun x => k2 ε (Φ x) * dk k Φ x
  have hF : Continuous F := (hk2c.comp hD.1.continuous).mul (cont_dk hD k)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Cfg n)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm
  have hcomp : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth k p.1 p.2 := fun _ => rfl
  set B' : Set (Fin n → ℝ) := Icc (fun l => a (k.succAbove l) - r')
    (fun l => a (k.succAbove l) + r')
  have hpre : e.symm ⁻¹' boxL a k r r' = Icc (a k - r) (a k + r) ×ˢ B' := by
    ext ⟨t, y⟩
    simp only [mem_preimage, mem_prod, boxL, Set.mem_pi, mem_univ, true_implies, hcomp]
    rw [k.forall_iff_succAbove]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Fin.succAbove_ne,
      ite_true, ite_false, mem_Icc, B', Pi.le_def, ← forall_and]
  have h := he.setIntegral_preimage_emb e.symm.measurableEmbedding F (boxL a k r r')
  rw [hpre] at h
  rw [← h, ← Measure.prod_restrict]
  simp only [hcomp]
  have hc : Continuous fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth k p.1 p.2) :=
    hF.comp (by fun_prop)
  rw [integral_prod_symm (fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth k p.1 p.2)) (by
    rw [Measure.prod_restrict]
    exact hc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc))]
  have inner : ∀ y : Fin n → ℝ, ∫ t in Icc (a k - r) (a k + r), F (Fin.insertNth k t y) =
      kε ε (Φ (Fin.insertNth k (a k + r) y)) - kε ε (Φ (Fin.insertNth k (a k - r) y)) := by
    intro y
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => kε ε (Φ (Fin.insertNth k t y)))
      (fun t _ => (hasDerivAt_kε hε0 _).comp t (hasDerivAt_insertNth (diffF hD) k y t))
      ((hF.comp (by fun_prop)).intervalIntegrable _ _)
  simp only [inner]
  have hcont : Continuous fun y : Fin n → ℝ => kε ε (Φ (Fin.insertNth k (a k + r) y)) -
      kε ε (Φ (Fin.insertNth k (a k - r) y)) :=
    (hkc.comp (hD.1.continuous.comp (by fun_prop))).sub
      (hkc.comp (hD.1.continuous.comp (by fun_prop)))
  have hB'c : IsCompact B' := isCompact_Icc
  have hmono : ∫ y in B', (1 : ℝ) ≤ ∫ y in B', (kε ε (Φ (Fin.insertNth k (a k + r) y)) -
      kε ε (Φ (Fin.insertNth k (a k - r) y))) := by
    refine setIntegral_mono_on (integrableOn_const (hB'c.measure_lt_top.ne))
      (hcont.continuousOn.integrableOn_compact hB'c)
      measurableSet_Icc fun y hy => ?_
    set y0 : Cfg n := Fin.insertNth k (a k) y
    have hy0 : dist y0 a ≤ r' := by
      refine (dist_pi_le_iff hr'.le).2 fun l => ?_
      refine Fin.succAboveCases k ?_ (fun l' => ?_) l
      · simp [y0, hr'.le]
      · have h1 := hy.1 l'
        have h2 := hy.2 l'
        simp only [y0, Fin.insertNth_apply_succAbove, Real.dist_eq, abs_le]
        constructor <;> linarith
    obtain ⟨h1, h2⟩ := hsign y0 hy0
    simp only [y0, Fin.update_insertNth] at h1 h2
    have k1 := kε_ge_half hε0 (s := Φ (Fin.insertNth k (a k + r) y)) (by linarith)
    have k2' := kε_le_neg_half hε0 (s := Φ (Fin.insertNth k (a k - r) y)) (by linarith)
    linarith
  refine le_trans (le_of_eq ?_) hmono
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc_pi]
  simp only [show ∀ l : Fin n, a (k.succAbove l) + r' - (a (k.succAbove l) - r') = 2 * r' from
    fun l => by ring, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]

/-! ### Small lemmas kept out of the main proof -/

lemma fderiv_comp_applyL {F F' : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (F' s) s) {Φ : Cfg n → ℝ}
    (hΦ : Differentiable ℝ Φ) (x m : Cfg n) :
    fderiv ℝ (fun y => F (Φ y)) x m = F' (Φ x) * fderiv ℝ Φ x m := by
  have h := (hF (Φ x)).comp_hasFDerivAt x (hΦ x).hasFDerivAt
  rw [show (fun y => F (Φ y)) = F ∘ Φ from rfl, h.fderiv]
  simp [smul_eq_mul]

lemma fderiv_mul_applyL {f g : Cfg n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x m : Cfg n) :
    fderiv ℝ (fun y => f y * g y) x m = fderiv ℝ f x m * g x + f x * fderiv ℝ g x m := by
  have h : HasFDerivAt (fun y => f y * g y) (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x :=
    (hf x).hasFDerivAt.mul (hg x).hasFDerivAt
  rw [h.fderiv]
  simp [smul_eq_mul]
  ring

lemma abs_dk_le_norm (f : Cfg n → ℝ) (k : Fin (n + 1)) (x : Cfg n) :
    |dk k f x| ≤ ‖fderiv ℝ f x‖ := by
  have h := (fderiv ℝ f x).le_opNorm (Pi.single k 1)
  rw [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] at h
  exact h

/-- A configuration without collisions has a positive minimal gap. -/
lemma exists_far {a : Cfg n} (ha : Function.Injective a) : ∃ g, 0 < g ∧ Far g a := by
  set P := (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter fun p => p.1 ≠ p.2
  by_cases hP : P.Nonempty
  · set m := P.inf' hP fun p => |a p.1 - a p.2|
    have hm : 0 < m := (Finset.lt_inf'_iff hP).2 fun p hp => by
      have := (Finset.mem_filter.1 hp).2
      exact abs_pos.2 (sub_ne_zero.2 (ha.ne this))
    refine ⟨m / 2, by positivity, fun i j hij => ?_⟩
    have : m ≤ |a i - a j| :=
      Finset.inf'_le (f := fun p : Fin (n + 1) × Fin (n + 1) => |a p.1 - a p.2|) (b := (i, j))
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)
    linarith
  · refine ⟨1, one_pos, fun i j hij => absurd ⟨(i, j), ?_⟩ hP⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩

lemma Far.mono {η η' : ℝ} (h : η' ≤ η) {x : Cfg n} (hx : Far η x) : Far η' x :=
  fun i j hij => lt_of_le_of_lt h (hx i j hij)

lemma ar_lowN {s0 k d S p : ℝ} (hs : 0 < s0) (hk : 0 < k) (hd : s0 / 2 < d) (hS : d ^ 2 ≤ S)
    (hp : 1 ≤ p) : s0 / 2 * (k * d) ≤ k * S * p := by
  have hd0 : 0 < d := by linarith
  have e1 : s0 / 2 * (k * d) ≤ k * d * d := by nlinarith [mul_pos hk hd0]
  have e2 : k * d * d ≤ k * S := by nlinarith
  have e3 : k * S ≤ k * S * p := by
    have : 0 ≤ k * S := by nlinarith [sq_nonneg d]
    nlinarith
  linarith

/-- The pointwise identity behind the cross term, away from collisions. -/
lemma ptwise_far (dH dφ dΦ dφs dg : Fin (n + 1) → ℝ) {S S0 kk hh k2v V Φv φsv : ℝ}
    (hdH : ∀ l, dH l = S * (kk * dΦ l)) (hdφ : ∀ l, dφ l = S0 * dφs l)
    (hdg : ∀ l, dg l = k2v * dΦ l * φsv + kk * dφs l) (hSS : S * S0 = 1) :
    ∑ l, dH l * dφ l + V * (S * hh * (S0 * φsv)) =
      ∑ l, dΦ l * dg l + V * (Φv * (kk * φsv)) +
        (V * (hh - Φv * kk) * φsv - k2v * (∑ l, dΦ l ^ 2) * φsv) := by
  have e1 : ∑ l, dH l * dφ l = (S * S0) * ∑ l, kk * (dΦ l * dφs l) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; rw [hdH, hdφ]; ring
  have e2 : ∑ l, dΦ l * dg l = k2v * (∑ l, dΦ l ^ 2) * φsv + ∑ l, kk * (dΦ l * dφs l) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_; rw [hdg]; ring
  rw [e1, e2, hSS]
  linear_combination (V * hh * φsv) * hSS

/-- The energy excess of the competitor away from collisions. -/
lemma energy_far (dH dΦ : Fin (n + 1) → ℝ) {S kk hh V aV Φv ε : ℝ}
    (hdH : ∀ l, dH l = S * (kk * dΦ l)) (hS : S ^ 2 = 1) (hk : kk ^ 2 ≤ 1)
    (hVle : V * (hh ^ 2 - Φv ^ 2) ≤ aV * (2 * ε * |Φv|)) :
    ∑ l, dH l * dH l + V * (S * hh * (S * hh)) - (∑ l, dΦ l * dΦ l + V * (Φv * Φv)) ≤
      2 * ε * (aV * |Φv|) := by
  have e1 : ∑ l, dH l * dH l = kk ^ 2 * ∑ l, dΦ l * dΦ l := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; rw [hdH]
    linear_combination (kk ^ 2 * dΦ l ^ 2) * hS
  have e2 : S * hh * (S * hh) = hh ^ 2 := by linear_combination hh ^ 2 * hS
  have hpos : 0 ≤ ∑ l, dΦ l * dΦ l := Finset.sum_nonneg fun l _ => mul_self_nonneg _
  rw [e1, e2]
  have : (kk ^ 2 - 1) * ∑ l, dΦ l * dΦ l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos
  nlinarith

/-- The energy excess of the competitor near collisions is bounded. -/
lemma energy_near (dH dΦ : Fin (n + 1) → ℝ) {A V Hv Φv m1 m2 R : ℝ}
    (hdH : ∀ l, |dH l| ≤ A) (hV1 : V * (Hv * Hv) ≤ m1) (hV2 : -(V * (Φv * Φv)) ≤ m2)
    (hR : 0 ≤ R) :
    ∑ l, dH l * dH l + V * (Hv * Hv) - (∑ l, dΦ l * dΦ l + V * (Φv * Φv)) ≤
      R + ((n + 1) * A ^ 2 + m1 + m2) := by
  have h1 : ∑ l, dH l * dH l ≤ ∑ _l : Fin (n + 1), A ^ 2 := Finset.sum_le_sum fun l _ => by
    rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdH l) 2
  have h2 : 0 ≤ ∑ l, dΦ l * dΦ l := Finset.sum_nonneg fun l _ => mul_self_nonneg _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  push_cast at h1
  linarith

/-! ### Critical zeros away from collisions -/

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

set_option maxHeartbeats 2000000 in
-- the main proof is long and keeps many constants in context
/-- A ground state cannot vanish at a collision-free point of the cube where `∂ₖΦ > 0`. -/
lemma no_pos_dk {Φ : Cfg n → ℝ} (hΦ : IsGS (settingF n w hw) v Φ) {a : Cfg n} (ha : a ∈ Cube n)
    (hinj : Function.Injective a) {k : Fin (n + 1)} (h0 : Φ a = 0) (hpos : 0 < dk k Φ a) :
    False := by
  have hD : Φ ∈ DomF n := hΦ.1
  set s0 := dk k Φ a with hs0
  obtain ⟨g0, hg0p, hfa⟩ := exists_far hinj
  have hUo : IsOpen {x : Cfg n | Far (g0 / 2) x} := isOpen_far _
  have haU : a ∈ {x : Cfg n | Far (g0 / 2) x} := hfa.mono (by linarith)
  obtain ⟨r, r', δ, hr, hr', hrr, hδ, hin, hsign⟩ := box_data_line hD hUo ⟨ha, haU⟩ h0 hpos
  -- a bump at `a`, symmetrised; it vanishes near collisions
  let β : ContDiffBump a := ⟨r, 2 * r, hr, by linarith⟩
  have hβU : ∀ x, β x ≠ 0 → x ∈ Cube n ∧ Far (g0 / 2) x := by
    intro x hx
    have : x ∈ tsupport β := subset_tsupport _ hx
    rw [β.tsupport_eq] at this
    exact (hin x (mem_closedBall.mp this)).1
  have hβout : ∀ x, x ∉ Cube n → β x = 0 := fun x hx => by
    by_contra h; exact hx (hβU x h).1
  set W : Set (Cfg n) := {x | ∃ i j, i ≠ j ∧ |x i - x j| < g0 / 2} with hWd
  have hWo : IsOpen W := by
    have : W = ⋃ i, ⋃ j, {x : Cfg n | i ≠ j ∧ |x i - x j| < g0 / 2} := by
      ext x; simp [W]
    rw [this]
    refine isOpen_iUnion fun i => isOpen_iUnion fun j => ?_
    by_cases h : i = j
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, true_and]
      exact isOpen_lt (by fun_prop) continuous_const
  have hβW : ∀ x ∈ W, β x = 0 := fun x hx => by
    by_contra h
    obtain ⟨i, j, hij, hlt⟩ := hx
    have := (hβU x h).2 i j hij
    linarith
  have hWpm : ∀ x ∈ W, ∀ σ : Equiv.Perm (Fin (n + 1)), pm σ x ∈ W := by
    rintro x ⟨i, j, hij, hlt⟩ σ
    refine ⟨σ⁻¹ i, σ⁻¹ j, fun h => hij (σ⁻¹.injective h), ?_⟩
    simpa using hlt
  set φs : Cfg n → ℝ := sym β with hφsd
  have hφsc : ContDiff ℝ 2 φs := contDiff_sym β.contDiff
  have hφss : ∀ σ x, φs (pm σ x) = φs x := sym_pm β
  have hφsw : ∀ x l, (x l = 0 ∨ x l = 1) → φs x = 0 := fun x l hl =>
    Finset.sum_eq_zero fun σ _ => hβout _ (pm_not_mem_cube hl σ)
  have hφs0 : ∀ x, 0 ≤ φs x := fun x => Finset.sum_nonneg fun σ _ => β.nonneg' _
  have hφsW : ∀ x, ¬ Far (g0 / 4) x → φs x = 0 ∧ ∀ l, dk l φs x = 0 := by
    intro x hx
    have hxW : x ∈ W := by
      simp only [Far, not_forall, not_lt] at hx
      obtain ⟨i, j, hij, hle⟩ := hx
      exact ⟨i, j, hij, by linarith⟩
    have hz : ∀ y ∈ W, φs y = 0 := fun y hy =>
      Finset.sum_eq_zero fun σ _ => hβW _ (hWpm y hy σ)
    have hev : φs =ᶠ[𝓝 x] fun _ => 0 := Filter.eventually_of_mem (hWo.mem_nhds hxW) hz
    have hfd : fderiv ℝ φs x = 0 := by rw [hev.fderiv_eq]; exact fderiv_const_apply _
    exact ⟨hz x hxW, fun l => by simp [dk, hfd]⟩
  -- the box
  set Bx := boxL a k r r' with hBx
  have hBxd : ∀ x ∈ Bx, dist x a ≤ r := fun x hx => dist_le_of_boxL hrr hr'.le hx
  have hφs1 : ∀ x ∈ Bx, 1 ≤ φs x := fun x hx => by
    have h1 : β (pm 1 x) = 1 := β.one_of_mem_closedBall (mem_closedBall.mpr (hBxd x hx))
    have : β (pm 1 x) ≤ φs x :=
      Finset.single_le_sum (f := fun σ => β (pm σ x)) (fun σ _ => β.nonneg' _)
        (Finset.mem_univ (1 : Equiv.Perm (Fin (n + 1))))
    linarith
  have hBxS : Bx ⊆ Cube n := fun x hx => (hin x (by linarith [hBxd x hx])).1.1
  have hBxd1 : ∀ x ∈ Bx, s0 / 2 < dk k Φ x := fun x hx => (hin x (by linarith [hBxd x hx])).2
  -- constants independent of `ε`
  set E := Q (settingF n w hw) v Φ / ip (μ := μN n) Φ Φ with hE
  set V : Cfg n → ℝ := fun x => w x + LN n v x - E with hV
  have hVc : Continuous V := (hw.add (continuous_LN v)).sub continuous_const
  have hφc : Continuous φs := hφsc.continuous
  have hΦc : Continuous Φ := hD.1.continuous
  obtain ⟨Mf, hMf⟩ := isCompact_cubeC.exists_bound_of_continuousOn
    (hD.1.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨Pm, hPm⟩ := isCompact_cubeC.exists_bound_of_continuousOn hΦc.continuousOn
  obtain ⟨Vm, hVm⟩ := isCompact_cubeC.exists_bound_of_continuousOn hVc.continuousOn
  obtain ⟨Cs, hCs0, hCs⟩ := exists_dk_Sgn_bound (n := n)
  set Nc : ℝ := ((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℕ) : ℝ) with hNcd
  have hNc0 : 0 ≤ Nc := by positivity
  set M := max Mf 0 with hMd
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMq : ∀ y ∈ CubeC n, ∀ l, |dk l Φ y| ≤ M := fun y hy l =>
    (abs_dk_le_norm Φ l y).trans ((hMf y hy).trans (le_max_left _ _))
  have hSqK : ∀ x ∈ Cube n, x ∈ CubeC n := fun x hx => cube_subset hx
  set A := Cs * M + Nc * M with hAd
  have hA0 : 0 ≤ A := by positivity
  set Vm' := max Vm 0 with hVm'd
  set Kθ := (n + 1) * A ^ 2 + Vm' * (Nc ^ 2 * Pm ^ 2) + Vm' * Pm ^ 2 with hKθd
  have hKθ0 : 0 ≤ Kθ := by positivity
  set K1 := ∫ x, |V x| * |Φ x| ∂μN n with hK1d
  have hK1 : 0 ≤ K1 := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  set K2 := ∫ x, |V x| * φs x ∂μN n with hK2d
  have hK2 : 0 ≤ K2 := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (hφs0 x)
  -- the antisymmetric test function `Sgn η₀ · φs`, independent of `ε`
  set η0 := g0 / 4 with hη0d
  have hη0 : 0 < η0 := by positivity
  set φ : Cfg n → ℝ := fun x => Sgn η0 x * φs x with hφd
  have hφm : φ ∈ DomF n := Sgn_mul_mem hφsc hφss hφsw η0
  set C := RfL .fer w hw v E φ φ with hCd
  have hC : 0 ≤ C := RfL_nonneg hΦ hφm
  set L := s0 / 2 * (2 * r') ^ n with hLd
  have hL : 0 < L := by positivity
  set K1' := K1 + (n + 1) ^ 2 * Kθ with hK1'd
  have hK1' : 0 ≤ K1' := by positivity
  set ε := min δ (min (L / (4 * (K2 + 1))) (min (L ^ 2 / (16 * (K1' * C + 1))) η0)) with hεd
  have hε0 : 0 < ε := lt_min hδ (lt_min (by positivity) (lt_min (by positivity) hη0))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ L / (4 * (K2 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ L ^ 2 / (16 * (K1' * C + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε ≤ η0 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the competitor `Sgn ε · h_ε(Φ)` and the Euler–Lagrange test `k_ε(Φ) φs`
  have hhc2 : ContDiff ℝ 2 (fun x => hε ε (Φ x)) := (contDiff_hε hε0).comp hD.1
  set H : Cfg n → ℝ := fun x => Sgn ε x * hε ε (Φ x) with hHd
  have hHm : H ∈ DomF n := Sgn_mul_mem hhc2 (fun σ x => hε_comp_sym hD σ x)
    (fun x l hl => by simp only [hD.2.2 x l hl, hε_zero hε0]) ε
  set g : Cfg n → ℝ := fun x => kε ε (Φ x) * φs x with hgd
  have hgm : g ∈ DomF n := kε_mul_mem_line hD hφsc hφss hφsw hε0
  have hhd : Differentiable ℝ (fun x => hε ε (Φ x)) := hhc2.differentiable (by norm_num)
  have hSd : ∀ η, Differentiable ℝ (Sgn (n := n) η) := fun η =>
    (contDiff_Sgn η).differentiable (by norm_num)
  have hφsd' : Differentiable ℝ φs := hφsc.differentiable (by norm_num)
  have dH : ∀ l x, dk l H x =
      dk l (Sgn ε) x * hε ε (Φ x) + Sgn ε x * (kε ε (Φ x) * dk l Φ x) := fun l x => by
    simp only [dk, H]
    rw [fderiv_mul_applyL (hSd ε) hhd, fderiv_comp_applyL (hasDerivAt_hε hε0) (diffF hD)]
  have dφ : ∀ l x, dk l φ x = dk l (Sgn η0) x * φs x + Sgn η0 x * dk l φs x := fun l x => by
    simp only [dk, φ]; rw [fderiv_mul_applyL (hSd η0) hφsd']
  have dg : ∀ l x, dk l g x = k2 ε (Φ x) * dk l Φ x * φs x + kε ε (Φ x) * dk l φs x :=
    fun l x => by
      simp only [dk, g]
      rw [fderiv_mul_applyL (f := fun y => kε ε (Φ y)) (g := φs)
        (((contDiff_kε hε0).comp hD.1).differentiable (by norm_num)) hφsd',
        fderiv_comp_applyL (hasDerivAt_kε hε0) (diffF hD)]
  have hk2c : Continuous (k2 ε) := continuous_k2 hε0
  have hkc : Continuous (kε ε) := (contDiff_kε hε0).continuous
  have hhc : Continuous (hε ε) := (contDiff_hε hε0).continuous
  have hgradc : Continuous fun x => ∑ l, dk l Φ x ^ 2 :=
    continuous_finsetSum _ fun l _ => (cont_dk hD l).pow 2
  set G : Cfg n → ℝ := fun x => k2 ε (Φ x) * (∑ l, dk l Φ x ^ 2) * φs x with hGd
  have hGc : Continuous G := ((hk2c.comp hΦc).mul hgradc).mul hφc
  -- lower bound: `∫ G ≥ L`
  have hlow : L ≤ ∫ x, G x ∂μN n := by
    have hcpt : IsCompact Bx := isCompact_boxL a k r r'
    have h1 : ∫ x in Bx, G x ≤ ∫ x, G x ∂μN n :=
      setIntegral_mono_set (integrableN hGc)
        (ae_of_all _ fun x => mul_nonneg (mul_nonneg (k2_pos hε0 _).le
          (Finset.sum_nonneg fun l _ => sq_nonneg _)) (hφs0 x)) hBxS.eventuallyLE
    have hFc : Continuous fun x => k2 ε (Φ x) * dk k Φ x := (hk2c.comp hΦc).mul (cont_dk hD k)
    have h2 : ∫ x in Bx, s0 / 2 * (k2 ε (Φ x) * dk k Φ x) ≤ ∫ x in Bx, G x := by
      refine setIntegral_mono_on ((continuous_const.mul hFc).continuousOn.integrableOn_compact
        hcpt) (hGc.continuousOn.integrableOn_compact hcpt) (measurableSet_boxL a k r r')
        fun x hx => ?_
      exact ar_lowN hpos (k2_pos hε0 (Φ x)) (hBxd1 x hx)
        (Finset.single_le_sum (f := fun l => dk l Φ x ^ 2) (fun l _ => sq_nonneg _)
          (Finset.mem_univ k)) (hφs1 x hx)
    have h3 := box_integral_line hD hε0 hr hr' hεδ hsign
    rw [integral_const_mul] at h2
    calc L = s0 / 2 * (2 * r') ^ n := rfl
      _ ≤ s0 / 2 * ∫ x in Bx, k2 ε (Φ x) * dk k Φ x :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ ≤ _ := h2
      _ ≤ _ := h1
  -- the cross term
  set X : Cfg n → ℝ := fun x => V x * (hε ε (Φ x) - Φ x * kε ε (Φ x)) * φs x with hXd
  have hXc : Continuous X := (hVc.mul ((hhc.comp hΦc).sub (hΦc.mul (hkc.comp hΦc)))).mul hφc
  set B := RfL .fer w hw v E H φ with hBd
  have hU : ∫ x, G x ∂μN n = ∫ x, X x ∂μN n - B := by
    have hEL := RfL_EL hΦ hgm
    rw [RfL_eq E hD hgm] at hEL
    rw [hBd, RfL_eq E hHm hφm]
    have iA : Integrable (fun x => ∑ l, dk l Φ x * dk l g x +
        (w x + LN n v x - E) * (Φ x * g x)) (μN n) :=
      integrableN ((cont_kin hD hgm).add (hVc.mul (hΦc.mul hgm.1.continuous)))
    have iXG : Integrable (fun x => X x - G x) (μN n) := integrableN (hXc.sub hGc)
    have key : ∫ x, (∑ l, dk l H x * dk l φ x + (w x + LN n v x - E) * (H x * φ x)) ∂μN n =
        ∫ x, (∑ l, dk l Φ x * dk l g x + (w x + LN n v x - E) * (Φ x * g x)) ∂μN n +
          ∫ x, (X x - G x) ∂μN n := by
      rw [← integral_add iA iXG]
      congr 1; funext x
      by_cases hfar : Far (g0 / 4) x
      · have hfε : Far ε x := hfar.mono hε3
        have hf0 : Far η0 x := hfar
        have hSS := Sgn_mul_Sgn_far hε0 hη0 hfε hf0
        exact ptwise_far (fun l => dk l H x) (fun l => dk l φ x) (fun l => dk l Φ x)
          (fun l => dk l φs x) (fun l => dk l g x)
          (fun l => by rw [dH, dk_Sgn_far hε0 hfε, zero_mul, zero_add])
          (fun l => by rw [dφ, dk_Sgn_far hη0 hf0, zero_mul, zero_add])
          (fun l => dg l x) hSS
      · obtain ⟨e0, e1⟩ := hφsW x hfar
        simp only [X, G, H, φ, g, dφ, dg, e0, e1]
        simp
    rw [key, hEL, zero_add, integral_sub (integrableN hXc) (integrableN hGc)]
    ring
  have hB1 : |∫ x, X x ∂μN n| ≤ ε * K2 := by
    calc |∫ x, X x ∂μN n| ≤ ∫ x, |X x| ∂μN n := abs_integral_le_integral_abs
      _ ≤ ∫ x, ε * (|V x| * φs x) ∂μN n := by
          refine integral_mono (integrableN hXc.abs)
            (integrableN (continuous_const.mul (hVc.abs.mul hφc))) fun x => ?_
          simp only [X, abs_mul, abs_of_nonneg (hφs0 x)]
          exact ar_X (abs_hε_sub hε0 (Φ x)) (hφs0 x)
      _ = ε * K2 := integral_const_mul _ _
  -- the energy of the competitor
  have hB2 : RfL .fer w hw v E H H ≤ 2 * ε * K1' := by
    have hself := RfL_self hΦ
    rw [RfL_eq E hD hD] at hself
    rw [RfL_eq E hHm hHm]
    have iΦ : Integrable (fun x => ∑ l, dk l Φ x * dk l Φ x +
        (w x + LN n v x - E) * (Φ x * Φ x)) (μN n) :=
      integrableN ((cont_kin hD hD).add (hVc.mul (hΦc.mul hΦc)))
    have ih : Integrable (fun x => ∑ l, dk l H x * dk l H x +
        (w x + LN n v x - E) * (H x * H x)) (μN n) :=
      integrableN ((cont_kin hHm hHm).add (hVc.mul (hHm.1.continuous.mul hHm.1.continuous)))
    have ihΦ : Integrable (fun x => (∑ l, dk l H x * dk l H x +
        (w x + LN n v x - E) * (H x * H x)) - (∑ l, dk l Φ x * dk l Φ x +
          (w x + LN n v x - E) * (Φ x * Φ x))) (μN n) := ih.sub iΦ
    have e : ∫ x, (∑ l, dk l H x * dk l H x + (w x + LN n v x - E) * (H x * H x)) ∂μN n =
        ∫ x, (∑ l, dk l Φ x * dk l Φ x + (w x + LN n v x - E) * (Φ x * Φ x)) ∂μN n +
          ∫ x, ((∑ l, dk l H x * dk l H x + (w x + LN n v x - E) * (H x * H x)) -
            (∑ l, dk l Φ x * dk l Φ x + (w x + LN n v x - E) * (Φ x * Φ x))) ∂μN n := by
      rw [← integral_add iΦ ihΦ]
      congr 1; funext x; ring
    set St : Set (Cfg n) := NearS ε with hStd
    have hStm : MeasurableSet St := measurableSet_NearS ε
    have iR : Integrable (fun x => 2 * ε * (|V x| * |Φ x|) + St.indicator (fun _ => Kθ) x)
        (μN n) :=
      (integrableN (continuous_const.mul (hVc.abs.mul hΦc.abs))).add
        ((integrableN (continuous_const (y := Kθ))).indicator hStm)
    rw [e, hself, zero_add]
    calc _ ≤ ∫ x, (2 * ε * (|V x| * |Φ x|) + St.indicator (fun _ => Kθ) x) ∂μN n := by
          refine integral_mono_ae ihΦ iR ?_
          refine (ae_restrict_iff' measurableSet_cube).2 (ae_of_all _ fun x hx => ?_)
          have hxK := hSqK x hx
          have hsq := abs_hε_sq_sub hε0 (Φ x)
          have hVle : (w x + LN n v x - E) * (hε ε (Φ x) ^ 2 - Φ x ^ 2) ≤
              |V x| * (2 * ε * |Φ x|) := by
            calc (w x + LN n v x - E) * (hε ε (Φ x) ^ 2 - Φ x ^ 2)
                ≤ |(w x + LN n v x - E) * (hε ε (Φ x) ^ 2 - Φ x ^ 2)| := le_abs_self _
              _ = |V x| * |hε ε (Φ x) ^ 2 - Φ x ^ 2| := by rw [abs_mul]
              _ ≤ |V x| * (2 * ε * |Φ x|) :=
                  mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
          have hR0 : 0 ≤ 2 * ε * (|V x| * |Φ x|) := by positivity
          simp only
          by_cases hfar : Far ε x
          · rw [indicator_of_notMem (show x ∉ St from fun h => h hfar), add_zero]
            obtain ⟨σ, hσ1, -⟩ := Sgn_eventually_const hε0 hfar
            have hS2 : Sgn ε x ^ 2 = 1 := by rw [hσ1, sq, sgn_mul_self]
            exact energy_far (fun l => dk l H x) (fun l => dk l Φ x)
              (fun l => by rw [dH, dk_Sgn_far hε0 hfar, zero_mul, zero_add]) hS2
              (kε_sq_le hε0 (Φ x)) hVle
          · rw [indicator_of_mem (show x ∈ St from hfar)]
            simp only [Far, not_forall, not_lt] at hfar
            obtain ⟨i, j, hij, hle⟩ := hfar
            have hΦd : |Φ x| ≤ M * ε :=
              (abs_le_pair hD hij (fun y hy => hMq y hy i) hxK).trans
                (mul_le_mul_of_nonneg_left hle hM0)
            have hhΦ := abs_hε_le hε0 (Φ x)
            have hS := abs_Sgn_le (n := n) ε x
            have hk := abs_kε_le hε0 (Φ x)
            have bl : ∀ l, |dk l H x| ≤ A := by
              intro l
              rw [dH]
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul]
                calc |dk l (Sgn ε) x| * |hε ε (Φ x)| ≤ (Cs / ε) * (M * ε) :=
                      mul_le_mul (hCs ε hε0 l x) (hhΦ.trans hΦd) (abs_nonneg _) (by positivity)
                  _ = Cs * M := by field_simp
              · rw [abs_mul, abs_mul]
                calc |Sgn ε x| * (|kε ε (Φ x)| * |dk l Φ x|) ≤ Nc * (1 * M) :=
                      mul_le_mul hS (mul_le_mul hk (hMq x hxK l) (abs_nonneg _) zero_le_one)
                        (by positivity) hNc0
                  _ = Nc * M := by ring
            have hVq : |V x| ≤ Vm' := by
              have := hVm x hxK; rw [Real.norm_eq_abs] at this
              exact this.trans (le_max_left _ _)
            have hPq : |Φ x| ≤ Pm := by
              have := hPm x hxK; rw [Real.norm_eq_abs] at this; exact this
            have hHq : |H x| ≤ Nc * Pm := by
              simp only [H, abs_mul]
              exact mul_le_mul hS (hhΦ.trans hPq) (abs_nonneg _) hNc0
            have hH2 : H x * H x ≤ Nc ^ 2 * Pm ^ 2 := by
              rw [← abs_mul_abs_self, ← sq, ← mul_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) hHq 2
            have hΦ2 : Φ x * Φ x ≤ Pm ^ 2 := by
              rw [← abs_mul_abs_self, ← sq]
              exact pow_le_pow_left₀ (abs_nonneg _) hPq 2
            have hV1 : (w x + LN n v x - E) * (H x * H x) ≤ Vm' * (Nc ^ 2 * Pm ^ 2) := by
              calc _ ≤ |w x + LN n v x - E| * (H x * H x) :=
                    mul_le_mul_of_nonneg_right (le_abs_self _) (mul_self_nonneg _)
                _ ≤ _ := mul_le_mul hVq hH2 (mul_self_nonneg _) (le_max_right _ _)
            have hV2 : -((w x + LN n v x - E) * (Φ x * Φ x)) ≤ Vm' * Pm ^ 2 := by
              calc _ ≤ |w x + LN n v x - E| * (Φ x * Φ x) := by
                    rw [← neg_mul]
                    exact mul_le_mul_of_nonneg_right (neg_le_abs _) (mul_self_nonneg _)
                _ ≤ _ := mul_le_mul hVq hΦ2 (mul_self_nonneg _) (le_max_right _ _)
            exact (energy_near (fun l => dk l H x) (fun l => dk l Φ x) bl hV1 hV2
              hR0).trans_eq (by ring)
      _ = 2 * ε * K1 + (μN n).real St * Kθ := by
          rw [integral_add (f := fun x => 2 * ε * (|V x| * |Φ x|))
            (g := St.indicator fun _ => Kθ)
            (integrableN (continuous_const.mul (hVc.abs.mul hΦc.abs)))
            ((integrableN (continuous_const (y := Kθ))).indicator hStm),
            integral_const_mul, integral_indicator_const _ hStm, smul_eq_mul]
      _ ≤ 2 * ε * K1 + (n + 1) ^ 2 * (2 * ε) * Kθ := by
          have := mul_le_mul_of_nonneg_right (mu_near_le (n := n) hε0.le) hKθ0
          linarith
      _ = 2 * ε * K1' := by simp only [K1']; ring
  have hB3 : B ^ 2 ≤ RfL .fer w hw v E H H * C := by
    refine discr_le hC fun t => ?_
    have h := RfL_nonneg hΦ ((DomF n).add_mem hHm ((DomF n).smul_mem t hφm))
    rw [RfL_expand E hHm hφm t] at h
    linarith
  have hA : L ≤ ε * K2 + |B| := by
    have h1 := hlow
    rw [hU] at h1
    have h2 := (abs_le.mp hB1).2
    have h3 := le_abs_self (∫ x, X x ∂μN n)
    linarith [neg_abs_le B]
  exact final_arith hL hK1' hK2 hC hε0 hε1 hε2 hA hB2 hB3

/-- **Critical zeros away from collisions.** A ground state of `n + 1` interacting fermions has
zero gradient at each of its zeros in the open cube without collisions. -/
theorem grad_zero_at_zero_line {Φ : Cfg n → ℝ} (hΦ : IsGS (settingF n w hw) v Φ) :
    ∀ x ∈ Cube n, Function.Injective x → Φ x = 0 → ∀ k, dk k Φ x = 0 := by
  intro x hx hinj h0 k
  by_contra hd
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hN := isGS_neg_line hΦ
    have e : dk k (-Φ) x = -dk k Φ x := by
      simp only [dk]; rw [fderiv_neg]; rfl
    exact no_pos_dk hN hx hinj (by simp [h0]) (by rw [e]; linarith)
  · exact no_pos_dk hΦ hx hinj h0 hpos

end DFT.Continuum.Line
