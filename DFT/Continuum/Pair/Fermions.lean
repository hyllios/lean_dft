/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Pair.Sign


/-!
# Two interacting fermions: the nodal set is the diagonal

For two fermions in the box `[0, 1]` with a continuous symmetric interaction, the antisymmetric
ground state `Φ` vanishes on the diagonal `x₁ = x₂` and nowhere else in the open square. So it
vanishes only on a null set, and Hohenberg–Kohn holds with no unique-continuation assumption.

The proof reuses the Perron–Frobenius argument for bosons on the half-square `{x₁ < x₂}`. The
competitor `|Φ|` of the boson proof becomes `sign(x₂ - x₁) |Φ|`, which is antisymmetric. It is not
`C²` across the diagonal, so we use `θ((x₂ - x₁)/η) h_ε(Φ)` instead, where `θ` is a smooth odd step.
On the strip `|x₂ - x₁| ≤ η` the extra kinetic energy is bounded independently of `η`, because
`|Φ| ≤ M |x₂ - x₁|` there (`Φ` vanishes on the diagonal). The strip has area at most `2η`, so the
error is `O(η)`, and `η = ε` works.

* `θs`: a smooth odd step, `-1` below `-1` and `1` above `1`.
* `abs_le_diag`: `|Φ(x₁, x₂)| ≤ M |x₂ - x₁|` for antisymmetric `Φ`.
* `vol_strip`: the strip `|x₂ - x₁| ≤ η` over `[0, 1]` has area at most `2η`.
* `grad_zero_at_zero_f`: a fermionic ground state has zero gradient at its zeros off the diagonal.
* `gs_pos_half`: on the half-square `{x₁ < x₂}`, a fermionic ground state is either positive or
  negative everywhere.
* `ucp_fermions`: the ground state vanishes only on the diagonal, a null set.
* `hk_interacting_fermions`: **Hohenberg–Kohn for two interacting fermions in a box**.
-/

namespace DFT.Continuum.Pair

open MeasureTheory Set Filter Topology Box Metric

/-! ### A smooth odd step -/

/-- A smooth odd step: `θs t = 1` for `t ≥ 1` and `θs t = -1` for `t ≤ -1`. -/
noncomputable def θs (t : ℝ) : ℝ := Real.smoothTransition t - Real.smoothTransition (-t)

lemma contDiff_θs : ContDiff ℝ 2 θs :=
  (Real.smoothTransition.contDiff (n := 2)).sub
    ((Real.smoothTransition.contDiff (n := 2)).comp contDiff_neg)

lemma θs_neg (t : ℝ) : θs (-t) = -θs t := by simp only [θs, neg_neg]; ring

lemma θs_of_one_le {t : ℝ} (ht : 1 ≤ t) : θs t = 1 := by
  simp only [θs, Real.smoothTransition.one_of_one_le ht,
    Real.smoothTransition.zero_of_nonpos (show -t ≤ 0 by linarith), sub_zero]

lemma θs_of_le_neg_one {t : ℝ} (ht : t ≤ -1) : θs t = -1 := by
  have := θs_of_one_le (show 1 ≤ -t by linarith)
  rw [θs_neg] at this; linarith

lemma abs_θs_le (t : ℝ) : |θs t| ≤ 1 := by
  rcases le_total 0 t with ht | ht
  · simp only [θs, Real.smoothTransition.zero_of_nonpos (show -t ≤ 0 by linarith), sub_zero]
    rw [abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact Real.smoothTransition.le_one t
  · simp only [θs, Real.smoothTransition.zero_of_nonpos ht, zero_sub, abs_neg]
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _

lemma deriv_θs_of_one_lt {t : ℝ} (ht : 1 < |t|) : deriv θs t = 0 := by
  rcases lt_abs.mp ht with h | h
  · have : θs =ᶠ[𝓝 t] fun _ => 1 :=
      (lt_mem_nhds h).mono fun s hs => θs_of_one_le hs.le
    rw [this.deriv_eq, deriv_const]
  · have : θs =ᶠ[𝓝 t] fun _ => -1 :=
      (gt_mem_nhds (show t < -1 by linarith)).mono fun s hs => θs_of_le_neg_one hs.le
    rw [this.deriv_eq, deriv_const]

lemma continuous_deriv_θs : Continuous (deriv θs) :=
  contDiff_θs.continuous_deriv (by norm_num)

lemma hasDerivAt_θs (t : ℝ) : HasDerivAt θs (deriv θs t) t :=
  ((contDiff_θs.differentiable (by norm_num)) t).hasDerivAt

/-- The derivative of the step is bounded. -/
lemma exists_deriv_θs_bound : ∃ C, 0 ≤ C ∧ ∀ t, |deriv θs t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_deriv_θs.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have : 1 < |t| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    rw [deriv_θs_of_one_lt this, abs_zero]; exact le_max_right _ _

/-! ### The smoothed sign of `x₂ - x₁` -/

/-- `Sg η q = θs ((q₂ - q₁) / η)`: equal to `sign(q₂ - q₁)` off the strip `|q₂ - q₁| ≤ η`. -/
noncomputable def Sg (η : ℝ) (q : ℝ × ℝ) : ℝ := θs ((q.2 - q.1) / η)

lemma contDiff_Sg (η : ℝ) : ContDiff ℝ 2 (Sg η) :=
  contDiff_θs.comp ((contDiff_snd.sub contDiff_fst).div_const η)

lemma Sg_swap (η : ℝ) (q : ℝ × ℝ) : Sg η q.swap = -Sg η q := by
  simp only [Sg, Prod.fst_swap, Prod.snd_swap]
  rw [show (q.1 - q.2) / η = -((q.2 - q.1) / η) by ring, θs_neg]

lemma abs_Sg_le (η : ℝ) (q : ℝ × ℝ) : |Sg η q| ≤ 1 := abs_θs_le _

lemma Sg_of_lt {η : ℝ} (hη : 0 < η) {q : ℝ × ℝ} (h : η < q.2 - q.1) : Sg η q = 1 :=
  θs_of_one_le (by rw [le_div_iff₀ hη]; linarith)

lemma Sg_of_gt {η : ℝ} (hη : 0 < η) {q : ℝ × ℝ} (h : q.2 - q.1 < -η) : Sg η q = -1 :=
  θs_of_le_neg_one (by rw [div_le_iff₀ hη]; linarith)

lemma Sg_sq {η : ℝ} (hη : 0 < η) {q : ℝ × ℝ} (h : η < |q.2 - q.1|) : Sg η q ^ 2 = 1 := by
  rcases lt_abs.mp h with h | h
  · rw [Sg_of_lt hη h]; norm_num
  · rw [Sg_of_gt hη (by linarith)]; norm_num

lemma d1_Sg (η : ℝ) (q : ℝ × ℝ) :
    d1 (Sg η) q = deriv θs ((q.2 - q.1) / η) * (-1 / η) := by
  refine d1_eq_of_hasDerivAt ((contDiff_Sg η).differentiable (by norm_num)) ?_
  have hin : HasDerivAt (fun t : ℝ => (q.2 - t) / η) (-1 / η) q.1 := by
    have := ((hasDerivAt_id q.1).const_sub q.2).div_const η
    simpa using this
  exact (hasDerivAt_θs _).comp q.1 hin

lemma d2_Sg (η : ℝ) (q : ℝ × ℝ) :
    d2 (Sg η) q = deriv θs ((q.2 - q.1) / η) * (1 / η) := by
  refine d2_eq_of_hasDerivAt ((contDiff_Sg η).differentiable (by norm_num)) ?_
  have hin : HasDerivAt (fun t : ℝ => (t - q.1) / η) (1 / η) q.2 := by
    have := ((hasDerivAt_id q.2).sub_const q.1).div_const η
    simpa using this
  exact (hasDerivAt_θs _).comp q.2 hin

lemma d1_Sg_far {η : ℝ} (hη : 0 < η) {q : ℝ × ℝ} (h : η < |q.2 - q.1|) : d1 (Sg η) q = 0 := by
  rw [d1_Sg, deriv_θs_of_one_lt, zero_mul]
  rw [abs_div, abs_of_pos hη, lt_div_iff₀ hη]; linarith

lemma d2_Sg_far {η : ℝ} (hη : 0 < η) {q : ℝ × ℝ} (h : η < |q.2 - q.1|) : d2 (Sg η) q = 0 := by
  rw [d2_Sg, deriv_θs_of_one_lt, zero_mul]
  rw [abs_div, abs_of_pos hη, lt_div_iff₀ hη]; linarith

lemma abs_d1_Sg_le {η C : ℝ} (hη : 0 < η) (hC : ∀ t, |deriv θs t| ≤ C) (q : ℝ × ℝ) :
    |d1 (Sg η) q| ≤ C / η := by
  rw [d1_Sg, abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hη]
  have := hC ((q.2 - q.1) / η)
  rw [mul_one_div]; exact div_le_div_of_nonneg_right this hη.le

lemma abs_d2_Sg_le {η C : ℝ} (hη : 0 < η) (hC : ∀ t, |deriv θs t| ≤ C) (q : ℝ × ℝ) :
    |d2 (Sg η) q| ≤ C / η := by
  rw [d2_Sg, abs_mul, abs_div, abs_one, abs_of_pos hη]
  have := hC ((q.2 - q.1) / η)
  rw [mul_one_div]; exact div_le_div_of_nonneg_right this hη.le

/-! ### Antisymmetric functions near the diagonal, and the area of the strip -/

/-- An antisymmetric `C¹` function is bounded by `M |x₂ - x₁|` on the closed square, where `M`
bounds `∂₁Φ` there. -/
lemma abs_le_diag {Φ : ℝ × ℝ → ℝ} (hD : Φ ∈ Dom2 (-1)) {M : ℝ}
    (hM : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, |d1 Φ q| ≤ M) {q : ℝ × ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) : |Φ q| ≤ M * |q.2 - q.1| := by
  have hdiag : Φ (q.2, q.2) = 0 := by
    have := hD.2.1 (q.2, q.2); simp only [Prod.swap_prod_mk] at this; linarith
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => Φ (x, q.2)) (f' := fun x => d1 Φ (x, q.2)) (C := M)
    (fun x _ => (hasDerivAt_slice1 hD x q.2).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hM (x, q.2) ⟨hx, hq.2⟩) hq.2 hq.1
  simp only [Real.norm_eq_abs, hdiag, sub_zero] at h
  rw [abs_sub_comm] at h
  exact h

/-- The strip `{|x₂ - x₁| ≤ η}` over `x₁ ∈ [0, 1]` has area at most `2η`. -/
lemma vol_strip {η : ℝ} (hη : 0 ≤ η) :
    volume {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ |q.2 - q.1| ≤ η} ≤ ENNReal.ofReal (2 * η) := by
  have hm : MeasurableSet {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ |q.2 - q.1| ≤ η} :=
    (measurable_fst measurableSet_Icc).inter
      (measurableSet_le (continuous_snd.sub continuous_fst).abs.measurable measurable_const)
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  calc ∫⁻ x, volume (Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ |q.2 - q.1| ≤ η})
      ≤ ∫⁻ x, (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (2 * η)) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Icc (0 : ℝ) 1
        · rw [indicator_of_mem hx]
          have : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ |q.2 - q.1| ≤ η} =
              Icc (x - η) (x + η) := by
            ext y; simp only [mem_preimage, mem_setOf_eq, mem_Icc, abs_le]
            constructor
            · rintro ⟨-, h1, h2⟩; constructor <;> linarith
            · rintro ⟨h1, h2⟩; exact ⟨hx, by linarith, by linarith⟩
          rw [this, Real.volume_Icc]; ring_nf; exact le_rfl
        · rw [indicator_of_notMem hx]
          have : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ |q.2 - q.1| ≤ η} = ∅ := by
            ext y; simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
            exact fun h => hx h.1
          rw [this, measure_empty]
    _ = ENNReal.ofReal (2 * η) := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero,
          ENNReal.ofReal_one, mul_one]

/-- The strip has `μ2`-measure at most `2η`. -/
lemma mu2_strip {η : ℝ} (hη : 0 ≤ η) :
    μ2.real {q : ℝ × ℝ | |q.2 - q.1| ≤ η} ≤ 2 * η := by
  have hm : MeasurableSet {q : ℝ × ℝ | |q.2 - q.1| ≤ η} :=
    measurableSet_le (continuous_snd.sub continuous_fst).abs.measurable measurable_const
  have hle : μ2 {q : ℝ × ℝ | |q.2 - q.1| ≤ η} ≤ ENNReal.ofReal (2 * η) := by
    rw [Measure.restrict_apply hm]
    refine (measure_mono fun q hq => ?_).trans (vol_strip hη)
    exact ⟨⟨hq.2.1.1.le, hq.2.1.2.le⟩, hq.1⟩
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

lemma Sg_mul_Sg {η η' : ℝ} (hη : 0 < η) (hη' : 0 < η') {q : ℝ × ℝ} (h : η < |q.2 - q.1|)
    (h' : η' < |q.2 - q.1|) : Sg η q * Sg η' q = 1 := by
  rcases le_or_gt 0 (q.2 - q.1) with ht | ht
  · rw [abs_of_nonneg ht] at h h'
    rw [Sg_of_lt hη h, Sg_of_lt hη' h', one_mul]
  · rw [abs_of_neg ht] at h h'
    rw [Sg_of_gt hη (by linarith), Sg_of_gt hη' (by linarith)]; norm_num

/-! ### Admissible antisymmetric functions -/

lemma hε_neg (ε s : ℝ) : hε ε (-s) = hε ε s := by simp [hε]

lemma kε_neg (ε s : ℝ) : kε ε (-s) = -kε ε s := by simp [kε, neg_div]

lemma abs_hε_le {ε : ℝ} (hε0 : 0 < ε) (s : ℝ) : |hε ε s| ≤ |s| := by
  have h1 := eps_le_sqrt_eps hε0 s
  have h2 := sqrt_eps_le hε0 s
  rw [abs_of_nonneg (by simp only [hε]; linarith)]
  simp only [hε]; linarith

lemma hε_comp_mem {Φ : ℝ × ℝ → ℝ} (hD : Φ ∈ Dom2 (-1)) {ε : ℝ} (hε0 : 0 < ε) :
    (fun q => hε ε (Φ q)) ∈ Dom2 1 :=
  ⟨(contDiff_hε hε0).comp hD.1, fun p => by simp [hD.2.1 p, hε_neg],
    fun y => by simp [hD.2.2.1 y, hε_zero hε0], fun y => by simp [hD.2.2.2 y, hε_zero hε0]⟩

lemma Sg_mul_mem {f : ℝ × ℝ → ℝ} (hf : f ∈ Dom2 1) (η : ℝ) :
    (fun q => Sg η q * f q) ∈ Dom2 (-1) :=
  ⟨(contDiff_Sg η).mul hf.1, fun p => by simp [hf.2.1 p, Sg_swap],
    fun y => by simp [hf.2.2.1 y], fun y => by simp [hf.2.2.2 y]⟩

lemma kε_mul_mem {Φ φ : ℝ × ℝ → ℝ} (hD : Φ ∈ Dom2 (-1)) (hφ : φ ∈ Dom2 1) {ε : ℝ}
    (hε0 : 0 < ε) : (fun q => kε ε (Φ q) * φ q) ∈ Dom2 (-1) :=
  ⟨((contDiff_kε hε0).comp hD.1).mul hφ.1, fun p => by simp [hD.2.1 p, hφ.2.1 p, kε_neg],
    fun y => by simp [hφ.2.2.1 y], fun y => by simp [hφ.2.2.2 y]⟩

lemma fderiv_Sg_mul {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (η : ℝ) (q m : ℝ × ℝ) :
    fderiv ℝ (fun q => Sg η q * f q) q m =
      fderiv ℝ (Sg η) q m * f q + Sg η q * fderiv ℝ f q m :=
  fderiv_mul_apply ((contDiff_Sg η).differentiable (by norm_num)) hf q m

/-! ### Arithmetic steps (kept out of the main proof's large context) -/

lemma ar_low {s0 k d e p : ℝ} (hs : 0 < s0) (hk : 0 < k) (hd : s0 / 2 < d) (hp : 1 ≤ p) :
    s0 / 2 * (k * d) ≤ k * (d ^ 2 + e ^ 2) * p := by
  have hd0 : 0 < d := by linarith
  have e1 : s0 / 2 * (k * d) ≤ k * d * d := by nlinarith [mul_pos hk hd0]
  have e2 : k * d * d ≤ k * (d ^ 2 + e ^ 2) := by nlinarith [sq_nonneg e]
  have e3 : k * (d ^ 2 + e ^ 2) ≤ k * (d ^ 2 + e ^ 2) * p := by
    have : 0 ≤ k * (d ^ 2 + e ^ 2) := by positivity
    nlinarith
  linarith

lemma ar_X {V x p ε : ℝ} (h : |x| ≤ ε) (hp : 0 ≤ p) : |V| * |x| * p ≤ ε * (|V| * p) := by
  have := mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg V) hp)
  nlinarith

lemma ar_far {k a b c aV h P ε : ℝ} (hk : k ^ 2 ≤ 1)
    (hVle : c * (h ^ 2 - P ^ 2) ≤ aV * (2 * ε * |P|)) :
    (k * a) ^ 2 + (k * b) ^ 2 + c * h ^ 2 - (a * a + b * b + c * (P * P)) ≤
      2 * ε * (aV * |P|) := by
  have hkk : (k ^ 2 - 1) * (a ^ 2 + b ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  nlinarith

lemma ar_near {x1 x2 a b c H P A m R : ℝ} (sq1 : x1 ^ 2 ≤ A ^ 2) (sq2 : x2 ^ 2 ≤ A ^ 2)
    (hV1 : c * (H * H) ≤ m) (hV2 : -(c * (P * P)) ≤ m) (hR : 0 ≤ R) :
    x1 * x1 + x2 * x2 + c * (H * H) - (a * a + b * b + c * (P * P)) ≤ R + (2 * A ^ 2 + 2 * m) := by
  nlinarith [mul_self_nonneg a, mul_self_nonneg b]

/-! ### Critical zeros off the diagonal -/

variable {w : ℝ × ℝ → ℝ} {hw : Continuous w} {v : Pot}

set_option maxHeartbeats 1000000 in
/-- A fermionic ground state cannot vanish at a point off the diagonal where `∂₁Φ > 0`. -/
lemma no_pos_d1_f {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 (-1) w hw) v Φ) {a b : ℝ}
    (hab : (a, b) ∈ Sq) (hne : a ≠ b) (h0 : Φ (a, b) = 0) (hpos : 0 < d1 Φ (a, b)) : False := by
  have hD : Φ ∈ Dom2 (-1) := hΦ.1
  set s0 := d1 Φ (a, b) with hs0
  set g0 := |b - a| with hg0
  have hg0p : 0 < g0 := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  set U : Set (ℝ × ℝ) := {q | g0 / 2 < |q.2 - q.1|} with hUd
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_snd.sub continuous_fst).abs
  have haU : (a, b) ∈ U := by show g0 / 2 < |b - a|; linarith
  obtain ⟨r, r', δ, hr, hr', hrr, hδ, hin, hsign⟩ := box_data_on hD hUo ⟨hab, haU⟩ h0 hpos
  -- a bump at `(a, b)`, symmetrised; it vanishes near the diagonal
  let β : ContDiffBump ((a, b) : ℝ × ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  have hβU : ∀ q, β q ≠ 0 → q ∈ Sq ∩ U := by
    intro q hq
    have : q ∈ tsupport β := subset_tsupport _ hq
    rw [β.tsupport_eq] at this
    exact (hin q (mem_closedBall.mp this)).1
  have hβout : ∀ q, q ∉ Sq → β q = 0 := fun q hq => by
    by_contra h; exact hq (hβU q h).1
  have hβW : ∀ q : ℝ × ℝ, |q.2 - q.1| ≤ g0 / 2 → β q = 0 := fun q hq => by
    by_contra h
    have : g0 / 2 < |q.2 - q.1| := (hβU q h).2
    linarith
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
  have hφsW : ∀ q : ℝ × ℝ, |q.2 - q.1| < g0 / 2 → φs q = 0 ∧ d1 φs q = 0 ∧ d2 φs q = 0 := by
    intro q hq
    have hW : IsOpen {p : ℝ × ℝ | |p.2 - p.1| < g0 / 2} :=
      isOpen_lt (continuous_snd.sub continuous_fst).abs continuous_const
    have hz : ∀ p ∈ {p : ℝ × ℝ | |p.2 - p.1| < g0 / 2}, φs p = 0 := by
      intro p hp
      have hp' : |p.2 - p.1| ≤ g0 / 2 := le_of_lt hp
      have hps : |p.swap.2 - p.swap.1| ≤ g0 / 2 := by
        simp only [Prod.fst_swap, Prod.snd_swap]; rw [abs_sub_comm]; exact hp'
      simp only [φs, hβW p hp', hβW p.swap hps, add_zero]
    have hev : φs =ᶠ[𝓝 q] fun _ => 0 := Filter.eventually_of_mem (hW.mem_nhds hq) hz
    have hfd : fderiv ℝ φs q = 0 := by rw [hev.fderiv_eq]; exact fderiv_const_apply _
    refine ⟨hz q hq, ?_, ?_⟩ <;> simp [d1, d2, hfd]
  set Bx := Icc (a - r) (a + r) ×ˢ Icc (b - r') (b + r') with hBx
  have hBxd : ∀ q ∈ Bx, dist q (a, b) ≤ r := fun q hq =>
    dist_le_of_abs (abs_le.mpr ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩)
      (abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩)
  have hφs1 : ∀ q ∈ Bx, 1 ≤ φs q := fun q hq => by
    have : β q = 1 := β.one_of_mem_closedBall (mem_closedBall.mpr (hBxd q hq))
    simp only [φs, this]; linarith [β.nonneg' q.swap]
  have hBxS : Bx ⊆ Sq := fun q hq => (hin q (by linarith [hBxd q hq])).1.1
  have hBxd1 : ∀ q ∈ Bx, s0 / 2 < d1 Φ q := fun q hq => (hin q (by linarith [hBxd q hq])).2
  -- constants independent of `ε`
  set E := Q (setting2 (-1) w hw) v Φ / ip (μ := μ2) Φ Φ with hE
  set V : ℝ × ℝ → ℝ := fun q => w q + L2 v q - E with hV
  have hVc : Continuous V := (hw.add (continuous_L2 v)).sub continuous_const
  have hφc : Continuous φs := hφs.1.continuous
  have hΦc : Continuous Φ := hD.1.continuous
  have hKq : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M1, hM1⟩ := hKq.exists_bound_of_continuousOn (cont_d1 hD).continuousOn
  obtain ⟨M2, hM2⟩ := hKq.exists_bound_of_continuousOn (cont_d2 hD).continuousOn
  obtain ⟨Pm, hPm⟩ := hKq.exists_bound_of_continuousOn hΦc.continuousOn
  obtain ⟨Vm, hVm⟩ := hKq.exists_bound_of_continuousOn hVc.continuousOn
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_deriv_θs_bound
  set M := max (max M1 M2) 0 with hMd
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMq1 : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, |d1 Φ q| ≤ M := fun q hq => by
    have := hM1 q hq; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hMq2 : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, |d2 Φ q| ≤ M := fun q hq => by
    have := hM2 q hq; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hSqK : ∀ q ∈ Sq, q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun q hq =>
    ⟨⟨hq.1.1.le, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  set A := Cθ * M + M with hAd
  have hA0 : 0 ≤ A := by positivity
  set Kθ := 2 * A ^ 2 + 2 * (max Vm 0) * Pm ^ 2 with hKθd
  have hKθ0 : 0 ≤ Kθ := by positivity
  set K1 := ∫ q, |V q| * |Φ q| ∂μ2 with hK1d
  have hK1 : 0 ≤ K1 := integral_nonneg fun q => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  set K2 := ∫ q, |V q| * φs q ∂μ2 with hK2d
  have hK2 : 0 ≤ K2 := integral_nonneg fun q => mul_nonneg (abs_nonneg _) (hφs0 q)
  -- the antisymmetric test function `sign(x₂ - x₁) φs`, independent of `ε`
  set η0 := g0 / 4 with hη0d
  have hη0 : 0 < η0 := by positivity
  set φ : ℝ × ℝ → ℝ := fun q => Sg η0 q * φs q with hφd
  have hφm : φ ∈ Dom2 (-1) := Sg_mul_mem hφs η0
  set C := Rf (-1) w hw v E φ φ with hCd
  have hC : 0 ≤ C := Rf_nonneg hΦ hφm
  set L := s0 * r' with hLd
  have hL : 0 < L := mul_pos hpos hr'
  set K1' := K1 + Kθ with hK1'd
  have hK1' : 0 ≤ K1' := by positivity
  set ε := min δ (min (L / (4 * (K2 + 1))) (min (L ^ 2 / (16 * (K1' * C + 1))) η0)) with hεd
  have hε0 : 0 < ε := lt_min hδ (lt_min (by positivity) (lt_min (by positivity) hη0))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ L / (4 * (K2 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ L ^ 2 / (16 * (K1' * C + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε ≤ η0 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the competitor `θ((x₂ - x₁)/ε) h_ε(Φ)` and the Euler–Lagrange test `k_ε(Φ) φs`
  set H : ℝ × ℝ → ℝ := fun q => Sg ε q * hε ε (Φ q) with hHd
  have hHm : H ∈ Dom2 (-1) := Sg_mul_mem (hε_comp_mem hD hε0) ε
  set g : ℝ × ℝ → ℝ := fun q => kε ε (Φ q) * φs q with hgd
  have hgm : g ∈ Dom2 (-1) := kε_mul_mem hD hφs hε0
  have hhd : Differentiable ℝ (fun q => hε ε (Φ q)) :=
    ((contDiff_hε hε0).comp hD.1).differentiable (by norm_num)
  have dhε : ∀ q m, fderiv ℝ (fun q => hε ε (Φ q)) q m = kε ε (Φ q) * fderiv ℝ Φ q m :=
    fun q m => fderiv_comp_apply (hasDerivAt_hε hε0) (diff2 hD) q m
  have dH1 : ∀ q, d1 H q = d1 (Sg ε) q * hε ε (Φ q) + Sg ε q * (kε ε (Φ q) * d1 Φ q) :=
    fun q => by
      simp only [d1, H]; rw [fderiv_Sg_mul hhd, dhε]
  have dH2 : ∀ q, d2 H q = d2 (Sg ε) q * hε ε (Φ q) + Sg ε q * (kε ε (Φ q) * d2 Φ q) :=
    fun q => by
      simp only [d2, H]; rw [fderiv_Sg_mul hhd, dhε]
  have dφ1 : ∀ q, d1 φ q = d1 (Sg η0) q * φs q + Sg η0 q * d1 φs q := fun q => by
    simp only [d1, φ]; rw [fderiv_Sg_mul (diff2 hφs)]
  have dφ2 : ∀ q, d2 φ q = d2 (Sg η0) q * φs q + Sg η0 q * d2 φs q := fun q => by
    simp only [d2, φ]; rw [fderiv_Sg_mul (diff2 hφs)]
  have dg1 : ∀ q, d1 g q = k2 ε (Φ q) * d1 Φ q * φs q + kε ε (Φ q) * d1 φs q :=
    fun q => by
      simp only [d1, g]
      rw [fderiv_mul_apply (f := fun q => kε ε (Φ q)) (g := φs)
        (((contDiff_kε hε0).comp hD.1).differentiable (by norm_num)) (diff2 hφs),
        fderiv_comp_apply (hasDerivAt_kε hε0) (diff2 hD)]
  have dg2 : ∀ q, d2 g q = k2 ε (Φ q) * d2 Φ q * φs q + kε ε (Φ q) * d2 φs q :=
    fun q => by
      simp only [d2, g]
      rw [fderiv_mul_apply (f := fun q => kε ε (Φ q)) (g := φs)
        (((contDiff_kε hε0).comp hD.1).differentiable (by norm_num)) (diff2 hφs),
        fderiv_comp_apply (hasDerivAt_kε hε0) (diff2 hD)]
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
      exact ar_low hpos (k2_pos hε0 (Φ q)) (hBxd1 q hq) (hφs1 q hq)
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
  set B := Rf (-1) w hw v E H φ with hBd
  have hU : ∫ q, G q ∂μ2 = ∫ q, X q ∂μ2 - B := by
    have hEL := Rf_EL hΦ hgm
    rw [Rf_eq E hD hgm] at hEL
    rw [hBd, Rf_eq E hHm hφm]
    have iA : Integrable (fun q => d1 Φ q * d1 g q + d2 Φ q * d2 g q +
        (w q + L2 v q - E) * (Φ q * g q)) μ2 :=
      integrable2 ((((cont_d1 hD).mul (cont_d1 hgm)).add ((cont_d2 hD).mul
        (cont_d2 hgm))).add (hVc.mul (hΦc.mul hgm.1.continuous)))
    have iXG : Integrable (fun q => X q - G q) μ2 := integrable2 (hXc.sub hGc)
    have key : ∫ q, (d1 H q * d1 φ q + d2 H q * d2 φ q +
        (w q + L2 v q - E) * (H q * φ q)) ∂μ2 =
        ∫ q, (d1 Φ q * d1 g q + d2 Φ q * d2 g q + (w q + L2 v q - E) * (Φ q * g q)) ∂μ2 +
          ∫ q, (X q - G q) ∂μ2 := by
      rw [← integral_add iA iXG]
      congr 1; funext q
      rw [dH1 q, dH2 q, dφ1 q, dφ2 q, dg1 q, dg2 q]
      simp only [X, G, H, φ, g]
      by_cases hq : |q.2 - q.1| < g0 / 2
      · obtain ⟨e0, e1, e2⟩ := hφsW q hq
        rw [e0, e1, e2]; ring
      · have hfar : g0 / 2 ≤ |q.2 - q.1| := le_of_not_gt hq
        have hfε : ε < |q.2 - q.1| := by linarith
        have hf0 : η0 < |q.2 - q.1| := by linarith
        have hSS := Sg_mul_Sg hε0 hη0 hfε hf0
        rw [d1_Sg_far hε0 hfε, d2_Sg_far hε0 hfε, d1_Sg_far hη0 hf0, d2_Sg_far hη0 hf0]
        linear_combination (kε ε (Φ q) * (d1 Φ q * d1 φs q + d2 Φ q * d2 φs q) +
          (w q + L2 v q - E) * hε ε (Φ q) * φs q) * hSS
    rw [key, hEL, zero_add, integral_sub (integrable2 hXc) (integrable2 hGc)]
    ring
  have hB1 : |∫ q, X q ∂μ2| ≤ ε * K2 := by
    calc |∫ q, X q ∂μ2| ≤ ∫ q, |X q| ∂μ2 := abs_integral_le_integral_abs
      _ ≤ ∫ q, ε * (|V q| * φs q) ∂μ2 := by
          refine integral_mono (integrable2 hXc.abs)
            (integrable2 (continuous_const.mul (hVc.abs.mul hφc))) fun q => ?_
          simp only [X, abs_mul, abs_of_nonneg (hφs0 q)]
          exact ar_X (abs_hε_sub hε0 (Φ q)) (hφs0 q)
      _ = ε * K2 := integral_const_mul _ _
  -- the energy of the competitor
  have hB2 : Rf (-1) w hw v E H H ≤ 2 * ε * K1' := by
    have hself := Rf_self hΦ
    rw [Rf_eq E hD hD] at hself
    rw [Rf_eq E hHm hHm]
    have iΦ : Integrable (fun q => d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q +
        (w q + L2 v q - E) * (Φ q * Φ q)) μ2 :=
      integrable2 ((((cont_d1 hD).mul (cont_d1 hD)).add ((cont_d2 hD).mul
        (cont_d2 hD))).add (hVc.mul (hΦc.mul hΦc)))
    have ih : Integrable (fun q => d1 H q * d1 H q + d2 H q * d2 H q +
        (w q + L2 v q - E) * (H q * H q)) μ2 :=
      integrable2 ((((cont_d1 hHm).mul (cont_d1 hHm)).add ((cont_d2 hHm).mul
        (cont_d2 hHm))).add (hVc.mul (hHm.1.continuous.mul hHm.1.continuous)))
    have e : ∫ q, (d1 H q * d1 H q + d2 H q * d2 H q + (w q + L2 v q - E) * (H q * H q)) ∂μ2 =
        ∫ q, (d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q + (w q + L2 v q - E) * (Φ q * Φ q)) ∂μ2 +
          ∫ q, ((d1 H q * d1 H q + d2 H q * d2 H q + (w q + L2 v q - E) * (H q * H q)) -
            (d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q + (w q + L2 v q - E) * (Φ q * Φ q))) ∂μ2 := by
      have ihΦ : Integrable (fun q => (d1 H q * d1 H q + d2 H q * d2 H q +
          (w q + L2 v q - E) * (H q * H q)) - (d1 Φ q * d1 Φ q + d2 Φ q * d2 Φ q +
            (w q + L2 v q - E) * (Φ q * Φ q))) μ2 := ih.sub iΦ
      rw [← integral_add iΦ ihΦ]
      congr 1; funext q; ring
    set St : Set (ℝ × ℝ) := {q | |q.2 - q.1| ≤ ε} with hStd
    have hStm : MeasurableSet St :=
      measurableSet_le (continuous_snd.sub continuous_fst).abs.measurable measurable_const
    have iR : Integrable (fun q => 2 * ε * (|V q| * |Φ q|) + St.indicator (fun _ => Kθ) q) μ2 :=
      (integrable2 (continuous_const.mul (hVc.abs.mul hΦc.abs))).add
        ((integrable2 (continuous_const (y := Kθ))).indicator hStm)
    rw [e, hself, zero_add]
    calc _ ≤ ∫ q, (2 * ε * (|V q| * |Φ q|) + St.indicator (fun _ => Kθ) q) ∂μ2 := by
          refine integral_mono_ae (ih.sub iΦ) iR ?_
          refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2
            (ae_of_all _ fun q hq => ?_)
          have hqK := hSqK q hq
          have hsq := abs_hε_sq_sub hε0 (Φ q)
          have hVle : (w q + L2 v q - E) * (hε ε (Φ q) ^ 2 - Φ q ^ 2) ≤
              |V q| * (2 * ε * |Φ q|) := by
            calc (w q + L2 v q - E) * (hε ε (Φ q) ^ 2 - Φ q ^ 2)
                ≤ |(w q + L2 v q - E) * (hε ε (Φ q) ^ 2 - Φ q ^ 2)| := le_abs_self _
              _ = |V q| * |hε ε (Φ q) ^ 2 - Φ q ^ 2| := by rw [abs_mul]
              _ ≤ |V q| * (2 * ε * |Φ q|) :=
                  mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
          have hR0 : 0 ≤ 2 * ε * (|V q| * |Φ q|) := by positivity
          simp only
          rw [dH1 q, dH2 q]
          by_cases hfar : ε < |q.2 - q.1|
          · rw [indicator_of_notMem (show q ∉ St from fun h => absurd h (not_le.mpr hfar)),
              d1_Sg_far hε0 hfar, d2_Sg_far hε0 hfar]
            have hS2 := Sg_sq hε0 hfar
            simp only [H]
            have eH : ∀ x y : ℝ, (0 * x + Sg ε q * y) * (0 * x + Sg ε q * y) = y ^ 2 := by
              intro x y; linear_combination y ^ 2 * hS2
            have eH2 : Sg ε q * hε ε (Φ q) * (Sg ε q * hε ε (Φ q)) = hε ε (Φ q) ^ 2 := by
              linear_combination hε ε (Φ q) ^ 2 * hS2
            rw [eH, eH, eH2, add_zero]
            exact ar_far (kε_sq_le hε0 (Φ q)) hVle
          · have hnear : |q.2 - q.1| ≤ ε := le_of_not_gt hfar
            rw [indicator_of_mem (show q ∈ St from hnear)]
            have hΦd := abs_le_diag hD hMq1 hqK
            have hd1 := hMq1 q hqK
            have hd2 := hMq2 q hqK
            have hhΦ := abs_hε_le hε0 (Φ q)
            have hS := abs_Sg_le ε q
            have hk := abs_kε_le hε0 (Φ q)
            have hS1 := abs_d1_Sg_le hε0 hCθ q
            have hS2 := abs_d2_Sg_le hε0 hCθ q
            -- `|∂(Sg) h_ε(Φ)| ≤ Cθ M`
            have hprod : ∀ z : ℝ, |z| ≤ Cθ / ε → |z * hε ε (Φ q)| ≤ Cθ * M := by
              intro z hz
              rw [abs_mul]
              calc |z| * |hε ε (Φ q)| ≤ (Cθ / ε) * (M * ε) := by
                    apply mul_le_mul hz _ (abs_nonneg _) (by positivity)
                    exact hhΦ.trans (hΦd.trans (mul_le_mul_of_nonneg_left hnear hM0))
                _ = Cθ * M := by field_simp
            have hsec : ∀ z d : ℝ, |d| ≤ M → |Sg ε q * (kε ε (Φ q) * d)| ≤ M := by
              intro z d hd
              rw [abs_mul, abs_mul]
              calc |Sg ε q| * (|kε ε (Φ q)| * |d|) ≤ 1 * (1 * M) := by
                    apply mul_le_mul hS (mul_le_mul hk hd (abs_nonneg _) zero_le_one)
                      (by positivity) zero_le_one
                _ = M := by ring
            have b1 : |d1 (Sg ε) q * hε ε (Φ q) + Sg ε q * (kε ε (Φ q) * d1 Φ q)| ≤ A :=
              (abs_add_le _ _).trans (add_le_add (hprod _ hS1) (hsec 0 _ hd1))
            have b2 : |d2 (Sg ε) q * hε ε (Φ q) + Sg ε q * (kε ε (Φ q) * d2 Φ q)| ≤ A :=
              (abs_add_le _ _).trans (add_le_add (hprod _ hS2) (hsec 0 _ hd2))
            have sq1 := (sq_le_sq₀ (abs_nonneg _) hA0).mpr b1
            have sq2 := (sq_le_sq₀ (abs_nonneg _) hA0).mpr b2
            rw [sq_abs] at sq1 sq2
            have hVq : |V q| ≤ max Vm 0 := by
              have := hVm q hqK; rw [Real.norm_eq_abs] at this
              exact this.trans (le_max_left _ _)
            have hPq : |Φ q| ≤ Pm := by
              have := hPm q hqK; rw [Real.norm_eq_abs] at this; exact this
            have hHq : |H q| ≤ |Φ q| := by
              simp only [H, abs_mul]
              calc |Sg ε q| * |hε ε (Φ q)| ≤ 1 * |Φ q| :=
                    mul_le_mul hS hhΦ (abs_nonneg _) zero_le_one
                _ = |Φ q| := one_mul _
            have hH2 : H q * H q ≤ Pm ^ 2 := by
              rw [← abs_mul_abs_self, ← sq]
              exact pow_le_pow_left₀ (abs_nonneg _) (hHq.trans hPq) 2
            have hΦ2 : Φ q * Φ q ≤ Pm ^ 2 := by
              rw [← abs_mul_abs_self, ← sq]
              exact pow_le_pow_left₀ (abs_nonneg _) hPq 2
            have hV1 : (w q + L2 v q - E) * (H q * H q) ≤ max Vm 0 * Pm ^ 2 := by
              calc _ ≤ |w q + L2 v q - E| * (H q * H q) :=
                    mul_le_mul_of_nonneg_right (le_abs_self _) (mul_self_nonneg _)
                _ ≤ max Vm 0 * Pm ^ 2 :=
                    mul_le_mul hVq hH2 (mul_self_nonneg _) (le_max_right _ _)
            have hV2 : -((w q + L2 v q - E) * (Φ q * Φ q)) ≤ max Vm 0 * Pm ^ 2 := by
              calc _ ≤ |w q + L2 v q - E| * (Φ q * Φ q) := by
                    rw [← neg_mul]
                    exact mul_le_mul_of_nonneg_right (neg_le_abs _) (mul_self_nonneg _)
                _ ≤ max Vm 0 * Pm ^ 2 :=
                    mul_le_mul hVq hΦ2 (mul_self_nonneg _) (le_max_right _ _)
            exact (ar_near sq1 sq2 hV1 hV2 hR0).trans_eq (by rw [hKθd]; ring)
      _ = 2 * ε * K1 + μ2.real St * Kθ := by
          rw [integral_add (f := fun q => 2 * ε * (|V q| * |Φ q|)) (g := St.indicator fun _ => Kθ)
            (integrable2 (continuous_const.mul (hVc.abs.mul hΦc.abs)))
            ((integrable2 (continuous_const (y := Kθ))).indicator hStm),
            integral_const_mul, integral_indicator_const _ hStm, smul_eq_mul]
      _ ≤ 2 * ε * K1 + 2 * ε * Kθ := by
          have := mul_le_mul_of_nonneg_right (mu2_strip hε0.le) hKθ0
          linarith
      _ = 2 * ε * K1' := by simp only [K1']; ring
  have hB3 : B ^ 2 ≤ Rf (-1) w hw v E H H * C := by
    refine discr_le hC fun t => ?_
    have h := Rf_nonneg hΦ ((Dom2 (-1)).add_mem hHm ((Dom2 (-1)).smul_mem t hφm))
    rw [Rf_expand E hHm hφm t] at h
    linarith
  have hA : L ≤ ε * K2 + |B| := by
    have h1 := hlow
    rw [hU] at h1
    have h2 := (abs_le.mp hB1).2
    have h3 := le_abs_self (∫ q, X q ∂μ2)
    linarith [neg_abs_le B]
  exact final_arith hL hK1' hK2 hC hε0 hε1 hε2 hA hB2 hB3

/-- **Critical zeros off the diagonal.** A ground state of two interacting fermions has zero
gradient at each of its zeros in the open square off the diagonal. -/
theorem grad_zero_at_zero_f {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 (-1) w hw) v Φ) :
    ∀ p ∈ Sq, p.1 ≠ p.2 → Φ p = 0 → d1 Φ p = 0 ∧ d2 Φ p = 0 := by
  have hD : Φ ∈ Dom2 (-1) := hΦ.1
  have key : ∀ a b, (a, b) ∈ Sq → a ≠ b → Φ (a, b) = 0 → d1 Φ (a, b) = 0 := by
    intro a b hab hne h0
    by_contra hd
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · have hN := isGS_neg_pair hΦ
      have e : d1 (-Φ) (a, b) = -d1 Φ (a, b) := by
        simp only [d1]; rw [fderiv_neg]; rfl
      exact no_pos_d1_f hN hab hne (by simp [h0]) (by rw [e]; linarith)
    · exact no_pos_d1_f hΦ hab hne h0 hpos
  rintro ⟨a, b⟩ hp hne h0
  refine ⟨key a b hp hne h0, ?_⟩
  have hsw : Φ (b, a) = 0 := by
    have := hD.2.1 (a, b); simp only [Prod.swap_prod_mk] at this; rw [this, h0]; ring
  have := key b a ⟨hp.2, hp.1⟩ (Ne.symm hne) hsw
  rw [d1_swap_of hD b a] at this
  linarith

/-! ### The sign on the half-square, and unique continuation -/

/-- The open half-square `{0 < x₁ < x₂ < 1}`. -/
abbrev Half : Set (ℝ × ℝ) := Sq ∩ {q | q.1 < q.2}

lemma isOpen_half : IsOpen Half :=
  (isOpen_Ioo.prod isOpen_Ioo).inter (isOpen_lt continuous_fst continuous_snd)

lemma convex_half : Convex ℝ Half := by
  refine ((convex_Ioo 0 1).prod (convex_Ioo 0 1)).inter ?_
  intro x hx y hy s t hs ht hst
  simp only [mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hx hy ⊢
  rcases hs.lt_or_eq with hs' | hs'
  · nlinarith [mul_lt_mul_of_pos_left hx hs']
  · subst hs'; simp only [zero_add] at hst; subst hst; simpa using hy

/-- On the half-square a fermionic ground state is positive everywhere or nonpositive
everywhere. -/
lemma gs_pos_or_nonpos_half (hws : ∀ p, w p.swap = w p) {Φ : ℝ × ℝ → ℝ}
    (hΦ : IsGS (setting2 (-1) w hw) v Φ) :
    (∀ p ∈ Half, 0 < Φ p) ∨ ∀ p ∈ Half, Φ p ≤ 0 := by
  set E := Q (setting2 (-1) w hw) v Φ / ip (μ := μ2) Φ Φ
  set V : ℝ × ℝ → ℝ := fun p => w p + L2 v p - E
  have hV : Continuous V := (hw.add (continuous_L2 v)).sub continuous_const
  have heq := strong_eq (by norm_num) hws hΦ
  refine pos_or_nonpos_on isOpen_half convex_half.isPreconnected (c := fun p => max (V p) 0)
    hΦ.1.1 (hV.max continuous_const) (fun p => le_max_right _ _) (fun p hp hpos => ?_)
    (fun p hp h0 => grad_zero_at_zero_f hΦ p hp.1 (ne_of_lt hp.2) h0)
  have e := heq p hp.1
  have h1 : 0 ≤ (max (V p) 0 - V p) * Φ p :=
    mul_nonneg (by linarith [le_max_left (V p) 0]) hpos.le
  simp only [V] at e h1 ⊢
  nlinarith

/-- **A fermionic ground state has no zeros off the diagonal.** -/
theorem gs_ne_zero_f (hws : ∀ p, w p.swap = w p) {Φ : ℝ × ℝ → ℝ}
    (hΦ : IsGS (setting2 (-1) w hw) v Φ) : ∀ p ∈ Sq, p.1 ≠ p.2 → Φ p ≠ 0 := by
  have hD : Φ ∈ Dom2 (-1) := hΦ.1
  have hanti : ∀ p, Φ p.swap = -Φ p := fun p => by rw [hD.2.1 p]; ring
  -- no zeros on the half-square
  have hhalf : ∀ p ∈ Half, Φ p ≠ 0 := by
    intro p0 hp0 h0
    rcases gs_pos_or_nonpos_half hws hΦ with h | h
    · exact (h p0 hp0).ne' h0
    rcases gs_pos_or_nonpos_half hws (isGS_neg_pair hΦ) with h' | h'
    · exact (h' p0 hp0).ne' (by simp [h0])
    -- otherwise `Φ = 0` on the half-square, hence on the square
    have hz : ∀ p ∈ Half, Φ p = 0 := fun p hp =>
      le_antisymm (h p hp) (by have := h' p hp; simp only [Pi.neg_apply] at this; linarith)
    have hzS : ∀ p ∈ Sq, Φ p = 0 := by
      intro p hp
      rcases lt_trichotomy p.1 p.2 with hl | he | hg
      · exact hz p ⟨hp, hl⟩
      · have := hanti p
        have hps : p.swap = p := Prod.ext he.symm he
        rw [hps] at this; linarith
      · have := hz p.swap ⟨⟨hp.2, hp.1⟩, hg⟩
        rw [hanti p] at this; linarith
    have hip : ip (μ := μ2) Φ Φ = 0 := by
      unfold ip
      refine integral_eq_zero_of_ae ?_
      refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2
        (ae_of_all _ fun p hp => ?_)
      simp [hzS p hp]
    exact absurd hΦ.2.1 (by rw [hip]; exact lt_irrefl 0)
  intro p hp hne h0
  rcases lt_or_gt_of_ne hne with hl | hg
  · exact hhalf p ⟨hp, hl⟩ h0
  · exact hhalf p.swap ⟨⟨hp.2, hp.1⟩, hg⟩ (by rw [hanti p, h0, neg_zero])

/-- The diagonal of the plane is a null set. -/
lemma diag_null : volume {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall fun x => ?_
  have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
    ext y; simp [eq_comm]
  simp [this]

/-- **Unique continuation for fermions**: the ground state vanishes only on the diagonal, a null
set. -/
theorem ucp_fermions (hws : ∀ p, w p.swap = w p) {Φ : ℝ × ℝ → ℝ}
    (hΦ : IsGS (setting2 (-1) w hw) v Φ) : ∀ᵐ p ∂μ2, Φ p ≠ 0 := by
  have hd : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ p.2 := by
    rw [ae_iff]; simpa using diag_null
  refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 ?_
  filter_upwards [hd] with p hp hpS
  exact gs_ne_zero_f hws hΦ p hpS hp

/-- **Hohenberg–Kohn for two interacting fermions in a box.** For any continuous symmetric
interaction, if ground states of continuous potentials `v` and `v'` have the same one-body density,
then `v - v'` is constant. No unique-continuation hypothesis is needed. -/
theorem hk_interacting_fermions (hws : ∀ p, w p.swap = w p) {v' : Pot} {Φ Φ' : ℝ × ℝ → ℝ}
    (hΦ : IsGS (setting2 (-1) w hw) v Φ) (hΦ' : IsGS (setting2 (-1) w hw) v' Φ')
    (hρ : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, Φ (x, y) ^ 2 =
      ∫ y in Ioo (0 : ℝ) 1, Φ' (x, y) ^ 2) : ∃ k : ℝ, v - v' = k • one :=
  hk_pair_of_ucp (by norm_num) hΦ hΦ' hρ (ucp_fermions hws hΦ)

end DFT.Continuum.Pair
