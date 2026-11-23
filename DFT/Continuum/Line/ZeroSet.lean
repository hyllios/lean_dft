/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Translate

/-!
# The zero set of a nonnegative ground state is translation invariant

* `translate_lintegral_le`: for `f ∈ L²` with weak derivative `G` (zero boundary values), and
  sets `S`, `T ⊆ (0,1)ᴺ` such that every segment `[x, x + h eₖ]` with `x ∈ S` lies in `T`,
  `∫_S |f(x + h eₖ) - f(x)| ≤ h ∫_T |G|` (from `translate_identity`, Fubini and translation
  invariance; stated with lower integrals).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology
open scoped ContDiff ENNReal

variable {n : ℕ}

/-- **Translation differences are controlled by the weak derivative.** -/
theorem translate_lintegral_le {f G : Cfg n → ℝ} {k : Fin (n + 1)} (hf : MemLp f 2 (μN n))
    (hG : IsWD k f G) {h : ℝ} (hh : 0 ≤ h) {S T : Set (Cfg n)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hTc : T ⊆ Cube n)
    (hST : ∀ x ∈ S, ∀ s ∈ Icc 0 h, x + s • ek k ∈ T) :
    ∫⁻ x in S, ‖f (x + h • ek k) - f x‖ₑ ≤ ENNReal.ofReal h * ∫⁻ y in T, ‖G y‖ₑ := by
  set e := ek (n := n) k
  have hcube := measurableSet_cube (n := n)
  set F0 : Cfg n → ℝ := (Cube n).indicator f
  set H0 : Cfg n → ℝ := (Cube n).indicator G
  have hF0 : Integrable F0 := (integrable_indicator_iff hcube).2 (hf.integrable one_le_two)
  have hH0 : Integrable H0 := (integrable_indicator_iff hcube).2 (hG.1.integrable one_le_two)
  set F := hF0.aestronglyMeasurable.mk F0
  set H := hH0.aestronglyMeasurable.mk H0
  have hFe : F0 =ᵐ[volume] F := hF0.aestronglyMeasurable.ae_eq_mk
  have hHe : H0 =ᵐ[volume] H := hH0.aestronglyMeasurable.ae_eq_mk
  have hFm : StronglyMeasurable F := hF0.aestronglyMeasurable.stronglyMeasurable_mk
  have hHm : StronglyMeasurable H := hH0.aestronglyMeasurable.stronglyMeasurable_mk
  have hF : Integrable F := hF0.congr hFe
  have hH : Integrable H := hH0.congr hHe
  -- the weak derivative on all of `ℝᴺ`
  have hw : ∀ g : Cfg n → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, F x * dk k g x = -∫ x, H x * g x := fun g hg _ => by
    have h1 : ∫ x, F x * dk k g x = ∫ x, f x * dk k g x ∂μN n := by
      calc ∫ x, F x * dk k g x = ∫ x, F0 x * dk k g x :=
            integral_congr_ae (by filter_upwards [hFe] with x hx; rw [hx])
        _ = ∫ x, (Cube n).indicator (fun x => f x * dk k g x) x :=
            integral_congr_ae (ae_of_all _ fun x => by
              by_cases hx : x ∈ Cube n <;> simp [F0, hx])
        _ = _ := integral_indicator hcube
    have h2 : ∫ x, H x * g x = ∫ x, G x * g x ∂μN n := by
      calc ∫ x, H x * g x = ∫ x, H0 x * g x :=
            integral_congr_ae (by filter_upwards [hHe] with x hx; rw [hx])
        _ = ∫ x, (Cube n).indicator (fun x => G x * g x) x :=
            integral_congr_ae (ae_of_all _ fun x => by
              by_cases hx : x ∈ Cube n <;> simp [H0, hx])
        _ = _ := integral_indicator hcube
    rw [h1, h2]
    exact hG.2 g (hg.of_le (by simp))
  have hid := translate_identity hFm hHm hF hH hw hh
  have hFt : ∀ᵐ x, F0 (x + h • e) = F (x + h • e) :=
    (measurePreserving_add_right volume (h • e)).quasiMeasurePreserving.ae_eq_comp hFe
  have hpt : ∀ᵐ x ∂volume.restrict S,
      ‖f (x + h • e) - f x‖ₑ ≤ ∫⁻ s in Ioc 0 h, ‖H (x + s • e)‖ₑ := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hid, ae_restrict_of_ae hFe,
      ae_restrict_of_ae hFt] with x hx h1 h2 h3
    have hx0 : x ∈ Cube n := hTc (by simpa using hST x hx 0 ⟨le_rfl, hh⟩)
    have hxh : x + h • e ∈ Cube n := hTc (hST x hx h ⟨hh, le_rfl⟩)
    have e0 : f x = F x := by rw [← h2]; simp [F0, indicator_of_mem hx0]
    have eh : f (x + h • e) = F (x + h • e) := by rw [← h3]; simp [F0, indicator_of_mem hxh]
    rw [e0, eh, h1]
    exact enorm_integral_le_lintegral_enorm _
  have hjm : AEMeasurable (Function.uncurry fun x s => ‖H (x + s • e)‖ₑ)
      ((volume.restrict S).prod (volume.restrict (Ioc 0 h))) :=
    (hHm.measurable.enorm.comp (measurable_fst.add (measurable_snd.smul_const e))).aemeasurable
  calc ∫⁻ x in S, ‖f (x + h • e) - f x‖ₑ
      ≤ ∫⁻ x in S, ∫⁻ s in Ioc 0 h, ‖H (x + s • e)‖ₑ := lintegral_mono_ae hpt
    _ = ∫⁻ s in Ioc 0 h, ∫⁻ x in S, ‖H (x + s • e)‖ₑ := lintegral_lintegral_swap hjm
    _ ≤ ∫⁻ s in Ioc 0 h, ∫⁻ y in T, ‖H y‖ₑ := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        rw [← lintegral_indicator hS, ← lintegral_indicator hT,
          ← lintegral_add_right_eq_self (fun y => T.indicator (fun y => ‖H y‖ₑ) y) (s • e)]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ S
        · rw [indicator_of_mem hx, indicator_of_mem (hST x hx s ⟨hs.1.le, hs.2⟩)]
        · rw [indicator_of_notMem hx]; exact bot_le
    _ = ENNReal.ofReal h * ∫⁻ y in T, ‖G y‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
        congr 1
        refine setLIntegral_congr_fun_ae hT ?_
        filter_upwards [hHe] with y hy hyT
        rw [← hy]; simp [H0, indicator_of_mem (hTc hyT)]

/-! ### The logarithm and the cutoff -/

/-- `Lg ε t = log(1 + t/ε)` on `[0, ∞)`, extended oddly. -/
noncomputable def Lg (ε : ℝ) : ℝ → ℝ := oddExt fun t => Real.log (1 + t / ε)

section Lg

variable {ε : ℝ} (hε : 0 < ε)
include hε

lemma hasDerivAt_Lg (t : ℝ) : HasDerivAt (Lg ε) (1 / (|t| + ε)) t := by
  refine hasDerivAt_oddExt (g' := fun s => 1 / (s + ε)) (by simp) (fun s hs => ?_) t
  have hpos : 0 < 1 + s / ε := by positivity
  have h := (((hasDerivAt_id s).div_const ε).const_add 1).log hpos.ne'
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

lemma continuous_Lg' : Continuous fun t : ℝ => 1 / (|t| + ε) :=
  continuous_const.div (continuous_abs.add continuous_const) fun t => by positivity

lemma Lg'_le (t : ℝ) : |1 / (|t| + ε)| ≤ 1 / ε := by
  rw [abs_of_pos (by positivity)]
  exact one_div_le_one_div_of_le hε (by linarith [abs_nonneg t])

omit hε in
lemma Lg_zero : Lg ε 0 = 0 := by simp [Lg, oddExt]

omit hε in
lemma Lg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Lg ε t = Real.log (1 + t / ε) :=
  oddExt_of_nonneg _ ht

lemma continuous_Lg : Continuous (Lg ε) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_Lg hε t).continuousAt

lemma abs_Lg_le (t : ℝ) : |Lg ε t| ≤ |t| / ε := by
  have key : ∀ s, 0 ≤ s → 0 ≤ Real.log (1 + s / ε) ∧ Real.log (1 + s / ε) ≤ s / ε := by
    intro s hs
    have h0 : 0 ≤ s / ε := by positivity
    exact ⟨Real.log_nonneg (by linarith),
      by have := Real.log_le_sub_one_of_pos (show 0 < 1 + s / ε by positivity); linarith⟩
  simp only [Lg, oddExt]
  split_ifs with h
  · rw [abs_of_nonneg (key t h).1, abs_of_nonneg h]; exact (key t h).2
  · rw [abs_neg, abs_of_nonneg (key (-t) (by linarith)).1, abs_of_neg (not_le.1 h)]
    exact (key (-t) (by linarith)).2

end Lg

/-- The cutoff `Π_j sin(π x_j)`. -/
noncomputable def etaS (x : Cfg n) : ℝ := ∏ j, Real.sin (π * x j)

lemma contDiff_etaS : ContDiff ℝ 1 (etaS (n := n)) :=
  contDiff_prod fun j _ => Real.contDiff_sin.comp (contDiff_const.mul
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).contDiff)

lemma etaS_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : etaS (pm σ x) = etaS x := by
  simp only [etaS, pm_apply]
  exact Equiv.prod_comp σ (fun j => Real.sin (π * x j))

lemma etaS_wall (x : Cfg n) (k : Fin (n + 1)) (h : x k = 0 ∨ x k = 1) : etaS x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ k) (by rcases h with h | h <;> simp [h])

/-- The closed sub-cube `[a, 1 - a]ᴺ`. -/
def Qa (n : ℕ) (a : ℝ) : Set (Cfg n) := univ.pi fun _ => Icc a (1 - a)

lemma measurableSet_Qa (a : ℝ) : MeasurableSet (Qa n a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma Qa_sub_cube {a : ℝ} (ha : 0 < a) : Qa n a ⊆ Cube n := fun x hx =>
  Set.mem_univ_pi.2 fun j => by
    have := Set.mem_univ_pi.1 hx j
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

lemma sin_ge_of_mem {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a (1 - a)) :
    Real.sin (π * a) ≤ Real.sin (π * t) := by
  have hπ := Real.pi_pos
  rcases le_total t (1 / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith)
      (by nlinarith [ht.1])
  · rw [show π * t = π - π * (1 - t) by ring, Real.sin_pi_sub]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith)
      (by nlinarith [ht.2])

lemma etaS_ge {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {x : Cfg n} (hx : x ∈ Qa n a) :
    Real.sin (π * a) ^ (n + 1) ≤ etaS x := by
  have hs : 0 ≤ Real.sin (π * a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  calc Real.sin (π * a) ^ (n + 1) = ∏ _j : Fin (n + 1), Real.sin (π * a) := by simp
    _ ≤ etaS x := Finset.prod_le_prod₀ (fun _ _ => hs)
        fun j _ => sin_ge_of_mem ha (Set.mem_univ_pi.1 hx j)

/-! ### Translation invariance of the zero set -/

/-- The points of `[a, 1 - a]ᴺ` whose translate by `h eₖ` stays there. -/
def Sa (n : ℕ) (a h : ℝ) (k : Fin (n + 1)) : Set (Cfg n) :=
  {x | x ∈ Qa n a ∧ x + h • ek k ∈ Qa n a}

lemma measurableSet_Sa (a h : ℝ) (k : Fin (n + 1)) : MeasurableSet (Sa n a h k) :=
  (measurableSet_Qa a).inter ((measurableSet_Qa a).preimage (measurable_id.add_const _))

lemma Sa_segment {a h : ℝ} (k : Fin (n + 1)) :
    ∀ x ∈ Sa n a h k, ∀ s ∈ Icc 0 h, x + s • ek k ∈ Qa n a := by
  intro x hx s hs
  refine Set.mem_univ_pi.2 fun j => ?_
  have h1 := Set.mem_univ_pi.1 hx.1 j
  have h2 := Set.mem_univ_pi.1 hx.2 j
  simp only [Pi.add_apply, Pi.smul_apply, ek, smul_eq_mul] at h2 ⊢
  by_cases hj : j = k
  · subst hj
    simp only [Pi.single_eq_same, mul_one] at h2 ⊢
    exact ⟨by linarith [hs.1, h1.1], by linarith [hs.2, h2.2]⟩
  · simp only [Pi.single_eq_of_ne hj, mul_zero, add_zero] at h2 ⊢
    exact h1

section zero

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {u : Cfg n → ℝ}

/-- **The gradient of `log(u + ε)` is bounded in `L¹([a, 1 - a]ᴺ)`, uniformly in `ε`.** -/
theorem grad_L1_bound (hu : IsGS (settingW .bos n w hw) v u) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (k : Fin (n + 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε > 0,
      ∫⁻ y in Qa n a, ‖1 / (|u y| + ε) * dW k u y‖ₑ ≤ ENNReal.ofReal B := by
  set E := Q (settingW .bos n w hw) v u / ip (μ := μN n) u u
  obtain ⟨C, hC⟩ := ae_bound_cont (n := n)
    (continuous_const.sub ((continuous_LN v).add hw) : Continuous fun x => E - (LN n v x + w x))
  set C' := max C 0
  have hC' : ∀ᵐ x ∂μN n, |E - (LN n v x + w x)| ≤ C' := by
    filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs] at hx; exact hx.trans (le_max_left _ _)
  set c := Real.sin (π * a) ^ (n + 1)
  have hc : 0 < c := pow_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos])) _
  set K := 4 * ∑ k, ∫ x, dk k etaS x ^ 2 ∂μN n + 2 * C' * ∫ x, etaS x ^ 2 ∂μN n
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ ∑ k, ∫ x, dk k (etaS (n := n)) x ^ 2 ∂μN n :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
    have h2 : 0 ≤ ∫ x, etaS (n := n) x ^ 2 ∂μN n := integral_nonneg fun x => sq_nonneg _
    have h3 : 0 ≤ C' := le_max_right _ _
    positivity
  refine ⟨(1 + K / c ^ 2) / 2, by positivity, fun ε hε => ?_⟩
  have hD := hu.1
  have hlog := log_estimate hu hu0 contDiff_etaS etaS_pm etaS_wall hε (le_max_right C 0) hC'
  set q : Cfg n → ℝ := fun y => dW k u y / (u y + ε)
  have hq : MemLp q 2 (μN n) := by
    refine (memLp_dW hD k).of_le_mul (c := 1 / ε)
      ((memLp_dW hD k).aestronglyMeasurable.aemeasurable.div
        (hD.1.aestronglyMeasurable.aemeasurable.add_const ε)).aestronglyMeasurable ?_
    filter_upwards [hu0] with x h0
    have hp : 0 < u x + ε := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have : 1 / ε * |dW k u x| * ε ≤ 1 / ε * |dW k u x| * (u x + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 1 / ε * |dW k u x| * ε = |dW k u x| := by field_simp
    linarith
  -- `∫_{Q_a} q² ≤ K / c²`
  have hq2 : ∫ x, (Qa n a).indicator (fun y => q y ^ 2) x ∂μN n ≤ K / c ^ 2 := by
    have hηq : MemLp (fun x => etaS x * q x) 2 (μN n) := memLp_mul_cont contDiff_etaS.continuous hq
    calc ∫ x, (Qa n a).indicator (fun y => q y ^ 2) x ∂μN n
        ≤ ∫ x, (etaS x * q x) ^ 2 / c ^ 2 ∂μN n := by
          refine integral_mono (hq.integrable_sq.indicator (measurableSet_Qa a))
            (hηq.integrable_sq.div_const _) fun x => ?_
          by_cases hx : x ∈ Qa n a
          · rw [indicator_of_mem hx, le_div_iff₀ (by positivity), mul_pow]
            have h1 := etaS_ge ha ha2 hx
            have h2 : c ^ 2 ≤ etaS x ^ 2 := pow_le_pow_left₀ hc.le h1 2
            nlinarith [sq_nonneg (q x)]
          · rw [indicator_of_notMem hx]; positivity
      _ = (∫ x, (etaS x * q x) ^ 2 ∂μN n) / c ^ 2 := integral_div _ _
      _ ≤ K / c ^ 2 := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          refine le_trans ?_ hlog
          exact Finset.single_le_sum
            (f := fun k => ∫ x, (etaS x * (dW k u x / (u x + ε))) ^ 2 ∂μN n)
            (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ k)
  -- the lower integral
  have hQc := Qa_sub_cube (n := n) ha
  have hres : volume.restrict (Qa n a) = (μN n).restrict (Qa n a) :=
    (Measure.restrict_restrict_of_subset hQc).symm
  have hint : Integrable (fun y => (1 + q y ^ 2) / 2) ((μN n).restrict (Qa n a)) :=
    (((integrable_const 1).add hq.integrable_sq).div_const 2).restrict
  rw [hres]
  calc ∫⁻ y in Qa n a, ‖1 / (|u y| + ε) * dW k u y‖ₑ ∂μN n
      ≤ ∫⁻ y in Qa n a, ENNReal.ofReal ((1 + q y ^ 2) / 2) ∂μN n := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hu0] with y h0
        rw [abs_of_nonneg h0, ← ofReal_norm, Real.norm_eq_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have e : 1 / (u y + ε) * dW k u y = q y := by simp only [q]; ring
        rw [e]
        nlinarith [sq_nonneg (|q y| - 1), sq_abs (q y)]
    _ = ENNReal.ofReal (∫ y in Qa n a, (1 + q y ^ 2) / 2 ∂μN n) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => by positivity)).symm
    _ ≤ ENNReal.ofReal ((1 + K / c ^ 2) / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div, integral_add (integrable_const 1).restrict hq.integrable_sq.restrict,
          setIntegral_const, smul_eq_mul, mul_one, ← integral_indicator (measurableSet_Qa a)]
        have h1 : (μN n).real (Qa n a) ≤ 1 := by
          have : (μN n) (Qa n a) ≤ 1 := by
            rw [Measure.restrict_apply (measurableSet_Qa a), inter_eq_left.2 hQc]
            exact (measure_mono hQc).trans volume_cube.le
          rw [Measure.real]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
        linarith

/-- For each `δ > 0`, the points of `Sa` where `u` vanishes at one end of the segment and is
`≥ δ` at the other form a null set. -/
theorem bad_null (hu : IsGS (settingW .bos n w hw) v u) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (k : Fin (n + 1)) {h : ℝ} (hh : 0 ≤ h) {δ : ℝ}
    (hδ : 0 < δ) :
    volume {x | x ∈ Sa n a h k ∧ ((u x = 0 ∧ δ ≤ u (x + h • ek k)) ∨
      (δ ≤ u x ∧ u (x + h • ek k) = 0))} = 0 := by
  set e := ek (n := n) k
  set S := Sa n a h k
  set A := {x | x ∈ S ∧ ((u x = 0 ∧ δ ≤ u (x + h • e)) ∨ (δ ≤ u x ∧ u (x + h • e) = 0))}
  obtain ⟨B, hB0, hB⟩ := grad_L1_bound hu hu0 ha ha2 k
  have hQc := Qa_sub_cube (n := n) ha
  have hSc : S ⊆ Cube n := fun x hx => hQc hx.1
  have hD := hu.1
  -- the Chebyshev bound, for every `ε`
  have key : ∀ ε > 0, ENNReal.ofReal (Real.log (1 + δ / ε)) * volume A ≤
      ENNReal.ofReal (h * B) := by
    intro ε hε
    set wε : Cfg n → ℝ := fun x => Lg ε (u x)
    have hwL : MemLp wε 2 (μN n) :=
      hD.1.of_le_mul (c := 1 / ε) ((continuous_Lg hε).comp_aestronglyMeasurable
        hD.1.aestronglyMeasurable) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          have := abs_Lg_le hε (u x)
          rw [div_eq_inv_mul, ← one_div] at this
          exact this)
    have hwD := isWD_comp (h1W_of_mem hD) (hasDerivAt_Lg hε) (continuous_Lg' hε) (Lg'_le hε) Lg_zero k
    have htr := translate_lintegral_le hwL hwD hh (measurableSet_Sa a h k) (measurableSet_Qa a)
      hQc (Sa_segment k)
    have hint : ∫⁻ x in S, ‖wε (x + h • e) - wε x‖ₑ ≤ ENNReal.ofReal (h * B) := by
      rw [ENNReal.ofReal_mul hh]
      exact htr.trans (by gcongr; exact hB ε hε)
    -- measurability through a strongly measurable representative
    set wm := hwL.aestronglyMeasurable.mk wε
    have hwe : wε =ᵐ[μN n] wm := hwL.aestronglyMeasurable.ae_eq_mk
    have hwv : ∀ᵐ x ∂volume, x ∈ Cube n → wε x = wm x :=
      (ae_restrict_iff' measurableSet_cube).1 hwe
    have hwv' : ∀ᵐ x ∂volume, x + h • e ∈ Cube n → wε (x + h • e) = wm (x + h • e) :=
      (measurePreserving_add_right volume (h • e)).quasiMeasurePreserving.ae hwv
    have hmeas : AEMeasurable (fun x => ‖wε (x + h • e) - wε x‖ₑ) (volume.restrict S) := by
      refine (((hwL.aestronglyMeasurable.stronglyMeasurable_mk.measurable.comp
        (measurable_add_const (h • e))).sub
        hwL.aestronglyMeasurable.stronglyMeasurable_mk.measurable).enorm).aemeasurable.congr ?_
      filter_upwards [ae_restrict_mem (measurableSet_Sa a h k), ae_restrict_of_ae hwv,
        ae_restrict_of_ae hwv'] with x hx h1 h2
      rw [h1 (hSc hx), h2 (hQc hx.2)]
      rfl
    have hcheb := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (Real.log (1 + δ / ε)))
    have hsub : A ⊆ {x | ENNReal.ofReal (Real.log (1 + δ / ε)) ≤ ‖wε (x + h • e) - wε x‖ₑ} ∩ S := by
      rintro x ⟨hxS, hx⟩
      refine ⟨?_, hxS⟩
      change ENNReal.ofReal _ ≤ _
      rw [← ofReal_norm, Real.norm_eq_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmono : ∀ t, δ ≤ t → Real.log (1 + δ / ε) ≤ Lg ε t := fun t ht => by
        rw [Lg_of_nonneg (hδ.le.trans ht)]
        exact Real.log_le_log (by positivity) (by
          have := div_le_div_of_nonneg_right ht hε.le; linarith)
      rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · simp only [wε, h0, Lg_zero, sub_zero]
        exact (hmono _ h1).trans (le_abs_self _)
      · simp only [wε, h1, Lg_zero, zero_sub, abs_neg]
        exact (hmono _ h0).trans (le_abs_self _)
    calc ENNReal.ofReal (Real.log (1 + δ / ε)) * volume A
        ≤ ENNReal.ofReal (Real.log (1 + δ / ε)) *
            (volume.restrict S) {x | ENNReal.ofReal (Real.log (1 + δ / ε)) ≤
              ‖wε (x + h • e) - wε x‖ₑ} :=
          mul_le_mul' le_rfl ((measure_mono hsub).trans (Measure.le_restrict_apply _ _))
      _ ≤ _ := hcheb
      _ ≤ _ := hint
  -- letting `ε → 0`
  have hfin : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [volume_cube]; exact ENNReal.one_ne_top)
      (measure_mono fun x hx => hSc hx.1)
  by_contra hA
  have hm : 0 < (volume A).toReal := ENNReal.toReal_pos hA hfin
  set m := (volume A).toReal
  set L := h * B / m + 1
  have hL : 0 < L := by positivity
  have hE : 1 < Real.exp L := Real.one_lt_exp_iff.2 hL
  set ε := δ / (Real.exp L - 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hlog : Real.log (1 + δ / ε) = L := by
    have : δ / ε = Real.exp L - 1 := by
      simp only [ε]; field_simp
    rw [this, add_sub_cancel, Real.log_exp]
  have h1 := key ε hε
  rw [hlog, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hL.le] at h1
  have h2 : L * m = h * B + m := by simp only [L]; field_simp
  rw [h2] at h1
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  linarith

/-- **The zero set of a nonnegative bosonic ground state is invariant under translations** inside
`[a, 1 - a]ᴺ`: for a.e. `x ∈ Sa`, `u(x) = 0 ↔ u(x + h eₖ) = 0`. -/
theorem zero_set_translate (hu : IsGS (settingW .bos n w hw) v u) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (k : Fin (n + 1)) {h : ℝ} (hh : 0 ≤ h) :
    ∀ᵐ x ∂volume, x ∈ Sa n a h k → (u x = 0 ↔ u (x + h • ek k) = 0) := by
  set e := ek (n := n) k
  have hQc := Qa_sub_cube (n := n) ha
  have hn0 : ∀ᵐ x ∂volume, x ∈ Cube n → 0 ≤ u x := (ae_restrict_iff' measurableSet_cube).1 hu0
  have hn1 : ∀ᵐ x ∂volume, x + h • e ∈ Cube n → 0 ≤ u (x + h • e) :=
    (measurePreserving_add_right volume (h • e)).quasiMeasurePreserving.ae hn0
  have hbad : ∀ᵐ x ∂volume, ∀ j : ℕ, x ∉ {x | x ∈ Sa n a h k ∧
      ((u x = 0 ∧ 1 / ((j : ℝ) + 1) ≤ u (x + h • e)) ∨
        (1 / ((j : ℝ) + 1) ≤ u x ∧ u (x + h • e) = 0))} :=
    ae_all_iff.2 fun j => measure_eq_zero_iff_ae_notMem.1 (bad_null hu hu0 ha ha2 k hh
      (by positivity))
  filter_upwards [hn0, hn1, hbad] with x h0 h1 hb hx
  have hu0x := h0 (hQc hx.1)
  have hu1x := h1 (hQc hx.2)
  constructor
  · intro hz
    by_contra hne
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_of_le_of_ne hu1x (Ne.symm hne))
    exact hb j ⟨hx, Or.inl ⟨hz, hj.le⟩⟩
  · intro hz
    by_contra hne
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_of_le_of_ne hu0x (Ne.symm hne))
    exact hb j ⟨hx, Or.inr ⟨hj.le, hz⟩⟩

end zero

end DFT.Continuum.Line
