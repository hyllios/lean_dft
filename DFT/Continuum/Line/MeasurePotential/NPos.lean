/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.NUcp
import DFT.Continuum.Line.Regularity.Positive

/-!
# Bosonic ground-state densities of measure potentials are positive

For `N` bosons with a measure potential `ν` and a continuous interaction `w`, the continuous density
`ρ̂` of a ground state is positive on `(0, 1)` (**`rhoHat_pos_bos`**).

The argument of `Line/Positive` (after Corso): if `ρ̂(t₀) = 0`, write `ρ̂ = g²` with `g ∈ H¹₀`;
then `g(t₀) = 0` and `ρ̂(t) = (g(t) - g(t₀))² ≤ |t - t₀| ∫ g'²` (`sq_sub_le_H10`), which is all the
slab estimate needs. So `Ψ_U = 1_U Ψ`, `U = {xᵢ < t₀ ∀ i}`, is an `H¹₀` state; the energy splits
(the mixed density of `Ψ_U` and `Ψ - Ψ_U` vanishes), and one of the two pieces is a ground state
vanishing on a set of positive measure, contradicting unique continuation (`gsN_ne_zero_bos`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {w : Cfg n → ℝ}

/-- `(g(b) - g(a))² ≤ |b - a| ∫ g'²` for `g ∈ H¹₀`. -/
lemma sq_sub_le_H10 {g : ℝ → ℝ} (hg : H10 g) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : (g b - g a) ^ 2 ≤ |b - a| * kinM g := by
  have hk : 0 ≤ kinM g := integral_nonneg fun _ => sq_nonneg _
  have key : ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a ≤ b →
      (g b - g a) ^ 2 ≤ (b - a) * kinM g := fun {a b} ha hb hab => by
    have hac : AbsolutelyContinuousOnInterval g a b := hg.1.mono (by
      rw [uIcc01, uIcc_of_le hab]; exact Icc_subset_Icc ha.1 hb.2)
    have hd2 : IntegrableOn (fun t => deriv g t ^ 2) (Ioo (0 : ℝ) 1) := hg.2.2.2
    have hii : IntervalIntegrable (fun t => deriv g t ^ 2) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
        (hd2.mono_set (Ioo_subset_Ioo ha.1 hb.2))
    have h1 := sq_le_interval hab hac.intervalIntegrable_deriv hii
    rw [hac.integral_deriv_eq_sub] at h1
    have h2 : ∫ t in a..b, deriv g t ^ 2 ≤ kinM g := by
      rw [kinM, integral_vol01]
      exact intervalIntegral.integral_mono_interval ha.1 hab hb.2
        (ae_of_all _ fun s => by simp only [Pi.zero_apply]; positivity)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hd2)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hab))
  rcases le_total a b with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact key ha hb h
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, ← neg_sub, neg_sq]; exact key hb ha h

/-- The mixed density of states with disjoint supports vanishes. -/
lemma rhoHat2_eq_zero (hw : Continuous w) {τ : Stat} {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    (hΨ : Ψ ∈ DomW τ n) (h : ∀ x, Φ x * Ψ x = 0) : rhoHat2 τ Φ Ψ = 0 :=
  pot_eq_of_integral fun v => by
    rw [int_rhoHat2 hw hΦ hΨ]
    simp [pf, h, SturmLiouville.iccExt]

/-- **Given unique continuation, the density of a ground state of a measure potential is positive
on `(0, 1)`.** -/
theorem rhoHat_pos_of_ucp (hw : Continuous w) {τ : Stat} {ν : PotM}
    (hucp : ∀ Φ : Cfg n → ℝ, IsGSN τ w ν Φ → ∀ᵐ x ∂μN n, Φ x ≠ 0) {Ψ : Cfg n → ℝ}
    (hΨ : IsGSN τ w ν Ψ) {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1) : 0 < iccExt (rhoHat τ Ψ) t0 := by
  have ht0I := Ioo_subset_Icc_self ht0
  set g := gN τ Ψ
  have hg : H10 g := h10_gN Ψ
  set K := iccExt (rhoHat τ Ψ)
  have hKg : ∀ t ∈ Icc (0 : ℝ) 1, K t = g t ^ 2 := fun t ht => ext_rhoHat ht
  have hK0 : 0 ≤ K t0 := by rw [hKg t0 ht0I]; positivity
  by_contra hcon
  have hKt0 : K t0 = 0 := le_antisymm (not_lt.1 hcon) hK0
  have hg0 : g t0 = 0 := by rw [hKg t0 ht0I] at hKt0; exact pow_eq_zero_iff two_ne_zero |>.1 hKt0
  -- `K(t) ≤ L |t - t₀|` near `t₀`
  set η := min t0 (1 - t0)
  have hη : 0 < η := lt_min ht0.1 (by linarith [ht0.2])
  set L := kinM g
  have hL : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have hKle : ∀ t, |t - t0| ≤ η → K t ≤ L * |t - t0| := fun t ht => by
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [abs_le] at ht
      constructor <;> linarith [min_le_left t0 (1 - t0), min_le_right t0 (1 - t0)]
    rw [hKg t htI]
    have := sq_sub_le_H10 hg ht0I htI
    rw [hg0, sub_zero] at this
    linarith [mul_comm L |t - t0|]
  have hρ : ∀ v : C01, dens (settingW τ n w hw) Ψ v = ∫ t, iccExt v t * K t ∂vol01 := fun v =>
    (int_rhoHat hw hΨ.1 v).symm
  have hKi : Integrable K vol01 :=
    (continuous_iccExt _).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hslab := fun (F : Cfg n → ℝ) (_ : AEStronglyMeasurable F (μN n)) hF i =>
    slab_small (w := w) (hw := hw) hΨ.1 (K := K) hρ hKi hη hL hKle (F := F) hF i
  -- the cut state
  set U := Uset (Finset.univ : Finset (Fin (n + 1))) t0
  have hU : MeasurableSet U := measurableSet_Uset _ t0
  have hmemU : ∀ x, x ∈ U ↔ ∀ i, x i < t0 := fun x => by
    simp [U, Uset, HalfT]
  set ΨU := U.indicator Ψ
  have hWD : ∀ k, IsWD k ΨU (U.indicator (dW k Ψ)) :=
    isWD_cutAll (h1W_of_mem hΨ.1) t0 hslab Finset.univ
  have hUD : ΨU ∈ DomW τ n := by
    refine ⟨hΨ.1.1.indicator hU.nullMeasurableSet, fun k => ⟨_, hWD k⟩, fun σ _ => ?_⟩
    filter_upwards [hΨ.1.2.2 σ trivial] with x hx
    have hσ : pm σ x ∈ U ↔ x ∈ U := by
      rw [hmemU, hmemU]
      exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩
    by_cases hxU : x ∈ U
    · simp only [ΨU, indicator_of_mem hxU, indicator_of_mem (hσ.2 hxU), hx]
    · simp only [ΨU, indicator_of_notMem hxU, indicator_of_notMem (fun h => hxU (hσ.1 h)),
        mul_zero]
  set ΨV := Ψ - ΨU
  have hVD : ΨV ∈ DomW τ n := (DomW τ n).sub_mem hΨ.1 hUD
  have hsplit : Ψ = ΨU + (1 : ℝ) • ΨV := by simp [ΨV]
  have hUV : ∀ x, ΨU x * ΨV x = 0 := fun x => by
    by_cases hxU : x ∈ U <;> simp [ΨV, ΨU, hxU]
  have hdU : ∀ k, dW k ΨU =ᵐ[μN n] U.indicator (dW k Ψ) := fun k => dW_ae_eq (hWD k)
  have hdV : ∀ k, dW k ΨV =ᵐ[μN n] fun x => dW k Ψ x - U.indicator (dW k Ψ) x := fun k => by
    have h := IsWD.add hΨ.1.1 (hΨ.1.1.indicator hU.nullMeasurableSet |>.const_mul (-1))
      (dW_spec (hΨ.1.2.1 k)) (IsWD.const_mul (-1) (hWD k))
    have e1 : (fun x => Ψ x + -1 * ΨU x) = ΨV := funext fun x => by simp [ΨV]; ring
    have e2 : (fun x => dW k Ψ x + -1 * U.indicator (dW k Ψ) x) =
        fun x => dW k Ψ x - U.indicator (dW k Ψ) x := funext fun x => by ring
    rw [e1, e2] at h
    exact dW_ae_eq h
  have hcross_h0 : h0W n w ΨU ΨV = 0 := by
    simp only [h0W]
    have hk : ∀ k, ∫ x, dW k ΨU x * dW k ΨV x ∂μN n = 0 := fun k =>
      integral_eq_zero_of_ae (by
        filter_upwards [hdU k, hdV k] with x h1 h2
        rw [h1, h2]
        by_cases hxU : x ∈ U <;> simp [hxU])
    simp only [hk, Finset.sum_const_zero, zero_add]
    exact integral_eq_zero_of_ae (Eventually.of_forall fun x => by simp [hUV x])
  have hQ : QMN τ w ν Ψ = QMN τ w ν ΨU + QMN τ w ν ΨV := by
    rw [congrArg (QMN τ w ν) hsplit, QMN_expand hw ν hUD hVD, hcross_h0,
      rhoHat2_eq_zero hw hUD hVD hUV, map_zero]
    ring
  have hsq : ∀ (F : Cfg n → ℝ), ∫ x, F x ^ 2 ∂μN n = ip (μ := μN n) F F := fun F => by
    simp only [ip, sq]
  have hip : ip (μ := μN n) Ψ Ψ = ip (μ := μN n) ΨU ΨU + ip (μ := μN n) ΨV ΨV := by
    have hcross_ip : ip (μ := μN n) ΨU ΨV = 0 :=
      integral_eq_zero_of_ae (Eventually.of_forall fun x => by simp [hUV x])
    rw [congrArg (fun φ => ip (μ := μN n) φ φ) hsplit]
    rw [ip_expand (S := settingW τ n w hw) hUD hVD, hcross_ip]; ring
  set E := QMN τ w ν Ψ
  have hge : ∀ φ ∈ DomW τ n, E * ip (μ := μN n) φ φ ≤ QMN τ w ν φ := fun φ hφ => by
    rw [← hsq]; exact EN_mul_le hw hΨ hφ
  have hp1 : ip (μ := μN n) Ψ Ψ = 1 := by rw [← hsq]; exact hΨ.2.1
  have h1 := hge ΨU hUD
  have h2 := hge ΨV hVD
  have hQU : QMN τ w ν ΨU = E * ip (μ := μN n) ΨU ΨU := by
    have : E = E * ip (μ := μN n) Ψ Ψ := by rw [hp1, mul_one]
    rw [hip] at this; linarith
  have hipU0 : 0 ≤ ip (μ := μN n) ΨU ΨU := integral_nonneg fun x => mul_self_nonneg _
  have hPV : 0 < μN n (Set.pi univ fun j : Fin (n + 1) =>
      Ioo (if j = 0 then t0 else 0) 1) :=
    pos_measure_pi (fun j => by split_ifs <;> linarith [ht0.1])
      (fun j => by split_ifs <;> linarith [ht0.2]) (fun _ => le_rfl)
  have hPU : 0 < μN n (Set.pi univ fun _ : Fin (n + 1) => Ioo 0 t0) :=
    pos_measure_pi (fun _ => le_rfl) (fun _ => ht0.1) (fun _ => ht0.2.le)
  rcases hipU0.lt_or_eq with hpos | hzero
  · -- the normalised `Ψ_U` is a ground state vanishing on `{x₀ > t₀}`
    set c := 1 / √(ip (μ := μN n) ΨU ΨU)
    have hc2 : c ^ 2 = 1 / ip (μ := μN n) ΨU ΨU := by
      rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
    have hcD : c • ΨU ∈ DomW τ n := Submodule.smul_mem _ c hUD
    have hcn : ∫ x, (c • ΨU) x ^ 2 ∂μN n = 1 := by
      rw [hsq]; simp only [ip, Pi.smul_apply, smul_eq_mul]
      rw [show (fun x => c * ΨU x * (c * ΨU x)) = fun x => c ^ 2 * (ΨU x * ΨU x) from
        funext fun x => by ring, integral_const_mul, hc2]
      exact one_div_mul_cancel hpos.ne'
    have hGS : IsGSN τ w ν (c • ΨU) := ⟨hcD, hcn, fun φ hφ hφn => by
      rw [QMN_smul hw ν hUD, hQU, hc2]
      have := hge φ hφ
      rw [← hsq, hφn, mul_one] at this
      field_simp; linarith⟩
    refine not_ae_ne_of_zero_on hPV (fun x hx => ?_) (hucp _ hGS)
    have hx0 : ¬ x 0 < t0 := by
      have := hx 0 trivial; simp only [↓reduceIte] at this; exact not_lt.2 this.1.le
    have hxU : x ∉ U := fun h => hx0 ((hmemU x).1 h 0)
    simp [ΨU, hxU]
  · -- `Ψ_U = 0`, so `Ψ = 0` on `U`
    have hz : ΨU =ᵐ[μN n] 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (ΨU x))
        (int_mul_L2 hUD.1 hUD.1)).1 hzero.symm
      filter_upwards [this] with x hx
      exact mul_self_eq_zero.1 hx
    have hucp' := hucp _ hΨ
    have hP : μN n (Set.pi univ fun _ : Fin (n + 1) => Ioo 0 t0) = 0 := by
      have : μN n {x | ¬ (Ψ x ≠ 0 ∧ ΨU x = 0)} = 0 := ae_iff.1 (hucp'.and hz)
      refine measure_mono_null (fun x hx => ?_) this
      intro ⟨h1, h2⟩
      have hxU : x ∈ U := (hmemU x).2 fun i => (hx i trivial).2
      simp only [ΨU, indicator_of_mem hxU] at h2
      exact h1 h2
    exact hPU.ne' hP

/-- **The density of a bosonic ground state of a measure potential is positive on `(0, 1)`.** -/
theorem rhoHat_pos_bos (hw : Continuous w) {ν : PotM} {Ψ : Cfg n → ℝ} (hΨ : IsGSN .bos w ν Ψ)
    {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1) : 0 < iccExt (rhoHat .bos Ψ) t0 :=
  rhoHat_pos_of_ucp hw (fun _ h => gsN_ne_zero_bos hw h) hΨ ht0

end DFT.Continuum.Line
