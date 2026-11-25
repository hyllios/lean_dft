/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.NeuFer
import DFT.Continuum.Line.Regularity.Positive

/-!
# Ground-state densities with Neumann walls are positive on `[0, 1]`

For bosons or fermions, every `H⁻¹` potential and every continuous interaction, the density of a
Neumann ground state is positive on the closed interval `[0, 1]`, walls included
(**`rhoE_pos`**). With `integral_fnE_rhoE` this is the necessity half of Corso's Theorem 2.3:
`v`-representable densities lie in `{ρ ∈ H¹ : ρ > 0 on [0, 1], ∫ ρ = N}` (**`vrepNH_nec`**).

The proof works at a wall as in the interior. Let `u = |Ψ|` (the companion `B` for fermions) and
suppose `ρ(t₀) = 0`, so that `ρ(t) ≤ L |t - t₀|` (`ρ = g²`, `g ∈ H¹(0, 1)`, `g(t₀) = 0`). Test the
Neumann weak derivative of `L_ε = log(1 + u/ε)` with `φ(x) = χ(x₀) Z(x)`, where
`χ' = α - β`, `β` is a normalised bump of width `δ = a ε⁴` at `t₀` and `α` a fixed normalised bump
nearby, and `Z` keeps the other particles in fixed separated windows. On the support of `φ` the
cutoff `η = Π_{i≠j}(xᵢ - xⱼ)` of Moser's estimate is bounded below, so
`∫ L_ε α Z ≤ ∫ (u/ε) β + C ≤ C'` uniformly in `ε`. But `L_ε → ∞` where `u > 0`, which is almost
everywhere by unique continuation.

* `tentR`, `nbump`, `chiAB`: one-dimensional test functions; `exists_grid`: windows for the
  other particles.
* `sq_sub_le_H1N`, `log_wall_ineq`, `rho_pos_core`, **`rhoE_pos`**, `integral_fnE_rhoE`,
  `VRepNH`, **`vrepNH_nec`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Metric

variable {n : ℕ}

/-! ### One-dimensional test functions -/

/-- The tent `max 0 (1 - |t - m|/h)`. -/
noncomputable def tentR (m h t : ℝ) : ℝ := max 0 (1 - |t - m| / h)

section tent

variable {m h : ℝ}

lemma continuous_tentR (m h : ℝ) : Continuous (tentR m h) := by unfold tentR; fun_prop

lemma tentR_nonneg (t : ℝ) : 0 ≤ tentR m h t := le_max_left _ _

lemma tentR_le_one (hh : 0 < h) (t : ℝ) : tentR m h t ≤ 1 :=
  max_le zero_le_one (by have := div_nonneg (abs_nonneg (t - m)) hh.le; linarith)

lemma tentR_eq_zero (hh : 0 < h) {t : ℝ} (ht : h ≤ |t - m|) : tentR m h t = 0 :=
  max_eq_left (by rw [sub_nonpos, le_div_iff₀ hh, one_mul]; exact ht)

lemma tentR_ge_half (hh : 0 < h) {t : ℝ} (ht : |t - m| ≤ h / 2) : 1 / 2 ≤ tentR m h t := by
  refine le_max_of_le_right ?_
  have : |t - m| / h ≤ 1 / 2 := by rw [div_le_iff₀ hh]; linarith
  linarith

lemma integrable_cont_mu1 {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ1 :=
  hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self

lemma integral_tentR_pos (hh : 0 < h) (h0 : 0 ≤ m - h) (h1 : m + h ≤ 1) :
    0 < ∫ t, tentR m h t ∂μ1 := by
  set J := Ioo (m - h / 2) (m + h / 2)
  have hJ : J ⊆ Ioo 0 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hle : ∫ t, J.indicator (fun _ => (1 / 2 : ℝ)) t ∂μ1 ≤ ∫ t, tentR m h t ∂μ1 := by
    refine integral_mono ((integrable_const _).indicator measurableSet_Ioo)
      (integrable_cont_mu1 (continuous_tentR m h)) fun t => ?_
    by_cases ht : t ∈ J
    · rw [indicator_of_mem ht]
      exact tentR_ge_half hh (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    · rw [indicator_of_notMem ht]; exact tentR_nonneg t
  have hval : ∫ t, J.indicator (fun _ => (1 / 2 : ℝ)) t ∂μ1 = h * (1 / 2) := by
    rw [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul, measureReal_def,
      Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 hJ, Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  linarith [hval ▸ hle, mul_pos hh (by norm_num : (0 : ℝ) < 1 / 2)]

end tent

/-- The normalised tent. -/
noncomputable def nbump (m h t : ℝ) : ℝ := tentR m h t / ∫ s, tentR m h s ∂μ1

section nbump

variable {m h : ℝ} (hh : 0 < h) (h0 : 0 ≤ m - h) (h1 : m + h ≤ 1)

lemma continuous_nbump (m h : ℝ) : Continuous (nbump m h) :=
  (continuous_tentR m h).div_const _

include hh h0 h1

lemma nbump_nonneg (t : ℝ) : 0 ≤ nbump m h t :=
  div_nonneg (tentR_nonneg t) (integral_tentR_pos hh h0 h1).le

lemma integral_nbump : ∫ t, nbump m h t ∂μ1 = 1 := by
  unfold nbump
  rw [integral_div]
  exact div_self (integral_tentR_pos hh h0 h1).ne'

omit h0 h1 in
lemma nbump_eq_zero {t : ℝ} (ht : h ≤ |t - m|) : nbump m h t = 0 := by
  rw [nbump, tentR_eq_zero hh ht, zero_div]

lemma nbump_ge {t : ℝ} (ht : |t - m| ≤ h / 2) :
    1 / 2 / (∫ s, tentR m h s ∂μ1) ≤ nbump m h t :=
  div_le_div_of_nonneg_right (tentR_ge_half hh ht) (integral_tentR_pos hh h0 h1).le

end nbump

/-- `χ(t) = ∫₀ᵗ (α - β)`. -/
noncomputable def chiAB (α β : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, (α s - β s)

section chi

variable {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β)
include hα hβ

lemma hasDerivAt_chiAB (t : ℝ) : HasDerivAt (chiAB α β) (α t - β t) t :=
  ((hα.sub hβ).integral_hasStrictDerivAt 0 t).hasDerivAt

lemma deriv_chiAB : deriv (chiAB α β) = fun t => α t - β t :=
  funext fun t => (hasDerivAt_chiAB hα hβ t).deriv

lemma contDiff_chiAB : ContDiff ℝ 1 (chiAB α β) :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_chiAB hα hβ t).differentiableAt,
    by rw [deriv_chiAB hα hβ]; exact hα.sub hβ⟩

lemma chiAB_eq_sub (t : ℝ) :
    chiAB α β t = (∫ s in (0 : ℝ)..t, α s) - ∫ s in (0 : ℝ)..t, β s :=
  intervalIntegral.integral_sub (hα.intervalIntegrable _ _) (hβ.intervalIntegrable _ _)

omit hα hβ in
lemma chiAB_zero : chiAB α β 0 = 0 := by simp [chiAB]

variable (hα0 : ∀ t, 0 ≤ α t) (hβ0 : ∀ t, 0 ≤ β t) (hα1 : ∫ t, α t ∂μ1 = 1)
  (hβ1 : ∫ t, β t ∂μ1 = 1)

include hα1 hβ1 in
lemma chiAB_one : chiAB α β 1 = 0 := by
  rw [chiAB_eq_sub hα hβ, ← integral_mu1, ← integral_mu1, hα1, hβ1, sub_self]

omit hα hβ in
lemma int_mem01 {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∫ t, f t ∂μ1 = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ ∫ s in (0 : ℝ)..t, f s ∧ ∫ s in (0 : ℝ)..t, f s ≤ 1 := by
  refine ⟨intervalIntegral.integral_nonneg ht.1 fun s _ => hf0 s, ?_⟩
  rw [← hf1, integral_mu1]
  exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (ae_of_all _ fun s => hf0 s) (hf.intervalIntegrable _ _)

include hα0 hβ0 hα1 hβ1 in
lemma abs_chiAB_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |chiAB α β t| ≤ 1 := by
  rw [chiAB_eq_sub hα hβ]
  have h1 := int_mem01 hα hα0 hα1 ht
  have h2 := int_mem01 hβ hβ0 hβ1 ht
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

include hα1 hβ1 in
/-- `χ` vanishes outside `[lo, hi]` on `[0, 1]` when `α` and `β` do. -/
lemma chiAB_eq_zero_of {lo hi : ℝ} (hlo : ∀ t, t ≤ lo → α t = 0 ∧ β t = 0)
    (hhi : ∀ t, hi ≤ t → α t = 0 ∧ β t = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hout : t ≤ lo ∨ hi ≤ t) : chiAB α β t = 0 := by
  rcases hout with h | h
  · unfold chiAB
    refine intervalIntegral.integral_zero_ae (ae_of_all _ fun s hs => ?_)
    rw [uIoc_of_le ht.1] at hs
    have := hlo s (hs.2.trans h)
    rw [this.1, this.2, sub_self]
  · have e : ∀ f : ℝ → ℝ, Continuous f → (∀ s, hi ≤ s → f s = 0) →
        ∫ s in (0 : ℝ)..t, f s = ∫ s, f s ∂μ1 := fun f hf hz => by
      rw [integral_mu1, ← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t 1)]
      have : ∫ s in t..1, f s = 0 :=
        intervalIntegral.integral_zero_ae (ae_of_all _ fun s hs => by
          rw [uIoc_of_le ht.2] at hs
          exact hz s (h.trans hs.1.le))
      rw [this, add_zero]
    rw [chiAB_eq_sub hα hβ, e α hα fun s hs => (hhi s hs).1, e β hβ fun s hs => (hhi s hs).2,
      hα1, hβ1, sub_self]

end chi

/-! ### The inequality on the cube -/

lemma dk0_eq_zero {Z : Cfg n → ℝ} (hZ : ContDiff ℝ 1 Z)
    (hZc : ∀ x (s : ℝ), Z (x + s • (Pi.single 0 1 : Cfg n)) = Z x) (x : Cfg n) :
    dk 0 Z x = 0 := by
  set v : Cfg n := Pi.single 0 1
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun s : ℝ => Z (x + s • v)) (fderiv ℝ Z x v) 0 :=
    (hZ.differentiable one_ne_zero x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have h2 : HasDerivAt (fun s : ℝ => Z (x + s • v)) 0 0 := by
    have : (fun s : ℝ => Z (x + s • v)) = fun _ => Z x := funext fun s => hZc x s
    rw [this]; exact hasDerivAt_const _ _
  exact h1.unique h2

lemma integral_coord0 {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f (x 0) ∂μN n = ∫ t, f t ∂μ1 := by
  have hi : Integrable (fun x : Cfg n => f (x 0)) (μN n) :=
    integrableN (hf.comp (continuous_apply 0))
  rw [integral_cube_cons' hi]
  simp only [Fin.cons_zero, setIntegral_const, measureReal_def, volume_cube',
    ENNReal.toReal_one, one_smul]

/-- **The basic inequality.** For `u ≥ 0` with the weighted logarithmic bound `K`, the test
`χ(x₀) Z(x)` with `χ' = α - β` gives
`∫ log(1 + u/ε) α(x₀) Z ≤ (2ε³)⁻¹ ∫ u² β(x₀) + ε/2 + √K / c`, where `c ≤ |η|` on the support of
the test function. -/
theorem log_wall_ineq {u : Cfg n → ℝ} (hu : u ∈ DomN .bos n) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η) {K : ℝ} {ε : ℝ} (hε : 0 < ε)
    (hK : ∫ x, (η x * (dWN 0 u x / (u x + ε))) ^ 2 ∂μN n ≤ K)
    {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β) (hα0 : ∀ t, 0 ≤ α t)
    (hβ0 : ∀ t, 0 ≤ β t) (hα1 : ∫ t, α t ∂μ1 = 1) (hβ1 : ∫ t, β t ∂μ1 = 1)
    {Z : Cfg n → ℝ} (hZ : ContDiff ℝ 1 Z) (hZ0 : ∀ x, 0 ≤ Z x) (hZ1 : ∀ x, Z x ≤ 1)
    (hZc : ∀ x (s : ℝ), Z (x + s • (Pi.single 0 1 : Cfg n)) = Z x) {c : ℝ} (hc : 0 < c)
    (hηc : ∀ x ∈ Cube n, chiAB α β (x 0) * Z x ≠ 0 → c ≤ |η x|) :
    ∫ x, Lg ε (u x) * (α (x 0) * Z x) ∂μN n ≤
      1 / (2 * ε ^ 3) * ∫ x, u x ^ 2 * β (x 0) ∂μN n + ε / 2 + √K / c := by
  set χ := chiAB α β
  have hχ : ContDiff ℝ 1 χ := contDiff_chiAB hα hβ
  set L : Cfg n → ℝ := fun x => Lg ε (u x)
  set G : Cfg n → ℝ := fun x => 1 / (|u x| + ε) * dWN 0 u x
  have hLG : IsWDN 0 L G :=
    isWDN_comp hu (hasDerivAt_Lg hε) (continuous_Lg' hε) (Lg'_le hε) Lg_zero 0
  have hLm : MemLp L 2 (μN n) := hu.1.of_le_mul (c := 1 / ε)
    ((continuous_Lg hε).comp_aestronglyMeasurable hu.1.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, div_eq_mul_inv, one_mul, mul_comm]
      exact (abs_Lg_le hε _).trans (le_of_eq (by rw [div_eq_mul_inv])))
  -- the test function
  set φ : Cfg n → ℝ := fun x => χ (x 0) * Z x
  have hχ0 : Continuous fun x : Cfg n => χ (x 0) := hχ.continuous.comp (continuous_apply 0)
  have hφ : TestN 0 φ := ⟨(hχ.comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (n + 1) => ℝ) 0).contDiff).mul hZ, fun x hx => by
    rcases hx with h | h
    · simp [φ, h, χ, chiAB_zero]
    · simp [φ, h, χ, chiAB_one hα hβ hα1 hβ1]⟩
  have hdφ : ∀ x, dk 0 φ x = (α (x 0) - β (x 0)) * Z x := fun x => by
    have h := dk_mul (a := fun x : Cfg n => χ (x 0)) (b := Z)
      ((hχ.comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (n + 1) => ℝ) 0).contDiff).differentiable one_ne_zero)
      (hZ.differentiable one_ne_zero) 0 x
    rw [h, dk0_eq_zero hZ hZc, dk_coord0 (hχ.differentiable one_ne_zero), deriv_chiAB hα hβ]
    ring
  have hw := hLG.2 φ hφ
  simp only [hdφ] at hw
  -- integrability
  have hαZ : Continuous fun x : Cfg n => α (x 0) * Z x :=
    (hα.comp (continuous_apply 0)).mul hZ.continuous
  have hβZ : Continuous fun x : Cfg n => β (x 0) * Z x :=
    (hβ.comp (continuous_apply 0)).mul hZ.continuous
  have iα := int_mul_cont hLm hαZ
  have iβ := int_mul_cont hLm hβZ
  have iG := int_mul_cont hLG.1 (hχ0.mul hZ.continuous)
  have e1 : ∫ x, L x * ((α (x 0) - β (x 0)) * Z x) ∂μN n =
      ∫ x, L x * (α (x 0) * Z x) ∂μN n - ∫ x, L x * (β (x 0) * Z x) ∂μN n := by
    rw [← integral_sub iα iβ]; congr 1; funext x; ring
  rw [e1] at hw
  have hsplit : ∫ x, L x * (α (x 0) * Z x) ∂μN n =
      ∫ x, L x * (β (x 0) * Z x) ∂μN n - ∫ x, G x * φ x ∂μN n := by linarith
  -- the near term
  obtain ⟨Cβ, hCβ⟩ := ae_bound_cont (n := n) (hβ.comp (continuous_apply 0))
  have hβi : Integrable (fun x => u x ^ 2 * β (x 0)) (μN n) := by
    have hm : AEStronglyMeasurable (fun x : Cfg n => β (x 0)) (μN n) :=
      (hβ.comp (continuous_apply 0)).aestronglyMeasurable
    have := (int_sq hu.1).bdd_mul hm hCβ
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [mul_comm]
  have hβc : Integrable (fun x : Cfg n => β (x 0)) (μN n) :=
    integrableN (hβ.comp (continuous_apply 0))
  have hβ1' : ∫ x, β (x 0) ∂μN n = 1 := by rw [integral_coord0 hβ, hβ1]
  have hnear : ∫ x, L x * (β (x 0) * Z x) ∂μN n ≤
      1 / (2 * ε ^ 3) * ∫ x, u x ^ 2 * β (x 0) ∂μN n + ε / 2 := by
    have i2 : Integrable (fun x => 1 / (2 * ε ^ 3) * (u x ^ 2 * β (x 0)) + ε / 2 * β (x 0))
        (μN n) := (hβi.const_mul _).add (hβc.const_mul _)
    calc ∫ x, L x * (β (x 0) * Z x) ∂μN n
        ≤ ∫ x, (1 / (2 * ε ^ 3) * (u x ^ 2 * β (x 0)) + ε / 2 * β (x 0)) ∂μN n := by
          refine integral_mono_ae iβ i2 ?_
          filter_upwards [hu0] with x h0
          have hb := hβ0 (x 0)
          have hL0 : 0 ≤ L x := by
            simp only [L]; rw [Lg_of_nonneg h0]
            exact Real.log_nonneg (by have := div_nonneg h0 hε.le; linarith)
          have hL1 : L x ≤ u x / ε := by
            have := abs_Lg_le hε (u x)
            rwa [abs_of_nonneg hL0, abs_of_nonneg h0] at this
          have key : u x ^ 2 / (2 * ε ^ 3) + ε / 2 - u x / ε =
              (u x - ε ^ 2) ^ 2 / (2 * ε ^ 3) := by field_simp; ring
          have hamgm : u x / ε ≤ u x ^ 2 / (2 * ε ^ 3) + ε / 2 := by
            linarith [div_nonneg (sq_nonneg (u x - ε ^ 2)) (by positivity : (0 : ℝ) ≤ 2 * ε ^ 3)]
          have hz0 := hZ0 x
          have hz1 := hZ1 x
          calc L x * (β (x 0) * Z x) ≤ L x * β (x 0) :=
                mul_le_mul_of_nonneg_left (by nlinarith) hL0
            _ ≤ u x / ε * β (x 0) := mul_le_mul_of_nonneg_right hL1 hb
            _ ≤ (u x ^ 2 / (2 * ε ^ 3) + ε / 2) * β (x 0) := mul_le_mul_of_nonneg_right hamgm hb
            _ = _ := by ring
      _ = _ := by
          rw [integral_add (hβi.const_mul _) (hβc.const_mul _), integral_const_mul,
            integral_const_mul, hβ1', mul_one]
  -- the far term
  set A : Cfg n → ℝ := fun x => η x * (dWN 0 u x / (u x + ε))
  have hAm : MemLp A 2 (μN n) := memLp_logA hu hu0 hη hε 0
  have hpt : ∀ᵐ x ∂μN n, |G x * φ x| ≤ |A x| / c := by
    filter_upwards [hu0, ae_cube] with x h0 hx
    by_cases hz : χ (x 0) * Z x = 0
    · simp only [φ, hz, mul_zero, abs_zero]; positivity
    · have hcx := hηc x hx hz
      have h01 : x 0 ∈ Icc (0 : ℝ) 1 := ⟨(hx 0 trivial).1.le, (hx 0 trivial).2.le⟩
      have hχZ : |χ (x 0) * Z x| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (hZ0 x)]
        calc |χ (x 0)| * Z x ≤ 1 * 1 :=
              mul_le_mul (abs_chiAB_le hα hβ hα0 hβ0 hα1 hβ1 h01) (hZ1 x) (hZ0 x) zero_le_one
          _ = 1 := one_mul 1
      have hG : G x = dWN 0 u x / (u x + ε) := by simp only [G, abs_of_nonneg h0]; ring
      rw [abs_mul, hG, le_div_iff₀ hc]
      simp only [A, abs_mul]
      calc |dWN 0 u x / (u x + ε)| * |χ (x 0) * Z x| * c
          ≤ |dWN 0 u x / (u x + ε)| * 1 * |η x| := by gcongr
        _ = |η x| * |dWN 0 u x / (u x + ε)| := by ring
  have hvol : ∫ _x, (1 : ℝ) ∂μN n = 1 := by
    simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ, volume_cube]
  have hfar : -∫ x, G x * φ x ∂μN n ≤ √K / c := by
    have h1 : -∫ x, G x * φ x ∂μN n ≤ ∫ x, |A x| / c ∂μN n := by
      refine (neg_le_abs _).trans ?_
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le ((hAm.integrable one_le_two).abs.div_const c)
        (by filter_upwards [hpt] with x hx; rwa [Real.norm_eq_abs])
    have h2 : ∫ x, |A x| ∂μN n ≤ √K := by
      have hcs := abs_integral_mul_le (f := fun x => |A x|) (g := fun _ => (1 : ℝ)) hAm.abs
        (memLp_const 1)
      simp only [mul_one, one_pow, sq_abs, hvol, Real.sqrt_one] at hcs
      exact (le_abs_self _).trans (hcs.trans (Real.sqrt_le_sqrt hK))
    rw [integral_div] at h1
    exact h1.trans (div_le_div_of_nonneg_right h2 hc.le)
  change ∫ x, L x * (α (x 0) * Z x) ∂μN n ≤ _
  linarith

/-! ### Windows for the other particles -/

/-- `n` points of `[0, 1]`, separated by `s = 1/(n+2)` and at distance `≥ s/6` from `t₀`. -/
lemma exists_grid (t0 : ℝ) : ∃ c : Fin n → ℝ,
    (∀ j, 4 / 3 * (1 / ((n : ℝ) + 2)) ≤ c j ∧ c j ≤ 1 - 4 / 3 * (1 / ((n : ℝ) + 2))) ∧
    (∀ i j, i ≠ j → 1 / ((n : ℝ) + 2) ≤ |c i - c j|) ∧
    (∀ j, 1 / ((n : ℝ) + 2) / 6 ≤ |c j - t0|) := by
  set s := 1 / ((n : ℝ) + 2)
  have hs : 0 < s := by positivity
  have hns : ((n : ℝ) + 2) * s = 1 := by simp only [s]; field_simp
  have hsep : ∀ θ : ℝ, ∀ i j : Fin n, i ≠ j →
      s ≤ |((i : ℝ) + θ) * s - ((j : ℝ) + θ) * s| := fun θ i j hij => by
    rw [show ((i : ℝ) + θ) * s - ((j : ℝ) + θ) * s = ((i : ℝ) - j) * s by ring, abs_mul,
      abs_of_pos hs]
    have : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hne with h | h
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    nlinarith
  have hrange : ∀ θ : ℝ, 4 / 3 ≤ θ → θ ≤ 5 / 3 → ∀ j : Fin n,
      4 / 3 * s ≤ ((j : ℝ) + θ) * s ∧ ((j : ℝ) + θ) * s ≤ 1 - 4 / 3 * s := fun θ h1 h2 j => by
    have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    have hj0 : (0 : ℝ) ≤ j := by positivity
    constructor <;> nlinarith
  by_cases hbad : ∃ j : Fin n, |((j : ℝ) + 4 / 3) * s - t0| < s / 6
  · obtain ⟨j0, hj0⟩ := hbad
    refine ⟨fun j => ((j : ℝ) + 5 / 3) * s, fun j => hrange _ (by norm_num) le_rfl j,
      fun i j hij => hsep _ i j hij, fun j => ?_⟩
    -- `|j - j₀ + 1/3| ≥ 1/3`
    have hk : 1 / 3 ≤ |(j : ℝ) - j0 + 1 / 3| := by
      rcases le_or_gt (j0 : ℕ) j with h | h
      · have : (j0 : ℝ) ≤ j := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
      · have : (j : ℝ) + 1 ≤ j0 := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
    have e : ((j : ℝ) + 5 / 3) * s - t0 =
        ((j : ℝ) - j0 + 1 / 3) * s + (((j0 : ℝ) + 4 / 3) * s - t0) := by ring
    rw [e]
    have h1 : 1 / 3 * s ≤ |((j : ℝ) - j0 + 1 / 3) * s| := by
      rw [abs_mul, abs_of_pos hs]; nlinarith
    have h3 := abs_sub_abs_le_abs_sub (((j : ℝ) - j0 + 1 / 3) * s)
      (-(((j0 : ℝ) + 4 / 3) * s - t0))
    rw [sub_neg_eq_add, abs_neg] at h3
    linarith
  · push Not at hbad
    exact ⟨fun j => ((j : ℝ) + 4 / 3) * s, fun j => hrange _ le_rfl (by norm_num) j,
      fun i j hij => hsep _ i j hij, hbad⟩

/-- `(g(b) - g(a))² ≤ |b - a| ∫ g'²` for `g ∈ H¹(0, 1)`. -/
lemma sq_sub_le_H1N {g : ℝ → ℝ} (hg : H1N g) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : (g b - g a) ^ 2 ≤ |b - a| * kinM g := by
  have key : ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a ≤ b →
      (g b - g a) ^ 2 ≤ (b - a) * kinM g := fun {a b} ha hb hab => by
    have hac : AbsolutelyContinuousOnInterval g a b := hg.1.mono (by
      rw [uIcc01, uIcc_of_le hab]; exact Icc_subset_Icc ha.1 hb.2)
    have hd2 : IntegrableOn (fun t => deriv g t ^ 2) (Ioo (0 : ℝ) 1) := hg.2
    have hii : IntervalIntegrable (fun t => deriv g t ^ 2) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
        (hd2.mono_set (Ioo_subset_Ioo ha.1 hb.2))
    have h1 := sq_le_interval hab hac.intervalIntegrable_deriv hii
    rw [hac.integral_deriv_eq_sub] at h1
    have h2 : ∫ t in a..b, deriv g t ^ 2 ≤ kinM g := by
      rw [kinM, integral_mu1]
      exact intervalIntegral.integral_mono_interval ha.1 hab hb.2
        (ae_of_all _ fun s => by simp only [Pi.zero_apply]; positivity)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hd2)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hab))
  rcases le_total a b with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact key ha hb h
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, ← neg_sub, neg_sq]; exact key hb ha h

lemma DgY_ne_zero_of_inj {x : Cfg n} (h : ∀ i j, i ≠ j → x i ≠ x j) : DgY (n + 1) x ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  by_cases hij : i = j ∨ ¬ SameB (n + 1) i j
  · simp [hij]
  · simp only [hij, ↓reduceIte]
    push Not at hij
    exact sub_ne_zero.2 (h i j hij.1)

lemma memLp_Lg {u : Cfg n → ℝ} (hu : MemLp u 2 (μN n)) {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun x => Lg ε (u x)) 2 (μN n) :=
  hu.of_le_mul (c := 1 / ε) ((continuous_Lg hε).comp_aestronglyMeasurable hu.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc |Lg ε (u x)| ≤ |u x| / ε := abs_Lg_le hε _
        _ = 1 / ε * |u x| := by ring)

/-! ### Positivity -/

/-- **The core of positivity.** A nonnegative symmetric Neumann `u`, nonzero a.e., with the
weighted logarithmic bound for `η = Π_{i≠j}(xᵢ - xⱼ)`, has a density without zeros on `[0, 1]`. -/
theorem rho_pos_core {u : Cfg n → ℝ} (hu : u ∈ DomN .bos n) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    (hne : ∀ᵐ x ∂μN n, u x ≠ 0) {K : ℝ}
    (hK : ∀ ε > 0, ∫ x, (DgY (n + 1) x * (dWN 0 u x / (u x + ε))) ^ 2 ∂μN n ≤ K)
    {t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) 1) (hρ0 : fnE (rhoE .bos u) t0 = 0) : False := by
  -- the density near `t₀`
  set g := gNH .bos u
  have hg : H1N g := h1N_gNH u
  have hgρ := (gNH_spec hu).2.1
  have hfg : ∀ t ∈ Icc (0 : ℝ) 1, fnE (rhoE .bos u) t = g t ^ 2 := fun t ht => by
    rw [rhoE, sqE, fnE_toE _ ht, sq]
  have hg0 : g t0 = 0 := by
    have := hfg t0 ht0
    rw [hρ0] at this
    exact pow_eq_zero_iff two_ne_zero |>.1 this.symm
  set Lc := kinM g
  have hLc : 0 ≤ Lc := integral_nonneg fun _ => sq_nonneg _
  have hgle : ∀ t ∈ Icc (0 : ℝ) 1, g t ^ 2 ≤ |t - t0| * Lc := fun t ht => by
    have := sq_sub_le_H1N hg ht0 ht
    rwa [hg0, sub_zero] at this
  -- parameters
  obtain ⟨c, hcr, hcsep, hct⟩ := exists_grid (n := n) t0
  set s := 1 / ((n : ℝ) + 2) with hsdef
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 / 2 := by
    rw [hsdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set r := s / 24 with hrdef
  set a := s / 48 with hadef
  have hr : 0 < r := by positivity
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 / 96 := by linarith
  -- the far bump `α`
  set m' := if t0 ≤ 1 / 2 then t0 + 3 * a / 2 else t0 - 3 * a / 2 with hm'def
  have hm' : 0 ≤ m' - a / 2 ∧ m' + a / 2 ≤ 1 ∧ t0 - 2 * a ≤ m' - a / 2 ∧
      m' + a / 2 ≤ t0 + 2 * a := by
    rw [hm'def]
    split_ifs with h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [ht0.1, ht0.2]
  have ha2 : 0 < a / 2 := by positivity
  set α := nbump m' (a / 2)
  have hαc : Continuous α := continuous_nbump _ _
  have hα0 : ∀ t, 0 ≤ α t := nbump_nonneg ha2 hm'.1 hm'.2.1
  have hα1 : ∫ t, α t ∂μ1 = 1 := integral_nbump ha2 hm'.1 hm'.2.1
  set κ := 1 / 2 / (∫ s, tentR m' (a / 2) s ∂μ1)
  have hκ : 0 < κ := div_pos (by norm_num) (integral_tentR_pos ha2 hm'.1 hm'.2.1)
  -- the windows `Z`
  set Z : Cfg n → ℝ := fun x => ∏ j : Fin n,
    (⟨r / 2, r, by positivity, by linarith⟩ : ContDiffBump (c j)) (x j.succ) with hZdef
  have hZ : ContDiff ℝ 1 Z := contDiff_prod fun j _ => (ContDiffBump.contDiff _).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j.succ).contDiff
  have hZ0 : ∀ x, 0 ≤ Z x := fun x => Finset.prod_nonneg fun j _ => ContDiffBump.nonneg _
  have hZ1 : ∀ x, Z x ≤ 1 := fun x =>
    Finset.prod_le_one₀ (fun j _ => ContDiffBump.nonneg _) fun j _ => ContDiffBump.le_one _
  have hZc : ∀ x (s' : ℝ), Z (x + s' • (Pi.single 0 1 : Cfg n)) = Z x := fun x s' => by
    simp only [hZdef, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.succ_ne_zero,
      ↓reduceIte, smul_zero, add_zero]
  have hZne : ∀ x, Z x ≠ 0 → ∀ j, dist (x j.succ) (c j) < r := fun x hx j => by
    have hj := (Finset.prod_ne_zero_iff.1 hx) j (Finset.mem_univ j)
    have := (ContDiffBump.support_eq _).le (Function.mem_support.2 hj)
    rwa [Metric.mem_ball] at this
  have hZone : ∀ x, (∀ j, dist (x j.succ) (c j) ≤ r / 2) → Z x = 1 := fun x hx =>
    Finset.prod_eq_one fun j _ => ContDiffBump.one_of_mem_closedBall _
      (Metric.mem_closedBall.2 (hx j))
  -- the compact set where `η` is bounded below
  set Cs : Set (Cfg n) := univ.pi (Fin.cons (Icc (t0 - 2 * a) (t0 + 2 * a))
    fun j => Icc (c j - r) (c j + r) : Fin (n + 1) → Set ℝ) with hCsdef
  have hCsc : IsCompact Cs := isCompact_univ_pi fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact isCompact_Icc
    · simp only [Fin.cons_succ]; exact isCompact_Icc
  have hmemCs : ∀ x, x ∈ Cs ↔ x 0 ∈ Icc (t0 - 2 * a) (t0 + 2 * a) ∧
      ∀ j : Fin n, x j.succ ∈ Icc (c j - r) (c j + r) := fun x => by
    rw [hCsdef, Set.mem_univ_pi, Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hct' : ∀ j, 8 * a ≤ |c j - t0| := fun j => by
    have := hct j; rw [hadef]; linarith
  have hcsep' : ∀ i j, i ≠ j → 48 * a ≤ |c i - c j| := fun i j hij => by
    have := hcsep i j hij; rw [hadef]; linarith
  have hrA : r = 2 * a := by rw [hrdef, hadef]; ring
  have hinj : ∀ x ∈ Cs, ∀ i j, i ≠ j → x i ≠ x j := by
    intro x hx
    rw [hmemCs] at hx
    have key0 : ∀ j : Fin n, x 0 ≠ x j.succ := fun j h => by
      have h1 := hx.1
      have h2 := hx.2 j
      rw [h] at h1
      rcases le_abs'.1 (hct' j) with h3 | h3 <;>
        linarith [h1.1, h1.2, h2.1, h2.2]
    have keyS : ∀ i j : Fin n, i ≠ j → x i.succ ≠ x j.succ := fun i j hij h => by
      have h1 := hx.2 i
      have h2 := hx.2 j
      rw [h] at h1
      rcases le_abs'.1 (hcsep' i j hij) with h3 | h3 <;>
        linarith [h1.1, h1.2, h2.1, h2.2]
    intro i j hij
    refine Fin.cases (fun hij => ?_) (fun i' hij => ?_) i hij
    · refine Fin.cases (fun h => absurd rfl h) (fun j' _ => key0 j') j hij
    · refine Fin.cases (fun _ => (key0 i').symm) (fun j' h => keyS i' j' fun e => h ?_) j hij
      rw [e]
  have hCsne : (Fin.cons t0 c : Cfg n) ∈ Cs := by
    rw [hmemCs]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨⟨by linarith, by linarith⟩, fun j => ⟨by linarith, by linarith⟩⟩
  obtain ⟨xm, hxm, hmin⟩ := hCsc.exists_isMinOn ⟨_, hCsne⟩
    (continuous_abs.comp (contDiff_DgY (n := n) (a := n + 1)).continuous).continuousOn
  set cη := |DgY (n + 1) xm|
  have hcη : 0 < cη := abs_pos.2 (DgY_ne_zero_of_inj (hinj xm hxm))
  -- the lower box
  set lb : Fin (n + 1) → ℝ := Fin.cons (m' - a / 4) fun j => c j - r / 2
  set ub : Fin (n + 1) → ℝ := Fin.cons (m' + a / 4) fun j => c j + r / 2
  set Bx : Set (Cfg n) := Set.pi univ fun i => Ioo (lb i) (ub i)
  have hlb : ∀ i, 0 ≤ lb i := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [lb, Fin.cons_zero]; linarith [hm'.1]
    · simp only [lb, Fin.cons_succ]; linarith [(hcr j).1]
  have hlu : ∀ i, lb i < ub i := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [lb, ub, Fin.cons_zero]; linarith
    · simp only [lb, ub, Fin.cons_succ]; linarith
  have hub : ∀ i, ub i ≤ 1 := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ub, Fin.cons_zero]; linarith [hm'.2.1]
    · simp only [ub, Fin.cons_succ]; linarith [(hcr j).2]
  have hBx : 0 < μN n Bx := pos_measure_pi hlb hlu hub
  have hBxm : MeasurableSet Bx := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hBxprop : ∀ x ∈ Bx, κ ≤ α (x 0) ∧ Z x = 1 := fun x hx => by
    have h0 := hx 0 trivial
    simp only [lb, ub, Fin.cons_zero] at h0
    refine ⟨nbump_ge ha2 hm'.1 hm'.2.1 (abs_le.2 ⟨by linarith [h0.1], by linarith [h0.2]⟩),
      hZone x fun j => ?_⟩
    have hj := hx j.succ trivial
    simp only [lb, ub, Fin.cons_succ] at hj
    rw [Real.dist_eq, abs_le]; constructor <;> linarith [hj.1, hj.2]
  -- `u > δ₀` on a part of the box of positive measure
  have hum := hu.1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  obtain ⟨δ₀, hδ₀, hB0⟩ : ∃ δ₀ > 0, 0 < μN n (Bx ∩ {x | δ₀ < u' x}) := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ k : ℕ, μN n (Bx ∩ {x | 1 / ((k : ℝ) + 1) < u' x}) = 0 := fun k =>
      nonpos_iff_eq_zero.1 (hcon _ (by positivity))
    have hpos : ∀ᵐ x ∂μN n, 0 < u' x := by
      filter_upwards [hu0, hne, hue] with x h1 h2 h3
      rw [← h3]; exact lt_of_le_of_ne h1 (Ne.symm h2)
    have hnull : μN n {x | ¬ 0 < u' x} = 0 := ae_iff.1 hpos
    have hsub : Bx ⊆ (⋃ k : ℕ, Bx ∩ {x | 1 / ((k : ℝ) + 1) < u' x}) ∪ {x | ¬ 0 < u' x} :=
      fun x hx => by
        by_cases h : 0 < u' x
        · obtain ⟨k, hk⟩ := exists_nat_one_div_lt h
          exact Or.inl (Set.mem_iUnion.2 ⟨k, hx, hk⟩)
        · exact Or.inr h
    have := measure_mono_null hsub (measure_union_null (measure_iUnion_null hz) hnull)
    exact hBx.ne' this
  set B0 := Bx ∩ {x | δ₀ < u' x}
  have hB0m : MeasurableSet B0 := hBxm.inter (measurableSet_lt measurable_const hu'm)
  set mB := (μN n).real B0
  have hmB : 0 < mB := ENNReal.toReal_pos hB0.ne' (measure_ne_top _ _)
  -- the upper bound, uniformly in `ε ∈ (0, 1]`
  set C1 := Lc + 1 + √K / cη
  have hupper : ∀ ε, 0 < ε → ε ≤ 1 →
      ∫ x, Lg ε (u x) * (α (x 0) * Z x) ∂μN n ≤ C1 := by
    intro ε hε hε1
    set δ := a * ε ^ 4
    have hδ : 0 < δ := by positivity
    have hδa : δ ≤ a := by
      have : ε ^ 4 ≤ 1 := pow_le_one₀ hε.le hε1
      nlinarith
    set m := max (δ / 2) (min (1 - δ / 2) t0)
    have hm1 : 0 ≤ m - δ / 2 := by linarith [le_max_left (δ / 2) (min (1 - δ / 2) t0)]
    have hm2 : m + δ / 2 ≤ 1 := by
      have : m ≤ 1 - δ / 2 := max_le (by linarith) (min_le_left _ _)
      linarith
    have hm3 : |m - t0| ≤ δ / 2 := by
      have h1 : m ≤ t0 + δ / 2 :=
        max_le (by linarith [ht0.1]) ((min_le_right _ _).trans (by linarith))
      have h2 : t0 - δ / 2 ≤ m :=
        (le_min (by linarith [ht0.2]) (by linarith)).trans (le_max_right _ _)
      rw [abs_le]; constructor <;> linarith
    have hδ2 : 0 < δ / 2 := by positivity
    set β := nbump m (δ / 2)
    have hβc : Continuous β := continuous_nbump _ _
    have hβ0 : ∀ t, 0 ≤ β t := nbump_nonneg hδ2 hm1 hm2
    have hβ1 : ∫ t, β t ∂μ1 = 1 := integral_nbump hδ2 hm1 hm2
    -- the supports
    rw [abs_le] at hm3
    have hlo : ∀ t, t ≤ t0 - 2 * a → α t = 0 ∧ β t = 0 := by
      intro t ht
      constructor
      · refine nbump_eq_zero ha2 ?_
        rw [abs_sub_comm, abs_of_pos (by linarith [hm'.2.2.1])]
        linarith [hm'.2.2.1]
      · refine nbump_eq_zero hδ2 ?_
        rw [abs_sub_comm, abs_of_pos (by linarith [hm3.1])]
        linarith [hm3.1]
    have hhi : ∀ t, t0 + 2 * a ≤ t → α t = 0 ∧ β t = 0 := by
      intro t ht
      constructor
      · refine nbump_eq_zero ha2 ?_
        rw [abs_of_pos (by linarith [hm'.2.2.2])]
        linarith [hm'.2.2.2]
      · refine nbump_eq_zero hδ2 ?_
        rw [abs_of_pos (by linarith [hm3.2])]
        linarith [hm3.2]
    have hηc : ∀ x ∈ Cube n, chiAB α β (x 0) * Z x ≠ 0 → cη ≤ |DgY (n + 1) x| := by
      intro x hx hne'
      have h01 : x 0 ∈ Icc (0 : ℝ) 1 := ⟨(hx 0 trivial).1.le, (hx 0 trivial).2.le⟩
      have hχ : chiAB α β (x 0) ≠ 0 := left_ne_zero_of_mul hne'
      have hZx : Z x ≠ 0 := right_ne_zero_of_mul hne'
      have hin : t0 - 2 * a < x 0 ∧ x 0 < t0 + 2 * a := by
        by_contra hc
        rw [not_and_or, not_lt, not_lt] at hc
        exact hχ (chiAB_eq_zero_of hαc hβc hα1 hβ1 hlo hhi h01 hc)
      have hxC : x ∈ Cs := by
        rw [hmemCs]
        refine ⟨⟨hin.1.le, hin.2.le⟩, fun j => ?_⟩
        have := hZne x hZx j
        rw [Real.dist_eq, abs_lt] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      exact hmin hxC
    have hmain := log_wall_ineq hu hu0 contDiff_DgY hε (hK ε hε) hαc hβc hα0 hβ0 hα1 hβ1 hZ hZ0
      hZ1 hZc hcη hηc
    -- the near term: `∫ u² β(x₀) ≤ δ Lc / N`
    obtain ⟨Cβ, hCβ⟩ := ae_bound_cont (n := n) (hβc.comp (continuous_apply 0))
    have hβi : Integrable (fun x => u x ^ 2 * β (x 0)) (μN n) := by
      have hm : AEStronglyMeasurable (fun x : Cfg n => β (x 0)) (μN n) :=
        (hβc.comp (continuous_apply 0)).aestronglyMeasurable
      refine ((int_sq hu.1).bdd_mul hm hCβ).congr (ae_of_all _ fun x => ?_)
      simp only [mul_comm]
    have hI := integral_tentR_pos hδ2 hm1 hm2
    have hρi : Integrable (fun t => β t * rhoN u t) μ1 := by
      have hb : ∀ᵐ t ∂μ1, ‖β t‖ ≤ 1 / ∫ s, tentR m (δ / 2) s ∂μ1 := ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hβ0 t)]
        exact div_le_div_of_nonneg_right (tentR_le_one hδ2 t) hI.le
      exact ((integrable_marg hu.1).const_mul ((n : ℝ) + 1)).bdd_mul hβc.aestronglyMeasurable hb
    have he : ∫ x, u x ^ 2 * β (x 0) ∂μN n = (∫ t, β t * rhoN u t ∂μ1) / ((n : ℝ) + 1) := by
      rw [integral_cube_cons' hβi, ← integral_div]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      simp only [Fin.cons_zero, rhoN, marg]
      rw [integral_mul_const]
      field_simp
    have hb : ∫ t, β t * rhoN u t ∂μ1 ≤ δ * Lc := by
      calc ∫ t, β t * rhoN u t ∂μ1 ≤ ∫ t, β t * (δ * Lc) ∂μ1 := by
            refine integral_mono_ae hρi ((integrable_cont_mu1 hβc).mul_const _) ?_
            filter_upwards [hgρ, ae_restrict_mem measurableSet_Ioo] with t h1 ht
            rw [← h1]
            by_cases hβt : β t = 0
            · simp [hβt]
            · refine mul_le_mul_of_nonneg_left ?_ (hβ0 t)
              have hd : |t - m| < δ / 2 := by
                by_contra hc
                push Not at hc
                exact hβt (nbump_eq_zero hδ2 hc)
              have htt : |t - t0| ≤ δ := by
                have := abs_sub_le t m t0
                have hm3' : |m - t0| ≤ δ / 2 := abs_le.2 hm3
                linarith
              calc g t ^ 2 ≤ |t - t0| * Lc := hgle t (Ioo_subset_Icc_self ht)
                _ ≤ δ * Lc := mul_le_mul_of_nonneg_right htt hLc
        _ = δ * Lc := by rw [integral_mul_const, hβ1, one_mul]
    have hX0 : 0 ≤ ∫ t, β t * rhoN u t ∂μ1 :=
      integral_nonneg fun t => mul_nonneg (hβ0 t) (mul_nonneg (by positivity) (marg_nonneg t))
    have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith only [this]
    have hnear : 1 / (2 * ε ^ 3) * ∫ x, u x ^ 2 * β (x 0) ∂μN n ≤ Lc := by
      rw [he]
      have haε : a * ε ≤ 1 := by
        calc a * ε ≤ 1 * 1 := mul_le_mul (by linarith only [ha1]) hε1 hε.le zero_le_one
          _ = 1 := one_mul 1
      calc 1 / (2 * ε ^ 3) * ((∫ t, β t * rhoN u t ∂μ1) / ((n : ℝ) + 1))
          ≤ 1 / (2 * ε ^ 3) * (δ * Lc) :=
            mul_le_mul_of_nonneg_left ((div_le_self hX0 hN).trans hb) (by positivity)
        _ = a * ε * Lc / 2 := by simp only [δ]; field_simp
        _ ≤ Lc := by
            have := mul_le_mul_of_nonneg_right haε hLc
            linarith only [this, hLc]
    have hcη0 : 0 ≤ √K / cη := div_nonneg (Real.sqrt_nonneg _) hcη.le
    simp only [C1]
    linarith only [hmain, hnear, hε1]
  -- the lower bound
  have hlower : ∀ ε, 0 < ε →
      mB * (κ * Real.log (1 + δ₀ / ε)) ≤ ∫ x, Lg ε (u x) * (α (x 0) * Z x) ∂μN n := by
    intro ε hε
    have hLm := memLp_Lg hu.1 hε
    have hi := int_mul_cont hLm ((hαc.comp (continuous_apply 0)).mul hZ.continuous)
    calc mB * (κ * Real.log (1 + δ₀ / ε)) =
          ∫ x, B0.indicator (fun _ => κ * Real.log (1 + δ₀ / ε)) x ∂μN n := by
          rw [integral_indicator_const _ hB0m, smul_eq_mul]
      _ ≤ _ := by
          refine integral_mono_ae ((integrable_const _).indicator hB0m) hi ?_
          filter_upwards [hu0, hue] with x h0 he'
          have hL0 : 0 ≤ Lg ε (u x) := by
            rw [Lg_of_nonneg h0]
            exact Real.log_nonneg (by have := div_nonneg h0 hε.le; linarith)
          by_cases hx : x ∈ B0
          · rw [indicator_of_mem hx]
            obtain ⟨hκx, hZx⟩ := hBxprop x hx.1
            have hux : δ₀ < u x := by rw [he']; exact hx.2
            have hlog : Real.log (1 + δ₀ / ε) ≤ Lg ε (u x) := by
              rw [Lg_of_nonneg h0]
              exact Real.log_le_log (by positivity)
                (by have := div_le_div_of_nonneg_right hux.le hε.le; linarith)
            rw [hZx, mul_one]
            calc κ * Real.log (1 + δ₀ / ε) = Real.log (1 + δ₀ / ε) * κ := mul_comm _ _
              _ ≤ Lg ε (u x) * α (x 0) := mul_le_mul hlog hκx hκ.le hL0
          · rw [indicator_of_notMem hx]
            exact mul_nonneg hL0 (mul_nonneg (hα0 _) (hZ0 x))
  -- the contradiction
  set T := C1 / (mB * κ) + 1
  have hmBκ : 0 < mB * κ := mul_pos hmB hκ
  set ε := δ₀ / (Real.exp T + δ₀)
  have hεpos : 0 < ε := div_pos hδ₀ (by positivity)
  have hε1 : ε ≤ 1 := (div_le_one (by positivity)).2 (by linarith [Real.exp_pos T])
  have hlogT : T ≤ Real.log (1 + δ₀ / ε) := by
    have e : δ₀ / ε = Real.exp T + δ₀ := by
      simp only [ε]; field_simp
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos T) (by rw [e]; linarith only [hδ₀])
  have h1 := hlower ε hεpos
  have h2 := hupper ε hεpos hε1
  have h3 : mB * (κ * T) ≤ mB * (κ * Real.log (1 + δ₀ / ε)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogT hκ.le) hmB.le
  have h4 : mB * (κ * T) = C1 + mB * κ := by
    simp only [T]; field_simp
  linarith only [h1, h2, h3, h4, hmBκ]

/-! ### Ground states -/

lemma DgY_props : ContDiff ℝ 1 (DgY (n := n) (n + 1)) ∧
    (∀ σ (x : Cfg n), DgY (n + 1) (pm σ x) = DgY (n + 1) x) ∧
    (∀ᵐ x ∂μN n, |DgY (n + 1) x| ≤ 1) ∧
    (∀ (x : Cfg n) (i j : Fin (n + 1)), i ≠ j → x i = x j → DgY (n + 1) x = 0) :=
  ⟨contDiff_DgY, fun σ x => DgY_pm (YG_all σ) x,
    by filter_upwards [ae_cube] with x hx using abs_DgY_le hx,
    fun x _ _ hij h => DgY_diag x hij h⟩

lemma fnE_rhoE_nonneg {τ : Stat} (Ψ : Cfg n → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ fnE (rhoE τ Ψ) t := by
  rw [rhoE, sqE, fnE_toE _ ht]; exact mul_self_nonneg _

/-- **Bosonic Neumann ground-state densities are positive on `[0, 1]`.** -/
theorem rhoE_pos_bos {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH .bos w v Ψ) {t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    0 < fnE (rhoE .bos Ψ) t0 := by
  set u : Cfg n → ℝ := fun x => |Ψ x|
  have hu : IsGSNH .bos w v u := isGSNH_abs hΨ
  have hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x := ae_of_all _ fun x => abs_nonneg _
  obtain ⟨hη, hηs, hη1, -⟩ := DgY_props (n := n)
  obtain ⟨K, -, hK⟩ := log_estimate_gen (v := v) hw hu.1 hu0 hη hηs hη1 (QNH .bos w v u)
    fun ε hε => ⟨rhoE2 .bos u (logTest (DgY (n + 1)) u ε),
      fun u' => int_rhoE2 hu.1 (logTest_memN hu.1 hη hηs hε) u',
      euler_lagrangeNH hw hu (logTest_memN hu.1 hη hηs hε)⟩
  have hK0 : ∀ ε > 0, ∫ x, (DgY (n + 1) x * (dWN 0 u x / (u x + ε))) ^ 2 ∂μN n ≤ K :=
    fun ε hε => (Finset.single_le_sum
      (f := fun k => ∫ x, (DgY (n + 1) x * (dWN k u x / (u x + ε))) ^ 2 ∂μN n)
      (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ 0)).trans (hK ε hε)
  have hne : ∀ᵐ x ∂μN n, u x ≠ 0 := by
    filter_upwards [gsNH_ne_zero_bos hw hΨ] with x hx using abs_ne_zero.2 hx
  refine lt_of_le_of_ne (fnE_rhoE_nonneg Ψ ht0) fun h => ?_
  rw [← rhoE_abs hΨ.1] at h
  exact rho_pos_core hu.1 hu0 hne hK0 ht0 h.symm

/-- **Fermionic Neumann ground-state densities are positive on `[0, 1]`.** -/
theorem rhoE_pos_fer {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH .fer w v Ψ) {t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    0 < fnE (rhoE .fer Ψ) t0 := by
  set u := PhiBY (n + 1) Ψ
  have hu : u ∈ DomN .bos n := PhiBY_memN hΨ.1
  have hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x := ae_of_all _ (PhiBY_nonneg Ψ)
  obtain ⟨hη, hηs, hη1, hpl⟩ := DgY_props (n := n)
  obtain ⟨K, -, hK⟩ := log_estimate_ferη hw hΨ hη hηs hη1 hpl
  have hK0 : ∀ ε > 0, ∫ x, (DgY (n + 1) x * (dWN 0 u x / (u x + ε))) ^ 2 ∂μN n ≤ K :=
    fun ε hε => (Finset.single_le_sum
      (f := fun k => ∫ x, (DgY (n + 1) x * (dWN k u x / (u x + ε))) ^ 2 ∂μN n)
      (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ 0)).trans (hK ε hε)
  have hne : ∀ᵐ x ∂μN n, u x ≠ 0 := by
    filter_upwards [gsNH_ne_zero_fer hw hΨ, PhiBY_ae_eq_absN hΨ.1] with x hx h2
    change PhiBY (n + 1) Ψ x ≠ 0
    rw [h2]; exact abs_ne_zero.2 hx
  have hρ : rhoE .bos u = rhoE .fer Ψ := eq_of_int fun u' => by
    rw [int_rhoE hu, int_rhoE hΨ.1]
    refine integral_congr_ae ?_
    filter_upwards [PhiBY_ae_eq_absN hΨ.1] with x hx
    simp only [u] at hx ⊢
    rw [hx, abs_mul_abs_self]
  refine lt_of_le_of_ne (fnE_rhoE_nonneg Ψ ht0) fun h => ?_
  rw [← hρ] at h
  exact rho_pos_core hu hu0 hne hK0 ht0 h.symm

/-- **Neumann ground-state densities of `H⁻¹` potentials are positive on `[0, 1]`**, walls
included, for bosons or fermions and any continuous interaction. -/
theorem rhoE_pos {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) {t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) 1) : 0 < fnE (rhoE τ Ψ) t0 := by
  cases τ with
  | bos => exact rhoE_pos_bos hw hΨ ht0
  | fer => exact rhoE_pos_fer hw hΨ ht0

/-- The density has mass `N ∫ Ψ²`. -/
theorem integral_fnE_rhoE {τ : Stat} {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN τ n) :
    ∫ t, fnE (rhoE τ Ψ) t ∂μ1 = (n + 1) * ∫ x, Ψ x ^ 2 ∂μN n := by
  rw [← integral_gNH_sq hΨ]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [rhoE, sqE, fnE_toE _ (Ioo_subset_Icc_self ht), sq]

/-- `ρ ∈ H¹(0, 1)` is the density of a normalised Neumann ground state of an `H⁻¹` potential. -/
def VRepNH (τ : Stat) (n : ℕ) (w : Cfg n → ℝ) (ρ : H1E) : Prop :=
  ∃ (v : PotH) (Ψ : Cfg n → ℝ), IsGSNH τ w v Ψ ∧ rhoE τ Ψ = ρ

/-- **Necessity in Corso's Theorem 2.3**: a `v`-representable density (Neumann walls, `H⁻¹`
potentials, continuous interaction, bosons or fermions) is an `H¹(0, 1)` function, positive on
`[0, 1]`, with mass `N`. -/
theorem vrepNH_nec {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) {ρ : H1E}
    (h : VRepNH τ n w ρ) :
    (∀ t ∈ Icc (0 : ℝ) 1, 0 < fnE ρ t) ∧ ∫ t, fnE ρ t ∂μ1 = n + 1 := by
  obtain ⟨v, Ψ, hΨ, rfl⟩ := h
  refine ⟨fun t ht => rhoE_pos hw hΨ ht, ?_⟩
  rw [integral_fnE_rhoE hΨ.1, hΨ.2.1, mul_one]

end DFT.Continuum.Line
