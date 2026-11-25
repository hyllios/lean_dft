/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePos

/-!
# A plateau density: two δ-functions

The trapezoid `g = min(3t, 1, 3(1 - t))` rises linearly, has a plateau on `[⅓, ⅔]` and falls
linearly. It solves `-g'' + ν g = 0` weakly for `ν = -3δ_{1/3} - 3δ_{2/3}`, and it is positive on
`(0, 1)`, so (`isGSM_of_pos_weak`) it is the ground state of `-d²/dt² - 3δ_{1/3} - 3δ_{2/3}`,
with energy `0`. Its square has kinks at `⅓` and `⅔`.

* `trapG`, `h10_trapG`, `trapG_pos`, `deriv_trapG_*`.
* `integral_dtrap`: `∫ g'φ' = 3φ(⅓) + 3φ(⅔)` for `φ ∈ H¹₀`.
* **`trap_isGSM`**: `g` is a ground state of `-d² - 3δ_{1/3} - 3δ_{2/3}`; `IsGSM.const_mul`.
* **`trap_vrepM`**: the normalised plateau density is `v`-representable with a measure potential;
  **`trap_nrep_not_vrep`**: for any `N`, the plateau density is `N`-representable but not
  (ensemble) `v`-representable with continuous potentials.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

/-- The trapezoid `min(3t, 1, 3(1 - t))`. -/
noncomputable def trapG (t : ℝ) : ℝ := min (3 * t) (min 1 (3 * (1 - t)))

lemma trapG_left {t : ℝ} (h : t ≤ 1 / 3) : trapG t = 3 * t :=
  min_eq_left (le_min (by linarith) (by linarith))

lemma trapG_mid {t : ℝ} (h1 : 1 / 3 ≤ t) (h2 : t ≤ 2 / 3) : trapG t = 1 := by
  rw [trapG, min_eq_left (by linarith : (1 : ℝ) ≤ 3 * (1 - t)), min_eq_right (by linarith)]

lemma trapG_right {t : ℝ} (h : 2 / 3 ≤ t) : trapG t = 3 * (1 - t) := by
  rw [trapG, min_eq_right (by linarith : 3 * (1 - t) ≤ 1), min_eq_right (by linarith)]

lemma lipschitz_trapG : LipschitzWith 3 trapG := by
  have h1 : LipschitzWith 3 fun t : ℝ => 3 * t := LipschitzWith.of_dist_le_mul fun x y => by
    simp [Real.dist_eq, ← mul_sub, abs_mul]
  have h2 : LipschitzWith 3 fun t : ℝ => 3 * (1 - t) := LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, Real.dist_eq, show 3 * (1 - x) - 3 * (1 - y) = 3 * (y - x) by ring, abs_mul,
      abs_sub_comm]
    simp
  have h := h1.min (h2.const_min 1)
  rw [max_self] at h
  exact h

lemma trapG_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < trapG t :=
  lt_min (by linarith [ht.1]) (lt_min one_pos (by linarith [ht.2]))

lemma trapG_le_one (t : ℝ) : trapG t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)

lemma h10_trapG : H10 trapG := by
  refine ⟨(lipschitz_trapG.lipschitzOnWith).absolutelyContinuousOnInterval, ?_, ?_, ?_⟩
  · rw [trapG_left (by norm_num)]; ring
  · rw [trapG_right (by norm_num)]; ring
  · refine Integrable.of_bound ((measurable_deriv trapG).pow_const 2).aestronglyMeasurable
      ((3 : ℝ) ^ 2) (ae_of_all _ fun t => ?_)
    have hd : ‖deriv trapG t‖ ≤ 3 := by
      simpa using norm_deriv_le_of_lipschitz lipschitz_trapG (x₀ := t)
    rw [Real.norm_eq_abs] at hd
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2

lemma deriv_trapG_left {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 3)) : deriv trapG t = 3 := by
  have hev : trapG =ᶠ[𝓝 t] fun s => 3 * s := by
    filter_upwards [Iio_mem_nhds ht.2] with s hs using trapG_left (le_of_lt hs)
  rw [hev.deriv_eq]
  simp

lemma deriv_trapG_mid {t : ℝ} (ht : t ∈ Ioo (1 / 3 : ℝ) (2 / 3)) : deriv trapG t = 0 := by
  have hev : trapG =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using trapG_mid hs.1.le hs.2.le
  rw [hev.deriv_eq]; simp

lemma deriv_trapG_right {t : ℝ} (ht : t ∈ Ioo (2 / 3 : ℝ) 1) : deriv trapG t = -3 := by
  have hev : trapG =ᶠ[𝓝 t] fun s => 3 * (1 - s) := by
    filter_upwards [Ioi_mem_nhds ht.1] with s hs using trapG_right (le_of_lt hs)
  rw [hev.deriv_eq]
  have := (((hasDerivAt_id t).const_sub 1).const_mul (3 : ℝ)).deriv
  simp only [id] at this
  rw [this]; ring

/-! ### The weak equation -/

lemma ae_ne_pt (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]; simp

/-- `∫_a^b g'φ' = k (φ(b) - φ(a))` when `g' = k` on `(a, b) ⊆ (0, 1)`. -/
lemma integral_piece {φ : ℝ → ℝ} (hφ : H10 φ) {a b k : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hd : ∀ t ∈ Ioo a b, deriv trapG t = k) :
    ∫ t in a..b, deriv trapG t * deriv φ t = k * (φ b - φ a) := by
  have hac : AbsolutelyContinuousOnInterval φ a b := hφ.1.mono (by
    rw [uIcc01, uIcc_of_le hab]; exact Icc_subset_Icc ha hb)
  rw [← hac.integral_deriv_eq_sub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_pt b] with t htb ht
  rw [uIoc_of_le hab] at ht
  rw [hd t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩]

/-- **`∫ g'φ' = 3φ(⅓) + 3φ(⅔)`** for `φ ∈ H¹₀`. -/
theorem integral_dtrap {φ : ℝ → ℝ} (hφ : H10 φ) :
    ∫ t, deriv trapG t * deriv φ t ∂μ1 = 3 * φ (1 / 3) + 3 * φ (2 / 3) := by
  have hi : IntervalIntegrable (fun t => deriv trapG t * deriv φ t) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 (integrable_dd h10_trapG hφ)
  have hii : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => deriv trapG t * deriv φ t) volume a b := fun ha hab hb =>
    hi.mono_set (by rw [uIcc01, uIcc_of_le hab]; exact Icc_subset_Icc ha hb)
  rw [integral_mu1, ← intervalIntegral.integral_add_adjacent_intervals
      (hii le_rfl (by norm_num) (by norm_num) : IntervalIntegrable _ _ 0 (1 / 3))
      (hii (by norm_num) (by norm_num) le_rfl : IntervalIntegrable _ _ (1 / 3) 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hii (by norm_num) (by norm_num) (by norm_num) : IntervalIntegrable _ _ (1 / 3) (2 / 3))
      (hii (by norm_num) (by norm_num) le_rfl : IntervalIntegrable _ _ (2 / 3) 1),
    integral_piece hφ le_rfl (by norm_num) (by norm_num) fun t ht => deriv_trapG_left ht,
    integral_piece hφ (by norm_num) (by norm_num) (by norm_num) fun t ht => deriv_trapG_mid ht,
    integral_piece hφ (by norm_num) (by norm_num) le_rfl fun t ht => deriv_trapG_right ht,
    hφ.2.1, hφ.2.2.1]
  ring

/-- The potential `-3δ_{1/3} - 3δ_{2/3}`. -/
noncomputable def nuTrap : PotM :=
  -3 • deltaM ⟨1 / 3, by norm_num, by norm_num⟩ - 3 • deltaM ⟨2 / 3, by norm_num, by norm_num⟩

/-- **The trapezoid is a ground state of `-d²/dt² - 3δ_{1/3} - 3δ_{2/3}`**, with energy `0`. -/
theorem trap_isGSM : IsGSM nuTrap trapG ∧ EM nuTrap = 0 := by
  have hw : ∀ φ (hφ : H10 φ), ∫ t, deriv trapG t * deriv φ t ∂μ1 + nuTrap (mulP h10_trapG hφ) =
      0 * ∫ t, trapG t * φ t ∂μ1 := fun φ hφ => by
    rw [integral_dtrap hφ, zero_mul]
    simp only [nuTrap, sub_apply, smul_apply, deltaM, ContinuousMap.evalCLM_apply, mulP_apply]
    rw [trapG_left (by norm_num), trapG_mid (by norm_num) (by norm_num)]
    ring
  obtain ⟨h1, h2⟩ := isGSM_of_pos_weak h10_trapG (fun t ht => trapG_pos ht) hw
  exact ⟨h1, h2.symm⟩

/-! ### Scaling and the normalised density -/

lemma IsGSM.const_mul {ν : PotM} {ψ : ℝ → ℝ} (h : IsGSM ν ψ) {c : ℝ} (hc : c ≠ 0) :
    IsGSM ν fun t => c * ψ t := by
  obtain ⟨hψ, hpos, hmin⟩ := h
  refine ⟨hψ.const_mul c, by rw [norm2_smul]; positivity, fun φ hφ => ?_⟩
  rw [QM_smul ν hψ c, norm2_smul]
  have := hmin φ hφ
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  calc c ^ 2 * QM ν hψ * ∫ t, φ t ^ 2 ∂μ1 = c ^ 2 * (QM ν hψ * ∫ t, φ t ^ 2 ∂μ1) := by ring
    _ ≤ c ^ 2 * (QM ν hφ * ∫ t, ψ t ^ 2 ∂μ1) := mul_le_mul_of_nonneg_left this hc2
    _ = QM ν hφ * (c ^ 2 * ∫ t, ψ t ^ 2 ∂μ1) := by ring

lemma integral_trapG_sq_pos : 0 < ∫ t, trapG t ^ 2 ∂μ1 :=
  integral_sq_pos h10_trapG fun _ ht => trapG_pos ht

lemma integral_trapG_sq_le : ∫ t, trapG t ^ 2 ∂μ1 ≤ 1 := by
  calc ∫ t, trapG t ^ 2 ∂μ1 ≤ ∫ _t, (1 : ℝ) ∂μ1 := by
        refine integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) (integrable_const _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have h0 := (trapG_pos ht).le
        have h1 := trapG_le_one t
        nlinarith
    _ = 1 := by simp

/-- `c` with `∫ (c trapG)² = N`. -/
noncomputable def cTrap (n : ℕ) : ℝ := √((n + 1) / ∫ t, trapG t ^ 2 ∂μ1)

lemma cTrap_sq (n : ℕ) : cTrap n ^ 2 = (n + 1) / ∫ t, trapG t ^ 2 ∂μ1 :=
  Real.sq_sqrt (by have := integral_trapG_sq_pos; positivity)

lemma cTrap_ne (n : ℕ) : cTrap n ≠ 0 := by
  intro h
  have := cTrap_sq n
  rw [h] at this
  have hI := integral_trapG_sq_pos
  have : (0 : ℝ) < (n + 1) / ∫ t, trapG t ^ 2 ∂μ1 := by positivity
  linarith

/-- The normalised plateau density for one particle. -/
noncomputable def trapP : Pot := sqP (h10_trapG.const_mul (cTrap 0))

/-- **The plateau density is `v`-representable with a measure potential**
(`-3δ_{1/3} - 3δ_{2/3}`). -/
theorem trap_vrepM : VRepM trapP := by
  refine ⟨nuTrap, _, trap_isGSM.1.const_mul (cTrap_ne 0), ?_, fun _ => rfl⟩
  rw [norm2_smul, cTrap_sq, div_mul_cancel₀ _ integral_trapG_sq_pos.ne']
  norm_num

/-! ### Not `v`-representable with continuous potentials -/

/-- The plateau density `ρ = (c trapG)²` for `N = n + 1` particles. -/
noncomputable def rhoTrap (n : ℕ) (v : Pot) : ℝ := ∫ t, ext v t * (cTrap n * trapG t) ^ 2 ∂μ1

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-- **The plateau density is `N`-representable but not `v`-representable** with continuous
potentials, for any number of bosons or fermions. -/
theorem trap_nrep_not_vrep (hws : ∀ σ x, w (pm σ x) = w x) :
    (∃ ψ ∈ Nst (settingW τ n w hw), dens (settingW τ n w hw) ψ = rhoTrap n) ∧
      ¬ EnsVRep (settingW τ n w hw) (rhoTrap n) := by
  have hI := integral_trapG_sq_pos
  have hI1 := integral_trapG_sq_le
  have hc1 : 1 ≤ cTrap n ^ 2 := by
    rw [cTrap_sq, le_div_iff₀ hI]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  refine ⟨(lieb_characterisation (rhoTrap n)).2 ⟨fun t => cTrap n * trapG t,
    h10_trapG.const_mul _, ?_, rfl⟩, ?_⟩
  · rw [norm2_smul, cTrap_sq, div_mul_cancel₀ _ hI.ne']
  · intro h
    obtain ⟨v, ψ, hψ, -, hd⟩ := (ensVRep_iff_W_cont _).1 h
    have hC1 := gs_dens_C1_stat hws hψ
    rw [hd] at hC1
    refine not_C1Dens_of_kink (f := fun t => (cTrap n * trapG t) ^ 2)
      ((continuous_const.mul lipschitz_trapG.continuous).pow 2) (t0 := 1 / 3) (δ := 1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun h h0 hδ => ?_) hC1
    simp only [D2]
    rw [trapG_mid (t := 1 / 3 + h) (by linarith) (by linarith),
      trapG_mid (t := 1 / 3) (by norm_num) (by norm_num), trapG_left (t := 1 / 3 - h) (by linarith)]
    have e : (cTrap n * 1) ^ 2 - 2 * (cTrap n * 1) ^ 2 + (cTrap n * (3 * (1 / 3 - h))) ^ 2 =
        -(cTrap n ^ 2 * (3 * h * (2 - 3 * h))) := by ring
    have h8 : 0 ≤ 3 * h * (2 - 3 * h) := mul_nonneg (by positivity) (by linarith)
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (by positivity) h8)]
    have h1 : 2 * h ≤ 3 * h * (2 - 3 * h) := by nlinarith only [h0, hδ]
    have h2 : 1 * (3 * h * (2 - 3 * h)) ≤ cTrap n ^ 2 * (3 * h * (2 - 3 * h)) :=
      mul_le_mul_of_nonneg_right hc1 h8
    linarith

end DFT.Continuum.Line
