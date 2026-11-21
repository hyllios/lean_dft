/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Cube
import DFT.Continuum.Line.Strong

/-!
# States of `N` particles in the sine basis

For a state `φ` of `n + 1` particles on `[0, 1]` (`C²`, vanishing on the faces of the cube) the
kinetic energy is diagonal in the sine basis,

`∫ |∇φ|² = Σ_m π² |k|² ⟨s_m, φ⟩²`,  `k = m + 1`,

because `⟨s_m, -Δφ⟩ = ⟨-Δ s_m, φ⟩ = π² |k|² ⟨s_m, φ⟩` (integration by parts twice), followed by
Parseval for the pair `(-Δφ, φ)`. Relabelling the particles relabels the coefficients.

* `muN_eq`: the measure of the cube is the product measure.
* `dkk_smd`: `∂ₖₖ s_m = -(π kₖ)² s_m`.
* `ibpN'`: integration by parts against any `C²` function vanishing on the faces.
* `hasSum_kin`: **the kinetic energy in the sine basis**.
* `cf_pm`: the coefficients of a state of exchange symmetry `τ`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real

variable {n : ℕ}

lemma muN_eq : μN n = piM (n + 1) := by
  rw [piM, ← Measure.restrict_pi_pi, ← volume_pi]

/-- `|k|² = Σⱼ (mⱼ + 1)²`. -/
def ksq (m : Fin (n + 1) → ℕ) : ℕ := ∑ j, (m j + 1) ^ 2

/-! ### Derivatives of the sines -/

lemma hasDerivAt_sn (k : ℕ) (t : ℝ) :
    HasDerivAt (sn k) (√2 * (π * k) * Real.cos (π * k * t)) t := by
  have h := ((hasDerivAt_id t).const_mul (π * k)).sin.const_mul √2
  simp only [id, mul_one] at h
  convert h using 1
  · funext x; simp [sn]
  · ring

lemma hasDerivAt_dsn (k : ℕ) (t : ℝ) :
    HasDerivAt (fun t => √2 * (π * k) * Real.cos (π * k * t)) (-(π * k) ^ 2 * sn k t) t := by
  have h := ((hasDerivAt_id t).const_mul (π * k)).cos.const_mul (√2 * (π * k))
  simp only [id, mul_one] at h
  convert h using 1
  simp only [sn]; ring

lemma sn_zero (k : ℕ) : sn k 0 = 0 := by simp [sn]

lemma sn_one (k : ℕ) : sn k 1 = 0 := by
  simp only [sn, mul_one]
  rw [show π * (k : ℝ) = k * π by ring, Real.sin_nat_mul_pi, mul_zero]

lemma smd_update (m : Fin (n + 1) → ℕ) (x : Cfg n) (j : Fin (n + 1)) (t : ℝ) :
    smd m (Function.update x j t) =
      sn (m j + 1) t * ∏ i ∈ Finset.univ.erase j, sn (m i + 1) (x i) := by
  simp only [smd]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

lemma contDiff_smd (m : Fin (n + 1) → ℕ) : ContDiff ℝ 2 (smd m) :=
  contDiff_prod fun j _ => (by unfold sn; fun_prop : ContDiff ℝ 2 (sn (m j + 1))).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).contDiff

lemma dk_smd_update (m : Fin (n + 1) → ℕ) (x : Cfg n) (j : Fin (n + 1)) (t : ℝ) :
    dk j (smd m) (Function.update x j t) = √2 * (π * (m j + 1 : ℕ)) *
      Real.cos (π * (m j + 1 : ℕ) * t) * ∏ i ∈ Finset.univ.erase j, sn (m i + 1) (x i) := by
  have h1 := hasDerivAt_slice ((contDiff_smd m).differentiable (by norm_num)) x j t
  have h2 : HasDerivAt (fun s => smd m (Function.update x j s)) (√2 * (π * (m j + 1 : ℕ)) *
      Real.cos (π * (m j + 1 : ℕ) * t) * ∏ i ∈ Finset.univ.erase j, sn (m i + 1) (x i)) t := by
    simp only [smd_update]
    exact (hasDerivAt_sn _ t).mul_const _
  exact h1.unique h2

/-- `∂ⱼⱼ s_m = -(π kⱼ)² s_m`. -/
lemma dkk_smd (m : Fin (n + 1) → ℕ) (x : Cfg n) (j : Fin (n + 1)) :
    dkk j (smd m) x = -(π * (m j + 1 : ℕ)) ^ 2 * smd m x := by
  have hd : Differentiable ℝ (dk j (smd m)) :=
    (contDiff_dk (contDiff_smd m) j).differentiable one_ne_zero
  have h1 := hasDerivAt_slice hd x j (x j)
  rw [Function.update_eq_self] at h1
  have h2 : HasDerivAt (fun s => dk j (smd m) (Function.update x j s))
      (-(π * (m j + 1 : ℕ)) ^ 2 * sn (m j + 1) (x j) *
        ∏ i ∈ Finset.univ.erase j, sn (m i + 1) (x i)) (x j) := by
    simp only [dk_smd_update]
    exact (hasDerivAt_dsn _ (x j)).mul_const _
  rw [dkk, h1.unique h2, ← Function.update_eq_self j x, smd_update, Function.update_eq_self]
  ring

lemma smd_face (m : Fin (n + 1) → ℕ) (x : Cfg n) (j : Fin (n + 1)) (h : x j = 0 ∨ x j = 1) :
    smd m x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j) (by
    rcases h with h | h <;> rw [h]
    exacts [sn_zero _, sn_one _])

/-! ### Integration by parts -/

/-- **Integration by parts along coordinate `k`**, against a `C²` function vanishing on the
faces. -/
lemma ibpN' {Φ φ : Cfg n → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ x k, (x k = 0 ∨ x k = 1) → φ x = 0) (k : Fin (n + 1)) :
    ∫ x, dk k Φ x * dk k φ x ∂μN n = -∫ x, dkk k Φ x * φ x ∂μN n := by
  have hdc : Continuous (dk k Φ) := (contDiff_dk hΦ k).continuous
  have hdφ : Continuous (dk k φ) := (contDiff_dk hφ k).continuous
  rw [integral_cube_insertNth (F := fun x => dk k Φ x * dk k φ x) (hdc.mul hdφ) k,
    integral_cube_insertNth (F := fun x => dkk k Φ x * φ x)
      ((continuous_dkk hΦ k).mul hφ.continuous) k, ← integral_neg]
  congr 1; funext y
  have hd1 : Differentiable ℝ (dk k Φ) := (contDiff_dk hΦ k).differentiable one_ne_zero
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun t => dk k Φ (Fin.insertNth k t y)) (u' := fun t => dkk k Φ (Fin.insertNth k t y))
    (v := fun t => φ (Fin.insertNth k t y)) (v' := fun t => dk k φ (Fin.insertNth k t y))
    (fun t _ => hasDerivAt_insertNth hd1 k y t)
    (fun t _ => hasDerivAt_insertNth (hφ.differentiable (by norm_num)) k y t)
    (((continuous_dkk hΦ k).comp (by fun_prop)).intervalIntegrable _ _)
    ((hdφ.comp (by fun_prop)).intervalIntegrable _ _)
  have h0 : φ (Fin.insertNth k 0 y) = 0 := hφ0 _ k (Or.inl (by simp))
  have h1 : φ (Fin.insertNth k 1 y) = 0 := hφ0 _ k (Or.inr (by simp))
  rw [h0, h1, mul_zero, mul_zero, sub_zero, zero_sub, integral_unit', integral_unit'] at h
  rw [h]

/-! ### The kinetic energy -/

/-- The coefficient over the cube of `n + 1` particles. -/
noncomputable abbrev cN (m : Fin (n + 1) → ℕ) (f : Cfg n → ℝ) : ℝ := cf m f

lemma cN_eq (m : Fin (n + 1) → ℕ) (f : Cfg n → ℝ) : cN m f = ∫ x, smd m x * f x ∂μN n := by
  rw [muN_eq]; rfl

variable {τ : Stat}

/-- `⟨s_m, -Δφ⟩ = π² |k|² ⟨s_m, φ⟩`, for `φ` `C²` and vanishing on the walls. -/
lemma cN_lap0 {φ : Cfg n → ℝ} (hφ2 : ContDiff ℝ 2 φ)
    (hφw : ∀ x k, (x k = 0 ∨ x k = 1) → φ x = 0) (m : Fin (n + 1) → ℕ) :
    cN m (fun x => -lapN φ x) = π ^ 2 * ksq m * cN m φ := by
  have hs := contDiff_smd m
  have hc := hφ2.continuous
  have hj : ∀ j, ∫ x, smd m x * dkk j φ x ∂μN n = -(π * (m j + 1 : ℕ)) ^ 2 * cN m φ := by
    intro j
    have a := ibpN' hφ2 hs (smd_face m) j
    have b := ibpN0 hs hφ2 hφw j
    have e : ∫ x, dk j φ x * dk j (smd m) x ∂μN n = ∫ x, dk j (smd m) x * dk j φ x ∂μN n :=
      integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    rw [cN_eq, ← integral_const_mul]
    have c : ∫ x, smd m x * dkk j φ x ∂μN n = ∫ x, dkk j (smd m) x * φ x ∂μN n := by
      have := integral_congr_ae (μ := μN n) (ae_of_all _ fun x => mul_comm (smd m x) (dkk j φ x))
      rw [this]; linarith
    rw [c]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [dkk_smd]; ring
  rw [cN_eq, cN_eq]
  have e : (fun x => smd m x * -lapN φ x) = fun x => -∑ j, smd m x * dkk j φ x := by
    funext x; simp only [lapN, Finset.mul_sum, mul_neg]
  rw [e, integral_neg, integral_finsetSum (f := fun j x => smd m x * dkk j φ x) _ fun j _ =>
    integrableN (hs.continuous.mul (continuous_dkk hφ2 j))]
  simp only [hj, ksq, ← cN_eq]
  push_cast
  rw [← Finset.sum_mul, Finset.mul_sum, ← neg_mul, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma cN_lap {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) (m : Fin (n + 1) → ℕ) :
    cN m (fun x => -lapN φ x) = π ^ 2 * ksq m * cN m φ :=
  cN_lap0 hφ.1 hφ.2.2 m

/-- **The kinetic energy in the sine basis**, for `φ` `C²` and vanishing on the walls. -/
theorem hasSum_kin0 {φ : Cfg n → ℝ} (hφ2 : ContDiff ℝ 2 φ)
    (hφw : ∀ x k, (x k = 0 ∨ x k = 1) → φ x = 0) :
    HasSum (fun m => π ^ 2 * ksq m * cN m φ ^ 2) (∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n) := by
  have hc := hφ2.continuous
  have hd : ∀ k, Continuous (dk k φ) := fun k => (contDiff_dk hφ2 k).continuous
  have hpair := hasSum_pair_cube (f := fun x => -lapN φ x) (g := φ)
    (continuous_lapN hφ2).neg hc
  have hkin : ∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n = ∫ x, -lapN φ x * φ x ∂μN n := by
    rw [integral_finsetSum (f := fun k x => dk k φ x * dk k φ x) _
      fun k _ => integrableN ((hd k).mul (hd k))]
    simp only [ibpN0 hφ2 hφ2 hφw]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum (f := fun k x => dkk k φ x * φ x) _
      fun k _ => integrableN ((continuous_dkk hφ2 k).mul hc), ← integral_neg]
    congr 1; funext x; simp only [lapN, Finset.sum_mul, neg_mul]
  rw [hkin, muN_eq]
  refine hpair.congr_fun fun m => ?_
  change π ^ 2 * ksq m * cN m φ ^ 2 = cN m (fun x => -lapN φ x) * cN m φ
  rw [cN_lap0 hφ2 hφw]; ring

/-- **The kinetic energy in the sine basis**: `∫ |∇φ|² = Σ_m π² |k|² ⟨s_m, φ⟩²`. -/
theorem hasSum_kin {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) :
    HasSum (fun m => π ^ 2 * ksq m * cN m φ ^ 2) (∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n) :=
  hasSum_kin0 hφ.1 hφ.2.2

/-! ### Relabelling -/

/-- Relabelling of multi-indices. -/
def pmI (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ := fun i => m (σ i)

lemma pmI_pmI (σ ρ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) :
    pmI σ (pmI ρ m) = pmI (ρ * σ) m := by
  funext i; simp [pmI]

lemma pmI_one (m : Fin (n + 1) → ℕ) : pmI 1 m = m := rfl

lemma smd_pm (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    smd (pmI σ m) (pm σ x) = smd m x := by
  simp only [smd, pmI, pm_apply]
  exact Equiv.prod_comp σ (fun i => sn (m i + 1) (x i))

/-- The coefficients of a state of exchange symmetry `τ`. -/
lemma cN_pm {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) (σ : Equiv.Perm (Fin (n + 1)))
    (m : Fin (n + 1) → ℕ) : cN (pmI σ m) φ = ch τ σ * cN m φ := by
  rw [cN_eq, cN_eq, ← integral_pm σ, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smd_pm, hφ.2.1 σ x]; ring

end DFT.Continuum.Sine
