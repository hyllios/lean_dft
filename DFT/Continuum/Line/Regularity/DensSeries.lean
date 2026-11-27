/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.PSeries
import DFT.Continuum.Line.H1.WeakRep
import DFT.Continuum.Sine.Min

/-!
# The density profile of a coefficient sequence

For sine coefficients `c_m`, `m = (k, μ)` with `k` the index of particle `0`, put

  `u_μ(t) = Σ_k c_{(k, μ)} s_{k+1}(t)`,  `K(t) = N Σ_μ u_μ(t)²`.

If `Σ_m λ_m² c_m² < ∞` (`H²`), then `K` is `C¹` on `ℝ`, with derivative
`K' = N Σ_μ 2 u_μ u_μ'`, and vanishes at `0` and `1`: by Cauchy–Schwarz
`(Σ_k (k+1)|c_{(k,μ)}|)² ≤ ζ(2) Σ_k (k+1)⁴ c_{(k,μ)}²`, and `Σ_μ Σ_k (k+1)⁴ c² ≤ Σ λ² c² / π⁴`.

* `cc`, `uS`, `uD`, `KS`, `KD`; `consE : (Fin n → ℕ) × ℕ ≃ (Fin (n+1) → ℕ)`.
* `hasDerivAt_KS`, `continuous_KD`, `KS_zero`, `KS_one`.
* `integral_KS`: `∫ v K = N Σ_μ Σ_{k'} c_{(k',μ)} Σ_k c_{(k,μ)} ∫ v s_{k'+1} s_{k+1}`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ}

/-- `(μ, k) ↦ (k, μ)` as an index of the sine basis. -/
def consE (n : ℕ) : (Fin n → ℕ) × ℕ ≃ (Fin (n + 1) → ℕ) :=
  (Equiv.prodComm _ _).trans (Fin.consEquiv fun _ => ℕ)

@[simp] lemma consE_apply (p : (Fin n → ℕ) × ℕ) : consE n p = Fin.cons p.2 p.1 := rfl

section series

variable (c : (Fin (n + 1) → ℕ) → ℝ)

/-- `c_{(k, μ)}`. -/
def cc (k : ℕ) (μ : Fin n → ℕ) : ℝ := c (Fin.cons k μ)

/-- `u_μ(t) = Σ_k c_{(k, μ)} s_{k+1}(t)`. -/
noncomputable def uS (μ : Fin n → ℕ) (t : ℝ) : ℝ := ∑' k, cc c k μ * sn (k + 1) t

/-- The termwise derivative of `u_μ`. -/
noncomputable def uD (μ : Fin n → ℕ) (t : ℝ) : ℝ :=
  ∑' k, cc c k μ * (√2 * (π * ((k + 1 : ℕ) : ℝ)) * Real.cos (π * ((k + 1 : ℕ) : ℝ) * t))

/-- The density profile `K(t) = N Σ_μ u_μ(t)²`. -/
noncomputable def KS (t : ℝ) : ℝ := (n + 1) * ∑' μ, uS c μ t ^ 2

/-- Its derivative `N Σ_μ 2 u_μ u_μ'`. -/
noncomputable def KD (t : ℝ) : ℝ := (n + 1) * ∑' μ, 2 * uS c μ t * uD c μ t

/-- `Σ_k (k+1)⁴ c_{(k,μ)}²`. -/
noncomputable def A4 (μ : Fin n → ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ 4 * cc c k μ ^ 2

/-- `Σ_k (k+1) |c_{(k,μ)}|`. -/
noncomputable def S1 (μ : Fin n → ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * |cc c k μ|

end series

/-- `ζ(2) = Σ_k 1/(k+1)²`. -/
noncomputable def Z2 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2

lemma summable_inv_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine this.congr fun k => ?_
  push_cast; ring

lemma abs_sn_le (k : ℕ) (t : ℝ) : |sn k t| ≤ √2 := by
  simp only [sn, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_sin_le_one _)

lemma sn_zero (k : ℕ) : sn k 0 = 0 := by simp [sn]

lemma sn_one (k : ℕ) : sn k 1 = 0 := by
  simp only [sn, mul_one]
  rw [show π * (k : ℝ) = (k : ℕ) * π by ring, Real.sin_nat_mul_pi, mul_zero]

variable {c : (Fin (n + 1) → ℕ) → ℝ}

section free

lemma A4_nonneg (μ : Fin n → ℕ) : 0 ≤ A4 c μ := tsum_nonneg fun _ => by positivity

lemma S1_nonneg (μ : Fin n → ℕ) : 0 ≤ S1 c μ := tsum_nonneg fun _ => by positivity

/-! ### Termwise bounds -/

lemma norm_term_le (μ : Fin n → ℕ) (k : ℕ) (t : ℝ) :
    ‖cc c k μ * sn (k + 1) t‖ ≤ √2 * (((k : ℝ) + 1) * |cc c k μ|) := by
  rw [Real.norm_eq_abs, abs_mul]
  calc |cc c k μ| * |sn (k + 1) t| ≤ |cc c k μ| * √2 :=
        mul_le_mul_of_nonneg_left (abs_sn_le _ _) (abs_nonneg _)
    _ ≤ √2 * (((k : ℝ) + 1) * |cc c k μ|) := by
        have : |cc c k μ| ≤ ((k : ℝ) + 1) * |cc c k μ| :=
          le_mul_of_one_le_left (abs_nonneg _) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        nlinarith [Real.sqrt_nonneg 2]

lemma norm_dterm_le (μ : Fin n → ℕ) (k : ℕ) (t : ℝ) :
    ‖cc c k μ * (√2 * (π * ((k + 1 : ℕ) : ℝ)) * Real.cos (π * ((k + 1 : ℕ) : ℝ) * t))‖ ≤
      √2 * π * (((k : ℝ) + 1) * |cc c k μ|) := by
  rw [Real.norm_eq_abs]
  push_cast
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos pi_pos, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  have := Real.abs_cos_le_one (π * ((k : ℝ) + 1) * t)
  have h0 : 0 ≤ √2 * (π * ((k : ℝ) + 1)) * |cc c k μ| := by positivity
  nlinarith

lemma uS_zero (μ : Fin n → ℕ) : uS c μ 0 = 0 := by simp [uS, sn_zero]

lemma uS_one (μ : Fin n → ℕ) : uS c μ 1 = 0 := by simp [uS, sn_one]

lemma KS_zero : KS c 0 = 0 := by simp [KS, uS_zero]

lemma KS_one : KS c 1 = 0 := by simp [KS, uS_one]

/-- `a(k', k) = ∫ v s_{k'+1} s_{k+1}`. -/
noncomputable def aK (v : Pot) (k' k : ℕ) : ℝ := ∫ t, sn (k' + 1) t * (ext v t * sn (k + 1) t) ∂μ1

lemma integrable_mu1_cont {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ1 :=
  (hf.continuousOn.integrableOn_compact (K := Icc (0 : ℝ) 1) isCompact_Icc).mono_set
    Ioo_subset_Icc_self


end free

section bounds

variable (hcl : Summable fun m => lam m ^ 2 * c m ^ 2)
include hcl

lemma summable_pow4 : Summable fun m : Fin (n + 1) → ℕ => ((m 0 : ℝ) + 1) ^ 4 * c m ^ 2 := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (hcl.div_const (π ^ 4))
  have hk : ((m 0 : ℝ) + 1) ^ 2 ≤ ksq m := by
    have e : ((ksq m : ℕ) : ℝ) = ∑ j, ((m j : ℝ) + 1) ^ 2 := by simp [ksq]
    rw [e]
    exact Finset.single_le_sum (f := fun j => ((m j : ℝ) + 1) ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ 0)
  have hk4 : ((m 0 : ℝ) + 1) ^ 4 ≤ (ksq m : ℝ) ^ 2 := by
    rw [show ((m 0 : ℝ) + 1) ^ 4 = (((m 0 : ℝ) + 1) ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) hk 2
  have hπ : 0 < π ^ 4 := by positivity
  rw [le_div_iff₀ hπ, lam]
  calc ((m 0 : ℝ) + 1) ^ 4 * c m ^ 2 * π ^ 4 ≤ (ksq m : ℝ) ^ 2 * c m ^ 2 * π ^ 4 := by gcongr
    _ = (π ^ 2 * ksq m) ^ 2 * c m ^ 2 := by ring

lemma summable_A4_prod :
    Summable fun p : (Fin n → ℕ) × ℕ => ((p.2 : ℝ) + 1) ^ 4 * cc c p.2 p.1 ^ 2 := by
  have := (consE n).summable_iff.2 (summable_pow4 hcl)
  refine this.congr fun p => ?_
  simp [cc]

lemma summable_A4_fiber (μ : Fin n → ℕ) :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ 4 * cc c k μ ^ 2 :=
  ((summable_prod_of_nonneg (fun _ => by positivity)).1 (summable_A4_prod hcl)).1 μ

lemma summable_A4 : Summable (A4 c) :=
  ((summable_prod_of_nonneg (fun _ => by positivity)).1 (summable_A4_prod hcl)).2

/-- **Cauchy–Schwarz**: `(Σ_k (k+1)|c|)² ≤ ζ(2) Σ_k (k+1)⁴ c²`. -/
lemma summable_S1_and (μ : Fin n → ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * |cc c k μ|) ∧ S1 c μ ≤ √(Z2 * A4 c μ) := by
  have hT : ∀ T : Finset ℕ, ∑ k ∈ T, ((k : ℝ) + 1) * |cc c k μ| ≤ √(Z2 * A4 c μ) := by
    intro T
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun k => 1 / ((k : ℝ) + 1))
      (fun k => ((k : ℝ) + 1) ^ 2 * |cc c k μ|)
    have e : ∀ k : ℕ, 1 / ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 * |cc c k μ|) =
        ((k : ℝ) + 1) * |cc c k μ| := fun k => by field_simp
    have e2 : ∀ k : ℕ, (((k : ℝ) + 1) ^ 2 * |cc c k μ|) ^ 2 = ((k : ℝ) + 1) ^ 4 * cc c k μ ^ 2 :=
      fun k => by rw [mul_pow, sq_abs]; ring
    have e3 : ∀ k : ℕ, (1 / ((k : ℝ) + 1)) ^ 2 = 1 / ((k : ℝ) + 1) ^ 2 := fun k => by
      rw [div_pow, one_pow]
    simp only [e, e2, e3] at hcs
    have h1 : ∑ k ∈ T, 1 / ((k : ℝ) + 1) ^ 2 ≤ Z2 :=
      summable_inv_sq.sum_le_tsum T fun k _ => by positivity
    have h2 : ∑ k ∈ T, ((k : ℝ) + 1) ^ 4 * cc c k μ ^ 2 ≤ A4 c μ :=
      (summable_A4_fiber hcl μ).sum_le_tsum T fun k _ => by positivity
    refine Real.le_sqrt_of_sq_le (hcs.trans ?_)
    exact mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => by positivity)
      (tsum_nonneg fun k => by positivity)
  have h0 : 0 ≤ fun k : ℕ => ((k : ℝ) + 1) * |cc c k μ| := fun k => by positivity
  exact ⟨summable_of_sum_le h0 hT, Real.tsum_le_of_sum_le h0 hT⟩

lemma summable_S1_fiber (μ : Fin n → ℕ) :
    Summable fun k : ℕ => ((k : ℝ) + 1) * |cc c k μ| := (summable_S1_and hcl μ).1

lemma S1_sq_le (μ : Fin n → ℕ) : S1 c μ ^ 2 ≤ Z2 * A4 c μ := by
  have h := (summable_S1_and hcl μ).2
  have hZ : 0 ≤ Z2 := tsum_nonneg fun k => by positivity
  calc S1 c μ ^ 2 ≤ √(Z2 * A4 c μ) ^ 2 := pow_le_pow_left₀ (S1_nonneg μ) h 2
    _ = Z2 * A4 c μ := Real.sq_sqrt (mul_nonneg hZ (A4_nonneg μ))

lemma summable_abs_cc (μ : Fin n → ℕ) : Summable fun k : ℕ => |cc c k μ| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun k => le_mul_of_one_le_left (abs_nonneg _)
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
    (summable_S1_fiber hcl μ)

lemma abs_uS_le (μ : Fin n → ℕ) (t : ℝ) : |uS c μ t| ≤ √2 * S1 c μ := by
  have hs : Summable fun k : ℕ => √2 * (((k : ℝ) + 1) * |cc c k μ|) :=
    (summable_S1_fiber hcl μ).mul_left _
  rw [← Real.norm_eq_abs, S1, ← tsum_mul_left]
  exact tsum_of_norm_bounded hs.hasSum (norm_term_le μ · t)

lemma abs_uD_le (μ : Fin n → ℕ) (t : ℝ) : |uD c μ t| ≤ √2 * π * S1 c μ := by
  have hs : Summable fun k : ℕ => √2 * π * (((k : ℝ) + 1) * |cc c k μ|) :=
    (summable_S1_fiber hcl μ).mul_left _
  rw [← Real.norm_eq_abs, S1, ← tsum_mul_left]
  exact tsum_of_norm_bounded hs.hasSum (norm_dterm_le μ · t)

/-! ### Differentiability -/

lemma hasDerivAt_uS (μ : Fin n → ℕ) (t : ℝ) : HasDerivAt (uS c μ) (uD c μ t) t := by
  refine hasDerivAt_tsum (u := fun k : ℕ => √2 * π * (((k : ℝ) + 1) * |cc c k μ|))
    ((summable_S1_fiber hcl μ).mul_left _) (fun k y => ((hasDerivAt_sn (k + 1) y).const_mul
      (cc c k μ))) (fun k y => norm_dterm_le μ k y) (y₀ := 0) ?_ t
  simp [sn_zero]

lemma continuous_uS (μ : Fin n → ℕ) : Continuous (uS c μ) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_uS hcl μ t).continuousAt

lemma continuous_uD (μ : Fin n → ℕ) : Continuous (uD c μ) :=
  continuous_tsum (fun _ => continuous_const.mul (continuous_const.mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))))
    ((summable_S1_fiber hcl μ).mul_left (√2 * π)) fun k t => norm_dterm_le μ k t

lemma bound_KD (μ : Fin n → ℕ) (t : ℝ) :
    ‖2 * uS c μ t * uD c μ t‖ ≤ 4 * π * (Z2 * A4 c μ) := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
  have h1 := abs_uS_le hcl μ t
  have h2 := abs_uD_le hcl μ t
  have h3 := S1_sq_le hcl μ
  have hS := S1_nonneg (c := c) μ
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc 2 * |uS c μ t| * |uD c μ t| ≤ 2 * (√2 * S1 c μ) * (√2 * π * S1 c μ) := by
        gcongr
    _ = 4 * π * S1 c μ ^ 2 := by rw [show 2 * (√2 * S1 c μ) * (√2 * π * S1 c μ) =
          2 * (√2 * √2) * π * S1 c μ ^ 2 by ring, hs2]; ring
    _ ≤ 4 * π * (Z2 * A4 c μ) := by gcongr

lemma bound_KS (μ : Fin n → ℕ) (t : ℝ) : ‖uS c μ t ^ 2‖ ≤ 2 * (Z2 * A4 c μ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := abs_uS_le hcl μ t
  have h3 := S1_sq_le hcl μ
  have hS := S1_nonneg (c := c) μ
  calc uS c μ t ^ 2 = |uS c μ t| ^ 2 := (sq_abs _).symm
    _ ≤ (√2 * S1 c μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = 2 * S1 c μ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
    _ ≤ 2 * (Z2 * A4 c μ) := by gcongr

lemma summable_bound : Summable fun μ : Fin n → ℕ => Z2 * A4 c μ :=
  (summable_A4 hcl).mul_left _

/-- **`K` is differentiable with derivative `K'`.** -/
theorem hasDerivAt_KS (t : ℝ) : HasDerivAt (KS c) (KD c t) t := by
  have h := hasDerivAt_tsum (u := fun μ => 4 * π * (Z2 * A4 c μ))
    ((summable_bound hcl).mul_left _)
    (fun μ y => ((hasDerivAt_uS hcl μ y).pow 2).congr_deriv (by push_cast; ring))
    (fun μ y => bound_KD hcl μ y) (y₀ := 0) (by simp [uS_zero]) t
  exact h.const_mul _

theorem continuous_KD : Continuous (KD c) :=
  continuous_const.mul (continuous_tsum (fun μ => (continuous_const.mul
    (continuous_uS hcl μ)).mul (continuous_uD hcl μ))
    ((summable_bound hcl).mul_left (4 * π)) fun μ t => bound_KD hcl μ t)

theorem continuous_KS : Continuous (KS c) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_KS hcl t).continuousAt

/-! ### The integral of `v K` -/

/-- `∫ v u_μ² = Σ_{k'} c_{(k',μ)} Σ_k c_{(k,μ)} a(k', k)`. -/
lemma integral_uS_sq (v : Pot) (μ : Fin n → ℕ) :
    ∫ t, ext v t * uS c μ t ^ 2 ∂μ1 =
      ∑' k', cc c k' μ * ∑' k, aK v k' k * cc c k μ := by
  have hv := continuous_ext v
  have hu := continuous_uS hcl μ
  have habs := summable_abs_cc hcl μ
  -- the outer sum
  have hF : ∀ k' : ℕ, Integrable (fun t => cc c k' μ * sn (k' + 1) t * (ext v t * uS c μ t)) μ1 :=
    fun k' => integrable_mu1_cont ((continuous_const.mul (continuous_sn _)).mul
      ((continuous_ext v).mul (continuous_uS hcl μ)))
  have hbd : ∀ k' : ℕ, ∫ t, ‖cc c k' μ * sn (k' + 1) t * (ext v t * uS c μ t)‖ ∂μ1 ≤
      |cc c k' μ| * (√2 * (‖v‖ * (√2 * S1 c μ))) := fun k' => by
    have hb : ∀ t, ‖cc c k' μ * sn (k' + 1) t * (ext v t * uS c μ t)‖ ≤
        |cc c k' μ| * (√2 * (‖v‖ * (√2 * S1 c μ))) := fun t => by
      have a1 := abs_sn_le (k' + 1) t
      have a2 := abs_ext_le v t
      have a3 := abs_uS_le hcl μ t
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      calc |cc c k' μ| * |sn (k' + 1) t| * (|ext v t| * |uS c μ t|)
          ≤ |cc c k' μ| * √2 * (‖v‖ * (√2 * S1 c μ)) := by gcongr
        _ = _ := by ring
    calc _ ≤ ∫ t, |cc c k' μ| * (√2 * (‖v‖ * (√2 * S1 c μ))) ∂μ1 :=
          integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (integrable_const _)
            (ae_of_all _ hb)
      _ = _ := by simp
  have hsum : Summable fun k' : ℕ => ∫ t, ‖cc c k' μ * sn (k' + 1) t * (ext v t * uS c μ t)‖ ∂μ1 :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hbd
      (habs.mul_right _)
  have h1 : ∫ t, ext v t * uS c μ t ^ 2 ∂μ1 =
      ∑' k', ∫ t, cc c k' μ * sn (k' + 1) t * (ext v t * uS c μ t) ∂μ1 := by
    rw [integral_tsum_of_summable_integral_norm hF hsum]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [tsum_mul_right]
    change ext v t * uS c μ t ^ 2 = uS c μ t * (ext v t * uS c μ t)
    ring
  rw [h1]
  refine tsum_congr fun k' => ?_
  -- the inner sum
  have hG : ∀ k : ℕ,
      Integrable (fun t => cc c k μ * (sn (k' + 1) t * (ext v t * sn (k + 1) t))) μ1 :=
    fun k => integrable_mu1_cont (continuous_const.mul ((continuous_sn _).mul
      ((continuous_ext v).mul (continuous_sn _))))
  have hbd2 : ∀ k : ℕ, ∫ t, ‖cc c k μ * (sn (k' + 1) t * (ext v t * sn (k + 1) t))‖ ∂μ1 ≤
      |cc c k μ| * (√2 * (‖v‖ * √2)) := fun k => by
    have hb : ∀ t, ‖cc c k μ * (sn (k' + 1) t * (ext v t * sn (k + 1) t))‖ ≤
        |cc c k μ| * (√2 * (‖v‖ * √2)) := fun t => by
      have a1 := abs_sn_le (k' + 1) t
      have a2 := abs_ext_le v t
      have a3 := abs_sn_le (k + 1) t
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      calc |cc c k μ| * (|sn (k' + 1) t| * (|ext v t| * |sn (k + 1) t|))
          ≤ |cc c k μ| * (√2 * (‖v‖ * √2)) := by gcongr
        _ = _ := by ring
    calc _ ≤ ∫ t, |cc c k μ| * (√2 * (‖v‖ * √2)) ∂μ1 :=
          integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (integrable_const _)
            (ae_of_all _ hb)
      _ = _ := by simp
  have hsum2 : Summable fun k : ℕ =>
      ∫ t, ‖cc c k μ * (sn (k' + 1) t * (ext v t * sn (k + 1) t))‖ ∂μ1 :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hbd2
      (habs.mul_right _)
  have h2 := integral_tsum_of_summable_integral_norm hG hsum2
  have e1 : ∫ t, cc c k' μ * sn (k' + 1) t * (ext v t * uS c μ t) ∂μ1 =
      cc c k' μ * ∫ t, ∑' k, cc c k μ * (sn (k' + 1) t * (ext v t * sn (k + 1) t)) ∂μ1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [uS, ← tsum_mul_left]
    congr 1; funext k; ring
  rw [e1, ← h2]
  congr 1
  refine tsum_congr fun k => ?_
  rw [integral_const_mul, aK]; ring

/-- `∫ v K = N Σ_μ Σ_{k'} c_{(k',μ)} Σ_k c_{(k,μ)} a(k', k)`. -/
theorem integral_KS (v : Pot) :
    ∫ t, ext v t * KS c t ∂μ1 =
      (n + 1) * ∑' μ, ∑' k', cc c k' μ * ∑' k, aK v k' k * cc c k μ := by
  have hF : ∀ μ : Fin n → ℕ, Integrable (fun t => ext v t * uS c μ t ^ 2) μ1 :=
    fun μ => integrable_mu1_cont ((continuous_ext v).mul ((continuous_uS hcl μ).pow 2))
  have hbd : ∀ μ : Fin n → ℕ, ∫ t, ‖ext v t * uS c μ t ^ 2‖ ∂μ1 ≤ ‖v‖ * (2 * (Z2 * A4 c μ)) :=
    fun μ => by
      have hb : ∀ t, ‖ext v t * uS c μ t ^ 2‖ ≤ ‖v‖ * (2 * (Z2 * A4 c μ)) := fun t => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (abs_ext_le v t) (bound_KS hcl μ t) (norm_nonneg _) (norm_nonneg _)
      calc _ ≤ ∫ t, ‖v‖ * (2 * (Z2 * A4 c μ)) ∂μ1 :=
            integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (integrable_const _)
              (ae_of_all _ hb)
        _ = _ := by simp
  have hsum : Summable fun μ : Fin n → ℕ => ∫ t, ‖ext v t * uS c μ t ^ 2‖ ∂μ1 :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hbd
      (((summable_bound hcl).mul_left 2).mul_left _)
  have h := integral_tsum_of_summable_integral_norm hF hsum
  have e : ∫ t, ext v t * KS c t ∂μ1 = (n + 1) * ∫ t, ∑' μ, ext v t * uS c μ t ^ 2 ∂μ1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [KS]
    rw [tsum_mul_left]; ring
  rw [e, ← h]
  congr 1
  exact tsum_congr fun μ => integral_uS_sq hcl v μ

end bounds

end DFT.Continuum.Line
