/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import DFT.Continuum.Line.MeasurePotential.MeasureGS

/-!
# Positive solutions are ground states (measure potentials, one particle)

* `deriv_abs_sq_le`, `H10.abs`, `kinM_abs_le`, `QM_abs_le`: `|ψ| ∈ H¹₀` with `∫ |ψ|'² ≤ ∫ ψ'²`
  (at a zero of `ψ`, `|ψ|` has a local minimum, so its derivative vanishes).
* `exists_min_nonneg`: every measure potential has a nonnegative normalised ground state.
* **`isGSM_of_pos_weak`**: if `g ∈ H¹₀` is positive on `(0, 1)` and solves `-g'' + ν g = E g` weakly
  for some measure potential `ν`, then `E = E₀(ν)` and `g` is a ground state of `ν`.
* **`vrepM_of_pos_weak`**: so `g²` is `v`-representable with measure potentials.

The proof tests the weak equation of `g` with a nonnegative ground state `ψ₀`, and the
Euler–Lagrange equation of `ψ₀` with `g`: `(E - E₀) ∫ g ψ₀ = 0`, and `∫ g ψ₀ > 0`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

/-! ### `|ψ|` -/

lemma deriv_abs_sq_le {ψ : ℝ → ℝ} {t : ℝ} (hd : DifferentiableAt ℝ ψ t) :
    deriv (fun s => |ψ s|) t ^ 2 ≤ deriv ψ t ^ 2 := by
  rcases lt_trichotomy (ψ t) 0 with h | h | h
  · have := ((hasDerivAt_abs_neg h).comp t hd.hasDerivAt).deriv
    change deriv ((fun x : ℝ => |x|) ∘ ψ) t ^ 2 ≤ _
    rw [this]; simp
  · have hmin : IsLocalMin (fun s => |ψ s|) t :=
      Filter.Eventually.of_forall fun s => by simp [h, abs_nonneg]
    rw [hmin.deriv_eq_zero]; simp [sq_nonneg]
  · have := ((hasDerivAt_abs_pos h).comp t hd.hasDerivAt).deriv
    change deriv ((fun x : ℝ => |x|) ∘ ψ) t ^ 2 ≤ _
    rw [this]; simp

lemma ae_deriv_abs_sq_le {ψ : ℝ → ℝ} (hψ : H10 ψ) :
    ∀ᵐ t ∂μ1, deriv (fun s => |ψ s|) t ^ 2 ≤ deriv ψ t ^ 2 := by
  have hd := hψ.1.ae_differentiableAt
  rw [uIcc01] at hd
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t h ht
  exact deriv_abs_sq_le (h (Ioo_subset_Icc_self ht))

lemma H10.abs {ψ : ℝ → ℝ} (hψ : H10 ψ) : H10 fun t => |ψ t| := by
  have hac : AbsolutelyContinuousOnInterval (fun t => |ψ t|) 0 1 := by
    have := (lipschitzWith_one_norm (E := ℝ)).comp_absolutelyContinuousOnInterval hψ.1
    simpa [Function.comp_def, Real.norm_eq_abs] using this
  refine ⟨hac, by simp [hψ.2.1], by simp [hψ.2.2.1], ?_⟩
  refine (show Integrable (fun t => deriv ψ t ^ 2) μ1 from hψ.2.2.2).mono'
    ((measurable_deriv _).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_deriv_abs_sq_le hψ] with t ht
  rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

lemma kinM_abs_le {ψ : ℝ → ℝ} (hψ : H10 ψ) : kinM (fun t => |ψ t|) ≤ kinM ψ :=
  integral_mono_ae hψ.abs.2.2.2 hψ.2.2.2 (ae_deriv_abs_sq_le hψ)

lemma sqP_abs {ψ : ℝ → ℝ} (hψ : H10 ψ) : sqP hψ.abs = sqP hψ := by
  ext t; simp [sq_abs]

lemma QM_abs_le (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) : QM ν hψ.abs ≤ QM ν hψ := by
  rw [QM, QM, sqP_abs hψ]; linarith [kinM_abs_le hψ]

/-- **A nonnegative ground state.** -/
theorem exists_min_nonneg (ν : PotM) :
    ∃ ψ : ℝ → ℝ, ∃ hψ : H10 ψ, (∀ t, 0 ≤ ψ t) ∧ ∫ t, ψ t ^ 2 ∂μ1 = 1 ∧ QM ν hψ = EM ν := by
  obtain ⟨ψ, hψ, hn, hmin⟩ := exists_min ν
  have hn' : ∫ t, |ψ t| ^ 2 ∂μ1 = 1 := by simpa [sq_abs] using hn
  exact ⟨_, hψ.abs, fun t => abs_nonneg _, hn',
    le_antisymm ((QM_abs_le ν hψ).trans hmin.le) (EM_le ν hψ.abs hn')⟩

/-! ### Positive weak solutions -/

lemma mulP_comm {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) : mulP hψ hφ = mulP hφ hψ := by
  ext t; simp [mul_comm]

lemma mulP_self {ψ : ℝ → ℝ} (hψ : H10 ψ) : mulP hψ hψ = sqP hψ := by
  ext t; simp [sq]

/-- `∫ g ψ > 0` for `g > 0` on `(0, 1)` and `ψ ≥ 0` not a.e. zero. -/
lemma integral_mul_pos {g ψ : ℝ → ℝ} (hg : H10 g) (hψ : H10 ψ)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) (hψ0 : ∀ t, 0 ≤ ψ t) (hn : ∫ t, ψ t ^ 2 ∂μ1 ≠ 0) :
    0 < ∫ t, g t * ψ t ∂μ1 := by
  have h0 : 0 ≤ᵐ[μ1] fun t => g t * ψ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (hpos t ht).le (hψ0 t)
  refine (integral_nonneg_of_ae h0).lt_of_ne fun h => hn ?_
  have hz := (integral_eq_zero_iff_of_nonneg_ae h0 (integrable_pp hg hψ)).1 h.symm
  have : (fun t => ψ t ^ 2) =ᵐ[μ1] 0 := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with t h1 ht
    have : ψ t = 0 := by
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (hpos t ht).ne'
      · exact h2
    simp [this]
  rw [integral_congr_ae this]; simp

lemma integral_sq_pos {g : ℝ → ℝ} (hg : H10 g) (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) :
    0 < ∫ t, g t ^ 2 ∂μ1 := by
  have h0 : 0 ≤ᵐ[μ1] fun t => g t ^ 2 := ae_of_all _ fun t => sq_nonneg _
  refine (integral_nonneg_of_ae h0).lt_of_ne fun h => ?_
  have hz := (integral_eq_zero_iff_of_nonneg_ae h0 (H10.int_sq_of_contOn hg.continuousOn)).1 h.symm
  have hpos' : ∀ᵐ t ∂μ1, 0 < g t ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact pow_pos (hpos t ht) 2
  obtain ⟨t, h1, h2⟩ := (hz.and hpos').exists
  simp [h1] at h2

/-- **Positive weak solutions are ground states**: if `g ∈ H¹₀` is positive on `(0, 1)` and solves
`-g'' + ν g = E g` weakly, then `E = E₀(ν)` and `g` is a ground state of `ν`. -/
theorem isGSM_of_pos_weak {ν : PotM} {g : ℝ → ℝ} (hg : H10 g)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) {E : ℝ}
    (hE : ∀ φ (hφ : H10 φ), ∫ t, deriv g t * deriv φ t ∂μ1 + ν (mulP hg hφ) =
      E * ∫ t, g t * φ t ∂μ1) :
    IsGSM ν g ∧ E = EM ν := by
  obtain ⟨ψ, hψ, hψ0, hn, hmin⟩ := exists_min_nonneg ν
  have h1 := euler_lagrange hψ hn hmin hg
  have h2 := hE ψ hψ
  have hI := integral_mul_pos hg hψ hpos hψ0 (by rw [hn]; exact one_ne_zero)
  have e1 : ∫ t, deriv ψ t * deriv g t ∂μ1 = ∫ t, deriv g t * deriv ψ t ∂μ1 := by
    simp_rw [mul_comm (deriv ψ _)]
  have e2 : ∫ t, ψ t * g t ∂μ1 = ∫ t, g t * ψ t ∂μ1 := by simp_rw [mul_comm (ψ _)]
  rw [e1, e2, mulP_comm hψ hg] at h1
  have hEE : E = EM ν := by
    have : (E - EM ν) * ∫ t, g t * ψ t ∂μ1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hI.ne'
  refine ⟨⟨hg, integral_sq_pos hg hpos, fun φ hφ => ?_⟩, hEE⟩
  have hgg := hE g hg
  rw [mulP_self, hEE] at hgg
  have hQ : QM ν hg = EM ν * ∫ t, g t ^ 2 ∂μ1 := by
    rw [QM, kinM]; simp_rw [sq]; exact hgg
  rw [hQ, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (EM_mul_le ν hφ) (integral_nonneg fun _ => sq_nonneg _)

/-- **`g²` is `v`-representable with a measure potential** whenever `g ∈ H¹₀` is positive on
`(0, 1)`, normalised, and solves `-g'' + ν g = E g` weakly for some `ν`. -/
theorem vrepM_of_pos_weak {ν : PotM} {g : ℝ → ℝ} (hg : H10 g)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) (hn : ∫ t, g t ^ 2 ∂μ1 = 1) {E : ℝ}
    (hE : ∀ φ (hφ : H10 φ), ∫ t, deriv g t * deriv φ t ∂μ1 + ν (mulP hg hφ) =
      E * ∫ t, g t * φ t ∂μ1) :
    VRepM (sqP hg) :=
  ⟨ν, g, (isGSM_of_pos_weak hg hpos hE).1, hn, fun _ => rfl⟩

end DFT.Continuum.Line
