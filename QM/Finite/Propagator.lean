/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import ForMathlib.Analysis.ODE.Linear

/-!
# The time-dependent Schrödinger equation

For a continuous family of self-adjoint operators `H(s)` on a finite-dimensional complex Hilbert
space and `ε > 0`, the propagator `U_ε` solves `i ε U' = H(s) U` with `U(0) = 1` on `[0, 1]`. It
exists and is unique (`ForMathlib.exists_linear_ode`, `ForMathlib.linear_ode_unique`), and every
`U_ε(s)` is unitary because `d/ds (U† U) = 0`.

## Main definitions

* `QM.IsPropagator H ε U`: `U(0) = 1` and `U' = -(i/ε) H U` on `[0, 1]`.

## Main results

* `exists_propagator`, `propagator_unique`: existence and uniqueness.
* `propagator_mem_unitary`: `U_ε(s)` is unitary for `s ∈ [0, 1]`.
-/

namespace QM

open Set Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `U` is the propagator of `i ε U' = H(s) U` on `[0, 1]`. -/
def IsPropagator (H : ℝ → E →L[ℂ] E) (ε : ℝ) (U : ℝ → E →L[ℂ] E) : Prop :=
  U 0 = 1 ∧ ∀ s ∈ Icc (0 : ℝ) 1,
    HasDerivWithinAt U ((-(I / ε)) • H s * U s) (Icc (0 : ℝ) 1) s

/-- **Existence of the propagator.** -/
theorem exists_propagator {H : ℝ → E →L[ℂ] E} (hH : Continuous H) (ε : ℝ) :
    ∃ U, IsPropagator H ε U :=
  ForMathlib.exists_linear_ode (A := fun s => (-(I / ε)) • H s) (by fun_prop)
    zero_le_one

omit [CompleteSpace E] in
/-- **Uniqueness of the propagator.** -/
theorem propagator_unique {H : ℝ → E →L[ℂ] E} (hH : Continuous H) {ε : ℝ} {U V : ℝ → E →L[ℂ] E}
    (hU : IsPropagator H ε U) (hV : IsPropagator H ε V) : EqOn U V (Icc 0 1) :=
  ForMathlib.linear_ode_unique (A := fun s => (-(I / ε)) • H s) (by fun_prop) hU.2 hV.2
    (hU.1.trans hV.1.symm)

omit [CompleteSpace E] in
/-- In finite dimension a left inverse of an operator is a right inverse. -/
lemma mul_eq_one_comm_clm [FiniteDimensional ℂ E] {A B : E →L[ℂ] E} (h : A * B = 1) :
    B * A = 1 := by
  have h' : (A : E →ₗ[ℂ] E) * (B : E →ₗ[ℂ] E) = 1 := by
    rw [← ContinuousLinearMap.toLinearMap_mul, h, ContinuousLinearMap.toLinearMap_one]
  have := mul_eq_one_comm.mp h'
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_mul, this, ContinuousLinearMap.toLinearMap_one]

/-- `star (-(i/ε) H) = -(-(i/ε) H)` for self-adjoint `H`. -/
lemma star_gen {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (ε : ℝ) :
    star ((-(I / ε)) • H) = -((-(I / ε)) • H) := by
  rw [star_smul, hH.star_eq, ← neg_smul]
  congr 1
  simp [Complex.conj_ofReal]
  ring

/-- **The propagator is unitary.** -/
theorem propagator_mem_unitary [FiniteDimensional ℂ E] {H : ℝ → E →L[ℂ] E}
    (hsa : ∀ s, IsSelfAdjoint (H s)) {ε : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsPropagator H ε U)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : U s ∈ unitary (E →L[ℂ] E) := by
  have hG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t => star (U t) * U t) 0 (Icc 0 1) t := by
    intro t ht
    have h := ((hU.2 t ht).star).mul (hU.2 t ht)
    convert h using 1
    rw [star_mul, star_gen (hsa t), mul_neg, neg_mul, mul_assoc, neg_add_cancel]
  have hc := norm_image_sub_le_of_norm_deriv_le_segment' hG (C := 0) (fun _ _ => by simp) s hs
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, hU.1, star_one, mul_one] at hc
  exact Unitary.mem_iff.mpr ⟨hc, mul_eq_one_comm_clm hc⟩

end QM
