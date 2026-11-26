/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Physlib.Mathematics.ForMathlib.OneParameterSubgroups.Unitary
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Time evolution, the Heisenberg picture and the Ehrenfest theorem

For a bounded self-adjoint Hamiltonian `H` on a complex Hilbert space (in particular any
Hermitian operator in finite dimension), Physlib provides the unitary one-parameter group
`U(t) = e^{-itH}` (`UnitaryOneParameterGroup.ofSelfAdjoint`, with `ħ = 1`). This file adds the
Schrödinger equation with uniqueness, the Heisenberg picture and the Ehrenfest theorem.

## Main definitions

* `QM.evolution hH t = e^{-itH}`, `QM.heisenberg hH A t = U(t)† A U(t)`.

## Main results

* `evolution_mem_unitary`, `evolution_add`: `U(t)` is unitary and `U(t + s) = U(t) U(s)`.
* `hasDerivAt_evolution_apply` and `eq_evolution_of_hasDerivAt` (**Schrödinger equation**):
  `ψ(t) = U(t) ψ₀` solves `ψ' = -i H ψ`, and it is the only solution with `ψ(0) = ψ₀`.
* `hasDerivAt_heisenberg` (**Heisenberg picture**): `A'(t) = i [H, A(t)]`, and
  `inner_evolution_heisenberg`: `⟨ψ(t), A ψ(t)⟩ = ⟨ψ₀, A(t) ψ₀⟩`.
* `hasDerivAt_expectation` (**Ehrenfest**): `d/dt ⟨ψ(t), A ψ(t)⟩ = ⟨ψ(t), i [H, A] ψ(t)⟩`, and
  `expectation_const` (conservation laws): if `[H, A] = 0` the expectation value is constant,
  in particular `norm_evolution_apply` and `energy_const`.
-/

namespace QM

open Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {H : E →L[ℂ] E}

omit [CompleteSpace E] in
/-- The product rule for a path of `ℂ`-linear operators applied to a path of vectors, with the
derivative taken over `ℝ`. -/
lemma hasDerivAt_apply {c : ℝ → E →L[ℂ] E} {c' : E →L[ℂ] E} {u : ℝ → E} {u' : E} {t : ℝ}
    (hc : HasDerivAt c c' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => c s (u s)) (c' (u t) + c t u') t := by
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hc
  exact hr.clm_apply hu

/-- The time evolution `U(t) = e^{-itH}` of a bounded self-adjoint Hamiltonian. -/
noncomputable def evolution (hH : IsSelfAdjoint H) (t : ℝ) : E →L[ℂ] E :=
  UnitaryOneParameterGroup.ofSelfAdjoint hH t

variable (hH : IsSelfAdjoint H)

lemma evolution_eq_exp (t : ℝ) : evolution hH t = NormedSpace.exp ((-(t : ℂ) * I) • H) :=
  UnitaryOneParameterGroup.ofSelfAdjoint_apply hH t

/-- `U(t)` is unitary. -/
theorem evolution_mem_unitary (t : ℝ) : evolution hH t ∈ unitary (E →L[ℂ] E) :=
  (UnitaryOneParameterGroup.ofSelfAdjoint hH).mem_unitary t

/-- `U(t + s) = U(t) U(s)`. -/
theorem evolution_add (t s : ℝ) : evolution hH (t + s) = evolution hH t * evolution hH s :=
  AddChar.map_add_eq_mul _ t s

lemma evolution_zero : evolution hH 0 = 1 := AddChar.map_zero_eq_one _

lemma star_evolution (t : ℝ) : star (evolution hH t) = evolution hH (-t) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (UnitaryOneParameterGroup.ofSelfAdjoint hH).adjoint_eq t

/-- `H` commutes with `U(t)`. -/
lemma commute_evolution (t : ℝ) : H * evolution hH t = evolution hH t * H := by
  have h := (UnitaryOneParameterGroup.ofSelfAdjoint hH).commute_generator t
  rw [UnitaryOneParameterGroup.generator_ofSelfAdjoint] at h
  exact h.eq

lemma hasDerivAt_evolution (t : ℝ) :
    HasDerivAt (evolution hH) (evolution hH t * (-(I • H))) t := by
  have h := (UnitaryOneParameterGroup.ofSelfAdjoint hH).hasDerivAt t
  rw [UnitaryOneParameterGroup.generator_ofSelfAdjoint] at h
  exact h

/-- **Schrödinger equation**: `ψ(t) = U(t) ψ₀` satisfies `ψ'(t) = -i H ψ(t)`. -/
theorem hasDerivAt_evolution_apply (ψ₀ : E) (t : ℝ) :
    HasDerivAt (fun s => evolution hH s ψ₀) (-(I • H (evolution hH t ψ₀))) t := by
  have h := hasDerivAt_apply (hasDerivAt_evolution hH t) (hasDerivAt_const t ψ₀)
  simp only [map_zero, add_zero] at h
  convert h using 1
  have hc := congrArg (fun T : E →L[ℂ] E => T ψ₀) (commute_evolution hH t)
  simp only [mul_apply_eq_comp] at hc
  simp [mul_apply_eq_comp, hc]

/-- **Uniqueness**: a solution of `ψ' = -i H ψ` with `ψ(0) = ψ₀` is `U(t) ψ₀`. -/
theorem eq_evolution_of_hasDerivAt {φ : ℝ → E} (hφ : ∀ t, HasDerivAt φ (-(I • H (φ t))) t)
    (t : ℝ) : φ t = evolution hH t (φ 0) := by
  set g : ℝ → E := fun s => evolution hH (-s) (φ s)
  have hU : ∀ s, HasDerivAt (fun s => evolution hH (-s)) (-(evolution hH (-s) * (-(I • H)))) s :=
    fun s => by
      have h := HasDerivAt.scomp s (hasDerivAt_evolution hH (-s)) (hasDerivAt_neg s)
      simpa [Function.comp_def] using h
  have hg : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h := hasDerivAt_apply (hU s) (hφ s)
    convert h using 1
    simp [mul_apply_eq_comp, map_neg, map_smul]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
    (fun s => (hg s).deriv) t 0
  simp only [g, neg_zero, evolution_zero, _root_.one_apply_eq_self] at hconst
  rw [← hconst, ← mul_apply_eq_comp, ← evolution_add, add_neg_cancel, evolution_zero,
    _root_.one_apply_eq_self]

/-! ### The Heisenberg picture -/

/-- The Heisenberg operator `A(t) = U(t)† A U(t)`. -/
noncomputable def heisenberg (A : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  star (evolution hH t) * A * evolution hH t

/-- `⟨U(t) ψ₀, A U(t) ψ₀⟩ = ⟨ψ₀, A(t) ψ₀⟩`. -/
theorem inner_evolution_heisenberg (A : E →L[ℂ] E) (t : ℝ) (ψ₀ : E) :
    inner ℂ (evolution hH t ψ₀) (A (evolution hH t ψ₀)) = inner ℂ ψ₀ (heisenberg hH A t ψ₀) := by
  rw [heisenberg, mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

lemma star_evolution_mul_comm (t : ℝ) : star (evolution hH t) * H = H * star (evolution hH t) := by
  rw [star_evolution, commute_evolution]

/-- `U(t)† [H, A] U(t) = [H, A(t)]`. -/
lemma heisenberg_commutator (A : E →L[ℂ] E) (t : ℝ) :
    heisenberg hH (I • (H * A - A * H)) t =
      I • (H * heisenberg hH A t - heisenberg hH A t * H) := by
  set U := evolution hH t
  have hc : star U * H = H * star U := star_evolution_mul_comm hH t
  have hU : H * U = U * H := commute_evolution hH t
  have e1 : star U * (H * A) * U = H * (star U * A * U) := by
    rw [← mul_assoc, hc]; simp only [mul_assoc]
  have e2 : star U * (A * H) * U = star U * A * U * H := by
    simp only [mul_assoc]; rw [hU]
  simp only [heisenberg, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
  rw [e1, e2]

/-- **The Heisenberg equation** `A'(t) = i [H, A(t)]`. -/
theorem hasDerivAt_heisenberg (A : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (heisenberg hH A) (I • (H * heisenberg hH A t - heisenberg hH A t * H)) t := by
  have hs : HasDerivAt (fun s => star (evolution hH s)) (star (evolution hH t) * (I • H)) t := by
    have h := (UnitaryOneParameterGroup.ofSelfAdjoint hH).hasDerivAt_star t
    rw [UnitaryOneParameterGroup.generator_ofSelfAdjoint] at h
    exact h
  have h := (hs.mul (hasDerivAt_const t A)).mul (hasDerivAt_evolution hH t)
  refine h.congr_deriv ?_
  rw [← heisenberg_commutator]
  simp only [heisenberg, Pi.mul_apply, mul_zero, add_zero, mul_neg, mul_smul_comm, smul_mul_assoc,
    add_mul, mul_add, neg_mul, smul_add, smul_neg, sub_eq_add_neg]
  simp only [mul_assoc]
  rw [← commute_evolution hH t]

/-! ### The Ehrenfest theorem -/

/-- **The Ehrenfest theorem**: `d/dt ⟨ψ(t), A ψ(t)⟩ = ⟨ψ(t), i [H, A] ψ(t)⟩`. -/
theorem hasDerivAt_expectation (A : E →L[ℂ] E) (ψ₀ : E) (t : ℝ) :
    HasDerivAt (fun s => inner ℂ (evolution hH s ψ₀) (A (evolution hH s ψ₀)))
      (inner ℂ (evolution hH t ψ₀) ((I • (H * A - A * H)) (evolution hH t ψ₀))) t := by
  simp_rw [inner_evolution_heisenberg]
  have h := hasDerivAt_apply (hasDerivAt_heisenberg hH A t) (hasDerivAt_const t ψ₀)
  simp only [map_zero, add_zero] at h
  have h2 := (((innerSL ℂ ψ₀).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h)
  refine h2.congr_deriv ?_
  rw [heisenberg_commutator]
  rfl

/-- **Conservation law**: if `[H, A] = 0`, then `⟨ψ(t), A ψ(t)⟩` is constant. -/
theorem expectation_const {A : E →L[ℂ] E} (hA : H * A = A * H) (ψ₀ : E) (t : ℝ) :
    inner ℂ (evolution hH t ψ₀) (A (evolution hH t ψ₀)) = inner ℂ ψ₀ (A ψ₀) := by
  have hd : ∀ s, HasDerivAt (fun s => inner ℂ (evolution hH s ψ₀) (A (evolution hH s ψ₀))) 0 s := by
    intro s
    have h := hasDerivAt_expectation hH A ψ₀ s
    rwa [hA, sub_self, smul_zero, _root_.zero_apply, inner_zero_right] at h
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [evolution_zero] using this

/-- **Conservation of the norm.** -/
theorem norm_evolution_apply (ψ₀ : E) (t : ℝ) : ‖evolution hH t ψ₀‖ = ‖ψ₀‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (evolution_mem_unitary hH t) ψ₀

/-- **Conservation of the energy.** -/
theorem energy_const (ψ₀ : E) (t : ℝ) :
    inner ℂ (evolution hH t ψ₀) (H (evolution hH t ψ₀)) = inner ℂ ψ₀ (H ψ₀) :=
  expectation_const hH rfl ψ₀ t

end QM
