/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.Configurations
import QM.ManyBody.Fock

/-!
# The number operator

The occupation operator of mode `i` is `n̂_i = c_i† c_i` (`num i`); the total number operator is
`N̂ = Σ_i n̂_i` (`numTot`). On a configuration `s`, `n̂_i` multiplies by the occupation of `i` and `N̂`
by the number of occupied modes `|s|`. On `N`-particle configurations `s : Conf M N`, the eigenvalue of
`n̂_i` is the occupation `DFT.occF i s` of the lattice code.

## Main definitions

* `QM.ManyBody.num i`: `n̂_i = c_i† c_i`; `QM.ManyBody.numTot`: `N̂ = Σ_i n̂_i`.

## Main results

* `num_mulVec`, `num_mulVec_single`: `n̂_i |s⟩ = [i ∈ s] |s⟩`.
* `num_mulVec_single_conf`: for `s : Conf M N`, `n̂_i |s⟩ = occF i s |s⟩`.
* `numTot_mulVec`, `numTot_mulVec_single`: `N̂ |s⟩ = |s| |s⟩`.
* `num_isHermitian`, `numTot_isHermitian`: both are self-adjoint; `num_mul_num`: `n̂_i` is a projection.
* `numTotOp_isSelfAdjoint`: `N̂` is a self-adjoint bounded operator on the Fock Hilbert space.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-- The occupation operator `n̂_i = c_i† c_i` of mode `i`. -/
def num (i : Fin M) : FockOp M := cre i * ann i

/-- The total number operator `N̂ = Σ_i c_i† c_i`. -/
def numTot : FockOp M := ∑ i, num i

/-- `n̂_i` multiplies a function of configurations by the occupation of `i`. -/
theorem num_mulVec (i : Fin M) (v : Finset (Fin M) → ℂ) (u : Finset (Fin M)) :
    (num i *ᵥ v) u = (if i ∈ u then 1 else 0) * v u := by
  rw [num, ← Matrix.mulVec_mulVec, cre_mulVec]
  by_cases hu : i ∈ u
  · rw [ite_eq_left hu, ite_eq_left hu, ann_mulVec, ite_eq_left (Finset.notMem_erase i u),
      Finset.insert_erase hu, ← mul_assoc, jwSign_mul_self]
  · rw [ite_eq_right hu, ite_eq_right hu, zero_mul]

/-- `n̂_i |s⟩ = [i ∈ s] |s⟩`. -/
theorem num_mulVec_single (i : Fin M) (s : Finset (Fin M)) :
    num i *ᵥ Pi.single s 1 = (if i ∈ s then 1 else 0 : ℂ) • Pi.single s 1 := by
  funext u
  rw [num_mulVec, Pi.smul_apply, smul_eq_mul]
  by_cases hu : u = s
  · subst hu; rfl
  · simp [hu]

/-- On `N`-particle configurations, the eigenvalue of `n̂_i` is the occupation `occF i s` of the
lattice code. -/
theorem num_mulVec_single_conf {N : ℕ} (i : Fin M) (s : DFT.Conf M N) :
    num i *ᵥ Pi.single s.1 1 = (DFT.occF i s : ℂ) • Pi.single s.1 1 := by
  rw [num_mulVec_single, DFT.occF]
  split_ifs <;> simp

/-- `N̂` multiplies a function of configurations by the number of occupied modes. -/
theorem numTot_mulVec (v : Finset (Fin M) → ℂ) (u : Finset (Fin M)) :
    (numTot *ᵥ v) u = (u.card : ℂ) * v u := by
  rw [numTot, Matrix.sum_mulVec, Finset.sum_apply]
  simp_rw [num_mulVec, ← Finset.sum_mul]
  congr 1
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- `N̂ |s⟩ = |s| |s⟩`. -/
theorem numTot_mulVec_single (s : Finset (Fin M)) :
    numTot *ᵥ Pi.single s 1 = (s.card : ℂ) • Pi.single s 1 := by
  funext u
  rw [numTot_mulVec, Pi.smul_apply, smul_eq_mul]
  by_cases hu : u = s
  · subst hu; rfl
  · simp [hu]

/-- `n̂_i` is self-adjoint. -/
theorem num_isHermitian (i : Fin M) : (num i).IsHermitian := by
  rw [Matrix.IsHermitian, num, Matrix.conjTranspose_mul, ann, Matrix.conjTranspose_conjTranspose]

/-- `N̂` is self-adjoint. -/
theorem numTot_isHermitian : (numTot : FockOp M).IsHermitian := by
  rw [Matrix.IsHermitian, numTot, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => num_isHermitian i

/-- `n̂_i` is a projection: `n̂_i² = n̂_i`. -/
theorem num_mul_num (i : Fin M) : num i * num i = num i := by
  refine ext_of_mulVec fun v => ?_
  funext u
  rw [← Matrix.mulVec_mulVec, num_mulVec, num_mulVec]
  split_ifs <;> simp

/-- `N̂` as a bounded operator on the Fock (Hilbert) space. -/
noncomputable def numTotOp : Fock M →L[ℂ] Fock M := toFockCLM numTot

/-- `N̂` is a self-adjoint operator on the Fock space. -/
theorem numTotOp_isSelfAdjoint : IsSelfAdjoint (numTotOp : Fock M →L[ℂ] Fock M) := by
  unfold numTotOp
  rw [IsSelfAdjoint, ← map_star]
  exact congrArg toFockCLM numTot_isHermitian

end QM.ManyBody
