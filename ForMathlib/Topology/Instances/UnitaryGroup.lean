/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic

/-!
# The unitary group of complex matrices is compact

`unitaryGroup n ℂ = {u | u† u = 1}` is closed, and the entries of a unitary matrix have modulus at
most `1` (its columns are unit vectors), so it is a closed subset of a product of closed discs.

## Main results

* `Matrix.isCompact_unitaryGroup`.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entries of a unitary matrix have modulus at most `1`. -/
lemma norm_apply_le_one_of_mem_unitaryGroup {u : Matrix n n ℂ} (hu : u ∈ unitaryGroup n ℂ)
    (i j : n) : ‖u i j‖ ≤ 1 := by
  have h := congrFun (congrFun ((mem_unitaryGroup_iff').mp hu) j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have hs : ∑ k, ‖u k j‖ ^ 2 = 1 := by
    have := congrArg Complex.re h
    simp only [star_apply, Complex.re_sum, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  have hle : ‖u i j‖ ^ 2 ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (f := fun k => ‖u k j‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (u i j)]

/-- **The unitary group of complex matrices is compact.** -/
theorem isCompact_unitaryGroup : IsCompact (unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have hclosed : IsClosed (unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
    have : (unitaryGroup n ℂ : Set (Matrix n n ℂ)) = {u | star u * u = 1} := by
      ext u; exact mem_unitaryGroup_iff'
    rw [this]
    exact isClosed_eq ((continuous_id.matrix_map continuous_star).matrix_transpose.matrix_mul
      continuous_id) continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : n =>
      Set.pi Set.univ fun _ : n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hbox.of_isClosed_subset hclosed fun u hu => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => norm_apply_le_one_of_mem_unitaryGroup hu i j

end Matrix
