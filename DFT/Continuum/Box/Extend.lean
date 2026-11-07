/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Regularity of ODE solutions and cutoff extension

* `contDiffOn_sol`: the first component of a solution of `(ψ, ψ')' = (ψ', W ψ)` with continuous
  `W` is `C²`.
* `exists_contDiff_ext`: a function that is `C²` on `(-1, 2)` agrees on `(-1/2, 3/2)` with a `C²`
  function on all of `ℝ` (multiply by a smooth cutoff).
-/

namespace DFT

namespace Continuum

namespace Box

open Set Filter Topology Metric

lemma two_eq_one_add_one : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num

lemma one_eq_zero_add_one : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num

/-- A solution of the ODE is `C²` in its first component. -/
theorem contDiffOn_sol {W : ℝ → ℝ} (hW : Continuous W) {α : ℝ → ℝ × ℝ}
    (hd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt α (field W t (α t)) t) :
    ContDiffOn ℝ 2 (fun t => (α t).1) (Ioo (-1 : ℝ) 2) := by
  set U := Ioo (-1 : ℝ) 2
  have hU : IsOpen U := isOpen_Ioo
  have h1 : ∀ t ∈ U, HasDerivAt (fun s => (α s).1) (α t).2 t := fun t ht => (hd t ht).fst
  have h2 : ∀ t ∈ U, HasDerivAt (fun s => (α s).2) (W t * (α t).1) t := fun t ht =>
    (hd t ht).snd
  have hc1 : ContinuousOn (fun t => (α t).1) U := fun t ht =>
    (h1 t ht).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fun t => (α t).2) U := fun t ht =>
    (h2 t ht).continuousAt.continuousWithinAt
  -- the second component is `C¹`
  have hC1 : ContDiffOn ℝ 1 (fun t => (α t).2) U := by
    rw [one_eq_zero_add_one, contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨fun t ht => (h2 t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    refine ((hW.continuousOn).mul hc1).congr fun t ht => ?_
    exact (h2 t ht).deriv
  rw [two_eq_one_add_one, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun t ht => (h1 t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  exact hC1.congr fun t ht => (h1 t ht).deriv

/-- Cutoff extension: a function that is `C²` on `(-1, 2)` agrees on `(-1/2, 3/2)` with a `C²`
function on `ℝ`. -/
theorem exists_contDiff_ext {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ 2 ψ (Ioo (-1 : ℝ) 2)) :
    ∃ ψe : ℝ → ℝ, ContDiff ℝ 2 ψe ∧ ∀ x ∈ Ioo (-1 / 2 : ℝ) (3 / 2), ψe x = ψ x := by
  let χ : ContDiffBump (1 / 2 : ℝ) := ⟨1, 7 / 5, by norm_num, by norm_num⟩
  have hball : closedBall (1 / 2 : ℝ) (7 / 5) ⊆ Ioo (-1 : ℝ) 2 := by
    rw [Real.closedBall_eq_Icc]
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨fun x => χ x * ψ x, ?_, fun x hx => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ioo (-1 : ℝ) 2
    · exact (χ.contDiff.contDiffAt).mul (hψ.contDiffAt (isOpen_Ioo.mem_nhds hx))
    · have hnot : x ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        exact fun h => hx (hball h)
      have hev : (fun y => χ y * ψ y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : χ x = 1 := by
      apply χ.one_of_mem_closedBall
      change x ∈ closedBall (1 / 2 : ℝ) 1
      rw [Real.closedBall_eq_Icc]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simp [h1]

end Box

end Continuum

end DFT
