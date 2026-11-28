/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean_dft contributors
-/
import DFT.Continuum.Line.NeumannKS.Hartree

/-!
# Ordered pair interactions and the Hartree derivative

Corso uses the ordered-pair convention in Eq. (2.2). Doubling the unordered kernel
gives the corresponding Hartree energy and derivative in Lemma 6.3.
-/

namespace DFT.Continuum.Line

open Set MeasureTheory SturmLiouville

theorem orderedPairSum {n : ℕ} (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ))
    (symm : ∀ s t, u (s, t) = u (t, s)) (x : Cfg n) :
    pairW ((2 : ℝ) • u) x =
      ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 ≠ p.2),
        sqExt u (x p.1) (x p.2) := by
  classical
  let lo := Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)
  let hi := Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.2 < p.1)
  let F := fun p : Fin (n + 1) × Fin (n + 1) => sqExt u (x p.1) (x p.2)
  have split : Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 ≠ p.2) = lo ∪ hi := by
    ext p
    simp only [lo, hi, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact ne_iff_lt_or_gt
  have disj : Disjoint lo hi := by
    refine Finset.disjoint_left.mpr fun p h₁ h₂ => ?_
    exact (asymm (Finset.mem_filter.mp h₁).2) (Finset.mem_filter.mp h₂).2
  have swap : (∑ p ∈ hi, F p) = ∑ p ∈ lo, F p := by
    exact Finset.sum_nbij' Prod.swap Prod.swap
      (fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
      (fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => symm _ _)
  rw [split, Finset.sum_union disj]
  change (∑ p ∈ lo, 2 * F p) = (∑ p ∈ lo, F p) + ∑ p ∈ hi, F p
  rw [swap, ← Finset.mul_sum, two_mul]

private theorem doubledForm (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) (ρ δ : H1E) :
    hartreeBE ((2 : ℝ) • u) ρ δ = 2 * hartreeBE u ρ δ := by
  change hartreeB _ (evE ρ) (evE δ) = 2 * hartreeB u (evE ρ) (evE δ)
  simp only [hartreeB_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  change (2 * sqExt u p.1 p.2) * _ = 2 * (sqExt u p.1 p.2 * _)
  ring

theorem orderedHartree (u : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ)) (ρ : H1E) :
    hartreeE ((2 : ℝ) • u) ρ = hartreeBE u ρ ρ ∧
      HasFDerivAt (hartreeE ((2 : ℝ) • u)) (hartreeBE u ρ + (hartreeBE u).flip ρ) ρ := by
  constructor
  · rw [hartreeE, doubledForm]
    ring
  · apply (hasFDerivAt_hartreeE ((2 : ℝ) • u) ρ).congr_fderiv
    ext δ
    change (1 / 2 : ℝ) * (hartreeBE ((2 : ℝ) • u) ρ δ + hartreeBE ((2 : ℝ) • u) δ ρ) = _
    rw [doubledForm, doubledForm]
    change _ = hartreeBE u ρ δ + hartreeBE u δ ρ
    ring

end DFT.Continuum.Line
