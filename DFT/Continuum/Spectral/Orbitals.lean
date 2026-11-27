/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Ground
import ForMathlib.Analysis.SturmLiouville.Expand

/-!
# Orthonormal eigenfunctions and the one-particle bound in the box

For a box potential `v`, the `N` lowest eigenfunctions of `-d²/dx² + v` (from the Green-operator
eigenbasis, `ForMathlib/Analysis/SturmLiouville/Expand`) give the one-particle bound used for
`N` free fermions:

`Λ ‖ψ‖² - Σⱼ (Λ - λⱼ) ⟪φⱼ, ψ⟫² ≤ ⟨ψ, h ψ⟩`.

* `exists_orbitals`: **the one-particle bound**, with `N` orthonormal `C²` eigenfunctions.
-/

namespace DFT.Continuum.Spectral

open MeasureTheory Set Filter Topology SturmLiouville CompactEigenbasis Box

/-! ### The one-particle bound -/

/-- **`N` orthonormal eigenfunctions and the one-particle bound.** For a box potential `v` and
`N = n + 1` there are `C²` eigenfunctions `φⱼ` (`-φⱼ'' + v φⱼ = λⱼ φⱼ`), orthonormal in
`L²(0, 1)`, and `Λ ≥ λⱼ` with `Λ ‖ψ‖² - Σⱼ (Λ - λⱼ) ⟪φⱼ, ψ⟫² ≤ ⟨ψ, h ψ⟩` for every state `ψ`. -/
theorem exists_orbitals (v : Pot) (n : ℕ) : ∃ (φ : Fin (n + 1) → ℝ → ℝ) (lam : Fin (n + 1) → ℝ)
    (Λ : ℝ), (∀ j, φ j ∈ SturmLiouville.Dom) ∧
    (∀ j, ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv (φ j)) x = (ext v x - lam j) * φ j x) ∧
    (∀ j k, ∫ x, φ j x * φ k x ∂μ1 = if j = k then 1 else 0) ∧ (∀ j, lam j ≤ Λ) ∧
    ∀ ψ ∈ SturmLiouville.Dom, Λ * ip (μ := μ1) ψ ψ - ∑ j, (Λ - lam j) * (∫ x, φ j x * ψ x ∂μ1) ^ 2 ≤
      Q Box.setting v ψ := by
  classical
  set E := -‖v‖
  have hWc := continuous_Wof v E
  have hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ Wof v E t := fun t _ => by
    have := abs_ext_le v t
    simp only [Wof, E, sub_neg_eq_add]
    linarith [neg_abs_le (ext v t)]
  obtain ⟨f, hf⟩ := exists_injective_idx hWc hW0 (n + 1)
  obtain ⟨S, hS, hord⟩ := exists_top (mu hWc) (mu_pos hWc hW0)
    (fun δ hδ => finite_ge (isCompactOperator_Gop hWc) (isSymmetric_Gop hWc)
      (fun _ hf => Gop_injective hWc hW0 hf) hδ) (n + 1) ⟨f, hf⟩
  have hne : S.Nonempty := Finset.card_pos.1 (by rw [hS]; exact Nat.succ_pos n)
  set e : Fin (n + 1) ≃ S := (Fintype.equivFinOfCardEq (by simp [hS])).symm
  set idx : Fin (n + 1) → Idx hWc := fun j => (e j : Idx hWc)
  have hidx : ∀ j k, idx j = idx k ↔ j = k := fun j k =>
    ⟨fun h => e.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  set Λ' := S.sup' hne fun i => (mu hWc i)⁻¹
  refine ⟨fun j => rep hWc hW0 (idx j), fun j => (mu hWc (idx j))⁻¹ + E, Λ' + E,
    fun j => rep_mem hWc hW0 _, fun j x hx => ?_, fun j k => ?_, fun j => ?_, fun ψ hψ => ?_⟩
  · rw [rep_ode hWc hW0 _ x hx]; simp only [Wof]; ring
  · rw [rep_orthonormal]; exact if_congr (hidx j k) rfl rfl
  · simp only [add_le_add_iff_right]
    exact Finset.le_sup' (fun i => (mu hWc i)⁻¹) (e j).2
  · -- the expansion, with the terms outside `S` dropped
    have hF := hasSum_form hWc hW0 hψ
    have hN := hasSum_sq hWc hW0 hψ.1.continuous
    have hD := hF.sub (hN.mul_left Λ')
    have hle := sum_le_hasSum S (fun i hi => by
      have hΛ : Λ' ≤ (mu hWc i)⁻¹ := Finset.sup'_le hne _ fun s hs =>
        inv_anti₀ (mu_pos hWc hW0 i) (hord s hs i hi)
      have := sq_nonneg (coef hWc hW0 i ψ)
      nlinarith) hD
    have hQ := Q_sub_eq v E hψ
    have hsum : ∑ i ∈ S, ((mu hWc i)⁻¹ * coef hWc hW0 i ψ ^ 2 - Λ' * coef hWc hW0 i ψ ^ 2) =
        ∑ j, ((mu hWc (idx j))⁻¹ * coef hWc hW0 (idx j) ψ ^ 2 -
          Λ' * coef hWc hW0 (idx j) ψ ^ 2) := by
      rw [← Finset.sum_coe_sort S]
      exact (e.sum_comp (fun i : S => (mu hWc i)⁻¹ * coef hWc hW0 i ψ ^ 2 -
        Λ' * coef hWc hW0 i ψ ^ 2)).symm
    have hneg : ∑ j, (Λ' + E - ((mu hWc (idx j))⁻¹ + E)) *
        (∫ x, rep hWc hW0 (idx j) x * ψ x ∂μ1) ^ 2 =
        -∑ j, ((mu hWc (idx j))⁻¹ * coef hWc hW0 (idx j) ψ ^ 2 -
          Λ' * coef hWc hW0 (idx j) ψ ^ 2) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [coef]; ring
    rw [hneg]
    rw [hsum] at hle
    simp only [ip] at hQ ⊢
    linarith

end DFT.Continuum.Spectral
