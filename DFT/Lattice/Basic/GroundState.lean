/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Ground states on finite-dimensional real Hilbert spaces

* `qf M ψ = ⟨ψ, M ψ⟩`, and `IsGroundState M ψ`: `ψ ≠ 0` minimises the Rayleigh quotient (written
  without division).
* `isGroundState_eigen`: a ground state of a symmetric matrix is an eigenvector with eigenvalue
  `qf/‖ψ‖²`.
* `qf_smul`: `⟨rχ, H rχ⟩ = r² ⟨χ, H χ⟩`.
* `mulVec_eq_zero_of_psd`: a symmetric positive semidefinite matrix annihilates every vector on
  which its quadratic form vanishes.
-/

namespace DFT

section
open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- quadratic form ⟨ψ, M ψ⟩ -/
def qf (M : Matrix V V ℝ) (ψ : V → ℝ) : ℝ := ψ ⬝ᵥ (M *ᵥ ψ)

/-- ψ is a ground state of M: nonzero minimiser of the Rayleigh quotient (written without division)
-/
def IsGroundState (M : Matrix V V ℝ) (ψ : V → ℝ) : Prop :=
  ψ ≠ 0 ∧ ∀ φ : V → ℝ, qf M ψ * (φ ⬝ᵥ φ) ≤ qf M φ * (ψ ⬝ᵥ ψ)

/-- elementary: a·s + b·s² ≥ 0 for all s forces a = 0 -/
lemma lin_coeff_zero {a b : ℝ} (h : ∀ s : ℝ, 0 ≤ a * s + b * s ^ 2) : a = 0 := by
  by_contra ha
  have hc : 0 < |b| + 1 := by positivity
  have ha2 : 0 < a ^ 2 := by positivity
  have key := h (-a / (2 * (|b| + 1)))
  have hid : a * (-a / (2 * (|b| + 1))) + b * (-a / (2 * (|b| + 1))) ^ 2
      = a ^ 2 * (b - 2 * (|b| + 1)) / (4 * (|b| + 1) ^ 2) := by
    field_simp; ring
  have hneg : a ^ 2 * (b - 2 * (|b| + 1)) / (4 * (|b| + 1) ^ 2) < 0 := by
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_pos_of_neg ha2 (by linarith [le_abs_self b, abs_nonneg b])
    · positivity
  linarith

omit [DecidableEq V] in
/-- A ground state of a symmetric matrix is an eigenvector with eigenvalue `qf M ψ / ‖ψ‖²`. -/
theorem isGroundState_eigen {M : Matrix V V ℝ} (hM : M.IsSymm) {ψ : V → ℝ}
    (h : IsGroundState M ψ) : M *ᵥ ψ = (qf M ψ / (ψ ⬝ᵥ ψ)) • ψ := by
  classical
  obtain ⟨hne, hmin⟩ := h
  have hpos : 0 < ψ ⬝ᵥ ψ := by
    obtain ⟨i, hi⟩ : ∃ i, ψ i ≠ 0 := by
      by_contra hc; push Not at hc; exact hne (funext hc)
    have hle : ψ i * ψ i ≤ ψ ⬝ᵥ ψ := by
      simp only [dotProduct]
      exact Finset.single_le_sum (f := fun j => ψ j * ψ j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    have : 0 < ψ i * ψ i := mul_self_pos.mpr hi
    linarith
  have hsym : ∀ x y : V → ℝ, x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  have hlin : ∀ φ : V → ℝ, φ ⬝ᵥ (M *ᵥ ψ) * (ψ ⬝ᵥ ψ) = qf M ψ * (φ ⬝ᵥ ψ) := by
    intro φ
    have h0 := lin_coeff_zero (a := 2 * (φ ⬝ᵥ (M *ᵥ ψ) * (ψ ⬝ᵥ ψ) - qf M ψ * (φ ⬝ᵥ ψ)))
        (b := qf M φ * (ψ ⬝ᵥ ψ) - qf M ψ * (φ ⬝ᵥ φ)) (fun s => by
          have hs := hmin (ψ + s • φ)
          simp only [qf, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
            dotProduct_smul, smul_dotProduct, smul_eq_mul] at hs ⊢
          rw [hsym ψ φ, dotProduct_comm ψ φ] at hs
          nlinarith [hs])
    linarith
  have hdef : ψ ⬝ᵥ ψ = ∑ j, ψ j * ψ j := rfl
  funext i
  have hi := hlin (Pi.single i 1)
  simp [dotProduct, Pi.single_apply] at hi
  rw [← hdef] at hi
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith

omit [DecidableEq V] in
lemma qf_smul (H : Matrix V V ℝ) (r : ℝ) (χ : V → ℝ) : qf H (r • χ) = r ^ 2 * qf H χ := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

omit [DecidableEq V] in
/-- A symmetric positive semidefinite matrix annihilates every vector on which its quadratic
form vanishes. -/
lemma mulVec_eq_zero_of_psd {K : Matrix V V ℝ} (hS : Kᵀ = K)
    (hpsd : ∀ u, 0 ≤ u ⬝ᵥ (K *ᵥ u)) {w : V → ℝ} (hw : w ⬝ᵥ (K *ᵥ w) = 0) : K *ᵥ w = 0 := by
  classical
  funext i
  set e : V → ℝ := Pi.single i 1
  have hwK : w ⬝ᵥ (K *ᵥ e) = (K *ᵥ w) i := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hS]
    simp [e, dotProduct, Pi.single_apply]
  have heK : e ⬝ᵥ (K *ᵥ w) = (K *ᵥ w) i := by simp [e, dotProduct, Pi.single_apply]
  have hee : e ⬝ᵥ (K *ᵥ e) = K i i := by
    simp [e, dotProduct, mulVec, Pi.single_apply]
  have key : ∀ s : ℝ, 0 ≤ (2 * (K *ᵥ w) i) * s + K i i * s ^ 2 := by
    intro s
    have h := hpsd (w + s • e)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hw, hwK, heK, hee] at h
    nlinarith [h]
  have := lin_coeff_zero key
  simp only [Pi.zero_apply]
  linarith

end

end DFT
