/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.Fock

/-!
# Second-quantized one-body operators

For a single-particle matrix `h`, the one-body operator on the Fock space is
`oneBody h = Σ_ij h_ij c_i† c_j`. A creation string `slaterVec τ = c_{τ 0}† ⋯ c_{τ (N-1)}† |∅⟩`
is the Fock vector of the (unnormalised, possibly zero) Slater determinant of the modes `τ`.

## Main definitions

* `QM.ManyBody.oneBody h`: the operator `Σ_ij h_ij c_i† c_j`.
* `QM.ManyBody.slaterVec τ`: the creation string `c_{τ 0}† ⋯ c_{τ (N-1)}† |∅⟩`.

## Main results

* `cre_ann_mul_cre`: `c_i† c_j c_a† = δ_ja c_i† + c_a† c_i† c_j` (from the anticommutation
  relations).
* `hop_mulVec_slaterVec`: `c_i† c_j` acts on a creation string as a derivation,
  `c_i† c_j (c_{τ 0}† ⋯ |∅⟩) = Σ_k [τ k = j] (the string with `τ k` replaced by `i`)`.
* `oneBody_mulVec_slaterVec`: the same for `Σ_ij h_ij c_i† c_j`.
* `oneBody_apply_eq_zero_of_card_ne`: `Σ_ij h_ij c_i† c_j` conserves the particle number.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-- The second-quantized one-body operator `Σ_ij h_ij c_i† c_j`. -/
noncomputable def oneBody (h : Matrix (Fin M) (Fin M) ℂ) : FockOp M :=
  ∑ i, ∑ j, h i j • (cre i * ann j)

/-- Commuting a hopping term `c_i† c_j` past a creation operator:
`c_i† c_j c_a† = δ_ja c_i† + c_a† c_i† c_j`. -/
theorem cre_ann_mul_cre (i j a : Fin M) :
    cre i * ann j * cre a = (if j = a then cre i else 0) + cre a * (cre i * ann j) := by
  have h1 : ann j * cre a = (if j = a then (1 : FockOp M) else 0) - cre a * ann j :=
    eq_sub_of_add_eq (ann_mul_cre_add j a)
  have h2 : cre i * cre a = -(cre a * cre i) := eq_neg_of_add_eq_zero_left (cre_mul_cre_add i a)
  rw [mul_assoc, h1, mul_sub, ← mul_assoc (cre i) (cre a), h2]
  split_ifs <;> noncomm_ring

/-- The creation string `c_{τ 0}† ⋯ c_{τ (N-1)}† |∅⟩`. -/
noncomputable def slaterVec : {N : ℕ} → (Fin N → Fin M) → Finset (Fin M) → ℂ
  | 0, _ => Pi.single ∅ 1
  | _ + 1, τ => cre (τ 0) *ᵥ slaterVec (Fin.tail τ)

lemma slaterVec_zero (τ : Fin 0 → Fin M) : slaterVec τ = Pi.single ∅ 1 := rfl

lemma slaterVec_succ {N : ℕ} (τ : Fin (N + 1) → Fin M) :
    slaterVec τ = cre (τ 0) *ᵥ slaterVec (Fin.tail τ) := rfl

/-- **`c_i† c_j` is a derivation on creation strings**: it replaces, one at a time, each
occurrence of the mode `j` by the mode `i`. -/
theorem hop_mulVec_slaterVec (i j : Fin M) {N : ℕ} (τ : Fin N → Fin M) :
    (cre i * ann j) *ᵥ slaterVec τ =
      ∑ k, if τ k = j then slaterVec (Function.update τ k i) else 0 := by
  induction N with
  | zero =>
    rw [slaterVec_zero, ← Matrix.mulVec_mulVec, ann_mulVec_single]
    simp
  | succ N ih =>
    rw [slaterVec_succ, Matrix.mulVec_mulVec, cre_ann_mul_cre, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ih, Fin.sum_univ_succ, Matrix.mulVec_sum]
    congr 1
    · by_cases h : τ 0 = j
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl, slaterVec_succ]
        simp
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h, Matrix.zero_mulVec]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have h0 : Function.update τ k.succ i 0 = τ 0 :=
        Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
      have ht : Fin.tail (Function.update τ k.succ i) = Function.update (Fin.tail τ) k i := by
        funext m
        simp only [Fin.tail, Function.update_apply, Fin.succ_inj]
      rw [show Fin.tail τ k = τ k.succ from rfl]
      by_cases hk : τ k.succ = j
      · rw [ite_eq_left hk, ite_eq_left hk, slaterVec_succ, h0, ht]
      · rw [ite_eq_right hk, ite_eq_right hk, Matrix.mulVec_zero]

/-- The one-body operator on a creation string:
`(Σ_ij h_ij c_i† c_j) |τ⟩ = Σ_k Σ_i h_{i, τ k} |τ with τ k replaced by i⟩`. -/
theorem oneBody_mulVec_slaterVec (h : Matrix (Fin M) (Fin M) ℂ) {N : ℕ} (τ : Fin N → Fin M) :
    oneBody h *ᵥ slaterVec τ =
      ∑ k, ∑ i, h i (τ k) • slaterVec (Function.update τ k i) := by
  rw [oneBody, Matrix.sum_mulVec]
  simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec, hop_mulVec_slaterVec, Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single (τ k)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- Matrix elements of `c_i† c_j` vanish between configurations of different particle number. -/
lemma hop_apply_eq_zero_of_card_ne (i j : Fin M) {s t : Finset (Fin M)} (hst : s.card ≠ t.card) :
    (cre i * ann j) s t = 0 := by
  simp only [Matrix.mul_apply, ann_apply, cre]
  refine Finset.sum_eq_zero fun u _ => ?_
  split_ifs with h1 h2
  · exfalso
    apply hst
    rw [h1.2, h2.2, Finset.card_insert_of_notMem h1.1, Finset.card_insert_of_notMem h2.1]
  all_goals simp

/-- **Particle-number conservation**: `Σ_ij h_ij c_i† c_j` has no matrix elements between
configurations with different numbers of particles. -/
theorem oneBody_apply_eq_zero_of_card_ne (h : Matrix (Fin M) (Fin M) ℂ) {s t : Finset (Fin M)}
    (hst : s.card ≠ t.card) : oneBody h s t = 0 := by
  simp [oneBody, Matrix.sum_apply, hop_apply_eq_zero_of_card_ne _ _ hst]

end QM.ManyBody
