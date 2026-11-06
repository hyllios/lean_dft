/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.StrongPotential.Resolvent

/-!
# Strong-potential coefficients of a Kronecker sum

Two independent systems `A₁`, `A₂` combine into the Kronecker sum `A₁ ⊗ 1 + 1 ⊗ A₂` on pairs of
configurations (two species that do not hop into each other).

* `T_eq_layer_pow`: the top coefficients `T_k(y)` are the entries of the `k`-th power of the layer
  matrix `layerMat` (diagonal `w`, plus the hops that increase the distance by one).
* `T_kronSum`: for a Kronecker sum, `T_k(y₁, y₂) = Σ_a (k choose a) T¹_a(y₁) T²_{k-a}(y₂)`.
* `alpha_kronSum`: the diagonal divided-difference coefficients factorise,
  `α_{(y₁,y₂)}(y₁,y₂) = α¹_{y₁}(y₁) α²_{y₂}(y₂)`.
-/

namespace DFT

open Matrix
open scoped Kronecker

section

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The layer matrix: `w` on the diagonal, and the entries of `A` that increase `d` by one. -/
noncomputable def layerMat (A : Matrix C C ℝ) (w : C → ℝ) (d : C → ℕ) : Matrix C C ℝ :=
  fun y z => if z = y then w y else if d z + 1 = d y then A y z else 0

/-- The top coefficients are the entries of the powers of the layer matrix. -/
theorem T_eq_layer_pow {A : Matrix C C ℝ} (w : C → ℝ) {d : C → ℕ} (hL : Lip A d) {c : C}
    (hc : d c = 0) (k : ℕ) (y : C) : T A w d c k y = (layerMat A w d ^ k) y c := by
  induction k generalizing y with
  | zero =>
    rw [T_zero w hc, pow_zero, Matrix.one_apply]
  | succ k ih =>
    rw [T_succ w hL hc, pow_succ', Matrix.mul_apply,← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
    simp only [layerMat, ite_true, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    rw [ite_eq_right (Finset.ne_of_mem_erase hz)]
    split_ifs <;> simp

end

section

variable {C₁ C₂ : Type*} [Fintype C₁] [DecidableEq C₁] [Fintype C₂] [DecidableEq C₂]

/-- Kronecker sum `A₁ ⊗ 1 + 1 ⊗ A₂`: two species that hop independently. -/
def kronSum (A₁ : Matrix C₁ C₁ ℝ) (A₂ : Matrix C₂ C₂ ℝ) : Matrix (C₁ × C₂) (C₁ × C₂) ℝ :=
  A₁ ⊗ₖ (1 : Matrix C₂ C₂ ℝ) + (1 : Matrix C₁ C₁ ℝ) ⊗ₖ A₂

omit [Fintype C₁] [Fintype C₂] in
lemma kronSum_apply (A₁ : Matrix C₁ C₁ ℝ) (A₂ : Matrix C₂ C₂ ℝ) (y z : C₁ × C₂) :
    kronSum A₁ A₂ y z = A₁ y.1 z.1 * (1 : Matrix C₂ C₂ ℝ) y.2 z.2 +
      (1 : Matrix C₁ C₁ ℝ) y.1 z.1 * A₂ y.2 z.2 := by
  simp [kronSum, Matrix.kroneckerMap_apply]

omit [Fintype C₁] [Fintype C₂] in
lemma kronSum_isSymm {A₁ : Matrix C₁ C₁ ℝ} {A₂ : Matrix C₂ C₂ ℝ} (h₁ : A₁.IsSymm)
    (h₂ : A₂.IsSymm) : (kronSum A₁ A₂).IsSymm := by
  ext y z
  simp only [Matrix.transpose_apply, kronSum_apply, Matrix.one_apply]
  rw [← h₁.apply y.1 z.1, ← h₂.apply y.2 z.2]
  simp only [eq_comm]

omit [Fintype C₁] [Fintype C₂] in
/-- The hop distance of a Kronecker sum is the sum of the two hop distances. -/
lemma lip_kronSum {A₁ : Matrix C₁ C₁ ℝ} {A₂ : Matrix C₂ C₂ ℝ} {d₁ : C₁ → ℕ} {d₂ : C₂ → ℕ}
    (h₁ : Lip A₁ d₁) (h₂ : Lip A₂ d₂) :
    Lip (kronSum A₁ A₂) (fun y => d₁ y.1 + d₂ y.2) := by
  intro y z hyz hA
  simp only [kronSum_apply, Matrix.one_apply] at hA
  by_cases e2 : y.2 = z.2
  · have e1 : y.1 ≠ z.1 := fun e1 => hyz (Prod.ext e1 e2)
    rw [ite_eq_left e2, ite_eq_right e1] at hA
    have := h₁ y.1 z.1 e1 (by simpa using hA)
    simp only [e2]; omega
  · rw [ite_eq_right e2] at hA
    by_cases e1 : y.1 = z.1
    · rw [ite_eq_left e1] at hA
      have := h₂ y.2 z.2 e2 (by simpa using hA)
      simp only [e1]; omega
    · rw [ite_eq_right e1] at hA; simp at hA

omit [Fintype C₁] [Fintype C₂] in
/-- The layer matrix of a Kronecker sum is the Kronecker sum of the layer matrices. -/
lemma layerMat_kronSum (A₁ : Matrix C₁ C₁ ℝ) (A₂ : Matrix C₂ C₂ ℝ) (w₁ : C₁ → ℝ) (w₂ : C₂ → ℝ)
    (d₁ : C₁ → ℕ) (d₂ : C₂ → ℕ) :
    layerMat (kronSum A₁ A₂) (fun y => w₁ y.1 + w₂ y.2) (fun y => d₁ y.1 + d₂ y.2) =
      kronSum (layerMat A₁ w₁ d₁) (layerMat A₂ w₂ d₂) := by
  ext y z
  rw [kronSum_apply]
  simp only [layerMat, kronSum_apply, Matrix.one_apply]
  by_cases e1 : z.1 = y.1 <;> by_cases e2 : z.2 = y.2
  · have : z = y := Prod.ext e1 e2
    simp [this]
  · have hne : z ≠ y := fun h => e2 (h ▸ rfl)
    simp only [hne, e1, e2, ite_true, ite_false, ite_eq_right (Ne.symm e2)]
    split_ifs <;> first | omega | simp
  · have hne : z ≠ y := fun h => e1 (h ▸ rfl)
    simp only [hne, e1, e2, ite_true, ite_false, ite_eq_right (Ne.symm e1)]
    split_ifs <;> first | omega | simp
  · have hne : z ≠ y := fun h => e1 (h ▸ rfl)
    simp [hne, e1, e2, Ne.symm e1, Ne.symm e2]

lemma kron_one_pow (B : Matrix C₁ C₁ ℝ) (k : ℕ) :
    (B ⊗ₖ (1 : Matrix C₂ C₂ ℝ)) ^ k = (B ^ k) ⊗ₖ (1 : Matrix C₂ C₂ ℝ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← mul_kronecker_mul, one_mul, pow_succ]

lemma one_kron_pow (B : Matrix C₂ C₂ ℝ) (k : ℕ) :
    ((1 : Matrix C₁ C₁ ℝ) ⊗ₖ B) ^ k = (1 : Matrix C₁ C₁ ℝ) ⊗ₖ (B ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← mul_kronecker_mul, one_mul, pow_succ]

/-- Powers of a Kronecker sum: the binomial theorem for the two commuting terms. -/
lemma kronSum_pow_apply (B₁ : Matrix C₁ C₁ ℝ) (B₂ : Matrix C₂ C₂ ℝ) (k : ℕ) (y z : C₁ × C₂) :
    (kronSum B₁ B₂ ^ k) y z =
      ∑ a ∈ Finset.range (k + 1), (B₁ ^ a) y.1 z.1 * (B₂ ^ (k - a)) y.2 z.2 * (k.choose a) := by
  have hc : Commute (B₁ ⊗ₖ (1 : Matrix C₂ C₂ ℝ)) ((1 : Matrix C₁ C₁ ℝ) ⊗ₖ B₂) := by
    rw [Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp
  rw [kronSum, hc.add_pow, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [kron_one_pow, one_kron_pow, ← mul_kronecker_mul, one_mul, mul_one]
  rw [show ((k.choose a : ℕ) : Matrix (C₁ × C₂) (C₁ × C₂) ℝ) = (k.choose a : ℝ) • 1 by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]]
  rw [mul_smul_comm, mul_one, Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
  ring

variable {A₁ : Matrix C₁ C₁ ℝ} {A₂ : Matrix C₂ C₂ ℝ} (w₁ : C₁ → ℝ) (w₂ : C₂ → ℝ)
  {d₁ : C₁ → ℕ} {d₂ : C₂ → ℕ} (h₁ : Lip A₁ d₁) (h₂ : Lip A₂ d₂) {c₁ : C₁} {c₂ : C₂}
  (hc₁ : d₁ c₁ = 0) (hc₂ : d₂ c₂ = 0)

include h₁ h₂ hc₁ hc₂ in
/-- **Top coefficients of a Kronecker sum.** -/
theorem T_kronSum (k : ℕ) (y : C₁ × C₂) :
    T (kronSum A₁ A₂) (fun y => w₁ y.1 + w₂ y.2) (fun y => d₁ y.1 + d₂ y.2) (c₁, c₂) k y =
      ∑ a ∈ Finset.range (k + 1),
        T A₁ w₁ d₁ c₁ a y.1 * T A₂ w₂ d₂ c₂ (k - a) y.2 * (k.choose a) := by
  rw [T_eq_layer_pow _ (lip_kronSum h₁ h₂) (by simp [hc₁, hc₂]), layerMat_kronSum,
    kronSum_pow_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [T_eq_layer_pow w₁ h₁ hc₁, T_eq_layer_pow w₂ h₂ hc₂]

include h₁ h₂ hc₁ hc₂ in
/-- **The diagonal coefficients of a Kronecker sum factorise.** -/
theorem alpha_kronSum (hw₁ : Function.Injective w₁) (hw₂ : Function.Injective w₂)
    (hw : Function.Injective (fun y : C₁ × C₂ => w₁ y.1 + w₂ y.2)) (y : C₁ × C₂) :
    alphaRep (kronSum A₁ A₂) (fun y => w₁ y.1 + w₂ y.2) hw (fun y => d₁ y.1 + d₂ y.2)
        (lip_kronSum h₁ h₂) (c₁, c₂) (by simp [hc₁, hc₂]) y y =
      alphaRep A₁ w₁ hw₁ d₁ h₁ c₁ hc₁ y.1 y.1 * alphaRep A₂ w₂ hw₂ d₂ h₂ c₂ hc₂ y.2 y.2 := by
  set α := alphaRep (kronSum A₁ A₂) (fun y => w₁ y.1 + w₂ y.2) hw (fun y => d₁ y.1 + d₂ y.2)
    (lip_kronSum h₁ h₂) (c₁, c₂) (by simp [hc₁, hc₂]) y
  set α₁ := alphaRep A₁ w₁ hw₁ d₁ h₁ c₁ hc₁ y.1
  set α₂ := alphaRep A₂ w₂ hw₂ d₂ h₂ c₂ hc₂ y.2
  have key : ∀ k : ℕ, ∑ z, α z * (w₁ z.1 + w₂ z.2) ^ k =
      ∑ z : C₁ × C₂, α₁ z.1 * α₂ z.2 * (w₁ z.1 + w₂ z.2) ^ k := by
    intro k
    have e := alphaRep_rep hw (lip_kronSum h₁ h₂) (c := (c₁, c₂)) (by simp [hc₁, hc₂]) y k
    rw [← e, T_kronSum w₁ w₂ h₁ h₂ hc₁ hc₂]
    simp only [alphaRep_rep hw₁ h₁ hc₁, alphaRep_rep hw₂ h₂ hc₂, add_pow, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Finset.sum_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro z₁ _
    apply Finset.sum_congr rfl; intro z₂ _
    ring
  have := ps_unique _ _ _ _ key (w₁ y.1 + w₂ y.2)
  have hfilt : Finset.univ.filter (fun z : C₁ × C₂ => w₁ z.1 + w₂ z.2 = w₁ y.1 + w₂ y.2) = {y} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hw h, fun h => h ▸ rfl⟩
  rw [hfilt, Finset.sum_singleton, Finset.sum_singleton] at this
  exact this

end

end DFT
