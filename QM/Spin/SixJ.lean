/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.Spin.Recoupling

/-!
# Recoupling of three angular momenta and the 6j symbols

Three ladders `f, g, h` of spins `j₁, j₂, j₃` couple in two orders. Coupling `j₁, j₂` to
`j₁₂ = j₁ + j₂ - a` and then `j₁₂, j₃` to `J = j₁₂ + j₃ - P` gives the states
`|(j₁ j₂) j₁₂, j₃; J M⟩`. Coupling `j₂, j₃` to `j₂₃ = j₂ + j₃ - b` and then `j₁, j₂₃` to
`J = j₁ + j₂₃ - Q` gives `|j₁, (j₂ j₃) j₂₃; J M⟩`. Both are ladders of the same system
(`IsLadder.couple`, `IsLadder.assoc`). When `f, g, h` are orthonormal, the overlap of the two is the
explicit sum `recoup3` of products of four Clebsch–Gordan coefficients (`dotp_recouple`).

## Main results

* `couple_couple_eq`, `couple_couple_assoc_eq`: the coupled states in the product basis.
* `dotp_recouple`: the overlap of the two couplings.
-/

namespace QM

open Finset

section Sums

lemma sum3_rotate (A B C : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c = ∑ b ∈ B, ∑ c ∈ C, ∑ a ∈ A, F a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma sum4_rotate (A B C D : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d =
      ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, F a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  exact sum3_rotate A C D _

end Sums

/-! ### The two couplings in the product basis -/

/-- The index set `{0..n₁} × {0..n₂} × {0..n₃}` of the product basis. -/
def idx3 (n₁ n₂ n₃ : ℕ) : Finset (ℕ × ℕ × ℕ) := range (n₁ + 1) ×ˢ range (n₂ + 1) ×ˢ range (n₃ + 1)

/-- The coordinates of `|(j₁ j₂) j₁₂, j₃; J M⟩` with `j₁₂ = j₁ + j₂ - a`, `J = j₁₂ + j₃ - P` and
`M = J - K`. -/
noncomputable def cU (n₁ n₂ n₃ a P K : ℕ) (i : ℕ × ℕ × ℕ) : ℝ :=
  ∑ w ∈ range (n₁ + n₂ - 2 * a + 1),
    cgCoeff n₁ n₂ a w i.1 i.2.1 * cgCoeff (n₁ + n₂ - 2 * a) n₃ P K w i.2.2

/-- The coordinates of `|j₁, (j₂ j₃) j₂₃; J M⟩` with `j₂₃ = j₂ + j₃ - b`, `J = j₁ + j₂₃ - Q` and
`M = J - K`. -/
noncomputable def cV (n₁ n₂ n₃ b Q K : ℕ) (i : ℕ × ℕ × ℕ) : ℝ :=
  ∑ u ∈ range (n₂ + n₃ - 2 * b + 1),
    cgCoeff n₂ n₃ b u i.2.1 i.2.2 * cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K i.1 u

/-- The recoupling coefficient `⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩`. -/
noncomputable def recoup3 (n₁ n₂ n₃ a b P Q K : ℕ) : ℝ :=
  ∑ i ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K i * cV n₁ n₂ n₃ b Q K i

section Expand

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

lemma sum_idx3 (n₁ n₂ n₃ : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    ∑ i ∈ idx3 n₁ n₂ n₃, F i.1 i.2.1 i.2.2 =
      ∑ t ∈ range (n₁ + 1), ∑ s ∈ range (n₂ + 1), ∑ r ∈ range (n₃ + 1), F t s r := by
  rw [idx3, Finset.sum_product]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_product _ _ _

omit [Fintype X] [Fintype Y] [Fintype Z] in
lemma couple_couple_eq (n₁ n₂ n₃ a P K : ℕ) (f : ℕ → X → ℝ) (g : ℕ → Y → ℝ)
    (h : ℕ → Z → ℝ) :
    couple (n₁ + n₂ - 2 * a) n₃ P (couple n₁ n₂ a f g) h K =
      ∑ i ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K i • tensor3 f g h i := by
  funext ⟨⟨x, y⟩, z⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tensor3]
  rw [sum_idx3 n₁ n₂ n₃ (fun t s r => cU n₁ n₂ n₃ a P K (t, s, r) * (f t x * g s y * h r z))]
  simp only [couple, cU, Finset.sum_mul, Finset.mul_sum]
  rw [sum4_rotate]
  conv_lhs => rw [sum3_rotate (range (n₃ + 1)) (range (n₁ + 1)) (range (n₂ + 1))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype X] [Fintype Y] [Fintype Z] in
lemma couple_couple_assoc_eq (n₁ n₂ n₃ b Q K : ℕ) (f : ℕ → X → ℝ) (g : ℕ → Y → ℝ)
    (h : ℕ → Z → ℝ) :
    (fun q : (X × Y) × Z =>
      couple n₁ (n₂ + n₃ - 2 * b) Q f (couple n₂ n₃ b g h) K (q.1.1, (q.1.2, q.2))) =
      ∑ i ∈ idx3 n₁ n₂ n₃, cV n₁ n₂ n₃ b Q K i • tensor3 f g h i := by
  funext ⟨⟨x, y⟩, z⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tensor3]
  rw [sum_idx3 n₁ n₂ n₃ (fun t s r => cV n₁ n₂ n₃ b Q K (t, s, r) * (f t x * g s y * h r z))]
  simp only [couple, cV, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum3_rotate]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

lemma mem_idx3 {n₁ n₂ n₃ : ℕ} {i : ℕ × ℕ × ℕ} :
    i ∈ idx3 n₁ n₂ n₃ ↔ i.1 ≤ n₁ ∧ i.2.1 ≤ n₂ ∧ i.2.2 ≤ n₃ := by
  simp only [idx3, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]

/-- **The overlap of the two couplings** of three orthonormal ladders is `recoup3`. -/
theorem dotp_recouple {n₁ n₂ n₃ : ℕ} {f : ℕ → X → ℝ} {g : ℕ → Y → ℝ} {h : ℕ → Z → ℝ}
    (hf : OrthoUpTo n₁ f) (hg : OrthoUpTo n₂ g) (hh : OrthoUpTo n₃ h) (a b P Q K : ℕ) :
    dotp (couple (n₁ + n₂ - 2 * a) n₃ P (couple n₁ n₂ a f g) h K)
      (fun q : (X × Y) × Z =>
        couple n₁ (n₂ + n₃ - 2 * b) Q f (couple n₂ n₃ b g h) K (q.1.1, (q.1.2, q.2))) =
      recoup3 n₁ n₂ n₃ a b P Q K := by
  rw [couple_couple_eq, couple_couple_assoc_eq, dotp_sum_smul]
  · rfl
  intro i hi j hj
  rw [mem_idx3] at hi hj
  rw [dotp_tensor3, hf _ hi.1 _ hj.1, hg _ hi.2.1 _ hj.2.1, hh _ hi.2.2 _ hj.2.2]
  obtain ⟨i1, i2, i3⟩ := i
  obtain ⟨j1, j2, j3⟩ := j
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

lemma orthoUpTo_one (n : ℕ) : OrthoUpTo n (oneVec n) := by
  intro t ht t' ht'
  unfold dotp oneVec
  rw [Finset.sum_eq_single ⟨t, Nat.lt_succ_of_le ht⟩]
  · simp only [ite_true]
    split_ifs <;> simp_all
  · intro x _ hx
    have : (x : ℕ) ≠ t := fun e => hx (Fin.ext e)
    simp [this]
  · simp

end Expand

/-! ### Single spins: independence of `M` -/

/-- `|(j₁ j₂) j₁₂, j₃; J M⟩` for three single spins. -/
noncomputable def stU (n₁ n₂ n₃ a P : ℕ) : ℕ → (Fin (n₁ + 1) × Fin (n₂ + 1)) × Fin (n₃ + 1) → ℝ :=
  couple (n₁ + n₂ - 2 * a) n₃ P (couple n₁ n₂ a (oneVec n₁) (oneVec n₂)) (oneVec n₃)

/-- `|j₁, (j₂ j₃) j₂₃; J M⟩` for three single spins, on the same index set. -/
noncomputable def stV (n₁ n₂ n₃ b Q : ℕ) : ℕ → (Fin (n₁ + 1) × Fin (n₂ + 1)) × Fin (n₃ + 1) → ℝ :=
  fun K q => couple n₁ (n₂ + n₃ - 2 * b) Q (oneVec n₁) (couple n₂ n₃ b (oneVec n₂) (oneVec n₃)) K
    (q.1.1, (q.1.2, q.2))

/-- The spin system of three single spins. -/
noncomputable abbrev sys3 (n₁ n₂ n₃ : ℕ) := prodSys (prodSys (oneSys n₁) (oneSys n₂)) (oneSys n₃)

lemma isLadder_stU {n₁ n₂ n₃ a P : ℕ} (ha : a ≤ min n₁ n₂) (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) :
    IsLadder (sys3 n₁ n₂ n₃) (n₁ + n₂ - 2 * a + n₃ - 2 * P) (stU n₁ n₂ n₃ a P) :=
  ((isLadder_one n₁).couple (isLadder_one n₂) ha).couple (isLadder_one n₃) hP

lemma isLadder_stV {n₁ n₂ n₃ b Q : ℕ} (hb : b ≤ min n₂ n₃) (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b)) :
    IsLadder (sys3 n₁ n₂ n₃) (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q) (stV n₁ n₂ n₃ b Q) :=
  ((isLadder_one n₁).couple ((isLadder_one n₂).couple (isLadder_one n₃) hb) hQ).assoc

lemma dotp_stU_stV (n₁ n₂ n₃ a b P Q K : ℕ) :
    dotp (stU n₁ n₂ n₃ a P K) (stV n₁ n₂ n₃ b Q K) = recoup3 n₁ n₂ n₃ a b P Q K :=
  dotp_recouple (orthoUpTo_one n₁) (orthoUpTo_one n₂) (orthoUpTo_one n₃) a b P Q K

/-- **The recoupling coefficient does not depend on `M`.** -/
theorem recoup3_const {n₁ n₂ n₃ a b P Q K : ℕ} (ha : a ≤ min n₁ n₂) (hb : b ≤ min n₂ n₃)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b))
    (hN : n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q)
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * P) :
    recoup3 n₁ n₂ n₃ a b P Q K = recoup3 n₁ n₂ n₃ a b P Q 0 := by
  rw [← dotp_stU_stV, ← dotp_stU_stV]
  have hV := isLadder_stV hb hQ
  rw [← hN] at hV
  exact (isLadder_stU ha hP).dotp_const hV hK

/-- **Couplings to different `J` or `M` are orthogonal.** -/
theorem dotp_stU_stV_eq_zero {n₁ n₂ n₃ a b P Q K K' : ℕ} (ha : a ≤ min n₁ n₂)
    (hb : b ≤ min n₂ n₃) (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃)
    (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b)) (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * P)
    (hK' : K' ≤ n₁ + (n₂ + n₃ - 2 * b) - 2 * Q)
    (hne : ¬(n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q ∧ K = K')) :
    dotp (stU n₁ n₂ n₃ a P K) (stV n₁ n₂ n₃ b Q K') = 0 :=
  (isLadder_stU ha hP).dotp_eq_zero (isLadder_stV hb hQ) hK hK' hne

/-! ### The 6j symbol -/

/-- The summand of the 6j symbol, with `yᵢ = jᵢ - mᵢ`. -/
noncomputable def sixJTerm (n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆ : ℕ) : ℝ :=
  (-1) ^ (y₁ + y₂ + y₃ + y₄ + y₅ + y₆) *
    (threeJ n₁ n₂ n₃ (n₁ - y₁) (n₂ - y₂) (n₃ - y₃) * threeJ n₁ n₅ n₆ y₁ (n₅ - y₅) y₆ *
      threeJ n₄ n₂ n₆ y₄ y₂ (n₆ - y₆) * threeJ n₄ n₅ n₃ (n₄ - y₄) y₅ y₃)

/-- **Wigner 6j symbol** `{j₁ j₂ j₃; j₄ j₅ j₆}` with `nᵢ = 2jᵢ`:
`Σ_{m₁…m₆} (-1)^(Σ (jᵢ - mᵢ)) (j₁ j₂ j₃; -m₁ -m₂ -m₃) (j₁ j₅ j₆; m₁ -m₅ m₆)
(j₄ j₂ j₆; m₄ m₂ -m₆) (j₄ j₅ j₃; -m₄ m₅ m₃)`. -/
noncomputable def sixJ (n₁ n₂ n₃ n₄ n₅ n₆ : ℕ) : ℝ :=
  ∑ y₁ ∈ range (n₁ + 1), ∑ y₂ ∈ range (n₂ + 1), ∑ y₃ ∈ range (n₃ + 1),
    ∑ y₄ ∈ range (n₄ + 1), ∑ y₅ ∈ range (n₅ + 1), ∑ y₆ ∈ range (n₆ + 1),
      sixJTerm n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆

lemma threeJ_eq_cg {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (h : Triad n₁ n₂ n₃) (hx : x₃ ≤ n₃) :
    threeJ n₁ n₂ n₃ x₁ x₂ x₃ = (-1) ^ (x₃ + n₁ + (n₁ + n₂ + n₃) / 2) / √((n₃ : ℝ) + 1) *
      cgCoeff n₁ n₂ ((n₁ + n₂ - n₃) / 2) (n₃ - x₃) x₁ x₂ := by
  rw [threeJ, ite_eq_left ⟨h, hx⟩]

lemma recoup_parity {n₁ n₂ n₃ n₁₂ n₂₃ N a b P Q t s w r K u : ℕ}
    (hA : n₁₂ + 2 * a = n₁ + n₂) (hB : n₂₃ + 2 * b = n₂ + n₃) (hC : N + 2 * P = n₁₂ + n₃)
    (hD : N + 2 * Q = n₁ + n₂₃) (a1 : a ≤ n₁) (a2 : a ≤ n₂) (b1 : b ≤ n₂) (b2 : b ≤ n₃)
    (p1 : P ≤ n₁₂) (p2 : P ≤ n₃) (q1 : Q ≤ n₁) (q2 : Q ≤ n₂₃) (ht : t ≤ n₁) (hs : s ≤ n₂)
    (hw : w ≤ n₁₂) (hr : r ≤ n₃) (hK : K ≤ N) (hu : u ≤ n₂₃) (hC1 : t + s = a + w)
    (hC2 : w + r = P + K) (hC3 : s + r = b + u) (hC4 : t + u = Q + K) :
    Even ((n₁ + n₂ + n₃ - a - P) + (n₁ - t + (n₂ - s) + w + (n₃ - r) + (N - K) + (n₂₃ - u)) +
      (n₁₂ - w + n₁ + (n₁ + n₂ - a)) + (n₁ + n₂₃ - Q) + (n₁ + n₂₃ - Q) +
      (N - K + n₁ + (n₁ + n₂₃ - Q)) + (n₂ + n₃ - b) + (n₂ + n₃ - b) +
      (n₂₃ - u + n₂ + (n₂ + n₃ - b)) + (N - K + n₁₂ + (n₁₂ + n₃ - P))) := by
  obtain ⟨t', rfl⟩ : ∃ t', n₁ = t + t' := ⟨n₁ - t, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', n₂ = s + s' := ⟨n₂ - s, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', n₃ = r + r' := ⟨n₃ - r, by omega⟩
  obtain ⟨K', rfl⟩ : ∃ K', N = K + K' := ⟨N - K, by omega⟩
  obtain ⟨u', rfl⟩ : ∃ u', n₂₃ = u + u' := ⟨n₂₃ - u, by omega⟩
  obtain ⟨w', rfl⟩ : ∃ w', n₁₂ = w + w' := ⟨n₁₂ - w, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  exact Nat.even_iff.mpr (by omega)

lemma recoup_alg (C1 C2 C3 C4 A B D ph sy e1 g1 g2 e4 h1 h2 e3 e2 : ℝ) (hA : 0 < A)
    (hB : 0 < B) (hD : 0 < D)
    (hs : ph * sy * e1 * g1 * g2 * e4 * h1 * h2 * e3 * e2 = 1 ∨ C1 * C2 * (C3 * C4) = 0) :
    C1 * C2 * (C3 * C4) = A * √(B * D) * ph *
      (sy * (e1 / √B * C1 * (g1 * (g2 * (e4 / √A * C4))) * (h1 * (h2 * (e3 / √D * C3))) *
        (e2 / √A * C2))) := by
  have sA := Real.sqrt_pos.mpr hA
  have sB := Real.sqrt_pos.mpr hB
  have sD := Real.sqrt_pos.mpr hD
  have hAA := Real.mul_self_sqrt hA.le
  have e : A * √(B * D) * ph *
      (sy * (e1 / √B * C1 * (g1 * (g2 * (e4 / √A * C4))) * (h1 * (h2 * (e3 / √D * C3))) *
        (e2 / √A * C2))) =
      (ph * sy * e1 * g1 * g2 * e4 * h1 * h2 * e3 * e2) * (C1 * C2 * (C3 * C4)) := by
    calc _ = (A * ((√A)⁻¹ * (√A)⁻¹)) * (√B * (√B)⁻¹) * (√D * (√D)⁻¹) *
          ((ph * sy * e1 * g1 * g2 * e4 * h1 * h2 * e3 * e2) * (C1 * C2 * (C3 * C4))) := by
          rw [Real.sqrt_mul hB.le]; simp only [div_eq_mul_inv]; ring
      _ = _ := by
          rw [mul_inv_cancel₀ sB.ne', mul_inv_cancel₀ sD.ne', ← mul_inv, hAA,
            mul_inv_cancel₀ hA.ne']
          ring
  rw [e]
  rcases hs with hs | hs
  · rw [hs, one_mul]
  · rw [hs, mul_zero]

/-- The termwise form of the recoupling formula. -/
lemma recoup_term {n₁ n₂ n₃ a b P Q : ℕ} (ha : a ≤ min n₁ n₂) (hb : b ≤ min n₂ n₃)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b))
    (hN : n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q)
    {t s w r K u : ℕ} (ht : t ≤ n₁) (hs : s ≤ n₂) (hw : w ≤ n₁ + n₂ - 2 * a) (hr : r ≤ n₃)
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * P) (hu : u ≤ n₂ + n₃ - 2 * b) :
    cgCoeff n₁ n₂ a w t s * cgCoeff (n₁ + n₂ - 2 * a) n₃ P K w r *
        (cgCoeff n₂ n₃ b u s r * cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K t u) =
      (((n₁ + n₂ - 2 * a + n₃ - 2 * P : ℕ) : ℝ) + 1) *
        √((((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * (((n₂ + n₃ - 2 * b : ℕ) : ℝ) + 1)) *
        (-1) ^ ((n₁ + n₂ + n₃ + (n₁ + n₂ - 2 * a + n₃ - 2 * P)) / 2) *
        sixJTerm n₁ n₂ (n₁ + n₂ - 2 * a) n₃ (n₁ + n₂ - 2 * a + n₃ - 2 * P) (n₂ + n₃ - 2 * b)
          (n₁ - t) (n₂ - s) w (n₃ - r) (n₁ + n₂ - 2 * a + n₃ - 2 * P - K)
          (n₂ + n₃ - 2 * b - u) := by
  generalize hn₁₂ : n₁ + n₂ - 2 * a = n₁₂ at *
  generalize hn₂₃ : n₂ + n₃ - 2 * b = n₂₃ at *
  generalize hNd : n₁₂ + n₃ - 2 * P = N at *
  have a1 : a ≤ n₁ := le_trans ha (min_le_left _ _)
  have a2 : a ≤ n₂ := le_trans ha (min_le_right _ _)
  have b1 : b ≤ n₂ := le_trans hb (min_le_left _ _)
  have b2 : b ≤ n₃ := le_trans hb (min_le_right _ _)
  have p1 : P ≤ n₁₂ := le_trans hP (min_le_left _ _)
  have p2 : P ≤ n₃ := le_trans hP (min_le_right _ _)
  have q1 : Q ≤ n₁ := le_trans hQ (min_le_left _ _)
  have q2 : Q ≤ n₂₃ := le_trans hQ (min_le_right _ _)
  clear ha hb hP hQ
  have hA : n₁₂ + 2 * a = n₁ + n₂ := by omega
  have hB : n₂₃ + 2 * b = n₂ + n₃ := by omega
  have hC : N + 2 * P = n₁₂ + n₃ := by omega
  have hD : N + 2 * Q = n₁ + n₂₃ := by omega
  clear hn₁₂ hn₂₃ hNd hN
  have h1 : Triad n₁ n₂ n₁₂ := ⟨by omega, by omega, by omega, Nat.even_iff.mpr (by omega)⟩
  have h2 : Triad n₁ n₂₃ N := ⟨by omega, by omega, by omega, Nat.even_iff.mpr (by omega)⟩
  have h3 : Triad n₂ n₃ n₂₃ := ⟨by omega, by omega, by omega, Nat.even_iff.mpr (by omega)⟩
  have h4 : Triad n₁₂ n₃ N := ⟨by omega, by omega, by omega, Nat.even_iff.mpr (by omega)⟩
  have d0 : (n₁ + n₂ + n₃ + N) / 2 = n₁ + n₂ + n₃ - a - P :=
    Nat.div_eq_of_eq_mul_left two_pos (by omega)
  have d1 : (n₁ + N + n₂₃) / 2 = n₁ + n₂₃ - Q :=
    Nat.div_eq_of_eq_mul_left two_pos (by omega)
  have d2 : (n₁ + n₂₃ + N) / 2 = n₁ + n₂₃ - Q :=
    Nat.div_eq_of_eq_mul_left two_pos (by omega)
  have d3 : (n₃ + n₂ + n₂₃) / 2 = n₂ + n₃ - b :=
    Nat.div_eq_of_eq_mul_left two_pos (by omega)
  have d4 : (n₂ + n₃ + n₂₃) / 2 = n₂ + n₃ - b :=
    Nat.div_eq_of_eq_mul_left two_pos (by omega)
  have d5 : (n₁ + n₂ + n₁₂) / 2 = n₁ + n₂ - a :=
    Nat.div_eq_of_eq_mul_left two_pos (by omega)
  have d6 : (n₁₂ + n₃ + N) / 2 = n₁₂ + n₃ - P :=
    Nat.div_eq_of_eq_mul_left two_pos (by omega)
  have f1 : (n₁ + n₂ - n₁₂) / 2 = a := by omega
  have f3 : (n₁ + n₂₃ - N) / 2 = Q := by omega
  have f5 : (n₂ + n₃ - n₂₃) / 2 = b := by omega
  have f7 : (n₁₂ + n₃ - N) / 2 = P := by omega
  unfold sixJTerm
  rw [Nat.sub_sub_self ht, Nat.sub_sub_self hs, Nat.sub_sub_self hr, Nat.sub_sub_self hK,
    Nat.sub_sub_self hu]
  have e2 := threeJ_reverse (n₁ := n₁) (n₂ := N) (n₃ := n₂₃) (x₁ := t) (x₂ := N - K) (x₃ := u)
    ht (Nat.sub_le _ _) hu
  rw [Nat.sub_sub_self hK, threeJ_swap23 n₁ n₂₃ N t u (N - K)] at e2
  have e3 := threeJ_reverse (n₁ := n₃) (n₂ := n₂) (n₃ := n₂₃) (x₁ := r) (x₂ := s)
    (x₃ := n₂₃ - u) hr hs (Nat.sub_le _ _)
  rw [Nat.sub_sub_self hu, threeJ_swap12 n₂ n₃ n₂₃ s r (n₂₃ - u)] at e3
  have f2 : n₁₂ - (n₁₂ - w) = w := Nat.sub_sub_self hw
  have f4 : N - (N - K) = K := Nat.sub_sub_self hK
  have f6 : n₂₃ - (n₂₃ - u) = u := Nat.sub_sub_self hu
  rw [e2, e3, threeJ_cyclic n₁₂ n₃ N w r (N - K)]
  clear e2 e3
  rw [threeJ_eq_cg h1 (Nat.sub_le _ _), threeJ_eq_cg h2 (Nat.sub_le _ _),
    threeJ_eq_cg h3 (Nat.sub_le _ _), threeJ_eq_cg h4 (Nat.sub_le _ _)]
  rw [f1, f2, f3, f4, f5, f6, f7]
  refine recoup_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity)
    (by positivity) ?_
  by_cases hz : cgCoeff n₁ n₂ a w t s * cgCoeff n₁₂ n₃ P K w r *
      (cgCoeff n₂ n₃ b u s r * cgCoeff n₁ n₂₃ Q K t u) = 0
  · exact Or.inr hz
  left
  have hC1 : t + s = a + w := by
    by_contra h; exact hz (by rw [cgCoeff_eq_zero h]; simp)
  have hC2 : w + r = P + K := by
    by_contra h; exact hz (by rw [cgCoeff_eq_zero (n₁ := n₁₂) h]; simp)
  have hC3 : s + r = b + u := by
    by_contra h; exact hz (by rw [cgCoeff_eq_zero (n₁ := n₂) h]; simp)
  have hC4 : t + u = Q + K := by
    by_contra h; exact hz (by rw [cgCoeff_eq_zero (n₂ := n₂₃) h]; simp)
  clear hz
  rw [d0, d1, d2, d3, d4, d5, d6]
  simp only [← pow_add]
  exact Even.neg_one_pow (recoup_parity hA hB hC hD a1 a2 b1 b2 p1 p2 q1 q2 ht hs hw hr hK hu
    hC1 hC2 hC3 hC4)

lemma sum_range_reflect' (n : ℕ) (f : ℕ → ℝ) :
    ∑ y ∈ range (n + 1), f y = ∑ t ∈ range (n + 1), f (n - t) := by
  rw [← Finset.sum_range_reflect]
  exact Finset.sum_congr rfl fun t _ => by rw [Nat.add_sub_cancel]

lemma recoup3_expand (n₁ n₂ n₃ a b P Q K : ℕ) :
    recoup3 n₁ n₂ n₃ a b P Q K =
      ∑ t ∈ range (n₁ + 1), ∑ s ∈ range (n₂ + 1), ∑ w ∈ range (n₁ + n₂ - 2 * a + 1),
        ∑ r ∈ range (n₃ + 1), ∑ u ∈ range (n₂ + n₃ - 2 * b + 1),
          cgCoeff n₁ n₂ a w t s * cgCoeff (n₁ + n₂ - 2 * a) n₃ P K w r *
            (cgCoeff n₂ n₃ b u s r * cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K t u) := by
  unfold recoup3
  rw [show ∑ i ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K i * cV n₁ n₂ n₃ b Q K i =
    ∑ i ∈ idx3 n₁ n₂ n₃, (fun t s r => cU n₁ n₂ n₃ a P K (t, s, r) *
      cV n₁ n₂ n₃ b Q K (t, s, r)) i.1 i.2.1 i.2.2 from rfl,
    sum_idx3 n₁ n₂ n₃ (fun t s r => cU n₁ n₂ n₃ a P K (t, s, r) * cV n₁ n₂ n₃ b Q K (t, s, r))]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [cU, cV, Finset.sum_mul_sum]
  exact Finset.sum_comm

lemma sixJ_reflect (n₁ n₂ n₃ n₄ n₅ n₆ : ℕ) :
    sixJ n₁ n₂ n₃ n₄ n₅ n₆ =
      ∑ t ∈ range (n₁ + 1), ∑ s ∈ range (n₂ + 1), ∑ w ∈ range (n₃ + 1),
        ∑ r ∈ range (n₄ + 1), ∑ K ∈ range (n₅ + 1), ∑ u ∈ range (n₆ + 1),
          sixJTerm n₁ n₂ n₃ n₄ n₅ n₆ (n₁ - t) (n₂ - s) w (n₄ - r) (n₅ - K) (n₆ - u) := by
  unfold sixJ
  rw [sum_range_reflect' n₁]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_range_reflect' n₂]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sum_range_reflect' n₄]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_range_reflect' n₅]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [sum_range_reflect' n₆]

lemma sum_recoup3 {n₁ n₂ n₃ a b P Q : ℕ} (ha : a ≤ min n₁ n₂) (hb : b ≤ min n₂ n₃)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b))
    (hN : n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q) :
    ∑ K ∈ range (n₁ + n₂ - 2 * a + n₃ - 2 * P + 1), recoup3 n₁ n₂ n₃ a b P Q K =
      (((n₁ + n₂ - 2 * a + n₃ - 2 * P : ℕ) : ℝ) + 1) *
        √((((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * (((n₂ + n₃ - 2 * b : ℕ) : ℝ) + 1)) *
        (-1) ^ ((n₁ + n₂ + n₃ + (n₁ + n₂ - 2 * a + n₃ - 2 * P)) / 2) *
        sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₃ (n₁ + n₂ - 2 * a + n₃ - 2 * P) (n₂ + n₃ - 2 * b) := by
  simp only [recoup3_expand]
  rw [sum4_rotate]
  rw [sixJ_reflect]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun s hs =>
    Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun K hK =>
    Finset.sum_congr rfl fun u hu => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at ht hs hw hr hK hu
  exact recoup_term ha hb hP hQ hN ht hs hw hr hK hu

/-- **Recoupling of three angular momenta**:
`⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩ =
  (-1)^(j₁ + j₂ + j₃ + J) √((2j₁₂ + 1)(2j₂₃ + 1)) {j₁ j₂ j₁₂; j₃ J j₂₃}`, independent of `M`. -/
theorem recoup3_eq_sixJ {n₁ n₂ n₃ a b P Q K : ℕ} (ha : a ≤ min n₁ n₂) (hb : b ≤ min n₂ n₃)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b))
    (hN : n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q)
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * P) :
    recoup3 n₁ n₂ n₃ a b P Q K =
      (-1) ^ ((n₁ + n₂ + n₃ + (n₁ + n₂ - 2 * a + n₃ - 2 * P)) / 2) *
        √((((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * (((n₂ + n₃ - 2 * b : ℕ) : ℝ) + 1)) *
        sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₃ (n₁ + n₂ - 2 * a + n₃ - 2 * P) (n₂ + n₃ - 2 * b) := by
  have h := sum_recoup3 ha hb hP hQ hN
  rw [Finset.sum_congr rfl fun K' hK' => recoup3_const ha hb hP hQ hN
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hK')), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at h
  rw [recoup3_const ha hb hP hQ hN hK]
  have hpos : (((n₁ + n₂ - 2 * a + n₃ - 2 * P : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  push_cast at h hpos ⊢
  apply mul_left_cancel₀ hpos
  rw [h]; ring

end QM
