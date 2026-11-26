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
* `recoup3_const`, `dotp_stU_stV_eq_zero`: independence of `M`, orthogonality across `J` and `M`.
* `recoup3_eq_sixJ`: the overlap is `(-1)^(j₁+j₂+j₃+J) √((2j₁₂+1)(2j₂₃+1)) {j₁ j₂ j₁₂; j₃ J j₂₃}`.
* `cU_complete`, `cV_ortho`: completeness and orthonormality of the coupled states.
* `sixJ_swap12`, `sixJ_swap23`, `sixJ_flip`: the tetrahedral symmetries of the 6j symbol.
* `sixJ_orthogonal`: the orthogonality relation of the 6j symbols.
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

/-- The overlap of the two couplings of three orthonormal ladders, for any `M` and `M'`. -/
theorem dotp_recouple₂ {n₁ n₂ n₃ : ℕ} {f : ℕ → X → ℝ} {g : ℕ → Y → ℝ} {h : ℕ → Z → ℝ}
    (hf : OrthoUpTo n₁ f) (hg : OrthoUpTo n₂ g) (hh : OrthoUpTo n₃ h) (a b P Q K K' : ℕ) :
    dotp (couple (n₁ + n₂ - 2 * a) n₃ P (couple n₁ n₂ a f g) h K)
      (fun q : (X × Y) × Z =>
        couple n₁ (n₂ + n₃ - 2 * b) Q f (couple n₂ n₃ b g h) K' (q.1.1, (q.1.2, q.2))) =
      ∑ i ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K i * cV n₁ n₂ n₃ b Q K' i := by
  rw [couple_couple_eq, couple_couple_assoc_eq, dotp_sum_smul]
  intro i hi j hj
  rw [mem_idx3] at hi hj
  rw [dotp_tensor3, hf _ hi.1 _ hj.1, hg _ hi.2.1 _ hj.2.1, hh _ hi.2.2 _ hj.2.2]
  obtain ⟨i1, i2, i3⟩ := i
  obtain ⟨j1, j2, j3⟩ := j
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **The overlap of the two couplings** of three orthonormal ladders is `recoup3`. -/
theorem dotp_recouple {n₁ n₂ n₃ : ℕ} {f : ℕ → X → ℝ} {g : ℕ → Y → ℝ} {h : ℕ → Z → ℝ}
    (hf : OrthoUpTo n₁ f) (hg : OrthoUpTo n₂ g) (hh : OrthoUpTo n₃ h) (a b P Q K : ℕ) :
    dotp (couple (n₁ + n₂ - 2 * a) n₃ P (couple n₁ n₂ a f g) h K)
      (fun q : (X × Y) × Z =>
        couple n₁ (n₂ + n₃ - 2 * b) Q f (couple n₂ n₃ b g h) K (q.1.1, (q.1.2, q.2))) =
      recoup3 n₁ n₂ n₃ a b P Q K :=
  dotp_recouple₂ hf hg hh a b P Q K K

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

/-! ### Symmetries of the 6j symbol -/

lemma threeJ_support {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (h : threeJ n₁ n₂ n₃ x₁ x₂ x₃ ≠ 0) :
    Triad n₁ n₂ n₃ ∧ x₁ ≤ n₁ ∧ x₂ ≤ n₂ ∧ x₃ ≤ n₃ ∧ 2 * (x₁ + x₂ + x₃) = n₁ + n₂ + n₃ := by
  have h1 : Triad n₁ n₂ n₃ ∧ x₃ ≤ n₃ := by
    by_contra h'; exact h (threeJ_of_not h')
  have h2 : 2 * (x₁ + x₂ + x₃) = n₁ + n₂ + n₃ := by
    by_contra h'; exact h (threeJ_eq_zero h')
  have h3 : x₁ ≤ n₁ ∧ x₂ ≤ n₂ := by
    by_contra h'; exact h (threeJ_eq_zero_of_gt (by omega))
  exact ⟨h1.1, h3.1, h3.2, h1.2, h2⟩

lemma prod4_signs (A B C D σ τ : ℝ) (h : A * B * C * D ≠ 0 → σ = τ) :
    σ * (A * B * C * D) = τ * (A * B * C * D) := by
  by_cases h0 : A * B * C * D = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [h h0]

lemma neg_one_pow_eq_of_even {a b : ℕ} (h : Even (a + b)) : (-1 : ℝ) ^ a = (-1) ^ b := by
  have e : (-1 : ℝ) ^ (a + b) = 1 := h.neg_one_pow
  rw [pow_add] at e
  have hb : ((-1 : ℝ) ^ b) * (-1) ^ b = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  linear_combination (-1 : ℝ) ^ b * e - (-1 : ℝ) ^ a * hb

lemma prod4_ne {A B C D : ℝ} (h : A * B * C * D ≠ 0) : A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ D ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h' <;> apply h <;> rw [h'] <;> ring

lemma sixJTerm_swap12 {n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆ : ℕ} (h₄ : y₄ ≤ n₄) (h₅ : y₅ ≤ n₅)
    (h₆ : y₆ ≤ n₆) :
    sixJTerm n₂ n₁ n₃ n₅ n₄ n₆ y₂ y₁ y₃ (n₅ - y₅) (n₄ - y₄) (n₆ - y₆) =
      sixJTerm n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆ := by
  unfold sixJTerm
  rw [Nat.sub_sub_self h₄, Nat.sub_sub_self h₅, Nat.sub_sub_self h₆,
    threeJ_swap12 n₁ n₂ n₃, threeJ_swap12 n₄ n₂ n₆, threeJ_swap12 n₁ n₅ n₆,
    threeJ_swap12 n₄ n₅ n₃]
  set A := threeJ n₁ n₂ n₃ (n₁ - y₁) (n₂ - y₂) (n₃ - y₃)
  set B := threeJ n₁ n₅ n₆ y₁ (n₅ - y₅) y₆
  set C := threeJ n₄ n₂ n₆ y₄ y₂ (n₆ - y₆)
  set D := threeJ n₄ n₅ n₃ (n₄ - y₄) y₅ y₃
  have key := prod4_signs A B C D
    ((-1) ^ (y₂ + y₁ + y₃ + (n₅ - y₅) + (n₄ - y₄) + (n₆ - y₆) + (n₁ + n₂ + n₃) / 2 +
      (n₄ + n₂ + n₆) / 2 + (n₁ + n₅ + n₆) / 2 + (n₄ + n₅ + n₃) / 2))
    ((-1) ^ (y₁ + y₂ + y₃ + y₄ + y₅ + y₆)) ?_
  · simp only [pow_add] at key
    linear_combination key
  intro h0
  obtain ⟨hA, hB, hC, hD⟩ := prod4_ne h0
  obtain ⟨⟨_, _, _, ⟨r₁, hr₁⟩⟩, -, -, -, s₁⟩ := threeJ_support hA
  obtain ⟨⟨_, _, _, ⟨r₂, hr₂⟩⟩, -, -, -, s₂⟩ := threeJ_support hB
  obtain ⟨⟨_, _, _, ⟨r₃, hr₃⟩⟩, -, -, -, s₃⟩ := threeJ_support hC
  obtain ⟨⟨_, _, _, ⟨r₄, hr₄⟩⟩, -, -, -, s₄⟩ := threeJ_support hD
  apply neg_one_pow_eq_of_even
  rw [show (n₁ + n₂ + n₃) / 2 = r₁ by omega, show (n₁ + n₅ + n₆) / 2 = r₂ by omega,
    show (n₄ + n₂ + n₆) / 2 = r₃ by omega, show (n₄ + n₅ + n₃) / 2 = r₄ by omega]
  exact Nat.even_iff.mpr (by omega)

lemma sixJTerm_swap23 {n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆ : ℕ} (h₄ : y₄ ≤ n₄) (h₅ : y₅ ≤ n₅)
    (h₆ : y₆ ≤ n₆) :
    sixJTerm n₁ n₃ n₂ n₄ n₆ n₅ y₁ y₃ y₂ (n₄ - y₄) (n₆ - y₆) (n₅ - y₅) =
      sixJTerm n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆ := by
  unfold sixJTerm
  rw [Nat.sub_sub_self h₄, Nat.sub_sub_self h₅, Nat.sub_sub_self h₆,
    threeJ_swap23 n₁ n₂ n₃, threeJ_swap23 n₁ n₅ n₆, threeJ_swap23 n₄ n₅ n₃,
    threeJ_swap23 n₄ n₂ n₆]
  set A := threeJ n₁ n₂ n₃ (n₁ - y₁) (n₂ - y₂) (n₃ - y₃)
  set B := threeJ n₁ n₅ n₆ y₁ (n₅ - y₅) y₆
  set C := threeJ n₄ n₂ n₆ y₄ y₂ (n₆ - y₆)
  set D := threeJ n₄ n₅ n₃ (n₄ - y₄) y₅ y₃
  have key := prod4_signs A B C D
    ((-1) ^ (y₁ + y₃ + y₂ + (n₄ - y₄) + (n₆ - y₆) + (n₅ - y₅) + (n₁ + n₂ + n₃) / 2 +
      (n₁ + n₅ + n₆) / 2 + (n₄ + n₅ + n₃) / 2 + (n₄ + n₂ + n₆) / 2))
    ((-1) ^ (y₁ + y₂ + y₃ + y₄ + y₅ + y₆)) ?_
  · simp only [pow_add] at key
    linear_combination key
  intro h0
  obtain ⟨hA, hB, hC, hD⟩ := prod4_ne h0
  obtain ⟨⟨_, _, _, ⟨r₁, hr₁⟩⟩, -, -, -, s₁⟩ := threeJ_support hA
  obtain ⟨⟨_, _, _, ⟨r₂, hr₂⟩⟩, -, -, -, s₂⟩ := threeJ_support hB
  obtain ⟨⟨_, _, _, ⟨r₃, hr₃⟩⟩, -, -, -, s₃⟩ := threeJ_support hC
  obtain ⟨⟨_, _, _, ⟨r₄, hr₄⟩⟩, -, -, -, s₄⟩ := threeJ_support hD
  apply neg_one_pow_eq_of_even
  rw [show (n₁ + n₂ + n₃) / 2 = r₁ by omega, show (n₁ + n₅ + n₆) / 2 = r₂ by omega,
    show (n₄ + n₂ + n₆) / 2 = r₃ by omega, show (n₄ + n₅ + n₃) / 2 = r₄ by omega]
  exact Nat.even_iff.mpr (by omega)

lemma sixJTerm_flip {n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆ : ℕ} (h₁ : y₁ ≤ n₁) (h₂ : y₂ ≤ n₂)
    (h₃ : y₃ ≤ n₃) (h₄ : y₄ ≤ n₄) (h₅ : y₅ ≤ n₅) (h₆ : y₆ ≤ n₆) :
    sixJTerm n₄ n₅ n₃ n₁ n₂ n₆ (n₄ - y₄) y₅ y₃ (n₁ - y₁) y₂ y₆ =
      sixJTerm n₁ n₂ n₃ n₄ n₅ n₆ y₁ y₂ y₃ y₄ y₅ y₆ := by
  have rA := threeJ_reverse (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) (Nat.sub_le n₁ y₁) (Nat.sub_le n₂ y₂)
    (Nat.sub_le n₃ y₃)
  rw [Nat.sub_sub_self h₁, Nat.sub_sub_self h₂, Nat.sub_sub_self h₃] at rA
  have rB := threeJ_reverse (n₁ := n₁) (n₂ := n₅) (n₃ := n₆) h₁ (Nat.sub_le n₅ y₅) h₆
  rw [Nat.sub_sub_self h₅] at rB
  have rC := threeJ_reverse (n₁ := n₄) (n₂ := n₂) (n₃ := n₆) h₄ h₂ (Nat.sub_le n₆ y₆)
  rw [Nat.sub_sub_self h₆] at rC
  have rD := threeJ_reverse (n₁ := n₄) (n₂ := n₅) (n₃ := n₃) (Nat.sub_le n₄ y₄) h₅ h₃
  rw [Nat.sub_sub_self h₄] at rD
  unfold sixJTerm
  rw [Nat.sub_sub_self h₄, Nat.sub_sub_self h₁, rA, rB, rC, rD]
  set A := threeJ n₁ n₂ n₃ (n₁ - y₁) (n₂ - y₂) (n₃ - y₃)
  set B := threeJ n₁ n₅ n₆ y₁ (n₅ - y₅) y₆
  set C := threeJ n₄ n₂ n₆ y₄ y₂ (n₆ - y₆)
  set D := threeJ n₄ n₅ n₃ (n₄ - y₄) y₅ y₃
  have key := prod4_signs A B C D
    ((-1) ^ (n₄ - y₄ + y₅ + y₃ + (n₁ - y₁) + y₂ + y₆ + (n₁ + n₂ + n₃) / 2 +
      (n₁ + n₅ + n₆) / 2 + (n₄ + n₅ + n₃) / 2 + (n₄ + n₂ + n₆) / 2))
    ((-1) ^ (y₁ + y₂ + y₃ + y₄ + y₅ + y₆)) ?_
  · simp only [pow_add] at key
    linear_combination key
  intro h0
  obtain ⟨hA, hB, hC, hD⟩ := prod4_ne h0
  obtain ⟨⟨_, _, _, ⟨r₁, hr₁⟩⟩, -, -, -, s₁⟩ := threeJ_support hA
  obtain ⟨⟨_, _, _, ⟨r₂, hr₂⟩⟩, -, -, -, s₂⟩ := threeJ_support hB
  obtain ⟨⟨_, _, _, ⟨r₃, hr₃⟩⟩, -, -, -, s₃⟩ := threeJ_support hC
  obtain ⟨⟨_, _, _, ⟨r₄, hr₄⟩⟩, -, -, -, s₄⟩ := threeJ_support hD
  apply neg_one_pow_eq_of_even
  rw [show (n₁ + n₂ + n₃) / 2 = r₁ by omega, show (n₁ + n₅ + n₆) / 2 = r₂ by omega,
    show (n₄ + n₂ + n₆) / 2 = r₃ by omega, show (n₄ + n₅ + n₃) / 2 = r₄ by omega]
  exact Nat.even_iff.mpr (by omega)

lemma sum5_perm (A B C D E : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, F a b c d e =
      ∑ d ∈ D, ∑ e ∈ E, ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c d e := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => sum3_rotate C D E _]
  rw [sum4_rotate, sum4_rotate]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ =>
    (sum3_rotate C A B _).symm

/-- **Exchange of the first two columns**: `{j₂ j₁ j₃; j₅ j₄ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
theorem sixJ_swap12 (n₁ n₂ n₃ n₄ n₅ n₆ : ℕ) :
    sixJ n₂ n₁ n₃ n₅ n₄ n₆ = sixJ n₁ n₂ n₃ n₄ n₅ n₆ := by
  unfold sixJ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ =>
    Finset.sum_congr rfl fun y₃ _ => ?_
  rw [Finset.sum_comm, sum_range_reflect' n₄]
  refine Finset.sum_congr rfl fun y₄ h₄ => ?_
  rw [sum_range_reflect' n₅]
  refine Finset.sum_congr rfl fun y₅ h₅ => ?_
  rw [sum_range_reflect' n₆]
  refine Finset.sum_congr rfl fun y₆ h₆ => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at h₄ h₅ h₆
  exact sixJTerm_swap12 h₄ h₅ h₆

/-- **Exchange of the last two columns**: `{j₁ j₃ j₂; j₄ j₆ j₅} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
theorem sixJ_swap23 (n₁ n₂ n₃ n₄ n₅ n₆ : ℕ) :
    sixJ n₁ n₃ n₂ n₄ n₆ n₅ = sixJ n₁ n₂ n₃ n₄ n₅ n₆ := by
  unfold sixJ
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₂ _ => Finset.sum_congr rfl fun y₃ _ => ?_
  rw [sum_range_reflect' n₄]
  refine Finset.sum_congr rfl fun y₄ h₄ => ?_
  rw [Finset.sum_comm, sum_range_reflect' n₅]
  refine Finset.sum_congr rfl fun y₅ h₅ => ?_
  rw [sum_range_reflect' n₆]
  refine Finset.sum_congr rfl fun y₆ h₆ => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at h₄ h₅ h₆
  exact sixJTerm_swap23 h₄ h₅ h₆

/-- **Exchange of upper and lower entries in the first two columns**:
`{j₄ j₅ j₃; j₁ j₂ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
theorem sixJ_flip (n₁ n₂ n₃ n₄ n₅ n₆ : ℕ) :
    sixJ n₄ n₅ n₃ n₁ n₂ n₆ = sixJ n₁ n₂ n₃ n₄ n₅ n₆ := by
  unfold sixJ
  rw [sum5_perm, sum_range_reflect' n₁]
  refine Finset.sum_congr rfl fun y₁ h₁ => Finset.sum_congr rfl fun y₂ h₂ =>
    Finset.sum_congr rfl fun y₃ h₃ => ?_
  rw [sum_range_reflect' n₄]
  refine Finset.sum_congr rfl fun y₄ h₄ => Finset.sum_congr rfl fun y₅ h₅ =>
    Finset.sum_congr rfl fun y₆ h₆ => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at h₁ h₂ h₃ h₄ h₅ h₆
  exact sixJTerm_flip h₁ h₂ h₃ h₄ h₅ h₆

/-! ### Orthogonality of the 6j symbols -/

/-- **Completeness of the couplings** `|(j₁ j₂) j₁₂, j₃; J M⟩`. -/
theorem cU_complete (n₁ n₂ n₃ : ℕ) {i j : ℕ × ℕ × ℕ} (hi : i ∈ idx3 n₁ n₂ n₃)
    (hj : j ∈ idx3 n₁ n₂ n₃) :
    ∑ a ∈ range (min n₁ n₂ + 1), ∑ P ∈ range (min (n₁ + n₂ - 2 * a) n₃ + 1),
      ∑ K ∈ range (n₁ + n₂ - 2 * a + n₃ - 2 * P + 1),
        cU n₁ n₂ n₃ a P K i * cU n₁ n₂ n₃ a P K j = if i = j then 1 else 0 := by
  rw [mem_idx3] at hi hj
  obtain ⟨i1, i2, i3⟩ := i
  obtain ⟨j1, j2, j3⟩ := j
  simp only at hi hj
  have inner : ∀ a, ∑ P ∈ range (min (n₁ + n₂ - 2 * a) n₃ + 1),
      ∑ K ∈ range (n₁ + n₂ - 2 * a + n₃ - 2 * P + 1),
        cU n₁ n₂ n₃ a P K (i1, i2, i3) * cU n₁ n₂ n₃ a P K (j1, j2, j3) =
      if i3 = j3 then ∑ w ∈ range (n₁ + n₂ - 2 * a + 1),
        cgCoeff n₁ n₂ a w i1 i2 * cgCoeff n₁ n₂ a w j1 j2 else 0 := by
    intro a
    simp only [cU, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl
      fun w _ => Finset.sum_congr rfl fun w' _ => (show
        cgCoeff n₁ n₂ a w i1 i2 * cgCoeff (n₁ + n₂ - 2 * a) n₃ P K w i3 *
          (cgCoeff n₁ n₂ a w' j1 j2 * cgCoeff (n₁ + n₂ - 2 * a) n₃ P K w' j3) =
        cgCoeff n₁ n₂ a w i1 i2 * cgCoeff n₁ n₂ a w' j1 j2 *
          (cgCoeff (n₁ + n₂ - 2 * a) n₃ P K w i3 * cgCoeff (n₁ + n₂ - 2 * a) n₃ P K w' j3)
        by ring)]
    rw [Finset.sum_congr rfl fun P _ => sum3_rotate _ _ _ _, sum3_rotate]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun w' hw' => by
      rw [cg_orthogonal_right (Nat.lt_succ_iff.mp (Finset.mem_range.mp hw))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hw')) hi.2.2 hj.2.2]]
    split_ifs with h3
    · refine Finset.sum_congr rfl fun w hw => ?_
      rw [Finset.sum_eq_single w]
      · simp [h3]
      · intro w' _ hne; simp [Ne.symm hne]
      · intro h; exact absurd hw h
    · simp [h3]
  rw [Finset.sum_congr rfl fun a _ => inner a]
  by_cases h3 : i3 = j3
  · simp only [h3, ite_true]
    rw [cg_orthogonal_right hi.1 hj.1 hi.2.1 hj.2.1]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  · simp only [h3, ite_false, Finset.sum_const_zero, Prod.mk.injEq]
    split_ifs <;> simp_all

/-- **Orthonormality of the couplings** `|j₁, (j₂ j₃) j₂₃; J M⟩`. -/
theorem cV_ortho {n₁ n₂ n₃ b Q K b' Q' K' : ℕ} (hb : b ≤ min n₂ n₃)
    (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b)) (hK : K ≤ n₁ + (n₂ + n₃ - 2 * b) - 2 * Q)
    (hb' : b' ≤ min n₂ n₃) (hQ' : Q' ≤ min n₁ (n₂ + n₃ - 2 * b')) :
    ∑ i ∈ idx3 n₁ n₂ n₃, cV n₁ n₂ n₃ b Q K i * cV n₁ n₂ n₃ b' Q' K' i =
      if b = b' ∧ Q = Q' ∧ K = K' then 1 else 0 := by
  rw [show ∑ i ∈ idx3 n₁ n₂ n₃, cV n₁ n₂ n₃ b Q K i * cV n₁ n₂ n₃ b' Q' K' i =
    ∑ i ∈ idx3 n₁ n₂ n₃, (fun t s r => cV n₁ n₂ n₃ b Q K (t, s, r) *
      cV n₁ n₂ n₃ b' Q' K' (t, s, r)) i.1 i.2.1 i.2.2 from rfl,
    sum_idx3 n₁ n₂ n₃ (fun t s r => cV n₁ n₂ n₃ b Q K (t, s, r) * cV n₁ n₂ n₃ b' Q' K' (t, s, r))]
  have inner : ∀ t, ∑ s ∈ range (n₂ + 1), ∑ r ∈ range (n₃ + 1),
      cV n₁ n₂ n₃ b Q K (t, s, r) * cV n₁ n₂ n₃ b' Q' K' (t, s, r) =
      if b = b' then ∑ u ∈ range (n₂ + n₃ - 2 * b + 1),
        cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K t u * cgCoeff n₁ (n₂ + n₃ - 2 * b') Q' K' t u
      else 0 := by
    intro t
    simp only [cV, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl
      fun u _ => Finset.sum_congr rfl fun u' _ => (show
        cgCoeff n₂ n₃ b u s r * cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K t u *
          (cgCoeff n₂ n₃ b' u' s r * cgCoeff n₁ (n₂ + n₃ - 2 * b') Q' K' t u') =
        cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K t u * cgCoeff n₁ (n₂ + n₃ - 2 * b') Q' K' t u' *
          (cgCoeff n₂ n₃ b u s r * cgCoeff n₂ n₃ b' u' s r) by ring)]
    rw [sum4_rotate, sum4_rotate]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' _ => by
      rw [cg_orthogonal_left hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)) hb']]
    split_ifs with hbb
    · subst hbb
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.sum_eq_single u]
      · simp
      · intro u' _ hne; simp [Ne.symm hne]
      · intro h; exact absurd hu h
    · simp [hbb]
  rw [Finset.sum_congr rfl fun t _ => inner t]
  by_cases hbb : b = b'
  · subst hbb
    simp only [ite_true, true_and]
    exact cg_orthogonal_left hQ hK hQ'
  · simp [hbb]

lemma sum3_rotate' {α β γ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ)
    (F : α → β → γ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c = ∑ b ∈ B, ∑ c ∈ C, ∑ a ∈ A, F a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma cU_cV_eq_zero {n₁ n₂ n₃ a b P Q K K' : ℕ} (ha : a ≤ min n₁ n₂) (hb : b ≤ min n₂ n₃)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b))
    (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * P) (hK' : K' ≤ n₁ + (n₂ + n₃ - 2 * b) - 2 * Q)
    (hne : ¬(n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q ∧ K = K')) :
    ∑ i ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K i * cV n₁ n₂ n₃ b Q K' i = 0 := by
  rw [← dotp_recouple₂ (orthoUpTo_one n₁) (orthoUpTo_one n₂) (orthoUpTo_one n₃)]
  exact dotp_stU_stV_eq_zero ha hb hP hQ hK hK' hne

/-- Expanding `⟨V_b, V_b'⟩` in the complete family `U`. -/
lemma cV_parseval (n₁ n₂ n₃ b Q b' Q' : ℕ) :
    ∑ i ∈ idx3 n₁ n₂ n₃, cV n₁ n₂ n₃ b Q 0 i * cV n₁ n₂ n₃ b' Q' 0 i =
      ∑ a ∈ range (min n₁ n₂ + 1), ∑ P ∈ range (min (n₁ + n₂ - 2 * a) n₃ + 1),
        ∑ K ∈ range (n₁ + n₂ - 2 * a + n₃ - 2 * P + 1),
          (∑ i ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K i * cV n₁ n₂ n₃ b Q 0 i) *
            ∑ j ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K j * cV n₁ n₂ n₃ b' Q' 0 j := by
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun P _ => sum3_rotate' _ _ _ _]
  rw [Finset.sum_congr rfl fun a _ => sum3_rotate' _ _ _ _, sum3_rotate']
  symm
  calc _ = ∑ i ∈ idx3 n₁ n₂ n₃, ∑ j ∈ idx3 n₁ n₂ n₃,
        cV n₁ n₂ n₃ b Q 0 i * cV n₁ n₂ n₃ b' Q' 0 j *
          ∑ a ∈ range (min n₁ n₂ + 1), ∑ P ∈ range (min (n₁ + n₂ - 2 * a) n₃ + 1),
            ∑ K ∈ range (n₁ + n₂ - 2 * a + n₃ - 2 * P + 1),
              cU n₁ n₂ n₃ a P K i * cU n₁ n₂ n₃ a P K j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_congr rfl fun j hj => by rw [cU_complete n₁ n₂ n₃ hi hj]]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hne; simp [Ne.symm hne]
        · intro h; exact absurd hi h

/-- Only `M = J` and the matching `J` survive in the expansion. -/
lemma sum_K_cU_cV {n₁ n₂ n₃ a b P Q b' Q' : ℕ} (ha : a ≤ min n₁ n₂) (hb : b ≤ min n₂ n₃)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b)) :
    ∑ K ∈ range (n₁ + n₂ - 2 * a + n₃ - 2 * P + 1),
      (∑ i ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K i * cV n₁ n₂ n₃ b Q 0 i) *
        ∑ j ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K j * cV n₁ n₂ n₃ b' Q' 0 j =
      if n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q then
        recoup3 n₁ n₂ n₃ a b P Q 0 * recoup3 n₁ n₂ n₃ a b' P Q' 0 else 0 := by
  split_ifs with hN
  · rw [Finset.sum_eq_single 0]
    · rfl
    · intro K hK hK0
      rw [cU_cV_eq_zero ha hb hP hQ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hK)) (Nat.zero_le _)
        (fun h => hK0 h.2), zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  · refine Finset.sum_eq_zero fun K hK => ?_
    rw [cU_cV_eq_zero ha hb hP hQ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hK)) (Nat.zero_le _)
      (fun h => hN h.1), zero_mul]

/-- **Orthogonality of the recoupling coefficients**. -/
theorem recoup3_orthogonal {n₁ n₂ n₃ b Q b' Q' : ℕ} (hb : b ≤ min n₂ n₃)
    (hQ : Q ≤ min n₁ (n₂ + n₃ - 2 * b)) (hb' : b' ≤ min n₂ n₃)
    (hQ' : Q' ≤ min n₁ (n₂ + n₃ - 2 * b'))
    (hN : n₁ + (n₂ + n₃ - 2 * b) - 2 * Q = n₁ + (n₂ + n₃ - 2 * b') - 2 * Q') :
    ∑ a ∈ range (min n₁ n₂ + 1), ∑ P ∈ range (min (n₁ + n₂ - 2 * a) n₃ + 1),
      (if n₁ + n₂ - 2 * a + n₃ - 2 * P = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q then
        recoup3 n₁ n₂ n₃ a b P Q 0 * recoup3 n₁ n₂ n₃ a b' P Q' 0 else 0) =
      if b = b' then 1 else 0 := by
  rw [← Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun P hP =>
    sum_K_cU_cV (b' := b') (Q' := Q') (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hb
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hP)) hQ, ← cV_parseval,
    cV_ortho hb hQ (Nat.zero_le _) hb' hQ']
  by_cases hbb : b = b'
  · subst hbb
    have : Q = Q' := by
      have := min_le_left n₁ (n₂ + n₃ - 2 * b)
      have := min_le_right n₁ (n₂ + n₃ - 2 * b)
      have := min_le_left n₁ (n₂ + n₃ - 2 * b)
      have := le_trans hQ' (min_le_left _ _)
      have := le_trans hQ' (min_le_right _ _)
      omega
    simp [this]
  · simp [hbb]

lemma sixJ_eq_zero_of_not_triad₁ {n₁ n₂ n₃ n₄ n₅ n₆ : ℕ} (h : ¬Triad n₁ n₂ n₃) :
    sixJ n₁ n₂ n₃ n₄ n₅ n₆ = 0 := by
  unfold sixJ sixJTerm
  simp [threeJ_of_not (show ¬(Triad n₁ n₂ n₃ ∧ _) from fun h' => h h'.1)]

lemma sixJ_eq_zero_of_not_triad₄ {n₁ n₂ n₃ n₄ n₅ n₆ : ℕ} (h : ¬Triad n₄ n₅ n₃) :
    sixJ n₁ n₂ n₃ n₄ n₅ n₆ = 0 := by
  unfold sixJ sixJTerm
  simp [threeJ_of_not (show ¬(Triad n₄ n₅ n₃ ∧ _) from fun h' => h h'.1)]

lemma sum_triad_reindex (n₁ n₂ : ℕ) (f : ℕ → ℝ) (hf : ∀ x, ¬Triad n₁ n₂ x → f x = 0) :
    ∑ x ∈ range (n₁ + n₂ + 1), f x = ∑ a ∈ range (min n₁ n₂ + 1), f (n₁ + n₂ - 2 * a) := by
  have hm1 := min_le_left n₁ n₂
  have hm2 := min_le_right n₁ n₂
  rw [← Finset.sum_image (f := f) (s := range (min n₁ n₂ + 1)) (g := fun a => n₁ + n₂ - 2 * a)]
  · symm
    refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => hf x ?_)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_range] at ha ⊢
      omega
    · rintro ⟨h1, h2, h3, r, hr⟩
      apply hx'
      refine Finset.mem_image.mpr ⟨(n₁ + n₂ - x) / 2, ?_, ?_⟩
      · simp only [Finset.mem_range]; omega
      · show n₁ + n₂ - 2 * ((n₁ + n₂ - x) / 2) = x
        omega
  · intro a ha a' ha' h
    simp only [Finset.coe_range, Set.mem_Iio] at ha ha'
    simp only at h
    omega

lemma sum_P_single (n₁₂ n₃ N : ℕ) (G : ℕ → ℝ) :
    ∑ P ∈ range (min n₁₂ n₃ + 1), (if n₁₂ + n₃ - 2 * P = N then G P else 0) =
      if Triad n₁₂ n₃ N then G ((n₁₂ + n₃ - N) / 2) else 0 := by
  have hm1 := min_le_left n₁₂ n₃
  have hm2 := min_le_right n₁₂ n₃
  split_ifs with ht
  · obtain ⟨h1, h2, h3, r, hr⟩ := ht
    rw [Finset.sum_eq_single ((n₁₂ + n₃ - N) / 2)]
    · rw [ite_eq_left (by omega)]
    · intro P hP hne
      simp only [Finset.mem_range] at hP
      rw [ite_eq_right]
      intro h; apply hne; omega
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · refine Finset.sum_eq_zero fun P hP => ?_
    rw [ite_eq_right]
    intro h
    apply ht
    simp only [Finset.mem_range] at hP
    exact ⟨by omega, by omega, by omega, ⟨n₁₂ + n₃ - P, by omega⟩⟩

lemma recoup_term_eq {n₁ n₂ n₄ n₅ n₆ n₆' a b b' Q Q' : ℕ} (ha : a ≤ min n₁ n₂)
    (hb : b ≤ min n₂ n₄) (hb' : b' ≤ min n₂ n₄) (hn₆ : n₂ + n₄ - 2 * b = n₆)
    (hn₆' : n₂ + n₄ - 2 * b' = n₆') (hQ : Q ≤ min n₁ n₆) (hQ' : Q' ≤ min n₁ n₆')
    (hn₅ : n₁ + n₆ - 2 * Q = n₅) (hn₅' : n₁ + n₆' - 2 * Q' = n₅) :
    (if Triad (n₁ + n₂ - 2 * a) n₄ (n₁ + (n₂ + n₄ - 2 * b) - 2 * Q) then
      recoup3 n₁ n₂ n₄ a b ((n₁ + n₂ - 2 * a + n₄ - (n₁ + (n₂ + n₄ - 2 * b) - 2 * Q)) / 2) Q 0 *
        recoup3 n₁ n₂ n₄ a b' ((n₁ + n₂ - 2 * a + n₄ - (n₁ + (n₂ + n₄ - 2 * b) - 2 * Q)) / 2) Q' 0
      else 0) =
      (((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * √(((n₆ : ℝ) + 1) * ((n₆' : ℝ) + 1)) *
        sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆ * sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆' := by
  rw [hn₆, hn₅]
  split_ifs with ht
  · obtain ⟨h1, h2, h3, r, hr⟩ := ht
    have hP : (n₁ + n₂ - 2 * a + n₄ - n₅) / 2 ≤ min (n₁ + n₂ - 2 * a) n₄ :=
      le_min (by omega) (by omega)
    have e1 := recoup3_eq_sixJ (K := 0) (Q := Q) ha hb hP (by rw [hn₆]; exact hQ)
      (by rw [hn₆, hn₅]; omega) (Nat.zero_le _)
    have e2 := recoup3_eq_sixJ (K := 0) (Q := Q') ha hb' hP (by rw [hn₆']; exact hQ')
      (by rw [hn₆', hn₅']; omega) (Nat.zero_le _)
    rw [e1, e2, hn₆, hn₆', show n₁ + n₂ - 2 * a + n₄ - 2 * ((n₁ + n₂ - 2 * a + n₄ - n₅) / 2) = n₅
      by omega]
    have hsq : ((-1 : ℝ) ^ ((n₁ + n₂ + n₄ + n₅) / 2)) * (-1) ^ ((n₁ + n₂ + n₄ + n₅) / 2) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hA : (0 : ℝ) ≤ ((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1 := by positivity
    rw [Real.sqrt_mul hA, Real.sqrt_mul hA, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (n₆ : ℝ) + 1)]
    have hs := Real.mul_self_sqrt hA
    linear_combination (√((n₆ : ℝ) + 1) * √((n₆' : ℝ) + 1) *
      sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆ * sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆') *
        (((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * hsq +
      (√((n₆ : ℝ) + 1) * √((n₆' : ℝ) + 1) *
        sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆ * sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆') *
        ((-1 : ℝ) ^ ((n₁ + n₂ + n₄ + n₅) / 2)) * (-1) ^ ((n₁ + n₂ + n₄ + n₅) / 2) * hs
  · rw [sixJ_eq_zero_of_not_triad₄ (n₁ := n₁) (n₂ := n₂) (n₆ := n₆)
      (fun h => ht (triad_cyclic.mp h))]
    ring

/-- **Orthogonality of the 6j symbols**
`Σ_x (2x + 1)(2j₆ + 1) {j₁ j₂ x; j₄ j₅ j₆} {j₁ j₂ x; j₄ j₅ j₆'} = δ_{j₆ j₆'}`
when `(j₂ j₄ j₆)`, `(j₁ j₆ j₅)` and the same with `j₆'` satisfy the triangle conditions. -/
theorem sixJ_orthogonal {n₁ n₂ n₄ n₅ n₆ n₆' : ℕ} (h₁ : Triad n₂ n₄ n₆) (h₂ : Triad n₁ n₆ n₅)
    (h₁' : Triad n₂ n₄ n₆') (h₂' : Triad n₁ n₆' n₅) :
    ∑ x ∈ range (n₁ + n₂ + 1), ((x : ℝ) + 1) * ((n₆ : ℝ) + 1) *
      sixJ n₁ n₂ x n₄ n₅ n₆ * sixJ n₁ n₂ x n₄ n₅ n₆' = if n₆ = n₆' then 1 else 0 := by
  obtain ⟨a1, a2, a3, r₁, hr₁⟩ := h₁
  obtain ⟨c1, c2, c3, t₁, ht₁⟩ := h₂
  obtain ⟨a1', a2', a3', r₁', hr₁'⟩ := h₁'
  obtain ⟨c1', c2', c3', t₁', ht₁'⟩ := h₂'
  have hb : (n₂ + n₄ - n₆) / 2 ≤ min n₂ n₄ := le_min (by omega) (by omega)
  have hb' : (n₂ + n₄ - n₆') / 2 ≤ min n₂ n₄ := le_min (by omega) (by omega)
  have hn₆ : n₂ + n₄ - 2 * ((n₂ + n₄ - n₆) / 2) = n₆ := by omega
  have hn₆' : n₂ + n₄ - 2 * ((n₂ + n₄ - n₆') / 2) = n₆' := by omega
  have hQ : (n₁ + n₆ - n₅) / 2 ≤ min n₁ n₆ := le_min (by omega) (by omega)
  have hQ' : (n₁ + n₆' - n₅) / 2 ≤ min n₁ n₆' := le_min (by omega) (by omega)
  have hn₅ : n₁ + n₆ - 2 * ((n₁ + n₆ - n₅) / 2) = n₅ := by omega
  have hn₅' : n₁ + n₆' - 2 * ((n₁ + n₆' - n₅) / 2) = n₅ := by omega
  have key := recoup3_orthogonal (n₃ := n₄) (Q := (n₁ + n₆ - n₅) / 2)
    (Q' := (n₁ + n₆' - n₅) / 2) hb (by rw [hn₆]; exact hQ) hb'
    (by rw [hn₆']; exact hQ') (by rw [hn₆, hn₆', hn₅, hn₅'])
  rw [Finset.sum_congr rfl fun a _ => sum_P_single _ _ _ _] at key
  rw [Finset.sum_congr rfl fun a ha => recoup_term_eq
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hb hb' hn₆ hn₆' hQ hQ' hn₅ hn₅'] at key
  have hbb : (n₂ + n₄ - n₆) / 2 = (n₂ + n₄ - n₆') / 2 ↔ n₆ = n₆' := by
    constructor <;> intro h <;> omega
  rw [sum_triad_reindex n₁ n₂ _ fun x hx => by rw [sixJ_eq_zero_of_not_triad₁ hx]; ring]
  have hc : 0 < √(((n₆ : ℝ) + 1) * ((n₆' : ℝ) + 1)) := Real.sqrt_pos.mpr (by positivity)
  have e : ∀ a, (((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * ((n₆ : ℝ) + 1) *
      sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆ * sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆' =
      ((n₆ : ℝ) + 1) / √(((n₆ : ℝ) + 1) * ((n₆' : ℝ) + 1)) *
        ((((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * √(((n₆ : ℝ) + 1) * ((n₆' : ℝ) + 1)) *
          sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆ * sixJ n₁ n₂ (n₁ + n₂ - 2 * a) n₄ n₅ n₆') := by
    intro a; field_simp
  rw [Finset.sum_congr rfl fun a _ => e a, ← Finset.mul_sum, key]
  by_cases h : n₆ = n₆'
  · subst h
    rw [ite_eq_left (hbb.mpr rfl), ite_eq_left rfl, mul_one,
      Real.sqrt_mul_self (by positivity)]
    exact div_self (by positivity)
  · rw [ite_eq_right (fun h' => h (hbb.mp h')), ite_eq_right h, mul_zero]

end QM
