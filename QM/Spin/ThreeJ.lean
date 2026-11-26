/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.Spin.CGCoeff

/-!
# Wigner 3j symbols

The 3j symbol `(j₁ j₂ j₃; m₁ m₂ m₃) = (-1)^(j₁ - j₂ - m₃) / √(2j₃ + 1) ⟨j₁ m₁; j₂ m₂ | j₃, -m₃⟩`
(`threeJ`), in the labels `nᵢ = 2jᵢ` and `xᵢ = jᵢ - mᵢ`. Racah's formula writes it as a sign, a
symmetric prefactor and the sum
`Σ_z (-1)^z / (z! (j₁+j₂-j₃-z)! (j₁-m₁-z)! (j₂+m₂-z)! (j₃-j₂+m₁+z)! (j₃-j₁-m₂+z)!)` over all
integers `z` (`threeJ_closed`). Every symmetry of the 3j symbol is a reindexing `z ↦ ±z + c` of this
sum.

## Main results

* `threeJ_cyclic`: invariance under cyclic permutations of the columns.
* `threeJ_swap12`, `threeJ_swap23`, `threeJ_swap13`: a transposition of two columns multiplies by
  `(-1)^(j₁ + j₂ + j₃)`.
* `threeJ_reverse`: so does `mᵢ ↦ -mᵢ`.
* `threeJ_orthogonal`: `Σ_{m₁ m₂} (2j₃ + 1) (j₁ j₂ j₃; m₁ m₂ m₃) (j₁ j₂ j₃'; m₁ m₂ m₃') = δ δ`.
-/

namespace QM

/-- The triangle and parity conditions on `(j₁ j₂ j₃)`, with `nᵢ = 2jᵢ`. -/
abbrev Triad (n₁ n₂ n₃ : ℕ) : Prop :=
  n₃ ≤ n₁ + n₂ ∧ n₁ ≤ n₂ + n₃ ∧ n₂ ≤ n₁ + n₃ ∧ Even (n₁ + n₂ + n₃)

/-- **Wigner 3j symbol** `(j₁ j₂ j₃; m₁ m₂ m₃)` with `nᵢ = 2jᵢ` and `xᵢ = jᵢ - mᵢ`:
`(-1)^(j₁ - j₂ - m₃) / √(2j₃ + 1) · ⟨j₁ m₁; j₂ m₂ | j₃, -m₃⟩`, and zero unless the triangle
condition holds. Here `J = j₃` and `M = -m₃` are the labels `p = j₁ + j₂ - j₃` and `k = j₃ + m₃` of
`cgCoeff`, and `j₁ - j₂ - m₃ ≡ x₃ + n₁ + (n₁ + n₂ + n₃)/2` modulo `2`. -/
noncomputable def threeJ (n₁ n₂ n₃ x₁ x₂ x₃ : ℕ) : ℝ :=
  if Triad n₁ n₂ n₃ ∧ x₃ ≤ n₃ then
    (-1) ^ (x₃ + n₁ + (n₁ + n₂ + n₃) / 2) / √((n₃ : ℝ) + 1) *
      cgCoeff n₁ n₂ ((n₁ + n₂ - n₃) / 2) (n₃ - x₃) x₁ x₂
  else 0

lemma threeJ_of_not {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (h : ¬(Triad n₁ n₂ n₃ ∧ x₃ ≤ n₃)) :
    threeJ n₁ n₂ n₃ x₁ x₂ x₃ = 0 := by
  rw [threeJ, ite_eq_right h]

/-- **Selection rule**: the 3j symbol vanishes unless `m₁ + m₂ + m₃ = 0`. -/
theorem threeJ_eq_zero {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (h : 2 * (x₁ + x₂ + x₃) ≠ n₁ + n₂ + n₃) :
    threeJ n₁ n₂ n₃ x₁ x₂ x₃ = 0 := by
  unfold threeJ
  split_ifs with ht
  · obtain ⟨⟨h1, h2, h3, ⟨r, hr⟩⟩, hx⟩ := ht
    rw [cgCoeff_eq_zero (by omega), mul_zero]
  · rfl

lemma threeJ_eq_zero_of_gt {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (h : n₁ < x₁ ∨ n₂ < x₂ ∨ n₃ < x₃) :
    threeJ n₁ n₂ n₃ x₁ x₂ x₃ = 0 := by
  unfold threeJ
  split_ifs with ht
  · rw [cgCoeff_of_not (by omega), mul_zero]
  · rfl

/-- **Orthogonality of the 3j symbols**
`Σ_{m₁ m₂} (2j₃ + 1) (j₁ j₂ j₃; m₁ m₂ m₃) (j₁ j₂ j₃'; m₁ m₂ m₃') = δ_{j₃ j₃'} δ_{m₃ m₃'}`. -/
theorem threeJ_orthogonal {n₁ n₂ n₃ n₃' x₃ x₃' : ℕ} (h : Triad n₁ n₂ n₃) (h' : Triad n₁ n₂ n₃')
    (hx : x₃ ≤ n₃) (hx' : x₃' ≤ n₃') :
    ∑ x₁ ∈ Finset.range (n₁ + 1), ∑ x₂ ∈ Finset.range (n₂ + 1),
      ((n₃ : ℝ) + 1) * threeJ n₁ n₂ n₃ x₁ x₂ x₃ * threeJ n₁ n₂ n₃' x₁ x₂ x₃' =
        if n₃ = n₃' ∧ x₃ = x₃' then 1 else 0 := by
  obtain ⟨h1, h2, h3, r, hr⟩ := h
  obtain ⟨h1', h2', h3', r', hr'⟩ := h'
  simp only [threeJ, ite_eq_left (show Triad n₁ n₂ n₃ ∧ x₃ ≤ n₃ from ⟨⟨h1, h2, h3, r, hr⟩, hx⟩),
    ite_eq_left (show Triad n₁ n₂ n₃' ∧ x₃' ≤ n₃' from ⟨⟨h1', h2', h3', r', hr'⟩, hx'⟩)]
  set c := (-1 : ℝ) ^ (x₃ + n₁ + (n₁ + n₂ + n₃) / 2) / √((n₃ : ℝ) + 1)
  set c' := (-1 : ℝ) ^ (x₃' + n₁ + (n₁ + n₂ + n₃') / 2) / √((n₃' : ℝ) + 1)
  have hp : (n₁ + n₂ - n₃) / 2 ≤ min n₁ n₂ := by omega
  have hk : n₃ - x₃ ≤ n₁ + n₂ - 2 * ((n₁ + n₂ - n₃) / 2) := by omega
  have hp' : (n₁ + n₂ - n₃') / 2 ≤ min n₁ n₂ := by omega
  have e : ∑ x₁ ∈ Finset.range (n₁ + 1), ∑ x₂ ∈ Finset.range (n₂ + 1),
      ((n₃ : ℝ) + 1) * (c * cgCoeff n₁ n₂ ((n₁ + n₂ - n₃) / 2) (n₃ - x₃) x₁ x₂) *
        (c' * cgCoeff n₁ n₂ ((n₁ + n₂ - n₃') / 2) (n₃' - x₃') x₁ x₂) =
      ((n₃ : ℝ) + 1) * c * c' * ∑ x₁ ∈ Finset.range (n₁ + 1), ∑ x₂ ∈ Finset.range (n₂ + 1),
        cgCoeff n₁ n₂ ((n₁ + n₂ - n₃) / 2) (n₃ - x₃) x₁ x₂ *
          cgCoeff n₁ n₂ ((n₁ + n₂ - n₃') / 2) (n₃' - x₃') x₁ x₂ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, cg_orthogonal_left hp hk hp']
  by_cases hn : n₃ = n₃' ∧ x₃ = x₃'
  · obtain ⟨rfl, rfl⟩ := hn
    rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left ⟨rfl, rfl⟩, mul_one]
    simp only [c, c']
    have hs : √((n₃ : ℝ) + 1) * √((n₃ : ℝ) + 1) = (n₃ : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hs0 : √((n₃ : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsq : ((-1 : ℝ) ^ (x₃ + n₁ + (n₁ + n₂ + n₃) / 2)) *
        (-1) ^ (x₃ + n₁ + (n₁ + n₂ + n₃) / 2) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [mul_assoc, div_mul_div_comm, hsq, hs]
    field_simp
  · rw [ite_eq_right hn, ite_eq_right]
    · ring
    · intro he
      apply hn
      obtain ⟨he1, he2⟩ := he
      have : n₃ = n₃' := by omega
      subst this
      exact ⟨rfl, by omega⟩

/-! ### Racah's form -/

/-- The summand of Racah's 3j sum at an integer `z`, with `s = j₁ + j₂ + j₃` and
`j₁ + j₂ - j₃ = s - n₃`. -/
noncomputable def tjTerm (n₁ n₂ n₃ x₁ x₂ s z : ℤ) : ℝ :=
  (-1 : ℝ) ^ z * (invFact z * invFact (s - n₃ - z) * invFact (x₁ - z) * invFact (n₂ - x₂ - z) *
    invFact (n₁ - (s - n₃) - x₁ + z) * invFact (x₂ - (s - n₃) + z))

/-- Racah's 3j sum over all integers. -/
noncomputable def tjSum (n₁ n₂ n₃ x₁ x₂ s : ℤ) : ℝ := ∑ᶠ z : ℤ, tjTerm n₁ n₂ n₃ x₁ x₂ s z

/-- The symmetric prefactor `Δ(j₁ j₂ j₃) √(Π (jᵢ - mᵢ)! (jᵢ + mᵢ)!)` with
`Δ² = (s - n₁)! (s - n₂)! (s - n₃)! / (s + 1)!`. -/
noncomputable def tjPre (n₁ n₂ n₃ x₁ x₂ x₃ : ℕ) : ℝ :=
  √((((n₁ + n₂ + n₃) / 2 - n₁).factorial * ((n₁ + n₂ + n₃) / 2 - n₂).factorial *
      ((n₁ + n₂ + n₃) / 2 - n₃).factorial : ℕ) / (((n₁ + n₂ + n₃) / 2 + 1).factorial : ℕ)) *
    √((x₁.factorial * (n₁ - x₁).factorial * x₂.factorial * (n₂ - x₂).factorial *
      x₃.factorial * (n₃ - x₃).factorial : ℕ) : ℝ)

lemma neg_one_zpow_eq {a b : ℤ} (h : Even (a - b)) : (-1 : ℝ) ^ a = (-1) ^ b := by
  rw [show a = (a - b) + b by ring, zpow_add₀ (by norm_num), h.neg_one_zpow, one_mul]

lemma neg_one_zpow_sub (a b : ℤ) : (-1 : ℝ) ^ (a - b) = (-1) ^ a * (-1) ^ b := by
  rw [← zpow_add₀ (by norm_num)]
  exact neg_one_zpow_eq ⟨-b, by ring⟩

lemma tjSum_eq_racahSum {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (h : Triad n₁ n₂ n₃)
    (hs : 2 * (x₁ + x₂ + x₃) = n₁ + n₂ + n₃) :
    tjSum n₁ n₂ n₃ x₁ x₂ ((n₁ + n₂ + n₃) / 2 : ℕ) = racahSum n₁ n₂ ((n₁ + n₂ - n₃) / 2) x₁ x₂ := by
  obtain ⟨h1, h2, h3, r, hr⟩ := h
  set p := (n₁ + n₂ - n₃) / 2
  have hp : (((n₁ + n₂ + n₃) / 2 : ℕ) : ℤ) - n₃ = p := by omega
  rw [← racahZ_eq_racahSum, racahZ, tjSum,
    finsum_eq_sum_of_support_subset _ (s := (Finset.range (p + 1)).map Nat.castEmbedding),
    Finset.sum_map]
  · refine Finset.sum_congr rfl fun z _ => ?_
    simp only [tjTerm, racahTerm, Nat.castEmbedding_apply, zpow_natCast, hp]
  · intro z hz
    rw [Function.mem_support] at hz
    simp only [Finset.coe_map, Nat.castEmbedding_apply, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    by_contra hc
    apply hz
    simp only [tjTerm, hp]
    rcases lt_or_ge z 0 with hz0 | hz0
    · rw [invFact_of_neg hz0]; ring
    · have : (p : ℤ) < z := by
        by_contra h'
        exact hc ⟨z.toNat, by omega, by omega⟩
      rw [invFact_of_neg (show (p : ℤ) - z < 0 by omega)]; ring

/-- **Racah's form of the 3j symbol.** -/
theorem threeJ_closed {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (h : Triad n₁ n₂ n₃) (hx₁ : x₁ ≤ n₁)
    (hx₂ : x₂ ≤ n₂) (hx₃ : x₃ ≤ n₃) (hs : 2 * (x₁ + x₂ + x₃) = n₁ + n₂ + n₃) :
    threeJ n₁ n₂ n₃ x₁ x₂ x₃ = (-1) ^ (x₃ + n₁ + (n₁ + n₂ + n₃) / 2) *
      tjPre n₁ n₂ n₃ x₁ x₂ x₃ * tjSum n₁ n₂ n₃ x₁ x₂ ((n₁ + n₂ + n₃) / 2 : ℕ) := by
  rw [threeJ, ite_eq_left ⟨h, hx₃⟩, tjSum_eq_racahSum h hs]
  obtain ⟨h1, h2, h3, r, hr⟩ := h
  rw [cg_racah (by omega) (by omega) hx₁ hx₂ (by omega),
    show n₁ + n₂ - 2 * ((n₁ + n₂ - n₃) / 2) + 1 = n₃ + 1 by omega,
    show n₁ - (n₁ + n₂ - n₃) / 2 = (n₁ + n₂ + n₃) / 2 - n₂ by omega,
    show n₂ - (n₁ + n₂ - n₃) / 2 = (n₁ + n₂ + n₃) / 2 - n₁ by omega,
    show (n₁ + n₂ - n₃) / 2 = (n₁ + n₂ + n₃) / 2 - n₃ by omega,
    show n₁ + n₂ - ((n₁ + n₂ + n₃) / 2 - n₃) + 1 = (n₁ + n₂ + n₃) / 2 + 1 by omega,
    show n₁ + n₂ - 2 * ((n₁ + n₂ + n₃) / 2 - n₃) - (n₃ - x₃) = x₃ by omega]
  have e1 : √((((n₃ + 1 : ℕ) : ℝ)) * (((n₁ + n₂ + n₃) / 2 - n₂).factorial : ℕ) *
      (((n₁ + n₂ + n₃) / 2 - n₁).factorial : ℕ) * (((n₁ + n₂ + n₃) / 2 - n₃).factorial : ℕ) /
        (((n₁ + n₂ + n₃) / 2 + 1).factorial : ℕ)) =
      √((n₃ : ℝ) + 1) * √((((n₁ + n₂ + n₃) / 2 - n₁).factorial *
        ((n₁ + n₂ + n₃) / 2 - n₂).factorial * ((n₁ + n₂ + n₃) / 2 - n₃).factorial : ℕ) /
          (((n₁ + n₂ + n₃) / 2 + 1).factorial : ℕ)) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    push_cast; ring
  have e2 : √((((x₃.factorial : ℕ) : ℝ)) * ((n₃ - x₃).factorial : ℕ) * (x₁.factorial : ℕ) *
      ((n₁ - x₁).factorial : ℕ) * (x₂.factorial : ℕ) * ((n₂ - x₂).factorial : ℕ)) =
      √((x₁.factorial * (n₁ - x₁).factorial * x₂.factorial * (n₂ - x₂).factorial *
        x₃.factorial * (n₃ - x₃).factorial : ℕ) : ℝ) := by
    congr 1
    push_cast; ring
  rw [e1, e2, tjPre]
  have hs0 : √((n₃ : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-! ### Symmetries of Racah's sum -/

lemma tjSum_cyclic {n₁ n₂ n₃ x₁ x₂ x₃ s : ℤ} (h2s : 2 * s = n₁ + n₂ + n₃)
    (hs : s = x₁ + x₂ + x₃) :
    tjSum n₂ n₃ n₁ x₂ x₃ s = (-1) ^ (x₂ - s + n₃) * tjSum n₁ n₂ n₃ x₁ x₂ s := by
  unfold tjSum
  rw [mul_finsum]
  conv_lhs => rw [← finsum_comp_equiv (Equiv.addRight (x₂ - s + n₃))]
  refine finsum_congr fun z => ?_
  simp only [Equiv.coe_addRight, tjTerm]
  rw [zpow_add₀ (by norm_num),
    show s - n₁ - (z + (x₂ - s + n₃)) = n₂ - x₂ - z by omega,
    show x₂ - (z + (x₂ - s + n₃)) = s - n₃ - z by omega,
    show n₃ - x₃ - (z + (x₂ - s + n₃)) = x₁ - z by omega,
    show n₂ - (s - n₁) - x₂ + (z + (x₂ - s + n₃)) = z by omega,
    show x₃ - (s - n₁) + (z + (x₂ - s + n₃)) = n₁ - (s - n₃) - x₁ + z by omega,
    show z + (x₂ - s + n₃) = x₂ - (s - n₃) + z by omega]
  ring

lemma tjSum_reverse (n₁ n₂ n₃ x₁ x₂ s : ℤ) :
    tjSum n₁ n₂ n₃ (n₁ - x₁) (n₂ - x₂) s = (-1) ^ (s - n₃) * tjSum n₁ n₂ n₃ x₁ x₂ s := by
  unfold tjSum
  rw [mul_finsum]
  conv_lhs => rw [← finsum_comp_equiv (Equiv.subLeft (s - n₃))]
  refine finsum_congr fun z => ?_
  simp only [Equiv.subLeft_apply, tjTerm]
  rw [neg_one_zpow_sub,
    show s - n₃ - (s - n₃ - z) = z by omega,
    show n₁ - x₁ - (s - n₃ - z) = n₁ - (s - n₃) - x₁ + z by omega,
    show n₂ - (n₂ - x₂) - (s - n₃ - z) = x₂ - (s - n₃) + z by omega,
    show n₁ - (s - n₃) - (n₁ - x₁) + (s - n₃ - z) = x₁ - z by omega,
    show n₂ - x₂ - (s - n₃) + (s - n₃ - z) = n₂ - x₂ - z by omega]
  ring

lemma tjSum_swap_reverse (n₁ n₂ n₃ x₁ x₂ s : ℤ) :
    tjSum n₂ n₁ n₃ (n₂ - x₂) (n₁ - x₁) s = tjSum n₁ n₂ n₃ x₁ x₂ s := by
  unfold tjSum
  refine finsum_congr fun z => ?_
  simp only [tjTerm]
  rw [show n₁ - (n₁ - x₁) - z = x₁ - z by omega,
    show n₂ - (s - n₃) - (n₂ - x₂) + z = x₂ - (s - n₃) + z by omega,
    show n₁ - x₁ - (s - n₃) + z = n₁ - (s - n₃) - x₁ + z by omega]
  ring

/-! ### Symmetries of the 3j symbol -/

lemma triad_cyclic {n₁ n₂ n₃ : ℕ} : Triad n₂ n₃ n₁ ↔ Triad n₁ n₂ n₃ := by
  simp only [Triad, show n₂ + n₃ + n₁ = n₁ + n₂ + n₃ by ring]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by omega, by omega, by omega, h4⟩

lemma triad_swap12 {n₁ n₂ n₃ : ℕ} : Triad n₂ n₁ n₃ ↔ Triad n₁ n₂ n₃ := by
  simp only [Triad, show n₂ + n₁ + n₃ = n₁ + n₂ + n₃ by ring]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by omega, by omega, by omega, h4⟩

lemma tjPre_cyclic (n₁ n₂ n₃ x₁ x₂ x₃ : ℕ) :
    tjPre n₂ n₃ n₁ x₂ x₃ x₁ = tjPre n₁ n₂ n₃ x₁ x₂ x₃ := by
  unfold tjPre
  rw [show n₂ + n₃ + n₁ = n₁ + n₂ + n₃ by ring]
  congr 2
  · push_cast; ring
  · push_cast; ring

lemma tjPre_swap_reverse {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (hx₁ : x₁ ≤ n₁) (hx₂ : x₂ ≤ n₂)
    (hx₃ : x₃ ≤ n₃) :
    tjPre n₂ n₁ n₃ (n₂ - x₂) (n₁ - x₁) (n₃ - x₃) = tjPre n₁ n₂ n₃ x₁ x₂ x₃ := by
  unfold tjPre
  rw [show n₂ + n₁ + n₃ = n₁ + n₂ + n₃ by ring, Nat.sub_sub_self hx₁, Nat.sub_sub_self hx₂,
    Nat.sub_sub_self hx₃]
  congr 2
  · push_cast; ring
  · push_cast; ring

lemma tjPre_reverse {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (hx₁ : x₁ ≤ n₁) (hx₂ : x₂ ≤ n₂) (hx₃ : x₃ ≤ n₃) :
    tjPre n₁ n₂ n₃ (n₁ - x₁) (n₂ - x₂) (n₃ - x₃) = tjPre n₁ n₂ n₃ x₁ x₂ x₃ := by
  unfold tjPre
  rw [Nat.sub_sub_self hx₁, Nat.sub_sub_self hx₂, Nat.sub_sub_self hx₃]
  congr 2
  push_cast; ring

/-- **Cyclic symmetry**: `(j₂ j₃ j₁; m₂ m₃ m₁) = (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
theorem threeJ_cyclic (n₁ n₂ n₃ x₁ x₂ x₃ : ℕ) :
    threeJ n₂ n₃ n₁ x₂ x₃ x₁ = threeJ n₁ n₂ n₃ x₁ x₂ x₃ := by
  by_cases ht : Triad n₁ n₂ n₃
  swap
  · rw [threeJ_of_not (by rw [triad_cyclic]; tauto), threeJ_of_not (by tauto)]
  by_cases hx : x₁ ≤ n₁ ∧ x₂ ≤ n₂ ∧ x₃ ≤ n₃
  swap
  · rw [threeJ_eq_zero_of_gt (by omega), threeJ_eq_zero_of_gt (by omega)]
  by_cases hs : 2 * (x₁ + x₂ + x₃) = n₁ + n₂ + n₃
  swap
  · rw [threeJ_eq_zero (by omega), threeJ_eq_zero hs]
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  rw [threeJ_closed (triad_cyclic.mpr ht) hx₂ hx₃ hx₁ (by omega),
    threeJ_closed ht hx₁ hx₂ hx₃ hs, tjPre_cyclic, show n₂ + n₃ + n₁ = n₁ + n₂ + n₃ by ring]
  obtain ⟨h1, h2, h3, r, hr⟩ := ht
  rw [tjSum_cyclic (x₁ := x₁) (by omega) (by omega), ← zpow_natCast, ← zpow_natCast]
  have e : (-1 : ℝ) ^ (((x₁ + n₂ + (n₁ + n₂ + n₃) / 2 : ℕ) : ℤ)) *
      (-1) ^ ((x₂ : ℤ) - (((n₁ + n₂ + n₃) / 2 : ℕ) : ℤ) + n₃) =
      (-1) ^ (((x₃ + n₁ + (n₁ + n₂ + n₃) / 2 : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (by norm_num)]
    exact neg_one_zpow_eq ⟨(r : ℤ) - n₁ - x₃, by omega⟩
  linear_combination (tjPre n₁ n₂ n₃ x₁ x₂ x₃ *
    tjSum n₁ n₂ n₃ x₁ x₂ (((n₁ + n₂ + n₃) / 2 : ℕ) : ℤ)) * e

lemma threeJ_swap_reverse {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (hx₁ : x₁ ≤ n₁) (hx₂ : x₂ ≤ n₂)
    (hx₃ : x₃ ≤ n₃) :
    threeJ n₂ n₁ n₃ (n₂ - x₂) (n₁ - x₁) (n₃ - x₃) = threeJ n₁ n₂ n₃ x₁ x₂ x₃ := by
  by_cases ht : Triad n₁ n₂ n₃
  swap
  · rw [threeJ_of_not (by rw [triad_swap12]; tauto), threeJ_of_not (by tauto)]
  by_cases hs : 2 * (x₁ + x₂ + x₃) = n₁ + n₂ + n₃
  swap
  · rw [threeJ_eq_zero (by omega), threeJ_eq_zero hs]
  rw [threeJ_closed (triad_swap12.mpr ht) (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
      (by omega), threeJ_closed ht hx₁ hx₂ hx₃ hs, tjPre_swap_reverse hx₁ hx₂ hx₃,
    show n₂ + n₁ + n₃ = n₁ + n₂ + n₃ by ring]
  obtain ⟨h1, h2, h3, r, hr⟩ := ht
  rw [show (((n₂ - x₂ : ℕ) : ℤ)) = n₂ - x₂ by omega, show (((n₁ - x₁ : ℕ) : ℤ)) = n₁ - x₁ by omega,
    tjSum_swap_reverse, ← zpow_natCast, ← zpow_natCast,
    neg_one_zpow_eq (a := ((n₃ - x₃ + n₂ + (n₁ + n₂ + n₃) / 2 : ℕ) : ℤ))
      (b := ((x₃ + n₁ + (n₁ + n₂ + n₃) / 2 : ℕ) : ℤ)) ⟨(r : ℤ) - n₁ - x₃, by omega⟩]

/-- **Reversal of the projections**:
`(j₁ j₂ j₃; -m₁ -m₂ -m₃) = (-1)^(j₁+j₂+j₃) (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
theorem threeJ_reverse {n₁ n₂ n₃ x₁ x₂ x₃ : ℕ} (hx₁ : x₁ ≤ n₁) (hx₂ : x₂ ≤ n₂) (hx₃ : x₃ ≤ n₃) :
    threeJ n₁ n₂ n₃ (n₁ - x₁) (n₂ - x₂) (n₃ - x₃) =
      (-1) ^ ((n₁ + n₂ + n₃) / 2) * threeJ n₁ n₂ n₃ x₁ x₂ x₃ := by
  by_cases ht : Triad n₁ n₂ n₃
  swap
  · rw [threeJ_of_not (by tauto), threeJ_of_not (by tauto), mul_zero]
  by_cases hs : 2 * (x₁ + x₂ + x₃) = n₁ + n₂ + n₃
  swap
  · rw [threeJ_eq_zero (by omega), threeJ_eq_zero hs, mul_zero]
  rw [threeJ_closed ht (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _) (by omega),
    threeJ_closed ht hx₁ hx₂ hx₃ hs, tjPre_reverse hx₁ hx₂ hx₃]
  obtain ⟨h1, h2, h3, r, hr⟩ := ht
  rw [show (((n₁ - x₁ : ℕ) : ℤ)) = n₁ - x₁ by omega, show (((n₂ - x₂ : ℕ) : ℤ)) = n₂ - x₂ by omega,
    tjSum_reverse, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast]
  have e : (-1 : ℝ) ^ (((n₃ - x₃ + n₁ + (n₁ + n₂ + n₃) / 2 : ℕ) : ℤ)) *
      (-1) ^ ((((n₁ + n₂ + n₃) / 2 : ℕ) : ℤ) - n₃) =
      (-1) ^ (((n₁ + n₂ + n₃) / 2 : ℕ) : ℤ) *
        (-1) ^ (((x₃ + n₁ + (n₁ + n₂ + n₃) / 2 : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
    exact neg_one_zpow_eq ⟨-(x₃ : ℤ), by omega⟩
  linear_combination (tjPre n₁ n₂ n₃ x₁ x₂ x₃ *
    tjSum n₁ n₂ n₃ x₁ x₂ (((n₁ + n₂ + n₃) / 2 : ℕ) : ℤ)) * e

/-- **Transposition of the first two columns**:
`(j₂ j₁ j₃; m₂ m₁ m₃) = (-1)^(j₁+j₂+j₃) (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
theorem threeJ_swap12 (n₁ n₂ n₃ x₁ x₂ x₃ : ℕ) :
    threeJ n₂ n₁ n₃ x₂ x₁ x₃ = (-1) ^ ((n₁ + n₂ + n₃) / 2) * threeJ n₁ n₂ n₃ x₁ x₂ x₃ := by
  by_cases hx : x₁ ≤ n₁ ∧ x₂ ≤ n₂ ∧ x₃ ≤ n₃
  swap
  · rw [threeJ_eq_zero_of_gt (by omega), threeJ_eq_zero_of_gt (by omega), mul_zero]
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  have := threeJ_swap_reverse (Nat.sub_le n₁ x₁) (Nat.sub_le n₂ x₂) (Nat.sub_le n₃ x₃)
  rw [Nat.sub_sub_self hx₁, Nat.sub_sub_self hx₂, Nat.sub_sub_self hx₃] at this
  rw [this, threeJ_reverse hx₁ hx₂ hx₃]

/-- **Transposition of the last two columns**. -/
theorem threeJ_swap23 (n₁ n₂ n₃ x₁ x₂ x₃ : ℕ) :
    threeJ n₁ n₃ n₂ x₁ x₃ x₂ = (-1) ^ ((n₁ + n₂ + n₃) / 2) * threeJ n₁ n₂ n₃ x₁ x₂ x₃ := by
  rw [threeJ_cyclic n₂ n₁ n₃ x₂ x₁ x₃, threeJ_swap12]

/-- **Transposition of the first and last columns**. -/
theorem threeJ_swap13 (n₁ n₂ n₃ x₁ x₂ x₃ : ℕ) :
    threeJ n₃ n₂ n₁ x₃ x₂ x₁ = (-1) ^ ((n₁ + n₂ + n₃) / 2) * threeJ n₁ n₂ n₃ x₁ x₂ x₃ := by
  rw [threeJ_cyclic n₁ n₃ n₂ x₁ x₃ x₂, threeJ_swap23]

end QM
