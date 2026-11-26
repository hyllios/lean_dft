/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.Spin.SixJ

/-!
# Recoupling of four angular momenta and the 9j symbols

Work in the product basis of four spins. The coupled states are explicit sums of products of
Clebsch–Gordan coefficients. Overlaps of states that share a coupled pair reduce to the recoupling
of three angular momenta (`recoup3`), and the overlap of `|(j₁ j₂) j₁₂, (j₃ j₄) j₃₄; J M⟩` with
`|(j₁ j₃) j₁₃, (j₂ j₄) j₂₄; J M⟩` follows by inserting the complete sets `|j₁, (j₂ (j₃ j₄)) x; J M⟩`
and `|j₁, ((j₂ j₄) j₃) x; J M⟩`.

## Main results

* `cg_exchange`: `⟨j₁ m₁; j₂ m₂ | J M⟩ = (-1)^(j₁ + j₂ - J) ⟨j₂ m₂; j₁ m₁ | J M⟩`.
* `cV_complete`, `cU_expand`: completeness of the couplings of three spins and the expansion of one
  coupling in the other.
* `recoup4_chain`: the overlap as a sum over the intermediate `x` of three recoupling coefficients.
* `recoup4_eq_nineJ`: the overlap is `√((2j₁₂+1)(2j₃₄+1)(2j₁₃+1)(2j₂₄+1))` times the 9j symbol.
-/

namespace QM

open Finset

/-- **Exchange symmetry** `⟨j₁ m₁; j₂ m₂ | J M⟩ = (-1)^(j₁ + j₂ - J) ⟨j₂ m₂; j₁ m₁ | J M⟩`. -/
theorem cg_exchange {n₁ n₂ p : ℕ} (hp : p ≤ min n₁ n₂) (K x y : ℕ) :
    cgCoeff n₁ n₂ p K x y = (-1) ^ p * cgCoeff n₂ n₁ p K y x := by
  have hp1 := le_trans hp (min_le_left _ _)
  have hp2 := le_trans hp (min_le_right _ _)
  rcases lt_or_ge (n₁ + n₂ - 2 * p) K with hK | hK
  · rw [cgCoeff_eq_zero_of_lt hp hK, cgCoeff_eq_zero_of_lt (by rwa [min_comm])
      (by rw [add_comm]; exact hK), mul_zero]
  have ht : Triad n₁ n₂ (n₁ + n₂ - 2 * p) :=
    ⟨by omega, by omega, by omega, ⟨n₁ + n₂ - p, by omega⟩⟩
  have ht' : Triad n₂ n₁ (n₁ + n₂ - 2 * p) :=
    ⟨by omega, by omega, by omega, ⟨n₁ + n₂ - p, by omega⟩⟩
  have e1 := threeJ_eq_cg (x₁ := x) (x₂ := y) ht (Nat.sub_le _ K)
  have e2 := threeJ_eq_cg (x₁ := y) (x₂ := x) ht' (Nat.sub_le _ K)
  have e3 := threeJ_swap12 n₁ n₂ (n₁ + n₂ - 2 * p) x y (n₁ + n₂ - 2 * p - K)
  rw [show (n₁ + n₂ - (n₁ + n₂ - 2 * p)) / 2 = p by omega,
    show n₁ + n₂ - 2 * p - (n₁ + n₂ - 2 * p - K) = K by omega] at e1
  rw [show (n₂ + n₁ - (n₁ + n₂ - 2 * p)) / 2 = p by omega,
    show n₁ + n₂ - 2 * p - (n₁ + n₂ - 2 * p - K) = K by omega] at e2
  rw [e1, e2] at e3
  have hs : √(((n₁ + n₂ - 2 * p : ℕ) : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have d1 : (n₂ + n₁ + (n₁ + n₂ - 2 * p)) / 2 = n₁ + n₂ - p := by omega
  have d2 : (n₁ + n₂ + (n₁ + n₂ - 2 * p)) / 2 = n₁ + n₂ - p := by omega
  rw [d1, d2] at e3
  have hsg : ((-1 : ℝ) ^ (n₁ + n₂ - 2 * p - K + n₂ + (n₁ + n₂ - p))) =
      (-1) ^ (n₁ + n₂ - p) * (-1) ^ (n₁ + n₂ - 2 * p - K + n₁ + (n₁ + n₂ - p)) * (-1) ^ p := by
    simp only [← pow_add]
    exact neg_one_pow_eq_of_even (Nat.even_iff.mpr (by omega))
  rw [hsg] at e3
  field_simp at e3
  exact e3.symm

/-! ### Three spins: completeness and expansions -/

/-- **Completeness of the couplings** `|j₁, (j₂ j₃) j₂₃; J M⟩`. -/
theorem cV_complete (n₁ n₂ n₃ : ℕ) {i j : ℕ × ℕ × ℕ} (hi : i ∈ idx3 n₁ n₂ n₃)
    (hj : j ∈ idx3 n₁ n₂ n₃) :
    ∑ b ∈ range (min n₂ n₃ + 1), ∑ Q ∈ range (min n₁ (n₂ + n₃ - 2 * b) + 1),
      ∑ K ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
        cV n₁ n₂ n₃ b Q K i * cV n₁ n₂ n₃ b Q K j = if i = j then 1 else 0 := by
  rw [mem_idx3] at hi hj
  obtain ⟨i1, i2, i3⟩ := i
  obtain ⟨j1, j2, j3⟩ := j
  simp only at hi hj
  have inner : ∀ b, ∑ Q ∈ range (min n₁ (n₂ + n₃ - 2 * b) + 1),
      ∑ K ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
        cV n₁ n₂ n₃ b Q K (i1, i2, i3) * cV n₁ n₂ n₃ b Q K (j1, j2, j3) =
      if i1 = j1 then ∑ u ∈ range (n₂ + n₃ - 2 * b + 1),
        cgCoeff n₂ n₃ b u i2 i3 * cgCoeff n₂ n₃ b u j2 j3 else 0 := by
    intro b
    simp only [cV, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl
      fun u _ => Finset.sum_congr rfl fun u' _ => (show
        cgCoeff n₂ n₃ b u i2 i3 * cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K i1 u *
          (cgCoeff n₂ n₃ b u' j2 j3 * cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K j1 u') =
        cgCoeff n₂ n₃ b u i2 i3 * cgCoeff n₂ n₃ b u' j2 j3 *
          (cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K i1 u * cgCoeff n₁ (n₂ + n₃ - 2 * b) Q K j1 u')
        by ring)]
    rw [Finset.sum_congr rfl fun Q _ => sum3_rotate _ _ _ _, sum3_rotate]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => by
      rw [cg_orthogonal_right hi.1 hj.1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu'))]]
    split_ifs with h1
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.sum_eq_single u]
      · simp [h1]
      · intro u' _ hne; simp [Ne.symm hne]
      · intro h; exact absurd hu h
    · simp [h1]
  rw [Finset.sum_congr rfl fun b _ => inner b]
  by_cases h1 : i1 = j1
  · simp only [h1, ite_true]
    rw [cg_orthogonal_right hi.2.1 hj.2.1 hi.2.2 hj.2.2]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  · simp only [h1, ite_false, Finset.sum_const_zero, Prod.mk.injEq]
    split_ifs <;> simp_all

/-- **Expansion** of `|(j₁ j₂) j₁₂, j₃; J M⟩` in the states `|j₁, (j₂ j₃) j₂₃; J M⟩`. -/
theorem cU_expand {n₁ n₂ n₃ a P K : ℕ} (ha : a ≤ min n₁ n₂)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) n₃) (hK : K ≤ n₁ + n₂ - 2 * a + n₃ - 2 * P)
    {i : ℕ × ℕ × ℕ} (hi : i ∈ idx3 n₁ n₂ n₃) :
    cU n₁ n₂ n₃ a P K i = ∑ b ∈ range (min n₂ n₃ + 1),
      if Triad n₁ (n₂ + n₃ - 2 * b) (n₁ + n₂ - 2 * a + n₃ - 2 * P) then
        recoup3 n₁ n₂ n₃ a b P ((n₁ + (n₂ + n₃ - 2 * b) - (n₁ + n₂ - 2 * a + n₃ - 2 * P)) / 2) K *
          cV n₁ n₂ n₃ b ((n₁ + (n₂ + n₃ - 2 * b) - (n₁ + n₂ - 2 * a + n₃ - 2 * P)) / 2) K i
      else 0 := by
  set N := n₁ + n₂ - 2 * a + n₃ - 2 * P with hNd
  have e : cU n₁ n₂ n₃ a P K i = ∑ b ∈ range (min n₂ n₃ + 1),
      ∑ Q ∈ range (min n₁ (n₂ + n₃ - 2 * b) + 1),
        ∑ K' ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
          cV n₁ n₂ n₃ b Q K' i *
            ∑ j ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K j * cV n₁ n₂ n₃ b Q K' j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun Q _ => Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
    rw [Finset.sum_eq_single i]
    · symm
      rw [show ∑ b ∈ range (min n₂ n₃ + 1), ∑ Q ∈ range (min n₁ (n₂ + n₃ - 2 * b) + 1),
          ∑ K' ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
            cV n₁ n₂ n₃ b Q K' i * (cU n₁ n₂ n₃ a P K i * cV n₁ n₂ n₃ b Q K' i) =
          cU n₁ n₂ n₃ a P K i * ∑ b ∈ range (min n₂ n₃ + 1),
            ∑ Q ∈ range (min n₁ (n₂ + n₃ - 2 * b) + 1),
              ∑ K' ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
                cV n₁ n₂ n₃ b Q K' i * cV n₁ n₂ n₃ b Q K' i by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring,
        cV_complete n₁ n₂ n₃ hi hi, ite_eq_left rfl, mul_one]
    · intro j hj hne
      have := cV_complete n₁ n₂ n₃ hi hj
      rw [ite_eq_right (Ne.symm hne)] at this
      rw [show ∑ b ∈ range (min n₂ n₃ + 1), ∑ Q ∈ range (min n₁ (n₂ + n₃ - 2 * b) + 1),
          ∑ K' ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
            cV n₁ n₂ n₃ b Q K' i * (cU n₁ n₂ n₃ a P K j * cV n₁ n₂ n₃ b Q K' j) =
          cU n₁ n₂ n₃ a P K j * ∑ b ∈ range (min n₂ n₃ + 1),
            ∑ Q ∈ range (min n₁ (n₂ + n₃ - 2 * b) + 1),
              ∑ K' ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
                cV n₁ n₂ n₃ b Q K' i * cV n₁ n₂ n₃ b Q K' j by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring, this, mul_zero]
    · intro h; exact absurd hi h
  rw [e]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  rw [Finset.sum_congr rfl fun Q hQ => (show
    ∑ K' ∈ range (n₁ + (n₂ + n₃ - 2 * b) - 2 * Q + 1),
      cV n₁ n₂ n₃ b Q K' i * ∑ j ∈ idx3 n₁ n₂ n₃, cU n₁ n₂ n₃ a P K j * cV n₁ n₂ n₃ b Q K' j =
    if N = n₁ + (n₂ + n₃ - 2 * b) - 2 * Q then
      recoup3 n₁ n₂ n₃ a b P Q K * cV n₁ n₂ n₃ b Q K i else 0 by
    split_ifs with hN
    · rw [Finset.sum_eq_single K]
      · rw [mul_comm]; rfl
      · intro K' hK' hne
        rw [cU_cV_eq_zero ha hb' hP (Nat.lt_succ_iff.mp (Finset.mem_range.mp hQ)) hK
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hK')) (fun h => hne h.2.symm), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · refine Finset.sum_eq_zero fun K' hK' => ?_
      rw [cU_cV_eq_zero ha hb' hP (Nat.lt_succ_iff.mp (Finset.mem_range.mp hQ)) hK
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hK')) (fun h => hN h.1), mul_zero])]
  simp_rw [eq_comm (a := N)]
  exact sum_P_single n₁ (n₂ + n₃ - 2 * b) N _

/-! ### Four spins -/

/-- The overlap of `|j₂, (j₃ j₄) j₃₄; x u⟩` with `|(j₂ j₄) j₂₄, j₃; x' u'⟩`. -/
lemma overlap_inner {n₂ n₃ n₄ b c e g u u' : ℕ} (hc : c ≤ min n₃ n₄) (he : e ≤ min n₂ n₄)
    (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c)) (hg : g ≤ min (n₂ + n₄ - 2 * e) n₃)
    (hu : u ≤ n₂ + (n₃ + n₄ - 2 * c) - 2 * b) (hu' : u' ≤ n₂ + n₄ - 2 * e + n₃ - 2 * g) :
    ∑ x₂ ∈ range (n₂ + 1), ∑ x₃ ∈ range (n₃ + 1), ∑ x₄ ∈ range (n₄ + 1),
      (∑ v ∈ range (n₃ + n₄ - 2 * c + 1),
          cgCoeff n₃ n₄ c v x₃ x₄ * cgCoeff n₂ (n₃ + n₄ - 2 * c) b u x₂ v) *
        (∑ v ∈ range (n₂ + n₄ - 2 * e + 1),
          cgCoeff n₂ n₄ e v x₂ x₄ * cgCoeff n₃ (n₂ + n₄ - 2 * e) g u' x₃ v) =
      (-1) ^ (c + g) * (if n₂ + (n₃ + n₄ - 2 * c) - 2 * b = n₂ + n₄ - 2 * e + n₃ - 2 * g ∧ u = u'
        then recoup3 n₂ n₄ n₃ e c g b 0 else 0) := by
  have hc' : c ≤ min n₄ n₃ := by rwa [min_comm]
  have hg' : g ≤ min n₃ (n₂ + n₄ - 2 * e) := by rwa [min_comm]
  have e34 : n₃ + n₄ - 2 * c = n₄ + n₃ - 2 * c := by rw [add_comm n₃]
  have key : ∀ x₂ x₃ x₄,
      (∑ v ∈ range (n₃ + n₄ - 2 * c + 1),
          cgCoeff n₃ n₄ c v x₃ x₄ * cgCoeff n₂ (n₃ + n₄ - 2 * c) b u x₂ v) *
        (∑ v ∈ range (n₂ + n₄ - 2 * e + 1),
          cgCoeff n₂ n₄ e v x₂ x₄ * cgCoeff n₃ (n₂ + n₄ - 2 * e) g u' x₃ v) =
      (-1) ^ (c + g) * (cU n₂ n₄ n₃ e g u' (x₂, x₄, x₃) * cV n₂ n₄ n₃ c b u (x₂, x₄, x₃)) := by
    intro x₂ x₃ x₄
    have hA : ∑ v ∈ range (n₃ + n₄ - 2 * c + 1),
        cgCoeff n₃ n₄ c v x₃ x₄ * cgCoeff n₂ (n₃ + n₄ - 2 * c) b u x₂ v =
        (-1) ^ c * cV n₂ n₄ n₃ c b u (x₂, x₄, x₃) := by
      simp only [cV]
      rw [← e34, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [cg_exchange hc]; ring
    have hB : ∑ v ∈ range (n₂ + n₄ - 2 * e + 1),
        cgCoeff n₂ n₄ e v x₂ x₄ * cgCoeff n₃ (n₂ + n₄ - 2 * e) g u' x₃ v =
        (-1) ^ g * cU n₂ n₄ n₃ e g u' (x₂, x₄, x₃) := by
      simp only [cU]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [cg_exchange hg']; ring
    rw [hA, hB, pow_add]; ring
  rw [Finset.sum_congr rfl fun x₂ _ => Finset.sum_congr rfl fun x₃ _ =>
    Finset.sum_congr rfl fun x₄ _ => key x₂ x₃ x₄]
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun x₂ _ => Finset.sum_comm]
  rw [← sum_idx3 n₂ n₄ n₃ (fun t s r => cU n₂ n₄ n₃ e g u' (t, s, r) *
    cV n₂ n₄ n₃ c b u (t, s, r))]
  have hb' : b ≤ min n₂ (n₄ + n₃ - 2 * c) := by rwa [← e34]
  split_ifs with h
  · obtain ⟨hN, huu⟩ := h
    subst huu
    change recoup3 n₂ n₄ n₃ e c g b u = _
    rw [recoup3_const he hc' hg hb' (by rw [← e34]; omega) hu']
  · exact cU_cV_eq_zero he hc' hg hb' hu' (by rw [← e34]; exact hu)
      (fun h' => h ⟨by rw [e34]; omega, h'.2.symm⟩)

/-- `|j₁, (j₂ (j₃ j₄) j₃₄) x; J M⟩` with `x = j₂ + j₃₄ - b`, `J = j₁ + x - R`, `M = J - K`. -/
noncomputable def stE1 (n₁ n₂ n₃ n₄ c b R K x₁ x₂ x₃ x₄ : ℕ) : ℝ :=
  ∑ v ∈ range (n₃ + n₄ - 2 * c + 1),
    cgCoeff n₃ n₄ c v x₃ x₄ * cV n₁ n₂ (n₃ + n₄ - 2 * c) b R K (x₁, x₂, v)

/-- `|j₁, ((j₂ j₄) j₂₄ j₃) x; J M⟩` with `x = j₂₄ + j₃ - g`, `J = j₁ + x - R`, `M = J - K`. -/
noncomputable def stE2 (n₁ n₂ n₃ n₄ e g R K x₁ x₂ x₃ x₄ : ℕ) : ℝ :=
  ∑ v ∈ range (n₂ + n₄ - 2 * e + 1),
    cgCoeff n₂ n₄ e v x₂ x₄ * cV n₁ n₃ (n₂ + n₄ - 2 * e) g R K (x₁, x₃, v)

/-- Sum over the product basis of four spins. -/
noncomputable def sum4 (n₁ n₂ n₃ n₄ : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ x₁ ∈ range (n₁ + 1), ∑ x₂ ∈ range (n₂ + 1), ∑ x₃ ∈ range (n₃ + 1), ∑ x₄ ∈ range (n₄ + 1),
    F x₁ x₂ x₃ x₄

lemma stE1_eq (n₁ n₂ n₃ n₄ c b R K x₁ x₂ x₃ x₄ : ℕ) :
    stE1 n₁ n₂ n₃ n₄ c b R K x₁ x₂ x₃ x₄ =
      ∑ u ∈ range (n₂ + (n₃ + n₄ - 2 * c) - 2 * b + 1),
        cgCoeff n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) R K x₁ u *
          ∑ v ∈ range (n₃ + n₄ - 2 * c + 1),
            cgCoeff n₃ n₄ c v x₃ x₄ * cgCoeff n₂ (n₃ + n₄ - 2 * c) b u x₂ v := by
  simp only [stE1, cV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma stE2_eq (n₁ n₂ n₃ n₄ e g R K x₁ x₂ x₃ x₄ : ℕ) :
    stE2 n₁ n₂ n₃ n₄ e g R K x₁ x₂ x₃ x₄ =
      ∑ u ∈ range (n₃ + (n₂ + n₄ - 2 * e) - 2 * g + 1),
        cgCoeff n₁ (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) R K x₁ u *
          ∑ v ∈ range (n₂ + n₄ - 2 * e + 1),
            cgCoeff n₂ n₄ e v x₂ x₄ * cgCoeff n₃ (n₂ + n₄ - 2 * e) g u x₃ v := by
  simp only [stE2, cV, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The overlap of the two intermediate couplings.** -/
lemma overlap_E {n₁ n₂ n₃ n₄ b c e g R R' K : ℕ} (hc : c ≤ min n₃ n₄) (he : e ≤ min n₂ n₄)
    (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c)) (hg : g ≤ min (n₂ + n₄ - 2 * e) n₃)
    (hR : R ≤ min n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b))
    (hK : K ≤ n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) - 2 * R)
    (hR' : R' ≤ min n₁ (n₃ + (n₂ + n₄ - 2 * e) - 2 * g))
    (hRR : n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) - 2 * R =
      n₁ + (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) - 2 * R') :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ => stE1 n₁ n₂ n₃ n₄ c b R K x₁ x₂ x₃ x₄ *
      stE2 n₁ n₂ n₃ n₄ e g R' K x₁ x₂ x₃ x₄) =
      (-1) ^ (c + g) * (if n₂ + (n₃ + n₄ - 2 * c) - 2 * b = n₂ + n₄ - 2 * e + n₃ - 2 * g then
        recoup3 n₂ n₄ n₃ e c g b 0 else 0) := by
  set j := n₂ + (n₃ + n₄ - 2 * c) - 2 * b with hj
  set j' := n₃ + (n₂ + n₄ - 2 * e) - 2 * g with hj'
  have step : ∀ x₁, ∑ x₂ ∈ range (n₂ + 1), ∑ x₃ ∈ range (n₃ + 1), ∑ x₄ ∈ range (n₄ + 1),
      stE1 n₁ n₂ n₃ n₄ c b R K x₁ x₂ x₃ x₄ * stE2 n₁ n₂ n₃ n₄ e g R' K x₁ x₂ x₃ x₄ =
      ∑ u ∈ range (j + 1), ∑ u' ∈ range (j' + 1),
        cgCoeff n₁ j R K x₁ u * cgCoeff n₁ j' R' K x₁ u' *
          ((-1) ^ (c + g) * (if n₂ + (n₃ + n₄ - 2 * c) - 2 * b = n₂ + n₄ - 2 * e + n₃ - 2 * g ∧
            u = u' then recoup3 n₂ n₄ n₃ e c g b 0 else 0)) := by
    intro x₁
    simp only [stE1_eq, stE2_eq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun x₂ _ => Finset.sum_congr rfl fun x₃ _ => sum3_rotate _ _ _ _]
    rw [sum4_rotate, sum4_rotate]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
    rw [← overlap_inner hc he hb hg (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu))
      (by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu'); omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold sum4
  rw [Finset.sum_congr rfl fun x₁ _ => step x₁]
  split_ifs with hcond
  · have hjj : j = j' := by omega
    have hRe : R = R' := by omega
    rw [← hjj, ← hRe]
    rw [Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun u hu => (show
      ∑ u' ∈ range (j + 1), cgCoeff n₁ j R K x₁ u * cgCoeff n₁ j R K x₁ u' *
        ((-1) ^ (c + g) * (if n₂ + (n₃ + n₄ - 2 * c) - 2 * b = n₂ + n₄ - 2 * e + n₃ - 2 * g ∧
          u = u' then recoup3 n₂ n₄ n₃ e c g b 0 else 0)) =
      (-1) ^ (c + g) * recoup3 n₂ n₄ n₃ e c g b 0 * (cgCoeff n₁ j R K x₁ u * cgCoeff n₁ j R K x₁ u)
      by
        rw [Finset.sum_eq_single u]
        · rw [ite_eq_left ⟨hcond, rfl⟩]; ring
        · intro u' _ hne; simp [Ne.symm hne]
        · intro h; exact absurd hu h)]
    simp only [← Finset.mul_sum]
    rw [cg_orthogonal_left hR hK hR]
    simp
  · simp only [mul_ite, mul_zero]
    exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun u _ =>
      Finset.sum_eq_zero fun u' _ => ite_eq_right (fun h => hcond h.1)

lemma sum4_sum {ι : Type*} (n₁ n₂ n₃ n₄ : ℕ) (B : Finset ι) (f : ι → ℕ → ℕ → ℕ → ℕ → ℝ) :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ => ∑ b ∈ B, f b x₁ x₂ x₃ x₄) =
      ∑ b ∈ B, sum4 n₁ n₂ n₃ n₄ (f b) := by
  unfold sum4
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]

lemma sum4_mul_left (n₁ n₂ n₃ n₄ : ℕ) (c : ℝ) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ => c * f x₁ x₂ x₃ x₄) = c * sum4 n₁ n₂ n₃ n₄ f := by
  simp only [sum4, Finset.mul_sum]

/-- `|(j₁ j₂) j₁₂, (j₃ j₄) j₃₄; J M⟩` in the product basis. -/
noncomputable def st1234 (n₁ n₂ n₃ n₄ a c P K x₁ x₂ x₃ x₄ : ℕ) : ℝ :=
  ∑ v ∈ range (n₃ + n₄ - 2 * c + 1),
    cgCoeff n₃ n₄ c v x₃ x₄ * cU n₁ n₂ (n₃ + n₄ - 2 * c) a P K (x₁, x₂, v)

/-- `|(j₁ j₃) j₁₃, (j₂ j₄) j₂₄; J M⟩` in the product basis. -/
noncomputable def st1324 (n₁ n₂ n₃ n₄ d e Q K x₁ x₂ x₃ x₄ : ℕ) : ℝ :=
  ∑ v ∈ range (n₂ + n₄ - 2 * e + 1),
    cgCoeff n₂ n₄ e v x₂ x₄ * cU n₁ n₃ (n₂ + n₄ - 2 * e) d Q K (x₁, x₃, v)

/-- The recoupling coefficient `⟨(j₁ j₂) j₁₂, (j₃ j₄) j₃₄; J M | (j₁ j₃) j₁₃, (j₂ j₄) j₂₄; J M⟩`. -/
noncomputable def recoup4 (n₁ n₂ n₃ n₄ a c d e P Q K : ℕ) : ℝ :=
  sum4 n₁ n₂ n₃ n₄ fun x₁ x₂ x₃ x₄ =>
    st1234 n₁ n₂ n₃ n₄ a c P K x₁ x₂ x₃ x₄ * st1324 n₁ n₂ n₃ n₄ d e Q K x₁ x₂ x₃ x₄

lemma st1234_expand {n₁ n₂ n₃ n₄ a c P K x₁ x₂ x₃ x₄ : ℕ} (ha : a ≤ min n₁ n₂)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) (n₃ + n₄ - 2 * c))
    (hK : K ≤ n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) (hx₁ : x₁ ≤ n₁) (hx₂ : x₂ ≤ n₂) :
    st1234 n₁ n₂ n₃ n₄ a c P K x₁ x₂ x₃ x₄ =
      ∑ b ∈ range (min n₂ (n₃ + n₄ - 2 * c) + 1),
        (if Triad n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)
            (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) then
          recoup3 n₁ n₂ (n₃ + n₄ - 2 * c) a b P ((n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) -
            (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)) / 2) K else 0) *
        stE1 n₁ n₂ n₃ n₄ c b ((n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) -
          (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)) / 2) K x₁ x₂ x₃ x₄ := by
  unfold st1234 stE1
  rw [Finset.sum_congr rfl fun v hv => by
    rw [cU_expand ha hP hK (mem_idx3.mpr ⟨hx₁, hx₂, Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)⟩),
      Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

lemma st1324_expand {n₁ n₂ n₃ n₄ d e Q K x₁ x₂ x₃ x₄ : ℕ} (hd : d ≤ min n₁ n₃)
    (hQ : Q ≤ min (n₁ + n₃ - 2 * d) (n₂ + n₄ - 2 * e))
    (hK : K ≤ n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q) (hx₁ : x₁ ≤ n₁) (hx₃ : x₃ ≤ n₃) :
    st1324 n₁ n₂ n₃ n₄ d e Q K x₁ x₂ x₃ x₄ =
      ∑ g ∈ range (min n₃ (n₂ + n₄ - 2 * e) + 1),
        (if Triad n₁ (n₃ + (n₂ + n₄ - 2 * e) - 2 * g)
            (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q) then
          recoup3 n₁ n₃ (n₂ + n₄ - 2 * e) d g Q ((n₁ + (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) -
            (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)) / 2) K else 0) *
        stE2 n₁ n₂ n₃ n₄ e g ((n₁ + (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) -
          (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)) / 2) K x₁ x₂ x₃ x₄ := by
  unfold st1324 stE2
  rw [Finset.sum_congr rfl fun v hv => by
    rw [cU_expand hd hQ hK (mem_idx3.mpr ⟨hx₁, hx₃, Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)⟩),
      Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

lemma sum4_congr {n₁ n₂ n₃ n₄ : ℕ} {f g : ℕ → ℕ → ℕ → ℕ → ℝ}
    (h : ∀ x₁ ≤ n₁, ∀ x₂ ≤ n₂, ∀ x₃ ≤ n₃, ∀ x₄ ≤ n₄, f x₁ x₂ x₃ x₄ = g x₁ x₂ x₃ x₄) :
    sum4 n₁ n₂ n₃ n₄ f = sum4 n₁ n₂ n₃ n₄ g := by
  unfold sum4
  exact Finset.sum_congr rfl fun x₁ h₁ => Finset.sum_congr rfl fun x₂ h₂ =>
    Finset.sum_congr rfl fun x₃ h₃ => Finset.sum_congr rfl fun x₄ h₄ =>
      h x₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp h₁)) x₂
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp h₂)) x₃
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp h₃)) x₄
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp h₄))

/-- The coefficient of `|j₁, (j₂ (j₃ j₄)) x⟩` in the expansion of `|(j₁ j₂), (j₃ j₄)⟩`. -/
noncomputable def coefA (n₁ n₂ n₃ n₄ a c P K b : ℕ) : ℝ :=
  if Triad n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) then
    recoup3 n₁ n₂ (n₃ + n₄ - 2 * c) a b P ((n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) -
      (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)) / 2) K else 0

/-- The coefficient of `|j₁, ((j₂ j₄) j₃) x⟩` in the expansion of `|(j₁ j₃), (j₂ j₄)⟩`. -/
noncomputable def coefB (n₁ n₂ n₃ n₄ d e Q K g : ℕ) : ℝ :=
  if Triad n₁ (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q) then
    recoup3 n₁ n₃ (n₂ + n₄ - 2 * e) d g Q ((n₁ + (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) -
      (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)) / 2) K else 0

lemma recoup4_expand {n₁ n₂ n₃ n₄ a c d e P Q K : ℕ} (ha : a ≤ min n₁ n₂)
    (hd : d ≤ min n₁ n₃) (hP : P ≤ min (n₁ + n₂ - 2 * a) (n₃ + n₄ - 2 * c))
    (hQ : Q ≤ min (n₁ + n₃ - 2 * d) (n₂ + n₄ - 2 * e))
    (hN : n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P = n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)
    (hK : K ≤ n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) :
    recoup4 n₁ n₂ n₃ n₄ a c d e P Q K =
      ∑ b ∈ range (min n₂ (n₃ + n₄ - 2 * c) + 1), ∑ g ∈ range (min n₃ (n₂ + n₄ - 2 * e) + 1),
        coefA n₁ n₂ n₃ n₄ a c P K b * coefB n₁ n₂ n₃ n₄ d e Q K g *
          sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
            stE1 n₁ n₂ n₃ n₄ c b ((n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) -
              (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)) / 2) K x₁ x₂ x₃ x₄ *
            stE2 n₁ n₂ n₃ n₄ e g ((n₁ + (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) -
              (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)) / 2) K x₁ x₂ x₃ x₄) := by
  unfold recoup4
  rw [sum4_congr fun x₁ h₁ x₂ h₂ x₃ h₃ x₄ _ => by
    rw [st1234_expand ha hP hK h₁ h₂, st1324_expand hd hQ (hN ▸ hK) h₁ h₃,
      Finset.sum_mul_sum]]
  rw [sum4_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum4_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← sum4_mul_left]
  congr 1
  funext x₁ x₂ x₃ x₄
  simp only [coefA, coefB]
  ring

lemma coef_overlap {n₁ n₂ n₃ n₄ a c d e P Q K b g : ℕ} (hc : c ≤ min n₃ n₄)
    (he : e ≤ min n₂ n₄)
    (hN : n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P = n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)
    (hK : K ≤ n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)
    (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c)) (hg : g ≤ min n₃ (n₂ + n₄ - 2 * e)) :
    coefA n₁ n₂ n₃ n₄ a c P K b * coefB n₁ n₂ n₃ n₄ d e Q K g *
      sum4 n₁ n₂ n₃ n₄ (fun x₁ x₂ x₃ x₄ =>
        stE1 n₁ n₂ n₃ n₄ c b ((n₁ + (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) -
          (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)) / 2) K x₁ x₂ x₃ x₄ *
        stE2 n₁ n₂ n₃ n₄ e g ((n₁ + (n₃ + (n₂ + n₄ - 2 * e) - 2 * g) -
          (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)) / 2) K x₁ x₂ x₃ x₄) =
      coefA n₁ n₂ n₃ n₄ a c P K b * coefB n₁ n₂ n₃ n₄ d e Q K g *
        ((-1) ^ (c + g) * (if n₂ + (n₃ + n₄ - 2 * c) - 2 * b = n₂ + n₄ - 2 * e + n₃ - 2 * g then
          recoup3 n₂ n₄ n₃ e c g b 0 else 0)) := by
  by_cases hA : Triad n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)
      (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)
  swap
  · simp [coefA, hA]
  by_cases hB : Triad n₁ (n₃ + (n₂ + n₄ - 2 * e) - 2 * g)
      (n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)
  swap
  · simp [coefB, hB]
  congr 1
  obtain ⟨a1, a2, a3, ra, hra⟩ := hA
  obtain ⟨b1, b2, b3, rb, hrb⟩ := hB
  have hg' : g ≤ min (n₂ + n₄ - 2 * e) n₃ := by rwa [min_comm]
  exact overlap_E hc he hb hg' (le_min (by omega) (by omega)) (by omega)
    (le_min (by omega) (by omega)) (by omega)

/-- **The chain** `(12)(34) → 1(2(34)) → 1((24)3) → (13)(24)`. -/
theorem recoup4_chain {n₁ n₂ n₃ n₄ a c d e P Q K : ℕ} (ha : a ≤ min n₁ n₂) (hc : c ≤ min n₃ n₄)
    (hd : d ≤ min n₁ n₃) (he : e ≤ min n₂ n₄)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) (n₃ + n₄ - 2 * c))
    (hQ : Q ≤ min (n₁ + n₃ - 2 * d) (n₂ + n₄ - 2 * e))
    (hN : n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P = n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)
    (hK : K ≤ n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) :
    recoup4 n₁ n₂ n₃ n₄ a c d e P Q K =
      ∑ b ∈ range (min n₂ (n₃ + n₄ - 2 * c) + 1),
        if Triad (n₂ + n₄ - 2 * e) n₃ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) then
          coefA n₁ n₂ n₃ n₄ a c P K b *
            coefB n₁ n₂ n₃ n₄ d e Q K
              ((n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) *
            ((-1) ^ (c + (n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) *
              recoup3 n₂ n₄ n₃ e c ((n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2)
                b 0)
        else 0 := by
  rw [recoup4_expand ha hd hP hQ hN hK]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  rw [Finset.sum_congr rfl fun g hg => coef_overlap hc he hN hK hb'
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hg))]
  simp only [mul_ite, mul_zero]
  rw [show min n₃ (n₂ + n₄ - 2 * e) = min (n₂ + n₄ - 2 * e) n₃ from min_comm _ _]
  simp_rw [eq_comm (a := n₂ + (n₃ + n₄ - 2 * c) - 2 * b)]
  exact sum_P_single (n₂ + n₄ - 2 * e) n₃ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) _

/-! ### The 9j symbol -/

/-- The summand of the 9j symbol. -/
noncomputable def nineJTerm (n₁ n₂ n₁₂ n₃ n₄ n₃₄ n₁₃ n₂₄ N x : ℕ) : ℝ :=
  (-1) ^ x * ((x : ℝ) + 1) * sixJ n₁ n₃ n₁₃ n₂₄ N x * sixJ n₂ n₄ n₂₄ n₃ x n₃₄ *
    sixJ n₁₂ n₃₄ N x n₁ n₂

/-- **Wigner 9j symbol** `{j₁ j₂ j₁₂; j₃ j₄ j₃₄; j₁₃ j₂₄ J}` with `nᵢ = 2jᵢ`:
`Σ_x (-1)^(2x) (2x + 1) {j₁ j₃ j₁₃; j₂₄ J x} {j₂ j₄ j₂₄; j₃ x j₃₄} {j₁₂ j₃₄ J; x j₁ j₂}`,
summed over all `x` (the terms vanish beyond the bound). -/
noncomputable def nineJ (n₁ n₂ n₁₂ n₃ n₄ n₃₄ n₁₃ n₂₄ N : ℕ) : ℝ :=
  ∑ x ∈ range (n₁ + n₂ + n₁₂ + n₃ + n₄ + n₃₄ + n₁₃ + n₂₄ + N + 1),
    nineJTerm n₁ n₂ n₁₂ n₃ n₄ n₃₄ n₁₃ n₂₄ N x

lemma sixJ_eq_zero_of_not_triad₂ {n₁ n₂ n₃ n₄ n₅ n₆ : ℕ} (h : ¬Triad n₁ n₅ n₆) :
    sixJ n₁ n₂ n₃ n₄ n₅ n₆ = 0 := by
  unfold sixJ sixJTerm
  simp [threeJ_of_not (show ¬(Triad n₁ n₅ n₆ ∧ _) from fun h' => h h'.1)]

lemma sixJ_nine_sym (n₁ n₂ n₁₂ n₃₄ N x : ℕ) :
    sixJ n₁₂ n₃₄ N x n₁ n₂ = sixJ n₁ n₂ n₁₂ n₃₄ N x := by
  rw [sixJ_swap12 n₃₄ n₁₂ N n₁ x n₂, sixJ_swap23 n₃₄ N n₁₂ n₁ n₂ x, sixJ_flip]

lemma triad_swap23 {n₁ n₂ n₃ : ℕ} : Triad n₁ n₃ n₂ ↔ Triad n₁ n₂ n₃ := by
  simp only [Triad, show n₁ + n₃ + n₂ = n₁ + n₂ + n₃ by ring]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by omega, by omega, by omega, h4⟩

/-- The sign and normalization algebra of the 9j term. -/
lemma nine_alg (A B C s₁ s₂ s₃ σ x y₁₂ y₃₄ y₁₃ y₂₄ : ℝ) (hx : 0 ≤ x) (h₁₂ : 0 ≤ y₁₂)
    (h₃₄ : 0 ≤ y₃₄) (h₁₃ : 0 ≤ y₁₃) (h₂₄ : 0 ≤ y₂₄) (hσ : s₁ * s₃ * s₂ = σ) :
    s₁ * √(y₁₂ * x) * A * (s₃ * √(y₁₃ * x) * C) * (s₂ * √(y₂₄ * y₃₄) * B) =
      √(y₁₂ * y₃₄ * y₁₃ * y₂₄) * (σ * x * C * B * A) := by
  rw [Real.sqrt_mul h₁₂, Real.sqrt_mul h₁₃, Real.sqrt_mul h₂₄,
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul h₁₂, ← hσ]
  have := Real.mul_self_sqrt hx
  linear_combination (s₁ * s₃ * s₂ * A * B * C * √y₁₂ * √y₁₃ * √y₂₄ * √y₃₄) * this

lemma nine_parity {n₁ n₂ n₃ n₄ n₁₂ n₃₄ n₁₃ n₂₄ N j a c d e P Q b g : ℕ}
    (hA : n₁₂ + 2 * a = n₁ + n₂) (hC : n₃₄ + 2 * c = n₃ + n₄) (hD : n₁₃ + 2 * d = n₁ + n₃)
    (hE : n₂₄ + 2 * e = n₂ + n₄) (hP : N + 2 * P = n₁₂ + n₃₄) (hQ : N + 2 * Q = n₁₃ + n₂₄)
    (hj : j + 2 * b = n₂ + n₃₄) (hg : j + 2 * g = n₂₄ + n₃) :
    Even ((n₁ + n₂ + n₃₄ + N) / 2 + (n₁ + n₃ + n₂₄ + N) / 2 + (c + g + (n₂ + n₄ + n₃ + j) / 2) +
      j) :=
  Nat.even_iff.mpr (by omega)

lemma nine_term {n₁ n₂ n₃ n₄ a c d e P Q K b : ℕ} (ha : a ≤ min n₁ n₂) (hc : c ≤ min n₃ n₄)
    (hd : d ≤ min n₁ n₃) (he : e ≤ min n₂ n₄)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) (n₃ + n₄ - 2 * c))
    (hQ : Q ≤ min (n₁ + n₃ - 2 * d) (n₂ + n₄ - 2 * e))
    (hN : n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P = n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)
    (hK : K ≤ n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) (hb : b ≤ min n₂ (n₃ + n₄ - 2 * c)) :
    (if Triad (n₂ + n₄ - 2 * e) n₃ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) then
      coefA n₁ n₂ n₃ n₄ a c P K b *
        coefB n₁ n₂ n₃ n₄ d e Q K ((n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) *
        ((-1) ^ (c + (n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) *
          recoup3 n₂ n₄ n₃ e c ((n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2)
            b 0)
      else 0) =
    √((((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * (((n₃ + n₄ - 2 * c : ℕ) : ℝ) + 1) *
        (((n₁ + n₃ - 2 * d : ℕ) : ℝ) + 1) * (((n₂ + n₄ - 2 * e : ℕ) : ℝ) + 1)) *
      nineJTerm n₁ n₂ (n₁ + n₂ - 2 * a) n₃ n₄ (n₃ + n₄ - 2 * c) (n₁ + n₃ - 2 * d)
        (n₂ + n₄ - 2 * e) (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)
        (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) := by
  have a1 := le_trans ha (min_le_left _ _)
  have a2 := le_trans ha (min_le_right _ _)
  have c1 := le_trans hc (min_le_left _ _)
  have c2 := le_trans hc (min_le_right _ _)
  have d1 := le_trans hd (min_le_left _ _)
  have d2 := le_trans hd (min_le_right _ _)
  have e1 := le_trans he (min_le_left _ _)
  have e2 := le_trans he (min_le_right _ _)
  have p1 := le_trans hP (min_le_left _ _)
  have p2 := le_trans hP (min_le_right _ _)
  have q1 := le_trans hQ (min_le_left _ _)
  have q2 := le_trans hQ (min_le_right _ _)
  have b1 := le_trans hb (min_le_left _ _)
  have b2 := le_trans hb (min_le_right _ _)
  clear ha hc hd he hP hQ hb
  unfold nineJTerm
  rw [sixJ_nine_sym n₁ n₂ (n₁ + n₂ - 2 * a) (n₃ + n₄ - 2 * c)
    (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)]
  by_cases h2 : Triad (n₂ + n₄ - 2 * e) n₃ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)
  swap
  · rw [ite_eq_right h2, sixJ_eq_zero_of_not_triad₄ (n₁ := n₂) (n₂ := n₄) (n₆ := n₃ + n₄ - 2 * c)
      (fun h => h2 (triad_cyclic.mp h))]
    ring
  rw [ite_eq_left h2]
  by_cases h1 : Triad n₁ (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)
      (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)
  swap
  · rw [show coefA n₁ n₂ n₃ n₄ a c P K b = 0 by rw [coefA, ite_eq_right h1],
      sixJ_eq_zero_of_not_triad₂ (n₁ := n₁) (n₂ := n₃) (n₃ := n₁ + n₃ - 2 * d)
        (n₄ := n₂ + n₄ - 2 * e) (fun h => h1 (triad_swap23.mp h))]
    ring
  obtain ⟨t1, t2, t3, rg, hrg⟩ := h2
  obtain ⟨s1, s2, s3, rn, hrn⟩ := h1
  have g1 : (n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2 ≤ n₃ := by omega
  have g2 : (n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2 ≤ n₂ + n₄ - 2 * e := by
    omega
  have b3 : b ≤ n₄ + n₃ - 2 * c := by omega
  have hgj : n₃ + (n₂ + n₄ - 2 * e) -
      2 * ((n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) =
      n₂ + (n₃ + n₄ - 2 * c) - 2 * b := by omega
  have hgj2 : n₂ + n₄ - 2 * e + n₃ -
      2 * ((n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2) =
      n₂ + (n₃ + n₄ - 2 * c) - 2 * b := by omega
  have h43 : n₄ + n₃ - 2 * c = n₃ + n₄ - 2 * c := by omega
  rw [coefA, ite_eq_left ⟨s1, s2, s3, rn, hrn⟩, coefB, hgj, ← hN, ite_eq_left ⟨s1, s2, s3, rn, hrn⟩]
  rw [recoup3_eq_sixJ (le_min a1 a2) (le_min b1 b2) (le_min p1 p2)
      (le_min (by omega) (by omega)) (by omega) hK,
    recoup3_eq_sixJ (le_min d1 d2) (le_min g1 g2) (le_min q1 q2)
      (le_min (by omega) (by omega)) (by omega) (by omega),
    recoup3_eq_sixJ (le_min e1 e2) (le_min c2 c1) (le_min g2 g1) (le_min b1 b3) (by omega)
      (Nat.zero_le _)]
  rw [hgj, hgj2, ← hN, h43]
  rw [← mul_assoc ((-1 : ℝ) ^ (c + (n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2)),
    ← mul_assoc ((-1 : ℝ) ^ (c + (n₂ + n₄ - 2 * e + n₃ - (n₂ + (n₃ + n₄ - 2 * c) - 2 * b)) / 2))]
  refine nine_alg _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) ?_
  rw [← pow_add, ← pow_add, ← pow_add]
  exact neg_one_pow_eq_of_even (nine_parity (n₁₂ := n₁ + n₂ - 2 * a) (n₃₄ := n₃ + n₄ - 2 * c)
    (n₁₃ := n₁ + n₃ - 2 * d) (n₂₄ := n₂ + n₄ - 2 * e) (a := a) (c := c) (d := d) (e := e)
    (P := P) (Q := Q) (b := b) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega))

/-- **Recoupling of four angular momenta**:
`⟨(j₁ j₂) j₁₂, (j₃ j₄) j₃₄; J M | (j₁ j₃) j₁₃, (j₂ j₄) j₂₄; J M⟩ =
  √((2j₁₂ + 1)(2j₃₄ + 1)(2j₁₃ + 1)(2j₂₄ + 1)) {j₁ j₂ j₁₂; j₃ j₄ j₃₄; j₁₃ j₂₄ J}`. -/
theorem recoup4_eq_nineJ {n₁ n₂ n₃ n₄ a c d e P Q K : ℕ} (ha : a ≤ min n₁ n₂)
    (hc : c ≤ min n₃ n₄) (hd : d ≤ min n₁ n₃) (he : e ≤ min n₂ n₄)
    (hP : P ≤ min (n₁ + n₂ - 2 * a) (n₃ + n₄ - 2 * c))
    (hQ : Q ≤ min (n₁ + n₃ - 2 * d) (n₂ + n₄ - 2 * e))
    (hN : n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P = n₁ + n₃ - 2 * d + (n₂ + n₄ - 2 * e) - 2 * Q)
    (hK : K ≤ n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) :
    recoup4 n₁ n₂ n₃ n₄ a c d e P Q K =
      √((((n₁ + n₂ - 2 * a : ℕ) : ℝ) + 1) * (((n₃ + n₄ - 2 * c : ℕ) : ℝ) + 1) *
          (((n₁ + n₃ - 2 * d : ℕ) : ℝ) + 1) * (((n₂ + n₄ - 2 * e : ℕ) : ℝ) + 1)) *
        nineJ n₁ n₂ (n₁ + n₂ - 2 * a) n₃ n₄ (n₃ + n₄ - 2 * c) (n₁ + n₃ - 2 * d)
          (n₂ + n₄ - 2 * e) (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) := by
  have hf : ∀ x, ¬Triad n₂ (n₃ + n₄ - 2 * c) x →
      nineJTerm n₁ n₂ (n₁ + n₂ - 2 * a) n₃ n₄ (n₃ + n₄ - 2 * c) (n₁ + n₃ - 2 * d)
        (n₂ + n₄ - 2 * e) (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) x = 0 := by
    intro x hx
    rw [nineJTerm, sixJ_eq_zero_of_not_triad₂ (n₂ := n₄) (n₃ := n₂ + n₄ - 2 * e) (n₄ := n₃)
      (fun h => hx (triad_swap23.mp h))]
    ring
  have hsum : ∑ b ∈ range (min n₂ (n₃ + n₄ - 2 * c) + 1),
      nineJTerm n₁ n₂ (n₁ + n₂ - 2 * a) n₃ n₄ (n₃ + n₄ - 2 * c) (n₁ + n₃ - 2 * d)
        (n₂ + n₄ - 2 * e) (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P)
        (n₂ + (n₃ + n₄ - 2 * c) - 2 * b) =
      nineJ n₁ n₂ (n₁ + n₂ - 2 * a) n₃ n₄ (n₃ + n₄ - 2 * c) (n₁ + n₃ - 2 * d)
        (n₂ + n₄ - 2 * e) (n₁ + n₂ - 2 * a + (n₃ + n₄ - 2 * c) - 2 * P) := by
    rw [← sum_triad_reindex n₂ (n₃ + n₄ - 2 * c) _ hf, nineJ]
    refine Finset.sum_subset (fun x hx => ?_) (fun x _ hx => hf x ?_)
    · simp only [Finset.mem_range] at hx ⊢; omega
    · rintro ⟨h1, -, -, -⟩
      simp only [Finset.mem_range] at hx
      omega
  rw [recoup4_chain ha hc hd he hP hQ hN hK, Finset.sum_congr rfl fun b hb =>
    nine_term ha hc hd he hP hQ hN hK (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)),
    ← Finset.mul_sum, hsum]

end QM
