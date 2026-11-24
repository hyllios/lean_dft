/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.YoungL2

/-!
# Lowering is injective

For `g` of mixed symmetry `(a + 1, b - 1)` (antisymmetric in particles `0, …, a` and in
`a + 1, …, N - 1`) with `b ≤ a`, the Young antisymmetrisation `altY a g` of type `(a, b)` (the
spin-lowering operator, up to a factor) is not zero: `⟨g, altY a g⟩ > 0`
(**`integral_mul_altY_lower_pos`**).

With `t σ = sgn σ ⟨g, g ∘ σ⟩`, invariant under the symmetry group of `g` on both sides
(`term_left`, `term_right`), the sum over `YG a` splits along the preimage of particle `a`
(`sum_YG_coset`): `⟨g, altY a g⟩ = m (‖g‖² + (b - 1) T)` with `T = t(swap a (a+1))`. The same
splitting of `YG (a + 2)` along particle `a + 1` gives `0 ≤ ⟨g, altY (a+2) g⟩ = m' (‖g‖² + (a + 1) T)`,
and `b - 1 < a + 1`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### Splitting a sum over the Young group -/

open Classical in
/-- A sum over `YG c` of a function that only sees whether `σ⁻¹ Q = Q`. -/
theorem sum_YG_coset (c : ℕ) (Q : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hQS : Q ∈ S)
    (hS : ∀ σ, YG c σ → σ⁻¹ Q ∈ S) (hsw : ∀ j ∈ S, YG c (Equiv.swap Q j))
    (t : Equiv.Perm (Fin (n + 1)) → ℝ) (t1 t2 : ℝ)
    (ht : ∀ σ, YG c σ → t σ = if σ⁻¹ Q = Q then t1 else t2) :
    ∑ σ, (if YG c σ then t σ else 0) =
      ((Finset.univ.filter fun σ => YG c σ ∧ σ⁻¹ Q = Q).card : ℝ) *
        (t1 + ((S.card : ℝ) - 1) * t2) := by
  set F := Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => YG c σ
  set m := (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => YG c σ ∧ σ⁻¹ Q = Q).card
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := S) (g := fun σ => σ⁻¹ Q)
    (fun σ hσ => hS σ (Finset.mem_filter.1 hσ).2)]
  have hfib : ∀ j ∈ S, (F.filter fun σ => σ⁻¹ Q = j).card = m := fun j hj => by
    refine Finset.card_nbij' (fun σ => σ * Equiv.swap Q j) (fun σ => σ * Equiv.swap Q j)
      (fun σ hσ => ?_) (fun σ hσ => ?_) (fun σ _ => ?_) (fun σ _ => ?_)
    · simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      refine ⟨YG_mul hσ.1 (hsw j hj), ?_⟩
      rw [mul_inv_rev, Equiv.Perm.mul_apply, hσ.2, Equiv.swap_inv, Equiv.swap_apply_right]
    · simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      refine ⟨YG_mul hσ.1 (hsw j hj), ?_⟩
      rw [mul_inv_rev, Equiv.Perm.mul_apply, hσ.2, Equiv.swap_inv, Equiv.swap_apply_left]
    · simp only [mul_assoc, Equiv.swap_mul_self, mul_one]
    · simp only [mul_assoc, Equiv.swap_mul_self, mul_one]
  have hval : ∀ j ∈ S, ∑ σ ∈ F.filter (fun σ => σ⁻¹ Q = j), t σ =
      (m : ℝ) * (if j = Q then t1 else t2) := fun j hj => by
    rw [Finset.sum_congr rfl fun σ hσ => by
      have h := Finset.mem_filter.1 hσ
      rw [ht σ (Finset.mem_filter.1 h.1).2, h.2], Finset.sum_const, nsmul_eq_mul, hfib j hj]
  rw [Finset.sum_congr rfl hval, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.filter_eq' S Q]
  simp only [hQS, ↓reduceIte]
  rw [Finset.card_singleton, Finset.filter_ne' S Q, Finset.card_erase_of_mem hQS]
  rw [Nat.cast_sub (Finset.card_pos.2 ⟨Q, hQS⟩)]
  push_cast; ring

/-! ### The terms `sgn σ ⟨g, g ∘ σ⟩` -/

/-- `sgn σ ⟨g, g ∘ σ⟩`. -/
noncomputable def tY (g : Cfg n → ℝ) (σ : Equiv.Perm (Fin (n + 1))) : ℝ :=
  sgn σ * ∫ x, g x * g (pm σ x) ∂μN n

section terms

variable {c : ℕ} {g : Cfg n → ℝ} (hanti : AntiY c g)
include hanti

lemma tY_left {h : Equiv.Perm (Fin (n + 1))} (hh : YG c h) (σ : Equiv.Perm (Fin (n + 1))) :
    tY g (h * σ) = tY g σ := by
  have hc := integral_pm h (fun y => g (pm h⁻¹ y) * g (pm σ y))
  simp only [pm_inv_pm] at hc
  simp only [tY, pm_mul, hc, sgn_mul]
  have e : ∫ x, g (pm h⁻¹ x) * g (pm σ x) ∂μN n = sgn h * ∫ x, g x * g (pm σ x) ∂μN n := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hanti h⁻¹ (YG_inv hh)] with x hx
    rw [hx, sgn_inv]; ring
  rw [e]
  linear_combination (sgn σ * ∫ x, g x * g (pm σ x) ∂μN n) * sgn_mul_self h

lemma tY_right {h : Equiv.Perm (Fin (n + 1))} (hh : YG c h) (σ : Equiv.Perm (Fin (n + 1))) :
    tY g (σ * h) = tY g σ := by
  simp only [tY, pm_mul, sgn_mul]
  have e : ∫ x, g x * g (pm h (pm σ x)) ∂μN n = sgn h * ∫ x, g x * g (pm σ x) ∂μN n := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_pm (hanti h hh) σ] with x hx
    rw [hx]; ring
  rw [e]
  linear_combination (sgn σ * ∫ x, g x * g (pm σ x) ∂μN n) * sgn_mul_self h

lemma tY_of_YG {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG c σ) : tY g σ = ∫ x, g x * g x ∂μN n := by
  have := tY_right hanti hσ 1
  rw [one_mul] at this
  rw [this, tY, sgn_one, one_mul]
  rfl

lemma tY_conj {ρ : Equiv.Perm (Fin (n + 1))} (hρ : YG c ρ) (s : Equiv.Perm (Fin (n + 1))) :
    tY g (ρ * s * ρ) = tY g s := by
  rw [mul_assoc, tY_left hanti hρ, tY_right hanti hρ]

end terms

open Classical in
lemma integral_mul_altY_eq (c : ℕ) {g : Cfg n → ℝ} (hg : MemLp g 2 (μN n)) :
    ∫ x, g x * altY c g x ∂μN n = ∑ σ, (if YG c σ then tY g σ else 0) := by
  have e : (fun x => g x * altY c g x) = fun x =>
      ∑ σ, (if YG c σ then sgn σ else 0) * (g x * g (pm σ x)) := by
    funext x; simp only [altY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by split_ifs <;> ring
  rw [e, integral_finsetSum _ fun σ _ => (int_mul_L2 hg (memLp_comp_pm hg σ)).const_mul _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul]
  split_ifs <;> simp [tY]

/-! ### Lowering is injective -/

/-- Membership in the symmetry group of `g` for relabellings fixing the moved particle. -/
lemma YG_succ_of_fix {c : ℕ} {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG c σ) {Q : Fin (n + 1)}
    (hQ : (Q : ℕ) = c) (hfix : σ⁻¹ Q = Q) : YG (c + 1) σ := by
  have hσQ : σ Q = Q := by
    have := congrArg σ hfix; simpa using this.symm
  intro i
  by_cases hi : i = Q
  · subst hi; rw [hσQ]
  · have hne : σ i ≠ Q := fun h => hi (σ.injective (h.trans hσQ.symm))
    have h1 : (σ i : ℕ) ≠ c := fun h => hne (Fin.ext (h.trans hQ.symm))
    have h2 : (i : ℕ) ≠ c := fun h => hi (Fin.ext (h.trans hQ.symm))
    have := hσ i
    constructor <;> intro h <;> omega

lemma YG_pred_of_fix {c : ℕ} {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG (c + 1) σ)
    {Q : Fin (n + 1)} (hQ : (Q : ℕ) = c) (hfix : σ⁻¹ Q = Q) : YG c σ := by
  have hσQ : σ Q = Q := by
    have := congrArg σ hfix; simpa using this.symm
  intro i
  by_cases hi : i = Q
  · subst hi; rw [hσQ]
  · have hne : σ i ≠ Q := fun h => hi (σ.injective (h.trans hσQ.symm))
    have h1 : (σ i : ℕ) ≠ c := fun h => hne (Fin.ext (h.trans hQ.symm))
    have h2 : (i : ℕ) ≠ c := fun h => hi (Fin.ext (h.trans hQ.symm))
    have := hσ i
    constructor <;> intro h <;> omega

/-- **Lowering is injective.** For `g ≠ 0` of mixed symmetry `(a + 1, b - 1)` with `b ≤ a`,
`⟨g, altY a g⟩ > 0`. -/
theorem integral_mul_altY_lower_pos {a b : ℕ} (hab : a + b = n + 1) (hb : 1 ≤ b) (hba : b ≤ a)
    {g : Cfg n → ℝ} (hg : MemLp g 2 (μN n)) (hanti : AntiY (a + 1) g)
    (hpos : 0 < ∫ x, g x * g x ∂μN n) : 0 < ∫ x, g x * altY a g x ∂μN n := by
  classical
  set G := ∫ x, g x * g x ∂μN n
  set Q : Fin (n + 1) := ⟨a, by omega⟩
  set SA := Finset.univ.filter fun i : Fin (n + 1) => a ≤ (i : ℕ)
  have hcardA : (SA.card : ℝ) = b := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (n + 1)))) (fun i : Fin (n + 1) => (i : ℕ) < a)
    have h2 : (Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) < a).card = a := by
      rw [Fin.card_filter_val_lt]; omega
    have h3 : (Finset.univ.filter fun i : Fin (n + 1) => ¬ (i : ℕ) < a) = SA := by
      ext i; simp [SA]
    rw [h2, h3, Finset.card_univ, Fintype.card_fin] at h1
    have : SA.card = b := by omega
    exact_mod_cast this
  have hQS : Q ∈ SA := by simp [SA, Q]
  have hSA : ∀ σ, YG a σ → σ⁻¹ Q ∈ SA := fun σ hσ => by
    have := YG_inv hσ Q
    simp only [SA, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h; push Not at h
    exact absurd (this.1 h) (by simp [Q])
  have hswA : ∀ j ∈ SA, YG a (Equiv.swap Q j) := fun j hj => YG_swap (by
    simp only [SA, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [SameB, Q]; omega)
  have hA := integral_mul_altY_eq a hg
  rcases Nat.eq_or_lt_of_le hb with hb1 | hb2
  · -- `b = 1`: only the trivial coset
    subst hb1
    have hSA1 : SA.card = 1 := by exact_mod_cast hcardA
    rw [hA, sum_YG_coset a Q SA hQS hSA hswA (tY g) G 0 (fun σ hσ => by
      split_ifs with hfix
      · exact tY_of_YG hanti (YG_succ_of_fix hσ rfl hfix)
      · exfalso
        have h1 := hSA σ hσ
        have : SA = {Q} := Finset.eq_singleton_iff_unique_mem.2 ⟨hQS, fun j hj => by
          have := Finset.card_le_one.1 hSA1.le j hj Q hQS; exact this⟩
        rw [this, Finset.mem_singleton] at h1
        exact hfix h1)]
    have hm : (0 : ℝ) < ((Finset.univ.filter fun σ => YG a σ ∧ σ⁻¹ Q = Q).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨1, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨YG_one _, rfl⟩⟩
    rw [hcardA]; push_cast
    nlinarith
  · -- `b ≥ 2`
    set P1 : Fin (n + 1) := ⟨a + 1, by omega⟩
    have hQP1 : Q ≠ P1 := by simp [Q, P1, Fin.ext_iff]
    set T := tY g (Equiv.swap Q P1)
    -- the coset values for `YG a`
    have htA : ∀ σ, YG a σ → tY g σ = if σ⁻¹ Q = Q then G else T := fun σ hσ => by
      split_ifs with hfix
      · exact tY_of_YG hanti (YG_succ_of_fix hσ rfl hfix)
      · set j := σ⁻¹ Q
        have hj := hSA σ hσ
        simp only [SA, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hja : a + 1 ≤ (j : ℕ) := by
          have : (j : ℕ) ≠ a := fun h => hfix (Fin.ext h)
          omega
        set h := σ * Equiv.swap Q j
        have hh : YG (a + 1) h := YG_succ_of_fix (YG_mul hσ (hswA j (by simp [SA]; omega))) rfl
          (by rw [mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_right])
        have hσh : σ = h * Equiv.swap Q j := by
          simp only [h, mul_assoc, Equiv.swap_mul_self, mul_one]
        rw [hσh, tY_left hanti hh]
        by_cases hjP : j = P1
        · rw [hjP]
        · have hQj : Q ≠ j := fun h => hfix h.symm
          have hconj := Equiv.swap_mul_swap_mul_swap hQP1 hQj
          rw [Equiv.swap_comm j Q] at hconj
          rw [← hconj, tY_conj hanti (YG_swap (by simp only [SameB, P1]; omega))]
    rw [hA, sum_YG_coset a Q SA hQS hSA hswA (tY g) G T htA]
    -- the raising inequality from `YG (a + 2)`
    set SB := Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) < a + 2
    have hcardB : (SB.card : ℝ) = a + 2 := by
      have : SB.card = a + 2 := by rw [Fin.card_filter_val_lt]; omega
      exact_mod_cast this
    have hP1S : P1 ∈ SB := by simp [SB, P1]
    have hSB : ∀ σ, YG (a + 2) σ → σ⁻¹ P1 ∈ SB := fun σ hσ => by
      have := YG_inv hσ P1
      simp only [SB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact this.2 (by simp [P1])
    have hswB : ∀ j ∈ SB, YG (a + 2) (Equiv.swap P1 j) := fun j hj => YG_swap (by
      simp only [SB, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [SameB, P1]; omega)
    have htB : ∀ σ, YG (a + 2) σ → tY g σ = if σ⁻¹ P1 = P1 then G else T := fun σ hσ => by
      split_ifs with hfix
      · exact tY_of_YG hanti (YG_pred_of_fix hσ rfl hfix)
      · set i := σ⁻¹ P1
        have hi := hSB σ hσ
        simp only [SB, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have hia : (i : ℕ) ≤ a := by
          have : (i : ℕ) ≠ a + 1 := fun h => hfix (Fin.ext h)
          omega
        set h := σ * Equiv.swap P1 i
        have hh : YG (a + 1) h := YG_pred_of_fix (YG_mul hσ (hswB i (by simp [SB]; omega))) rfl
          (by rw [mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_right])
        have hσh : σ = h * Equiv.swap P1 i := by
          simp only [h, mul_assoc, Equiv.swap_mul_self, mul_one]
        rw [hσh, tY_left hanti hh]
        by_cases hiQ : i = Q
        · rw [hiQ, Equiv.swap_comm]
        · have hP1Q : P1 ≠ Q := hQP1.symm
          have hP1i : P1 ≠ i := fun h => hfix h.symm
          have hconj := Equiv.swap_mul_swap_mul_swap hP1Q hP1i
          rw [Equiv.swap_comm i P1] at hconj
          rw [← hconj, tY_conj hanti (YG_swap (by simp only [SameB, Q]; omega)),
            Equiv.swap_comm]
    have hB := integral_mul_altY_eq (a + 2) hg
    rw [sum_YG_coset (a + 2) P1 SB hP1S hSB hswB (tY g) G T htB] at hB
    have hBnn := integral_mul_altY_self_nonneg (a := a + 2) hg
    rw [hB, hcardB] at hBnn
    have hmB : (0 : ℝ) < ((Finset.univ.filter fun σ => YG (a + 2) σ ∧ σ⁻¹ P1 = P1).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨1, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨YG_one _, rfl⟩⟩
    have hmA : (0 : ℝ) < ((Finset.univ.filter fun σ => YG a σ ∧ σ⁻¹ Q = Q).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨1, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨YG_one _, rfl⟩⟩
    have hB' : 0 ≤ G + ((a : ℝ) + 2 - 1) * T := by
      by_contra h; push Not at h; nlinarith
    rw [hcardA]
    have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
    have hb2' : (2 : ℝ) ≤ b := by exact_mod_cast hb2
    rcases le_or_gt 0 T with hT | hT
    · have : 0 < G + ((b : ℝ) - 1) * T := by nlinarith
      positivity
    · have : 0 < G + ((b : ℝ) - 1) * T := by nlinarith
      positivity

end DFT.Continuum.Line
