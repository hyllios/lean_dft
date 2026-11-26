/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Linear ODEs in a Banach algebra have global solutions

Mathlib's Picard–Lindelöf theorem gives local solutions. For a linear equation `U' = A(t) U` with
continuous `A` in a complete normed algebra the local solutions exist on intervals of a uniform
length, and gluing finitely many of them gives a solution on any interval `[0, T]`. Solutions are
unique by Grönwall.

## Main results

* `hasDerivWithinAt_glue`: gluing two solutions on adjacent closed intervals.
* `exists_linear_ode`: a solution of `U' = A(t) U`, `U(0) = 1` on `[0, T]`.
* `linear_ode_unique`: two solutions of `U' = A(t) U` with the same value at `0` agree on `[0, T]`.
-/

namespace ForMathlib

open Set Filter Topology NNReal

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- Gluing two functions with derivatives within adjacent closed intervals. -/
lemma hasDerivWithinAt_glue {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g f' g' : ℝ → F} {a b c : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hg : ∀ t ∈ Icc b c, HasDerivWithinAt g (g' t) (Icc b c) t) (hfg : f b = g b)
    (hd : f' b = g' b) (hab : a ≤ b) (hbc : b ≤ c) :
    ∀ t ∈ Icc a c, HasDerivWithinAt (fun t => if t ≤ b then f t else g t)
      (if t ≤ b then f' t else g' t) (Icc a c) t := by
  intro t ht
  have hF : ∀ x ∈ Icc a b, (fun t => if t ≤ b then f t else g t) x = f x := fun x hx => by
    simp [hx.2]
  have hG : ∀ x ∈ Icc b c, (fun t => if t ≤ b then f t else g t) x = g x := fun x hx => by
    by_cases h : x ≤ b
    · have : x = b := le_antisymm h hx.1
      simp [this, hfg]
    · simp [h]
  rcases lt_trichotomy t b with htb | rfl | htb
  · have h1 := (hf t ⟨ht.1, htb.le⟩).congr_of_mem hF ⟨ht.1, htb.le⟩
    rw [ite_eq_left htb.le]
    refine h1.mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr ⟨Iio b, isOpen_Iio, htb, ?_⟩)
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2.1, le_of_lt hx1⟩
  · have h1 := (hf t ⟨ht.1, le_rfl⟩).congr_of_mem hF ⟨ht.1, le_rfl⟩
    have h2 := (hg t ⟨le_rfl, ht.2⟩).congr_of_mem hG ⟨le_rfl, ht.2⟩
    rw [ite_eq_left le_rfl, ← Icc_union_Icc_eq_Icc hab hbc]
    exact h1.union (hd ▸ h2)
  · have h2 := (hg t ⟨htb.le, ht.2⟩).congr_of_mem hG ⟨htb.le, ht.2⟩
    rw [ite_eq_right (not_le.mpr htb)]
    refine h2.mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr ⟨Ioi b, isOpen_Ioi, htb, ?_⟩)
    rintro x ⟨hx1, hx2⟩
    exact ⟨le_of_lt hx1, hx2.2⟩

/-- A local solution of `U' = A(t) U`, `U(t₀) = 1` on `[t₀, t₀ + δ]`, for `δ` controlled by a bound
`M` on `‖A‖`. -/
lemma exists_local_linear_ode {A : ℝ → B} (hA : Continuous A) {M : ℝ} (hM0 : 0 ≤ M) {t₀ δ : ℝ}
    (hδ : 0 ≤ δ) (hM : ∀ t ∈ Icc t₀ (t₀ + δ), ‖A t‖ ≤ M) (hδM : M * (‖(1 : B)‖ + 1) * δ ≤ 1) :
    ∃ V : ℝ → B, V t₀ = 1 ∧
      ∀ t ∈ Icc t₀ (t₀ + δ), HasDerivWithinAt V (A t * V t) (Icc t₀ (t₀ + δ)) t := by
  have ht₀ : t₀ ∈ Icc t₀ (t₀ + δ) := ⟨le_rfl, by linarith⟩
  have hPL : IsPicardLindelof (fun t x => A t * x) (⟨t₀, ht₀⟩ : Icc t₀ (t₀ + δ)) (1 : B) 1 0
      ⟨M * (‖(1 : B)‖ + 1), by positivity⟩ ⟨M, hM0⟩ := by
    refine ⟨fun t ht => ?_, fun x _ => ?_, fun t ht x hx => ?_, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))
    · exact (hA.mul continuous_const).continuousOn
    · have hx' : ‖x‖ ≤ ‖(1 : B)‖ + 1 := by
        have := norm_le_of_mem_closedBall hx
        simpa using this
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (hM t ht) hx' (norm_nonneg _) hM0
    · change M * (‖(1 : B)‖ + 1) * max (t₀ + δ - t₀) (t₀ - t₀) ≤ ((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
      rw [add_sub_cancel_left, sub_self, max_eq_left hδ, NNReal.coe_one, NNReal.coe_zero, sub_zero]
      exact hδM
  obtain ⟨V, hV0, hV⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨V, hV0, hV⟩

/-- **Global existence for linear ODEs**: for continuous `A` and `T ≥ 0` there is `U` with
`U(0) = 1` and `U' = A(t) U` on `[0, T]`. -/
theorem exists_linear_ode {A : ℝ → B} (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T) :
    ∃ U : ℝ → B, U 0 = 1 ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt U (A t * U t) (Icc 0 T) t := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T + 1)).exists_bound_of_continuousOn
    hA.continuousOn
  set M := max M₀ 1
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_right _ _)
  have hMb : ∀ t ∈ Icc 0 (T + 1), ‖A t‖ ≤ M := fun t ht => (hM₀ t ht).trans (le_max_left _ _)
  set c := M * (‖(1 : B)‖ + 1)
  have hc : 0 < c := by positivity
  set δ := min 1 (1 / c)
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδc : c * δ ≤ 1 := by
    calc c * δ ≤ c * (1 / c) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
      _ = 1 := by field_simp
  have hloc : ∀ t₀, 0 ≤ t₀ → t₀ + δ ≤ T + 1 → ∃ V : ℝ → B, V t₀ = 1 ∧
      ∀ t ∈ Icc t₀ (t₀ + δ), HasDerivWithinAt V (A t * V t) (Icc t₀ (t₀ + δ)) t :=
    fun t₀ ht₀ ht₁ => exists_local_linear_ode hA hM0 hδ0.le
      (fun t ht => hMb t ⟨ht₀.trans ht.1, ht.2.trans ht₁⟩) hδc
  -- induction on the number of steps
  have key : ∀ n : ℕ, ((n : ℝ) + 1) * δ ≤ T + δ → ∃ U : ℝ → B, U 0 = 1 ∧
      ∀ t ∈ Icc 0 (((n : ℝ) + 1) * δ),
        HasDerivWithinAt U (A t * U t) (Icc 0 (((n : ℝ) + 1) * δ)) t := by
    intro n
    induction n with
    | zero =>
      intro h
      obtain ⟨V, hV0, hV⟩ := hloc 0 le_rfl (by simp at h; linarith)
      refine ⟨V, hV0, ?_⟩
      simpa using hV
    | succ n ih =>
      intro h
      push_cast at h
      obtain ⟨U, hU0, hU⟩ := ih (by nlinarith)
      set t₀ := ((n : ℝ) + 1) * δ
      have ht₀ : 0 ≤ t₀ := by positivity
      obtain ⟨V, hV0, hV⟩ := hloc t₀ ht₀ (by
        have : t₀ + δ = ((n : ℝ) + 1 + 1) * δ := by ring
        linarith)
      have hW : ∀ t ∈ Icc t₀ (t₀ + δ),
          HasDerivWithinAt (fun t => V t * U t₀) (A t * (V t * U t₀)) (Icc t₀ (t₀ + δ)) t :=
        fun t ht => by simpa [mul_assoc] using (hV t ht).mul_const (U t₀)
      have hglue := hasDerivWithinAt_glue hU hW (by simp [hV0]) (by simp [hV0]) ht₀
        (by linarith)
      refine ⟨fun t => if t ≤ t₀ then U t else V t * U t₀, by simp [ht₀, hU0], fun t ht => ?_⟩
      have ht' : t ∈ Icc 0 (t₀ + δ) := by
        refine ⟨ht.1, ?_⟩
        have := ht.2
        push_cast at this
        have e : t₀ + δ = ((n : ℝ) + 1 + 1) * δ := by ring
        linarith
      have := hglue t ht'
      rw [show (((n + 1 : ℕ) : ℝ) + 1) * δ = t₀ + δ by push_cast; ring]
      convert this using 1
      split_ifs with h <;> simp [h]
  set m := Nat.ceil (T / δ)
  have hm : T ≤ ((m - 1 : ℕ) + 1 : ℝ) * δ := by
    have h1 : T / δ ≤ m := Nat.le_ceil _
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0] at h1 ⊢
      simp only [Nat.zero_sub, Nat.cast_zero, zero_add, one_mul]
      have : T ≤ 0 := by
        have := (div_le_iff₀ hδ0).mp h1
        simpa using this
      linarith
    · have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub hm0]; push_cast; ring
      rw [this]
      exact (div_le_iff₀ hδ0).mp h1
  have hm' : ((m - 1 : ℕ) + 1 : ℝ) * δ ≤ T + δ := by
    have h1 : (m : ℝ) < T / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0]; simp; linarith
    · have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub hm0]; push_cast; ring
      rw [this]
      have := mul_lt_mul_of_pos_right h1 hδ0
      rw [add_mul, div_mul_cancel₀ _ hδ0.ne', one_mul] at this
      linarith
  obtain ⟨U, hU0, hU⟩ := key (m - 1) hm'
  refine ⟨U, hU0, fun t ht => ?_⟩
  exact (hU t ⟨ht.1, ht.2.trans hm⟩).mono (Icc_subset_Icc le_rfl hm)

omit [CompleteSpace B] in
/-- **Uniqueness for linear ODEs**: two solutions of `U' = A(t) U` on `[0, T]` with the same
value at `0` agree on `[0, T]`. -/
theorem linear_ode_unique {A : ℝ → B} (hA : Continuous A) {T : ℝ} {U V : ℝ → B}
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (A t * U t) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V (A t * V t) (Icc 0 T) t) (h0 : U 0 = V 0) :
    EqOn U V (Icc 0 T) := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  set M := max M₀ 0
  have hM : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M := fun t ht => (hM₀ t ht).trans (le_max_left _ _)
  have hnh : ∀ t ∈ Ico 0 T, Icc 0 T ∈ 𝓝[Ici t] t := fun t ht =>
    mem_nhdsWithin.mpr ⟨Iio T, isOpen_Iio, ht.2, fun x hx => ⟨ht.1.trans hx.2, le_of_lt hx.1⟩⟩
  refine ODE_solution_unique_of_mem_Icc_right (v := fun t x => A t * x) (s := fun _ => univ)
    (K := ⟨M, le_max_right _ _⟩) (fun t ht => ?_)
    (fun t ht => (hU t ht).continuousWithinAt)
    (fun t ht => (hU t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hnh t ht))
    (fun _ _ => mem_univ _)
    (fun t ht => (hV t ht).continuousWithinAt)
    (fun t ht => (hV t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hnh t ht))
    (fun _ _ => mem_univ _) h0
  refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM t (Ico_subset_Icc_self ht))
    (norm_nonneg _))

end ForMathlib
