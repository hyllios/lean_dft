/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Pittalis
-/
import ForMathlib.Analysis.Sobolev.CubeTrace

/-!
# Coordinate sections of finite ordering chambers

Each section is an interval with endpoints at a wall or at one of the fixed coordinates.
-/

namespace MeasureTheory.UnitCube

open Set

variable {n : ℕ}

def Endpoint (y : Fin n → ℝ) (t : ℝ) : Prop := t = 0 ∨ t = 1 ∨ ∃ j, t = y j

private def Segment (y : Fin n → ℝ) (p : ℝ → Prop) : Prop :=
  ∃ a b, Endpoint y a ∧ Endpoint y b ∧ ∀ t ∈ Ioo (0 : ℝ) 1, p t ↔ t ∈ Ioo a b

private lemma segment_true (y : Fin n → ℝ) : Segment y (fun _ => True) :=
  ⟨0, 1, Or.inl rfl, Or.inr (Or.inl rfl), fun _ ht => iff_of_true trivial ht⟩

private lemma segment_false (y : Fin n → ℝ) : Segment y (fun _ => False) :=
  ⟨0, 0, Or.inl rfl, Or.inl rfl, fun _ _ => by simp⟩

private lemma segment_and {y : Fin n → ℝ} {p q : ℝ → Prop} (hp : Segment y p) (hq : Segment y q) :
    Segment y (fun t => p t ∧ q t) := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  obtain ⟨c, d, hc, hd, hq⟩ := hq
  refine ⟨max a c, min b d, ?_, ?_, fun t ht => ?_⟩
  · rcases max_choice a c with h|h <;> rwa [h]
  · rcases min_choice b d with h|h <;> rwa [h]
  · dsimp only
    rw [hp t ht, hq t ht]
    simp only [mem_Ioo, max_lt_iff, lt_min_iff]
    tauto

private lemma segment_pair (k i j : Fin (n + 1)) (y : Fin n → ℝ) :
    Segment y (fun t => line k y t i < line k y t j) := by
  have hj := Fin.eq_self_or_eq_succAbove k j
  rcases Fin.eq_self_or_eq_succAbove k i with hi | ⟨u, hi⟩ <;> rw [hi] <;>
    rcases hj with hj | ⟨v, hj⟩ <;> rw [hj]
  · simpa [line] using segment_false y
  · refine ⟨0, y v, Or.inl rfl, Or.inr (Or.inr ⟨v, rfl⟩), fun t ht => ?_⟩
    simp [line, ht.1]
  · refine ⟨y u, 1, Or.inr (Or.inr ⟨u, rfl⟩), Or.inr (Or.inl rfl), fun t ht => ?_⟩
    simp [line, ht.2]
  · by_cases h : y u < y v
    · simpa [line, h] using segment_true y
    · simpa [line, h] using segment_false y

theorem segment_pairs (k : Fin (n + 1)) (y : Fin n → ℝ)
    (s : Finset (Fin (n + 1) × Fin (n + 1))) :
    ∃ a b, Endpoint y a ∧ Endpoint y b ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
      (∀ p ∈ s, line k y t p.1 < line k y t p.2) ↔ t ∈ Ioo a b := by
  classical
  change Segment y (fun t => ∀ p ∈ s, line k y t p.1 < line k y t p.2)
  induction s using Finset.induction_on with
  | empty => simpa using segment_true y
  | insert p s _ ih =>
    simpa using segment_and (segment_pair k p.1 p.2 y) ih

end MeasureTheory.UnitCube
