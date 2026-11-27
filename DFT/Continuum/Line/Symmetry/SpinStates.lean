/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.Spin.SpinAlg
import DFT.Continuum.Line.Symmetry.Young

/-!
# Spin sectors of `N` spin-½ particles

* `sc c`: the configuration with spins `0, …, c-1` up; `nup_sc`: it has `c` spins up;
  `rel_sc_iff`: the relabellings fixing it are the Young subgroup `YG c`.
* `exists_rel_sc`: every configuration with `c` spins up is a relabelling of `sc c`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology Sine Function

variable {n : ℕ}

/-! ### Spin-orbital states -/

lemma rel_rel (σ ρ : Equiv.Perm (Fin (n + 1))) (s : SpinC n) :
    rel σ (rel ρ s) = rel (ρ * σ) s := rfl

/-- The configuration with spins `0, …, c-1` up. -/
def sc (n c : ℕ) : SpinC n := fun i => decide ((i : ℕ) < c)

lemma rel_sc_iff {c : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : rel σ (sc n c) = sc n c ↔ YG c σ := by
  constructor
  · intro h i
    have := congrFun h i
    simp only [rel, sc, decide_eq_decide] at this
    exact this
  · intro h; funext i; simp only [rel, sc, decide_eq_decide]; exact h i

lemma nup_sc {c : ℕ} (hc : c ≤ n + 1) : nup (sc n c) = c := by
  rw [nup_eq_sum]
  simp only [sc, decide_eq_true_eq]
  rw [Finset.sum_boole, Nat.cast_id]
  rw [Fin.card_filter_val_lt]; omega

lemma subtypeCongr_apply' {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) (a : α) :
    Equiv.subtypeCongr e f a = if h : p a then (e ⟨a, h⟩ : α) else (f ⟨a, h⟩ : α) := by
  by_cases h : p a <;> simp [Equiv.subtypeCongr, h]

/-- **Every configuration with `c` spins up is a relabelling of `sc c`.** -/
lemma exists_rel_sc {s : SpinC n} {c : ℕ} (h : nup s = c) :
    ∃ τ : Equiv.Perm (Fin (n + 1)), rel τ (sc n c) = s := by
  classical
  have hc : c ≤ n + 1 := h ▸ nup_le s
  have h1 : Fintype.card {i // s i = true} = Fintype.card {j : Fin (n + 1) // (j : ℕ) < c} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hc]
    exact h
  have h2 : Fintype.card {i // ¬ s i = true} =
      Fintype.card {j : Fin (n + 1) // ¬ (j : ℕ) < c} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  set e1 := Fintype.equivOfCardEq h1
  set e2 := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e1 e2, ?_⟩
  funext i
  simp only [rel, sc, subtypeCongr_apply']
  by_cases hi : s i = true
  · rw [dite_eq_left hi]; simp [hi, (e1 ⟨i, hi⟩).2]
  · rw [dite_eq_right hi]
    have := (e2 ⟨i, hi⟩).2
    simp only [Bool.not_eq_true] at hi
    simp [hi, this]

end DFT.Continuum.Line
