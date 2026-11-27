/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Set.Countable
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Cofinite

/-!
# Enumerating a function with finite sublevel sets

Let `f : ι → ℝ` on an infinite type have finite sublevel sets `{i | f i ≤ c}`. Then `ι` can be
enumerated by `ℕ` in nondecreasing order of `f`, and `f` tends to `+∞` along the enumeration.

Order `ι` by `(f i, c i)` lexicographically, for an injection `c : ι → ℕ` (`ι` is countable, a
union of finite sets). The rank `r i = #{j | (f j, c j) < (f i, c i)}` is strictly monotone, so it
identifies `ι` with an infinite subset of `ℕ`, which `Nat.Subtype.orderIsoOfNat` enumerates.

* **`exists_equiv_nat_monotone`**.
-/

open Filter Set

namespace FiniteSublevel

variable {ι : Type*} {f : ι → ℝ}

lemma countable_of_finite_sublevel (hf : ∀ c, {i | f i ≤ c}.Finite) : Countable ι := by
  have : (univ : Set ι) = ⋃ n : ℕ, {i | f i ≤ n} := by
    ext i; simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge (f i); exact ⟨n, hn⟩
  exact countable_univ_iff.1 (this ▸ countable_iUnion fun n => (hf n).countable)

end FiniteSublevel

open FiniteSublevel in
/-- **Enumeration in nondecreasing order.** A real function with finite sublevel sets on an
infinite type is nondecreasing along some enumeration `ℕ ≃ ι`, and tends to `+∞` along it. -/
theorem exists_equiv_nat_monotone {ι : Type*} [Infinite ι] (f : ι → ℝ)
    (hf : ∀ c, {i | f i ≤ c}.Finite) :
    ∃ e : ℕ ≃ ι, Monotone (f ∘ e) ∧ Tendsto (f ∘ e) atTop atTop := by
  classical
  have := countable_of_finite_sublevel hf
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat ι
  -- the strict total order: by `f`, ties broken by `c`
  set lt : ι → ι → Prop := fun j i => f j < f i ∨ (f j = f i ∧ c j < c i)
  have lt_trans : ∀ {a b d}, lt a b → lt b d → lt a d := fun {a b d} h1 h2 => by
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩
  have lt_irrefl : ∀ a, ¬ lt a a := fun a h => by
    rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
  have lt_tri : ∀ a b, lt a b ∨ a = b ∨ lt b a := fun a b => by
    rcases lt_trichotomy (f a) (f b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (c a) (c b) with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl (hc h'))
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
    · exact Or.inr (Or.inr (Or.inl h))
  have hfin : ∀ i, {j | lt j i}.Finite := fun i =>
    (hf (f i)).subset fun j hj => by
      rcases hj with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
  set r : ι → ℕ := fun i => (hfin i).toFinset.card
  have hr : ∀ {i j}, lt i j → r i < r j := fun {i j} hij => by
    refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
    · simp only [Finite.mem_toFinset] at hk ⊢; exact lt_trans hk hij
    · have : i ∈ (hfin i).toFinset := hsub (by simpa using hij)
      simp only [Finite.mem_toFinset] at this
      exact lt_irrefl i this
  have hrinj : Function.Injective r := fun i j h => by
    rcases lt_tri i j with hl | he | hg
    · exact absurd h (hr hl).ne
    · exact he
    · exact absurd h (hr hg).ne'
  have : Infinite (range r) := (infinite_range_of_injective hrinj).to_subtype
  set φ := Nat.Subtype.orderIsoOfNat (range r)
  set e : ℕ ≃ ι := φ.toEquiv.trans (Equiv.ofInjective r hrinj).symm
  have hre : ∀ k, r (e k) = φ k := fun k => by
    simp [e, Equiv.apply_ofInjective_symm]
  have hmono : Monotone (f ∘ e) := fun k l hkl => by
    have h1 : r (e k) ≤ r (e l) := by rw [hre, hre]; exact_mod_cast φ.monotone hkl
    rcases lt_tri (e k) (e l) with h | h | h
    · rcases h with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    · simp [h]
    · exact absurd h1 (not_le.2 (hr h))
  refine ⟨e, hmono, tendsto_atTop.2 fun b => ?_⟩
  have hfin' : {k : ℕ | f (e k) ≤ b}.Finite := (hf b).preimage e.injective.injOn
  filter_upwards [hfin'.eventually_cofinite_notMem.filter_mono Nat.cofinite_eq_atTop.ge]
    with k hk
  exact (not_le.1 hk).le
