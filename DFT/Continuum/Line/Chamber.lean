/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Strong
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Orderings and collisions

* `Far η x`: all pairs of particles are more than `η` apart; `Far.injective`, `Far.pm`.
* `perm_eq_of_strictMono`, `exists_strictMono`: a configuration without collisions has a unique
  sorting relabelling.
* `eq_zero_of_collision`: an antisymmetric state vanishes where two particles meet.
* `mu_strip_le`, `NearS`: the strip `|xᵢ - xⱼ| ≤ η` has measure at most `2η` in the cube, and the
  near-collision set `NearS η` is measurable.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ}

/-! ### The smooth transition -/

/-! ### The smooth indicator of the ordered chamber -/

lemma abs_sgn (σ : Equiv.Perm (Fin (n + 1))) : |sgn σ| = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sgn, h]

/-- Points without near-collisions. -/
def Far (η : ℝ) (x : Cfg n) : Prop := ∀ i j, i ≠ j → η < |x i - x j|

lemma Far.injective {η : ℝ} (hη : 0 ≤ η) {x : Cfg n} (h : Far η x) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have := h i j hne
  rw [hij, sub_self, abs_zero] at this
  linarith

lemma Far.pm {η : ℝ} {x : Cfg n} (h : Far η x) (σ : Equiv.Perm (Fin (n + 1))) : Far η (pm σ x) :=
  fun i j hij => h (σ i) (σ j) (σ.injective.ne hij)

/-- Two strictly monotone rearrangements of an injective configuration coincide. -/
lemma perm_eq_of_strictMono {x : Cfg n} (hx : Function.Injective x)
    {σ ρ : Equiv.Perm (Fin (n + 1))} (hσ : StrictMono (pm σ x)) (hρ : StrictMono (pm ρ x)) :
    σ = ρ := by
  have hr : Set.range (pm σ x) = Set.range (pm ρ x) := by
    have e : ∀ τ : Equiv.Perm (Fin (n + 1)), Set.range (pm τ x) = Set.range x := fun τ =>
      (τ.surjective.range_comp x)
    rw [e, e]
  have hf := (StrictMono.range_inj_of_wellFoundedLT hσ hρ).1 hr
  ext i
  exact congrArg Fin.val (hx (congrFun hf i))

/-- A configuration without collisions has a sorting permutation. -/
lemma exists_strictMono {x : Cfg n} (hx : Function.Injective x) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), StrictMono (pm σ x) :=
  ⟨Tuple.sort x, (Tuple.monotone_sort x).strictMono_of_injective
    (hx.comp (Tuple.sort x).injective)⟩

/-! ### The derivative bound -/

/-! ### Antisymmetric functions near collisions -/

/-- An antisymmetric function vanishes at a collision. -/
lemma eq_zero_of_collision {Φ : Cfg n → ℝ} (hD : Φ ∈ DomF n) {x : Cfg n} {i j : Fin (n + 1)}
    (hij : i ≠ j) (h : x i = x j) : Φ x = 0 := by
  have hpm : pm (Equiv.swap i j) x = x := by
    funext l
    simp only [pm_apply]
    by_cases hl : l = i
    · subst hl; simp [h]
    by_cases hl' : l = j
    · subst hl'; simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hl']
  have := anti hD (Equiv.swap i j) x
  rw [hpm, sgn_swap hij] at this
  linarith

/-! ### The measure of the near-collision set -/

lemma volume_cube' : volume (Cube' n) = 1 := by
  rw [Real.volume_pi_Ioo]; simp

/-- A single collision strip has measure at most `2η` in the cube. -/
lemma mu_strip_le {η : ℝ} (_hη : 0 ≤ η) {i j : Fin (n + 1)} (hij : i ≠ j) :
    μN n {x | |x i - x j| ≤ η} ≤ ENNReal.ofReal (2 * η) := by
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Cfg n)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hm : MeasurableSet {x : Cfg n | |x i - x (i.succAbove j')| ≤ η} :=
    measurableSet_le (show Continuous fun x : Cfg n => |x i - x (i.succAbove j')| by
      fun_prop).measurable measurable_const
  rw [Measure.restrict_apply hm,
    ← he.measure_preimage (hm.inter measurableSet_cube).nullMeasurableSet]
  set T : Set (ℝ × (Fin n → ℝ)) := {p | |p.1 - p.2 j'| ≤ η ∧ p.2 ∈ Cube' n}
  have hsub : e.symm ⁻¹' ({x : Cfg n | |x i - x (i.succAbove j')| ≤ η} ∩ Cube n) ⊆ T := by
    rintro ⟨t, y⟩ ⟨h1, h2⟩
    have hc : e.symm (t, y) = Fin.insertNth i t y := rfl
    simp only [mem_ofPred_eq, hc, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove] at h1 h2
    refine ⟨h1, fun l _ => ?_⟩
    have := h2 (i.succAbove l) (mem_univ _)
    simpa [hc, Fin.insertNth_apply_succAbove] using this
  have hTm : MeasurableSet T :=
    (measurableSet_le (show Continuous fun p : ℝ × (Fin n → ℝ) => |p.1 - p.2 j'| by
      fun_prop).measurable measurable_const).inter
      (measurable_snd (MeasurableSet.univ_pi fun _ => measurableSet_Ioo))
  refine (measure_mono hsub).trans ?_
  rw [Measure.prod_apply_symm hTm]
  calc ∫⁻ y, volume ((fun t => (t, y)) ⁻¹' T)
      ≤ ∫⁻ y, (Cube' n).indicator (fun _ => ENNReal.ofReal (2 * η)) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ Cube' n
        · rw [indicator_of_mem hy]
          refine (measure_mono (t := Icc (y j' - η) (y j' + η)) fun t ht => ?_).trans ?_
          · have := (abs_le.mp ht.1); exact ⟨by linarith [this.1], by linarith [this.2]⟩
          · rw [Real.volume_Icc]; ring_nf; exact le_rfl
        · rw [indicator_of_notMem hy]
          have : (fun t => (t, y)) ⁻¹' T = ∅ := by
            ext t; simp only [mem_preimage, mem_empty_iff_false, iff_false]
            exact fun h => hy h.2
          rw [this, measure_empty]
    _ = ENNReal.ofReal (2 * η) := by
        rw [lintegral_indicator_const (MeasurableSet.univ_pi fun _ => measurableSet_Ioo),
          volume_cube', mul_one]

/-- The near-collision set. -/
def NearS (η : ℝ) : Set (Cfg n) := {x | ¬ Far η x}

lemma NearS_eq (η : ℝ) :
    NearS (n := n) η = ⋃ i, ⋃ j, {x : Cfg n | i ≠ j ∧ |x i - x j| ≤ η} := by
  ext x; simp [NearS, Far]

lemma measurableSet_pair (η : ℝ) (i j : Fin (n + 1)) :
    MeasurableSet {x : Cfg n | i ≠ j ∧ |x i - x j| ≤ η} := by
  by_cases h : i = j
  · simp [h]
  · simp only [ne_eq, h, not_false_eq_true, true_and]
    exact measurableSet_le (show Continuous fun x : Cfg n => |x i - x j| by fun_prop).measurable
      measurable_const

lemma measurableSet_NearS (η : ℝ) : MeasurableSet (NearS (n := n) η) := by
  rw [NearS_eq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => measurableSet_pair η i j

end DFT.Continuum.Line
