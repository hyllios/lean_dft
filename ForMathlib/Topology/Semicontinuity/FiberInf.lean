/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Infima over the fibres of a continuous map on a compact set

For `K` compact, `f : X → Y` and `g : X → ℝ` continuous on `K`, consider the constrained infimum
`F y = ⨅ x ∈ K, f x = y, g x` in `EReal` (`⊤` off `f '' K`).

* `iInf_fiber_eq_top`: `F y = ⊤` off `f '' K`.
* `IsCompact.exists_eq_iInf_fiber`: on `f '' K` the infimum is attained.
* `IsCompact.lowerSemicontinuous_iInf_fiber`: `F` is lower semicontinuous.
-/

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {K : Set X} {f : X → Y}
  {g : X → ℝ}

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem iInf_fiber_eq_top {y : Y} (hy : y ∉ f '' K) :
    ⨅ x ∈ {x ∈ K | f x = y}, (g x : EReal) = ⊤ :=
  iInf₂_eq_top.2 fun x hx => (hy ⟨x, hx.1, hx.2⟩).elim

/-- The constrained infimum is attained on `f '' K`. -/
theorem IsCompact.exists_eq_iInf_fiber [T2Space X] [T1Space Y] (hK : IsCompact K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) {y : Y} (hy : y ∈ f '' K) :
    ∃ x ∈ K, f x = y ∧ ⨅ x' ∈ {x ∈ K | f x = y}, (g x' : EReal) = g x := by
  have hc : IsCompact {x ∈ K | f x = y} :=
    hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      fun x hx => hx.1
  obtain ⟨x0, hx0K, hx0⟩ := hy
  obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn ⟨x0, hx0K, hx0⟩ (hg.mono fun x hx => hx.1)
  refine ⟨x, hx.1, hx.2, le_antisymm (iInf₂_le x hx) (le_iInf₂ fun x' hx' => ?_)⟩
  exact EReal.coe_le_coe_iff.2 (hmin hx')

/-- The constrained infimum is lower semicontinuous. -/
theorem IsCompact.lowerSemicontinuous_iInf_fiber [T2Space X] [T2Space Y] (hK : IsCompact K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) :
    LowerSemicontinuous fun y => ⨅ x ∈ {x ∈ K | f x = y}, (g x : EReal) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c = ⊤
  · subst hc; simp
  have hset : (fun y => ⨅ x ∈ {x ∈ K | f x = y}, (g x : EReal)) ⁻¹' Iic c =
      f '' {x ∈ K | (g x : EReal) ≤ c} := by
    ext y
    constructor
    · intro hy
      simp only [mem_preimage, mem_Iic] at hy
      have hyK : y ∈ f '' K := by
        by_contra h
        rw [iInf_fiber_eq_top h, top_le_iff] at hy
        exact hc hy
      obtain ⟨x, hxK, rfl, heq⟩ := hK.exists_eq_iInf_fiber hf hg hyK
      exact ⟨x, ⟨hxK, by rw [← heq]; exact hy⟩, rfl⟩
    · rintro ⟨x, ⟨hxK, hxc⟩, rfl⟩
      simp only [mem_preimage, mem_Iic]
      exact (iInf₂_le x ⟨hxK, rfl⟩).trans hxc
  rw [hset]
  have hcK : IsCompact {x ∈ K | (g x : EReal) ≤ c} :=
    hK.of_isClosed_subset (hg.preimage_isClosed_of_isClosed hK.isClosed
      (isClosed_le continuous_coe_real_ereal continuous_const)) fun x hx => hx.1
  exact (hcK.image_of_continuousOn (hf.mono fun x hx => hx.1)).isClosed
