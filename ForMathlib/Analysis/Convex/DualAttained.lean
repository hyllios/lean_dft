/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.Compact

/-!
# Attainment of a dual problem at relative-interior points

* `exists_add_smul_sub_mem_of_mem_intrinsicInterior`: from a point `x` of the intrinsic (relative)
  interior of `s` one can step a little beyond `x` away from any `y ∈ s` and stay in `s`.
* `IsCompact.exists_isMaxOn_sInf_affine`: let `K` be compact and `a : X → ℝ^m`, `b : X → ℝ`
  continuous, with `0` in the relative algebraic interior of `a(K)` (every `a x` has a negative
  multiple `-ε a x` in `a(K)`). Then the concave function `v ↦ min_{x ∈ K} (b x + a x · v)` attains
  its supremum over `ℝ^m`.

The second statement is the attainment of the dual problem in Lieb's convex duality (a potential
exists for every density in the relative interior of the ensemble range). The proof: the function is
invariant along `W = {w | a x · w = 0 on K}`; on a complement `U` of `W` it is bounded by
`max b - δ ‖u‖` with `δ > 0` (compactness of the unit sphere of `U`), so its maximum over `U` is
attained in a ball.
-/

open Set Metric

/-- From a point of the intrinsic interior one can step slightly beyond it, away from any point
of the set, and stay in the set. -/
theorem exists_add_smul_sub_mem_of_mem_intrinsicInterior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {x y : E} (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s) :
    ∃ ε > (0 : ℝ), x + ε • (x - y) ∈ s := by
  obtain ⟨p, hp, rfl⟩ := mem_intrinsicInterior.1 hx
  have hyA : y ∈ affineSpan ℝ s := subset_affineSpan ℝ s hy
  have hmem : ∀ t : ℝ, (p : E) + t • ((p : E) - y) ∈ affineSpan ℝ s := fun t => by
    have := AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.smul_mem _ t (AffineSubspace.vsub_mem_direction p.2 hyA)) p.2
    simpa [vadd_eq_add, vsub_eq_sub, add_comm] using this
  set f : ℝ → affineSpan ℝ s := fun t => ⟨(p : E) + t • ((p : E) - y), hmem t⟩
  have hf : Continuous f := Continuous.subtype_mk (by fun_prop) _
  have hf0 : f 0 = p := Subtype.ext (by simp [f])
  have hnhds : f ⁻¹' ((↑) ⁻¹' s) ∈ nhds (0 : ℝ) :=
    hf.continuousAt.preimage_mem_nhds (by rw [hf0]; exact mem_interior_iff_mem_nhds.1 hp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨r / 2, half_pos hr, hball ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

variable {X : Type*} [TopologicalSpace X] {m : Type*} [Fintype m]

/-- **Attainment of the dual problem.** -/
theorem IsCompact.exists_isMaxOn_sInf_affine {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {a : X → m → ℝ} {b : X → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hsym : ∀ x ∈ K, ∃ ε > (0 : ℝ), ∃ x' ∈ K, a x' = -ε • a x) :
    ∃ v : m → ℝ, ∀ v', sInf ((fun x => b x + a x ⬝ᵥ v') '' K) ≤
      sInf ((fun x => b x + a x ⬝ᵥ v) '' K) := by
  set h : (m → ℝ) → ℝ := fun v => sInf ((fun x => b x + a x ⬝ᵥ v) '' K) with hh
  have hcont : Continuous h :=
    hK.continuous_sInf (f := fun v x => b x + a x ⬝ᵥ v) (by fun_prop)
  have hbdd : ∀ v, BddBelow ((fun x => b x + a x ⬝ᵥ v) '' K) := fun v =>
    (hK.image (by fun_prop)).bddBelow
  have hle : ∀ v, ∀ x ∈ K, h v ≤ b x + a x ⬝ᵥ v := fun v x hx =>
    csInf_le (hbdd v) ⟨x, hx, rfl⟩
  -- the directions along which `h` is constant
  let W : Submodule ℝ (m → ℝ) :=
    { carrier := {w | ∀ x ∈ K, a x ⬝ᵥ w = 0}
      add_mem' := fun hv hw x hx => by rw [dotProduct_add, hv x hx, hw x hx, add_zero]
      zero_mem' := fun x _ => dotProduct_zero _
      smul_mem' := fun c w hw x hx => by rw [dotProduct_smul, hw x hx, smul_zero] }
  have hW : ∀ v, ∀ w ∈ W, h (v + w) = h v := fun v w hw => by
    simp only [hh]
    congr 1
    refine image_congr fun x hx => ?_
    rw [dotProduct_add, (hw : ∀ x ∈ K, a x ⬝ᵥ w = 0) x hx, add_zero]
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl W
  -- `h` decreases linearly along every direction of `U`
  have hneg : ∀ u ∈ U, u ≠ 0 → ∃ x ∈ K, a x ⬝ᵥ u < 0 := fun u hu hu0 => by
    have hnW : u ∉ W := fun huW => hu0 (by
      have := hU.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨huW, hu⟩)
      simpa using this)
    have hnW' : ¬∀ x ∈ K, a x ⬝ᵥ u = 0 := hnW
    push Not at hnW'
    obtain ⟨x, hx, hne⟩ := hnW'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨x, hx, hlt⟩
    · obtain ⟨ε, hε, x', hx', hax'⟩ := hsym x hx
      refine ⟨x', hx', ?_⟩
      rw [hax', smul_dotProduct, smul_eq_mul]
      nlinarith
  set φ : (m → ℝ) → ℝ := fun u => sInf ((fun x => a x ⬝ᵥ u) '' K) with hφ
  have hφc : Continuous φ := hK.continuous_sInf (f := fun u x => a x ⬝ᵥ u) (by fun_prop)
  have hSU : IsCompact (sphere (0 : m → ℝ) 1 ∩ U) :=
    (isCompact_sphere _ _).inter_right (Submodule.isClosed_of_finiteDimensional U)
  have hφneg : ∀ u ∈ sphere (0 : m → ℝ) 1 ∩ U, φ u < 0 := fun u hu => by
    obtain ⟨hu1, huU⟩ := hu
    have hu0 : u ≠ 0 := by
      rintro rfl; simp at hu1
    obtain ⟨x, hx, hlt⟩ := hneg u huU hu0
    exact (csInf_le ((hK.image (f := fun x => a x ⬝ᵥ u) (by fun_prop)).bddBelow)
      ⟨x, hx, rfl⟩).trans_lt hlt
  obtain ⟨δ, hδ, hδφ⟩ : ∃ δ > (0 : ℝ), ∀ u ∈ sphere (0 : m → ℝ) 1 ∩ U, φ u ≤ -δ := by
    rcases (sphere (0 : m → ℝ) 1 ∩ U).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨u₀, hu₀, hmax⟩ := hSU.exists_isMaxOn hne hφc.continuousOn
      exact ⟨-φ u₀, neg_pos.2 (hφneg u₀ hu₀), fun u hu => by rw [neg_neg]; exact hmax hu⟩
  obtain ⟨B, hB⟩ := (hK.image hb).bddAbove
  have hbB : ∀ x ∈ K, b x ≤ B := fun x hx => hB ⟨x, hx, rfl⟩
  have hcoer : ∀ u ∈ U, h u ≤ B - δ * ‖u‖ := fun u hu => by
    rcases eq_or_ne u 0 with rfl | hu0
    · obtain ⟨x, hx⟩ := hKne
      simpa using (hle 0 x hx).trans (by simpa using hbB x hx)
    · set û := ‖u‖⁻¹ • u
      have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
      have hû : û ∈ sphere (0 : m → ℝ) 1 ∩ U :=
        ⟨by simp [û, norm_smul, hn.ne'], U.smul_mem _ hu⟩
      obtain ⟨x, hx, hxφ⟩ := (hK.image (f := fun x => a x ⬝ᵥ û) (by fun_prop)).sInf_mem
        (hKne.image _)
      have h1 : a x ⬝ᵥ û ≤ -δ := by
        have := hδφ û hû
        change sInf ((fun x => a x ⬝ᵥ û) '' K) ≤ -δ at this
        rwa [← hxφ] at this
      have h2 : a x ⬝ᵥ u = ‖u‖ * a x ⬝ᵥ û := by
        rw [dotProduct_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
      have := hle u x hx
      nlinarith [hbB x hx]
  -- the maximum over a ball of `U`
  set R := (B - h 0) / δ
  have hh0 : h 0 ≤ B := by simpa using hcoer 0 U.zero_mem
  have hR : 0 ≤ R := div_nonneg (by linarith) hδ.le
  have hC : IsCompact ((U : Set (m → ℝ)) ∩ closedBall 0 R) :=
    (isCompact_closedBall _ _).inter_left (Submodule.isClosed_of_finiteDimensional U)
  obtain ⟨u₀, hu₀, hmax⟩ := hC.exists_isMaxOn ⟨0, U.zero_mem, by simpa using hR⟩
    hcont.continuousOn
  refine ⟨u₀, fun v => ?_⟩
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 (hU.sup_eq_top ▸ Submodule.mem_top (x := v))
  change h (w + u) ≤ h u₀
  rw [add_comm, hW u w hw]
  by_cases huR : ‖u‖ ≤ R
  · exact hmax ⟨hu, by simpa using huR⟩
  · push Not at huR
    have h1 := hcoer u hu
    have h2 : h 0 ≤ h u₀ := hmax ⟨U.zero_mem, by simpa using hR⟩
    have h3 : δ * R = B - h 0 := by rw [mul_div_cancel₀ _ hδ.ne']
    nlinarith
