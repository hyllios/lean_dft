/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Ekeland's variational principle and the Brøndsted–Rockafellar theorem

Abstract convex analysis needed for the density of v-representable densities.

* `ekeland`: **Ekeland's variational principle** (weak form). A lower semicontinuous function
  bounded below on a complete metric space has, for every `δ > 0`, a point `x` with
  `g x ≤ g y + δ · d(y, x)` for all `y`.
* `exists_minorant_of_ge_neg_norm`: a convex `f` with `f 0 = 0` and `f ≥ -η‖·‖` has a continuous
  linear minorant of norm at most `η` (Hahn–Banach).
* `exists_supergrad_near`: **Brøndsted–Rockafellar** (concave form). Let `E` be concave and upper
  semicontinuous on a Banach space, and `ρ` a continuous linear functional with
  `sup_v (E v - ρ v) < ∞`. Then for every `η > 0` there is a potential `v` and a supergradient
  `ρ'` of `E` at `v` with `‖ρ' - ρ‖ ≤ η`.

In DFT language: `E` is the ground-state energy, `sup_v (E v - ρ v)` is the Lieb functional, and
the theorem says every density of finite `F` is a norm-limit of supergradient densities.
-/

namespace DFT

namespace Continuum

open Set Filter Topology

section Ekeland

variable {M : Type*} [MetricSpace M] [CompleteSpace M]

/-- **Ekeland's variational principle** (weak form). -/
theorem ekeland [Nonempty M] {g : M → ℝ} (hg : LowerSemicontinuous g) (hb : BddBelow (range g))
    {δ : ℝ} (hδ : 0 < δ) : ∃ x, ∀ y, g x ≤ g y + δ * dist y x := by
  classical
  -- `S x`: the points that improve on `x` by at least `δ` times the distance.
  set S : M → Set M := fun x => {y | g y + δ * dist y x ≤ g x} with hS
  have hSx : ∀ x, x ∈ S x := fun x => by simp [hS]
  have hSc : ∀ x, IsClosed (S x) := fun x => by
    have hl : LowerSemicontinuous fun y => g y + δ * dist y x - g x :=
      (hg.add (continuous_const.mul (continuous_id.dist continuous_const)).lowerSemicontinuous).add
        continuous_const.lowerSemicontinuous
    have := hl.isClosed_preimage 0
    convert this using 1
    ext y; simp [hS]
  have htrans : ∀ x y z, y ∈ S x → z ∈ S y → z ∈ S x := by
    intro x y z hy hz
    simp only [hS, mem_ofPred_eq] at hy hz ⊢
    have := dist_triangle z y x
    nlinarith
  have hbdd : ∀ x, BddBelow (g '' S x) := fun x => hb.mono (image_subset_range _ _)
  have hstep : ∀ (n : ℕ) (x : M), ∃ y ∈ S x, g y < sInf (g '' S x) + (1 / 2) ^ n := by
    intro n x
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_lt_of_csInf_lt (Set.Nonempty.image g ⟨x, hSx x⟩)
      (lt_add_of_pos_right _ (by positivity : (0 : ℝ) < (1 / 2) ^ n))
    exact ⟨y, hy, h⟩
  choose nx hnxS hnxg using hstep
  obtain ⟨x₀⟩ := ‹Nonempty M›
  let u : ℕ → M := fun n => Nat.rec x₀ (fun k x => nx k x) n
  have hu : ∀ n, u (n + 1) = nx n (u n) := fun n => rfl
  have hmono : ∀ n, u (n + 1) ∈ S (u n) := fun n => hu n ▸ hnxS n (u n)
  have hkey : ∀ n, ∀ z ∈ S (u (n + 1)), δ * dist z (u (n + 1)) ≤ (1 / 2) ^ n := by
    intro n z hz
    have hzn : z ∈ S (u n) := htrans _ _ _ (hmono n) hz
    have hinf : sInf (g '' S (u n)) ≤ g z := csInf_le (hbdd _) ⟨z, hzn, rfl⟩
    have h1 := hnxg n (u n)
    rw [← hu] at h1
    simp only [hS, mem_ofPred_eq] at hz
    linarith
  have hnest : ∀ n m, n ≤ m → u m ∈ S (u n) := by
    intro n m hnm
    induction hnm with
    | refl => exact hSx _
    | step _ ih => exact htrans _ _ _ ih (hmono _)
  have hdist : ∀ n, dist (u (n + 1)) (u (n + 1 + 1)) ≤ 2 / δ / 2 / 2 ^ n := by
    intro n
    have h := hkey n (u (n + 1 + 1)) (hmono (n + 1))
    rw [dist_comm]
    have : 2 / δ / 2 / 2 ^ n = (1 / 2) ^ n / δ := by
      rw [one_div_pow]; field_simp
    rw [this, le_div_iff₀ hδ]
    linarith
  obtain ⟨xb, hxb⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hdist)
  have hxbS : ∀ n, xb ∈ S (u n) := fun n =>
    (hSc _).mem_of_tendsto hxb (eventually_atTop.2 ⟨n, fun m hm => hnest n (m + 1) (by omega)⟩)
  refine ⟨xb, fun y => ?_⟩
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hy : y ∈ S xb := le_of_lt hlt
  have hyn : ∀ n, y ∈ S (u (n + 1)) := fun n => htrans _ _ _ (hxbS (n + 1)) hy
  have hlim : Tendsto (fun n => u (n + 1)) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (g := fun n => (1 / 2) ^ n / δ) ?_
    · rw [dist_comm, le_div_iff₀ hδ, mul_comm]; exact hkey n y (hyn n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).div_const δ
  have := tendsto_nhds_unique hxb hlim
  subst this
  simp at hlt

end Ekeland

section BR

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Hahn–Banach minorant.** A convex `f` with `f 0 = 0` and `f ≥ -η‖·‖` has a continuous linear
minorant of norm at most `η`. -/
theorem exists_minorant_of_ge_neg_norm {f : P → ℝ} (hf : ConvexOn ℝ univ f) (hf0 : f 0 = 0)
    {η : ℝ} (hη : 0 ≤ η) (h : ∀ y, -(η * ‖y‖) ≤ f y) :
    ∃ ℓ : StrongDual ℝ P, ‖ℓ‖ ≤ η ∧ ∀ y, ℓ y ≤ f y := by
  set A : Set (P × ℝ) := {p | p.2 + η * ‖p.1‖ < 0} with hA
  set B : Set (P × ℝ) := {p | p.1 ∈ univ ∧ f p.1 ≤ p.2} with hB
  have hAc : Convex ℝ A := by
    have hc : ConvexOn ℝ univ fun p : P × ℝ => p.2 + η * ‖p.1‖ := by
      refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 : ‖a • x.1 + b • y.1‖ ≤ a * ‖x.1‖ + b * ‖y.1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      nlinarith
    simpa using hc.convex_lt 0
  have hAo : IsOpen A :=
    isOpen_lt (continuous_snd.add (continuous_const.mul continuous_fst.norm)) continuous_const
  have hBc : Convex ℝ B := hf.convex_epigraph
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ⟨y, t⟩ ha ⟨_, hb⟩
    simp only [hA, mem_ofPred_eq] at ha
    have := h y
    simp only at hb
    linarith
  obtain ⟨φ, u, hφA, hφB⟩ := geometric_hahn_banach_open hAc hAo hBc hdisj
  set ℓ₀ : StrongDual ℝ P := φ.comp (ContinuousLinearMap.inl ℝ P ℝ) with hℓ₀
  set c : ℝ := φ (0, 1) with hc
  have hφ : ∀ y t, φ (y, t) = ℓ₀ y + t * c := by
    intro y t
    have : ((y, t) : P × ℝ) = (y, 0) + t • ((0 : P), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul, hℓ₀]
    rfl
  have hu0 : u ≤ 0 := by
    have := hφB (0, 0) ⟨mem_univ _, by simp [hf0]⟩
    rwa [hφ, map_zero, zero_mul, add_zero] at this
  have hAt : ∀ y : P, ∀ t, t + η * ‖y‖ < 0 → ℓ₀ y + t * c < u := fun y t ht => by
    rw [← hφ]; exact hφA (y, t) ht
  have hcpos : 0 < c := by
    have := hAt 0 (-1) (by simp)
    simp at this
    linarith
  have hu_nonneg : 0 ≤ u := by
    by_contra hneg
    replace hneg := not_le.mp hneg
    have := hAt 0 (u / c) (by
      rw [norm_zero, mul_zero, add_zero]; exact div_neg_of_neg_of_pos hneg hcpos)
    rw [map_zero, zero_add, div_mul_cancel₀ _ hcpos.ne'] at this
    exact lt_irrefl _ this
  have hbound : ∀ y, ℓ₀ y ≤ c * (η * ‖y‖) := by
    intro y
    refine le_of_forall_pos_lt_add fun s hs => ?_
    have := hAt y (-(η * ‖y‖) - s / c) (by
      have : 0 < s / c := div_pos hs hcpos
      linarith)
    have hsc : (-(η * ‖y‖) - s / c) * c = -(c * (η * ‖y‖)) - s := by
      field_simp
    rw [hsc] at this
    linarith
  refine ⟨(-(1 / c)) • ℓ₀, ?_, fun y => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ hη fun y => ?_
    rw [smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_pos (one_div_pos.mpr hcpos), one_div_mul_eq_div, div_le_iff₀ hcpos, abs_le]
    have h1 := hbound y
    have h2 := hbound (-y)
    rw [map_neg, norm_neg] at h2
    constructor <;> linarith
  · have := hφB (y, f y) ⟨mem_univ _, le_rfl⟩
    rw [hφ] at this
    have hq : ((-(1 / c)) • ℓ₀) y = -(ℓ₀ y / c) := by
      rw [smul_apply, smul_eq_mul]; ring
    rw [hq, neg_le, le_div_iff₀ hcpos]
    linarith

omit [NormedSpace ℝ P] in
lemma lowerSemicontinuous_neg_of_upper {E : P → ℝ} (hE : UpperSemicontinuous E) :
    LowerSemicontinuous fun v => -E v := by
  intro x y hy
  filter_upwards [hE x (-y) (by linarith)] with x' hx'
  linarith

variable [CompleteSpace P]

/-- **Brøndsted–Rockafellar** (concave form). Densities of finite Lieb functional are norm-limits
of supergradients: for every `η > 0` there is `v` and a supergradient `ρ'` of `E` at `v` within
`η` of `ρ`. -/
theorem exists_supergrad_near {E : P → ℝ} (hE : ConcaveOn ℝ univ E) (hus : UpperSemicontinuous E)
    (ρ : StrongDual ℝ P) (hρ : BddAbove (range fun v => E v - ρ v)) {η : ℝ} (hη : 0 < η) :
    ∃ (v : P) (ρ' : StrongDual ℝ P), ‖ρ' - ρ‖ ≤ η ∧ ∀ w, E w ≤ E v + ρ' (w - v) := by
  set g : P → ℝ := fun v => ρ v - E v with hg
  have hgl : LowerSemicontinuous g := by
    have : g = fun v => ρ v + -E v := by funext v; simp [hg, sub_eq_add_neg]
    rw [this]
    exact ρ.continuous.lowerSemicontinuous.add (lowerSemicontinuous_neg_of_upper hus)
  have hgb : BddBelow (range g) := by
    obtain ⟨C, hC⟩ := hρ
    refine ⟨-C, ?_⟩
    rintro _ ⟨v, rfl⟩
    have := hC ⟨v, rfl⟩
    simp only [hg]
    linarith
  obtain ⟨vb, hvb⟩ := ekeland hgl hgb hη
  set f : P → ℝ := fun y => g (vb + y) - g vb with hfdef
  have hfc : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hE' := hE.2 (mem_univ (vb + x)) (mem_univ (vb + y)) ha hb hab
    have hpt : a • (vb + x) + b • (vb + y) = vb + (a • x + b • y) := by
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
    rw [hpt] at hE'
    simp only [smul_eq_mul] at hE' ⊢
    change ρ (vb + (a • x + b • y)) - E (vb + (a • x + b • y)) - (ρ vb - E vb) ≤
      a * (ρ (vb + x) - E (vb + x) - (ρ vb - E vb)) +
        b * (ρ (vb + y) - E (vb + y) - (ρ vb - E vb))
    rw [map_add, map_add, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    obtain rfl : b = 1 - a := by linarith
    linarith
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hfn : ∀ y, -(η * ‖y‖) ≤ f y := by
    intro y
    have := hvb (vb + y)
    rw [dist_eq_norm, add_sub_cancel_left] at this
    simp only [hfdef]
    linarith
  obtain ⟨ℓ, hℓn, hℓ⟩ := exists_minorant_of_ge_neg_norm hfc hf0 hη.le hfn
  refine ⟨vb, ρ - ℓ, by rwa [sub_sub_cancel_left, norm_neg], fun w => ?_⟩
  have := hℓ (w - vb)
  simp only [hfdef, hg, add_sub_cancel] at this
  rw [sub_apply, map_sub ρ]
  linarith

end BR

end Continuum

end DFT
