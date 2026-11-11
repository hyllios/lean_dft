/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Spectral.Eigen
import DFT.Continuum.Spectral.Basis
import DFT.Continuum.Box.Ground

/-!
# The energy in the eigenbasis

Let `(eᵢ)` be the eigenbasis of the Green operator `G` of `-d²/dx² + W` (`W ≥ 0`), with
`G eᵢ = μᵢ eᵢ`. For `ψ` in the `C²` form domain, `ψ = G(-ψ'' + Wψ)`, so
`⟪eᵢ, ψ⟫ = μᵢ ⟪eᵢ, -ψ'' + Wψ⟫` and Parseval gives

`∫ ψ'² + ∫ W ψ² = Σᵢ μᵢ⁻¹ ⟪eᵢ, ψ⟫²`.

The eigenvalues `μᵢ` accumulate only at `0` and there are infinitely many of them, so the
`N` largest exist. With `λⱼ = μⱼ⁻¹` their inverses and `Λ = max λⱼ`, every other term has
`μᵢ⁻¹ ≥ Λ`, and the expansion gives the one-particle bound used for `N` free fermions:

`Λ ‖ψ‖² - Σⱼ (Λ - λⱼ) ⟪φⱼ, ψ⟫² ≤ ⟨ψ, h ψ⟩`.

* `toHL`: continuous functions as elements of `L²(0, 1)`.
* `Gop_toHL_src`: `G(-ψ'' + Wψ) = ψ` for `ψ` in the form domain.
* `hasSum_form`, `hasSum_sq`: the expansions of the energy and of the norm.
* `exists_top`: the `N` largest eigenvalues.
* `exists_orbitals`: **the one-particle bound** for a box potential `v`, with `N` orthonormal
  `C²` eigenfunctions.
-/

namespace DFT.Continuum.Spectral

open MeasureTheory Set Filter Topology Box

/-! ### Continuous functions in `L²(0, 1)` -/

/-- A continuous function as an element of `L²(0, 1)`. -/
noncomputable def toHL {g : ℝ → ℝ} (hg : Continuous g) : HL := (memLp_of_continuous hg).toLp

lemma toHL_ae {g : ℝ → ℝ} (hg : Continuous g) : (toHL hg : ℝ → ℝ) =ᵐ[μ1] g :=
  MemLp.coeFn_toLp _

lemma inner_toHL_right (f : HL) {g : ℝ → ℝ} (hg : Continuous g) :
    inner ℝ f (toHL hg) = ∫ x, (f : ℝ → ℝ) x * g x ∂μ1 := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [toHL_ae hg] with x hx
  rw [hx]; simp [mul_comm]

lemma inner_toHL_toHL {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) :
    inner ℝ (toHL ha) (toHL hb) = ∫ x, a x * b x ∂μ1 := by
  rw [inner_toHL_right]
  refine integral_congr_ae ?_
  filter_upwards [toHL_ae ha] with x hx
  rw [hx]

/-! ### Inverting the Green operator on the form domain -/

variable {W : ℝ → ℝ} (hWc : Continuous W) (hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t)

section dom

variable {ψ : ℝ → ℝ} (hψ : ψ ∈ Box.Dom)
include hψ

lemma dom_c2 : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.1 hψ.1).2.2

include hWc in
lemma continuous_src_dom : Continuous (src (W := W) ψ) :=
  (((dom_c2 hψ).continuous_deriv le_rfl).neg).add (hWc.mul hψ.1.continuous)

include hW0 in
/-- `G(-ψ'' + Wψ) = ψ` on `[0, 1]`. -/
lemma Gk_src {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Gk hWc (src (W := W) ψ) x = ψ x := by
  have hd1 : Differentiable ℝ ψ := hψ.1.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv ψ) := (dom_c2 hψ).differentiable one_ne_zero
  rw [Gk_eq_Gf hWc (continuous_src_dom hWc hψ) hx]
  have := eq_Gf hWc hW0 (continuous_src_dom hWc hψ) (y := ψ) (dy := deriv ψ)
    (fun t _ => (hd1 t).hasDerivAt)
    (fun t _ => by
      refine (hd2 t).hasDerivAt.congr_deriv ?_
      simp only [src]; ring)
    hψ.2.1 hψ.2.2 x (Icc_sub_Ioo' hx)
  exact this.symm

include hW0 in
/-- **`G(-ψ'' + Wψ) = ψ` in `L²(0, 1)`.** -/
lemma Gop_toHL_src :
    Gop hWc (toHL (continuous_src_dom hWc hψ)) = toHL hψ.1.continuous := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [Gop_ae hWc (toHL (continuous_src_dom hWc hψ)), toHL_ae hψ.1.continuous,
    ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
  rw [h1, h2, ← Gk_src hWc hW0 hψ (Ioo_subset_Icc_self hx)]
  exact Gk_congr hWc (toHL_ae _) x

include hWc in
/-- `⟨ψ, -ψ'' + Wψ⟩ = ∫ ψ'² + ∫ W ψ²` (integration by parts). -/
lemma inner_src :
    ∫ x, ψ x * src (W := W) ψ x ∂μ1 = ∫ x, (deriv ψ x ^ 2 + W x * ψ x ^ 2) ∂μ1 := by
  have h2 : ContDiff ℝ 2 ψ := hψ.1
  have hd1 : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t =>
    ((h2.differentiable (by norm_num)) t).hasDerivAt
  have hd2 : ∀ t, HasDerivAt (deriv ψ) (deriv (deriv ψ) t) t := fun t =>
    (((dom_c2 hψ).differentiable one_ne_zero) t).hasDerivAt
  have hc0 := h2.continuous
  have hc1 : Continuous (deriv ψ) := (dom_c2 hψ).continuous
  have hc2 : Continuous (deriv (deriv ψ)) := (dom_c2 hψ).continuous_deriv le_rfl
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := ψ) (u' := deriv ψ) (v := deriv ψ) (v' := deriv (deriv ψ))
    (fun t _ => hd1 t) (fun t _ => hd2 t) (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _)
  rw [hψ.2.1, hψ.2.2, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  rw [← integral_unit_mu1, ← integral_unit_mu1]
  have e1 : (fun x => ψ x * src (W := W) ψ x) =
      fun x => W x * ψ x ^ 2 - ψ x * deriv (deriv ψ) x := by
    funext x; simp only [src]; ring
  have e2 : (fun x => deriv ψ x ^ 2 + W x * ψ x ^ 2) =
      fun x => W x * ψ x ^ 2 + deriv ψ x * deriv ψ x := by
    funext x; ring
  rw [e1, e2, intervalIntegral.integral_sub (μ := volume)
      (f := fun x => W x * ψ x ^ 2) (g := fun x => ψ x * deriv (deriv ψ) x)
      ((hWc.mul (hc0.pow 2)).intervalIntegrable _ _) ((hc0.mul hc2).intervalIntegrable _ _),
    intervalIntegral.integral_add (μ := volume)
      (f := fun x => W x * ψ x ^ 2) (g := fun x => deriv ψ x * deriv ψ x)
      ((hWc.mul (hc0.pow 2)).intervalIntegrable _ _) ((hc1.mul hc1).intervalIntegrable _ _),
    hibp]
  ring

end dom

/-! ### The eigenbasis -/

/-- The index set of the eigenbasis. -/
abbrev Idx (hWc : Continuous W) := EIdx (Gop hWc)

/-- The eigenbasis of the Green operator. -/
noncomputable def eB : HilbertBasis (Idx hWc) ℝ HL :=
  eigenBasis (isCompactOperator_Gop hWc) (isSymmetric_Gop hWc)
    (fun _ hf => Gop_injective hWc hW0 hf)

/-- The eigenvalue of `eB i`. -/
def mu (i : Idx hWc) : ℝ := (i.1 : ℝ)

lemma Gop_eB (i : Idx hWc) : Gop hWc (eB hWc hW0 i) = mu hWc i • eB hWc hW0 i := by
  rw [eB, eigenBasis_coe]
  exact eigVec_apply _ _ i

include hW0 in
lemma mu_ne_zero (i : Idx hWc) : mu hWc i ≠ 0 :=
  eval_ne_zero (fun _ hf => Gop_injective hWc hW0 hf) i.1

lemma eB_ne_zero (i : Idx hWc) : eB hWc hW0 i ≠ 0 := by
  intro h
  have := (eB hWc hW0).orthonormal.1 i
  rw [h, norm_zero] at this
  exact zero_ne_one this

include hW0 in
lemma mu_pos (i : Idx hWc) : 0 < mu hWc i :=
  eigenvalue_pos hWc hW0 (eB_ne_zero hWc hW0 i) (mu_ne_zero hWc hW0 i) (Gop_eB hWc hW0 i)

lemma exists_rep (i : Idx hWc) : ∃ e : ℝ → ℝ, e ∈ Box.Dom ∧
    ((eB hWc hW0 i : HL) : ℝ → ℝ) =ᵐ[μ1] e ∧
      ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv e) x = (W x - (mu hWc i)⁻¹) * e x :=
  eigen_regular hWc hW0 (mu_ne_zero hWc hW0 i) (Gop_eB hWc hW0 i)

/-- The `C²` representative of `eB i`: a classical eigenfunction. -/
noncomputable def rep (i : Idx hWc) : ℝ → ℝ := Classical.choose (exists_rep hWc hW0 i)

lemma rep_mem (i : Idx hWc) : rep hWc hW0 i ∈ Box.Dom :=
  (Classical.choose_spec (exists_rep hWc hW0 i)).1

lemma rep_ae (i : Idx hWc) : ((eB hWc hW0 i : HL) : ℝ → ℝ) =ᵐ[μ1] rep hWc hW0 i :=
  (Classical.choose_spec (exists_rep hWc hW0 i)).2.1

lemma rep_ode (i : Idx hWc) : ∀ x ∈ Icc (0 : ℝ) 1,
    deriv (deriv (rep hWc hW0 i)) x = (W x - (mu hWc i)⁻¹) * rep hWc hW0 i x :=
  (Classical.choose_spec (exists_rep hWc hW0 i)).2.2

lemma inner_eB_toHL (i : Idx hWc) {g : ℝ → ℝ} (hg : Continuous g) :
    inner ℝ (eB hWc hW0 i) (toHL hg) = ∫ x, rep hWc hW0 i x * g x ∂μ1 := by
  rw [inner_toHL_right]
  refine integral_congr_ae ?_
  filter_upwards [rep_ae hWc hW0 i] with x hx
  rw [hx]

/-- The representatives are orthonormal in `L²(0, 1)`. -/
lemma rep_orthonormal (i j : Idx hWc) :
    ∫ x, rep hWc hW0 i x * rep hWc hW0 j x ∂μ1 = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.1 (eB hWc hW0).orthonormal i j
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [rep_ae hWc hW0 i, rep_ae hWc hW0 j] with x hi hj
  rw [hi, hj]; simp [mul_comm]

/-! ### The expansions -/

/-- The coefficient `⟪eᵢ, ψ⟫ = ∫ eᵢ ψ`. -/
noncomputable def coef (i : Idx hWc) (ψ : ℝ → ℝ) : ℝ := ∫ x, rep hWc hW0 i x * ψ x ∂μ1

/-- **Parseval**: `∫ ψ² = Σᵢ ⟪eᵢ, ψ⟫²`. -/
lemma hasSum_sq {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    HasSum (fun i => coef hWc hW0 i ψ ^ 2) (∫ x, ψ x * ψ x ∂μ1) := by
  have h := (eB hWc hW0).hasSum_inner_mul_inner (toHL hψ) (toHL hψ)
  rw [inner_toHL_toHL] at h
  refine h.congr_fun fun i => ?_
  rw [real_inner_comm, inner_eB_toHL, coef]; ring

/-- **The energy in the eigenbasis**: `∫ ψ'² + ∫ W ψ² = Σᵢ μᵢ⁻¹ ⟪eᵢ, ψ⟫²`. -/
lemma hasSum_form {ψ : ℝ → ℝ} (hψ : ψ ∈ Box.Dom) :
    HasSum (fun i => (mu hWc i)⁻¹ * coef hWc hW0 i ψ ^ 2)
      (∫ x, (deriv ψ x ^ 2 + W x * ψ x ^ 2) ∂μ1) := by
  have hg := continuous_src_dom hWc hψ
  have h := (eB hWc hW0).hasSum_inner_mul_inner (toHL hψ.1.continuous) (toHL hg)
  rw [inner_toHL_toHL, inner_src hWc hψ] at h
  refine h.congr_fun fun i => ?_
  -- `⟪eᵢ, ψ⟫ = ⟪eᵢ, G g⟫ = μᵢ ⟪eᵢ, g⟫`
  have hc := inner_eB_toHL hWc hW0 i hψ.1.continuous
  have hd := inner_eB_toHL hWc hW0 i hg
  rw [← coef] at hc hd
  have hG : coef hWc hW0 i ψ = mu hWc i * coef hWc hW0 i (src (W := W) ψ) := by
    rw [← hc, ← hd, ← Gop_toHL_src hWc hW0 hψ, ← Gop_symm, Gop_eB, real_inner_smul_left]
  have hμ := mu_ne_zero hWc hW0 i
  rw [real_inner_comm (eB hWc hW0 i) (toHL hψ.1.continuous), hc, hd, hG]
  field_simp

/-! ### Infinitely many eigenvectors -/

/-- The cell `(j/N, (j+1)/N)`. -/
noncomputable def cell (N : ℕ) (j : Fin N) : Set ℝ := Ioo ((j : ℝ) / N) ((j + 1 : ℝ) / N)

lemma cell_sub {N : ℕ} (j : Fin N) : cell N j ⊆ Ioo (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast j.pos
  have hj : (j : ℝ) + 1 ≤ N := by exact_mod_cast j.2
  intro x hx
  refine ⟨lt_of_le_of_lt (by positivity) hx.1, lt_of_lt_of_le hx.2 ?_⟩
  rw [div_le_one hN]; exact hj

lemma measurableSet_cell (N : ℕ) (j : Fin N) : MeasurableSet (cell N j) := measurableSet_Ioo

lemma cell_disjoint {N : ℕ} {j k : Fin N} (hjk : j ≠ k) : cell N j ∩ cell N k = ∅ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast j.pos
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  rw [cell, mem_Ioo] at h1 h2
  have a : (k : ℝ) < j + 1 := (div_lt_div_iff_of_pos_right hN).1 (h2.1.trans h1.2)
  have b : (j : ℝ) < k + 1 := (div_lt_div_iff_of_pos_right hN).1 (h1.1.trans h2.2)
  have a' : (k : ℕ) < j + 1 := by exact_mod_cast a
  have b' : (j : ℕ) < k + 1 := by exact_mod_cast b
  exact hjk (Fin.ext (by omega))

lemma mu1_cell {N : ℕ} (j : Fin N) : μ1 (cell N j) ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast j.pos
  change (volume.restrict (Ioo (0 : ℝ) 1)) (cell N j) ≠ 0
  rw [Measure.restrict_apply (measurableSet_cell N j), inter_eq_left.2 (cell_sub j), cell,
    Real.volume_Ioo]
  rw [Ne, ENNReal.ofReal_eq_zero, not_le, sub_pos]
  exact div_lt_div_of_pos_right (by linarith) hN

/-- `N` orthogonal nonzero vectors of `L²(0, 1)`: indicators of disjoint cells. -/
noncomputable def cellV (N : ℕ) (j : Fin N) : HL :=
  indicatorConstLp 2 (measurableSet_cell N j) (measure_ne_top μ1 (cell N j)) (1 : ℝ)

lemma linearIndependent_cellV (N : ℕ) : LinearIndependent ℝ (cellV N) := by
  refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun j h => ?_) fun j k hjk => ?_
  · have hn := norm_indicatorConstLp' (p := 2) (c := (1 : ℝ)) (hs := measurableSet_cell N j)
      (hμs := measure_ne_top μ1 (cell N j)) two_ne_zero (mu1_cell j)
    have h' : indicatorConstLp 2 (measurableSet_cell N j) (measure_ne_top μ1 (cell N j))
        (1 : ℝ) = 0 := h
    rw [h', norm_zero, norm_one, one_mul] at hn
    have hpos : 0 < μ1.real (cell N j) :=
      ENNReal.toReal_pos (mu1_cell j) (measure_ne_top μ1 _)
    have := Real.rpow_pos_of_pos hpos (1 / (2 : ENNReal).toReal)
    linarith
  · change inner ℝ (cellV N j) (cellV N k) = 0
    unfold cellV
    rw [L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_cell N j)
      (measurableSet_cell N k) (measure_ne_top μ1 _) (measure_ne_top μ1 _), cell_disjoint hjk]
    simp

include hW0 in
/-- **There are at least `N` eigenvectors**, for every `N`. -/
lemma exists_injective_idx (N : ℕ) : ∃ f : Fin N → Idx hWc, Function.Injective f := by
  by_cases hfin : Finite (Idx hWc)
  · let _ := Fintype.ofFinite (Idx hWc)
    have ob := (eB hWc hW0).toOrthonormalBasis
    have : FiniteDimensional ℝ HL := Module.Finite.of_basis ob.toBasis
    have h1 := (linearIndependent_cellV N).fintype_card_le_finrank
    rw [Module.finrank_eq_card_basis ob.toBasis, Fintype.card_fin] at h1
    exact ⟨(Fintype.equivFin _).symm ∘ Fin.castLE h1,
      (Fintype.equivFin _).symm.injective.comp (Fin.castLE_injective h1)⟩
  · have := not_finite_iff_infinite.1 hfin
    exact ⟨fun j => Infinite.natEmbedding _ j,
      (Infinite.natEmbedding _).injective.comp Fin.val_injective⟩

/-! ### The largest eigenvalues -/

/-- **The `N` largest values** of a positive function whose superlevel sets are finite. -/
lemma exists_top {ι : Type*} (m : ι → ℝ) (hpos : ∀ i, 0 < m i)
    (hfin : ∀ δ, 0 < δ → {i | δ ≤ m i}.Finite) :
    ∀ N : ℕ, (∃ f : Fin N → ι, Function.Injective f) →
      ∃ S : Finset ι, S.card = N ∧ ∀ i ∈ S, ∀ j ∉ S, m j ≤ m i := by
  classical
  intro N
  induction N with
  | zero => exact fun _ => ⟨∅, rfl, by simp⟩
  | succ N ih =>
    rintro ⟨f, hf⟩
    obtain ⟨S, hS, hord⟩ := ih ⟨f ∘ Fin.castSucc, hf.comp (Fin.castSucc_injective N)⟩
    -- some `f k` is outside `S`
    obtain ⟨j0, hj0⟩ : ∃ j0, j0 ∉ S := by
      by_contra h
      push Not at h
      have := Finset.card_le_card_of_injOn f (s := Finset.univ) (t := S)
        (fun k _ => h (f k)) (hf.injOn)
      simp [hS] at this
    set T := (hfin (m j0) (hpos j0)).toFinset.filter (· ∉ S)
    have hj0T : j0 ∈ T := by simp [T, hj0]
    obtain ⟨j1, hj1T, hmax⟩ := T.exists_max_image m ⟨j0, hj0T⟩
    have hj1S : j1 ∉ S := (Finset.mem_filter.1 hj1T).2
    have hj1m : m j0 ≤ m j1 := by
      have := (Finset.mem_filter.1 hj1T).1
      simpa using this
    refine ⟨insert j1 S, by rw [Finset.card_insert_of_notMem hj1S, hS], fun i hi j hj => ?_⟩
    rw [Finset.mem_insert, not_or] at hj
    rcases Finset.mem_insert.1 hi with rfl | hi
    · by_cases hjm : m j0 ≤ m j
      · exact hmax j (by simp [T, hjm, hj.2])
      · push Not at hjm; linarith
    · exact hord i hi j hj.2

/-! ### The one-particle bound -/

/-- **`N` orthonormal eigenfunctions and the one-particle bound.** For a box potential `v` and
`N = n + 1` there are `C²` eigenfunctions `φⱼ` (`-φⱼ'' + v φⱼ = λⱼ φⱼ`), orthonormal in
`L²(0, 1)`, and `Λ ≥ λⱼ` with `Λ ‖ψ‖² - Σⱼ (Λ - λⱼ) ⟪φⱼ, ψ⟫² ≤ ⟨ψ, h ψ⟩` for every state `ψ`. -/
theorem exists_orbitals (v : Pot) (n : ℕ) : ∃ (φ : Fin (n + 1) → ℝ → ℝ) (lam : Fin (n + 1) → ℝ)
    (Λ : ℝ), (∀ j, φ j ∈ Box.Dom) ∧
    (∀ j, ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv (φ j)) x = (ext v x - lam j) * φ j x) ∧
    (∀ j k, ∫ x, φ j x * φ k x ∂μ1 = if j = k then 1 else 0) ∧ (∀ j, lam j ≤ Λ) ∧
    ∀ ψ ∈ Box.Dom, Λ * ip (μ := μ1) ψ ψ - ∑ j, (Λ - lam j) * (∫ x, φ j x * ψ x ∂μ1) ^ 2 ≤
      Q Box.setting v ψ := by
  classical
  set E := -‖v‖
  have hWc := continuous_Wof v E
  have hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ Wof v E t := fun t _ => by
    have := abs_ext_le v t
    simp only [Wof, E, sub_neg_eq_add]
    linarith [neg_abs_le (ext v t)]
  obtain ⟨f, hf⟩ := exists_injective_idx hWc hW0 (n + 1)
  obtain ⟨S, hS, hord⟩ := exists_top (mu hWc) (mu_pos hWc hW0)
    (fun δ hδ => finite_ge (isCompactOperator_Gop hWc) (isSymmetric_Gop hWc)
      (fun _ hf => Gop_injective hWc hW0 hf) hδ) (n + 1) ⟨f, hf⟩
  have hne : S.Nonempty := Finset.card_pos.1 (by rw [hS]; exact Nat.succ_pos n)
  set e : Fin (n + 1) ≃ S := (Fintype.equivFinOfCardEq (by simp [hS])).symm
  set idx : Fin (n + 1) → Idx hWc := fun j => (e j : Idx hWc)
  have hidx : ∀ j k, idx j = idx k ↔ j = k := fun j k =>
    ⟨fun h => e.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  set Λ' := S.sup' hne fun i => (mu hWc i)⁻¹
  refine ⟨fun j => rep hWc hW0 (idx j), fun j => (mu hWc (idx j))⁻¹ + E, Λ' + E,
    fun j => rep_mem hWc hW0 _, fun j x hx => ?_, fun j k => ?_, fun j => ?_, fun ψ hψ => ?_⟩
  · rw [rep_ode hWc hW0 _ x hx]; simp only [Wof]; ring
  · rw [rep_orthonormal]; exact if_congr (hidx j k) rfl rfl
  · simp only [add_le_add_iff_right]
    exact Finset.le_sup' (fun i => (mu hWc i)⁻¹) (e j).2
  · -- the expansion, with the terms outside `S` dropped
    have hF := hasSum_form hWc hW0 hψ
    have hN := hasSum_sq hWc hW0 hψ.1.continuous
    have hD := hF.sub (hN.mul_left Λ')
    have hle := sum_le_hasSum S (fun i hi => by
      have hΛ : Λ' ≤ (mu hWc i)⁻¹ := Finset.sup'_le hne _ fun s hs =>
        inv_anti₀ (mu_pos hWc hW0 i) (hord s hs i hi)
      have := sq_nonneg (coef hWc hW0 i ψ)
      nlinarith) hD
    have hQ := Q_sub_eq v E hψ
    have hsum : ∑ i ∈ S, ((mu hWc i)⁻¹ * coef hWc hW0 i ψ ^ 2 - Λ' * coef hWc hW0 i ψ ^ 2) =
        ∑ j, ((mu hWc (idx j))⁻¹ * coef hWc hW0 (idx j) ψ ^ 2 -
          Λ' * coef hWc hW0 (idx j) ψ ^ 2) := by
      rw [← Finset.sum_coe_sort S]
      exact (e.sum_comp (fun i : S => (mu hWc i)⁻¹ * coef hWc hW0 i ψ ^ 2 -
        Λ' * coef hWc hW0 i ψ ^ 2)).symm
    have hneg : ∑ j, (Λ' + E - ((mu hWc (idx j))⁻¹ + E)) *
        (∫ x, rep hWc hW0 (idx j) x * ψ x ∂μ1) ^ 2 =
        -∑ j, ((mu hWc (idx j))⁻¹ * coef hWc hW0 (idx j) ψ ^ 2 -
          Λ' * coef hWc hW0 (idx j) ψ ^ 2) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [coef]; ring
    rw [hneg]
    rw [hsum] at hle
    simp only [ip] at hQ ⊢
    linarith

end DFT.Continuum.Spectral
