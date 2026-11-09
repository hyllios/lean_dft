/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Pair.Basic
import DFT.Continuum.Box.Ground
import DFT.Continuum.Box.PiconeEq

/-!
# Two free bosons in a box: an unconditional many-body Hohenberg–Kohn theorem

Two non-interacting bosons on `[0, 1]` with hard walls and a continuous potential `v`. Let `ψ₀` be
the one-particle ground state (energy `E₀`, from `Continuum/Box/Ground`).

* `Q_free_sub`, `lower_bound`: the energy splits into one-particle energies along horizontal and
  vertical slices, each `≥ E₀` (Fubini), so every state has energy `≥ 2E₀`.
* `prod_isGS`: the product `ψ₀(x₁) ψ₀(x₂)` has energy exactly `2E₀`, so it is a ground state.
* `ucp_free`: every ground state has energy `2E₀`, so every horizontal slice is an equality case of
  the Picone inequality, hence a multiple of `ψ₀`; with exchange symmetry the ground state is
  `k ψ₀ ⊗ ψ₀` with `k ≠ 0`, which has no zeros in the square.
* `hk_free_bosons`: **Hohenberg–Kohn for two free bosons in a box, with no assumption**.
-/

namespace DFT

namespace Continuum

namespace Pair

open MeasureTheory Set Filter Topology Box

/-- Two non-interacting bosons in the box. -/
noncomputable abbrev free : Setting μ2 Pot := setting2 1 (fun _ => 0) continuous_const

lemma hprod : (μ2 : Measure (ℝ × ℝ)) = μ1.prod μ1 := by
  rw [Measure.prod_restrict]; rfl

/-- Fubini on the square, inner integral over `x₁`. -/
lemma fub1 {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    ∫ p, F p ∂μ2 = ∫ y, ∫ x, F (x, y) ∂μ1 ∂μ1 := by
  have hi := integrable2 hF
  rw [hprod] at hi ⊢
  exact integral_prod_symm F hi

/-- Fubini on the square, inner integral over `x₂`. -/
lemma fub2 {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    ∫ p, F p ∂μ2 = ∫ x, ∫ y, F (x, y) ∂μ1 ∂μ1 := by
  have hi := integrable2 hF
  rw [hprod] at hi ⊢
  exact integral_prod F hi

section slices

variable {φ : ℝ × ℝ → ℝ}

lemma slice1_mem (hφ : φ ∈ Dom2 1) (y : ℝ) : (fun x => φ (x, y)) ∈ Dom :=
  ⟨hφ.1.comp (contDiff_id.prodMk contDiff_const), hφ.2.2.1 y, hφ.2.2.2 y⟩

lemma slice2_mem (hφ : φ ∈ Dom2 1) (x : ℝ) : (fun y => φ (x, y)) ∈ Dom := by
  refine ⟨hφ.1.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
  · have := hφ.2.1 (0, x); simp only [Prod.swap_prod_mk, one_mul] at this
    simp only [this, hφ.2.2.1 x]
  · have := hφ.2.1 (1, x); simp only [Prod.swap_prod_mk, one_mul] at this
    simp only [this, hφ.2.2.2 x]

lemma deriv_slice1 (hφ : φ ∈ Dom2 1) (x y : ℝ) : deriv (fun x => φ (x, y)) x = d1 φ (x, y) := by
  have h := ((diff2 hφ (x, y)).hasFDerivAt).comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  exact h.deriv

lemma deriv_slice2 (hφ : φ ∈ Dom2 1) (x y : ℝ) : deriv (fun y => φ (x, y)) y = d2 φ (x, y) := by
  have h := ((diff2 hφ (x, y)).hasFDerivAt).comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  exact h.deriv

end slices

variable (v : Pot)

/-- The slice energies: `A = (∂₁φ)² + W(x₁) φ²` and `B = (∂₂φ)² + W(x₂) φ²`, `W = v - E`. -/
noncomputable def sA (E : ℝ) (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d1 φ p ^ 2 + Wof v E p.1 * φ p ^ 2
noncomputable def sB (E : ℝ) (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d2 φ p ^ 2 + Wof v E p.2 * φ p ^ 2

lemma continuous_sA (E : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) : Continuous (sA v E φ) :=
  ((cont_d1 hφ).pow 2).add (((continuous_Wof v E).comp continuous_fst).mul (hφ.1.continuous.pow 2))

lemma continuous_sB (E : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) : Continuous (sB v E φ) :=
  ((cont_d2 hφ).pow 2).add (((continuous_Wof v E).comp continuous_snd).mul (hφ.1.continuous.pow 2))

/-- The two-particle energy above `2E` is the sum of the slice energies. -/
lemma Q_free_sub (E : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) :
    Q free v φ - 2 * E * ip (μ := μ2) φ φ = ∫ p, sA v E φ p ∂μ2 + ∫ p, sB v E φ p ∂μ2 := by
  have hc := hφ.1.continuous
  have i1 := integrable2 (((cont_d1 hφ).mul (cont_d1 hφ)).add ((cont_d2 hφ).mul (cont_d2 hφ)))
  have i2 := integrable2 ((continuous_L2 v).mul (hc.mul hc))
  have i3 := integrable2 (hc.mul hc)
  rw [← integral_add (integrable2 (continuous_sA v E hφ)) (integrable2 (continuous_sB v E hφ))]
  have hpt : (fun p => sA v E φ p + sB v E φ p) = fun p =>
      ((d1 φ p * d1 φ p + d2 φ p * d2 φ p) + L2 v p * (φ p * φ p)) - 2 * E * (φ p * φ p) := by
    funext p
    simp only [sA, sB, Wof, L2, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  rw [hpt, integral_sub (f := fun p => (d1 φ p * d1 φ p + d2 φ p * d2 φ p) + L2 v p * (φ p * φ p))
    (g := fun p => 2 * E * (φ p * φ p)) (i1.add i2) (i3.const_mul _),
    integral_add (f := fun p => d1 φ p * d1 φ p + d2 φ p * d2 φ p)
      (g := fun p => L2 v p * (φ p * φ p)) i1 i2, integral_const_mul]
  simp only [Q, setting2, h02, pf, ip, zero_mul, integral_zero, add_zero]

/-- The slice energy along `x₁` at height `y` is a one-particle energy above `E`. -/
lemma slice_A (E : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) (y : ℝ) :
    ∫ x, sA v E φ (x, y) ∂μ1 =
      Q setting v (fun x => φ (x, y)) -
        E * ip (μ := μ1) (fun x => φ (x, y)) (fun x => φ (x, y)) := by
  rw [Q_sub_eq v E (slice1_mem hφ y)]
  simp only [sA, deriv_slice1 hφ]

lemma slice_B (E : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) (x : ℝ) :
    ∫ y, sB v E φ (x, y) ∂μ1 =
      Q setting v (fun y => φ (x, y)) -
        E * ip (μ := μ1) (fun y => φ (x, y)) (fun y => φ (x, y)) := by
  rw [Q_sub_eq v E (slice2_mem hφ x)]
  simp only [sB, deriv_slice2 hφ]

/-- **Lower bound.** Every two-boson state has energy at least `2E₀`. -/
theorem lower_bound {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) :
    2 * Estar v * ip (μ := μ2) φ φ ≤ Q free v φ := by
  obtain ⟨-, -, -, -, -, hlow⟩ := gs_data v
  have h := Q_free_sub v (Estar v) hφ
  have hA : 0 ≤ ∫ p, sA v (Estar v) φ p ∂μ2 := by
    rw [fub1 (continuous_sA v _ hφ)]
    refine integral_nonneg fun y => ?_
    show (0 : ℝ) ≤ _
    rw [slice_A v _ hφ y]
    linarith [hlow _ (slice1_mem hφ y)]
  have hB : 0 ≤ ∫ p, sB v (Estar v) φ p ∂μ2 := by
    rw [fub2 (continuous_sB v _ hφ)]
    refine integral_nonneg fun x => ?_
    show (0 : ℝ) ≤ _
    rw [slice_B v _ hφ x]
    linarith [hlow _ (slice2_mem hφ x)]
  linarith

/-- The product state `ψ(x₁) ψ(x₂)`. -/
noncomputable def prodState (ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := ψ p.1 * ψ p.2

lemma prodState_mem {ψ : ℝ → ℝ} (hψ : ψ ∈ Dom) : prodState ψ ∈ Dom2 1 :=
  ⟨(hψ.1.comp contDiff_fst).mul (hψ.1.comp contDiff_snd), fun p => by simp [prodState]; ring,
    fun y => by simp [prodState, hψ.2.1], fun y => by simp [prodState, hψ.2.2]⟩

lemma ip_prodState (ψ : ℝ → ℝ) :
    ip (μ := μ2) (prodState ψ) (prodState ψ) = ip (μ := μ1) ψ ψ ^ 2 := by
  simp only [ip, prodState]
  rw [hprod]
  have : (fun p : ℝ × ℝ => ψ p.1 * ψ p.2 * (ψ p.1 * ψ p.2)) =
      fun p => (ψ p.1 * ψ p.1) * (ψ p.2 * ψ p.2) := by funext p; ring
  rw [this, integral_prod_mul (fun x => ψ x * ψ x) (fun y => ψ y * ψ y), sq]

/-- **The product of one-particle ground states is a two-boson ground state**, with energy `2E₀`. -/
theorem prod_isGS : ∃ Ψ, IsGS free v Ψ ∧ Q free v Ψ = 2 * Estar v * ip (μ := μ2) Ψ Ψ := by
  obtain ⟨ψ, hD, -, hQ, hpos, -⟩ := gs_data v
  set E := Estar v
  have hΨ := prodState_mem hD
  have h1d : ∫ x, (deriv ψ x ^ 2 + Wof v E x * ψ x ^ 2) ∂μ1 = 0 := by
    rw [← Q_sub_eq v E hD, hQ]; ring
  have hA : ∫ p, sA v E (prodState ψ) p ∂μ2 = 0 := by
    rw [fub1 (continuous_sA v E hΨ)]
    have : ∀ y, ∫ x, sA v E (prodState ψ) (x, y) ∂μ1 =
        ψ y ^ 2 * ∫ x, (deriv ψ x ^ 2 + Wof v E x * ψ x ^ 2) ∂μ1 := by
      intro y
      rw [← integral_const_mul]
      congr 1; funext x
      simp only [sA]
      rw [← deriv_slice1 hΨ]
      simp only [prodState]
      rw [deriv_mul_const (diff_of_mem hD x)]
      ring
    simp [this, h1d]
  have hB : ∫ p, sB v E (prodState ψ) p ∂μ2 = 0 := by
    rw [fub2 (continuous_sB v E hΨ)]
    have : ∀ x, ∫ y, sB v E (prodState ψ) (x, y) ∂μ1 =
        ψ x ^ 2 * ∫ y, (deriv ψ y ^ 2 + Wof v E y * ψ y ^ 2) ∂μ1 := by
      intro x
      rw [← integral_const_mul]
      congr 1; funext y
      simp only [sB]
      rw [← deriv_slice2 hΨ]
      simp only [prodState]
      rw [deriv_const_mul _ (diff_of_mem hD y)]
      ring
    simp [this, h1d]
  have hQΨ : Q free v (prodState ψ) = 2 * E * ip (μ := μ2) (prodState ψ) (prodState ψ) := by
    have := Q_free_sub v E hΨ
    rw [hA, hB] at this
    linarith
  have hposΨ : 0 < ip (μ := μ2) (prodState ψ) (prodState ψ) := by
    rw [ip_prodState]; positivity
  refine ⟨prodState ψ, ⟨hΨ, hposΨ, fun φ hφ => ?_⟩, hQΨ⟩
  rw [hQΨ]
  nlinarith [mul_le_mul_of_nonneg_left (lower_bound v hφ) hposΨ.le]

/-- A continuous nonnegative function on `(0, 1)` with zero integral vanishes on `(0, 1)`. -/
lemma eq_zero_of_integral_zero {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ y, 0 ≤ f y)
    (hint : ∫ y, f y ∂μ1 = 0) : ∀ y ∈ Ioo (0 : ℝ) 1, f y = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => h0 y) (integrable_of_continuous hf)).1 hint
  exact Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hf.continuousOn continuousOn_const

/-- The slice energy is continuous in the slice position. -/
lemma continuous_sliceA (E : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : φ ∈ Dom2 1) :
    Continuous fun y => ∫ x, sA v E φ (x, y) ∂μ1 := by
  have h : (fun y => ∫ x, sA v E φ (x, y) ∂μ1) =
      fun y => ∫ x in Icc (0 : ℝ) 1, sA v E φ (x, y) := by
    funext y; exact (integral_Icc_eq_integral_Ioo).symm
  rw [h]
  exact continuous_parametric_integral_of_continuous
    (f := fun y x => sA v E φ (x, y))
    ((continuous_sA v E hφ).comp continuous_swap) isCompact_Icc

/-- **Unique continuation for free bosons.** Every two-boson ground state is a nonzero multiple of
`ψ₀(x₁) ψ₀(x₂)` on the square, so it has no zeros there. -/
theorem ucp_free {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS free v Φ) : ∀ᵐ p ∂μ2, Φ p ≠ 0 := by
  set E := Estar v
  set α := sol v E
  obtain ⟨Ψ, hΨ, hQΨ⟩ := prod_isGS v
  have hD : Φ ∈ Dom2 1 := hΦ.1
  -- `Φ` has energy exactly `2E`
  have hQ : Q free v Φ = 2 * E * ip (μ := μ2) Φ Φ := by
    have h1 := hΦ.2.2 Ψ hΨ.1
    rw [hQΨ] at h1
    have h2 := lower_bound v hD
    have hp := hΨ.2.1
    nlinarith
  -- so the slice energies along `x₁` vanish
  have hsum := Q_free_sub v E hD
  rw [hQ, sub_self] at hsum
  obtain ⟨-, -, -, -, -, hlow⟩ := gs_data v
  have hIA : ∀ y, 0 ≤ ∫ x, sA v E Φ (x, y) ∂μ1 := fun y => by
    rw [slice_A v E hD y]; linarith [hlow _ (slice1_mem hD y)]
  have hIB : ∀ x, 0 ≤ ∫ y, sB v E Φ (x, y) ∂μ1 := fun x => by
    rw [slice_B v E hD x]; linarith [hlow _ (slice2_mem hD x)]
  have hA0 : ∫ p, sA v E Φ p ∂μ2 = 0 := by
    have hA := integral_nonneg (μ := μ1) (f := fun y => ∫ x, sA v E Φ (x, y) ∂μ1)
      (fun y => hIA y)
    have hB := integral_nonneg (μ := μ1) (f := fun x => ∫ y, sB v E Φ (x, y) ∂μ1)
      (fun x => hIB x)
    rw [fub1 (continuous_sA v E hD)] at hsum ⊢
    rw [fub2 (continuous_sB v E hD)] at hsum
    linarith
  rw [fub1 (continuous_sA v E hD)] at hA0
  have hslice := eq_zero_of_integral_zero (continuous_sliceA v E hD) hIA hA0
  -- each horizontal slice is a multiple of `ψ₀`
  have hmult : ∀ y ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, Φ (x, y) = c * (α x).1 := by
    intro y hy
    refine picone_eq (continuous_Wof v E) (ψ := fun t => (α t).1) (ψ' := fun t => (α t).2)
      (fun t ht => hasDerivAt_fst_of (sol_deriv v E) ht)
      (fun t ht => hasDerivAt_snd_of (sol_deriv v E) ht)
      (star_pos v) (by simp [α, sol_zero]) (star_one v) (by simp [α, sol_zero]) (star_d1 v)
      (slice1_mem hD y) ?_
    have := hslice y hy
    simp only [sA, ← deriv_slice1 hD] at this
    exact this
  -- by exchange symmetry, `Φ = k ψ₀ ⊗ ψ₀` on the square
  have hx0 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hα0 : 0 < (α (1 / 2)).1 := star_pos v _ hx0
  have hform : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      Φ (x, y) = Φ (1 / 2, y) / (α (1 / 2)).1 * (α x).1 := by
    intro x hx y hy
    obtain ⟨c, hc⟩ := hmult y hy
    rw [hc x hx, hc _ hx0]
    field_simp
  have hsym : ∀ p, Φ p.swap = Φ p := fun p => by simpa using hD.2.1 p
  set k := Φ (1 / 2, 1 / 2) / (α (1 / 2)).1 / (α (1 / 2)).1
  have hprodf : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, Φ (x, y) = k * (α x).1 * (α y).1 := by
    intro x hx y hy
    have h1 := hform x hx y hy
    have h2 : Φ (1 / 2, y) = Φ (y, 1 / 2) := by simpa using hsym (y, 1 / 2)
    have h3 := hform y hy (1 / 2) hx0
    rw [h1, h2, h3]
    simp only [k]
    field_simp
  -- `k ≠ 0`, since `Φ ≠ 0`
  have hk : k ≠ 0 := by
    intro hk0
    have hpos := hΦ.2.1
    have : ip (μ := μ2) Φ Φ = 0 := by
      simp only [ip]
      rw [setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
        (g := fun _ => (0 : ℝ)) (fun p hp => by
          simp only
          rw [show p = (p.1, p.2) from rfl, hprodf p.1 hp.1 p.2 hp.2, hk0]; ring)]
      simp
    linarith
  refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 (ae_of_all _ ?_)
  intro p hp
  rw [show p = (p.1, p.2) from rfl, hprodf p.1 hp.1 p.2 hp.2]
  exact mul_ne_zero (mul_ne_zero hk (star_pos v _ hp.1).ne') (star_pos v _ hp.2).ne'

/-- **Hohenberg–Kohn for two free bosons in a box, unconditional.** Every continuous potential
has a two-boson ground state, and ground states of two continuous potentials with the same one-body
density `ρ(x) = ∫ ψ(x, y)² dy` force the potentials to differ by a constant. -/
theorem hk_free_bosons (v v' : Pot) :
    (∃ Φ, IsGS free v Φ) ∧ ∀ Φ Φ', IsGS free v Φ → IsGS free v' Φ' →
      (∀ x ∈ Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, Φ (x, y) ^ 2 =
        ∫ y in Ioo (0 : ℝ) 1, Φ' (x, y) ^ 2) → ∃ k : ℝ, v - v' = k • one := by
  refine ⟨(prod_isGS v).imp fun _ h => h.1, fun Φ Φ' h h' hρ => ?_⟩
  exact hk_pair_of_ucp (by norm_num) h h' hρ (ucp_free v h)

end Pair

end Continuum

end DFT
