/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean_dft contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Basic.Real.Sign
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Girardeau's sign and extension from the ordered chamber

The sign of the Vandermonde determinant recovers a symmetric wavefunction from its
alternating extension. The image criterion applies to any form domain for which chamber
restriction and antisymmetrization are admissible and collision vanishing depends on the
squared modulus.
-/
namespace QM.ManyBody.Girardeau

open MeasureTheory Set
variable {N : ℕ}

private abbrev permSign (σ : Equiv.Perm (Fin N)) : ℝ := ((Equiv.Perm.sign σ : ℤˣ) : ℤ)

/-- Girardeau's sign, with value zero at a coincidence. -/
noncomputable def sign (x : Fin N → ℝ) : ℝ := Real.sign (Matrix.vandermonde x).det

theorem sign_eq_pair_product (x : Fin N → ℝ) :
    sign x = ∏ i, ∏ j ∈ Finset.Ioi i, Real.sign (x j - x i) := by
  let signMap : ℝ →*₀ ℝ := SignType.castHom.comp signHom
  have hsign (r : ℝ) : signMap r = Real.sign r := by
    change ((SignType.sign r : SignType) : ℝ) = Real.sign r
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · rw [_root_.sign_neg hr, Real.sign_of_neg hr]
      rfl
    · rw [_root_.sign_zero, Real.sign_zero]
      rfl
    · rw [_root_.sign_pos hr, Real.sign_of_pos hr]
      rfl
  rw [sign, Matrix.det_vandermonde]
  simp only [← hsign, map_prod]

private theorem sign_sq {x : Fin N → ℝ} (hx : Function.Injective x) : sign x ^ 2 = 1 := by
  rcases Real.sign_apply_eq_of_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.mpr hx) with h | h <;>
    simp [sign, h]

private theorem sign_comp_perm (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    sign (x ∘ σ) = permSign σ * sign x := by
  have hm : Matrix.vandermonde (x ∘ σ) = (Matrix.vandermonde x).submatrix σ id := rfl
  rw [sign, hm, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [sign, permSign, h, Real.sign_neg]

/-- Unnormalized antisymmetrization of a wavefunction. -/
noncomputable def alternating (u : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin N), permSign σ * u (x ∘ σ)

/-- Exactly one permutation places a collision-free configuration in the ordered chamber. -/
theorem sign_mul_alternating_indicator {C : Set (Fin N → ℝ)} {x : Fin N → ℝ}
    (hC : ∀ z ∈ C, StrictMono z) (hx : Function.Injective x)
    (hex : ∃ σ : Equiv.Perm (Fin N), x ∘ σ ∈ C) {f : (Fin N → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin N), f (x ∘ σ) = f x) :
    sign x * alternating (C.indicator f) x = f x := by
  classical
  obtain ⟨σ, hs⟩ := hex
  have hs₁ := hC _ hs
  have hone : sign (x ∘ σ) = 1 := by
    apply Real.sign_of_pos
    rw [Matrix.det_vandermonde]
    exact Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      sub_pos.mpr (hs₁ (Finset.mem_Ioi.mp hj))
  have hsign := sign_comp_perm x σ
  rw [hone] at hsign
  unfold alternating
  rw [Finset.sum_eq_single σ, indicator_of_mem hs, hf σ]
  · rw [mul_left_comm, ← mul_assoc, ← hsign, one_mul]
  · intro τ _ hne
    have hnot : x ∘ τ ∉ C := by
      intro ht
      have h₁ := Tuple.comp_sort_eq_comp_iff_monotone.mpr (hC _ ht).monotone
      have h₂ := Tuple.comp_sort_eq_comp_iff_monotone.mpr hs₁.monotone
      exact hne (Equiv.ext fun i => hx (congrFun (h₁.trans h₂.symm) i))
    rw [indicator_of_notMem hnot, mul_zero]
  · simp

/-- Image of the sign map on symmetric states. The two closure hypotheses concern
ordinary restriction and the alternating sum, separately. -/
theorem image_iff {μ : Measure (Fin N → ℝ)} {C : Set (Fin N → ℝ)}
    {regular fermionic : Set ((Fin N → ℝ) → ℝ)} {zeroTrace : ((Fin N → ℝ) → ℝ) → Prop}
    {f : (Fin N → ℝ) → ℝ} (hC : ∀ x ∈ C, StrictMono x)
    (hinj : ∀ᵐ x ∂μ, Function.Injective x)
    (hcover : ∀ᵐ x ∂μ, ∃ σ : Equiv.Perm (Fin N), x ∘ σ ∈ C)
    (hsym : ∀ᵐ x ∂μ, ∀ σ : Equiv.Perm (Fin N), f (x ∘ σ) = f x)
    (hcut : zeroTrace f → C.indicator f ∈ regular)
    (halt : ∀ u ∈ regular, alternating u ∈ fermionic)
    (hfer : ∀ g ∈ fermionic, zeroTrace g)
    (hmod : ∀ g ∈ fermionic, (∀ᵐ x ∂μ, f x ^ 2 = g x ^ 2) → zeroTrace g → zeroTrace f) :
    zeroTrace f ↔ ∃ g ∈ fermionic, f =ᵐ[μ] fun x => sign x * g x := by
  constructor
  · intro hz
    refine ⟨_, halt _ (hcut hz), ?_⟩
    filter_upwards [hinj, hcover, hsym] with x hx hc hf
    exact (sign_mul_alternating_indicator hC hx hc hf).symm
  · rintro ⟨g, hg, he⟩
    apply hmod g hg _ (hfer g hg)
    filter_upwards [hinj, he] with x hx heq
    rw [heq, mul_pow, sign_sq hx, one_mul]

end QM.ManyBody.Girardeau
