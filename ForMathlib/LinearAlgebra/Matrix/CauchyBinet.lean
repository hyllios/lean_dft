/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort

/-!
# The Cauchy–Binet formula

For `A : n × m` and `B : m × n` matrices over a commutative ring,
`det (A B) = Σ_S det (A_{·,S}) det (B_{S,·})`, the sum over the `n`-element subsets `S` of the
`m` columns of `A` (rows of `B`), each listed in increasing order.

The proof expands `det (A B) = Σ_τ (Π_a B_{τ(a), a}) det (A_{·,τ})` over all maps
`τ : Fin n → Fin m`, groups the maps by their image, drops the non-injective ones (their minor has
two equal columns), and writes an injective map with image `S` as `S`'s increasing enumeration
composed with a permutation.

## Main results

* `Matrix.det_mul_eq_sum_det_mul_det` (**Cauchy–Binet**).
-/

namespace Matrix

open Finset Equiv

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- `det (A B) = Σ_τ (Π_a B_{τ(a), a}) det (A_{·,τ})`, the sum over all maps `τ`. -/
lemma det_mul_eq_sum_fun (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ τ : Fin n → Fin m, (∏ a, B (τ a) a) * (A.submatrix id τ).det := by
  simp only [det_apply, Matrix.mul_apply, Units.smul_def, zsmul_eq_mul]
  have h1 : ∀ σ : Perm (Fin n), ∏ a, ∑ k, A (σ a) k * B k a =
      ∑ τ : Fin n → Fin m, ∏ a, (A (σ a) (τ a) * B (τ a) a) := fun σ => Fintype.prod_sum _
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib]
  ring

/-- An injective map `Fin n → Fin m` is the increasing enumeration of its image composed with a
permutation. -/
lemma exists_perm_of_image {τ : Fin n → Fin m} {S : Finset (Fin m)} (hS : S.card = n)
    (himg : Finset.univ.image τ = S) : ∃ π : Perm (Fin n), τ = S.orderEmbOfFin hS ∘ π := by
  have hmem : ∀ a, τ a ∈ S := fun a => himg ▸ Finset.mem_image_of_mem τ (Finset.mem_univ a)
  let f : Fin n → Fin n := fun a => (S.orderIsoOfFin hS).symm ⟨τ a, hmem a⟩
  have hsurj : Function.Surjective f := by
    intro b
    have hb : S.orderEmbOfFin hS b ∈ Finset.univ.image τ := by
      rw [himg]; exact Finset.orderEmbOfFin_mem S hS b
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hb
    refine ⟨a, ?_⟩
    simp only [f, OrderIso.symm_apply_eq]
    ext; simp [ha]
  have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  funext a
  simp only [Function.comp_apply, Equiv.ofBijective_apply, f]
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

/-- **The Cauchy–Binet formula.** -/
theorem det_mul_eq_sum_det_mul_det (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ S : {S : Finset (Fin m) // S.card = n},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  rw [det_mul_eq_sum_fun, ← Finset.sum_fiberwise Finset.univ (fun τ => Finset.univ.image τ),
    ← Fintype.sum_subtype_add_sum_subtype (fun S : Finset (Fin m) => S.card = n)]
  -- fibres over images of the wrong size vanish
  have hzero : ∀ S : {S : Finset (Fin m) // ¬ S.card = n},
      ∑ τ ∈ Finset.univ.filter (fun τ : Fin n → Fin m => Finset.univ.image τ = S.1),
        (∏ a, B (τ a) a) * (A.submatrix id τ).det = 0 := by
    intro S
    refine Finset.sum_eq_zero fun τ hτ => ?_
    have himg := (Finset.mem_filter.mp hτ).2
    have hni : ¬ Function.Injective τ := by
      intro hinj
      apply S.2
      rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    rw [det_zero_of_column_eq hne (fun i => by simp [hab]), mul_zero]
  rw [Finset.sum_eq_zero fun S _ => hzero S, add_zero]
  refine Finset.sum_congr rfl fun S _ => ?_
  set e := S.1.orderEmbOfFin S.2
  -- the fibre over `S` is `{e ∘ π}`
  have hfib : ∑ τ ∈ Finset.univ.filter (fun τ : Fin n → Fin m => Finset.univ.image τ = S.1),
      (∏ a, B (τ a) a) * (A.submatrix id τ).det =
      ∑ π : Perm (Fin n), (∏ a, B (e (π a)) a) * (A.submatrix id (e ∘ π)).det := by
    symm
    refine Finset.sum_bij (fun π _ => e ∘ π) (fun π _ => ?_) (fun π₁ _ π₂ _ h => ?_)
      (fun τ hτ => ?_) (fun π _ => rfl)
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
      · intro hx
        obtain ⟨b, hb⟩ : ∃ b, e b = x := by
          have := (S.1.orderIsoOfFin S.2).surjective ⟨x, hx⟩
          obtain ⟨b, hb⟩ := this
          exact ⟨b, by simpa using congrArg Subtype.val hb⟩
        exact ⟨π.symm b, by simp [hb]⟩
    · ext a
      have := congrFun h a
      simp only [Function.comp_apply] at this
      exact congrArg Fin.val (e.injective this)
    · obtain ⟨π, hπ⟩ := exists_perm_of_image S.2 (Finset.mem_filter.mp hτ).2
      exact ⟨π, Finset.mem_univ _, hπ.symm⟩
  rw [hfib]
  have hperm : ∀ π : Perm (Fin n), (A.submatrix id (e ∘ π)).det =
      Perm.sign π * (A.submatrix id e).det := by
    intro π
    rw [show A.submatrix id (e ∘ π) = (A.submatrix id e).submatrix id π from rfl, det_permute']
  simp only [hperm]
  rw [det_apply (B.submatrix e id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring

end Matrix
