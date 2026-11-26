/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.LinearCombination

/-!
# Harmonic polynomials

The Laplacian `Δ = Σᵢ ∂ᵢ²` on `MvPolynomial σ R` and the harmonic homogeneous polynomials of
degree `n`. In three variables `x, y, z` over a field of characteristic `0`, `Δp = 0` expresses
the coefficients of `zᶜ⁺²` through those of `zᶜ`, so a harmonic polynomial of degree `n` is
determined by its `n + 1` coefficients of `xⁿ⁻ᵏ yᵏ` and its `n` coefficients of `xⁿ⁻¹⁻ᵏ yᵏ z`.
Hence the harmonic polynomials of degree `n` form a space of dimension at most `2n + 1`.

## Main definitions

* `MvPolynomial.laplacian σ R`: the Laplacian.
* `MvPolynomial.harmonicSubmodule σ R n`: homogeneous polynomials of degree `n` with `Δp = 0`.

## Main results

* `MvPolynomial.coeff_laplacian_mon3`: the coefficients of `Δp` in three variables.
* `MvPolynomial.eq_zero_of_harmonicData_eq_zero`: a harmonic polynomial is determined by its
  coefficients of `zᶜ`, `c ≤ 1`.
* `MvPolynomial.finrank_harmonicSubmodule_le`: `dim ≤ 2n + 1` in three variables.
* `MvPolynomial.pow_mem_harmonicSubmodule`: `(x + c y)ⁿ` is harmonic when `c² = -1`.
-/

namespace MvPolynomial

open Module Finsupp

section Laplacian

variable {σ R : Type*} [CommSemiring R] [Fintype σ]

variable (σ R) in
/-- The Laplacian `Δ = Σᵢ ∂ᵢ²`. -/
noncomputable def laplacian : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  ∑ i, (pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap

lemma laplacian_apply (p : MvPolynomial σ R) :
    laplacian σ R p = ∑ i, pderiv i (pderiv i p) := by
  rw [laplacian, LinearMap.sum_apply]; rfl

variable (σ R) in
/-- The harmonic polynomials of degree `n`: homogeneous of degree `n` with `Δp = 0`. -/
noncomputable def harmonicSubmodule (n : ℕ) : Submodule R (MvPolynomial σ R) :=
  homogeneousSubmodule σ R n ⊓ LinearMap.ker (laplacian σ R)

lemma mem_harmonicSubmodule {n : ℕ} {p : MvPolynomial σ R} :
    p ∈ harmonicSubmodule σ R n ↔ p.IsHomogeneous n ∧ laplacian σ R p = 0 := by
  simp [harmonicSubmodule, mem_homogeneousSubmodule]

end Laplacian

lemma coeff_pderiv_pderiv {σ R : Type*} [CommSemiring R] (i : σ) (p : MvPolynomial σ R)
    (m : σ →₀ ℕ) :
    (pderiv i (pderiv i p)).coeff m =
      p.coeff (m + single i 2) * (((m i : R) + 2) * ((m i : R) + 1)) := by
  classical
  rw [coeff_pderiv, coeff_pderiv, add_assoc, ← single_add]
  simp only [Finsupp.add_apply, single_eq_same, Nat.cast_add, Nat.cast_one]
  ring

/-! ### Three variables -/

section Three

/-- The exponent of `xᵃ yᵇ zᶜ`. -/
noncomputable def mon3 (a b c : ℕ) : Fin 3 →₀ ℕ := single 0 a + single 1 b + single 2 c

@[simp] lemma mon3_apply_zero (a b c : ℕ) : mon3 a b c 0 = a := by simp [mon3]
@[simp] lemma mon3_apply_one (a b c : ℕ) : mon3 a b c 1 = b := by simp [mon3]
@[simp] lemma mon3_apply_two (a b c : ℕ) : mon3 a b c 2 = c := by simp [mon3]

lemma eq_mon3 (m : Fin 3 →₀ ℕ) : m = mon3 (m 0) (m 1) (m 2) := by
  ext i; fin_cases i <;> simp

lemma degree_mon3 (a b c : ℕ) : (mon3 a b c).degree = a + b + c := by
  simp [mon3, map_add, degree_single]

lemma mon3_add_single_zero (a b c k : ℕ) : mon3 a b c + single 0 k = mon3 (a + k) b c := by
  ext i; fin_cases i <;> simp

lemma mon3_add_single_one (a b c k : ℕ) : mon3 a b c + single 1 k = mon3 a (b + k) c := by
  ext i; fin_cases i <;> simp

lemma mon3_add_single_two (a b c k : ℕ) : mon3 a b c + single 2 k = mon3 a b (c + k) := by
  ext i; fin_cases i <;> simp

/-- The coefficients of `Δp` in three variables. -/
lemma coeff_laplacian_mon3 {R : Type*} [CommSemiring R] (p : MvPolynomial (Fin 3) R)
    (a b c : ℕ) :
    (laplacian (Fin 3) R p).coeff (mon3 a b c) =
      p.coeff (mon3 (a + 2) b c) * (((a : R) + 2) * ((a : R) + 1)) +
        p.coeff (mon3 a (b + 2) c) * (((b : R) + 2) * ((b : R) + 1)) +
        p.coeff (mon3 a b (c + 2)) * (((c : R) + 2) * ((c : R) + 1)) := by
  rw [laplacian_apply, Fin.sum_univ_three, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, Finsupp.add_apply, coeff_pderiv_pderiv,
    coeff_pderiv_pderiv, coeff_pderiv_pderiv, mon3_add_single_zero, mon3_add_single_one,
    mon3_add_single_two]
  simp

variable {K : Type*} [Field K]

/-- The coefficients that determine a harmonic polynomial of degree `n`: those of `xⁿ⁻ᵏ yᵏ`
(`k ≤ n`) and of `xⁿ⁻¹⁻ᵏ yᵏ z` (`k < n`). -/
noncomputable def harmonicData (n : ℕ) :
    MvPolynomial (Fin 3) K →ₗ[K] (Fin (n + 1) → K) × (Fin n → K) :=
  LinearMap.prod (LinearMap.pi fun k => lcoeff K (mon3 (n - k) k 0))
    (LinearMap.pi fun k => lcoeff K (mon3 (n - 1 - k) k 1))

variable [CharZero K]

/-- **A harmonic polynomial is determined by its coefficients of `z⁰` and `z¹`.** -/
theorem eq_zero_of_harmonicData_eq_zero {n : ℕ} {p : MvPolynomial (Fin 3) K}
    (hp : p ∈ harmonicSubmodule (Fin 3) K n) (h0 : harmonicData n p = 0) : p = 0 := by
  obtain ⟨hh, hΔ⟩ := mem_harmonicSubmodule.mp hp
  have hfst : ∀ k : Fin (n + 1), p.coeff (mon3 (n - k) k 0) = 0 := fun k =>
    congrFun (congrArg Prod.fst h0) k
  have hsnd : ∀ k : Fin n, p.coeff (mon3 (n - 1 - k) k 1) = 0 := fun k =>
    congrFun (congrArg Prod.snd h0) k
  have low : ∀ c, c ≤ 1 → ∀ a b, p.coeff (mon3 a b c) = 0 := by
    intro c hc a b
    by_cases hd : a + b + c = n
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
      · have := hfst ⟨b, by omega⟩
        rwa [show n - b = a by omega] at this
      · have := hsnd ⟨b, by omega⟩
        rwa [show n - 1 - b = a by omega] at this
    · exact hh.coeff_eq_zero (by rw [degree_mon3]; exact hd)
  have all : ∀ c a b, p.coeff (mon3 a b c) = 0 := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      rcases lt_or_ge c 2 with hc | hc
      · exact low c (by omega)
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
        intro a b
        have key := coeff_laplacian_mon3 p a b c'
        rw [hΔ, ih c' (by omega) (a + 2) b, ih c' (by omega) a (b + 2)] at key
        have hne : ((c' + 2 : ℕ) : K) * ((c' + 1 : ℕ) : K) ≠ 0 :=
          mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
        push_cast at hne
        simp only [zero_mul, zero_add] at key
        rw [show (0 : MvPolynomial (Fin 3) K).coeff (mon3 a b c') = 0 by simp] at key
        exact (mul_eq_zero.mp key.symm).resolve_right hne
  ext m
  rw [eq_mon3 m, all]; simp

instance (n : ℕ) : FiniteDimensional K (harmonicSubmodule (Fin 3) K n) :=
  FiniteDimensional.of_injective ((harmonicData n).comp (harmonicSubmodule (Fin 3) K n).subtype)
    (by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      exact Subtype.ext (eq_zero_of_harmonicData_eq_zero p.2 hp))

/-- **The harmonic polynomials of degree `n` in three variables have dimension at most
`2n + 1`.** -/
theorem finrank_harmonicSubmodule_le (n : ℕ) :
    finrank K (harmonicSubmodule (Fin 3) K n) ≤ 2 * n + 1 := by
  have hinj : Function.Injective
      ((harmonicData n).comp (harmonicSubmodule (Fin 3) K n).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    exact Subtype.ext (eq_zero_of_harmonicData_eq_zero p.2 hp)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at this
  omega

end Three

/-- **`(x + c y)ⁿ` is harmonic** when `c² = -1`. -/
theorem pow_mem_harmonicSubmodule {R : Type*} [CommRing R] {c : R} (hc : c * c = -1) (n : ℕ) :
    (X 0 + C c * X 1 : MvPolynomial (Fin 3) R) ^ n ∈ harmonicSubmodule (Fin 3) R n := by
  set u : MvPolynomial (Fin 3) R := X 0 + C c * X 1
  have hu : u.IsHomogeneous 1 :=
    (isHomogeneous_X R 0).add ((isHomogeneous_X R 1).C_mul c)
  refine mem_harmonicSubmodule.mpr ⟨by simpa using hu.pow n, ?_⟩
  have d0 : pderiv 0 u = 1 := by simp [u, pderiv_X]
  have d1 : pderiv 1 u = C c := by simp [u, pderiv_X]
  have d2 : pderiv 2 u = 0 := by simp [u, pderiv_X]
  have hcC : C c * C c = (-1 : MvPolynomial (Fin 3) R) := by rw [← C_mul, hc, C_neg, C_1]
  rw [laplacian_apply, Fin.sum_univ_three]
  simp only [Derivation.leibniz_pow, d0, d1, d2, nsmul_eq_mul, smul_eq_mul, mul_one,
    mul_zero, map_zero, Derivation.map_natCast, Derivation.leibniz, pderiv_C,
    add_zero, zero_add, smul_zero]
  linear_combination ((n : MvPolynomial (Fin 3) R) * ((n - 1 : ℕ) : MvPolynomial (Fin 3) R) *
    u ^ (n - 1 - 1)) * hcC

end MvPolynomial
