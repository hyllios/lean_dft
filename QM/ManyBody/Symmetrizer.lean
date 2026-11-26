/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.GroupTheory.Perm.Sign
import QM.ManyBody.Slater

/-!
# The symmetrizer and the antisymmetrizer

Permutations `σ ∈ S_N` act on functions of `N` variables by `(σ f)(x) = f (x ∘ σ)`, that is
`(σ f)(x₁, …, x_N) = f(x_{σ 1}, …, x_{σ N})`. The symmetrizer is `𝒮 = (1/N!) Σ_σ σ` and the
antisymmetrizer is `𝒜 = (1/N!) Σ_σ sign(σ) σ`.

## Main definitions

* `permL σ`: the action of `σ` as a linear map.
* `symm`, `anti`: the symmetrizer and the antisymmetrizer.
* `IsSymmFun f`, `IsAntiFun f`: symmetric and antisymmetric functions.

## Main results

* `permL_comp_symm`, `permL_comp_anti`: `σ 𝒮 = 𝒮`, `σ 𝒜 = sign(σ) 𝒜`.
* `symm_comp_symm`, `anti_comp_anti`: both are idempotent.
* `symm_comp_anti`, `anti_comp_symm`: `𝒮 𝒜 = 𝒜 𝒮 = 0` for `N ≥ 2`.
* `mem_range_symm_iff`, `mem_range_anti_iff`: the ranges are the symmetric and the
  antisymmetric functions.
* `ip_symm_left`, `ip_anti_left`: on a finite set of positions both are self-adjoint for
  `⟨f, g⟩ = Σ_x conj (f x) g x`, hence orthogonal projections.
* `anti_prod`, `anti_prod_eq_slater`: the antisymmetrized product of orbitals is the Slater
  determinant divided by `N!`.
-/

namespace QM.ManyBody

open Equiv Finset

variable {X 𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- The action `(σ f)(x) = f (x ∘ σ)` of a permutation on functions of `N` variables. -/
def permL (σ : Perm (Fin N)) : ((Fin N → X) → 𝕜) →ₗ[𝕜] ((Fin N → X) → 𝕜) where
  toFun f x := f (x ∘ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma permL_apply (σ : Perm (Fin N)) (f : (Fin N → X) → 𝕜) (x : Fin N → X) :
    permL σ f x = f (x ∘ σ) := rfl

lemma permL_mul (σ τ : Perm (Fin N)) :
    (permL σ).comp (permL τ) = (permL (σ * τ) : ((Fin N → X) → 𝕜) →ₗ[𝕜] _) := rfl

lemma permL_one : (permL 1 : ((Fin N → X) → 𝕜) →ₗ[𝕜] _) = LinearMap.id := rfl

/-- The symmetrizer `𝒮 = (1/N!) Σ_σ σ`. -/
noncomputable def symm : ((Fin N → X) → 𝕜) →ₗ[𝕜] ((Fin N → X) → 𝕜) :=
  ((N.factorial : 𝕜)⁻¹) • ∑ σ : Perm (Fin N), permL σ

/-- The antisymmetrizer `𝒜 = (1/N!) Σ_σ sign(σ) σ`. -/
noncomputable def anti : ((Fin N → X) → 𝕜) →ₗ[𝕜] ((Fin N → X) → 𝕜) :=
  ((N.factorial : 𝕜)⁻¹) • ∑ σ : Perm (Fin N), ((Perm.sign σ : ℤ) : 𝕜) • permL σ

/-- Symmetric functions: `σ f = f` for every `σ`. -/
def IsSymmFun (f : (Fin N → X) → 𝕜) : Prop := ∀ σ : Perm (Fin N), permL σ f = f

/-- Antisymmetric functions: `σ f = sign(σ) f` for every `σ`. -/
def IsAntiFun (f : (Fin N → X) → 𝕜) : Prop :=
  ∀ σ : Perm (Fin N), permL σ f = ((Perm.sign σ : ℤ) : 𝕜) • f

lemma card_perm_ne_zero : ((Fintype.card (Perm (Fin N)) : ℕ) : 𝕜) ≠ 0 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  exact_mod_cast N.factorial_ne_zero

lemma sign_mul_sign (σ : Perm (Fin N)) :
    ((Perm.sign σ : ℤ) : 𝕜) * ((Perm.sign σ : ℤ) : 𝕜) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

lemma symm_apply (f : (Fin N → X) → 𝕜) :
    symm f = (N.factorial : 𝕜)⁻¹ • ∑ σ : Perm (Fin N), permL σ f := by
  rw [symm, LinearMap.smul_apply, LinearMap.sum_apply]

lemma anti_apply (f : (Fin N → X) → 𝕜) :
    anti f = (N.factorial : 𝕜)⁻¹ • ∑ σ : Perm (Fin N), ((Perm.sign σ : ℤ) : 𝕜) • permL σ f := by
  rw [anti, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

/-- `σ 𝒮 = 𝒮`. -/
theorem permL_comp_symm (σ : Perm (Fin N)) :
    (permL σ).comp (symm : ((Fin N → X) → 𝕜) →ₗ[𝕜] _) = symm := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, symm_apply, map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ => rfl

/-- `σ 𝒜 = sign(σ) 𝒜`. -/
theorem permL_comp_anti (σ : Perm (Fin N)) :
    (permL σ).comp (anti : ((Fin N → X) → 𝕜) →ₗ[𝕜] _) = ((Perm.sign σ : ℤ) : 𝕜) • anti := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, anti_apply, map_smul, map_sum,
    smul_comm ((Perm.sign σ : ℤ) : 𝕜), Finset.smul_sum (r := ((Perm.sign σ : ℤ) : 𝕜))]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft σ)
    (fun τ => permL σ (((Perm.sign τ : ℤ) : 𝕜) • permL τ f))
    (fun ρ => ((Perm.sign σ : ℤ) : 𝕜) • (((Perm.sign ρ : ℤ) : 𝕜) • permL ρ f)) fun τ => ?_
  rw [map_smul, smul_smul, Equiv.coe_mulLeft, Perm.sign_mul, Units.val_mul, Int.cast_mul,
    ← mul_assoc, sign_mul_sign, one_mul]
  rfl

lemma symm_comp_of {L : ((Fin N → X) → 𝕜) →ₗ[𝕜] ((Fin N → X) → 𝕜)} {c : Perm (Fin N) → 𝕜}
    (h : ∀ σ, (permL σ).comp L = c σ • L) :
    symm.comp L = (((N.factorial : 𝕜)⁻¹) * ∑ σ, c σ) • L := by
  refine LinearMap.ext fun f => ?_
  have h' : ∀ σ, permL σ (L f) = c σ • L f := fun σ => congrArg (fun T => T f) (h σ)
  rw [LinearMap.comp_apply, symm_apply, LinearMap.smul_apply,
    Finset.sum_congr rfl fun σ _ => h' σ, ← Finset.sum_smul, smul_smul]

lemma anti_comp_of {L : ((Fin N → X) → 𝕜) →ₗ[𝕜] ((Fin N → X) → 𝕜)} {c : Perm (Fin N) → 𝕜}
    (h : ∀ σ, (permL σ).comp L = c σ • L) :
    anti.comp L = (((N.factorial : 𝕜)⁻¹) * ∑ σ, ((Perm.sign σ : ℤ) : 𝕜) * c σ) • L := by
  refine LinearMap.ext fun f => ?_
  have h' : ∀ σ, permL σ (L f) = c σ • L f := fun σ => congrArg (fun T => T f) (h σ)
  rw [LinearMap.comp_apply, anti_apply, LinearMap.smul_apply,
    Finset.sum_congr rfl fun σ _ => by rw [h' σ, smul_smul], ← Finset.sum_smul, smul_smul]

lemma sum_one_perm : ∑ _σ : Perm (Fin N), (1 : 𝕜) = N.factorial := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_one]

/-- For `N ≥ 2` there are as many even as odd permutations. -/
lemma sum_sign_eq_zero (hN : 2 ≤ N) : ∑ σ : Perm (Fin N), ((Perm.sign σ : ℤ) : 𝕜) = 0 := by
  set τ : Perm (Fin N) := swap ⟨0, by omega⟩ ⟨1, by omega⟩
  have hτ : Perm.sign τ = -1 := Perm.sign_swap (by simp [Fin.ext_iff])
  have h : ∑ σ : Perm (Fin N), ((Perm.sign σ : ℤ) : 𝕜) =
      -∑ σ : Perm (Fin N), ((Perm.sign σ : ℤ) : 𝕜) := by
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
    simp [Perm.sign_mul, hτ]
  have h2 : (2 : 𝕜) * ∑ σ : Perm (Fin N), ((Perm.sign σ : ℤ) : 𝕜) = 0 := by
    rw [two_mul]; nth_rw 2 [h]; exact add_neg_cancel _
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

lemma factorial_ne_zero' : (N.factorial : 𝕜) ≠ 0 := by exact_mod_cast N.factorial_ne_zero

/-- **`𝒮² = 𝒮`.** -/
theorem symm_comp_symm : (symm : ((Fin N → X) → 𝕜) →ₗ[𝕜] _).comp symm = symm := by
  rw [symm_comp_of (c := fun _ => 1) (fun σ => by rw [permL_comp_symm, one_smul]), sum_one_perm,
    inv_mul_cancel₀ factorial_ne_zero', one_smul]

/-- **`𝒜² = 𝒜`.** -/
theorem anti_comp_anti : (anti : ((Fin N → X) → 𝕜) →ₗ[𝕜] _).comp anti = anti := by
  rw [anti_comp_of permL_comp_anti]
  simp_rw [sign_mul_sign]
  rw [sum_one_perm, inv_mul_cancel₀ factorial_ne_zero', one_smul]

/-- **`𝒮 𝒜 = 0`** for `N ≥ 2`. -/
theorem symm_comp_anti (hN : 2 ≤ N) : (symm : ((Fin N → X) → 𝕜) →ₗ[𝕜] _).comp anti = 0 := by
  rw [symm_comp_of permL_comp_anti, sum_sign_eq_zero hN, mul_zero, zero_smul]

/-- **`𝒜 𝒮 = 0`** for `N ≥ 2`. -/
theorem anti_comp_symm (hN : 2 ≤ N) : (anti : ((Fin N → X) → 𝕜) →ₗ[𝕜] _).comp symm = 0 := by
  rw [anti_comp_of (c := fun _ => 1) (fun σ => by rw [permL_comp_symm, one_smul])]
  simp_rw [mul_one]
  rw [sum_sign_eq_zero hN, mul_zero, zero_smul]

/-! ### The ranges -/

/-- `𝒮 f` is symmetric. -/
lemma isSymmFun_symm (f : (Fin N → X) → 𝕜) : IsSymmFun (symm f) := fun σ =>
  congrArg (fun L : ((Fin N → X) → 𝕜) →ₗ[𝕜] _ => L f) (permL_comp_symm σ)

/-- `𝒜 f` is antisymmetric. -/
lemma isAntiFun_anti (f : (Fin N → X) → 𝕜) : IsAntiFun (anti f) := fun σ =>
  congrArg (fun L : ((Fin N → X) → 𝕜) →ₗ[𝕜] _ => L f) (permL_comp_anti σ)

/-- A symmetric function is fixed by `𝒮`. -/
lemma symm_of_isSymmFun {f : (Fin N → X) → 𝕜} (hf : IsSymmFun f) : symm f = f := by
  rw [symm_apply, Finset.sum_congr rfl fun σ _ => hf σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul 𝕜,
    smul_smul, inv_mul_cancel₀ factorial_ne_zero', one_smul]

/-- An antisymmetric function is fixed by `𝒜`. -/
lemma anti_of_isAntiFun {f : (Fin N → X) → 𝕜} (hf : IsAntiFun f) : anti f = f := by
  rw [anti_apply, Finset.sum_congr rfl fun σ _ => by rw [hf σ, smul_smul, sign_mul_sign, one_smul],
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul 𝕜,
    smul_smul, inv_mul_cancel₀ factorial_ne_zero', one_smul]

/-- **The range of `𝒮` is the space of symmetric functions.** -/
theorem mem_range_symm_iff (f : (Fin N → X) → 𝕜) :
    f ∈ LinearMap.range (symm : ((Fin N → X) → 𝕜) →ₗ[𝕜] _) ↔ IsSymmFun f := by
  constructor
  · rintro ⟨g, rfl⟩; exact isSymmFun_symm g
  · exact fun hf => ⟨f, symm_of_isSymmFun hf⟩

/-- **The range of `𝒜` is the space of antisymmetric functions.** -/
theorem mem_range_anti_iff (f : (Fin N → X) → 𝕜) :
    f ∈ LinearMap.range (anti : ((Fin N → X) → 𝕜) →ₗ[𝕜] _) ↔ IsAntiFun f := by
  constructor
  · rintro ⟨g, rfl⟩; exact isAntiFun_anti g
  · exact fun hf => ⟨f, anti_of_isAntiFun hf⟩

/-! ### Self-adjointness -/

section Finite

variable [Fintype X]

/-- The `ℓ²` inner product `⟨f, g⟩ = Σ_x conj (f x) g x`. -/
def ip (f g : (Fin N → X) → 𝕜) : 𝕜 := ∑ x, star (f x) * g x

/-- `⟨σ f, g⟩ = ⟨f, σ⁻¹ g⟩`. -/
lemma ip_permL_left (σ : Perm (Fin N)) (f g : (Fin N → X) → 𝕜) :
    ip (permL σ f) g = ip f (permL σ⁻¹ g) := by
  unfold ip
  refine Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl X)) _ _ fun x => ?_
  simp only [permL_apply]
  congr 2
  funext i; simp [Perm.inv_def]

lemma star_inv_factorial : star ((N.factorial : 𝕜)⁻¹) = (N.factorial : 𝕜)⁻¹ := by
  rw [star_inv₀, star_natCast]

lemma star_sign (σ : Perm (Fin N)) : star ((Perm.sign σ : ℤ) : 𝕜) = ((Perm.sign σ : ℤ) : 𝕜) := by
  rw [star_intCast]

lemma ip_smul_sum_left (F : (Fin N → X) → 𝕜) (c : 𝕜) (G : Perm (Fin N) → (Fin N → X) → 𝕜) :
    ip (c • ∑ σ, G σ) F = star c * ∑ σ, ip (G σ) F := by
  unfold ip
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, star_mul', star_sum, Finset.mul_sum,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by ring

lemma ip_smul_sum_right (F : (Fin N → X) → 𝕜) (c : 𝕜) (G : Perm (Fin N) → (Fin N → X) → 𝕜) :
    ip F (c • ∑ σ, G σ) = c * ∑ σ, ip F (G σ) := by
  unfold ip
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- **`𝒮` is self-adjoint.** -/
theorem ip_symm_left (f g : (Fin N → X) → 𝕜) : ip (symm f) g = ip f (symm g) := by
  rw [symm, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    ip_smul_sum_left, ip_smul_sum_right, star_inv_factorial]
  congr 1
  simp_rw [ip_permL_left]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => rfl

/-- **`𝒜` is self-adjoint.** -/
theorem ip_anti_left (f g : (Fin N → X) → 𝕜) : ip (anti f) g = ip f (anti g) := by
  have hs : ∀ (c : 𝕜) (F G : (Fin N → X) → 𝕜), ip (c • F) G = star c * ip F G := by
    intro c F G; simp [ip, Finset.mul_sum, mul_assoc]
  have hs' : ∀ (c : 𝕜) (F G : (Fin N → X) → 𝕜), ip F (c • G) = c * ip F G := by
    intro c F G
    unfold ip
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
  rw [anti, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    ip_smul_sum_left, ip_smul_sum_right, star_inv_factorial]
  congr 1
  simp_rw [LinearMap.smul_apply, hs, hs', star_sign, ip_permL_left]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => ?_
  simp [Perm.sign_inv]

end Finite

/-! ### Slater determinants -/

/-- **The antisymmetrized product of orbitals is a determinant**:
`𝒜 (φ₁ ⊗ ⋯ ⊗ φ_N)(x) = det [φ_j (x_k)] / N!`. -/
theorem anti_prod (φ : Fin N → X → 𝕜) (x : Fin N → X) :
    anti (fun y : Fin N → X => ∏ j, φ j (y j)) x =
      (N.factorial : 𝕜)⁻¹ * (Matrix.of fun k j => φ j (x k)).det := by
  rw [anti, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.det_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, LinearMap.smul_apply, permL_apply, smul_eq_mul,
    Function.comp_apply, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]

/-- For real orbitals on `Fin M` the antisymmetrized product is the lattice Slater determinant
`DFT.slater` divided by `N!`. -/
theorem anti_prod_eq_slater {M : ℕ} (φ : Fin N → Fin M → ℝ) (x : Fin N → Fin M) :
    anti (fun y : Fin N → Fin M => ∏ j, φ j (y j)) x = DFT.slater φ x / N.factorial := by
  rw [anti_prod, DFT.slater, div_eq_inv_mul]

end QM.ManyBody
