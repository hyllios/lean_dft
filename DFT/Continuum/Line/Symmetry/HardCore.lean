/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Basic.Real.Sign
import DFT.Continuum.Line.Core.Chamber

/-!
# Girardeau's map

Girardeau's map multiplies by the sign of the Vandermonde product,

  `A(x) = sign ∏_{i<j} (x_j - x_i)`,

which is `±1` away from collisions, locally constant there, and changes sign as a fermionic wave
function does. So `ψ ↦ A ψ` sends fermionic states to symmetric states vanishing at contact, and
preserves `|ψ|²` and the gradient almost everywhere. Hard-core bosons are built on it in
`Line/HardCoreW`, the Tonks–Girardeau gas in `Line/TonksW`.

* `gA`: Girardeau's sign; `gA_pm`, `gA_mul_self`, `gA_eventually`.
* `mu_collision`, `ae_injective`: the collision set is null.
* `mulA`: the map; `mulA_mulA`, `sq_mulA`, `dk_mulA` on fermionic `C²` states.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ}

/-! ### Girardeau's sign -/

/-- The Vandermonde product `∏_{i<j} (x_j - x_i)`, as a determinant. -/
noncomputable def vdm (x : Cfg n) : ℝ := (Matrix.vandermonde x).det

/-- Girardeau's sign `A(x) = sign ∏_{i<j} (x_j - x_i)`. -/
noncomputable def gA (x : Cfg n) : ℝ := Real.sign (vdm x)

lemma vdm_ne_zero_iff {x : Cfg n} : vdm x ≠ 0 ↔ Function.Injective x :=
  Matrix.det_vandermonde_ne_zero_iff

lemma continuous_vdm : Continuous (vdm (n := n)) := by
  unfold vdm
  exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).pow _)

lemma vdm_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : vdm (pm σ x) = sgn σ * vdm x := by
  have : Matrix.vandermonde (pm σ x) = (Matrix.vandermonde x).submatrix σ id := rfl
  rw [vdm, this, Matrix.det_permute, vdm, sgn]

lemma sgn_eq_or (σ : Equiv.Perm (Fin (n + 1))) : sgn σ = 1 ∨ sgn σ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sgn, h]

lemma gA_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : gA (pm σ x) = sgn σ * gA x := by
  rw [gA, gA, vdm_pm]
  rcases sgn_eq_or σ with h | h <;> simp [h, Real.sign_neg]

lemma gA_eq_zero {x : Cfg n} (hx : ¬ Function.Injective x) : gA x = 0 := by
  rw [gA, show vdm x = 0 by by_contra h; exact hx (vdm_ne_zero_iff.1 h), Real.sign_zero]

lemma gA_mul_self {x : Cfg n} (hx : Function.Injective x) : gA x * gA x = 1 := by
  rcases Real.sign_apply_eq_of_ne_zero _ (vdm_ne_zero_iff.2 hx) with h | h <;>
    simp [gA, h]

lemma abs_gA_le (x : Cfg n) : |gA x| ≤ 1 := by
  rcases Real.sign_apply_eq (vdm x) with h | h | h <;> simp [gA, h]

/-- Away from collisions, `A` is locally constant. -/
lemma gA_eventually {x : Cfg n} (hx : Function.Injective x) : ∀ᶠ y in 𝓝 x, gA y = gA x := by
  have h0 := vdm_ne_zero_iff.2 hx
  rcases h0.lt_or_gt with h | h
  · filter_upwards [continuous_vdm.continuousAt.eventually (gt_mem_nhds h)] with y hy
    simp [gA, Real.sign_of_neg hy, Real.sign_of_neg h]
  · filter_upwards [continuous_vdm.continuousAt.eventually (lt_mem_nhds h)] with y hy
    simp [gA, Real.sign_of_pos hy, Real.sign_of_pos h]

/-- The collision set is null. -/
lemma mu_collision : μN n (NearS 0) = 0 := by
  rw [NearS_eq]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · refine le_antisymm ?_ (zero_le)
    refine (measure_mono (s := {x : Cfg n | i ≠ j ∧ |x i - x j| ≤ 0})
      (t := {x : Cfg n | |x i - x j| ≤ 0}) fun x hx => hx.2).trans ?_
    simpa using mu_strip_le (n := n) le_rfl hij

/-- Almost every configuration has no collision. -/
lemma ae_injective : ∀ᵐ x ∂μN n, Function.Injective x := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (mu_collision (n := n))] with x hx
  exact Far.injective le_rfl (not_not.1 hx)

/-! ### The Girardeau map -/

/-- Multiplication by Girardeau's sign. -/
noncomputable def mulA : (Cfg n → ℝ) →ₗ[ℝ] (Cfg n → ℝ) where
  toFun ψ := fun x => gA x * ψ x
  map_add' a b := by funext x; simp [mul_add]
  map_smul' r a := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma mulA_apply (ψ : Cfg n → ℝ) (x : Cfg n) : mulA ψ x = gA x * ψ x := rfl

lemma DomF_collision {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) {x : Cfg n} (hx : ¬ Function.Injective x) :
    ψ x = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, x i = x j ∧ i ≠ j := by
    by_contra h; push Not at h; exact hx fun i j hij => by_contra fun hne => hne (h i j hij)
  exact eq_zero_of_collision hψ hne hij

/-- `A² ψ φ = ψ φ` pointwise when `ψ` is fermionic. -/
lemma mulA_mul_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (φ : Cfg n → ℝ) (x : Cfg n) :
    mulA ψ x * mulA φ x = ψ x * φ x := by
  by_cases hx : Function.Injective x
  · rw [mulA_apply, mulA_apply, show gA x * ψ x * (gA x * φ x) = (gA x * gA x) * (ψ x * φ x) by
      ring, gA_mul_self hx, one_mul]
  · simp [mulA_apply, gA_eq_zero hx, DomF_collision hψ hx]

lemma mulA_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) : mulA (mulA ψ) = ψ := by
  funext x
  have := mulA_mul_mulA hψ (fun _ => 1) x
  by_cases hx : Function.Injective x
  · rw [mulA_apply, mulA_apply, ← mul_assoc, gA_mul_self hx, one_mul]
  · simp [mulA_apply, gA_eq_zero hx, DomF_collision hψ hx]

lemma sq_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) (x : Cfg n) : mulA ψ x ^ 2 = ψ x ^ 2 := by
  rw [sq, sq, mulA_mul_mulA hψ]

/-- Off collisions, the partial derivatives of `A ψ` are `A` times those of `ψ`. -/
lemma dk_mulA {ψ : Cfg n → ℝ} (hψ : ψ ∈ DomF n) {x : Cfg n} (hx : Function.Injective x)
    (k : Fin (n + 1)) : dk k (mulA ψ) x = gA x * dk k ψ x := by
  have he : (mulA ψ : Cfg n → ℝ) =ᶠ[𝓝 x] fun y => gA x * ψ y := by
    filter_upwards [gA_eventually hx] with y hy
    rw [mulA_apply, hy]
  simp only [dk, he.fderiv_eq, fderiv_const_mul ((diffF hψ) x), FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]

end DFT.Continuum.Line
