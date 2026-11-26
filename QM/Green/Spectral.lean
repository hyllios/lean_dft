/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.Analysis.PoissonKernel
import QM.Green.Lehmann

/-!
# The spectral function

The spectral function is `A(ω) = -π⁻¹ Im G(ω + i0)`, where `Im G = (G - G†) / 2i` is the
anti-Hermitian part of the matrix `G_ij`. By the Lehmann representation,
`-π⁻¹ Im G(ω + iη) = Σ_k W_k P_η(ω - ω_k)` with the Poisson kernel `P_η`. Since `P_η` is an
approximate identity, `A = Σ_k W_k δ(ω - ω_k)` as a limit of measures. The weights `W_k` are
positive semidefinite and add up to the identity (`QM.Green.lehmannWeight_posSemidef`,
`QM.Green.sum_lehmannWeight`), so `A` is a positive matrix-valued measure of total mass the
identity.

## Main definitions

* `imPart A = (A - A†) / 2i`.
* `greenMat H Ψ z`: the matrix `G_ij(z)`.

## Main results

* `neg_inv_pi_imPart_greenMat`: `-π⁻¹ Im G(ω + iη) = Σ_k W_k P_η(ω - ω_k)` for `η > 0`.
* `tendsto_spectral` (**spectral function**): for every bounded continuous `f`,
  `∫ f(ω) (-π⁻¹ Im G(ω + iη))_ij dω → Σ_k W_k,ij f(ω_k)` as `η → 0⁺`.
-/

namespace QM.Green

open Matrix Complex QM.ManyBody MeasureTheory Filter Topology ForMathlib
open scoped ComplexOrder

variable {M : ℕ}

/-- The anti-Hermitian part `Im A = (A - A†) / 2i` of a matrix. -/
noncomputable def imPart (A : Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  (2 * I)⁻¹ • (A - Aᴴ)

/-- The matrix `G_ij(z)`. -/
noncomputable def greenMat (H : FockOp M) (Ψ : Fock M) (z : ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun i j => greenZ H Ψ i j z

/-- `-π⁻¹ Im (x + iη)⁻¹ = P_η(x)`. -/
lemma neg_inv_pi_im_inv (x : ℝ) {η : ℝ} (hη : 0 < η) :
    -(Real.pi : ℂ)⁻¹ * ((2 * I)⁻¹ * (((x : ℂ) + η * I)⁻¹ - ((x : ℂ) - η * I)⁻¹)) =
      (poissonKernel η x : ℂ) := by
  have h1 : (x : ℂ) + η * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have h2 : (x : ℂ) - η * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h3 : ((x : ℂ) ^ 2 + (η : ℂ) ^ 2) ≠ 0 := by
    have : (x : ℝ) ^ 2 + η ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hprod : ((x : ℂ) + η * I) * ((x : ℂ) - η * I) = (x : ℂ) ^ 2 + (η : ℂ) ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [poissonKernel]
  push_cast
  rw [inv_sub_inv h1 h2, hprod]
  field_simp
  ring

/-- **`-π⁻¹ Im G(ω + iη) = Σ_k W_k P_η(ω - ω_k)`** for `η > 0`. -/
theorem neg_inv_pi_imPart_greenMat {H : FockOp M} (hH : H.IsHermitian) {Ψ : Fock M} {E₀ : ℝ}
    (hΨ : toFockCLM H Ψ = (E₀ : ℂ) • Ψ) (i j : Fin M) (ω : ℝ) {η : ℝ} (hη : 0 < η) :
    -(Real.pi : ℂ)⁻¹ * imPart (greenMat H Ψ (ω + η * I)) i j =
      ∑ k, lehmannWeight hH Ψ k i j * (poissonKernel η (ω - lehmannPole hH E₀ k) : ℂ) := by
  have hz : 0 < ((ω : ℂ) + η * I).im := by simpa using hη
  have hW : ∀ k, star (lehmannWeight hH Ψ k j i) = lehmannWeight hH Ψ k i j := fun k =>
    (lehmannWeight_posSemidef hH Ψ k).isHermitian.apply i j
  simp only [imPart, greenMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, smul_eq_mul]
  rw [greenZ_eq_sum hH hΨ i j hz, greenZ_eq_sum hH hΨ j i hz, star_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_div₀, hW, ← neg_inv_pi_im_inv _ hη]
  have hc : star ((ω : ℂ) + η * I - lehmannPole hH E₀ k) =
      ((ω - lehmannPole hH E₀ k : ℝ) : ℂ) - η * I := by
    apply Complex.ext <;> simp
  rw [hc]
  push_cast
  ring

/-- **The spectral function** `A(ω) = -π⁻¹ Im G(ω + i0) = Σ_k W_k δ(ω - ω_k)`: for every bounded
continuous `f`, `∫ f(ω) (-π⁻¹ Im G(ω + iη))_ij dω → Σ_k W_k,ij f(ω_k)` as `η → 0⁺`. -/
theorem tendsto_spectral {H : FockOp M} (hH : H.IsHermitian) {Ψ : Fock M} {E₀ : ℝ}
    (hΨ : toFockCLM H Ψ = (E₀ : ℂ) • Ψ) (i j : Fin M) {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun η : ℝ => ∫ ω : ℝ, (-(Real.pi : ℂ)⁻¹ * imPart (greenMat H Ψ (ω + η * I)) i j) * f ω)
      (𝓝[>] 0) (𝓝 (∑ k, lehmannWeight hH Ψ k i j * f (lehmannPole hH E₀ k))) := by
  have hlim : Tendsto (fun η : ℝ => ∑ k, lehmannWeight hH Ψ k i j *
      ∫ ω : ℝ, poissonKernel η (ω - lehmannPole hH E₀ k) • f ω) (𝓝[>] 0)
      (𝓝 (∑ k, lehmannWeight hH Ψ k i j * f (lehmannPole hH E₀ k))) :=
    tendsto_finsetSum _ fun k _ =>
      (tendsto_integral_poissonKernel hf hC (lehmannPole hH E₀ k)).const_mul _
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
  simp_rw [neg_inv_pi_imPart_greenMat hH hΨ i j _ hη, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [Complex.real_smul]
    ring
  · intro k _
    have := (integrable_poissonKernel_smul hf hC hη (lehmannPole hH E₀ k)).const_mul
      (lehmannWeight hH Ψ k i j)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Complex.real_smul]
    ring

end QM.Green
