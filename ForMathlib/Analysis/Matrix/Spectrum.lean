/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Rank-one spectral decompositions and Rayleigh minimisers of Hermitian matrices

* `Matrix.trace_vecMulVec_star_mul`: `tr(|u⟩⟨u| B) = ⟨u, B u⟩`.
* `Matrix.IsHermitian.eq_sum_vecMulVec`: `A = Σ_k λ_k |u_k⟩⟨u_k|` over the eigenvector basis.
* `Matrix.IsHermitian.trace_mul_eq_sum`: `tr(A B) = Σ_k λ_k ⟨u_k, B u_k⟩`.
* `Matrix.star_dotProduct_self_eq`: `⟨x, x⟩ = Σ_i ‖x_i‖²`.
* `Matrix.IsHermitian.mulVec_eq_of_le`: a unit vector minimising `⟨φ, A φ⟩` over unit vectors is an
  eigenvector, with the minimum as eigenvalue.
-/

namespace Matrix

open RCLike
open scoped ComplexOrder

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

lemma trace_vecMulVec_star_mul (u : n → 𝕜) (B : Matrix n n 𝕜) :
    (vecMulVec u (star u) * B).trace = star u ⬝ᵥ (B *ᵥ u) := by
  simp only [trace, diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum,
    Pi.star_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma star_dotProduct_self_eq (x : n → 𝕜) : star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [dotProduct, Pi.star_apply, ofReal_sum, ofReal_pow]
  exact Finset.sum_congr rfl fun i _ => by rw [RCLike.star_def, RCLike.conj_mul]

variable [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

lemma star_dotProduct_eigenvectorBasis (hA : A.IsHermitian) (k : n) :
    star ⇑(hA.eigenvectorBasis k) ⬝ᵥ ⇑(hA.eigenvectorBasis k) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    hA.eigenvectorBasis.orthonormal.1 k]
  simp

/-- **Spectral decomposition** into rank-one projections onto the eigenvectors. -/
lemma eq_sum_vecMulVec (hA : A.IsHermitian) :
    A = ∑ k, (hA.eigenvalues k : 𝕜) •
      vecMulVec ⇑(hA.eigenvectorBasis k) (star ⇑(hA.eigenvectorBasis k)) := by
  have h : A = (hA.eigenvectorUnitary : Matrix n n 𝕜) * diagonal (ofReal ∘ hA.eigenvalues) *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := hA.spectral_theorem
  refine h.trans ?_
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Function.comp_apply, star_apply, eigenvectorUnitary_apply,
    Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `tr(A B) = Σ_k λ_k ⟨u_k, B u_k⟩` over the eigenvectors of `A`. -/
lemma trace_mul_eq_sum (hA : A.IsHermitian) (B : Matrix n n 𝕜) :
    (A * B).trace = ∑ k, (hA.eigenvalues k : 𝕜) *
      (star ⇑(hA.eigenvectorBasis k) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis k))) := by
  conv_lhs => rw [hA.eq_sum_vecMulVec]
  rw [Finset.sum_mul, trace_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_mul_assoc, trace_smul, smul_eq_mul,
    trace_vecMulVec_star_mul]

omit [DecidableEq n] in
/-- **Rayleigh minimisers are eigenvectors.** If `c ≤ ⟨φ, A φ⟩` for all unit `φ` and the unit
vector `ψ` attains `c`, then `A ψ = c ψ`. -/
theorem mulVec_eq_of_le (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ φ : n → 𝕜, star φ ⬝ᵥ φ = 1 → c ≤ re (star φ ⬝ᵥ (A *ᵥ φ))) {ψ : n → 𝕜}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hψc : re (star ψ ⬝ᵥ (A *ᵥ ψ)) = c) : A *ᵥ ψ = (c : 𝕜) • ψ := by
  classical
  set M : Matrix n n 𝕜 := A - (c : 𝕜) • 1 with hM
  have hMh : M.IsHermitian := hA.sub (by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, RCLike.star_def, conj_ofReal])
  have hquad : ∀ x : n → 𝕜, star x ⬝ᵥ (M *ᵥ x) =
      star x ⬝ᵥ (A *ᵥ x) - (c : 𝕜) * star x ⬝ᵥ x := fun x => by
    rw [hM, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hpos : M.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hMh fun x => ?_
    refine RCLike.nonneg_iff.2 ⟨?_, hMh.im_star_dotProduct_mulVec_self x⟩
    rw [hquad, star_dotProduct_self_eq, map_sub, ← ofReal_mul, ofReal_re, sub_nonneg]
    set N := ∑ i, ‖x i‖ ^ 2
    rcases (Finset.sum_nonneg fun i _ => sq_nonneg ‖x i‖ : 0 ≤ N).eq_or_lt with h0 | hN
    · have hx : x = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖x i‖).1 h0.symm i
          (Finset.mem_univ _)
        simpa using this
      subst hx; simp [N]
    · set a : ℝ := (Real.sqrt N)⁻¹
      have ha2 : a ^ 2 * N = 1 := by
        rw [inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']
      have hunit : star ((a : 𝕜) • x) ⬝ᵥ ((a : 𝕜) • x) = 1 := by
        rw [star_smul, smul_dotProduct, dotProduct_smul, star_dotProduct_self_eq, RCLike.star_def,
          conj_ofReal, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← ofReal_mul, ← ofReal_mul, ← sq,
          ha2, ofReal_one]
      have h := hc _ hunit
      rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, RCLike.star_def,
        conj_ofReal, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← ofReal_mul, re_ofReal_mul,
        ← sq] at h
      have e : a ^ 2 * re (star x ⬝ᵥ (A *ᵥ x)) * N = re (star x ⬝ᵥ (A *ᵥ x)) := by
        rw [mul_right_comm, ha2, one_mul]
      nlinarith [mul_le_mul_of_nonneg_right h hN.le]
  have h0 : star ψ ⬝ᵥ (M *ᵥ ψ) = 0 := by
    rw [hquad, hψ, mul_one]
    have him := hA.im_star_dotProduct_mulVec_self ψ
    apply RCLike.ext <;> simp [hψc, him]
  have := (hpos.dotProduct_mulVec_zero_iff).1 h0
  rw [hM, sub_mulVec, sub_eq_zero, smul_mulVec, one_mulVec] at this
  exact this

end IsHermitian

end Matrix
