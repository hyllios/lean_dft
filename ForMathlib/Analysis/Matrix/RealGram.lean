/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import ForMathlib.Analysis.Matrix.Spectrum

/-!
# The real Gram determinant of vectors in `𝕜ⁿ`

For vectors `x_a ∈ 𝕜ⁿ` (`𝕜 = ℝ` or `ℂ`), the real Gram matrix `G_ab = Re⟨x_a, x_b⟩` is the Gram
matrix of the `x_a` viewed as vectors of the real space `ℝ^{n}` or `ℝ^{2n}`.

* `Matrix.det_reGram_eq_zero_iff`: `det G = 0` iff the `x_a` are linearly dependent over `ℝ`.
-/

namespace Matrix

open RCLike

variable {𝕜 n ι : Type*} [RCLike 𝕜] [Fintype n] [Fintype ι]

/-- The real Gram matrix `Re⟨x_a, x_b⟩`. -/
def reGram (x : ι → n → 𝕜) : Matrix ι ι ℝ := of fun a b => re (star (x a) ⬝ᵥ x b)

lemma star_dotProduct_sum_smul (y : n → 𝕜) (c : ι → ℝ) (x : ι → n → 𝕜) :
    star y ⬝ᵥ ∑ b, c b • x b = ∑ b, (c b : 𝕜) * (star y ⬝ᵥ x b) := by
  rw [dotProduct_sum]
  exact Finset.sum_congr rfl fun b _ => by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), dotProduct_smul, smul_eq_mul]

/-- **The real Gram determinant vanishes iff the vectors are linearly dependent over `ℝ`.** -/
theorem det_reGram_eq_zero_iff [DecidableEq ι] (x : ι → n → 𝕜) :
    (reGram x).det = 0 ↔ ¬LinearIndependent ℝ x := by
  rw [← exists_mulVec_eq_zero_iff, Fintype.not_linearIndependent_iff]
  have hGc : ∀ (c : ι → ℝ) a, (reGram x *ᵥ c) a = re (star (x a) ⬝ᵥ ∑ b, c b • x b) := by
    intro c a
    rw [star_dotProduct_sum_smul, map_sum]
    simp only [mulVec, dotProduct, reGram, of_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [re_ofReal_mul, mul_comm]
  constructor
  · rintro ⟨c, hc0, hGc0⟩
    refine ⟨c, ?_, ?_⟩
    · set y := ∑ b, c b • x b
      have hq : re (star y ⬝ᵥ y) = 0 := by
        have : ∑ a, c a * (reGram x *ᵥ c) a = 0 := by simp [hGc0]
        rw [← this]
        conv_lhs => rw [show y = ∑ b, c b • x b from rfl]
        rw [star_sum, sum_dotProduct, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGc, star_smul, star_trivial, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_dotProduct,
          smul_eq_mul, re_ofReal_mul]
      rw [star_dotProduct_self_eq, ofReal_re] at hq
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖y i‖).1 hq i
        (Finset.mem_univ _)
      simpa using this
    · by_contra h
      push Not at h
      exact hc0 (funext h)
  · rintro ⟨c, hsum, a, ha⟩
    refine ⟨c, fun h => ha (congrFun h a), funext fun b => ?_⟩
    rw [hGc, hsum, dotProduct_zero, map_zero, Pi.zero_apply]

end Matrix
