/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.Generic.NullSets
import LatticeDFT.HK.SquareWall

/-!
# Two fermions on the square: (H*) by exact computation

Lean evaluates the six Krylov determinants at `v = (−3, −3, −2, 0)` (values 64, −432, −448, −448,
−432, 64), which proves (H*) and hence `square_generic_hk_ae`: the Hohenberg–Kohn theorem holds for
Lebesgue-almost every potential.
-/

namespace LatticeDFT

section

open Matrix MvPolynomial

def vsq : Fin 4 → ℝ := ![-3, -3, -2, 0]
def Hsq1 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![-2, -1, 0, 0, 1, 0; -1, -1, -1, -1, 0, 1; 0, -1, 1, 0, -1, 0; 0, -1, 0, -1, -1, 0; 1, 0, -1,
    -1, 1, -1; 0, 1, 0, 0, -1, 2]
lemma hamN_vsq : hamN H0sq occ4 vsq = Hsq1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp
      [hamN, H0sq, occ4, vsq, Hsq1, Fin.sum_univ_succ] <;> norm_num
def Hsq2 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![6, 3, 0, 0, -1, -2; 3, 5, 0, 2, 0, 1; 0, 0, 3, 2, -2, 0; 0, 2, 2, 3, 0, 0; -1, 0, -2, 0, 5,
    -3; -2, 1, 0, 0, -3, 6]
lemma Hsq_pow2 : Hsq1 ^ 2 = Hsq2 := by
  rw [pow_succ, pow_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp
      [Hsq1, Hsq2, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
def Hsq3 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![-16, -11, -2, -2, 7, 0; -11, -9, -5, -7, 0, 7; -2, -5, 5, 0, -7, 2; -2, -7, 0, -5, -5, 2; 7,
    0, -7, -5, 9, -11; 0, 7, 2, 2, -11, 16]
lemma Hsq_pow3 : Hsq1 ^ 3 = Hsq3 := by
  rw [pow_succ, Hsq_pow2]
  ext i j; fin_cases i <;> fin_cases j <;> simp
      [Hsq1, Hsq3, Hsq2, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
def Hsq4 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![50, 31, 2, 6, -5, -18; 31, 39, 4, 16, -6, 5; 2, 4, 17, 12, -16, 6; 6, 16, 12, 17, -4, 2; -5,
    -6, -16, -4, 39, -31; -18, 5, 6, 2, -31, 50]
lemma Hsq_pow4 : Hsq1 ^ 4 = Hsq4 := by
  rw [pow_succ, Hsq_pow3]
  ext i j; fin_cases i <;> fin_cases j <;> simp
      [Hsq1, Hsq4, Hsq3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
def Hsq5 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![-136, -107, -24, -32, 55, 0; -107, -85, -29, -49, 0, 55; -24, -29, 29, 0, -49, 32; -32, -49,
    0, -29, -29, 24; 55, 0, -49, -29, 85, -107; 0, 55, 32, 24, -107, 136]
lemma Hsq_pow5 : Hsq1 ^ 5 = Hsq5 := by
  rw [pow_succ, Hsq_pow4]
  ext i j; fin_cases i <;> fin_cases j <;> simp
      [Hsq1, Hsq5, Hsq4, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
lemma pow_cases (k : ℕ) (hk : k < 6) : Hsq1 ^ k = ![1, Hsq1, Hsq2, Hsq3, Hsq4, Hsq5] ⟨k, hk⟩ := by
  interval_cases k
  · simp
  · simp
  all_goals simp [Hsq_pow2, Hsq_pow3, Hsq_pow4, Hsq_pow5]
def Ksq0 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![1, -2, 6, -16, 50, -136; 0, -1, 3, -11, 31, -107; 0, 0, 0, -2, 2, -24; 0, 0, 0, -2, 6,
    -32; 0, 1, -1, 7, -5, 55; 0, 0, -2, 0, -18, 0]
lemma kry_sq0 : kry Hsq1 0 Fin.val = Ksq0 := by
  ext i j
  rw [kry, pow_cases j.val j.isLt]
  fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq2, Hsq3, Hsq4, Hsq5, Ksq0]
lemma det_Ksq0 : Ksq0.det = 64 := by
  simp [Ksq0, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num
def Ksq1 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![0, -1, 3, -11, 31, -107; 1, -1, 5, -9, 39, -85; 0, -1, 0, -5, 4, -29; 0, -1, 2, -7, 16,
    -49; 0, 0, 0, 0, -6, 0; 0, 1, 1, 7, 5, 55]
lemma kry_sq1 : kry Hsq1 1 Fin.val = Ksq1 := by
  ext i j
  rw [kry, pow_cases j.val j.isLt]
  fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq2, Hsq3, Hsq4, Hsq5, Ksq1]
lemma det_Ksq1 : Ksq1.det = -432 := by
  simp [Ksq1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num
def Ksq2 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![0, 0, 0, -2, 2, -24; 0, -1, 0, -5, 4, -29; 1, 1, 3, 5, 17, 29; 0, 0, 2, 0, 12, 0; 0, -1, -2,
    -7, -16, -49; 0, 0, 0, 2, 6, 32]
lemma kry_sq2 : kry Hsq1 2 Fin.val = Ksq2 := by
  ext i j
  rw [kry, pow_cases j.val j.isLt]
  fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq2, Hsq3, Hsq4, Hsq5, Ksq2]
lemma det_Ksq2 : Ksq2.det = -448 := by
  simp [Ksq2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num
def Ksq3 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![0, 0, 0, -2, 6, -32; 0, -1, 2, -7, 16, -49; 0, 0, 2, 0, 12, 0; 1, -1, 3, -5, 17, -29; 0, -1,
    0, -5, -4, -29; 0, 0, 0, 2, 2, 24]
lemma kry_sq3 : kry Hsq1 3 Fin.val = Ksq3 := by
  ext i j
  rw [kry, pow_cases j.val j.isLt]
  fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq2, Hsq3, Hsq4, Hsq5, Ksq3]
lemma det_Ksq3 : Ksq3.det = -448 := by
  simp [Ksq3, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num
def Ksq4 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![0, 1, -1, 7, -5, 55; 0, 0, 0, 0, -6, 0; 0, -1, -2, -7, -16, -49; 0, -1, 0, -5, -4, -29; 1, 1,
    5, 9, 39, 85; 0, -1, -3, -11, -31, -107]
lemma kry_sq4 : kry Hsq1 4 Fin.val = Ksq4 := by
  ext i j
  rw [kry, pow_cases j.val j.isLt]
  fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq2, Hsq3, Hsq4, Hsq5, Ksq4]
lemma det_Ksq4 : Ksq4.det = -432 := by
  simp [Ksq4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num
def Ksq5 : Matrix (Fin 6) (Fin 6) ℝ :=
    !![0, 0, -2, 0, -18, 0; 0, 1, 1, 7, 5, 55; 0, 0, 0, 2, 6, 32; 0, 0, 0, 2, 2, 24; 0, -1, -3, -11,
    -31, -107; 1, 2, 6, 16, 50, 136]
lemma kry_sq5 : kry Hsq1 5 Fin.val = Ksq5 := by
  ext i j
  rw [kry, pow_cases j.val j.isLt]
  fin_cases i <;> fin_cases j <;> simp [Hsq1, Hsq2, Hsq3, Hsq4, Hsq5, Ksq5]
lemma det_Ksq5 : Ksq5.det = 64 := by
  simp [Ksq5, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

lemma rigid_occ4 : Rigid occ4 := by
  intro w κ h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [occ4, Fin.sum_univ_succ] at h0 h1 h2 h3
  exact ⟨w 0, fun i => by fin_cases i <;> simp <;> linarith⟩

lemma hstar_sq : ∀ c, krylovPoly H0sq occ4 c Fin.val ≠ 0 := by
  intro c h
  have e := eval_krylovPoly H0sq occ4 c Fin.val vsq
  rw [h, map_zero, hamN_vsq] at e
  fin_cases c
  · exact absurd (show (kry Hsq1 0 Fin.val).det = 0 from e.symm)
      (by rw [kry_sq0, det_Ksq0]; norm_num)
  · exact absurd (show (kry Hsq1 1 Fin.val).det = 0 from e.symm)
      (by rw [kry_sq1, det_Ksq1]; norm_num)
  · exact absurd (show (kry Hsq1 2 Fin.val).det = 0 from e.symm)
      (by rw [kry_sq2, det_Ksq2]; norm_num)
  · exact absurd (show (kry Hsq1 3 Fin.val).det = 0 from e.symm)
      (by rw [kry_sq3, det_Ksq3]; norm_num)
  · exact absurd (show (kry Hsq1 4 Fin.val).det = 0 from e.symm)
      (by rw [kry_sq4, det_Ksq4]; norm_num)
  · exact absurd (show (kry Hsq1 5 Fin.val).det = 0 from e.symm)
      (by rw [kry_sq5, det_Ksq5]; norm_num)

/-- **Generic HK for two fermions on the square, fully formal.** The potentials at which the ground
state is shared with a genuinely different potential lie in a closed set with empty interior. -/
theorem square_generic_hk :
    ∃ Z : Set (Fin 4 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ {v | NonUV H0sq occ4 v} ⊆ Z :=
  generic_hk H0sq_isSymm rigid_occ4 Fin.val hstar_sq

end

section
open MeasureTheory

/-- **Two fermions on the square: HK holds for Lebesgue-almost every potential** (fully formal). -/
theorem square_generic_hk_ae :
    ∃ Z : Set (Fin 4 → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
        {v | NonUV H0sq occ4 v} ⊆ Z :=
  generic_hk_ae H0sq_isSymm rigid_occ4 Fin.val hstar_sq

end

end LatticeDFT
