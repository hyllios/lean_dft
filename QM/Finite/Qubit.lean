/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QuantumInfo.States.Pure.Qubit
import QM.Finite.States

/-!
# A qubit

The sanity theorem for the bridge between Physlib and QuantumInfo (`QM.Finite.States`). The Pauli
matrices `σ_x, σ_y, σ_z` are QuantumInfo's gates `Qubit.X`, `Qubit.Y`, `Qubit.Z` seen as Hermitian
matrices. The Bloch vector of a density matrix is `r_a = tr ρσ_a`.

## Main results

* `bloch_decomp`: `ρ = ½ (1 + r_x σ_x + r_y σ_y + r_z σ_z)`.
* `bloch_sq_eq`: `|r|² = 2 tr ρ² - 1`, hence `bloch_sq_le_one` (`|r| ≤ 1`) and `bloch_sq_eq_one_iff`
  (`|r| = 1` if and only if `ρ` is pure).
* `pauli_uncertainty`: Physlib's Robertson inequality gives `Δσ_x Δσ_y ≥ |⟨σ_z⟩|` in a pure state.
-/

namespace QM

open Matrix Complex ComplexConjugate

/-- The Pauli matrix `σ_x`. -/
def pauliX : HermitianMat (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/-- The Pauli matrix `σ_y`. -/
def pauliY : HermitianMat (Fin 2) ℂ :=
  ⟨!![0, -I; I, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/-- The Pauli matrix `σ_z`. -/
def pauliZ : HermitianMat (Fin 2) ℂ :=
  ⟨!![1, 0; 0, -1], by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

lemma pauliX_eq : pauliX.mat = !![0, 1; 1, 0] := rfl
lemma pauliY_eq : pauliY.mat = !![0, -I; I, 0] := rfl
lemma pauliZ_eq : pauliZ.mat = !![1, 0; 0, -1] := rfl

lemma pauliX_mat : pauliX.mat = (Qubit.X : Matrix (Fin 2) (Fin 2) ℂ) := rfl
lemma pauliY_mat : pauliY.mat = (Qubit.Y : Matrix (Fin 2) (Fin 2) ℂ) := rfl
lemma pauliZ_mat : pauliZ.mat = (Qubit.Z : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- The Bloch vector `r_a = tr ρσ_a` of a qubit density matrix. -/
noncomputable def bloch (ρ : MState (Fin 2)) : Fin 3 → ℝ :=
  ![ρ.exp_val pauliX, ρ.exp_val pauliY, ρ.exp_val pauliZ]

/-- The entries of a qubit density matrix: `ρ₁₀ = conj ρ₀₁`, real diagonal, trace one. -/
lemma qubit_entries (ρ : MState (Fin 2)) :
    ρ.m 1 0 = conj (ρ.m 0 1) ∧ (ρ.m 0 0).im = 0 ∧ (ρ.m 1 1).im = 0 ∧
      (ρ.m 0 0).re + (ρ.m 1 1).re = 1 := by
  have hH := ρ.Hermitian
  have h10 : ρ.m 1 0 = conj (ρ.m 0 1) := (hH.apply 1 0).symm
  have hd : ∀ i, (ρ.m i i).im = 0 := fun i => by
    have := hH.apply i i
    rw [RCLike.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have htr := ρ.tr'
  rw [Matrix.trace, Fin.sum_univ_two] at htr
  have := congrArg Complex.re htr
  simp only [Matrix.diag, Complex.add_re, Complex.one_re] at this
  exact ⟨h10, hd 0, hd 1, this⟩

lemma exp_val_eq_re_trace (ρ : MState (Fin 2)) (T : HermitianMat (Fin 2) ℂ) :
    ρ.exp_val T = (ρ.m * T.mat).trace.re := by
  rw [MState.exp_val, HermitianMat.inner_eq_re_trace, MState.mat_M]; rfl

lemma bloch_x (ρ : MState (Fin 2)) : bloch ρ 0 = 2 * (ρ.m 0 1).re := by
  obtain ⟨h10, -, -, -⟩ := qubit_entries ρ
  rw [show bloch ρ 0 = ρ.exp_val pauliX from rfl, exp_val_eq_re_trace, pauliX_eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, h10]
  ring

lemma bloch_y (ρ : MState (Fin 2)) : bloch ρ 1 = -2 * (ρ.m 0 1).im := by
  obtain ⟨h10, -, -, -⟩ := qubit_entries ρ
  rw [show bloch ρ 1 = ρ.exp_val pauliY from rfl, exp_val_eq_re_trace, pauliY_eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, h10]
  ring

lemma bloch_z (ρ : MState (Fin 2)) : bloch ρ 2 = (ρ.m 0 0).re - (ρ.m 1 1).re := by
  rw [show bloch ρ 2 = ρ.exp_val pauliZ from rfl, exp_val_eq_re_trace, pauliZ_eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]
  ring

/-- **The Bloch decomposition** `ρ = ½ (1 + r_x σ_x + r_y σ_y + r_z σ_z)`. -/
theorem bloch_decomp (ρ : MState (Fin 2)) :
    ρ.m = (1 / 2 : ℂ) • (1 + (bloch ρ 0 : ℂ) • pauliX.mat + (bloch ρ 1 : ℂ) • pauliY.mat +
      (bloch ρ 2 : ℂ) • pauliZ.mat) := by
  obtain ⟨h10, h0, h1, htr⟩ := qubit_entries ρ
  rw [bloch_x, bloch_y, bloch_z, pauliX_eq, pauliY_eq, pauliZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [h10, h0, h1] <;> linarith

/-- `|r|² = 2 tr ρ² - 1`. -/
theorem bloch_sq_eq (ρ : MState (Fin 2)) :
    ∑ a, bloch ρ a ^ 2 = 2 * (ρ.purity : ℝ) - 1 := by
  obtain ⟨h10, h0, h1, htr⟩ := qubit_entries ρ
  rw [MState.purity, MState.val_inner, HermitianMat.inner_eq_re_trace, MState.mat_M,
    Fin.sum_univ_three, bloch_x, bloch_y, bloch_z]
  simp only [RCLike.re_to_complex, Matrix.trace, Fin.sum_univ_two, Matrix.diag, Matrix.mul_apply,
    h10]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, h0, h1]
  have he : (ρ.m 1 1).re = 1 - (ρ.m 0 0).re := by linarith
  rw [he]
  ring

lemma purity_le_one (ρ : MState (Fin 2)) : (ρ.purity : ℝ) ≤ 1 := ρ.purity.2.2

/-- **The Bloch vector lies in the unit ball**: `|r| ≤ 1`. -/
theorem bloch_sq_le_one (ρ : MState (Fin 2)) : ∑ a, bloch ρ a ^ 2 ≤ 1 := by
  rw [bloch_sq_eq]; linarith [purity_le_one ρ]

/-- **Pure states are the Bloch sphere**: `|r| = 1` if and only if `ρ` is pure. -/
theorem bloch_sq_eq_one_iff (ρ : MState (Fin 2)) :
    ∑ a, bloch ρ a ^ 2 = 1 ↔ ∃ ψ, ρ = MState.pure ψ := by
  rw [bloch_sq_eq, MState.pure_iff_purity_one]
  constructor
  · intro h
    apply Subtype.ext
    change (ρ.purity : ℝ) = 1
    linarith
  · intro h
    rw [h]
    change 2 * (1 : ℝ) - 1 = 1
    norm_num

/-! ### The uncertainty relation -/

/-- `[σ_x, σ_y] = 2i σ_z` on vectors. -/
lemma pauli_comm (v : EuclideanSpace ℂ (Fin 2)) :
    Matrix.toEuclideanLin pauliX.mat (Matrix.toEuclideanLin pauliY.mat v) -
      Matrix.toEuclideanLin pauliY.mat (Matrix.toEuclideanLin pauliX.mat v) =
      (2 * I) • Matrix.toEuclideanLin pauliZ.mat v := by
  ext i
  fin_cases i <;>
    simp [pauliX_eq, pauliY_eq, pauliZ_eq, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_two] <;> ring

/-- **Uncertainty for the Pauli matrices**: in every pure state,
`Δσ_x Δσ_y ≥ |⟨σ_z⟩|`, from Physlib's Robertson inequality and `[σ_x, σ_y] = 2i σ_z`. -/
theorem pauli_uncertainty (ψ : Ket (Fin 2)) :
    |LinearPMap.expectedValue (obs pauliZ) (ketDom pauliZ ψ)| ≤
      LinearPMap.standardDeviation (obs pauliX) (ketDom pauliX ψ) *
        LinearPMap.standardDeviation (obs pauliY) (ketDom pauliY ψ) := by
  set c := 2 * LinearPMap.expectedValue (obs pauliZ) (ketDom pauliZ ψ)
  have h_raw : LinearPMap.rawCommutatorExpectation (obs pauliX) (obs pauliY) (ketDom pauliX ψ)
      Submodule.mem_top Submodule.mem_top Submodule.mem_top = I * c := by
    change inner ℂ (ketVec ψ) (Matrix.toEuclideanLin pauliX.mat
      (Matrix.toEuclideanLin pauliY.mat (ketVec ψ)) - Matrix.toEuclideanLin pauliY.mat
        (Matrix.toEuclideanLin pauliX.mat (ketVec ψ))) = _
    rw [pauli_comm, inner_smul_right]
    have hz := LinearPMap.expectedValue_eq_inner (obs pauliZ) (obs_isSymmetric pauliZ)
      (ketDom pauliZ ψ)
    change inner ℂ (ketVec ψ) (Matrix.toEuclideanLin pauliZ.mat (ketVec ψ)) = _ at hz
    rw [hz]
    simp only [c]
    push_cast
    ring
  have h := LinearPMap.state_uncertainty_of_raw_commutator (obs pauliX) (obs pauliY)
    (obs_isSymmetric pauliX) (obs_isSymmetric pauliY) (ketDom pauliX ψ) Submodule.mem_top
    (norm_ketVec ψ) Submodule.mem_top Submodule.mem_top h_raw
  have hc : |c| / 2 = |LinearPMap.expectedValue (obs pauliZ) (ketDom pauliZ ψ)| := by
    simp only [c, abs_mul, abs_two]; ring
  rw [← hc]
  exact h

end QM
