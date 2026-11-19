/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Generic.Eliminate
import DFT.Lattice.RDMFT.KohnSham
import DFT.Lattice.RDMFT.Counting

/-!
# Interacting ground states are generically not Slater determinants (conditional)

Fix an interaction `W` and let the one-body operator `h = symOf θ` range over all real symmetric
matrices. The `θ` at which the gapped ground state of `Γ(h) + W` has an idempotent one-body reduced
density matrix lie in a closed, nowhere dense, Lebesgue-null set, provided one elimination
polynomial is not identically zero (`generic_nonidem`). That proviso is the analogue of hypothesis
(H*) in the generic Hohenberg–Kohn theorem. It is discharged by a single parameter point at which
`Γ(h) + W` has an orthonormal eigenbasis with distinct eigenvalues whose vectors have nonzero
overlap with `u` and non-idempotent `γ` (`elimPoly_ne_zero_of_eigenbasis`).

Idempotency is detected by the polynomial `Σ_ij ((γ² - ‖ψ‖² γ)_ij)²` in the amplitudes
(`idemP`), which is homogeneous of degree 8 (`eval_idemP_smul`) and vanishes on normalised states
with `γ² = γ` (`eval_idemP_eq_zero_of_idem`). The abstract machinery is `generic_avoid`.

* `rdmP`, `normP`, `idemP` and their evaluations.
* `hamRP`, `evalMat_hamRP`: the family `θ ↦ Γ(symOf θ) + W` as a polynomial matrix.
* `generic_nonidem`: **generic non-idempotency, conditional on a nonzero elimination polynomial**.
-/

namespace DFT

section

open Matrix MvPolynomial

variable {M N : ℕ}

/-- `γ_ij` as a quadratic polynomial in the amplitudes. -/
noncomputable def rdmP (i j : Fin M) : MvPolynomial (Conf M N) ℝ :=
  ∑ s, ∑ s', C ((Γ (Matrix.single i j 1) : Matrix (Conf M N) (Conf M N) ℝ) s s') * X s * X s'

lemma eval_rdmP (i j : Fin M) (ψ : Conf M N → ℝ) : eval ψ (rdmP i j) = rdm ψ i j := by
  simp only [rdmP, rdm, qf, dotProduct, mulVec, map_sum, map_mul, eval_C, eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro s' _
  ring

/-- `‖ψ‖²` as a polynomial. -/
noncomputable def normP : MvPolynomial (Conf M N) ℝ := ∑ s, X s * X s

lemma eval_normP (ψ : Conf M N → ℝ) : eval ψ (normP (M := M) (N := N)) = ψ ⬝ᵥ ψ := by
  simp [normP, dotProduct]

/-- `Σ_ij ((γ² - ‖ψ‖² γ)_ij)²`. -/
noncomputable def idemP : MvPolynomial (Conf M N) ℝ :=
  ∑ i : Fin M, ∑ j : Fin M, ((∑ k, rdmP i k * rdmP k j) - normP * rdmP i j) ^ 2

lemma eval_idemP (ψ : Conf M N → ℝ) :
    eval ψ (idemP (M := M) (N := N)) =
      ∑ i, ∑ j, ((rdm ψ * rdm ψ) i j - (ψ ⬝ᵥ ψ) * rdm ψ i j) ^ 2 := by
  simp [idemP, eval_rdmP, eval_normP, Matrix.mul_apply]

lemma eval_idemP_eq_zero_of_idem {ψ : Conf M N → ℝ} (hN : ψ ⬝ᵥ ψ = 1)
    (h : rdm ψ * rdm ψ = rdm ψ) : eval ψ (idemP (M := M) (N := N)) = 0 := by
  rw [eval_idemP, h, hN]; simp

lemma eval_idemP_smul (a : ℝ) (ψ : Conf M N → ℝ) :
    eval (a • ψ) (idemP (M := M) (N := N)) = a ^ 8 * eval ψ idemP := by
  rw [eval_idemP, eval_idemP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rdm_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, dotProduct_smul, smul_dotProduct]
  ring

/-- The RDMFT Hamiltonian `Γ(symOf θ) + W` as a matrix of polynomials in `θ`. -/
noncomputable def hamRP (W : Matrix (Conf M N) (Conf M N) ℝ) :
    Matrix (Conf M N) (Conf M N) (MvPolynomial (Sym2 (Fin M)) ℝ) :=
  W.map C + ∑ e, (X e : MvPolynomial (Sym2 (Fin M)) ℝ) •
    (Γ (symOf (Pi.single e 1)) : Matrix (Conf M N) (Conf M N) ℝ).map C

lemma symOf_eq_sum (θ : Sym2 (Fin M) → ℝ) : symOf θ = ∑ e, θ e • symOf (Pi.single e 1) := by
  ext i j; simp [symOf, Matrix.sum_apply, Pi.single_apply]

lemma evalMat_hamRP (W : Matrix (Conf M N) (Conf M N) ℝ) (θ : Sym2 (Fin M) → ℝ) :
    evalMat (hamRP W) θ = hamR W (symOf θ) := by
  have hΓ : (Γ (symOf θ) : Matrix (Conf M N) (Conf M N) ℝ) =
      ∑ e, θ e • Γ (symOf (Pi.single e 1)) := by
    rw [symOf_eq_sum θ]
    change gammaL (∑ e, θ e • symOf (Pi.single e 1)) = _
    rw [map_sum]
    simp_rw [map_smul]
    rfl
  ext s s'
  simp [evalMat, hamRP, hamR, hΓ, Matrix.sum_apply, add_comm]

/-- **Interacting ground states are generically not Slater determinants** (conditional). If the
elimination polynomial of one vector `u` is nonzero, the one-body operators `h = symOf θ`
for which the gapped ground state of `Γ(h) + W` has idempotent `γ` lie in a closed, nowhere dense,
Lebesgue-null set. -/
theorem generic_nonidem {W : Matrix (Conf M N) (Conf M N) ℝ} (hW : W.IsSymm) {u : Conf M N → ℝ}
    (hR : elimPoly (hamRP W) idemP u ≠ 0) :
    ∃ Z : Set (Sym2 (Fin M) → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {θ | ∃ ψ : Conf M N → ℝ, IsGroundState (hamR W (symOf θ)) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧
        (∃ g : ℝ, 0 < g ∧ ∀ χ, ψ ⬝ᵥ χ = 0 →
          (qf (hamR W (symOf θ)) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamR W (symOf θ)) χ) ∧
        rdm ψ * rdm ψ = rdm ψ} ⊆ Z := by
  have hS : ∀ θ, (evalMat (hamRP W) θ).IsSymm := fun θ => by
    rw [evalMat_hamRP]; exact hamR_isSymm hW (symOf_isSymm θ)
  obtain ⟨Z, h1, h2, h3, h4⟩ := generic_avoid hS
    (fun a ψ h => by rw [eval_idemP_smul, h, mul_zero]) hR
  refine ⟨Z, h1, h2, h3, fun θ hθ => h4 ?_⟩
  obtain ⟨ψ, hψ, hN, hgap, hid⟩ := hθ
  change ∃ ψ : Conf M N → ℝ, _
  rw [evalMat_hamRP]
  exact ⟨ψ, hψ, hN, hgap, eval_idemP_eq_zero_of_idem hN hid⟩

end

end DFT
