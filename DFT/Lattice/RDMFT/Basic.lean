/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Fermions.SecondQuantization
import DFT.Lattice.HK.Gap

/-!
# Density-matrix functional theory on a lattice

In reduced-density-matrix functional theory (RDMFT) the variable conjugate to the one-body reduced
density matrix `γ` is a full one-body operator `h`. It holds the hoppings as well as the on-site
potential. For `N` spinless fermions on `M` sites the Hamiltonian is

`H(h) = Γ(h) + W`,

where `h` is a real symmetric `M × M` matrix, `Γ(h)` its second quantisation and `W` a fixed
many-body operator (the interaction). The lattice-DFT Hamiltonian is the special case
`h = -t A + diag v` (`hamN_H0F_eq_hamR`).

The energy is linear in `γ`, `⟨ψ, Γ(h) ψ⟩ = Σ_ij h_ij γ_ij` (`qf_gamma`). So Gilbert's version of
the first Hohenberg–Kohn step goes through verbatim. Two Hamiltonians with ground states of the same
`γ` share their ground states (`gilbert_weak`).

* `gammaL`: `Γ` as a linear map.
* `rdm ψ`: the one-body reduced density matrix, `γ_ij = ⟨ψ, Γ(E_ij) ψ⟩`.
* `qf_gamma`: `⟨ψ, Γ(h) ψ⟩ = Σ_ij h_ij γ_ij`.
* `hamR W h`: the RDMFT Hamiltonian `Γ(h) + W`.
* `gilbert_weak`: **Gilbert's theorem**, weak form.
-/

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-- The second quantisation `Γ` as a linear map. -/
def gammaL : Matrix (Fin M) (Fin M) ℝ →ₗ[ℝ] Matrix (Conf M N) (Conf M N) ℝ where
  toFun h := Γ h
  map_add' := gamma_add
  map_smul' := gamma_smul

lemma gamma_sub (a b : Matrix (Fin M) (Fin M) ℝ) :
    (Γ (a - b) : Matrix (Conf M N) (Conf M N) ℝ) = Γ a - Γ b :=
  map_sub (gammaL (N := N)) a b

/-- A linear functional on matrices is determined by its values on the matrix units. -/
lemma linear_eq_sum_single (f : Matrix (Fin M) (Fin M) ℝ →ₗ[ℝ] ℝ) (h : Matrix (Fin M) (Fin M) ℝ) :
    f h = ∑ i, ∑ j, h i j * f (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (h i j) = h i j • Matrix.single i j (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

variable {C : Type*} [Fintype C]

/-- The quadratic form `A ↦ ⟨ψ, A ψ⟩` as a linear functional on matrices. -/
def qfL (ψ : C → ℝ) : Matrix C C ℝ →ₗ[ℝ] ℝ where
  toFun A := qf A ψ
  map_add' A B := by simp [qf, Matrix.add_mulVec, dotProduct_add]
  map_smul' a A := by simp [qf, Matrix.smul_mulVec, dotProduct_smul]

lemma qf_add (A B : Matrix C C ℝ) (ψ : C → ℝ) : qf (A + B) ψ = qf A ψ + qf B ψ :=
  map_add (qfL ψ) A B

lemma qf_add_smul (A B : Matrix C C ℝ) (ε : ℝ) (ψ : C → ℝ) :
    qf (A + ε • B) ψ = qf A ψ + ε * qf B ψ := by
  rw [qf_add]; exact congrArg _ (map_smul (qfL ψ) ε B)

/-- The one-body reduced density matrix `γ_ij = ⟨ψ, Γ(E_ij) ψ⟩` (unnormalised). -/
def rdm (ψ : Conf M N → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => qf (Γ (Matrix.single i j 1)) ψ

/-- **The one-body energy is linear in `γ`**: `⟨ψ, Γ(h) ψ⟩ = Σ_ij h_ij γ_ij`. -/
theorem qf_gamma (h : Matrix (Fin M) (Fin M) ℝ) (ψ : Conf M N → ℝ) :
    qf (Γ h) ψ = ∑ i, ∑ j, h i j * rdm ψ i j :=
  linear_eq_sum_single ((qfL ψ).comp gammaL) h

/-- The RDMFT Hamiltonian `H(h) = Γ(h) + W`. -/
def hamR (W : Matrix (Conf M N) (Conf M N) ℝ) (h : Matrix (Fin M) (Fin M) ℝ) :
    Matrix (Conf M N) (Conf M N) ℝ :=
  Γ h + W

lemma qf_hamR (W : Matrix (Conf M N) (Conf M N) ℝ) (h : Matrix (Fin M) (Fin M) ℝ)
    (φ : Conf M N → ℝ) : qf (hamR W h) φ = (∑ i, ∑ j, h i j * rdm φ i j) + qf W φ := by
  rw [hamR, qf_add, qf_gamma]

lemma hamR_isSymm {W : Matrix (Conf M N) (Conf M N) ℝ} (hW : W.IsSymm)
    {h : Matrix (Fin M) (Fin M) ℝ} (hh : h.IsSymm) : (hamR W h).IsSymm :=
  (gamma_isSymm hh).add hW

lemma hamR_add_smul (W : Matrix (Conf M N) (Conf M N) ℝ) (h d : Matrix (Fin M) (Fin M) ℝ)
    (ε : ℝ) : hamR W (h + ε • d) = hamR W h + ε • Γ d := by
  rw [hamR, hamR, gamma_add, gamma_smul]; abel

/-- The lattice-DFT Hamiltonian is the RDMFT Hamiltonian of `h = -t A + diag v`. -/
theorem hamN_H0F_eq_hamR (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : ℝ)
    (Vint : Conf M N → ℝ) (v : Fin M → ℝ) :
    hamN (H0F G t Vint) occF v = hamR (Matrix.diagonal Vint) (-t • G.adjMatrix ℝ + diagonal v) :=
  hamN_H0F G t Vint v

/-- **Gilbert's theorem** (weak form). If ground states of `H(h)` and `H(h')` have the same
one-body reduced density matrix, each is a ground state of the other Hamiltonian. -/
theorem gilbert_weak {W : Matrix (Conf M N) (Conf M N) ℝ} {h h' : Matrix (Fin M) (Fin M) ℝ}
    {ψ ψ' : Conf M N → ℝ}
    (hψ : IsGroundState (hamR W h) ψ) (hψ' : IsGroundState (hamR W h') ψ')
    (hN : ψ ⬝ᵥ ψ = 1) (hN' : ψ' ⬝ᵥ ψ' = 1) (hd : rdm ψ = rdm ψ') :
    IsGroundState (hamR W h') ψ ∧ IsGroundState (hamR W h) ψ' := by
  have a := hψ.2 ψ'
  have b := hψ'.2 ψ
  rw [hN, hN', mul_one, mul_one] at a b
  rw [qf_hamR, qf_hamR, hd] at a b
  have hE : qf W ψ = qf W ψ' := by linarith
  have e1 : qf (hamR W h') ψ = qf (hamR W h') ψ' := by rw [qf_hamR, qf_hamR, hd, hE]
  have e2 : qf (hamR W h) ψ' = qf (hamR W h) ψ := by rw [qf_hamR, qf_hamR, hd, hE]
  refine ⟨⟨hψ.1, fun φ => ?_⟩, ⟨hψ'.1, fun φ => ?_⟩⟩
  · rw [e1, hN]; have := hψ'.2 φ; rwa [hN'] at this
  · rw [e2, hN']; have := hψ.2 φ; rwa [hN] at this

end

end DFT
