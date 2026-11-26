/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import QM.ManyBody.Number

/-!
# Reduced density matrices on the Fock space

For a vector `Ψ` of the Fock space, the one-body reduced density matrix is
`γ_ij = ⟨Ψ, c_i† c_j Ψ⟩` (`rdm1`) and the two-body reduced density matrix is
`D_{ij,kl} = ⟨Ψ, c_i† c_j† c_l c_k Ψ⟩` (`rdm2`); the density is `ρ_i = γ_ii`. The convention
`γ_ij = ⟨c_i† c_j⟩` is the one of the lattice code (`DFT.Lattice.RDMFT.rdm_eq_inner`).

An `N`-particle state is a unit vector with `N̂ Ψ = N Ψ` (`IsNState`). An `N`-particle ensemble is a
finite family of `N`-particle states with convex weights (`IsNEnsemble`); its reduced density
matrices are the weighted sums (`rdm1Ens`, `rdm2Ens`).

## Main results

* `quad_rdm1`: `Σ_ij x̄_i γ_ij x_j = ⟨c(x) Ψ, c(x) Ψ⟩` with `c(x) = Σ_j x_j c_j`.
* `quad_one_sub_rdm1`: `Σ_ij x̄_i (δ_ij - γ_ij) x_j = ⟨c(x)† Ψ, c(x)† Ψ⟩` for a unit vector.
* `rdm1_isHermitian`, `rdm1_posSemidef`, `one_sub_rdm1_posSemidef`, `trace_rdm1`: **the necessary
  conditions** `γ = γ†`, `0 ≤ γ ≤ 1`, `tr γ = N` for an `N`-particle state, and the same for
  ensembles (`rdm1Ens_isHermitian`, `rdm1Ens_posSemidef`, `one_sub_rdm1Ens_posSemidef`,
  `trace_rdm1Ens`).
-/

namespace QM.ManyBody

open Matrix Finset
open scoped ComplexOrder

variable {M : ℕ}

/-! ### Definitions -/

/-- The one-body reduced density matrix `γ_ij = ⟨Ψ, c_i† c_j Ψ⟩`. -/
noncomputable def rdm1 (Ψ : Fock M) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => inner ℂ Ψ (creOp i (annOp j Ψ))

/-- The two-body reduced density matrix `D_{ij,kl} = ⟨Ψ, c_i† c_j† c_l c_k Ψ⟩`, as a matrix indexed
by pairs of modes. -/
noncomputable def rdm2 (Ψ : Fock M) : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ :=
  fun p q => inner ℂ Ψ (creOp p.1 (creOp p.2 (annOp q.2 (annOp q.1 Ψ))))

/-- An `N`-particle state: a unit vector with `N̂ Ψ = N Ψ`. -/
def IsNState (N : ℕ) (Ψ : Fock M) : Prop := ‖Ψ‖ = 1 ∧ numTotOp Ψ = (N : ℂ) • Ψ

/-- An `N`-particle ensemble: `N`-particle states `Ψ k` with weights `w k ≥ 0` summing to `1`. -/
def IsNEnsemble {ι : Type*} [Fintype ι] (N : ℕ) (w : ι → ℝ) (Ψ : ι → Fock M) : Prop :=
  (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧ ∀ k, IsNState N (Ψ k)

/-- The one-body reduced density matrix of an ensemble. -/
noncomputable def rdm1Ens {ι : Type*} [Fintype ι] (w : ι → ℝ) (Ψ : ι → Fock M) :
    Matrix (Fin M) (Fin M) ℂ :=
  ∑ k, (w k : ℂ) • rdm1 (Ψ k)

/-- The two-body reduced density matrix of an ensemble. -/
noncomputable def rdm2Ens {ι : Type*} [Fintype ι] (w : ι → ℝ) (Ψ : ι → Fock M) :
    Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ :=
  ∑ k, (w k : ℂ) • rdm2 (Ψ k)

/-! ### Adjoints -/

lemma creOp_eq_adjoint (i : Fin M) : creOp i = ContinuousLinearMap.adjoint (annOp i) := by
  rw [annOp_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

lemma inner_creOp (i : Fin M) (Φ Ψ : Fock M) :
    inner ℂ Φ (creOp i Ψ) = inner ℂ (annOp i Φ) Ψ := by
  rw [creOp_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

lemma inner_annOp (i : Fin M) (Φ Ψ : Fock M) :
    inner ℂ Φ (annOp i Ψ) = inner ℂ (creOp i Φ) Ψ := by
  rw [annOp_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- The total number operator is `Σ_i c_i† c_i` on the Hilbert space. -/
lemma numTotOp_eq_sum : (numTotOp : Fock M →L[ℂ] Fock M) = ∑ i, creOp i * annOp i := by
  unfold numTotOp numTot num creOp annOp
  rw [map_sum]
  simp_rw [map_mul]

/-! ### The one-body matrix of a state -/

/-- `c(x) = Σ_j x_j c_j`. -/
noncomputable def annX (x : Fin M → ℂ) : Fock M →L[ℂ] Fock M := ∑ j, x j • annOp j

/-- `c(x)† = Σ_i x̄_i c_i†`. -/
noncomputable def creX (x : Fin M → ℂ) : Fock M →L[ℂ] Fock M := ∑ i, star (x i) • creOp i

lemma inner_annX_left (x : Fin M → ℂ) (Φ Ψ : Fock M) :
    inner ℂ (annX x Φ) Ψ = ∑ i, star (x i) * inner ℂ Φ (creOp i Ψ) := by
  simp [annX, sum_inner, inner_smul_left, inner_creOp]

lemma inner_creX_left (x : Fin M → ℂ) (Φ Ψ : Fock M) :
    inner ℂ (creX x Φ) Ψ = ∑ i, x i * inner ℂ Φ (annOp i Ψ) := by
  simp [creX, sum_inner, inner_smul_left, inner_annOp]

/-- **`Σ_ij x̄_i γ_ij x_j = ‖c(x) Ψ‖²`.** -/
theorem quad_rdm1 (Ψ : Fock M) (x : Fin M → ℂ) :
    star x ⬝ᵥ (rdm1 Ψ *ᵥ x) = inner ℂ (annX x Ψ) (annX x Ψ) := by
  rw [inner_annX_left]
  simp only [dotProduct, mulVec, Pi.star_apply, rdm1, annX, _root_.sum_apply,
    _root_.smul_apply, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **`Σ_ij x̄_i (δ_ij - γ_ij) x_j = ‖c(x)† Ψ‖²`** for a unit vector, by `{c(x), c(x)†} = ‖x‖²`. -/
theorem quad_one_sub_rdm1 {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) (x : Fin M → ℂ) :
    star x ⬝ᵥ ((1 - rdm1 Ψ) *ᵥ x) = inner ℂ (creX x Ψ) (creX x Ψ) := by
  have hcar : ∀ i j : Fin M, (if i = j then (1 : ℂ) else 0) - rdm1 Ψ i j =
      inner ℂ Ψ (annOp j (creOp i Ψ)) := by
    intro i j
    have h := congrArg (fun A : Fock M →L[ℂ] Fock M => inner ℂ Ψ (A Ψ)) (annOp_mul_creOp_add j i)
    simp only [_root_.add_apply, _root_.mul_apply_eq_comp,
      inner_add_right] at h
    rw [rdm1]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, _root_.one_apply_eq_self, inner_self_eq_norm_sq_to_K, hΨ] at h ⊢
      push_cast at h
      linear_combination -h
    · rw [ite_eq_right hij]
      rw [ite_eq_right (Ne.symm hij), _root_.zero_apply, inner_zero_right] at h
      linear_combination -h
  rw [inner_creX_left]
  simp only [dotProduct, mulVec, Pi.star_apply, Matrix.sub_apply, Matrix.one_apply, hcar, creX,
    _root_.sum_apply, _root_.smul_apply, map_sum, map_smul, inner_sum,
    inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `γ` is Hermitian. -/
theorem rdm1_isHermitian (Ψ : Fock M) : (rdm1 Ψ).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, rdm1]
  rw [inner_creOp, inner_annOp, ← inner_conj_symm, inner_creOp, inner_annOp]
  simp

/-- **`γ ≥ 0`.** -/
theorem rdm1_posSemidef (Ψ : Fock M) : (rdm1 Ψ).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨rdm1_isHermitian Ψ, fun x => ?_⟩
  rw [quad_rdm1, inner_self_eq_norm_sq_to_K]
  simp

/-- **`γ ≤ 1`** for a unit vector. -/
theorem one_sub_rdm1_posSemidef {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) : (1 - rdm1 Ψ).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨isHermitian_one.sub (rdm1_isHermitian Ψ), fun x => ?_⟩
  rw [quad_one_sub_rdm1 hΨ, inner_self_eq_norm_sq_to_K]
  simp

/-- **`tr γ = N`** for an `N`-particle state. -/
theorem trace_rdm1 {N : ℕ} {Ψ : Fock M} (hΨ : IsNState N Ψ) : (rdm1 Ψ).trace = N := by
  have h : (rdm1 Ψ).trace = inner ℂ Ψ (numTotOp Ψ) := by
    rw [numTotOp_eq_sum, Matrix.trace]
    simp [rdm1, inner_sum]
  rw [h, hΨ.2, inner_smul_right, inner_self_eq_norm_sq_to_K, hΨ.1]
  simp

/-! ### Ensembles -/

/-- `γ` of an ensemble is Hermitian. -/
theorem rdm1Ens_isHermitian {ι : Type*} [Fintype ι] (w : ι → ℝ) (Ψ : ι → Fock M) :
    (rdm1Ens w Ψ).IsHermitian :=
  isSelfAdjoint_sum _ fun k _ =>
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (rdm1_isHermitian (Ψ k))

/-- **`γ ≥ 0`** for an ensemble. -/
theorem rdm1Ens_posSemidef {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k)
    (Ψ : ι → Fock M) : (rdm1Ens w Ψ).PosSemidef :=
  posSemidef_sum _ fun k _ => (rdm1_posSemidef (Ψ k)).smul (by exact_mod_cast hw k)

/-- **`γ ≤ 1`** for an `N`-particle ensemble. -/
theorem one_sub_rdm1Ens_posSemidef {ι : Type*} [Fintype ι] {N : ℕ} {w : ι → ℝ} {Ψ : ι → Fock M}
    (h : IsNEnsemble N w Ψ) : (1 - rdm1Ens w Ψ).PosSemidef := by
  have e : 1 - rdm1Ens w Ψ = ∑ k, (w k : ℂ) • (1 - rdm1 (Ψ k)) := by
    simp only [rdm1Ens, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [← Complex.ofReal_sum, h.2.1, Complex.ofReal_one, one_smul]
  rw [e]
  exact posSemidef_sum _ fun k _ =>
    (one_sub_rdm1_posSemidef (h.2.2 k).1).smul (by exact_mod_cast h.1 k)

/-- **`tr γ = N`** for an `N`-particle ensemble. -/
theorem trace_rdm1Ens {ι : Type*} [Fintype ι] {N : ℕ} {w : ι → ℝ} {Ψ : ι → Fock M}
    (h : IsNEnsemble N w Ψ) : (rdm1Ens w Ψ).trace = N := by
  simp only [rdm1Ens, Matrix.trace_sum, Matrix.trace_smul, trace_rdm1 (h.2.2 _), smul_eq_mul,
    ← Finset.sum_mul]
  rw [← Complex.ofReal_sum, h.2.1, Complex.ofReal_one, one_mul]

end QM.ManyBody
