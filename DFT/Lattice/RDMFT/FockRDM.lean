/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Fermions.FockBridge
import DFT.Lattice.RDMFT.Basic

/-!
# The lattice one-body reduced density matrix is `⟨Ψ, c_i† c_j Ψ⟩`

The lattice RDMFT code defines the one-body reduced density matrix of an `N`-particle state `ψ`
through the second-quantized matrix units, `γ_ij = ⟨ψ, Γ(E_ij) ψ⟩` (`DFT.rdm`). Through the bridge to
the Fock space (`DFT.Lattice.Fermions.oneBody_apply_conf`) this is the textbook definition
`γ_ij = ⟨Ψ, c_i† c_j Ψ⟩`, with `Ψ` the state extended by zero to the whole Fock space.

## Main definitions

* `toFock ψ`: an `N`-particle state as a vector of the Fock space, zero outside the `N`-particle
  sector.

## Main results

* `rdm_eq_inner`: `γ_ij = ⟨Ψ, c_i† c_j Ψ⟩`, with `c_i†`, `c_j` bounded operators on the Fock
  Hilbert space.
-/

namespace DFT.Lattice.RDMFT

open Matrix QM.ManyBody DFT.Lattice.Fermions

variable {M N : ℕ}

/-- An `N`-particle state as a vector of the Fock space, zero outside the `N`-particle sector. -/
noncomputable def toFock (ψ : Conf M N → ℝ) : Fock M :=
  WithLp.toLp 2 fun u => if hu : u.card = N then (ψ ⟨u, hu⟩ : ℂ) else 0

/-- A sum over all configurations of a function supported on the `N`-particle sector is a sum over
`N`-particle configurations. -/
lemma sum_eq_sum_conf {β : Type*} [AddCommMonoid β] (F : Finset (Fin M) → β)
    (hF : ∀ u, u.card ≠ N → F u = 0) :
    ∑ u, F u = ∑ s : Conf M N, F s.1 := by
  rw [← Finset.sum_filter_of_ne (p := fun u => u.card = N)
    (fun u _ h => by by_contra hc; exact h (hF u hc))]
  exact Finset.sum_subtype _ (by simp) F

/-- The one-body operator of a matrix unit is a single hopping term: `oneBody E_ij = c_i† c_j`. -/
lemma oneBody_single (i j : Fin M) :
    oneBody ((Matrix.single i j (1 : ℝ)).map ((↑) : ℝ → ℂ)) = cre i * ann j := by
  rw [oneBody, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm ha]
  · simp

/-- **The one-body reduced density matrix is `⟨Ψ, c_i† c_j Ψ⟩`**: the lattice definition
`γ_ij = ⟨ψ, Γ(E_ij) ψ⟩` agrees with the Fock-space expectation value of `c_i† c_j`. -/
theorem rdm_eq_inner (ψ : Conf M N → ℝ) (i j : Fin M) :
    (rdm ψ i j : ℂ) = inner ℂ (toFock ψ) (creOp i (annOp j (toFock ψ))) := by
  have hm : ∀ x, creOp i (annOp j x) = toFockCLM (cre i * ann j) x := fun x => by
    rw [map_mul]; rfl
  rw [hm, toFock, toEuclideanCLM_toLp,
    EuclideanSpace.inner_toLp_toLp, ← oneBody_single]
  simp only [dotProduct, Matrix.mulVec]
  rw [sum_eq_sum_conf (N := N) _ (fun u hu => by simp [hu])]
  simp only [rdm, qf, dotProduct, Matrix.mulVec, Complex.ofReal_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_eq_sum_conf (N := N) _ (fun u hu => by simp [hu]), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [oneBody_apply_conf, Pi.star_apply, dite_eq_left s.2, dite_eq_left s'.2]
  simp only [Subtype.coe_eta, RCLike.star_def, Complex.conj_ofReal]
  ring

end DFT.Lattice.RDMFT
