/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.KohnSham.Hypersimplex
import DFT.Lattice.RDMFT.FockRDM
import QM.ManyBody.RDM

/-!
# N-representability of the density

For spinless fermions on `M` modes the densities of `N`-particle states are exactly the vectors with
`0 ≤ ρ_i ≤ 1` and `Σ_i ρ_i = N`, for pure states as well as for ensembles. Necessity is the Pauli
principle in the form `0 ≤ γ ≤ 1` (`QM.ManyBody.rdm1Ens_posSemidef`,
`QM.ManyBody.one_sub_rdm1Ens_posSemidef`). Sufficiency comes from the vertex description of the
hypersimplex (`DFT.hypersimplex_mixture`): if `ρ = Σ_s μ_s occ(s)`, the state `Σ_s √μ_s |s⟩` has
density `ρ`, because `c_i† c_i` is diagonal on configurations.

## Main results

* `rdm1_toFock`: the Fock-space `γ` of a lattice state is its lattice `rdm`.
* `rdm_diag`: `rdm ψ i i = Σ_s occ_i(s) ψ_s²`.
* `toFock_isNState`: a normalised lattice state is an `N`-particle state of the Fock space.
* `density_nrep`: **N-representability of the density**. The three conditions (density of an
  `N`-particle state, of an `N`-particle ensemble, `0 ≤ ρ ≤ 1` with `Σ ρ = N`) are equivalent.
* `density_nrep_nonneg`: the state can be chosen with nonnegative real coefficients on
  configurations.
-/

namespace DFT.Lattice.RDMFT

open Matrix QM.ManyBody DFT.Lattice.Fermions
open scoped ComplexOrder

variable {M N : ℕ}

/-! ### Lattice states on the Fock space -/

/-- The Fock-space one-body matrix of a lattice state is the lattice `rdm`. -/
theorem rdm1_toFock (ψ : Conf M N → ℝ) : rdm1 (toFock ψ) = (rdm ψ).map ((↑) : ℝ → ℂ) := by
  ext i j
  rw [Matrix.map_apply, rdm_eq_inner]
  rfl

/-- The diagonal of the lattice `rdm`: `rdm ψ i i = Σ_s occ_i(s) ψ_s²`. -/
theorem rdm_diag (ψ : Conf M N → ℝ) (i : Fin M) : rdm ψ i i = ∑ s, occF i s * ψ s ^ 2 := by
  have hd : Matrix.single i i (1 : ℝ) = Matrix.diagonal (Pi.single i 1) :=
    (Matrix.diagonal_single i 1).symm
  rw [rdm, hd, gamma_diagonal]
  simp only [qf, dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [hj]
  · simp

/-- `‖toFock ψ‖² = Σ_s ψ_s²`. -/
theorem norm_toFock_sq (ψ : Conf M N → ℝ) : ‖toFock ψ‖ ^ 2 = ∑ s, ψ s ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, sum_eq_sum_conf (N := N)]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [toFock, s.2]
  · intro u hu; simp [toFock, hu]

/-- A lattice state is an eigenvector of `N̂` with eigenvalue `N`. -/
theorem numTotOp_toFock (ψ : Conf M N → ℝ) : numTotOp (toFock ψ) = (N : ℂ) • toFock ψ := by
  unfold numTotOp toFock
  rw [toEuclideanCLM_toLp]
  ext u
  simp only [PiLp.smul_apply, smul_eq_mul, numTot_mulVec]
  by_cases hu : u.card = N
  · rw [show (u.card : ℂ) = N by exact_mod_cast hu]
  · simp [hu]

/-- A normalised lattice state is an `N`-particle state of the Fock space. -/
theorem toFock_isNState {ψ : Conf M N → ℝ} (hψ : ∑ s, ψ s ^ 2 = 1) : IsNState N (toFock ψ) := by
  refine ⟨?_, numTotOp_toFock ψ⟩
  have h := norm_toFock_sq ψ
  rw [hψ] at h
  nlinarith [norm_nonneg (toFock ψ)]

/-! ### The density -/

/-- **N-representability of the density.** For `ρ : Fin M → ℝ` the following are equivalent:
`ρ` is the density of an `N`-particle state; `ρ` is the density of an `N`-particle ensemble;
`0 ≤ ρ_i ≤ 1` for all `i` and `Σ_i ρ_i = N`. -/
theorem density_nrep (ρ : Fin M → ℝ) :
    List.TFAE [
      ∃ Ψ : Fock M, IsNState N Ψ ∧ ∀ i, (rdm1 Ψ i i).re = ρ i,
      ∃ (k : ℕ) (w : Fin k → ℝ) (Ψ : Fin k → Fock M), IsNEnsemble N w Ψ ∧
        ∀ i, (rdm1Ens w Ψ i i).re = ρ i,
      (∀ i, 0 ≤ ρ i ∧ ρ i ≤ 1) ∧ ∑ i, ρ i = N] := by
  tfae_have 1 → 2 := by
    rintro ⟨Ψ, hΨ, hρ⟩
    refine ⟨1, fun _ => 1, fun _ => Ψ, ⟨fun _ => zero_le_one, by simp, fun _ => hΨ⟩, fun i => ?_⟩
    simpa [rdm1Ens] using hρ i
  tfae_have 2 → 3 := by
    rintro ⟨k, w, Ψ, hE, hρ⟩
    refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · rw [← hρ i]
      exact Complex.nonneg_iff.mp (rdm1Ens_posSemidef hE.1 Ψ).diag_nonneg |>.1
    · have h := (one_sub_rdm1Ens_posSemidef hE).diag_nonneg (i := i)
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at h
      have h' := (Complex.nonneg_iff.mp h).1
      rw [Complex.sub_re, Complex.one_re] at h'
      rw [← hρ i]; linarith
    · have h := congrArg Complex.re (trace_rdm1Ens hE)
      rw [Matrix.trace, Complex.re_sum] at h
      simpa [hρ] using h
  tfae_have 3 → 1 := by
    rintro ⟨hbox, hsum⟩
    obtain ⟨μ, hμ0, hμ1, hμρ⟩ := hypersimplex_mixture (N := N) (nfrac ρ) ρ rfl hbox hsum
    refine ⟨toFock fun s => √(μ s), toFock_isNState ?_, fun i => ?_⟩
    · simp_rw [Real.sq_sqrt (hμ0 _)]; exact hμ1
    · rw [rdm1_toFock, Matrix.map_apply, Complex.ofReal_re, rdm_diag, hμρ]
      simp_rw [Real.sq_sqrt (hμ0 _), mul_comm]
  tfae_finish

/-- The state realising a representable density can be chosen with nonnegative real coefficients
on configurations. -/
theorem density_nrep_nonneg {ρ : Fin M → ℝ} (hbox : ∀ i, 0 ≤ ρ i ∧ ρ i ≤ 1)
    (hsum : ∑ i, ρ i = N) :
    ∃ ψ : Conf M N → ℝ, (∀ s, 0 ≤ ψ s) ∧ IsNState N (toFock ψ) ∧
      ∀ i, (rdm1 (toFock ψ) i i).re = ρ i := by
  obtain ⟨μ, hμ0, hμ1, hμρ⟩ := hypersimplex_mixture (N := N) (nfrac ρ) ρ rfl hbox hsum
  refine ⟨fun s => √(μ s), fun s => Real.sqrt_nonneg _, toFock_isNState ?_, fun i => ?_⟩
  · simp_rw [Real.sq_sqrt (hμ0 _)]; exact hμ1
  · rw [rdm1_toFock, Matrix.map_apply, Complex.ofReal_re, rdm_diag, hμρ]
    simp_rw [Real.sq_sqrt (hμ0 _), mul_comm]

end DFT.Lattice.RDMFT
