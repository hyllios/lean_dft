/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.TDDFT.ForceBalance

/-!
# Excited states outside the exceptional set

(H*) (`hstar_lattice_fermions_w`) and `eigen_unique_of_hstar` give more than the ground-state
statement: outside one closed, nowhere dense, Lebesgue-null set of potentials, no eigenvector of
`H(v)`, ground or excited, has a zero amplitude, and every eigenvalue is simple (if `φ` and `ψ`
share an eigenvalue, `φ − (φ_c / ψ_c) ψ` is an eigenvector vanishing at `c`, hence zero).

* `excited_no_zero_and_simple`.
-/

namespace DFT

open Matrix MeasureTheory

variable {M N : ℕ}

/-- **Excited states.** For spinless fermions on a connected graph with symmetric hopping of a
common sign, outside a closed, nowhere dense, null set of potentials, no eigenstate (ground or
excited) has a zero amplitude, and every eigenvalue is simple. -/
theorem excited_no_zero_and_simple {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ v ∉ Z, ∀ (E : ℝ) (ψ : Conf M N → ℝ), ψ ≠ 0 →
        hamN (H0Fw G t Vint) occF v *ᵥ ψ = E • ψ →
        (∀ c, ψ c ≠ 0) ∧
        ∀ φ : Conf M N → ℝ, hamN (H0Fw G t Vint) occF v *ᵥ φ = E • φ → ∃ a : ℝ, φ = a • ψ := by
  set ord : Conf M N → ℕ := fun j => (Fintype.equivFin (Conf M N) j : ℕ)
  set Q := ∏ c, krylovPoly (H0Fw G t Vint) occF c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hstar_lattice_fermions_w hG hts c Vint)
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  have hS : ∀ v, (hamN (H0Fw G t Vint) occF v).IsSymm := fun v =>
    hamN_isSymm (H0Fw_isSymm G htsym Vint) occF v
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun v hv E ψ hψ hE => ?_⟩
  -- (H*) at v: every Krylov determinant is nonzero
  have hv' : ∀ c, (kry (hamN (H0Fw G t Vint) occF v) c ord).det ≠ 0 := by
    intro c hc
    apply hv
    change MvPolynomial.eval v Q = 0
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    rw [eval_krylovPoly]
    exact hc
  exact ⟨(eigen_unique_of_hstar (hS v) hv' hψ hE hE).1,
    fun φ hφ => (eigen_unique_of_hstar (hS v) hv' hψ hE hφ).2⟩

end DFT
