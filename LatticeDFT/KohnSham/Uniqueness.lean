/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.GenericHK

/-!
# Generic uniqueness of the Kohn–Sham potential

The Kohn–Sham system is non-interacting. Specialising the generic Hohenberg–Kohn theorem to a
vanishing interaction shows that the Kohn–Sham potential reproducing a given ground state is unique
(up to a constant) for all potentials outside a closed, nowhere dense, Lebesgue-null set. It is
*not* unique everywhere: the two-fermion square (`hk_fails_square`, a non-interacting example) has a
whole plane of potentials (`square_wall`) at which the Kohn–Sham potential is not determined by the
density.
-/

namespace LatticeDFT

variable {M N : ℕ}

/-- **Generic uniqueness of the Kohn–Sham potential.** For symmetric hopping amplitudes `t a b`
of a common sign on the edges, the Kohn–Sham potential reproducing a ground state is unique up to a
constant outside a closed, nowhere dense, Lebesgue-null set of potentials. -/
theorem ks_potential_generic_unique_w {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0Fw G t (0 : Conf M N → ℝ)) occF v} ⊆ Z :=
  generic_hk_lattice_fermions_w hG htsym hts hN0 hNM 0

/-- **Generic uniqueness of the Kohn–Sham potential, uniform hopping** `t ≠ 0`. The special case of
`ks_potential_generic_unique_w`. -/
theorem ks_potential_generic_unique {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : ℝ} (ht : t ≠ 0) (hN0 : 0 < N) (hNM : N < M) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0F G t (0 : Conf M N → ℝ)) occF v} ⊆ Z := by
  rw [H0F_eq_H0Fw]
  exact ks_potential_generic_unique_w hG (fun _ _ => rfl) (s := t)
    (fun _ _ _ => mul_self_pos.mpr ht) hN0 hNM

end LatticeDFT
