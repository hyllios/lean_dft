import LatticeDFT.GenericHK

/-!
# Generic uniqueness of the Kohn–Sham potential

The Kohn–Sham system is non-interacting. Specialising the generic Hohenberg–Kohn theorem to a vanishing
interaction shows that the Kohn–Sham potential reproducing a given ground state is unique (up to a constant)
for all potentials outside a closed, nowhere dense, Lebesgue-null set. It is *not* unique everywhere: the
two-fermion square (`hk_fails_square`, a non-interacting example) has a whole plane of potentials
(`square_wall`) at which the Kohn–Sham potential is not determined by the density.
-/

namespace LatticeDFT

variable {M N : ℕ}

/-- **Generic uniqueness of the Kohn–Sham potential.** -/
theorem ks_potential_generic_unique {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : ℝ} (ht : t ≠ 0) (hN0 : 0 < N) (hNM : N < M) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUV (H0F G t (0 : Conf M N → ℝ)) occF v} ⊆ Z :=
  generic_hk_lattice_fermions hG ht hN0 hNM 0

end LatticeDFT
