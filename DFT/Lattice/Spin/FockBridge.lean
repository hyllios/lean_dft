/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Fermions.FockBridge
import DFT.Lattice.Spin.Resolved
import QM.ManyBody.Spin

/-!
# The spin bridge

The lattice code describes `Nu` spin-up and `Nd` spin-down electrons on `M` sites with the
configurations `Conf M Nu × Conf M Nd` and the Kronecker sum `Γ h↑ ⊗ 1 + 1 ⊗ Γ h↓` of the two
spinless many-body matrices (`DFT/Lattice/Spin`). Here this is identified with the Fock space of
the `2M` spin modes, ordered with all spin-up modes first (`QM.ManyBody.Spin`). The pair
`(x↑, x↓)` is the configuration `x↑ ∪ (M + x↓)`.

## Main results

* `spinOneBody_apply_conf` (**spin bridge**): on the `(Nu, Nd)` sector the matrix of
  `Σ_ij (h↑_ij c_{i↑}† c_{j↑} + h↓_ij c_{i↓}† c_{j↓})` is `kronSum (Γ h↑) (Γ h↓)`.
* `fockHamS_apply_conf`, `fockHamS_apply_eq_zero`: with any configuration-diagonal interaction the
  Fock Hamiltonian preserves the sector, and its matrix there is `kronSum (Γ h↑) (Γ h↓) + diag V`.
* `hubbardOp_apply_conf`: `U Σ_i n_{i↑} n_{i↓}` restricts to `diag (hubbard U)`.
* `H0S_eq_fock`, `hamN_H0S_eq_fock`: the lattice Hamiltonians `H0S G t (hubbard U)` and
  `hamN (H0S G t (hubbard U)) occS v` are restrictions of second-quantized Hamiltonians.
-/

namespace DFT.Lattice.Spin

open Matrix QM.ManyBody DFT.Lattice.Fermions

variable {M Nu Nd : ℕ}

/-- The Fock-space configuration `x↑ ∪ (M + x↓)` of a pair of lattice configurations. -/
def spinConfOf (x : Conf M Nu × Conf M Nd) : Finset (Fin (M + M)) := spinConf x.1.1 x.2.1

lemma spinConfOf_inj {x y : Conf M Nu × Conf M Nd} : spinConfOf x = spinConfOf y ↔ x = y := by
  rw [spinConfOf, spinConfOf, spinConf_inj, Prod.ext_iff, Subtype.ext_iff, Subtype.ext_iff]

/-- A configuration-diagonal interaction on the `(Nu, Nd)` sector, extended by `0`. -/
noncomputable def diagExtS (V : Conf M Nu × Conf M Nd → ℝ) : FockOp (M + M) :=
  diagonal fun w => if h : (upPart w).card = Nu ∧ (dnPart w).card = Nd then
    (V (⟨upPart w, h.1⟩, ⟨dnPart w, h.2⟩) : ℂ) else 0

lemma apply_eq_mulVec {n : ℕ} (A : FockOp n) (t s : Finset (Fin n)) :
    A t s = (A *ᵥ Pi.single s 1) t := by
  rw [mulVec_single_one]; rfl

lemma single_conf {N : ℕ} (s s' : Conf M N) :
    (Pi.single s'.1 (1 : ℂ) : Finset (Fin M) → ℂ) s.1 =
      (((1 : Matrix (Conf M N) (Conf M N) ℝ) s s' : ℝ) : ℂ) := by
  by_cases h : s = s'
  · subst h; simp
  · have : s.1 ≠ s'.1 := fun e => h (Subtype.ext e)
    simp [Pi.single_eq_of_ne this, one_apply_ne h]

/-- **The spin bridge.** On the `(Nu, Nd)` sector, the matrix of the Fock-space operator
`Σ_ij (h↑_ij c_{i↑}† c_{j↑} + h↓_ij c_{i↓}† c_{j↓})` is the lattice Kronecker sum
`Γ h↑ ⊗ 1 + 1 ⊗ Γ h↓`. -/
theorem spinOneBody_apply_conf (hu hd : Matrix (Fin M) (Fin M) ℝ)
    (x y : Conf M Nu × Conf M Nd) :
    spinOneBody (hu.map ((↑) : ℝ → ℂ)) (hd.map ((↑) : ℝ → ℂ)) (spinConfOf x) (spinConfOf y) =
      (kronSum (Γ hu) (Γ hd) x y : ℂ) := by
  refine (apply_eq_mulVec _ _ _).trans ?_
  rw [spinConfOf, spinConfOf, ← tens_single, spinOneBody_mulVec_tens,
    Pi.add_apply, tens_spinConf, tens_spinConf, ← apply_eq_mulVec, ← apply_eq_mulVec,
    oneBody_apply_conf, oneBody_apply_conf, single_conf, single_conf, kronSum_apply]
  push_cast
  ring

/-- Outside the `(Nu, Nd)` sector the spin one-body operator has no matrix elements with it. -/
theorem spinOneBody_apply_eq_zero (hu hd : Matrix (Fin M) (Fin M) ℂ) (y : Conf M Nu × Conf M Nd)
    {w : Finset (Fin (M + M))} (hw : ¬((upPart w).card = Nu ∧ (dnPart w).card = Nd)) :
    spinOneBody hu hd w (spinConfOf y) = 0 := by
  refine (apply_eq_mulVec _ _ _).trans ?_
  rw [spinConfOf, ← tens_single, spinOneBody_mulVec_tens, ← spinConf_parts w,
    Pi.add_apply, tens_spinConf, tens_spinConf, ← apply_eq_mulVec, ← apply_eq_mulVec]
  rcases not_and_or.mp hw with h | h
  · have hne : upPart w ≠ y.1.1 := fun e => h (e ▸ y.1.2)
    rw [oneBody_apply_eq_zero_of_card_ne hu (s := upPart w) (t := y.1.1) (by rw [y.1.2]; exact h),
      Pi.single_eq_of_ne hne]
    ring
  · have hne : dnPart w ≠ y.2.1 := fun e => h (e ▸ y.2.2)
    rw [oneBody_apply_eq_zero_of_card_ne hd (s := dnPart w) (t := y.2.1) (by rw [y.2.2]; exact h),
      Pi.single_eq_of_ne hne]
    ring

lemma diagExtS_apply_conf (V : Conf M Nu × Conf M Nd → ℝ) (x y : Conf M Nu × Conf M Nd) :
    diagExtS V (spinConfOf x) (spinConfOf y) = ((diagonal V x y : ℝ) : ℂ) := by
  rw [diagExtS, diagonal_apply, diagonal_apply]
  by_cases h : x = y
  · subst h
    have hx : (upPart (spinConfOf x)).card = Nu ∧ (dnPart (spinConfOf x)).card = Nd := by
      simp [spinConfOf, x.1.2, x.2.2]
    rw [ite_eq_left rfl, ite_eq_left rfl, dite_eq_left hx]
    congr 2
    ext <;> simp [spinConfOf]
  · rw [ite_eq_right (fun e => h (spinConfOf_inj.mp e)), ite_eq_right h, Complex.ofReal_zero]

/-- The Fock Hamiltonian `Σ_ij (h↑_ij c_{i↑}† c_{j↑} + h↓_ij c_{i↓}† c_{j↓}) + V` with a
configuration-diagonal interaction `V`. -/
noncomputable def fockHamS (hu hd : Matrix (Fin M) (Fin M) ℝ) (V : Conf M Nu × Conf M Nd → ℝ) :
    FockOp (M + M) :=
  spinOneBody (hu.map ((↑) : ℝ → ℂ)) (hd.map ((↑) : ℝ → ℂ)) + diagExtS V

/-- **The Fock Hamiltonian on the `(Nu, Nd)` sector** is `kronSum (Γ h↑) (Γ h↓) + diag V`. -/
theorem fockHamS_apply_conf (hu hd : Matrix (Fin M) (Fin M) ℝ) (V : Conf M Nu × Conf M Nd → ℝ)
    (x y : Conf M Nu × Conf M Nd) :
    fockHamS hu hd V (spinConfOf x) (spinConfOf y) =
      ((kronSum (Γ hu) (Γ hd) + diagonal V : Matrix (Conf M Nu × Conf M Nd) _ ℝ) x y : ℂ) := by
  rw [fockHamS, Matrix.add_apply, spinOneBody_apply_conf, diagExtS_apply_conf, Matrix.add_apply]
  push_cast; rfl

/-- **The Fock Hamiltonian preserves the `(Nu, Nd)` sector.** -/
theorem fockHamS_apply_eq_zero (hu hd : Matrix (Fin M) (Fin M) ℝ) (V : Conf M Nu × Conf M Nd → ℝ)
    (y : Conf M Nu × Conf M Nd) {w : Finset (Fin (M + M))}
    (hw : ¬((upPart w).card = Nu ∧ (dnPart w).card = Nd)) :
    fockHamS hu hd V w (spinConfOf y) = 0 := by
  have hne : w ≠ spinConfOf y := by
    rintro rfl; exact hw (by simp [spinConfOf, y.1.2, y.2.2])
  rw [fockHamS, Matrix.add_apply, spinOneBody_apply_eq_zero _ _ y hw, diagExtS,
    diagonal_apply_ne _ hne, add_zero]

/-- **The Hubbard operator restricts to the Hubbard interaction** of the lattice code. -/
theorem hubbardOp_apply_conf (U : ℝ) (x y : Conf M Nu × Conf M Nd) :
    hubbardOp (U : ℂ) (spinConfOf x) (spinConfOf y) = ((diagonal (hubbard U) x y : ℝ) : ℂ) := by
  refine (apply_eq_mulVec _ _ _).trans ?_
  simp only [spinConfOf]
  rw [hubbardOp_mulVec, diagonal_apply]
  by_cases h : x = y
  · subst h
    rw [Pi.single_eq_same, ite_eq_left rfl, hubbard]
    push_cast
    simp only [occF, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  · have hne : spinConf x.1.1 x.2.1 ≠ spinConf y.1.1 y.2.1 := fun e => h (spinConfOf_inj.mp e)
    rw [Pi.single_eq_of_ne hne, ite_eq_right h]
    simp

/-- The lattice Hamiltonian `H0S G t (hubbard U)` of the Hubbard model is the restriction to the
`(Nu, Nd)` sector of `-Σ_σ Σ_ij t_ij A_ij c_{iσ}† c_{jσ} + U Σ_i n_{i↑} n_{i↓}`. -/
theorem H0S_eq_fock (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ) (U : ℝ)
    (x y : Conf M Nu × Conf M Nd) :
    (spinOneBody ((-hopM G t).map ((↑) : ℝ → ℂ)) ((-hopM G t).map ((↑) : ℝ → ℂ)) +
        hubbardOp (U : ℂ) : FockOp (M + M)) (spinConfOf x) (spinConfOf y) =
      (H0S G t (hubbard U) x y : ℂ) := by
  rw [Matrix.add_apply, spinOneBody_apply_conf, hubbardOp_apply_conf, H0S, Matrix.add_apply]
  push_cast; rfl

/-- With a spin-dependent potential `v`, the lattice spin-DFT Hamiltonian
`hamN (H0S G t (hubbard U)) occS v` is the restriction of
`Σ_σ Σ_ij (-t A + diag v_σ)_ij c_{iσ}† c_{jσ} + U Σ_i n_{i↑} n_{i↓}`. -/
theorem hamN_H0S_eq_fock (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ)
    (U : ℝ) (v : Fin M ⊕ Fin M → ℝ) (x y : Conf M Nu × Conf M Nd) :
    (spinOneBody ((-hopM G t + diagonal fun i => v (Sum.inl i)).map ((↑) : ℝ → ℂ))
        ((-hopM G t + diagonal fun i => v (Sum.inr i)).map ((↑) : ℝ → ℂ)) +
        hubbardOp (U : ℂ) : FockOp (M + M)) (spinConfOf x) (spinConfOf y) =
      (hamN (H0S G t (hubbard U)) occS v x y : ℂ) := by
  rw [Matrix.add_apply, spinOneBody_apply_conf, hubbardOp_apply_conf]
  simp only [hamN, H0S, sum_occS, Matrix.add_apply, kronSum_apply, gamma_add, gamma_diagonal, wC]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases eq_or_ne x1 y1 with rfl | h1 <;> rcases eq_or_ne x2 y2 with rfl | h2
  · simp only [one_apply_eq, diagonal_apply_eq]; push_cast; ring
  all_goals simp [*]

end DFT.Lattice.Spin
