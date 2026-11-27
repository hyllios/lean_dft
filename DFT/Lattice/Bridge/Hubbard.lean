/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.Spin.Resolved
import DFT.Lattice.TDDFT.Frozen

/-!
# Bridge: the hand-typed Hubbard matrices are the general two-species Hamiltonian

The Hubbard dimer and triangle at one electron per spin are entered by hand in the library: `H0D`,
`occD` (`Spin.HubbardCertificates`), `H0Tr`, `occTr`, and `hubD t U` (`TDDFT.Frozen`). This file
shows that they are the general two-species Hamiltonian `H0S` on the complete graph with hopping and
Hubbard interaction `hubbard U` (`H0D`, `H0Tr`: `t = 1`, `U = 4`; `hubD t U`: every `t` and `U`),
entry by entry, in the basis `cfgD`/`cfgTr` (index `2a + b` resp. `3a + b` ↦ up electron on `a`,
down electron on `b`), and that the occupations are `n_{i↑} + n_{i↓}` built from the general `occF`.
So the theorems proved for the hand-typed matrices are theorems about the physical model.

* `H0S_dimer`, `H0S_triangle`, `hubD_eq_H0S`, `hubD_1_4`;
* `occD_eq_occF`, `occTr_eq_occF`;
* `hubD_tripD`, `tripD_triplet`, `tripD_not_singlet`: `tripD` is a zero-energy triplet state of
  `hubD t U` for every `t` and `U`.
-/

namespace DFT

open Matrix

namespace Bridge.Hubbard

/-- One electron on site `a`. -/
def one (M : ℕ) (a : Fin M) : Conf M 1 := ⟨{a}, by simp⟩

lemma τs_one (M : ℕ) (a : Fin M) : τs (one M a) = ![a] := by
  unfold τs
  have h := Finset.orderEmbOfFin_unique (one M a).2 (f := ![a])
    (by intro x; fin_cases x; simp [one])
    (fun x y h => by fin_cases x; fin_cases y; exact absurd h (lt_irrefl _))
  exact h.symm ▸ rfl

lemma occF_one (M : ℕ) (i a : Fin M) : occF i (one M a) = if i = a then 1 else 0 := by
  simp [occF, one]

lemma one_inj (M : ℕ) (a b : Fin M) : one M a = one M b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun s : Conf M 1 => s.1) h
    simpa [one] using this
  · rintro rfl; rfl

/-- The dimer basis: index `2a + b` ↦ (up on `a`, down on `b`). -/
def cfgD : Fin 4 → Conf 2 1 × Conf 2 1 :=
  fun k => (one 2 ⟨k.val / 2, by omega⟩, one 2 ⟨k.val % 2, by omega⟩)

/-- The triangle basis: index `3a + b` ↦ (up on `a`, down on `b`). -/
def cfgTr : Fin 9 → Conf 3 1 × Conf 3 1 :=
  fun k => (one 3 ⟨k.val / 3, by omega⟩, one 3 ⟨k.val % 3, by omega⟩)

lemma cfgD_bijective : Function.Bijective cfgD := by decide

lemma cfgTr_bijective : Function.Bijective cfgTr := by decide

theorem H0S_dimer (i j : Fin 4) :
    H0S (⊤ : SimpleGraph (Fin 2)) (fun _ _ => 1) (hubbard 4) (cfgD i) (cfgD j) = H0D i j := by
  fin_cases i <;> fin_cases j <;>
    simp [H0S, kronSum, Matrix.add_apply, Matrix.kroneckerMap_apply, Γ, amp, slater, τs_one, hopM,
      hubbard, occF_one, one_inj, cfgD, H0D, Fin.sum_univ_succ, Matrix.det_unique, Function.update]

theorem H0S_triangle (i j : Fin 9) :
    H0S (⊤ : SimpleGraph (Fin 3)) (fun _ _ => 1) (hubbard 4) (cfgTr i) (cfgTr j) = H0Tr i j := by
  fin_cases i <;> fin_cases j <;>
    simp [H0S, kronSum, Matrix.add_apply, Matrix.kroneckerMap_apply, Γ, amp, slater, τs_one, hopM,
      hubbard, occF_one, one_inj, cfgTr, H0Tr, Fin.sum_univ_succ, Matrix.det_unique,
      Function.update]

/-- The hand-typed total occupations of the dimer are `n_{i↑} + n_{i↓}` built from `occF`. -/
theorem occD_eq_occF (i : Fin 2) (k : Fin 4) :
    occD i k = occF i (cfgD k).1 + occF i (cfgD k).2 := by
  fin_cases i <;> fin_cases k <;> simp [occD, occF_one, cfgD] <;> norm_num

/-- The hand-typed total occupations of the triangle are `n_{i↑} + n_{i↓}` built from `occF`. -/
theorem occTr_eq_occF (i : Fin 3) (k : Fin 9) :
    occTr i k = occF i (cfgTr k).1 + occF i (cfgTr k).2 := by
  fin_cases i <;> fin_cases k <;> simp [occTr, occF_one, cfgTr] <;> norm_num

/-- The Hubbard dimer `hubD t U` (`TDDFT/Frozen.lean`) is the general two-species `H0S` on the
dimer, entry by entry. -/
theorem hubD_eq_H0S (t U : ℝ) (i j : Fin 4) :
    H0S (⊤ : SimpleGraph (Fin 2)) (fun _ _ => t) (hubbard U) (cfgD i) (cfgD j) = hubD t U i j := by
  fin_cases i <;> fin_cases j <;>
    simp [H0S, kronSum, Matrix.add_apply, Matrix.kroneckerMap_apply, Γ, amp, slater, τs_one, hopM,
      hubbard, occF_one, one_inj, cfgD, hubD, Fin.sum_univ_succ, Matrix.det_unique, Function.update]

theorem hubD_1_4 : hubD 1 4 = H0D := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hubD, H0D]

/-- `tripD` has energy 0 for every `t` and `U`. For `U ≠ 0` and `t ≠ 0` it is the only zero-energy
state of the dimer (the singlet energies `U` and `(U ± √(U² + 16t²))/2` do not vanish; at `t = 0`,
`U ≠ 0`, the zero eigenspace is two-dimensional; not formalized here), so `tripD` is the triplet
whatever ket convention is used, as long as `hubD` is the physical Hamiltonian in that convention.
-/
theorem hubD_tripD (t U : ℝ) : hubD t U *ᵥ tripD = 0 := by
  rw [hubD_triplet, zero_smul]

theorem tripD_triplet : PTD *ᵥ tripD = tripD := by
  ext i; fin_cases i <;> simp [PTD, tripD, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    norm_num

theorem tripD_not_singlet : PSD *ᵥ tripD = 0 := by
  ext i; fin_cases i <;> simp [PSD, tripD, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Bridge.Hubbard

end DFT
