/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import QM.AngularMomentum.Ladder
import QM.Spin.Algebra

/-!
# Clebsch–Gordan for two and three spins

For two spin-½ particles `S² = 1 + P₀₁`, and for three `S² = ¾ + P₀₁ + P₀₂ + P₁₂`, where `P_ij`
exchanges the spins of particles `i` and `j` (`S2_two`, `S2_three`). The spin multiplets follow
from the exchange symmetry of the states.

## Main results

* `isSU2_spin`: the spin operators of `N` spin-½ particles (`QM.Spin.Algebra`) satisfy the su(2)
  relations `IsSU2` of `QM/AngularMomentum/Ladder`.
* `triplet_singlet`: for two spins, `|↑↑⟩`, `|↑↓⟩ + |↓↑⟩`, `|↓↓⟩` (triplet, `S² = 2`,
  `S_z = 1, 0, -1`) and `|↑↓⟩ - |↓↑⟩` (singlet, `S² = 0`, `S_z = 0`) form a basis of
  eigenvectors (`triplet_singlet_basis`).
* `S2_three_poly`: for three spins `(S² - 15/4)(S² - 3/4) = 0`.
* `quartet_highest`, `doublet_highest`: `|↑↑↑⟩` is a highest weight with `S² = 15/4`, and
  `|↑↑↓⟩ - |↑↓↑⟩`, `|↑↑↓⟩ - |↓↑↑⟩` are linearly independent highest weights with `S² = 3/4`,
  `S_z = 1/2`.
-/

namespace QM

open DFT.Continuum.Line Function Module

/-! ### Spin-½ particles satisfy su(2) -/

/-- **The spin operators of `N` spin-½ particles satisfy the su(2) relations.** -/
theorem isSU2_spin {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℝ W] :
    IsSU2 (DFT.Continuum.Line.Sp : End ℝ (DFT.Continuum.Line.SpinC n → W))
      DFT.Continuum.Line.Sm DFT.Continuum.Line.Sz where
  comm_pm := DFT.Continuum.Line.comm_Sp_Sm'
  comm_zp := DFT.Continuum.Line.comm_Sz_Sp'
  comm_zm := LinearMap.ext DFT.Continuum.Line.comm_Sz_Sm

/-- The total spin of `IsSU2` is the `S2` of `QM.Spin.Algebra`. -/
theorem isSU2_spin_S2 {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℝ W] :
    (isSU2_spin (n := n) (W := W)).S2 = DFT.Continuum.Line.S2 :=
  DFT.Continuum.Line.S2_eq.symm

/-! ### Two spins -/

lemma spinC1_eq (s : SpinC 1) : s = ![s 0, s 1] := by
  funext i; fin_cases i <;> rfl

@[simp] lemma upd2_zero (a b x : Bool) : update (![a, b] : SpinC 1) 0 x = ![x, b] := by
  funext i; fin_cases i <;> simp

@[simp] lemma upd2_one (a b x : Bool) : update (![a, b] : SpinC 1) 1 x = ![a, x] := by
  funext i; fin_cases i <;> simp

@[simp] lemma swap2 (a b : Bool) : (![a, b] : SpinC 1) ∘ Equiv.swap 0 1 = ![b, a] := by
  funext i; fin_cases i <;> simp

lemma nup2 (a b : Bool) :
    nup (![a, b] : SpinC 1) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- **`S² = 1 + P₀₁`** for two spins. -/
theorem S2_two (u : SpinC 1 → ℝ) (s : SpinC 1) : S2 u s = u s + u (s ∘ Equiv.swap 0 1) := by
  rw [← isSU2_spin_S2, IsSU2.S2]
  rw [spinC1_eq s]
  generalize s 0 = a
  generalize s 1 = b
  cases a <;> cases b <;>
    simp [Sp_apply, Sm_apply, Sz_apply, Mz, nup2, Fin.sum_univ_two, mul_apply_eq_comp] <;> ring

/-- The basis state `|a b⟩` of two spins (`true` is spin up). -/
def ket2 (a b : Bool) : SpinC 1 → ℝ := Pi.single ![a, b] 1

lemma ket2_apply (a b c d : Bool) : ket2 a b ![c, d] = if a = c ∧ b = d then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [ket2]

/-- The triplet `|↑↑⟩`, `|↑↓⟩ + |↓↑⟩`, `|↓↓⟩` and the singlet `|↑↓⟩ - |↓↑⟩`. -/
noncomputable def twoSpin : Fin 4 → SpinC 1 → ℝ :=
  ![ket2 true true, ket2 true false + ket2 false true, ket2 false false,
    ket2 true false - ket2 false true]

/-- The eigenvalues of `S²` on `twoSpin`. -/
def twoSpinS2 : Fin 4 → ℝ := ![2, 2, 2, 0]

/-- The eigenvalues of `S_z` on `twoSpin`. -/
def twoSpinSz : Fin 4 → ℝ := ![1, 0, -1, 0]

/-- **Triplet and singlet**: `S² = 2` and `S_z = 1, 0, -1` on the triplet, `S² = S_z = 0` on the
singlet. -/
theorem triplet_singlet (k : Fin 4) :
    S2 (twoSpin k) = twoSpinS2 k • twoSpin k ∧ Sz (twoSpin k) = twoSpinSz k • twoSpin k := by
  constructor
  · funext s
    rw [S2_two, spinC1_eq s]
    generalize s 0 = a
    generalize s 1 = b
    fin_cases k <;> cases a <;> cases b <;> simp [twoSpin, twoSpinS2, ket2_apply] <;> norm_num
  · funext s
    rw [Sz_apply, spinC1_eq s]
    generalize s 0 = a
    generalize s 1 = b
    fin_cases k <;> cases a <;> cases b <;> norm_num [twoSpin, twoSpinSz, ket2_apply, Mz, nup2]

lemma finrank_two : Module.finrank ℝ (SpinC 1 → ℝ) = 4 := by
  rw [Module.finrank_fintype_fun_eq_card]; rfl

/-- **The triplet and the singlet form a basis.** They are eigenvectors of `S² + 3 S_z` with the
distinct eigenvalues `5, 2, -1, 0`. -/
theorem triplet_singlet_basis :
    LinearIndependent ℝ twoSpin ∧ Submodule.span ℝ (Set.range twoSpin) = ⊤ := by
  have hli : LinearIndependent ℝ twoSpin := by
    refine Module.End.eigenvectors_linearIndependent' (S2 + (3 : ℝ) • Sz)
      (fun k => twoSpinS2 k + 3 * twoSpinSz k) ?_ twoSpin fun k => ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp [twoSpinS2, twoSpinSz] at hab ⊢ <;> norm_num at hab
    · refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · obtain ⟨h1, h2⟩ := triplet_singlet k
        rw [LinearMap.add_apply, LinearMap.smul_apply, h1, h2, smul_smul, ← add_smul]
      · intro h0
        have := congrFun h0 ![true, false]
        fin_cases k <;> simp [twoSpin, ket2_apply] at this
        · exact absurd (congrFun h0 ![true, true]) (by simp [twoSpin, ket2_apply])
        · exact absurd (congrFun h0 ![false, false]) (by simp [twoSpin, ket2_apply])
  exact ⟨hli, hli.span_eq_top_of_card_eq_finrank (by rw [finrank_two]; rfl)⟩

/-! ### Three spins -/

lemma spinC2_eq (s : SpinC 2) : s = ![s 0, s 1, s 2] := by
  funext i; fin_cases i <;> rfl

@[simp] lemma upd3_zero (a b c x : Bool) : update (![a, b, c] : SpinC 2) 0 x = ![x, b, c] := by
  funext i; fin_cases i <;> simp

@[simp] lemma upd3_one (a b c x : Bool) : update (![a, b, c] : SpinC 2) 1 x = ![a, x, c] := by
  funext i; fin_cases i <;> simp

@[simp] lemma upd3_two (a b c x : Bool) : update (![a, b, c] : SpinC 2) 2 x = ![a, b, x] := by
  funext i; fin_cases i <;> simp

@[simp] lemma swap3_01 (a b c : Bool) : (![a, b, c] : SpinC 2) ∘ Equiv.swap 0 1 = ![b, a, c] := by
  funext i; fin_cases i <;> simp [Equiv.swap_apply_def]

@[simp] lemma swap3_02 (a b c : Bool) : (![a, b, c] : SpinC 2) ∘ Equiv.swap 0 2 = ![c, b, a] := by
  funext i; fin_cases i <;> simp [Equiv.swap_apply_def]

@[simp] lemma swap3_12 (a b c : Bool) : (![a, b, c] : SpinC 2) ∘ Equiv.swap 1 2 = ![a, c, b] := by
  funext i; fin_cases i <;> simp [Equiv.swap_apply_def]

lemma nup3 (a b c : Bool) : nup (![a, b, c] : SpinC 2) =
    (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

/-- **`S² = ¾ + P₀₁ + P₀₂ + P₁₂`** for three spins. -/
theorem S2_three (u : SpinC 2 → ℝ) (s : SpinC 2) :
    S2 u s = (3 / 4 : ℝ) * u s + u (s ∘ Equiv.swap 0 1) + u (s ∘ Equiv.swap 0 2) +
      u (s ∘ Equiv.swap 1 2) := by
  rw [← isSU2_spin_S2, IsSU2.S2]
  rw [spinC2_eq s]
  generalize s 0 = a
  generalize s 1 = b
  generalize s 2 = c
  cases a <;> cases b <;> cases c <;>
    simp [Sp_apply, Sm_apply, Sz_apply, Mz, nup3, Fin.sum_univ_three, mul_apply_eq_comp] <;> ring

/-- **`(S² - 15/4)(S² - 3/4) = 0`** for three spins: the only total spins are `3/2` and `1/2`. -/
theorem S2_three_poly (u : SpinC 2 → ℝ) :
    S2 (S2 u - (3 / 4 : ℝ) • u) - (15 / 4 : ℝ) • (S2 u - (3 / 4 : ℝ) • u) = 0 := by
  funext s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sub, map_smul]
  simp only [S2_three]
  rw [spinC2_eq s]
  generalize s 0 = a
  generalize s 1 = b
  generalize s 2 = c
  cases a <;> cases b <;> cases c <;> simp <;> ring

/-- The basis state `|a b c⟩` of three spins. -/
def ket3 (a b c : Bool) : SpinC 2 → ℝ := Pi.single ![a, b, c] 1

lemma ket3_apply (a b c d e f : Bool) :
    ket3 a b c ![d, e, f] = if a = d ∧ b = e ∧ c = f then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp [ket3]

/-- **The quartet**: `|↑↑↑⟩` is a highest weight (`S₊ = 0`) with `S² = 15/4` and `S_z = 3/2`. -/
theorem quartet_highest :
    Sp (ket3 true true true) = 0 ∧ S2 (ket3 true true true) = (15 / 4 : ℝ) • ket3 true true true ∧
      Sz (ket3 true true true) = (3 / 2 : ℝ) • ket3 true true true := by
  refine ⟨?_, ?_, ?_⟩ <;> funext s <;> rw [spinC2_eq s] <;>
    generalize s 0 = a <;> generalize s 1 = b <;> generalize s 2 = c <;>
    cases a <;> cases b <;> cases c <;>
    simp [Sp_apply, S2_three, Sz_apply, Mz, nup3, Fin.sum_univ_three, ket3_apply] <;> norm_num

/-- The two doublet highest weights `|↑↑↓⟩ - |↑↓↑⟩` and `|↑↑↓⟩ - |↓↑↑⟩`. -/
noncomputable def doublet : Fin 2 → SpinC 2 → ℝ :=
  ![ket3 true true false - ket3 true false true, ket3 true true false - ket3 false true true]

/-- **Two doublets**: `|↑↑↓⟩ - |↑↓↑⟩` and `|↑↑↓⟩ - |↓↑↑⟩` are highest weights (`S₊ = 0`) with
`S² = 3/4` and `S_z = 1/2`, and they are linearly independent. -/
theorem doublet_highest :
    (∀ k, Sp (doublet k) = 0 ∧ S2 (doublet k) = (3 / 4 : ℝ) • doublet k ∧
      Sz (doublet k) = (1 / 2 : ℝ) • doublet k) ∧ LinearIndependent ℝ doublet := by
  refine ⟨fun k => ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;> funext s <;> rw [spinC2_eq s] <;>
      generalize s 0 = a <;> generalize s 1 = b <;> generalize s 2 = c <;>
      fin_cases k <;> cases a <;> cases b <;> cases c <;>
      simp [doublet, Sp_apply, S2_three, Sz_apply, Mz, nup3, Fin.sum_univ_three, ket3_apply] <;>
      norm_num
  · have h : doublet = ![doublet 0, doublet 1] := by
      funext k; fin_cases k <;> rfl
    rw [h, LinearIndependent.pair_iff]
    intro x y hxy
    have h1 := congrFun hxy ![true, false, true]
    have h2 := congrFun hxy ![false, true, true]
    exact ⟨by simpa [doublet, ket3_apply] using h1, by simpa [doublet, ket3_apply] using h2⟩

end QM
