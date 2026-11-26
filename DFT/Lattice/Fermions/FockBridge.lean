/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Fermions.SecondQuantization
import QM.ManyBody.OneBody

/-!
# The lattice second quantization is the Fock-space one

The lattice code defines the many-body matrix `Γ h` of a single-particle matrix `h` on
`N`-particle configurations with determinants (`DFT/Lattice/Fermions/SecondQuantization`). Here it is
identified with the matrix of the Fock-space operator `Σ_ij h_ij c_i† c_j` (`QM.ManyBody.oneBody`)
on the `N`-particle sector. The lattice Hamiltonians `H0F` and `hamN (H0F …)` are therefore
restrictions of second-quantized Hamiltonians on the Fock space.

The key step is `slaterVec_apply`: the creation string `c_{τ 0}† ⋯ c_{τ (N-1)}† |∅⟩` has the
determinant `amp s τ` as its coefficient on the configuration `s` (Laplace expansion along the first
row against the Jordan–Wigner sign).

## Main results

* `slaterVec_apply`: the coefficients of a creation string are the lattice amplitudes `amp s τ`.
* `slaterVec_τs`: the creation string of the sorted modes of `s` is the basis vector `|s⟩`.
* `oneBody_apply_conf` (**bridge**): `⟨s| Σ_ij h_ij c_i† c_j |s'⟩ = Γ h s s'` for `N`-particle
  configurations `s, s'`. Together with `QM.ManyBody.oneBody_apply_eq_zero_of_card_ne`, the operator
  preserves the `N`-particle sector and its matrix there is `Γ h`.
* `fockHam_apply_conf`, `H0F_eq_fock`, `hamN_H0F_eq_fock`: the lattice Hamiltonians are the
  restrictions of `Σ_ij h_ij c_i† c_j + (configuration-diagonal interaction)`.
-/

namespace DFT.Lattice.Fermions

open Matrix Finset QM.ManyBody

variable {M : ℕ}

/-! ### Sorted configurations -/

/-- The `j`-th occupied mode of `s` has exactly `j` occupied modes below it. -/
lemma card_filter_lt_τs {N : ℕ} (s : Conf M N) (j : Fin N) :
    (s.1.filter (· < τs s j)).card = j := by
  have : s.1.filter (· < τs s j) = (Finset.Iio j).map (s.1.orderEmbOfFin s.2).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨k, rfl⟩ := τs_surj s hx
      exact ⟨k, (s.1.orderEmbOfFin s.2).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (s.1.orderEmbOfFin s.2).lt_iff_lt.mpr hk⟩
  rw [this, Finset.card_map, Fin.card_Iio]

/-- The configuration `s` with its `j`-th occupied mode removed. -/
def confErase {N : ℕ} (s : Conf M (N + 1)) (j : Fin (N + 1)) : Conf M N :=
  ⟨s.1.erase (τs s j), by rw [Finset.card_erase_of_mem (τs_mem s j), s.2]; rfl⟩

/-- Removing the `j`-th occupied mode shifts the sorted modes past `j`. -/
lemma τs_confErase {N : ℕ} (s : Conf M (N + 1)) (j : Fin (N + 1)) :
    τs (confErase s j) = τs s ∘ j.succAbove := by
  have hmem : ∀ k, (τs s ∘ j.succAbove) k ∈ (confErase s j).1 := fun k =>
    Finset.mem_erase.mpr ⟨(τs_injective s).ne (Fin.succAbove_ne j k), τs_mem s _⟩
  have hmono : StrictMono (τs s ∘ j.succAbove) :=
    (s.1.orderEmbOfFin s.2).strictMono.comp (Fin.strictMono_succAbove j)
  exact (Finset.orderEmbOfFin_unique (confErase s j).2 hmem hmono).symm

/-- Laplace expansion of the amplitude along the first position. -/
lemma amp_succ {N : ℕ} (s : Conf M (N + 1)) (τ : Fin (N + 1) → Fin M) (j : Fin (N + 1))
    (hj : τs s j = τ 0) : amp s τ = (-1) ^ (j : ℕ) * amp (confErase s j) (Fin.tail τ) := by
  unfold amp slater
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single j]
  · simp only [Matrix.of_apply, hj, ite_true, mul_one]
    congr 2
    ext k m
    simp only [Matrix.submatrix_apply, Matrix.of_apply, τs_confErase, Function.comp_apply, Fin.tail]
  · intro m _ hm
    have : τ 0 ≠ τs s m := fun h => hm ((τs_injective s) (h ▸ hj).symm)
    simp [this]
  · simp

/-! ### Creation strings are Slater determinants -/

/-- **The coefficients of a creation string are the lattice amplitudes**:
`(c_{τ 0}† ⋯ c_{τ (N-1)}† |∅⟩)(u) = amp u τ` if `|u| = N`, and `0` otherwise. -/
theorem slaterVec_apply {N : ℕ} (τ : Fin N → Fin M) (u : Finset (Fin M)) :
    slaterVec τ u = if hu : u.card = N then (amp ⟨u, hu⟩ τ : ℂ) else 0 := by
  induction N generalizing u with
  | zero =>
    rw [slaterVec_zero]
    by_cases hu : u = ∅
    · subst hu
      simp [amp, slater]
    · rw [Pi.single_eq_of_ne hu, dite_eq_right (by simpa [Finset.card_eq_zero] using hu)]
  | succ N ih =>
    rw [slaterVec_succ, cre_mulVec]
    by_cases ha : τ 0 ∈ u
    · rw [ite_eq_left ha, ih]
      by_cases hu : u.card = N + 1
      · have hu' : (u.erase (τ 0)).card = N := by rw [Finset.card_erase_of_mem ha, hu]; rfl
        rw [dite_eq_left hu', dite_eq_left hu]
        set s : Conf M (N + 1) := ⟨u, hu⟩
        obtain ⟨j, hj⟩ := τs_surj s ha
        have hs' : (⟨u.erase (τ 0), hu'⟩ : Conf M N) = confErase s j :=
          Subtype.ext (by simp [confErase, hj, s])
        have hb : below (τ 0) (u.erase (τ 0)) = j := by
          rw [← card_filter_lt_τs s j, hj, below, Finset.filter_erase,
            Finset.erase_eq_of_notMem (by simp)]
        rw [hs', amp_succ s τ j hj, jwSign, hb]
        push_cast
        ring
      · have hu' : (u.erase (τ 0)).card ≠ N := by
          have := Finset.card_pos.mpr ⟨_, ha⟩
          rw [Finset.card_erase_of_mem ha]; omega
        rw [dite_eq_right hu', dite_eq_right hu, mul_zero]
    · rw [ite_eq_right ha]
      split_ifs with hu
      · rw [amp_of_not_mem ⟨u, hu⟩ (k := 0) ha]
        simp
      · rfl

/-- The creation string of the sorted occupied modes of `s` is the basis vector `|s⟩`. -/
theorem slaterVec_τs {N : ℕ} (s : Conf M N) : slaterVec (τs s) = Pi.single s.1 1 := by
  funext u
  rw [slaterVec_apply]
  split_ifs with hu
  · rw [amp_tau_eq]
    by_cases h : s = ⟨u, hu⟩
    · subst h
      simp
    · have hne : u ≠ s.1 := fun e => h (Subtype.ext e.symm)
      rw [ite_eq_right h, Pi.single_eq_of_ne hne]
      simp
  · have hne : u ≠ s.1 := fun e => hu (e ▸ s.2)
    rw [Pi.single_eq_of_ne hne]

/-! ### The bridge -/

/-- **Bridge to the lattice code.** On `N`-particle configurations, the matrix of the Fock-space
operator `Σ_ij h_ij c_i† c_j` is the lattice many-body matrix `Γ h`. -/
theorem oneBody_apply_conf (h : Matrix (Fin M) (Fin M) ℝ) {N : ℕ} (s s' : Conf M N) :
    oneBody (h.map ((↑) : ℝ → ℂ)) s.1 s'.1 = (Γ h s s' : ℂ) := by
  have e : oneBody (h.map ((↑) : ℝ → ℂ)) s.1 s'.1 =
      (oneBody (h.map ((↑) : ℝ → ℂ)) *ᵥ slaterVec (τs s')) s.1 := by
    rw [slaterVec_τs, Matrix.mulVec_single_one]
    rfl
  rw [e, oneBody_mulVec_slaterVec, ← Matrix.transpose_apply (Γ h), gamma_transpose]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, slaterVec_apply, dite_eq_left s.2,
    Matrix.map_apply, Γ, Matrix.transpose_apply]
  push_cast
  rfl

/-- A configuration-diagonal function, extended by `0` to the whole Fock space. -/
noncomputable def diagExt {N : ℕ} (V : Conf M N → ℝ) : FockOp M :=
  Matrix.diagonal fun u => if hu : u.card = N then (V ⟨u, hu⟩ : ℂ) else 0

/-- The Fock-space Hamiltonian `Σ_ij h_ij c_i† c_j + V` restricts on the `N`-particle sector to the
lattice Hamiltonian `Γ h + diag V`. -/
theorem fockHam_apply_conf (h : Matrix (Fin M) (Fin M) ℝ) {N : ℕ} (V : Conf M N → ℝ)
    (s s' : Conf M N) :
    (oneBody (h.map ((↑) : ℝ → ℂ)) + diagExt V) s.1 s'.1 =
      ((Γ h + Matrix.diagonal V : Matrix (Conf M N) (Conf M N) ℝ) s s' : ℂ) := by
  rw [Matrix.add_apply, oneBody_apply_conf, Matrix.add_apply, diagExt, Matrix.diagonal_apply,
    Matrix.diagonal_apply, dite_eq_left s.2]
  by_cases hss : s = s'
  · subst hss
    simp
  · have : s.1 ≠ s'.1 := fun e => hss (Subtype.ext e)
    simp [hss, this]

/-- The lattice Hamiltonian `H0F` of spinless fermions is the restriction to the `N`-particle
sector of the second-quantized Hamiltonian `-t Σ_{⟨ij⟩} c_i† c_j + V_int`. -/
theorem H0F_eq_fock (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : ℝ) {N : ℕ}
    (Vint : Conf M N → ℝ) (s s' : Conf M N) :
    (oneBody ((-t • G.adjMatrix ℝ).map ((↑) : ℝ → ℂ)) + diagExt Vint) s.1 s'.1 =
      (H0F G t Vint s s' : ℂ) := by
  rw [fockHam_apply_conf]
  rfl

/-- With an external potential `v`, the lattice DFT Hamiltonian `hamN (H0F …) occF v` is the
restriction of `Σ_ij (-t A + diag v)_ij c_i† c_j + V_int`. -/
theorem hamN_H0F_eq_fock (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : ℝ) {N : ℕ}
    (Vint : Conf M N → ℝ) (v : Fin M → ℝ) (s s' : Conf M N) :
    (oneBody ((-t • G.adjMatrix ℝ + Matrix.diagonal v).map ((↑) : ℝ → ℂ)) + diagExt Vint) s.1 s'.1 =
      (hamN (H0F G t Vint) occF v s s' : ℂ) := by
  rw [fockHam_apply_conf, hamN_H0F]

end DFT.Lattice.Fermions
