/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.StrongPotential.PowerSums

/-!
# Leading coefficients from a finite table

The leading strong-potential coefficient of the free Krylov determinant is `det T`, where
`T y j = T A w d c (ord j) y` are the top coefficients of the matrix powers (`top_coeff_eq_det`).
These satisfy the linear recursion `T_succ`, so in a concrete basis `e : Fin n ≃ C` they are fixed
by a finite table; the columns can be put in the order `0, 1, …, n − 1`, which changes `det T` only
by a sign (`det_equivFin_ne_zero`).

`krylovPoly_ne_zero_of_table`: a table that starts at `e_c`, satisfies the recursion and has
nonzero determinant gives (H*) at `c` for every configuration-diagonal interaction. No sign
condition on the hopping enters; `d` is any function with `d c = 0` that grows by at most one along
the nonzero off-diagonal entries.
-/

namespace DFT

section

open Polynomial Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **The leading coefficient as a determinant of top coefficients.** The coefficient of degree
`Σ ord − Σ d` of the free Krylov determinant along `w` is `det [T A w d c (ord j) y]`. -/
theorem top_coeff_eq_det {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d) {c : C} (hc : d c = 0)
    (w : C → ℝ) (ord : C → ℕ) :
    (kry (Hl A 0 w) c ord).det.coeff (∑ j, ord j - ∑ y, d y) =
      (Matrix.of fun y j => T A w d c (ord j) y).det := by
  simp only [Matrix.det_apply, finsetSum_coeff, kry]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, ← Polynomial.C_eq_intCast,
    coeff_C_mul]
  congr 1
  by_cases hall : ∀ i, d (σ i) ≤ ord i
  · have hsum : ∑ j, ord j - ∑ y, d y = ∑ i, (ord i - d (σ i)) := by
      rw [Finset.sum_tsub_distrib _ (fun i _ => hall i), Equiv.sum_comp σ d]
    rw [hsum, prod_coeff_top _ _ _ (fun i _ => entry_natDegree hL hc 0 w _ _)]
    apply Finset.prod_congr rfl
    intro i _
    simp [T, hall i]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (entry_zero hL hc 0 w hi)]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [T, Nat.not_le.mpr hi]

/-- **Column order.** With `ord` the enumeration `Fintype.equivFin C`, the matrix
`[τ (ord j) y]` has nonzero determinant as soon as `[τ k (e i)]` (columns `k = 0, …, n − 1`, rows
in the order of a basis `e : Fin n ≃ C`) has. -/
theorem det_equivFin_ne_zero {n : ℕ} (e : Fin n ≃ C) (τ : ℕ → C → ℝ)
    (h : (Matrix.of fun i k : Fin n => τ k (e i)).det ≠ 0) :
    (Matrix.of fun y j => τ (Fintype.equivFin C j : ℕ) y).det ≠ 0 := by
  set B : Matrix C C ℝ := Matrix.of fun y j => τ (Fintype.equivFin C j : ℕ) y
  have hn : n = Fintype.card C := by simpa using Fintype.card_congr e
  set g : Fin n ≃ C := (finCongr hn).trans (Fintype.equivFin C).symm
  have hsub : (Matrix.of fun i k : Fin n => τ k (e i)) =
      (B.submatrix e e).submatrix id (g.trans e.symm) := by
    ext i k
    simp [B, g]
  rw [hsub, Matrix.det_permute', Matrix.det_submatrix_equiv_self] at h
  intro h0
  apply h
  rw [h0, mul_zero]

/-- **Top coefficients from a table.** If `Tm` starts at `e_c` and satisfies the recursion
`T_succ` written in the basis `e`, then `T A w d c k (e i) = Tm i k` for `k < n`. -/
theorem T_eq_of_table {n : ℕ} (e : Fin n ≃ C) {A : Matrix C C ℝ} {d : C → ℕ} (hL : Lip A d)
    (w : C → ℝ) {ic : Fin n} (hc : d (e ic) = 0) {Ah : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, A (e i) (e j) = Ah i j) {wh : Fin n → ℝ} (hw : ∀ i, w (e i) = wh i)
    {dh : Fin n → ℕ} (hd : ∀ i, d (e i) = dh i) {Tm : Matrix (Fin n) (Fin n) ℝ}
    (h0 : ∀ i (k : Fin n), (k : ℕ) = 0 → Tm i k = if i = ic then 1 else 0)
    (hs : ∀ i (k k' : Fin n), (k' : ℕ) = k + 1 →
      Tm i k' = wh i * Tm i k + ∑ j, if j ≠ i ∧ dh j + 1 = dh i then Ah i j * Tm j k else 0) :
    ∀ (k : ℕ) (hk : k < n) i, T A w d (e ic) k (e i) = Tm i ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk i
    rw [T_zero w hc, h0 i ⟨0, hk⟩ rfl]
    simp [e.injective.eq_iff]
  | succ k ih =>
    intro hk i
    rw [T_succ w hL hc, hs i ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl, hw, ih (by omega) i]
    congr 1
    rw [← Finset.filter_ne', Finset.sum_filter, ← e.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · subst hji
      simp
    · have hne : e j ≠ e i := fun h => hji (e.injective h)
      simp only [ne_eq, hne, hji, not_false_eq_true, true_and, ite_true, hd, hA]
      split_ifs <;> simp [ih (by omega) j]

variable {V : Type*} [Fintype V]

/-- **(H*) from a table.** Let `e : Fin n ≃ C` be a basis in which the free matrix `A` reads `Ah`,
the energies along `u` read `wh`, and let `dh` grow by at most one along the nonzero off-diagonal
entries of `Ah`, with `dh ic = 0`. If a table `Tm` starts at `e_ic`, satisfies
`Tm i (k + 1) = wh i · Tm i k + Σ_{j ≠ i, dh j + 1 = dh i} Ah i j · Tm j k` and has nonzero
determinant, then the Krylov polynomial of `e ic` is nonzero for every configuration-diagonal
interaction. -/
theorem krylovPoly_ne_zero_of_table {n : ℕ} (e : Fin n ≃ C) {A : Matrix C C ℝ}
    {Ah : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, A (e i) (e j) = Ah i j) (nv : V → C → ℝ)
    (u : V → ℝ) {wh : Fin n → ℝ} (hw : ∀ i, ∑ v, u v * nv v (e i) = wh i) {dh : Fin n → ℕ}
    (hL : ∀ i j, i ≠ j → Ah i j ≠ 0 → dh i ≤ dh j + 1) {ic : Fin n} (hc : dh ic = 0)
    {Tm : Matrix (Fin n) (Fin n) ℝ}
    (h0 : ∀ i (k : Fin n), (k : ℕ) = 0 → Tm i k = if i = ic then 1 else 0)
    (hs : ∀ i (k k' : Fin n), (k' : ℕ) = k + 1 →
      Tm i k' = wh i * Tm i k + ∑ j, if j ≠ i ∧ dh j + 1 = dh i then Ah i j * Tm j k else 0)
    (hdet : Tm.det ≠ 0) (Vint : C → ℝ) :
    krylovPoly (A + Matrix.diagonal Vint) nv (e ic) (fun j => (Fintype.equivFin C j : ℕ)) ≠ 0 := by
  classical
  set d : C → ℕ := fun y => dh (e.symm y)
  have hd : ∀ i, d (e i) = dh i := fun i => by simp [d]
  have hLip : Lip A d := by
    intro y z hyz hAyz
    have h := hL (e.symm y) (e.symm z) (fun h => hyz (e.symm.injective h))
      (by rwa [← hA, e.apply_symm_apply, e.apply_symm_apply])
    simpa [d] using h
  have hc' : d (e ic) = 0 := by rw [hd]; exact hc
  apply krylovPoly_ne_zero_of_top hLip hc' nv u
  rw [top_coeff_eq_det hLip hc']
  apply det_equivFin_ne_zero e
  have hT : (Matrix.of fun i k : Fin n =>
      T A (fun y => ∑ v, u v * nv v y) d (e ic) k (e i)) = Tm := by
    ext i k
    exact T_eq_of_table e hLip _ hc' hA hw hd h0 hs k k.2 i
  rw [hT]
  exact hdet

end

end DFT
