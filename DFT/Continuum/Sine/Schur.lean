/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Kernel
import Mathlib.Analysis.MeanInequalities

/-!
# Weighted ℓ² bounds for the potential kernel

All sums here are in `ℝ≥0∞`, so no summability has to be checked.

* `tsum_mul_sq_le`: the weighted Cauchy–Schwarz inequality `(Σ g u)² ≤ (Σ g)(Σ g u²)`.
* `schur`: **the Schur test**. If the rows and columns of `A ≥ 0` have sums at most `R` and `C`,
  then `Σ_i (Σ_j A_ij u_j)² ≤ R C Σ_j u_j²`.
* `tsum_pi_prod`: a sum over `Fin d → ℕ` of a product is the product of the sums.
* `tsum_adm_le`, `tsum_adm_le'`: for fixed `l`, at most `3^(n+1)` indices are admissible, in
  either slot.
* `wt`, `wt_le`: the weight `W(m) = Σ_j (m_j + 1)`, and `W(m') ≤ W(m) (1 + |l|)` when `l` is
  admissible for `(m', m)`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

/-! ### Cauchy–Schwarz and the Schur test -/

/-- **Weighted Cauchy–Schwarz** in `ℝ≥0∞`: `(Σ g u)² ≤ (Σ g)(Σ g u²)`. -/
lemma tsum_mul_sq_le {ι : Type*} (g u : ι → ℝ≥0∞) :
    (∑' i, g i * u i) ^ 2 ≤ (∑' i, g i) * ∑' i, g i * u i ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  set X := (∑' i, g i) ^ (1 / 2 : ℝ) * (∑' i, g i * u i ^ 2) ^ (1 / 2 : ℝ)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, g i * u i ≤ X := by
    intro s
    have h := ENNReal.inner_le_Lp_mul_Lq s (fun i => g i ^ (1 / 2 : ℝ))
      (fun i => g i ^ (1 / 2 : ℝ) * u i) hpq
    have e1 : ∀ i, (g i ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = g i := fun i => by
      rw [← ENNReal.rpow_mul]; norm_num
    have e2 : ∀ i, (g i ^ (1 / 2 : ℝ) * u i) ^ (2 : ℝ) = g i * u i ^ 2 := fun i => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e1, ENNReal.rpow_two]
    have e3 : ∀ i, g i ^ (1 / 2 : ℝ) * (g i ^ (1 / 2 : ℝ) * u i) = g i * u i := fun i => by
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
    simp only [e1, e2, e3] at h
    refine h.trans (mul_le_mul' ?_ ?_)
    · exact ENNReal.rpow_le_rpow (sum_le_tsum s) (by norm_num)
    · exact ENNReal.rpow_le_rpow (sum_le_tsum s) (by norm_num)
  have h1 : ∑' i, g i * u i ≤ X := by
    rw [tsum_eq_iSup_sum]; exact iSup_le hfin
  calc (∑' i, g i * u i) ^ 2 ≤ X ^ 2 := pow_le_pow_left' h1 2
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

/-- **Cauchy–Schwarz** in `ℝ≥0∞`: `(Σ a b)² ≤ (Σ a²)(Σ b²)`. -/
lemma tsum_mul_le_sq {ι : Type*} (a b : ι → ℝ≥0∞) :
    (∑' i, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * ∑' i, b i ^ 2 := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  set X := (∑' i, a i ^ 2) ^ (1 / 2 : ℝ) * (∑' i, b i ^ 2) ^ (1 / 2 : ℝ)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, a i * b i ≤ X := by
    intro s
    have h := ENNReal.inner_le_Lp_mul_Lq s a b hpq
    simp only [ENNReal.rpow_two] at h
    refine h.trans (mul_le_mul' ?_ ?_)
    · exact ENNReal.rpow_le_rpow (sum_le_tsum s) (by norm_num)
    · exact ENNReal.rpow_le_rpow (sum_le_tsum s) (by norm_num)
  have h1 : ∑' i, a i * b i ≤ X := by
    rw [tsum_eq_iSup_sum]; exact iSup_le hfin
  calc (∑' i, a i * b i) ^ 2 ≤ X ^ 2 := pow_le_pow_left' h1 2
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

/-- **The Schur test.** -/
lemma schur {ι κ : Type*} (A : ι → κ → ℝ≥0∞) (u : κ → ℝ≥0∞) {R C : ℝ≥0∞}
    (hrow : ∀ i, ∑' j, A i j ≤ R) (hcol : ∀ j, ∑' i, A i j ≤ C) :
    ∑' i, (∑' j, A i j * u j) ^ 2 ≤ R * C * ∑' j, u j ^ 2 := by
  calc ∑' i, (∑' j, A i j * u j) ^ 2 ≤ ∑' i, R * ∑' j, A i j * u j ^ 2 :=
        tsum_le_tsum fun i => (tsum_mul_sq_le _ _).trans (mul_le_mul_left (hrow i) _)
    _ = R * ∑' j, u j ^ 2 * ∑' i, A i j := by
        rw [ENNReal.tsum_mul_left, tsum_comm]
        congr 1; congr 1; funext j
        rw [← ENNReal.tsum_mul_left]; congr 1; funext i; ring
    _ ≤ R * ∑' j, u j ^ 2 * C := by gcongr with j; exact hcol j
    _ = R * C * ∑' j, u j ^ 2 := by rw [ENNReal.tsum_mul_right]; ring

/-! ### Sums over multi-indices -/

/-- A sum over `Fin d → ℕ` of a product is the product of the sums. -/
lemma tsum_pi_prod : ∀ (d : ℕ) (f : Fin d → ℕ → ℝ≥0∞),
    ∑' m : Fin d → ℕ, ∏ j, f j (m j) = ∏ j, ∑' k, f j k := by
  intro d
  induction d with
  | zero => intro f; simp
  | succ d ih =>
    intro f
    rw [Fin.prod_univ_succ, ← ih (fun j => f j.succ), ← ENNReal.tsum_mul_right]
    simp only [← ENNReal.tsum_mul_left]
    rw [← tsum_prod' (f := fun p : ℕ × (Fin d → ℕ) => f 0 p.1 * ∏ j, f j.succ (p.2 j)),
      ← (Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)).symm.tsum_eq]
    congr 1; funext m
    simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]

lemma tsum_ite_eq_le (c : ℕ) : ∑' k : ℕ, (if k = c then (1 : ℝ≥0∞) else 0) ≤ 1 := by
  rw [tsum_ite_eq]

lemma tsum_adm1_le (a l : ℕ) : ∑' k : ℕ, (if adm1 a l (k + 1) then (1 : ℝ≥0∞) else 0) ≤ 3 := by
  calc ∑' k : ℕ, (if adm1 a l (k + 1) then (1 : ℝ≥0∞) else 0)
      ≤ ∑' k : ℕ, ((if k = a - 1 - l then 1 else 0) + (if k = a + l - 1 then 1 else 0) +
          (if k = l - a - 1 then 1 else 0)) := by
        refine tsum_le_tsum fun k => ?_
        unfold adm1
        split_ifs <;> (simp_all; try omega)
    _ ≤ 1 + 1 + 1 := by
        rw [tsum_add, tsum_add]
        gcongr <;> exact tsum_ite_eq_le _
    _ = 3 := by norm_num

lemma tsum_adm1_le' (l b : ℕ) : ∑' k : ℕ, (if adm1 (k + 1) l b then (1 : ℝ≥0∞) else 0) ≤ 3 := by
  calc ∑' k : ℕ, (if adm1 (k + 1) l b then (1 : ℝ≥0∞) else 0)
      ≤ ∑' k : ℕ, ((if k = b + l - 1 then 1 else 0) + (if k = b - 1 - l then 1 else 0) +
          (if k = l - b - 1 then 1 else 0)) := by
        refine tsum_le_tsum fun k => ?_
        unfold adm1
        split_ifs <;> (simp_all; try omega)
    _ ≤ 1 + 1 + 1 := by
        rw [tsum_add, tsum_add]
        gcongr <;> exact tsum_ite_eq_le _
    _ = 3 := by norm_num

variable {n : ℕ}

lemma ite_adm (m' l m : Fin (n + 1) → ℕ) :
    (if adm m' l m then (1 : ℝ≥0∞) else 0) =
      ∏ j, (if adm1 (m' j + 1) (l j) (m j + 1) then (1 : ℝ≥0∞) else 0) := by
  by_cases h : adm m' l m
  · rw [ite_eq_left h]; exact (Finset.prod_eq_one fun j _ => ite_eq_left (h j)).symm
  · rw [ite_eq_right h]
    simp only [adm, not_forall] at h
    obtain ⟨j, hj⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)).symm

/-- At most `3^(n+1)` indices `m` are admissible for fixed `m'` and `l`. -/
lemma tsum_adm_le (m' l : Fin (n + 1) → ℕ) :
    ∑' m, (if adm m' l m then (1 : ℝ≥0∞) else 0) ≤ 3 ^ (n + 1) := by
  simp only [ite_adm]
  rw [tsum_pi_prod (n + 1) (fun j k => if adm1 (m' j + 1) (l j) (k + 1) then 1 else 0)]
  calc ∏ j, ∑' k, (if adm1 (m' j + 1) (l j) (k + 1) then (1 : ℝ≥0∞) else 0)
      ≤ ∏ _j : Fin (n + 1), (3 : ℝ≥0∞) := Finset.prod_le_prod fun j _ => tsum_adm1_le _ _
    _ = 3 ^ (n + 1) := by simp

/-- At most `3^(n+1)` indices `m'` are admissible for fixed `l` and `m`. -/
lemma tsum_adm_le' (l m : Fin (n + 1) → ℕ) :
    ∑' m', (if adm m' l m then (1 : ℝ≥0∞) else 0) ≤ 3 ^ (n + 1) := by
  simp only [ite_adm]
  rw [tsum_pi_prod (n + 1) (fun j k => if adm1 (k + 1) (l j) (m j + 1) then 1 else 0)]
  calc ∏ j, ∑' k, (if adm1 (k + 1) (l j) (m j + 1) then (1 : ℝ≥0∞) else 0)
      ≤ ∏ _j : Fin (n + 1), (3 : ℝ≥0∞) := Finset.prod_le_prod fun j _ => tsum_adm1_le' _ _
    _ = 3 ^ (n + 1) := by simp

/-! ### Weights -/

/-- The weight `W(m) = Σ_j (m_j + 1)`. -/
def wt (m : Fin (n + 1) → ℕ) : ℕ := ∑ j, (m j + 1)

/-- The size `|l| = Σ_j l_j` of a cosine index. -/
def sz (l : Fin (n + 1) → ℕ) : ℕ := ∑ j, l j

lemma one_le_wt (m : Fin (n + 1) → ℕ) : 1 ≤ wt m :=
  le_trans (by simp) (Finset.single_le_sum (fun j _ => Nat.zero_le (m j + 1)) (Finset.mem_univ 0))

lemma wt_le {m' l m : Fin (n + 1) → ℕ} (h : adm m' l m) : wt m' ≤ wt m * (1 + sz l) := by
  have h1 : wt m' ≤ wt m + sz l := by
    simp only [wt, sz, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => adm1_le (h j)
  have h2 := one_le_wt m
  nlinarith

end DFT.Continuum.Sine
