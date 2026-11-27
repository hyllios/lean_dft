/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.Reg

/-!
# Ground-state densities in measure potentials are Hölder continuous of order `5/8`

For `N` interacting bosons or fermions (continuous `w`) in a measure potential, the continuous
density of a ground state satisfies `|ρ̂(t') - ρ̂(t)| ≤ C |t' - t|^{5/8}` (**`rhoHat_holder`**).
A general `H¹₀` density is only `1/2`-Hölder; the extra `1/8` comes from the regularity
`Σ λ^{5/4} c² < ∞` (`summable_lam54`).

The proof: for a finite sine sum `F`, `ρ̂_F(t') - ρ̂_F(t) = N ∫ (F(t') - F(t)) (F(t') + F(t)) dy`;
the trace inequality with `β_k = s_k(t') - s_k(t)`, `|β_k|² ≲ ((k+1)|t' - t|)^{5/4}` and weights
`(k+1)^{5/2}` bounds the first factor by `|t' - t|^{5/8}`. Truncations of the ground state have
uniformly bounded `Σ λ^{5/4} c²`, and their densities converge pointwise.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

lemma sqrt_two_lt : √2 < 1.42 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `|s_k(t') - s_k(t)|² ≤ 3 (5 (k+1) |t' - t|)^{5/4}`. -/
lemma sn_diff_sq_le (k : ℕ) (t t' : ℝ) :
    (sn (k + 1) t' - sn (k + 1) t) ^ 2 ≤ 3 * (5 * (((k : ℝ) + 1) * |t' - t|)) ^ (5 / 4 : ℝ) := by
  set β := |sn (k + 1) t' - sn (k + 1) t|
  have hβ0 : 0 ≤ β := abs_nonneg _
  have hs2 := sqrt_two_lt
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hdiff : β = √2 * |sin (π * ((k + 1 : ℕ) : ℝ) * t') - sin (π * ((k + 1 : ℕ) : ℝ) * t)| := by
    simp only [β, sn]; rw [← mul_sub, abs_mul, abs_of_nonneg hs0]
  have hb1 : β ≤ 3 := by
    rw [hdiff]
    set A := π * ((k + 1 : ℕ) : ℝ) * t'
    set B := π * ((k + 1 : ℕ) : ℝ) * t
    have hA := abs_sin_le_one A
    have hB := abs_sin_le_one B
    have h2 : |sin A - sin B| ≤ 2 := (abs_sub _ _).trans (by linarith)
    calc √2 * |sin A - sin B| ≤ 1.42 * 2 := mul_le_mul hs2.le h2 (abs_nonneg _) (by norm_num)
      _ ≤ 3 := by norm_num
  have hb2 : β ≤ 5 * (((k : ℝ) + 1) * |t' - t|) := by
    rw [hdiff]
    have h1 := abs_sin_sub_sin_le (π * ((k + 1 : ℕ) : ℝ) * t') (π * ((k + 1 : ℕ) : ℝ) * t)
    have e : |π * ((k + 1 : ℕ) : ℝ) * t' - π * ((k + 1 : ℕ) : ℝ) * t| =
        π * (((k : ℝ) + 1) * |t' - t|) := by
      push_cast
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]; ring
    rw [e] at h1
    have hp := pi_lt_d2
    have hk : 0 ≤ ((k : ℝ) + 1) * |t' - t| := by positivity
    calc √2 * |sin (π * ((k + 1 : ℕ) : ℝ) * t') - sin (π * ((k + 1 : ℕ) : ℝ) * t)|
        ≤ √2 * (π * (((k : ℝ) + 1) * |t' - t|)) := mul_le_mul_of_nonneg_left h1 hs0
      _ = (√2 * π) * (((k : ℝ) + 1) * |t' - t|) := by ring
      _ ≤ 5 * (((k : ℝ) + 1) * |t' - t|) := by
          refine mul_le_mul_of_nonneg_right ?_ hk
          nlinarith [pi_pos]
  have e : β ^ 2 = β ^ (3 / 4 : ℝ) * β ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_add' hβ0 (by norm_num), show (3 / 4 : ℝ) + 5 / 4 = 2 by norm_num,
      Real.rpow_two]
  rw [← sq_abs, e]
  have h3 : β ^ (3 / 4 : ℝ) ≤ 3 :=
    (Real.rpow_le_rpow hβ0 hb1 (by norm_num)).trans (by
      calc (3 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3)
  exact mul_le_mul h3 (Real.rpow_le_rpow hβ0 hb2 (by norm_num)) (by positivity) (by norm_num)

/-- `Σ_k 1/(k+1)^{5/4}`. -/
noncomputable def Z54 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (5 / 4 : ℝ)

/-- `Σ_k 1/(k+1)^{5/2}`. -/
noncomputable def Z52 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ)

lemma Z54_nonneg : 0 ≤ Z54 := tsum_nonneg fun k => by positivity
lemma Z52_nonneg : 0 ≤ Z52 := tsum_nonneg fun k => by positivity

/-- The sum `Σ_k β_k² / (k+1)^{5/2}` for differences of sine modes. -/
lemma sum_sn_diff_le (M : ℕ) (t t' : ℝ) :
    ∑ k ∈ Finset.range M, (sn (k + 1) t' - sn (k + 1) t) ^ 2 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ) ≤
      3 * 5 ^ (5 / 4 : ℝ) * Z54 * |t' - t| ^ (5 / 4 : ℝ) := by
  have hb : ∀ k : ℕ, (sn (k + 1) t' - sn (k + 1) t) ^ 2 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ) ≤
      3 * 5 ^ (5 / 4 : ℝ) * |t' - t| ^ (5 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ (5 / 4 : ℝ)) :=
    fun k => by
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have e1 : ((k : ℝ) + 1) ^ (5 / 2 : ℝ) =
          ((k : ℝ) + 1) ^ (5 / 4 : ℝ) * ((k : ℝ) + 1) ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_add hk]; norm_num
      have e2 : (5 * (((k : ℝ) + 1) * |t' - t|)) ^ (5 / 4 : ℝ) =
          5 ^ (5 / 4 : ℝ) * (((k : ℝ) + 1) ^ (5 / 4 : ℝ) * |t' - t| ^ (5 / 4 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hk.le (abs_nonneg _)]
      have hpos : 0 < ((k : ℝ) + 1) ^ (5 / 4 : ℝ) := by positivity
      rw [div_le_iff₀ (by positivity), e1]
      calc (sn (k + 1) t' - sn (k + 1) t) ^ 2 ≤
            3 * (5 * (((k : ℝ) + 1) * |t' - t|)) ^ (5 / 4 : ℝ) := sn_diff_sq_le k t t'
        _ = _ := by rw [e2]; field_simp
  have hsum := summable_inv_rpow (p := 5 / 4) (by norm_num)
  calc _ ≤ ∑ k ∈ Finset.range M,
        3 * 5 ^ (5 / 4 : ℝ) * |t' - t| ^ (5 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ (5 / 4 : ℝ)) :=
        Finset.sum_le_sum fun k _ => hb k
    _ = 3 * 5 ^ (5 / 4 : ℝ) * |t' - t| ^ (5 / 4 : ℝ) *
        ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1) ^ (5 / 4 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 3 * 5 ^ (5 / 4 : ℝ) * |t' - t| ^ (5 / 4 : ℝ) * Z54 :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun k _ => by positivity) (by positivity)
    _ = _ := by ring

lemma sum_sn_add_le (M : ℕ) (t t' : ℝ) :
    ∑ k ∈ Finset.range M, (sn (k + 1) t' + sn (k + 1) t) ^ 2 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ) ≤
      8 * Z52 := by
  have hsum := summable_inv_rpow (p := 5 / 2) (by norm_num)
  have hb : ∀ k : ℕ, (sn (k + 1) t' + sn (k + 1) t) ^ 2 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ) ≤
      8 * (1 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ)) := fun k => by
    rw [← mul_div_assoc, mul_one]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 := abs_sn_le (k + 1) t'
    have h2 := abs_sn_le (k + 1) t
    have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc (sn (k + 1) t' + sn (k + 1) t) ^ 2 = |sn (k + 1) t' + sn (k + 1) t| ^ 2 := (sq_abs _).symm
      _ ≤ (√2 + √2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans
          (add_le_add h1 h2)) 2
      _ = 8 := by nlinarith
  calc _ ≤ ∑ k ∈ Finset.range M, 8 * (1 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ)) :=
        Finset.sum_le_sum fun k _ => hb k
    _ = 8 * ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1) ^ (5 / 2 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 8 * Z52 := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun k _ => by positivity)
        (by norm_num)

/-- The Hölder constant `√(3 · 5^{5/4} Z₅₄ · 8 Z₅₂)`. -/
noncomputable def C58 : ℝ := √(3 * 5 ^ (5 / 4 : ℝ) * Z54 * (8 * Z52))

/-- **Hölder estimate for the density of a finite sine sum**:
`|ρ̂_F(t') - ρ̂_F(t)| ≤ N (Σ λ^{5/4} a²) C |t' - t|^{5/8}`. -/
theorem rhoHat_sumS_holder (hw : Continuous w) (M : ℕ) {a : (Fin (n + 1) → ℕ) → ℝ}
    (ha : ∀ σ m, a (pmI σ m) = ch τ σ * a m) (t t' : Icc (0 : ℝ) 1) :
    |rhoHat τ (sumS M a) t' - rhoHat τ (sumS M a) t| ≤
      (n + 1) * (∑ m ∈ boxI n M, lam m ^ (5 / 4 : ℝ) * a m ^ 2) * C58 *
        |(t' : ℝ) - t| ^ (5 / 8 : ℝ) := by
  have hD := sumS_mem (τ := τ) M ha
  set F := sumS M a
  rw [rhoHat_eq_marg (w := w) hw (Dom_le_DomW hD) (continuous_sumS M a) (Dom_sq_pm hD),
    rhoHat_eq_marg (w := w) hw (Dom_le_DomW hD) (continuous_sumS M a) (Dom_sq_pm hD)]
  set S := ∑ m ∈ boxI n M, lam m ^ (5 / 4 : ℝ) * a m ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ =>
    mul_nonneg (Real.rpow_nonneg (lam_pos' m).le _) (sq_nonneg _)
  set u : (Fin n → ℝ) → ℝ := fun y => F (Fin.cons (t' : ℝ) y) - F (Fin.cons (t : ℝ) y)
  set v : (Fin n → ℝ) → ℝ := fun y => F (Fin.cons (t' : ℝ) y) + F (Fin.cons (t : ℝ) y)
  have hFc : ∀ s : ℝ, Continuous fun y : Fin n → ℝ => F (Fin.cons s y) := fun s =>
    (continuous_sumS M a).comp (continuous_cons_right s)
  have hu : Continuous u := (hFc _).sub (hFc _)
  have hv : Continuous v := (hFc _).add (hFc _)
  have e1 : (∫ y in Cube' n, F (Fin.cons (t' : ℝ) y) ^ 2) -
      ∫ y in Cube' n, F (Fin.cons (t : ℝ) y) ^ 2
      = ∫ y in Cube' n, u y * v y := by
    rw [← integral_sub (f := fun y => F (Fin.cons (t' : ℝ) y) ^ 2)
      (g := fun y => F (Fin.cons (t : ℝ) y) ^ 2) (integrableOn_cube' ((hFc _).pow 2))
      (integrableOn_cube' ((hFc _).pow 2))]
    congr 1; funext y; simp only [u, v]; ring
  have hW : ∀ k : ℕ, 0 < ((k : ℝ) + 1) ^ (5 / 2 : ℝ) := fun k => by positivity
  have hSW : ∑ m ∈ boxI n M, ((m 0 : ℝ) + 1) ^ (5 / 2 : ℝ) * a m ^ 2 ≤ S :=
    Finset.sum_le_sum fun m _ => by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have := rpow_le_lam m (s := 5 / 4) (by norm_num)
      rwa [show 2 * (5 / 4 : ℝ) = 5 / 2 by norm_num] at this
  have hu2 : ∫ y in Cube' n, u y ^ 2 ≤
      S * (3 * 5 ^ (5 / 4 : ℝ) * Z54 * |(t' : ℝ) - t| ^ (5 / 4 : ℝ)) := by
    have e : ∀ y, u y = ∑ m ∈ boxI n M,
        a m * (sn (m 0 + 1) t' - sn (m 0 + 1) t) * smd (Fin.tail m) y := fun y => by
      simp only [u, F, sumS_cons, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp only [e]
    refine (trace_le (M := M) a (fun k => sn (k + 1) t' - sn (k + 1) t) _ hW).trans ?_
    exact mul_le_mul hSW (sum_sn_diff_le M t t') (Finset.sum_nonneg fun k _ =>
      div_nonneg (sq_nonneg _) (hW k).le) hS0
  have hv2 : ∫ y in Cube' n, v y ^ 2 ≤ S * (8 * Z52) := by
    have e : ∀ y, v y = ∑ m ∈ boxI n M,
        a m * (sn (m 0 + 1) t' + sn (m 0 + 1) t) * smd (Fin.tail m) y := fun y => by
      simp only [v, F, sumS_cons, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp only [e]
    refine (trace_le (M := M) a (fun k => sn (k + 1) t' + sn (k + 1) t) _ hW).trans ?_
    exact mul_le_mul hSW (sum_sn_add_le M t t') (Finset.sum_nonneg fun k _ =>
      div_nonneg (sq_nonneg _) (hW k).le) hS0
  have hcs : |∫ y in Cube' n, u y * v y| ≤
      √((∫ y in Cube' n, u y ^ 2) * ∫ y in Cube' n, v y ^ 2) :=
    (abs_integral_le_integral_abs).trans ((integral_abs_mul_le hu hv).trans_eq (by rfl))
  have hZ := Z54_nonneg
  have hZ' := Z52_nonneg
  have hh : 0 ≤ |(t' : ℝ) - t| := abs_nonneg _
  have hsq : √((S * (3 * 5 ^ (5 / 4 : ℝ) * Z54 * |(t' : ℝ) - t| ^ (5 / 4 : ℝ))) *
      (S * (8 * Z52))) = S * C58 * |(t' : ℝ) - t| ^ (5 / 8 : ℝ) := by
    have e : (S * (3 * 5 ^ (5 / 4 : ℝ) * Z54 * |(t' : ℝ) - t| ^ (5 / 4 : ℝ))) * (S * (8 * Z52)) =
        S ^ 2 * (3 * 5 ^ (5 / 4 : ℝ) * Z54 * (8 * Z52)) *
          (|(t' : ℝ) - t| ^ (5 / 8 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (|(t' : ℝ) - t| ^ (5 / 8 : ℝ)) 2, ← Real.rpow_mul hh]
      norm_num; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hS0, Real.sqrt_sq (by positivity), C58]
  rw [← mul_sub, e1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1), mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine hcs.trans ?_
  calc √((∫ y in Cube' n, u y ^ 2) * ∫ y in Cube' n, v y ^ 2)
      ≤ √((S * (3 * 5 ^ (5 / 4 : ℝ) * Z54 * |(t' : ℝ) - t| ^ (5 / 4 : ℝ))) * (S * (8 * Z52))) :=
        Real.sqrt_le_sqrt (mul_le_mul hu2 hv2 (integral_nonneg fun _ => sq_nonneg _)
          (by positivity))
    _ = S * C58 * |(t' : ℝ) - t| ^ (5 / 8 : ℝ) := hsq
    _ = S * (C58 * |(t' : ℝ) - t| ^ (5 / 8 : ℝ)) := by ring

/-! ### Passing to the ground state -/

lemma trunc_eq_sumS (M : ℕ) (Φ : Cfg n → ℝ) : trunc M Φ = sumS M fun m => cN m Φ := rfl

lemma tendsto_SH_sub_trunc {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) :
    Tendsto (fun M => SH (Φ - trunc M Φ)) atTop (𝓝 0) := by
  have h := ((tendsto_sq_sub_trunc hΦ).const_mul ((n : ℝ) + 1)).add (tendsto_kinW_sub_trunc hΦ)
  simpa [SH] using h

/-- **The densities of the truncations converge pointwise.** -/
theorem tendsto_rhoHat_trunc (hw : Continuous w) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    (t : Icc (0 : ℝ) 1) :
    Tendsto (fun M => rhoHat τ (trunc M Φ) t) atTop (𝓝 (rhoHat τ Φ t)) := by
  have hT : ∀ M, trunc M Φ ∈ DomW τ n := trunc_memW hΦ
  set D : ℕ → Cfg n → ℝ := fun M => Φ - trunc M Φ
  have hH := h1W_of_mem hΦ
  have hb : ∀ M, |rhoHat τ (trunc M Φ) t - rhoHat τ Φ t| ≤
      √(SH (D M) * (6 * SH Φ + 4 * SH (D M))) := fun M => by
    have hDm : D M ∈ DomW τ n := sub_mem hΦ (hT M)
    have e := congrArg (fun p : C01 => p t) (rhoHat_sub hw hΦ (hT M))
    simp only [ContinuousMap.sub_apply] at e
    rw [abs_sub_comm, e]
    refine (abs_rhoHat2_le_SH hw hDm (add_mem hΦ (hT M)) t).trans (Real.sqrt_le_sqrt ?_)
    refine mul_le_mul_of_nonneg_left ?_ (SH_nonneg _)
    have h1 := SH_add_le hH (h1W_of_mem (hT M))
    have e2 : trunc M Φ = Φ + -D M := by simp only [D]; abel
    have h2 : SH (trunc M Φ) ≤ 2 * SH Φ + 2 * SH (D M) := by
      rw [e2]
      refine (SH_add_le hH (h1W_of_mem (neg_mem hDm))).trans ?_
      rw [SH_neg (h1W_of_mem hDm)]
    linarith
  have hlim : Tendsto (fun M => √(SH (D M) * (6 * SH Φ + 4 * SH (D M)))) atTop (𝓝 0) := by
    have h := tendsto_SH_sub_trunc hΦ
    have := ((h.mul ((tendsto_const_nhds (x := 6 * SH Φ)).add (h.const_mul 4))).sqrt)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun M => by rw [Real.norm_eq_abs]; exact hb M) hlim

/-- **Ground-state densities in measure potentials are Hölder continuous of order `5/8`.** -/
theorem rhoHat_holder (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN τ w ν Φ) :
    ∃ C, 0 ≤ C ∧ ∀ t t' : Icc (0 : ℝ) 1,
      |rhoHat τ Φ t' - rhoHat τ Φ t| ≤ C * |(t' : ℝ) - t| ^ (5 / 8 : ℝ) := by
  have hs := summable_lam54 hw h
  set S := ∑' m, lam m ^ (5 / 4 : ℝ) * cN m Φ ^ 2
  have hS0 : 0 ≤ S := tsum_nonneg fun m =>
    mul_nonneg (Real.rpow_nonneg (lam_pos' m).le _) (sq_nonneg _)
  have hC : 0 ≤ C58 := Real.sqrt_nonneg _
  refine ⟨(n + 1) * S * C58, by positivity, fun t t' => ?_⟩
  have ha : ∀ σ m, cN (pmI σ m) Φ = ch τ σ * cN m Φ := cN_pmW h.1
  have hM : ∀ M, |rhoHat τ (trunc M Φ) t' - rhoHat τ (trunc M Φ) t| ≤
      (n + 1) * S * C58 * |(t' : ℝ) - t| ^ (5 / 8 : ℝ) := fun M => by
    rw [trunc_eq_sumS]
    refine (rhoHat_sumS_holder hw M ha t t').trans ?_
    have : ∑ m ∈ boxI n M, lam m ^ (5 / 4 : ℝ) * cN m Φ ^ 2 ≤ S :=
      hs.sum_le_tsum _ fun m _ => mul_nonneg (Real.rpow_nonneg (lam_pos' m).le _) (sq_nonneg _)
    gcongr
  have hlim := ((tendsto_rhoHat_trunc hw h.1 t').sub (tendsto_rhoHat_trunc hw h.1 t)).abs
  exact le_of_tendsto' hlim hM

end DFT.Continuum.Line
