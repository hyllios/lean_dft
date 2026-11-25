/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureHKgen

/-!
# Regularity of interacting ground states in measure potentials: finite sine sums

Tools for the `H^{1 + 1/4}` regularity of ground states of `N` interacting particles in a measure
potential (`Line/MeasureHolder`):

* `sum_boxI_cons`: a sum over the box of multi-indices splits into the first index and the rest.
* **`trace_le`**: the trace inequality for finite sine sums `F = Σ_m e_m s_m`: for any weights
  `W_k > 0` and numbers `β_k`,
  `∫ (Σ_m e_m β_{m₀} s_{m'}(y))² dy ≤ (Σ_m W_{m₀} e_m²) (Σ_k β_k² / W_k)`.
  With `β_k = s_k(t)` this bounds `∫ F(t, y)² dy`; with `β_k = s_k(t + h) - s_k(t)` it bounds
  differences.
* `sumS M a = Σ_{m ∈ box} a_m s_m`, its membership in `Dom τ n` for coefficients of the right
  symmetry (`sumS_mem`), and its pairings `∫ Φ sumS` and `h0W Φ sumS` (`h0W_sumS`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ}

/-- The box of multi-indices of the other `n` particles. -/
def boxT (n M : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun _ => Finset.range M

lemma sum_boxI_cons {M : ℕ} (f : (Fin (n + 1) → ℕ) → ℝ) :
    ∑ m ∈ boxI n M, f m = ∑ k ∈ Finset.range M, ∑ μ ∈ boxT n M, f (Fin.cons k μ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun m => (m 0, Fin.tail m)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_boxI] at hm
    simp only [Finset.mem_product, boxT, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨hm 0, fun i => hm _⟩
  · rintro ⟨k, μ⟩ hp
    simp only [Finset.mem_product, boxT, Fintype.mem_piFinset, Finset.mem_range] at hp
    rw [mem_boxI]
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hp.1
    · simpa using hp.2 i
  · intro m _; simp
  · rintro ⟨k, μ⟩ _; simp
  · intro m _; simp

lemma setIntegral_cube'_eq (f : (Fin n → ℝ) → ℝ) : ∫ y in Cube' n, f y = ∫ y, f y ∂piM n := by
  rw [piM, volume_pi, Measure.restrict_pi_pi]

lemma smd_orthonormal' (μ μ' : Fin n → ℕ) :
    ∫ y in Cube' n, smd μ y * smd μ' y = if μ = μ' then 1 else 0 := by
  rw [setIntegral_cube'_eq, smd_orthonormal]

/-- `∫ (Σ_μ A_μ s_μ)² = Σ_μ A_μ²` on the cube. -/
lemma integral_sum_smd_sq (T : Finset (Fin n → ℕ)) (A : (Fin n → ℕ) → ℝ) :
    ∫ y in Cube' n, (∑ μ ∈ T, A μ * smd μ y) ^ 2 = ∑ μ ∈ T, A μ ^ 2 := by
  have e : (fun y => (∑ μ ∈ T, A μ * smd μ y) ^ 2) =
      fun y => ∑ μ ∈ T, ∑ μ' ∈ T, A μ * A μ' * (smd μ y * smd μ' y) := by
    funext y; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e, integral_finsetSum (f := fun μ y => ∑ μ' ∈ T, A μ * A μ' * (smd μ y * smd μ' y)) _
    fun μ _ => integrable_finsetSum _ fun μ' _ =>
    (integrableOn_cube' ((continuous_smd μ).mul (continuous_smd μ'))).const_mul _]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [integral_finsetSum (f := fun μ' y => A μ * A μ' * (smd μ y * smd μ' y)) _ fun μ' _ =>
    (integrableOn_cube' ((continuous_smd μ).mul (continuous_smd μ'))).const_mul _]
  simp only [integral_const_mul, smd_orthonormal', mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq _ _ (fun μ' => A μ * A μ'), ite_eq_left hμ, sq]

/-- **The trace inequality for finite sine sums.** -/
theorem trace_le {M : ℕ} (e : (Fin (n + 1) → ℕ) → ℝ) (β W : ℕ → ℝ) (hW : ∀ k, 0 < W k) :
    ∫ y in Cube' n, (∑ m ∈ boxI n M, e m * β (m 0) * smd (Fin.tail m) y) ^ 2 ≤
      (∑ m ∈ boxI n M, W (m 0) * e m ^ 2) * ∑ k ∈ Finset.range M, β k ^ 2 / W k := by
  set A : (Fin n → ℕ) → ℝ := fun μ => ∑ k ∈ Finset.range M, e (Fin.cons k μ) * β k
  have hG : ∀ y, ∑ m ∈ boxI n M, e m * β (m 0) * smd (Fin.tail m) y =
      ∑ μ ∈ boxT n M, A μ * smd μ y := fun y => by
    rw [sum_boxI_cons, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [A, Fin.cons_zero, Fin.tail_cons, Finset.sum_mul]
  simp only [hG]
  rw [integral_sum_smd_sq, sum_boxI_cons, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun μ _ => ?_
  simp only [Fin.cons_zero]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M)
    (fun k => √(W k) * e (Fin.cons k μ)) (fun k => β k / √(W k))
  have e1 : ∀ k, √(W k) * e (Fin.cons k μ) * (β k / √(W k)) = e (Fin.cons k μ) * β k :=
    fun k => by
      have : 0 < √(W k) := Real.sqrt_pos.2 (hW k)
      field_simp
  have e2 : ∀ k, (√(W k) * e (Fin.cons k μ)) ^ 2 = W k * e (Fin.cons k μ) ^ 2 := fun k => by
    rw [mul_pow, Real.sq_sqrt (hW k).le]
  have e3 : ∀ k, (β k / √(W k)) ^ 2 = β k ^ 2 / W k := fun k => by
    rw [div_pow, Real.sq_sqrt (hW k).le]
  simp only [e1, e2, e3] at hcs
  exact hcs

/-! ### Finite sine sums as test functions -/

/-- The finite sine sum `Σ_{m ∈ box} a_m s_m`. -/
noncomputable def sumS (M : ℕ) (a : (Fin (n + 1) → ℕ) → ℝ) (x : Cfg n) : ℝ :=
  ∑ m ∈ boxI n M, a m * smd m x

lemma continuous_sumS (M : ℕ) (a : (Fin (n + 1) → ℕ) → ℝ) : Continuous (sumS M a) :=
  continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_smd m)

lemma smd_cons' (m : Fin (n + 1) → ℕ) (t : ℝ) (y : Fin n → ℝ) :
    smd m (Fin.cons t y) = sn (m 0 + 1) t * smd (Fin.tail m) y := by
  have := smd_cons (m 0) (Fin.tail m) t y
  rwa [Fin.cons_self_tail] at this

lemma sumS_cons (M : ℕ) (a : (Fin (n + 1) → ℕ) → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    sumS M a (Fin.cons t y) = ∑ m ∈ boxI n M, a m * sn (m 0 + 1) t * smd (Fin.tail m) y := by
  simp only [sumS, smd_cons', mul_assoc]

/-- A finite sine sum with coefficients of the right exchange symmetry is a `C²` state. -/
theorem sumS_mem {τ : Stat} (M : ℕ) {a : (Fin (n + 1) → ℕ) → ℝ}
    (ha : ∀ σ m, a (pmI σ m) = ch τ σ * a m) : sumS M a ∈ Dom τ n := by
  refine ⟨ContDiff.sum fun m _ => contDiff_const.mul (contDiff_smd m), fun σ x => ?_,
    fun x k hk => ?_⟩
  · simp only [sumS, smd_pm', Finset.mul_sum]
    refine Finset.sum_nbij' (pmI σ⁻¹) (pmI σ) (fun m hm => (pmI_mem_boxI σ⁻¹).2 hm)
      (fun m hm => (pmI_mem_boxI σ).2 hm) (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
    · rw [pmI_pmI, inv_mul_cancel, pmI_one]
    · rw [pmI_pmI, mul_inv_cancel, pmI_one]
    · have h := ha σ (pmI σ⁻¹ m)
      rw [pmI_pmI, inv_mul_cancel, pmI_one] at h
      rw [h]; ring
  · simp only [sumS, smd_face _ x k hk, mul_zero, Finset.sum_const_zero]

lemma integral_mul_sumS {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (M : ℕ)
    (a : (Fin (n + 1) → ℕ) → ℝ) :
    ∫ x, Φ x * sumS M a x ∂μN n = ∑ m ∈ boxI n M, a m * cN m Φ := by
  have e : (fun x => Φ x * sumS M a x) = fun x => ∑ m ∈ boxI n M, a m * (smd m x * Φ x) := by
    funext x; simp only [sumS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, integral_finsetSum _ fun m _ =>
    (int_mul_L2 (memLp_cont (continuous_smd m)) hΦ).const_mul _]
  simp only [integral_const_mul, cN_eq]

/-- **The energy form against a finite sine sum.** -/
theorem h0W_sumS {w : Cfg n → ℝ} (hw : Continuous w) {Φ : Cfg n → ℝ} (hΦ : H1W Φ) (M : ℕ)
    (a : (Fin (n + 1) → ℕ) → ℝ) :
    h0W n w Φ (sumS M a) = ∑ m ∈ boxI n M, a m * h0W n w Φ (smd m) := by
  have hd : ∀ k, dW k (sumS M a) =ᵐ[μN n]
      fun x => ∑ m ∈ boxI n M, a m * (π * (m k + 1) * cmd k m x) := fun k =>
    dW_ae_eq (IsWD.sum (boxI n M) (fun m _ => (memLp_cont (continuous_smd m)).const_mul _)
      (fun m _ => IsWD.const_mul (a m) (isWD_smd k m))).2
  have hk : ∀ k, ∫ x, dW k Φ x * dW k (sumS M a) x ∂μN n =
      ∑ m ∈ boxI n M, a m * ∫ x, dW k Φ x * dW k (smd m) x ∂μN n := fun k => by
    rw [integral_congr_ae ((hd k).mono fun x hx => by
      simp only [hx, Finset.mul_sum] : (fun x => dW k Φ x * dW k (sumS M a) x) =ᵐ[μN n]
        fun x => ∑ m ∈ boxI n M, dW k Φ x * (a m * (π * (m k + 1) * cmd k m x))),
      integral_finsetSum (f := fun m x => dW k Φ x * (a m * (π * (m k + 1) * cmd k m x))) _
        fun m _ => int_mul_L2 (memLp_dW_H hΦ k)
        (memLp_cont (continuous_const.mul ((contDiff_cmd k m).continuous.const_mul _)))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [dW_ae_eq (isWD_smd k m)] with x hx
    rw [hx]; ring
  have hwt : ∫ x, w x * (Φ x * sumS M a x) ∂μN n =
      ∑ m ∈ boxI n M, a m * ∫ x, w x * (Φ x * smd m x) ∂μN n := by
    obtain ⟨C, hC⟩ := ae_bound_cont hw
    have e : (fun x => w x * (Φ x * sumS M a x)) =
        fun x => ∑ m ∈ boxI n M, a m * (w x * (Φ x * smd m x)) := by
      funext x; simp only [sumS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, integral_finsetSum _ fun m _ => ((int_mul_L2 hΦ.1
      (memLp_cont (continuous_smd m))).bdd_mul hw.aestronglyMeasurable hC).const_mul _]
    simp only [integral_const_mul]
  simp only [h0W, hk, hwt]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum, ← mul_add]

/-! ### Elementary bounds -/

lemma sq0_le_lam (m : Fin (n + 1) → ℕ) : ((m 0 : ℝ) + 1) ^ 2 ≤ lam m := by
  have h1 : ((m 0 : ℝ) + 1) ^ 2 ≤ (ksq m : ℝ) := by
    have : (m 0 + 1) ^ 2 ≤ ksq m :=
      Finset.single_le_sum (f := fun j => (m j + 1) ^ 2) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ 0)
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ π ^ 2 := by nlinarith [pi_gt_three]
  rw [lam]
  nlinarith [sq_nonneg ((m 0 : ℝ) + 1)]

lemma one_le_lam (m : Fin (n + 1) → ℕ) : 1 ≤ lam m :=
  le_trans (by nlinarith [(m 0).cast_nonneg (α := ℝ)]) (sq0_le_lam m)

lemma lam_pos' (m : Fin (n + 1) → ℕ) : 0 < lam m := lt_of_lt_of_le one_pos (one_le_lam m)

/-- `(m₀ + 1)^{2s} ≤ λ_m^s`. -/
lemma rpow_le_lam (m : Fin (n + 1) → ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ((m 0 : ℝ) + 1) ^ (2 * s) ≤ lam m ^ s := by
  rw [Real.rpow_mul (by positivity), Real.rpow_two]
  exact Real.rpow_le_rpow (by positivity) (sq0_le_lam m) hs

lemma summable_inv_rpow {p : ℝ} (hp : 1 < p) :
    Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ p := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 hp)
  simpa using this

/-! ### `H^{1 + 1/4}` regularity of ground states in measure potentials -/

variable {τ : Stat} {w : Cfg n → ℝ}

/-- The weights `λ^{-3/4}(λ - E)`. -/
noncomputable def fW (E : ℝ) (m : Fin (n + 1) → ℕ) : ℝ := lam m ^ (-(3 / 4 : ℝ)) * (lam m - E)

lemma fW_pm (E : ℝ) (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) :
    fW E (pmI σ m) = fW E m := by simp only [fW, lam_pm]

/-- The constant of the trace inequality, `Σ_k 2 / (k+1)^{3/2}`. -/
noncomputable def Z32 : ℝ := ∑' k : ℕ, 2 / ((k : ℝ) + 1) ^ (3 / 2 : ℝ)

lemma summable_Z32 : Summable fun k : ℕ => 2 / ((k : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  have := (summable_inv_rpow (p := 3 / 2) (by norm_num)).mul_left 2
  simpa [div_eq_mul_inv] using this

/-- **The density of a finite sine sum is bounded by its `H^{3/4}`-type size in `x₀`.** -/
theorem rhoHat_sumS_le (hw : Continuous w) (M : ℕ) {a : (Fin (n + 1) → ℕ) → ℝ}
    (ha : ∀ σ m, a (pmI σ m) = ch τ σ * a m) (t : Icc (0 : ℝ) 1) :
    rhoHat τ (sumS M a) t ≤ (n + 1) * (Z32 * ∑ m ∈ boxI n M, lam m ^ (3 / 4 : ℝ) * a m ^ 2) := by
  have hD := sumS_mem (τ := τ) M ha
  rw [rhoHat_eq_marg (w := w) hw (Dom_le_DomW hD) (continuous_sumS M a) (Dom_sq_pm hD)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [sumS_cons]
  have hW : ∀ k : ℕ, 0 < ((k : ℝ) + 1) ^ (3 / 2 : ℝ) := fun k => by positivity
  have htr := trace_le (M := M) a (fun k => sn (k + 1) t) _ hW
  refine htr.trans ?_
  rw [mul_comm Z32]
  refine mul_le_mul (Finset.sum_le_sum fun m _ => ?_) ?_ (Finset.sum_nonneg fun k _ => ?_)
    (Finset.sum_nonneg fun m _ => mul_nonneg (Real.rpow_nonneg (lam_pos' m).le _) (sq_nonneg _))
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := rpow_le_lam m (s := 3 / 4) (by norm_num)
    rwa [show 2 * (3 / 4 : ℝ) = 3 / 2 by norm_num] at this
  · refine (Finset.sum_le_sum fun k _ => ?_).trans
      (summable_Z32.sum_le_tsum _ fun k _ => by positivity)
    refine div_le_div_of_nonneg_right ?_ (hW k).le
    have := abs_sn_le (k + 1) t
    calc sn (k + 1) t ^ 2 = |sn (k + 1) t| ^ 2 := (sq_abs _).symm
      _ ≤ √2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = 2 := Real.sq_sqrt (by norm_num)
  · exact div_nonneg (sq_nonneg _) (hW k).le

lemma rpow_neg34_le_one (m : Fin (n + 1) → ℕ) : lam m ^ (-(3 / 4 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_lam m) (by norm_num)

lemma rpow_neg34_nonneg (m : Fin (n + 1) → ℕ) : 0 ≤ lam m ^ (-(3 / 4 : ℝ)) :=
  Real.rpow_nonneg (lam_pos' m).le _

lemma rpow34_mul_neg34 (m : Fin (n + 1) → ℕ) :
    lam m ^ (3 / 4 : ℝ) * lam m ^ (-(3 / 4 : ℝ)) = 1 := by
  rw [Real.rpow_neg (lam_pos' m).le, mul_inv_cancel₀ (Real.rpow_pos_of_pos (lam_pos' m) _).ne']

lemma le_sq_of_le_mul_sqrt {X K : ℝ} (hX : 0 ≤ X) (h : X ≤ K * √X) : X ≤ K ^ 2 := by
  set s := √X
  have hs : 0 ≤ s := Real.sqrt_nonneg X
  have hs2 : s ^ 2 = X := Real.sq_sqrt hX
  rcases hs.lt_or_eq with hpos | h0
  · have : s ≤ K := by
      rw [← hs2, sq] at h
      exact le_of_mul_le_mul_right h hpos
    rw [← hs2]; exact pow_le_pow_left₀ hs this 2
  · have : X = 0 := by rw [← hs2, ← h0]; ring
    rw [this]; positivity

/-- **`H^{1 + 1/4}` regularity in `x₀`**: the sine coefficients of a ground state of `N`
interacting particles in a measure potential satisfy `Σ_m λ_m^{5/4} c_m² < ∞`. -/
theorem summable_lam54 (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN τ w ν Φ) :
    Summable fun m => lam m ^ (5 / 4 : ℝ) * cN m Φ ^ 2 := by
  set E := QMN τ w ν Φ
  set g : (Fin (n + 1) → ℕ) → ℝ :=
    fun m => lam m ^ (-(3 / 4 : ℝ)) * (lam m - E) ^ 2 * cN m Φ ^ 2
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    have := rpow_neg34_nonneg m
    simp only [g]; positivity
  set a : (Fin (n + 1) → ℕ) → ℝ := fun m => fW E m * cN m Φ
  have ha : ∀ σ m, a (pmI σ m) = ch τ σ * a m := fun σ m => by
    simp only [a, fW_pm, cN_pmW h.1]; ring
  have hH := h1W_of_mem h.1
  set R := ‖rhoHat τ Φ‖
  set Bw := ∫ x, (w x * Φ x) ^ 2 ∂μN n
  have hBw : 0 ≤ Bw := integral_nonneg fun _ => sq_nonneg _
  set A := R * ((n + 1) * Z32)
  have hZ : 0 ≤ Z32 := tsum_nonneg fun k => by positivity
  have hA : 0 ≤ A := by positivity
  set K := √Bw + ‖ν‖ * √A
  have hpar := parsevalW (memLp_mul_cont hw h.1.1)
  have key : ∀ M, ∑ m ∈ boxI n M, g m ≤ K ^ 2 := by
    intro M
    set X := ∑ m ∈ boxI n M, g m
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun m _ => hg0 m
    set Ψ := sumS M a
    have hΨ : Ψ ∈ DomW τ n := Dom_le_DomW (sumS_mem M ha)
    set wc : (Fin (n + 1) → ℕ) → ℝ := fun m => ∫ x, w x * (Φ x * smd m x) ∂μN n
    have hel := euler_lagrangeN hw h hΨ
    rw [h0W_sumS hw hH, integral_mul_sumS h.1.1] at hel
    simp only [h0W_smd hH] at hel
    have e1 : ∑ m ∈ boxI n M, a m * (lam m * cN m Φ + wc m) =
        X + E * ∑ m ∈ boxI n M, a m * cN m Φ + ∑ m ∈ boxI n M, a m * wc m := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [g, a, fW]; ring
    have hX : X = -(∑ m ∈ boxI n M, a m * wc m) - ν (rhoHat2 τ Φ Ψ) := by
      have := e1; simp only [wc] at this; linarith
    -- the interaction term
    have ha2 : ∑ m ∈ boxI n M, a m ^ 2 ≤ X := Finset.sum_le_sum fun m _ => by
      simp only [a, g, fW]
      have h1 := rpow_neg34_le_one m
      have h0 := rpow_neg34_nonneg m
      have : 0 ≤ (lam m - E) ^ 2 * cN m Φ ^ 2 := by positivity
      calc (lam m ^ (-(3 / 4 : ℝ)) * (lam m - E) * cN m Φ) ^ 2 =
            lam m ^ (-(3 / 4 : ℝ)) * lam m ^ (-(3 / 4 : ℝ)) * ((lam m - E) ^ 2 * cN m Φ ^ 2) := by
            ring
        _ ≤ lam m ^ (-(3 / 4 : ℝ)) * 1 * ((lam m - E) ^ 2 * cN m Φ ^ 2) := by gcongr
        _ = _ := by ring
    have hwc2 : ∑ m ∈ boxI n M, wc m ^ 2 ≤ Bw := by
      have e : ∀ m, wc m = cN m (fun x => w x * Φ x) := fun m => by
        simp only [wc, cN_eq]; congr 1; funext x; ring
      simp only [e]
      exact sum_le_hasSum _ (fun m _ => sq_nonneg _) hpar
    have hT1 : |∑ m ∈ boxI n M, a m * wc m| ≤ √X * √Bw := by
      rw [← Real.sqrt_mul hX0]
      refine Real.abs_le_sqrt ?_
      exact (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (mul_le_mul ha2 hwc2
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) hX0)
    -- the measure term
    have hρΨ : ∀ t, rhoHat τ Ψ t ≤ (n + 1) * (Z32 * X) := fun t => by
      refine (rhoHat_sumS_le hw M ha t).trans_eq ?_
      congr 2
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [a, g, fW]
      have := rpow34_mul_neg34 m
      calc lam m ^ (3 / 4 : ℝ) * (lam m ^ (-(3 / 4 : ℝ)) * (lam m - E) * cN m Φ) ^ 2 =
          (lam m ^ (3 / 4 : ℝ) * lam m ^ (-(3 / 4 : ℝ))) *
            (lam m ^ (-(3 / 4 : ℝ)) * (lam m - E) ^ 2 * cN m Φ ^ 2) := by ring
        _ = _ := by rw [this, one_mul]
    have hρ2 : ‖rhoHat2 τ Φ Ψ‖ ≤ √A * √X := by
      rw [← Real.sqrt_mul hA]
      refine (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2 fun t => ?_
      rw [Real.norm_eq_abs]
      refine (abs_rhoHat2_le hw h.1 hΨ t).trans (Real.sqrt_le_sqrt ?_)
      have h1 : rhoHat τ Φ t ≤ R :=
        (le_abs_self _).trans ((rhoHat τ Φ).norm_coe_le_norm t)
      calc rhoHat τ Φ t * rhoHat τ Ψ t ≤ R * ((n + 1) * (Z32 * X)) :=
            mul_le_mul h1 (hρΨ t) (rhoHat_nonneg τ Ψ t) (by positivity)
        _ = A * X := by simp only [A]; ring
    have hT2 : |ν (rhoHat2 τ Φ Ψ)| ≤ ‖ν‖ * (√A * √X) := by
      rw [← Real.norm_eq_abs]
      exact (ν.le_opNorm _).trans (mul_le_mul_of_nonneg_left hρ2 (norm_nonneg _))
    have hXK : X ≤ K * √X := by
      have := neg_abs_le (∑ m ∈ boxI n M, a m * wc m)
      have := neg_abs_le (ν (rhoHat2 τ Φ Ψ))
      have e : K * √X = √X * √Bw + ‖ν‖ * (√A * √X) := by simp only [K]; ring
      rw [e]; linarith
    exact le_sq_of_le_mul_sqrt hX0 hXK
  have hgs : Summable g := summable_of_sum_le hg0 fun s => by
    obtain ⟨M, hM⟩ := (tendsto_boxI.eventually (eventually_ge_atTop s)).exists
    exact (Finset.sum_le_sum_of_subset_of_nonneg hM fun i _ _ => hg0 i).trans (key M)
  have hc2 := (parsevalW h.1.1).summable
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (Real.rpow_nonneg (lam_pos' m).le _)
    (sq_nonneg _)) (fun m => ?_) ((hgs.mul_left 2).add (hc2.mul_left (2 * E ^ 2)))
  have hl := lam_pos' m
  have e : lam m ^ (5 / 4 : ℝ) = lam m ^ (-(3 / 4 : ℝ)) * lam m ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hl]; norm_num
  have h0 := rpow_neg34_nonneg m
  have h1 := rpow_neg34_le_one m
  rw [e]
  have hq : lam m ^ 2 ≤ 2 * (lam m - E) ^ 2 + 2 * E ^ 2 := by nlinarith [sq_nonneg (lam m - 2 * E)]
  simp only [g]
  calc lam m ^ (-(3 / 4 : ℝ)) * lam m ^ 2 * cN m Φ ^ 2
      ≤ lam m ^ (-(3 / 4 : ℝ)) * (2 * (lam m - E) ^ 2 + 2 * E ^ 2) * cN m Φ ^ 2 := by gcongr
    _ = 2 * (lam m ^ (-(3 / 4 : ℝ)) * (lam m - E) ^ 2 * cN m Φ ^ 2) +
        2 * E ^ 2 * (lam m ^ (-(3 / 4 : ℝ)) * cN m Φ ^ 2) := by ring
    _ ≤ 2 * (lam m ^ (-(3 / 4 : ℝ)) * (lam m - E) ^ 2 * cN m Φ ^ 2) +
        2 * E ^ 2 * (1 * cN m Φ ^ 2) := by gcongr
    _ = _ := by ring

end DFT.Continuum.Line
