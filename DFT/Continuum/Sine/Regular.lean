/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Min
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Regularity of the minimiser

A solution of the Euler–Lagrange equation `λ_m c_m + (Kc)_m = E c_m` has rapidly decreasing
coefficients: since `W(m)² ≤ (n + 1) |k|² = (n + 1) λ_m / π²`, the equation and the weighted Schur
bound `nw_Kc_le` give `Σ W^{2(s+2)} c² ≤ C_s Σ W^{2s} c²`, so every weighted norm is finite
(bootstrap). With `Σ_m W^{-2(n+1)} ≤ (Σ_k k^{-2})^{n+1} < ∞` and Cauchy–Schwarz, `Σ W^q |c_m| < ∞`
for every `q`.

* `nw_add_two_ne_top`, `nw_ne_top`: **the bootstrap**.
* `summable_wt_pow_mul`: `Σ W^q |c_m| < ∞`.
* `norm_iteratedFDeriv_smd_le`: `‖D^i s_m‖ ≤ D_i (1 + π W)^{i(n+1)}` on all of `ℝ^{n+1}`.
* `ser`, `contDiff_ser`, `ser_mem`, `cN_ser`: the series `Σ c_m s_m` is `C²`, has the exchange
  symmetry, vanishes on the faces, and has coefficients `c`.
* `ser_min`: **the minimiser of `Sine/Min` is the coefficient sequence of a function in `Dom`.**
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

variable {n : ℕ}

/-! ### The bootstrap -/

/-- `W(m)² ≤ (n + 1) |k|²`. -/
lemma wt_sq_le (m : Fin (n + 1) → ℕ) : ((wt m : ℕ) : ℝ) ^ 2 ≤ (n + 1) * (ksq m : ℝ) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : Fin (n + 1) => ((m j : ℝ) + 1))
    fun _ => 1
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  simp only [wt, ksq]; push_cast at h ⊢
  linarith

/-- `W(m)² ≤ A λ_m` with `A = (n + 1) / π²`. -/
lemma wt_sq_le_lam (m : Fin (n + 1) → ℕ) : ((wt m : ℕ) : ℝ) ^ 2 ≤ (n + 1) / π ^ 2 * lam m := by
  have hp : 0 < π ^ 2 := by positivity
  rw [lam, div_mul_eq_mul_div, mul_comm (π ^ 2), ← mul_assoc, mul_div_assoc, div_self hp.ne',
    mul_one]
  exact wt_sq_le m

lemma nw_mono {s t : ℕ} (hst : s ≤ t) (c : (Fin (n + 1) → ℕ) → ℝ) : nw s c ≤ nw t c :=
  tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal <| mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by exact_mod_cast one_le_wt m) (by omega)) (sq_nonneg _)

section boot

variable {V : Cfg n → ℝ} {β : (Fin (n + 1) → ℕ) → ℝ}
  (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s)
  (hV : ∀ x ∈ CubeC n, V x = ∑' l, β l * cosM l x)
include hβ hV

/-- **One bootstrap step**: a solution of `λ c + Kc = E c` in `h^s` lies in `h^{s+2}`. -/
lemma nw_add_two_ne_top {c : (Fin (n + 1) → ℕ) → ℝ} {E : ℝ}
    (hEL : ∀ m, lam m * c m + Kc V c m = E * c m) {s : ℕ} (hs : nw s c ≠ ⊤) :
    nw (s + 2) c ≠ ⊤ := by
  set A : ℝ := (n + 1) / π ^ 2
  have hpt : ∀ m, ENNReal.ofReal ((wt m : ℝ) ^ (2 * (s + 2)) * c m ^ 2) ≤
      ENNReal.ofReal (2 * A ^ 2 * E ^ 2) * ENNReal.ofReal ((wt m : ℝ) ^ (2 * s) * c m ^ 2) +
      ENNReal.ofReal (2 * A ^ 2) * ENNReal.ofReal ((wt m : ℝ) ^ (2 * s) * Kc V c m ^ 2) := by
    intro m
    have hw : 0 ≤ (wt m : ℝ) ^ (2 * s) := by positivity
    have hA : 0 ≤ A := by positivity
    have h1 := wt_sq_le_lam m
    have h0 : 0 ≤ ((wt m : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have hW : ((wt m : ℝ) ^ 2 * |c m|) ^ 2 ≤ (A * (lam m * |c m|)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have hL : (lam m * |c m|) ^ 2 = (E * c m - Kc V c m) ^ 2 := by
      rw [mul_pow, sq_abs, ← mul_pow]; congr 1; linarith [hEL m]
    have hQ : (E * c m - Kc V c m) ^ 2 ≤ 2 * (E ^ 2 * c m ^ 2) + 2 * Kc V c m ^ 2 := by
      nlinarith [sq_nonneg (E * c m + Kc V c m)]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (wt m : ℝ) ^ (2 * (s + 2)) * c m ^ 2 =
        (wt m : ℝ) ^ (2 * s) * ((wt m : ℝ) ^ 2 * |c m|) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [e]
    calc (wt m : ℝ) ^ (2 * s) * ((wt m : ℝ) ^ 2 * |c m|) ^ 2
        ≤ (wt m : ℝ) ^ (2 * s) * (A ^ 2 * (2 * (E ^ 2 * c m ^ 2) + 2 * Kc V c m ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (hW.trans ?_) hw
          rw [mul_pow, hL]
          exact mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
      _ = _ := by ring
  have hK := nw_Kc_le hβ hV s c
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hpt)
  rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_ hK)⟩
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) (Gam_ne_top hβ s))) hs

/-- **The bootstrap**: every weighted norm of a square-summable solution is finite. -/
theorem nw_ne_top {c : (Fin (n + 1) → ℕ) → ℝ} {E : ℝ}
    (hEL : ∀ m, lam m * c m + Kc V c m = E * c m) (hc : Summable fun m => c m ^ 2) (s : ℕ) :
    nw s c ≠ ⊤ := by
  have h2 : ∀ j, nw (2 * j) c ≠ ⊤ := fun j => by
    induction j with
    | zero => exact nw_zero_ne_top hc
    | succ j ih => exact nw_add_two_ne_top hβ hV hEL ih
  exact ne_top_of_le_ne_top (h2 s) (nw_mono (by omega) c)

end boot

/-! ### Weighted summability -/

/-- `Σ_m W(m)^{-2(n+1)} < ∞`. -/
lemma tsum_wt_inv_ne_top :
    ∑' m : Fin (n + 1) → ℕ, ENNReal.ofReal (((wt m : ℝ) ^ (n + 1))⁻¹) ^ 2 ≠ ⊤ := by
  have hs : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
    exact (summable_nat_add_iff 1).2 this |>.congr fun k => by push_cast; ring
  have hpt : ∀ m : Fin (n + 1) → ℕ, ENNReal.ofReal (((wt m : ℝ) ^ (n + 1))⁻¹) ^ 2 ≤
      ∏ j, ENNReal.ofReal (1 / ((m j : ℝ) + 1) ^ 2) := by
    intro m
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW : (0 : ℝ) < wt m := by exact_mod_cast one_le_wt m
    have hP : ∏ j, ((m j : ℝ) + 1) ^ 2 ≤ ((wt m : ℝ) ^ 2) ^ (n + 1) := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun j => ((m j : ℝ) + 1) ^ 2)
        (g := fun _ => (wt m : ℝ) ^ 2) (fun j _ => by positivity) fun j _ => by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          have : m j + 1 ≤ wt m := Finset.single_le_sum (f := fun j => m j + 1)
            (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
          exact_mod_cast this
      simpa using this
    have hP0 : 0 < ∏ j, ((m j : ℝ) + 1) ^ 2 := Finset.prod_pos fun j _ => by positivity
    simp only [one_div, Finset.prod_inv_distrib, inv_pow]
    rw [← pow_mul, mul_comm, pow_mul]
    exact inv_anti₀ hP0 hP
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hpt)
  rw [tsum_pi_prod (n + 1) (fun _ k => ENNReal.ofReal (1 / ((k : ℝ) + 1) ^ 2)),
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  simp

/-- **`Σ W^q |c_m| < ∞`** when every weighted norm of `c` is finite. -/
theorem summable_wt_pow_mul {c : (Fin (n + 1) → ℕ) → ℝ} (hc : ∀ s, nw s c ≠ ⊤) (q : ℕ) :
    Summable fun m => (wt m : ℝ) ^ q * |c m| := by
  refine summable_of_ofReal_abs ?_
  have hpt : ∀ m : Fin (n + 1) → ℕ, ENNReal.ofReal (abs ((wt m : ℝ) ^ q * |c m|)) =
      ENNReal.ofReal ((wt m : ℝ) ^ (q + (n + 1)) * |c m|) *
        ENNReal.ofReal (((wt m : ℝ) ^ (n + 1))⁻¹) := fun m => by
    have hW : (0 : ℝ) < wt m := by exact_mod_cast one_le_wt m
    rw [abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [pow_add]; field_simp
  simp only [hpt]
  have h := tsum_mul_le_sq
    (fun m : Fin (n + 1) → ℕ => ENNReal.ofReal ((wt m : ℝ) ^ (q + (n + 1)) * |c m|))
    (fun m => ENNReal.ofReal (((wt m : ℝ) ^ (n + 1))⁻¹))
  rw [← nw_eq] at h
  have hR := ENNReal.mul_ne_top (hc (q + (n + 1))) (tsum_wt_inv_ne_top (n := n))
  have h2 := ne_top_of_le_ne_top hR h
  exact (ENNReal.pow_ne_top_iff.1 h2).resolve_right two_ne_zero

/-! ### Derivatives of the sines -/

lemma contDiff_sn (k : ℕ) : ContDiff ℝ ⊤ (sn k) := by
  unfold sn; fun_prop

/-- `|(d/dt)^i sn_k| ≤ √2 (π k)^i`. -/
lemma norm_iteratedFDeriv_sn_le (k i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (sn k) t‖ ≤ √2 * (π * k) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h1 : iteratedDeriv i (sn k) t = √2 * iteratedDeriv i (fun x => Real.sin (π * k * x)) t :=
    iteratedDeriv_const_mul (f := fun x => Real.sin (π * k * x)) √2
      (((by fun_prop : ContDiff ℝ ⊤ fun x => Real.sin (π * k * x)).of_le le_top).contDiffAt)
  have h2 := iteratedDeriv_comp_const_mul (n := i) (Real.contDiff_sin.of_le le_top) (π * k)
  rw [h1, h2, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ √2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (π * k) ^ i)]
  have := Real.abs_iteratedDeriv_sin_le_one i (π * k * t)
  calc √2 * ((π * k) ^ i * |iteratedDeriv i Real.sin (π * k * t)|) ≤ √2 * ((π * k) ^ i * 1) := by
        gcongr
    _ = _ := by ring

lemma norm_proj_le (j : Fin (n + 1)) :
    ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x j

/-- A factor `x ↦ sn_k(x_j)` of a product of sines. -/
lemma norm_iteratedFDeriv_factor_le (k i : ℕ) (j : Fin (n + 1)) (x : Cfg n) :
    ‖iteratedFDeriv ℝ i (fun y : Cfg n => sn k (y j)) x‖ ≤ √2 * (π * k) ^ i := by
  have e : (fun y : Cfg n => sn k (y j)) =
      sn k ∘ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_sn k) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp :
      ∏ _i : Fin i, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_proj_le j
  calc _ ≤ ‖iteratedFDeriv ℝ i (sn k) (x j)‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact norm_iteratedFDeriv_sn_le k i _

/-- The constant in the derivative bound for products of sines. -/
noncomputable def Dc (n i : ℕ) : ℝ :=
  (∑ p ∈ (Finset.univ : Finset (Fin (n + 1))).sym i,
    (Multiset.countPerms (p : Multiset (Fin (n + 1))) : ℝ)) *
    √2 ^ (n + 1)

lemma contDiff_smd_top (m : Fin (n + 1) → ℕ) : ContDiff ℝ ⊤ (smd m) := by
  unfold smd
  exact contDiff_prod fun j _ => (contDiff_sn _).comp (by fun_prop)

/-- **`‖D^i s_m‖ ≤ D_i (1 + π W)^{i(n+1)}`** on all of `ℝ^{n+1}`. -/
lemma norm_iteratedFDeriv_smd_le (m : Fin (n + 1) → ℕ) (i : ℕ) (x : Cfg n) :
    ‖iteratedFDeriv ℝ i (smd m) x‖ ≤ Dc n i * (1 + π * wt m) ^ (i * (n + 1)) := by
  classical
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
      ContDiff ℝ ⊤ (fun y : Cfg n => sn (m j + 1) (y j)) := fun j _ =>
    (contDiff_sn _).comp (by fun_prop)
  have h := norm_iteratedFDeriv_prod_le (u := Finset.univ)
    (f := fun j (y : Cfg n) => sn (m j + 1) (y j)) hf (x := x) (n := i) (by exact_mod_cast le_top)
  have e : smd m = fun y : Cfg n => ∏ j ∈ Finset.univ, sn (m j + 1) (y j) := rfl
  rw [e]
  refine h.trans ?_
  have hW1 : (1 : ℝ) ≤ 1 + π * wt m := by
    have : 0 ≤ π * (wt m : ℝ) := by positivity
    linarith
  have hfac : ∀ p ∈ (Finset.univ : Finset (Fin (n + 1))).sym i, ∀ j ∈ (Finset.univ : Finset _),
      ‖iteratedFDeriv ℝ ((p : Multiset (Fin (n + 1))).count j)
        (fun y : Cfg n => sn (m j + 1) (y j)) x‖ ≤ √2 * (1 + π * wt m) ^ i := by
    intro p _ j _
    refine (norm_iteratedFDeriv_factor_le _ _ j x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
    have hc : (p : Multiset (Fin (n + 1))).count j ≤ i := by
      simpa using Multiset.count_le_card j (p : Multiset (Fin (n + 1)))
    have hk : ((m j + 1 : ℕ) : ℝ) ≤ wt m := by
      exact_mod_cast Finset.single_le_sum (f := fun j => m j + 1) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j)
    calc (π * ((m j + 1 : ℕ) : ℝ)) ^ _ ≤ (1 + π * wt m) ^ ((p : Multiset (Fin (n + 1))).count j) :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [pi_pos]) _
      _ ≤ _ := pow_le_pow_right₀ hW1 hc
  rw [Dc, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∏ j ∈ Finset.univ, ‖iteratedFDeriv ℝ ((p : Multiset (Fin (n + 1))).count j)
        (fun y : Cfg n => sn (m j + 1) (y j)) x‖
      ≤ ∏ _j ∈ (Finset.univ : Finset (Fin (n + 1))), √2 * (1 + π * wt m) ^ i :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (hfac p hp)
    _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
          mul_comm i]

/-! ### Summation of the sine series -/

/-- The sine series `Φ(x) = Σ_m c_m s_m(x)`. -/
noncomputable def ser (c : (Fin (n + 1) → ℕ) → ℝ) (x : Cfg n) : ℝ := ∑' m, c m * smd m x

lemma summable_wt_pow_mul' {c : (Fin (n + 1) → ℕ) → ℝ}
    (hc : ∀ q, Summable fun m => (wt m : ℝ) ^ q * |c m|) (q : ℕ) (D : ℝ) :
    Summable fun m => |c m| * D * (1 + π * wt m) ^ q := by
  refine Summable.of_norm_bounded (((hc q).mul_left ((1 + π) ^ q * |D|))) fun m => ?_
  have hW : (1 : ℝ) ≤ wt m := by exact_mod_cast one_le_wt m
  have h1 : 1 + π * wt m ≤ (1 + π) * wt m := by nlinarith [pi_pos]
  have h0 : 0 ≤ 1 + π * (wt m : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs, abs_of_nonneg (pow_nonneg h0 q)]
  calc |c m| * |D| * (1 + π * wt m) ^ q ≤ |c m| * |D| * ((1 + π) * wt m) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 q) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- **The sine series is `C²`** (indeed `C^∞`) when `Σ W^q |c_m| < ∞` for every `q`. -/
theorem contDiff_ser {c : (Fin (n + 1) → ℕ) → ℝ}
    (hc : ∀ q, Summable fun m => (wt m : ℝ) ^ q * |c m|) : ContDiff ℝ 2 (ser c) := by
  have hf : ∀ m, ContDiff ℝ 2 fun x => c m * smd m x := fun m =>
    contDiff_const.mul ((contDiff_smd_top m).of_le le_top)
  refine contDiff_tsum (v := fun k m => |c m| * Dc n k * (1 + π * wt m) ^ (k * (n + 1))) hf
    (fun k _ => summable_wt_pow_mul' hc _ _) fun k m x hk => ?_
  have e : (fun x => c m * smd m x) = c m • smd m := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((contDiff_smd_top m).of_le le_top).contDiffAt,
    norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smd_le m k x) (abs_nonneg _)

lemma ser_face (c : (Fin (n + 1) → ℕ) → ℝ) (x : Cfg n) (j : Fin (n + 1))
    (h : x j = 0 ∨ x j = 1) : ser c x = 0 := by
  simp [ser, fun m => smd_face m x j h]

lemma ser_pm {τ : Stat} {c : (Fin (n + 1) → ℕ) → ℝ} (hc : InS τ c)
    (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) : ser c (pm σ x) = ch τ σ * ser c x := by
  rw [ser, ser, ← (pmIe σ).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  change c (pmI σ m) * smd (pmI σ m) (pm σ x) = _
  rw [hc σ m, smd_pm]; ring

/-- The sine series lies in the domain. -/
theorem ser_mem {τ : Stat} {c : (Fin (n + 1) → ℕ) → ℝ}
    (hc : ∀ q, Summable fun m => (wt m : ℝ) ^ q * |c m|) (hS : InS τ c) : ser c ∈ Dom τ n :=
  ⟨contDiff_ser hc, ser_pm hS, ser_face c⟩

/-- **The coefficients of the sine series are `c`.** -/
theorem cN_ser {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => |c m|)
    (m : Fin (n + 1) → ℕ) : cN m (ser c) = c m := by
  set B : ℝ := √2 ^ (n + 1)
  have hF : ∀ m', Integrable (fun x => smd m x * (c m' * smd m' x)) (μN n) := fun m' =>
    integrableN ((continuous_smd m).mul (continuous_const.mul (continuous_smd m')))
  have hle : ∀ m', ∫ x, ‖smd m x * (c m' * smd m' x)‖ ∂μN n ≤ B * B * |c m'| := fun m' => by
    calc ∫ x, ‖smd m x * (c m' * smd m' x)‖ ∂μN n ≤ ∫ _x, B * B * |c m'| ∂μN n := by
          refine integral_mono (hF m').norm (integrable_const _) fun x => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have h1 := abs_smd_le m x
          have h2 := abs_smd_le m' x
          calc |smd m x| * (|c m'| * |smd m' x|) ≤ B * (|c m'| * B) := by gcongr
            _ = _ := by ring
      _ = B * B * |c m'| := by rw [integral_const, muN_real_univ, one_smul]
  have hsum : Summable fun m' => ∫ x, ‖smd m x * (c m' * smd m' x)‖ ∂μN n :=
    Summable.of_nonneg_of_le (fun m' => integral_nonneg fun x => norm_nonneg _) hle
      (hc.mul_left _)
  rw [cN_eq]
  have e : (fun x => smd m x * ser c x) = fun x => ∑' m', smd m x * (c m' * smd m' x) := by
    funext x; rw [ser, tsum_mul_left]
  rw [e, ← integral_tsum_of_summable_integral_norm hF hsum]
  have e2 : ∀ m', ∫ x, smd m x * (c m' * smd m' x) ∂μN n = c m' * if m = m' then 1 else 0 :=
    fun m' => by
      rw [← smd_orthonormal m m', ← muN_eq, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
  simp only [e2, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single m fun b hb => by simp [Ne.symm hb]]
  simp

/-! ### The minimiser as a function -/

section minimiser

variable {V : Cfg n → ℝ} {β : (Fin (n + 1) → ℕ) → ℝ}
  (hβ : ∀ s : ℕ, Summable fun l => |β l| * (1 + (sz l : ℝ)) ^ s)
  (hV : ∀ x ∈ CubeC n, V x = ∑' l, β l * cosM l x)
include hβ hV

/-- **The minimiser is a function in the domain**: `Φ = Σ c_m s_m ∈ Dom` with `cN Φ = c`. -/
theorem ser_min (hVs : ∀ σ x, V (pm σ x) = V x) {τ : Stat} {a : (Fin (n + 1) → ℕ) → ℝ}
    (ha : Adm τ a) (hmin : Fn V a = E0 V τ) :
    ser a ∈ Dom τ n ∧ ∀ m, cN m (ser a) = a m := by
  have hEL := euler_lagrange hβ hV hVs ha hmin
  have hq := summable_wt_pow_mul (nw_ne_top hβ hV hEL ha.sq)
  have h0 : Summable fun m => |a m| := by simpa using hq 0
  exact ⟨ser_mem hq ha.sym, cN_ser h0⟩

end minimiser

end DFT.Continuum.Sine
