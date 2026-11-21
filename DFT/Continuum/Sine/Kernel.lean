/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Coeff
import DFT.Continuum.Line.Free

/-!
# The potential in the sine basis

Let the potential be a cosine series on the closed cube, `V(x) = Σ_l β_l Π_j cos(π l_j x_j)` with
`Σ |β_l| < ∞`. Its matrix in the sine basis is

`K(m', m) = ⟨s_{m'}, V s_m⟩ = Σ_l β_l Π_j κ(k'_j, l_j, k_j)`,

where `κ(k', l, k) = ∫₀¹ sₖ' cos(πlx) sₖ = (δ_{k'-k-l} + δ_{k'-k+l} - δ_{k'+k-l}) / 2`. So
`|κ| ≤ 1`, and `κ ≠ 0` only if `k' = k + l`, `k = k' + l` or `k' + k = l`. In each case
`k' ≤ k + l`, which is what makes the regularity bootstrap work.

* `cosM`, `kap`, `kap_eq`, `abs_kap_le`.
* `Ker`, `Ker_symm`, `Ker_eq`: the kernel and its expansion.
* `abs_Ker_le`: `|K(m', m)| ≤ Σ_l |β_l| [l admissible for (m', m)]`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real

variable {n : ℕ}

/-- The product of cosines `Π_j cos(π l_j x_j)`. -/
noncomputable def cosM (l : Fin (n + 1) → ℕ) (x : Cfg n) : ℝ := ∏ j, Real.cos (π * l j * x j)

lemma continuous_cosM (l : Fin (n + 1) → ℕ) : Continuous (cosM l) :=
  continuous_finsetProd _ fun j _ => by fun_prop

lemma abs_cosM_le (l : Fin (n + 1) → ℕ) (x : Cfg n) : |cosM l x| ≤ 1 := by
  rw [cosM, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => Real.abs_cos_le_one _

lemma abs_sn_le (k : ℕ) (x : ℝ) : |sn k x| ≤ √2 := by
  rw [sn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < √2)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

lemma abs_smd_le (m : Fin (n + 1) → ℕ) (x : Cfg n) : |smd m x| ≤ √2 ^ (n + 1) := by
  rw [smd, Finset.abs_prod]
  calc ∏ j, |sn (m j + 1) (x j)| ≤ ∏ _j : Fin (n + 1), √2 :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => abs_sn_le _ _
    _ = √2 ^ (n + 1) := by simp

/-! ### The one-dimensional integral -/

/-- `κ(k', l, k) = ∫₀¹ sₖ'(x) cos(πlx) sₖ(x) dx`. -/
noncomputable def kap (k' l k : ℕ) : ℝ := ∫ x, sn k' x * Real.cos (π * l * x) * sn k x ∂μ1

/-- The indicator `[j = 0]` on the integers. -/
def dZ (j : ℤ) : ℝ := if j = 0 then 1 else 0

lemma kap_eq {k' k : ℕ} (hk' : 0 < k') (hk : 0 < k) (l : ℕ) :
    kap k' l k = (dZ ((k' : ℤ) - k - l) + dZ ((k' : ℤ) - k + l) - dZ ((k' : ℤ) + k - l)) / 2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : ∀ x, sn k' x * Real.cos (π * l * x) * sn k x =
      (Real.cos (π * ((k' : ℤ) - k - l : ℤ) * x) + Real.cos (π * ((k' : ℤ) - k + l : ℤ) * x) -
        Real.cos (π * ((k' : ℤ) + k - l : ℤ) * x) -
          Real.cos (π * ((k' : ℤ) + k + l : ℤ) * x)) / 2 := by
    intro x
    simp only [sn]
    push_cast
    have a : π * ((k' : ℝ) - k - l) * x = (π * k' * x - π * k * x) - π * l * x := by ring
    have b : π * ((k' : ℝ) - k + l) * x = (π * k' * x - π * k * x) + π * l * x := by ring
    have c : π * ((k' : ℝ) + k - l) * x = (π * k' * x + π * k * x) - π * l * x := by ring
    have d : π * ((k' : ℝ) + k + l) * x = (π * k' * x + π * k * x) + π * l * x := by ring
    rw [a, b, c, d, Real.cos_sub, Real.cos_add, Real.cos_sub (π * k' * x + _),
      Real.cos_add (π * k' * x + _),
      Real.cos_sub (π * k' * x), Real.cos_add (π * k' * x), Real.sin_sub, Real.sin_add]
    linear_combination (Real.sin (π * k' * x) * Real.cos (π * l * x) * Real.sin (π * k * x)) * h2
  rw [kap, integral_mu1_eq]
  simp only [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
    intervalIntegral.integral_add]
  all_goals try exact Continuous.intervalIntegrable (by fun_prop) _ _
  · rw [integral_cos_int, integral_cos_int, integral_cos_int, integral_cos_int]
    have hz : ((k' : ℤ) + k + l) ≠ 0 := by omega
    simp only [dZ, hz, ↓reduceIte, sub_zero]

/-- When `κ(k', l, k)` can be nonzero. -/
def adm1 (k' l k : ℕ) : Prop := k' = k + l ∨ k = k' + l ∨ k' + k = l

instance (k' l k : ℕ) : Decidable (adm1 k' l k) := by unfold adm1; infer_instance

lemma abs_kap_le {k' k : ℕ} (hk' : 0 < k') (hk : 0 < k) (l : ℕ) :
    |kap k' l k| ≤ if adm1 k' l k then 1 else 0 := by
  rw [kap_eq hk' hk]
  simp only [dZ, adm1]
  split_ifs <;> first | omega | norm_num

lemma adm1_le {k' l k : ℕ} (h : adm1 k' l k) : k' ≤ k + l := by
  unfold adm1 at h; omega

/-! ### The kernel -/

/-- The matrix of the potential `V` in the sine basis, `⟨s_{m'}, V s_m⟩`. -/
noncomputable def Ker (V : Cfg n → ℝ) (m' m : Fin (n + 1) → ℕ) : ℝ :=
  ∫ x, smd m' x * (V x * smd m x) ∂μN n

lemma Ker_symm (V : Cfg n → ℝ) (m' m : Fin (n + 1) → ℕ) : Ker V m' m = Ker V m m' := by
  simp only [Ker]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- `l` is admissible for `(m', m)`: every factor `κ(k'_j, l_j, k_j)` may be nonzero. -/
def adm (m' l m : Fin (n + 1) → ℕ) : Prop := ∀ j, adm1 (m' j + 1) (l j) (m j + 1)

instance (m' l m : Fin (n + 1) → ℕ) : Decidable (adm m' l m) := by unfold adm; infer_instance

instance : IsFiniteMeasure (μN n) :=
  isFiniteMeasure_restrict.2 (by rw [volume_cube]; exact ENNReal.one_ne_top)

lemma muN_real_univ : (μN n).real univ = 1 := by
  simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ, volume_cube]

section series

variable {V : Cfg n → ℝ} {β : (Fin (n + 1) → ℕ) → ℝ} (hβ : Summable fun l => |β l|)
  (hV : ∀ x ∈ CubeC n, V x = ∑' l, β l * cosM l x)
include hβ hV

/-- **The kernel of a cosine series**: `K(m', m) = Σ_l β_l Π_j κ(k'_j, l_j, k_j)`. -/
theorem Ker_eq (m' m : Fin (n + 1) → ℕ) :
    Ker V m' m = ∑' l, β l * ∏ j, kap (m' j + 1) (l j) (m j + 1) := by
  set F : (Fin (n + 1) → ℕ) → Cfg n → ℝ := fun l x => β l * (smd m' x * cosM l x * smd m x)
  have hFc : ∀ l, Continuous (F l) := fun l =>
    continuous_const.mul (((continuous_smd m').mul (continuous_cosM l)).mul (continuous_smd m))
  have hbd : ∀ l x, ‖F l x‖ ≤ |β l| * (√2 ^ (n + 1) * √2 ^ (n + 1)) := by
    intro l x
    simp only [F, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have a := abs_smd_le m' x
    have b := abs_smd_le m x
    have c := abs_cosM_le l x
    calc |smd m' x| * |cosM l x| * |smd m x| ≤ √2 ^ (n + 1) * 1 * √2 ^ (n + 1) := by
          gcongr
      _ = _ := by ring
  have hsum : Summable fun l => ∫ x, ‖F l x‖ ∂μN n := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun x => norm_nonneg _)
      (fun l => ?_) (hβ.mul_right (√2 ^ (n + 1) * √2 ^ (n + 1)))
    calc ∫ x, ‖F l x‖ ∂μN n ≤ ∫ _x, |β l| * (√2 ^ (n + 1) * √2 ^ (n + 1)) ∂μN n :=
          integral_mono (integrableN (hFc l).norm) (integrable_const _) (hbd l)
      _ = _ := by rw [integral_const, muN_real_univ, one_smul]
  have h1 : Ker V m' m = ∫ x, ∑' l, F l x ∂μN n := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
    rw [hV x (cube_subset hx), ← tsum_mul_right, ← tsum_mul_left]
    congr 1; funext l; simp only [F]; ring
  rw [h1, ← integral_tsum_of_summable_integral_norm (fun l => integrableN (hFc l)) hsum]
  congr 1; funext l
  simp only [F]
  rw [integral_const_mul, muN_eq]
  congr 1
  have e : (fun x => smd m' x * cosM l x * smd m x) = fun x : Fin (n + 1) → ℝ =>
      ∏ j, (sn (m' j + 1) (x j) * Real.cos (π * l j * x j) * sn (m j + 1) (x j)) := by
    funext x; simp only [smd, cosM, Finset.prod_mul_distrib]
  rw [e, integral_fintype_prod_eq_prod
    (f := fun j t => sn (m' j + 1) t * Real.cos (π * l j * t) * sn (m j + 1) t)]
  rfl

/-- **The kernel bound**: `|K(m', m)| ≤ Σ_l |β_l| [adm m' l m]`. -/
theorem abs_Ker_le (m' m : Fin (n + 1) → ℕ) :
    |Ker V m' m| ≤ ∑' l, |β l| * (if adm m' l m then 1 else 0) := by
  have hle : ∀ l, |β l * ∏ j, kap (m' j + 1) (l j) (m j + 1)| ≤
      |β l| * (if adm m' l m then 1 else 0) := by
    intro l
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    split_ifs with h
    · exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => by
        have := abs_kap_le (Nat.succ_pos (m' j)) (Nat.succ_pos (m j)) (l j)
        simpa only [h j, ite_true] using this
    · simp only [adm, not_forall] at h
      obtain ⟨j, hj⟩ := h
      refine le_of_eq (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
      have := abs_kap_le (Nat.succ_pos (m' j)) (Nat.succ_pos (m j)) (l j)
      simp only [hj, ite_false] at this
      exact le_antisymm this (abs_nonneg _)
  have hs : Summable fun l => |β l| * (if adm m' l m then 1 else 0) :=
    Summable.of_nonneg_of_le (fun l => by positivity) (fun l => by
      split_ifs <;> simp) hβ
  rw [Ker_eq hβ hV]
  calc |∑' l, β l * ∏ j, kap (m' j + 1) (l j) (m j + 1)|
      ≤ ∑' l, |β l * ∏ j, kap (m' j + 1) (l j) (m j + 1)| := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun l => (hle l)) hs)
    _ ≤ _ := (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hs).tsum_le_tsum hle hs

end series

end DFT.Continuum.Sine
