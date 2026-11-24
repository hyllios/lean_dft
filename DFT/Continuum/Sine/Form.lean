/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Kernel
import Mathlib.Analysis.MeanInequalities

/-!
# The potential acting on coefficient sequences

* `Kc`: the action `(Kc)_{m'} = Σ_m K(m', m) c_m` of the kernel; `Bf c d = Σ c (Kd)`;
* `KBd V C`: an `ℓ²` bound for the kernel (from continuity, `Sine/Cont`), and the consequences
  `KBd.Kc_add`, `KBd.Bf_sq_le`, `KBd.Bf_sub_left`, `KBd.Bf_sub_right`;
* `Kc_cN`, `Bf_cN`: for continuous `φ`, the coefficients of `Vφ` and `∫ V φ²`;
* `InS`, `Kc_InS`, `cN_InS`: sequences of a symmetry type.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

variable {n : ℕ}

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

/-- `|Σ f| ≤ Σ |f|` in `ℝ≥0∞`, with no summability assumption. -/
lemma ofReal_abs_tsum_le {ι : Type*} (f : ι → ℝ) :
    ENNReal.ofReal |∑' i, f i| ≤ ∑' i, ENNReal.ofReal |f i| := by
  by_cases hf : Summable f
  · have ha : Summable fun i => |f i| := hf.abs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) ha]
    exact ENNReal.ofReal_le_ofReal (by
      rw [← Real.norm_eq_abs]; exact (norm_tsum_le_tsum_norm hf.norm).trans le_rfl)
  · rw [tsum_eq_zero_of_not_summable hf, abs_zero, ENNReal.ofReal_zero]; exact bot_le

/-- A real sequence is summable if the sum of its absolute values is finite in `ℝ≥0∞`. -/
lemma summable_of_ofReal_abs {ι : Type*} {f : ι → ℝ}
    (h : ∑' i, ENNReal.ofReal |f i| ≠ ⊤) : Summable f := by
  have hs := ENNReal.summable_toReal h
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)] at hs
  exact hs.of_abs

/-- The action of the kernel on a coefficient sequence. -/
noncomputable def Kc (V : Cfg n → ℝ) (c : (Fin (n + 1) → ℕ) → ℝ) (m' : Fin (n + 1) → ℕ) : ℝ :=
  ∑' m, Ker V m' m * c m

variable {V : Cfg n → ℝ}

lemma Kc_smul (t : ℝ) (c : (Fin (n + 1) → ℕ) → ℝ) :
    Kc V (fun m => t * c m) = fun m => t * Kc V c m := by
  funext m'
  simp only [Kc]
  rw [← tsum_mul_left]; congr 1; funext m; ring

/-! ### The potential energy in coefficients -/

/-- The bilinear form `Σ_{m'} c_{m'} (Kd)_{m'}`. -/
noncomputable def Bf (V : Cfg n → ℝ) (c d : (Fin (n + 1) → ℕ) → ℝ) : ℝ := ∑' m, c m * Kc V d m

lemma summable_mul_of_sq {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) : Summable fun m => c m * d m := by
  refine Summable.of_norm_bounded ((hc.add hd).div_const 2) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (c m), sq_abs (d m), sq_nonneg (|c m| - |d m|)]

/-- Cauchy–Schwarz for real sequences: `(Σ c d)² ≤ (Σ c²)(Σ d²)`. -/
lemma tsum_mul_sq_le_real {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) :
    (∑' m, c m * d m) ^ 2 ≤ (∑' m, c m ^ 2) * ∑' m, d m ^ 2 := by
  have h := tsum_mul_le_sq (fun m => ENNReal.ofReal |c m|) (fun m => ENNReal.ofReal |d m|)
  have e1 : ∀ x : ℝ, ENNReal.ofReal |x| ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp only [e1] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hc,
    ← ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hd,
    ← ENNReal.ofReal_mul (tsum_nonneg fun m => sq_nonneg _)] at h
  have h2 := (ofReal_abs_tsum_le (fun m => c m * d m))
  have h3 : ENNReal.ofReal ((∑' m, c m * d m) ^ 2) ≤
      ENNReal.ofReal ((∑' m, c m ^ 2) * ∑' m, d m ^ 2) := by
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    refine le_trans (pow_le_pow_left' h2 2) (le_trans ?_ h)
    simp only [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    exact le_rfl
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (tsum_nonneg fun m => sq_nonneg _)
    (tsum_nonneg fun m => sq_nonneg _))).1 h3


/-! ### An abstract `ℓ²` bound for the kernel -/

/-- **An `ℓ²` bound for the kernel**: its rows pair with `ℓ²` sequences, and `‖Kc‖² ≤ C ‖c‖²`.
It follows from continuity (`Sine/Cont`, `kBd_of_continuous`). -/
structure KBd (V : Cfg n → ℝ) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  row : ∀ {c : (Fin (n + 1) → ℕ) → ℝ}, Summable (fun m => c m ^ 2) →
    ∀ m', Summable fun m => Ker V m' m * c m
  sq : ∀ {c : (Fin (n + 1) → ℕ) → ℝ}, Summable (fun m => c m ^ 2) →
    Summable fun m => Kc V c m ^ 2
  le : ∀ {c : (Fin (n + 1) → ℕ) → ℝ}, Summable (fun m => c m ^ 2) →
    ∑' m, Kc V c m ^ 2 ≤ C * ∑' m, c m ^ 2

namespace KBd

variable {V : Cfg n → ℝ} {C : ℝ} (hK : KBd V C)
include hK

lemma Kc_add {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) :
    Kc V (fun m => c m + d m) = fun m => Kc V c m + Kc V d m := by
  funext m'
  simp only [Kc, mul_add]
  exact (hK.row hc m').tsum_add (hK.row hd m')

lemma Bf_sq_le {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) :
    Bf V c d ^ 2 ≤ C * (∑' m, c m ^ 2) * ∑' m, d m ^ 2 := by
  have h := tsum_mul_sq_le_real hc (hK.sq hd)
  have h2 := hK.le hd
  calc Bf V c d ^ 2 ≤ (∑' m, c m ^ 2) * ∑' m, Kc V d m ^ 2 := h
    _ ≤ (∑' m, c m ^ 2) * (C * ∑' m, d m ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (tsum_nonneg fun m => sq_nonneg _)
    _ = _ := by ring

lemma Bf_sub_left {c c' d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hc' : Summable fun m => c' m ^ 2) (hd : Summable fun m => d m ^ 2) :
    Bf V c d - Bf V c' d = Bf V (fun m => c m - c' m) d := by
  simp only [Bf, sub_mul]
  exact ((summable_mul_of_sq hc (hK.sq hd)).tsum_sub (summable_mul_of_sq hc' (hK.sq hd))).symm

lemma Bf_sub_right {c d d' : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) (hd' : Summable fun m => d' m ^ 2) :
    Bf V c d - Bf V c d' = Bf V c (fun m => d m - d' m) := by
  have hneg : Summable fun m => (-1 * d' m) ^ 2 := by simpa [neg_one_mul, neg_sq] using hd'
  have e : (fun m => d m - d' m) = fun m => d m + (-1) * d' m := by funext m; ring
  rw [e]
  simp only [Bf]
  rw [hK.Kc_add hd hneg, Kc_smul]
  simp only [mul_add]
  rw [(summable_mul_of_sq hc (hK.sq hd)).tsum_add]
  · rw [show (∑' m, c m * (-1 * Kc V d' m)) = -∑' m, c m * Kc V d' m by
      rw [← tsum_neg]; congr 1; funext m; ring]
    ring
  · have := summable_mul_of_sq hc (hK.sq hd')
    simpa [mul_neg, neg_mul, one_mul] using this.neg

end KBd

/-! ### States and relabelling -/

lemma Ker_eq_cN (V : Cfg n → ℝ) (m' m : Fin (n + 1) → ℕ) :
    Ker V m' m = cN m (fun x => V x * smd m' x) := by
  rw [cN_eq, Ker]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- For a continuous `φ`, the kernel maps the coefficients of `φ` to those of `Vφ`. -/
lemma Kc_cN {V φ : Cfg n → ℝ} (hVc : Continuous V) (hφ : Continuous φ) (m' : Fin (n + 1) → ℕ) :
    Kc V (fun m => cN m φ) m' = cN m' (fun x => V x * φ x) := by
  have h := hasSum_pair_cube (f := fun x => V x * smd m' x) (g := φ)
    (hVc.mul (continuous_smd m')) hφ
  rw [Kc]
  simp only [Ker_eq_cN]
  rw [h.tsum_eq, ← muN_eq, cN_eq]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- **The potential energy in coefficients**: `Σ ⟨s, φ⟩ (K⟨s, φ⟩) = ∫ V φ²`. -/
lemma Bf_cN {V φ : Cfg n → ℝ} (hVc : Continuous V) (hφ : Continuous φ) :
    Bf V (fun m => cN m φ) (fun m => cN m φ) = ∫ x, V x * (φ x * φ x) ∂μN n := by
  simp only [Bf, Kc_cN hVc hφ]
  have h := hasSum_pair_cube (f := φ) (g := fun x => V x * φ x) hφ (hVc.mul hφ)
  rw [h.tsum_eq, ← muN_eq]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- Relabelling of multi-indices as an equivalence. -/
def pmIe (σ : Equiv.Perm (Fin (n + 1))) : (Fin (n + 1) → ℕ) ≃ (Fin (n + 1) → ℕ) where
  toFun := pmI σ
  invFun := pmI σ⁻¹
  left_inv m := by funext i; simp [pmI]
  right_inv m := by funext i; simp [pmI]

lemma ksq_pm (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) : ksq (pmI σ m) = ksq m := by
  simp only [ksq, pmI]
  exact Equiv.sum_comp σ (fun i => (m i + 1) ^ 2)

/-- The sequences of symmetry type `τ`. -/
def InS (τ : SymT n) (c : (Fin (n + 1) → ℕ) → ℝ) : Prop :=
  ∀ σ, τ.G σ → ∀ m, c (pmI σ m) = τ.χ σ * c m

lemma Ker_pm {V : Cfg n → ℝ} (hVs : ∀ σ x, V (pm σ x) = V x) (σ : Equiv.Perm (Fin (n + 1)))
    (m' m : Fin (n + 1) → ℕ) : Ker V (pmI σ m') (pmI σ m) = Ker V m' m := by
  rw [Ker, ← integral_pm σ]
  simp only [smd_pm, hVs]
  rfl

/-- The kernel preserves the exchange symmetry. -/
lemma Kc_InS {V : Cfg n → ℝ} (hVs : ∀ σ x, V (pm σ x) = V x) {τ : SymT n}
    {c : (Fin (n + 1) → ℕ) → ℝ} (hc : InS τ c) : InS τ (Kc V c) := by
  intro σ hσ m'
  simp only [Kc]
  rw [← (pmIe σ).tsum_eq]
  simp only [pmIe, Equiv.coe_fn_mk, Ker_pm hVs, hc σ hσ, ← tsum_mul_left]
  congr 1; funext m; ring

lemma cN_InS {τ : Stat} {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) : InS τ.toSym fun m => cN m φ :=
  fun σ _ m => cN_pm hφ σ m

end DFT.Continuum.Sine
