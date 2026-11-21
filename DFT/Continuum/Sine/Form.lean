/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Schur

/-!
# The potential acting on coefficient sequences

For a potential whose kernel is dominated by nonnegative weights,
`|K(m', m)| ≤ Σ_l b_l [adm m' l m]` (for a cosine series, `b_l = |β_l|`: `abs_Ker_le`), with
`Σ_l b_l (1 + |l|)^s < ∞`, the kernel `K` acts on coefficient sequences,
`(Kc)_{m'} = Σ_m K(m', m) c_m`, and is bounded on every weighted space:

`Σ_{m'} W(m')^{2s} (Kc)_{m'}² ≤ (3^{n+1} Γ_s)² Σ_m W(m)^{2s} c_m²`,  `Γ_s = Σ_l b_l (1 + |l|)^s`.

The proof combines the kernel bound with `W(m') ≤ W(m)(1 + |l|)` for admissible `l` and the Schur
test. Everything is stated in `ℝ≥0∞`.

* `nw`: the weighted norm `Σ_m W(m)^{2s} c_m²` in `ℝ≥0∞`.
* `Kc`: the action of the kernel.
* `nw_Kc_le`: **the weighted bound**.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal

variable {n : ℕ}

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

/-- The weighted norm `Σ_m W(m)^{2s} c_m²`. -/
noncomputable def nw (s : ℕ) (c : (Fin (n + 1) → ℕ) → ℝ) : ℝ≥0∞ :=
  ∑' m, ENNReal.ofReal ((wt m : ℝ) ^ (2 * s) * c m ^ 2)

lemma nw_eq (s : ℕ) (c : (Fin (n + 1) → ℕ) → ℝ) :
    nw s c = ∑' m, ENNReal.ofReal ((wt m : ℝ) ^ s * |c m|) ^ 2 := by
  refine tsum_congr fun m => ?_
  rw [← ENNReal.ofReal_pow (by positivity), mul_pow, sq_abs, ← pow_mul, mul_comm s 2]

/-- The action of the kernel on a coefficient sequence. -/
noncomputable def Kc (V : Cfg n → ℝ) (c : (Fin (n + 1) → ℕ) → ℝ) (m' : Fin (n + 1) → ℕ) : ℝ :=
  ∑' m, Ker V m' m * c m

section bound

variable {V : Cfg n → ℝ} {b : (Fin (n + 1) → ℕ) → ℝ} (hb0 : ∀ l, 0 ≤ b l) (hbS : Summable b)
  (hK : ∀ m' m, |Ker V m' m| ≤ ∑' l, b l * (if adm m' l m then 1 else 0))

/-- `Γ_s = Σ_l b_l (1 + |l|)^s`. -/
noncomputable def Gam (b : (Fin (n + 1) → ℕ) → ℝ) (s : ℕ) : ℝ≥0∞ :=
  ∑' l, ENNReal.ofReal (b l * (1 + (sz l : ℝ)) ^ s)

lemma Gam_ne_top (hb0 : ∀ l, 0 ≤ b l) {s : ℕ}
    (hs : Summable fun l => b l * (1 + (sz l : ℝ)) ^ s) : Gam b s ≠ ⊤ := by
  rw [Gam, ← ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (hb0 l) (by positivity)) hs]
  exact ENNReal.ofReal_ne_top

include hb0 hbS in
lemma Gam_zero_ne_top : Gam b 0 ≠ ⊤ := Gam_ne_top hb0 (by simpa using hbS)

/-- The majorant `A_s(m', m) = Σ_l b_l (1 + |l|)^s [adm m' l m]`. -/
noncomputable def Amaj (b : (Fin (n + 1) → ℕ) → ℝ) (s : ℕ) (m' m : Fin (n + 1) → ℕ) : ℝ≥0∞ :=
  ∑' l, ENNReal.ofReal (b l * (1 + (sz l : ℝ)) ^ s) * (if adm m' l m then 1 else 0)

lemma Amaj_row (s : ℕ) (m' : Fin (n + 1) → ℕ) :
    ∑' m, Amaj b s m' m ≤ 3 ^ (n + 1) * Gam b s := by
  simp only [Amaj]
  rw [tsum_comm]
  simp only [ENNReal.tsum_mul_left]
  rw [Gam, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun l => ?_
  rw [mul_comm]; exact mul_le_mul_left (tsum_adm_le m' l) _

lemma Amaj_col (s : ℕ) (m : Fin (n + 1) → ℕ) :
    ∑' m', Amaj b s m' m ≤ 3 ^ (n + 1) * Gam b s := by
  simp only [Amaj]
  rw [tsum_comm]
  simp only [ENNReal.tsum_mul_left]
  rw [Gam, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun l => ?_
  rw [mul_comm]; exact mul_le_mul_left (tsum_adm_le' l m) _

include hb0 hbS hK in
/-- The weighted kernel bound: `W(m')^s |K(m', m)| ≤ A_s(m', m) W(m)^s`. -/
lemma ofReal_wt_Ker_le (s : ℕ) (m' m : Fin (n + 1) → ℕ) :
    ENNReal.ofReal ((wt m' : ℝ) ^ s * |Ker V m' m|) ≤
      Amaj b s m' m * ENNReal.ofReal ((wt m : ℝ) ^ s) := by
  have h0 := hbS
  have hK := hK m' m
  have hs : Summable fun l => b l * (if adm m' l m then 1 else 0) :=
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hb0 l) (by split_ifs <;> norm_num))
      (fun l => by split_ifs <;> simp [hb0 l]) h0
  calc ENNReal.ofReal ((wt m' : ℝ) ^ s * |Ker V m' m|)
      ≤ ENNReal.ofReal ((wt m' : ℝ) ^ s * ∑' l, b l * (if adm m' l m then 1 else 0)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hK (by positivity))
    _ = ∑' l, ENNReal.ofReal ((wt m' : ℝ) ^ s * (b l * (if adm m' l m then 1 else 0))) := by
        rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (by positivity)
          (mul_nonneg (hb0 l) (by split_ifs <;> norm_num))) (hs.mul_left _)]
    _ ≤ ∑' l, ENNReal.ofReal (b l * (1 + (sz l : ℝ)) ^ s) * (if adm m' l m then 1 else 0) *
          ENNReal.ofReal ((wt m : ℝ) ^ s) := by
        refine tsum_le_tsum fun l => ?_
        split_ifs with h
        · rw [mul_one, mul_one, ← ENNReal.ofReal_mul (mul_nonneg (hb0 l) (by positivity))]
          refine ENNReal.ofReal_le_ofReal ?_
          have hw : (wt m' : ℝ) ≤ wt m * (1 + sz l) := by exact_mod_cast wt_le h
          have hw' : (wt m' : ℝ) ^ s ≤ (wt m * (1 + sz l)) ^ s :=
            pow_le_pow_left₀ (by positivity) hw s
          rw [mul_pow] at hw'
          nlinarith [hb0 l, pow_nonneg (by positivity : (0 : ℝ) ≤ wt m) s,
            pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + sz l) s]
        · simp
    _ = Amaj b s m' m * ENNReal.ofReal ((wt m : ℝ) ^ s) := by
        rw [Amaj, ENNReal.tsum_mul_right]

include hb0 hbS hK in
/-- **The weighted bound**: `Σ W^{2s} (Kc)² ≤ (3^{n+1} Γ_s)² Σ W^{2s} c²`. -/
theorem nw_Kc_le (s : ℕ) (c : (Fin (n + 1) → ℕ) → ℝ) :
    nw s (Kc V c) ≤ (3 ^ (n + 1) * Gam b s) ^ 2 * nw s c := by
  rw [nw_eq, nw_eq]
  have hpt : ∀ m', ENNReal.ofReal ((wt m' : ℝ) ^ s * |Kc V c m'|) ≤
      ∑' m, Amaj b s m' m * ENNReal.ofReal ((wt m : ℝ) ^ s * |c m|) := by
    intro m'
    calc ENNReal.ofReal ((wt m' : ℝ) ^ s * |Kc V c m'|)
        = ENNReal.ofReal ((wt m' : ℝ) ^ s) * ENNReal.ofReal |Kc V c m'| :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal ((wt m' : ℝ) ^ s) * ∑' m, ENNReal.ofReal |Ker V m' m * c m| :=
          by gcongr; exact ofReal_abs_tsum_le _
      _ = ∑' m, ENNReal.ofReal ((wt m' : ℝ) ^ s * |Ker V m' m|) * ENNReal.ofReal |c m| := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun m => ?_
          rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ∑' m, Amaj b s m' m * ENNReal.ofReal ((wt m : ℝ) ^ s) * ENNReal.ofReal |c m| :=
          tsum_le_tsum fun m => by gcongr; exact ofReal_wt_Ker_le hb0 hbS hK s m' m
      _ = _ := by
          refine tsum_congr fun m => ?_
          rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  calc ∑' m', ENNReal.ofReal ((wt m' : ℝ) ^ s * |Kc V c m'|) ^ 2
      ≤ ∑' m', (∑' m, Amaj b s m' m * ENNReal.ofReal ((wt m : ℝ) ^ s * |c m|)) ^ 2 :=
        tsum_le_tsum fun m' => pow_le_pow_left' (hpt m') 2
    _ ≤ 3 ^ (n + 1) * Gam b s * (3 ^ (n + 1) * Gam b s) *
          ∑' m, ENNReal.ofReal ((wt m : ℝ) ^ s * |c m|) ^ 2 :=
        schur _ _ (Amaj_row s) (Amaj_col s)
    _ = _ := by ring

lemma Amaj_le_Gam (s : ℕ) (m' m : Fin (n + 1) → ℕ) : Amaj b s m' m ≤ Gam b s :=
  tsum_le_tsum fun l => by split_ifs <;> simp

lemma nw_zero (c : (Fin (n + 1) → ℕ) → ℝ) : nw 0 c = ∑' m, ENNReal.ofReal (c m ^ 2) := by
  simp [nw]

lemma nw_zero_ne_top {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2) :
    nw 0 c ≠ ⊤ := by
  rw [nw_zero, ← ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hc]
  exact ENNReal.ofReal_ne_top

lemma summable_sq_of_nw {c : (Fin (n + 1) → ℕ) → ℝ} (h : nw 0 c ≠ ⊤) :
    Summable fun m => c m ^ 2 := by
  refine summable_of_ofReal_abs ?_
  simpa [nw_zero, abs_sq] using h

include hb0 hbS hK in
lemma summable_Ker_mul {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (m' : Fin (n + 1) → ℕ) : Summable fun m => Ker V m' m * c m := by
  refine summable_of_ofReal_abs ?_
  have hle : ∑' m, ENNReal.ofReal |Ker V m' m * c m| ≤
      ∑' m, Amaj b 0 m' m * ENNReal.ofReal |c m| := by
    refine tsum_le_tsum fun m => ?_
    have := ofReal_wt_Ker_le hb0 hbS hK 0 m' m
    simp only [pow_zero, one_mul, ENNReal.ofReal_one, mul_one] at this
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    gcongr
  refine ne_top_of_le_ne_top ?_ hle
  have hsq := tsum_mul_sq_le (fun m => Amaj b 0 m' m) (fun m => ENNReal.ofReal |c m|)
  have hU : ∑' m, ENNReal.ofReal |c m| ^ 2 ≠ ⊤ := by
    have := nw_zero_ne_top hc
    rw [nw_zero] at this
    simpa [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] using this
  have hb : ∑' m, Amaj b 0 m' m * ENNReal.ofReal |c m| ^ 2 ≤
      Gam b 0 * ∑' m, ENNReal.ofReal |c m| ^ 2 := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun m => by gcongr; exact Amaj_le_Gam 0 m' m
  have hfin : (∑' m, Amaj b 0 m' m) * ∑' m, Amaj b 0 m' m * ENNReal.ofReal |c m| ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (Gam_zero_ne_top hb0 hbS))
      (Amaj_row 0 m')) (ne_top_of_le_ne_top (ENNReal.mul_ne_top (Gam_zero_ne_top hb0 hbS) hU) hb)
  intro htop
  rw [htop, ENNReal.top_pow two_ne_zero] at hsq
  exact hfin (top_le_iff.1 hsq)

include hb0 hbS hK in
lemma summable_Kc_sq {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2) :
    Summable fun m => Kc V c m ^ 2 := by
  refine summable_sq_of_nw (ne_top_of_le_ne_top ?_ (nw_Kc_le hb0 hbS hK 0 c))
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp)
    (Gam_zero_ne_top hb0 hbS))) (nw_zero_ne_top hc)

/-- The constant of the unweighted bound. -/
noncomputable def C0 (b : (Fin (n + 1) → ℕ) → ℝ) : ℝ := ((3 ^ (n + 1) * Gam b 0) ^ 2).toReal

include hb0 hbS hK in
lemma tsum_Kc_sq_le {c : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2) :
    ∑' m, Kc V c m ^ 2 ≤ C0 b * ∑' m, c m ^ 2 := by
  have h := nw_Kc_le hb0 hbS hK 0 c
  rw [nw_zero, nw_zero, ← ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _)
    (summable_Kc_sq hb0 hbS hK hc), ← ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hc] at h
  have hne : (3 ^ (n + 1) * Gam b 0) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) (Gam_zero_ne_top hb0 hbS))
  rw [← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg
    (tsum_nonneg fun m => sq_nonneg _))).1 h

lemma C0_nonneg : 0 ≤ C0 b := ENNReal.toReal_nonneg

include hb0 hbS hK in
lemma Kc_add {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) :
    Kc V (fun m => c m + d m) = fun m => Kc V c m + Kc V d m := by
  funext m'
  simp only [Kc, mul_add]
  exact (summable_Ker_mul hb0 hbS hK hc m').tsum_add (summable_Ker_mul hb0 hbS hK hd m')

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

include hb0 hbS hK in
lemma Bf_sq_le {c d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) :
    Bf V c d ^ 2 ≤ C0 b * (∑' m, c m ^ 2) * ∑' m, d m ^ 2 := by
  have h := tsum_mul_sq_le_real hc (summable_Kc_sq hb0 hbS hK hd)
  have h2 := tsum_Kc_sq_le hb0 hbS hK hd
  calc Bf V c d ^ 2 ≤ (∑' m, c m ^ 2) * ∑' m, Kc V d m ^ 2 := h
    _ ≤ (∑' m, c m ^ 2) * (C0 b * ∑' m, d m ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (tsum_nonneg fun m => sq_nonneg _)
    _ = _ := by ring

include hb0 hbS hK in
lemma Bf_sub_left {c c' d : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hc' : Summable fun m => c' m ^ 2) (hd : Summable fun m => d m ^ 2) :
    Bf V c d - Bf V c' d = Bf V (fun m => c m - c' m) d := by
  simp only [Bf, sub_mul]
  exact ((summable_mul_of_sq hc (summable_Kc_sq hb0 hbS hK hd)).tsum_sub
    (summable_mul_of_sq hc' (summable_Kc_sq hb0 hbS hK hd))).symm

include hb0 hbS hK in
lemma Bf_sub_right {c d d' : (Fin (n + 1) → ℕ) → ℝ} (hc : Summable fun m => c m ^ 2)
    (hd : Summable fun m => d m ^ 2) (hd' : Summable fun m => d' m ^ 2) :
    Bf V c d - Bf V c d' = Bf V c (fun m => d m - d' m) := by
  have hneg : Summable fun m => (-1 * d' m) ^ 2 := by simpa [neg_one_mul, neg_sq] using hd'
  have e : (fun m => d m - d' m) = fun m => d m + (-1) * d' m := by funext m; ring
  rw [e]
  simp only [Bf]
  rw [Kc_add hb0 hbS hK hd hneg, Kc_smul]
  simp only [mul_add]
  rw [(summable_mul_of_sq hc (summable_Kc_sq hb0 hbS hK hd)).tsum_add]
  · rw [show (∑' m, c m * (-1 * Kc V d' m)) = -∑' m, c m * Kc V d' m by
      rw [← tsum_neg]; congr 1; funext m; ring]
    ring
  · have := summable_mul_of_sq hc (summable_Kc_sq hb0 hbS hK hd')
    simpa [mul_neg, neg_mul, one_mul] using this.neg

end bound

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

/-- A symmetry type: a set `G` of relabellings and a character `χ` on it. -/
structure SymT (n : ℕ) where
  /-- The relabellings under which states transform. -/
  G : Equiv.Perm (Fin (n + 1)) → Prop
  /-- The character. -/
  χ : Equiv.Perm (Fin (n + 1)) → ℝ

/-- Full exchange symmetry `τ` as a symmetry type. -/
noncomputable def _root_.DFT.Continuum.Line.Stat.toSym (τ : Stat) : SymT n := ⟨fun _ => True, ch τ⟩

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
