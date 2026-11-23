/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.ChamberGS
import DFT.Continuum.Line.HardCore
import DFT.Continuum.Line.SpinWeak

/-!
# A fermionic ground state that is nonnegative on the ordered chamber

For a fermionic `H¹₀` state `Ψ`, let `u = 1_C |Ψ|` (`C` the ordered chamber) and
`Φ = Σ_σ sgn σ · u ∘ σ` (`PhiF`), the antisymmetrisation of `u`.

* `PhiF_mem`: `Φ` is a fermionic `H¹₀` state (`isWD_chamber`, `isWD_abs`, relabelling);
* `PhiF_eq_of_mem`: `Φ = |Ψ|` on the chamber; `abs_PhiF`: `|Φ| = |Ψ|` a.e.;
* `kinW_PhiF_le`: `T(Φ) ≤ T(Ψ)`;
* **`isGS_PhiF`**: if `Ψ` is a fermionic ground state, so is `Φ`, and `Φ ≥ 0` on the chamber.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-- `u = 1_C |Ψ|`. -/
noncomputable def uC (Ψ : Cfg n → ℝ) (x : Cfg n) : ℝ := |(Ord n).indicator Ψ x|

/-- Its weak derivatives. -/
noncomputable def DuC (Ψ : Cfg n → ℝ) (l : Fin (n + 1)) (x : Cfg n) : ℝ :=
  rsgn ((Ord n).indicator Ψ x) * dW l ((Ord n).indicator Ψ) x

/-- The antisymmetrised chamber state. -/
noncomputable def PhiF (Ψ : Cfg n → ℝ) : Cfg n → ℝ := alt .fer (uC Ψ)

/-- Its weak derivatives. -/
noncomputable def DPhi (Ψ : Cfg n → ℝ) (k : Fin (n + 1)) (x : Cfg n) : ℝ :=
  ∑ σ, ch .fer σ * DuC Ψ (σ⁻¹ k) (pm σ x)

lemma rsgn_zero : rsgn 0 = 0 := by simp [rsgn]

/-- Off the chamber `u` and its derivatives vanish. -/
lemma uC_of_notMem {Ψ : Cfg n → ℝ} {y : Cfg n} (hy : y ∉ Ord n) :
    uC Ψ y = 0 ∧ ∀ l, DuC Ψ l y = 0 := by
  simp [uC, DuC, indicator_of_notMem hy, rsgn_zero]

/-- Only the sorting permutation brings `x` into the chamber. -/
lemma pm_notMem_Ord {x : Cfg n} (hx : Function.Injective x) {σ τ : Equiv.Perm (Fin (n + 1))}
    (hσ : pm σ x ∈ Ord n) (hτ : τ ≠ σ) : pm τ x ∉ Ord n := fun h =>
  hτ (perm_eq_of_strictMono hx (mem_Ord_iff.1 h) (mem_Ord_iff.1 hσ))

/-- **`Φ = |Ψ|` on the chamber.** -/
lemma PhiF_eq_of_mem (Ψ : Cfg n → ℝ) {x : Cfg n} (hx : x ∈ Ord n) : PhiF Ψ x = |Ψ x| := by
  have hinj : Function.Injective x := (mem_Ord_iff.1 hx).injective
  have h1 : pm 1 x ∈ Ord n := by rw [pm_one]; exact hx
  simp only [PhiF, alt]
  rw [Finset.sum_eq_single 1 (fun σ _ hσ => by
      rw [(uC_of_notMem (pm_notMem_Ord hinj h1 hσ)).1, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [ch_fer, sgn_one, pm_one, uC, indicator_of_mem hx]

/-- At an injective configuration, only the sorting permutation contributes. -/
lemma PhiF_DPhi_sort {Ψ : Cfg n → ℝ} {x : Cfg n} (hx : Function.Injective x)
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : pm σ x ∈ Ord n) (k : Fin (n + 1)) :
    PhiF Ψ x = ch .fer σ * uC Ψ (pm σ x) ∧
      DPhi Ψ k x = ch .fer σ * DuC Ψ (σ⁻¹ k) (pm σ x) := by
  constructor
  · simp only [PhiF, alt]
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by
        rw [(uC_of_notMem (pm_notMem_Ord hx hσ hτ)).1, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  · simp only [DPhi]
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by
        rw [(uC_of_notMem (pm_notMem_Ord hx hσ hτ)).2, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]

section state

variable {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW .fer n)
include hΨ

lemma h1W_chamber : H1W ((Ord n).indicator Ψ) :=
  ⟨hΨ.1.indicator (measurableSet_OrdS _).nullMeasurableSet, fun k => ⟨_, isWD_chamber hΨ k⟩⟩

lemma memLp_uC : MemLp (uC Ψ) 2 (μN n) := (h1W_chamber hΨ).1.abs

lemma isWD_uC (l : Fin (n + 1)) : IsWD l (uC Ψ) (DuC Ψ l) := isWD_abs (h1W_chamber hΨ) l

lemma sum_PhiF (k : Fin (n + 1)) :
    MemLp (PhiF Ψ) 2 (μN n) ∧ IsWD k (PhiF Ψ) (DPhi Ψ k) :=
  IsWD.sum (k := k) Finset.univ (Φs := fun σ x => ch .fer σ * uC Ψ (pm σ x))
    (Gs := fun σ x => ch .fer σ * DuC Ψ (σ⁻¹ k) (pm σ x))
    (fun σ _ => ((memLp_uC hΨ).comp_measurePreserving (mpN σ)).const_mul _)
    (fun σ _ => ((isWD_uC hΨ (σ⁻¹ k)).comp_pm σ).const_mul _)

lemma memLp_PhiF : MemLp (PhiF Ψ) 2 (μN n) := (sum_PhiF hΨ 0).1

lemma isWD_PhiF (k : Fin (n + 1)) : IsWD k (PhiF Ψ) (DPhi Ψ k) := (sum_PhiF hΨ k).2

/-- **`Φ` is a fermionic `H¹₀` state.** -/
theorem PhiF_mem : PhiF Ψ ∈ DomW .fer n :=
  ⟨memLp_PhiF hΨ, fun k => ⟨_, isWD_PhiF hΨ k⟩, fun σ => ae_of_all _ fun x => alt_pm .fer _ σ x⟩

/-- `|Ψ(σx)| = |Ψ(x)|` for all `σ`, a.e. -/
lemma ae_abs_pm : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), |Ψ (pm σ x)| = |Ψ x| := by
  rw [ae_all_iff]
  intro σ
  filter_upwards [hΨ.2.2 σ] with x hx
  rw [hx, abs_mul, abs_ch, one_mul]

/-- `|∂_{σ⁻¹k}Ψ(σx)| = |∂ₖΨ(x)|` for all `σ`, `k`, a.e. -/
lemma ae_abs_dW_pm : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ k : Fin (n + 1),
    |dW (σ⁻¹ k) Ψ (pm σ x)| = |dW k Ψ x| := by
  rw [ae_all_iff]; intro σ
  rw [ae_all_iff]; intro k
  have h1 := (dW_spec (hΨ.2.1 (σ⁻¹ k))).comp_pm σ
  have h2 : IsWD k (fun x => ch .fer σ * Ψ x) (fun x => ch .fer σ * dW k Ψ x) :=
    (dW_spec (hΨ.2.1 k)).const_mul _
  have h3 := h1.congr (hΨ.2.2 σ)
  filter_upwards [IsWD.unique h3 h2] with x hx
  rw [hx, abs_mul, abs_ch, one_mul]

/-- `|∂ₗ u| ≤ |∂ₗ Ψ|` at relabelled points, a.e. -/
lemma ae_abs_DuC_pm : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ l : Fin (n + 1),
    |DuC Ψ l (pm σ x)| ≤ |dW l Ψ (pm σ x)| := by
  rw [ae_all_iff]; intro σ
  rw [ae_all_iff]; intro l
  have hd := dW_ae_eq (isWD_chamber hΨ l)
  filter_upwards [ae_pm hd σ] with x hx
  simp only [DuC]
  rw [hx, abs_mul]
  have hs : |rsgn ((Ord n).indicator Ψ (pm σ x))| ≤ 1 := abs_rsgn_le _
  have hi : |(Ord n).indicator (dW l Ψ) (pm σ x)| ≤ |dW l Ψ (pm σ x)| := by
    by_cases h : pm σ x ∈ Ord n
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, abs_zero]; exact abs_nonneg _
  calc |rsgn ((Ord n).indicator Ψ (pm σ x))| * |(Ord n).indicator (dW l Ψ) (pm σ x)|
      ≤ 1 * |dW l Ψ (pm σ x)| := mul_le_mul hs hi (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **`|Φ| = |Ψ|` a.e.** -/
theorem abs_PhiF : ∀ᵐ x ∂μN n, |PhiF Ψ x| = |Ψ x| := by
  filter_upwards [ae_injective, ae_abs_pm hΨ] with x hx habs
  obtain ⟨σ, hσ⟩ := exists_strictMono hx
  have hσC : pm σ x ∈ Ord n := mem_Ord_iff.2 hσ
  rw [(PhiF_DPhi_sort hx hσC 0).1, abs_mul, abs_ch, one_mul]
  simp only [uC, indicator_of_mem hσC, abs_abs]
  exact habs σ

/-- **`|∂ₖΦ| ≤ |∂ₖΨ|` a.e.** -/
theorem abs_DPhi_le (k : Fin (n + 1)) : ∀ᵐ x ∂μN n, |DPhi Ψ k x| ≤ |dW k Ψ x| := by
  filter_upwards [ae_injective, ae_abs_dW_pm hΨ, ae_abs_DuC_pm hΨ] with x hx hdW hDu
  obtain ⟨σ, hσ⟩ := exists_strictMono hx
  have hσC : pm σ x ∈ Ord n := mem_Ord_iff.2 hσ
  rw [(PhiF_DPhi_sort hx hσC k).2, abs_mul, abs_ch, one_mul]
  exact (hDu σ (σ⁻¹ k)).trans (hdW σ k).le

/-- **`T(Φ) ≤ T(Ψ)`.** -/
theorem kinW_PhiF_le : kinW (PhiF Ψ) ≤ kinW Ψ := by
  refine Finset.sum_le_sum fun k _ => ?_
  have hd := dW_ae_eq (isWD_PhiF hΨ k)
  have hm := memLp_dW hΨ k
  rw [integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx])]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_self_nonneg _) (int_mul_L2 hm hm) ?_
  filter_upwards [abs_DPhi_le hΨ k] with x hx
  rw [← abs_mul_abs_self (DPhi Ψ k x), ← abs_mul_abs_self (dW k Ψ x)]
  exact mul_le_mul hx hx (abs_nonneg _) (abs_nonneg _)

end state

/-- **The chamber ground state.** If `Ψ` is a fermionic `H¹₀` ground state, so is `Φ`; moreover
`Φ = |Ψ| ≥ 0` on the ordered chamber. -/
theorem isGS_PhiF {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .fer n w hw) v Ψ) : IsGS (settingW .fer n w hw) v (PhiF Ψ) := by
  have hD := PhiF_mem hΨ.1
  have habs := abs_PhiF hΨ.1
  have hsq : ∀ᵐ x ∂μN n, PhiF Ψ x * PhiF Ψ x = Ψ x * Ψ x := by
    filter_upwards [habs] with x hx
    rw [← abs_mul_abs_self, hx, abs_mul_abs_self]
  have hip : ip (μ := μN n) (PhiF Ψ) (PhiF Ψ) = ip (μ := μN n) Ψ Ψ := integral_congr_ae hsq
  have hQ : Q (settingW .fer n w hw) v (PhiF Ψ) ≤ Q (settingW .fer n w hw) v Ψ := by
    rw [QW_eq v hD, QW_eq v hΨ.1]
    have e : ∫ x, (LN n v x + w x) * (PhiF Ψ x * PhiF Ψ x) ∂μN n =
        ∫ x, (LN n v x + w x) * (Ψ x * Ψ x) ∂μN n :=
      integral_congr_ae (by filter_upwards [hsq] with x hx; rw [hx])
    rw [e]
    linarith [kinW_PhiF_le hΨ.1]
  refine ⟨hD, hip ▸ hΨ.2.1, fun φ hφ => ?_⟩
  rw [hip]
  have h0 : 0 ≤ ip (μ := μN n) φ φ := integral_nonneg fun x => mul_self_nonneg (φ x)
  exact (mul_le_mul_of_nonneg_right hQ h0).trans (hΨ.2.2 φ hφ)

end DFT.Continuum.Line
