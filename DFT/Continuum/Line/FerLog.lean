/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.FerGS
import DFT.Continuum.Line.LogEst

/-!
# The logarithmic estimate for fermionic ground states

Let `Ψ` be a fermionic `H¹₀` ground state, `u = 1_C |Ψ|` and `Φ = alt_fer u` (`PhiF`, again a
ground state). Its bosonic companion `B = alt_bos u` (`PhiB`) is `|Ψ|` a.e. and `Φ = S·B` with `S`
the chamber sign (`sgnC`). A symmetric test function `φ` vanishing linearly on the adjacent
diagonals gives the fermionic test function `alt_fer (1_C φ) = S·φ` (`phiF`), with derivatives
`S·∂φ`. Testing the Euler–Lagrange equation of `Φ` with it, the signs cancel:

* `eq_PhiB`: `B` satisfies the bosonic weak equation (with the fermionic energy) against every
  such `φ`;
* **`log_estimate_fer`**: Moser's logarithmic estimate for `B`, for symmetric `C¹` cutoffs `η`
  vanishing on the walls and on the diagonals.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### Sums over relabellings at an injective configuration -/

/-- At an injective configuration, a relabelling sum of functions vanishing off the chamber keeps
only the sorting permutation. -/
lemma sum_sort {F : Equiv.Perm (Fin (n + 1)) → Cfg n → ℝ} (hF : ∀ ρ y, y ∉ Ord n → F ρ y = 0)
    {x : Cfg n} (hx : Function.Injective x) {σ : Equiv.Perm (Fin (n + 1))} (hσ : pm σ x ∈ Ord n)
    (τ : Stat) : ∑ ρ, ch τ ρ * F ρ (pm ρ x) = ch τ σ * F σ (pm σ x) :=
  Finset.sum_eq_single σ (fun ρ _ hρ => by rw [hF ρ _ (pm_notMem_Ord hx hσ hρ), mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)

/-- The chamber sign: `sgn σ` for the sorting permutation `σ` of an injective `x`. -/
noncomputable def sgnC (x : Cfg n) : ℝ := ∑ σ, ch .fer σ * (Ord n).indicator (fun _ => 1) (pm σ x)

lemma sgnC_sort {x : Cfg n} (hx : Function.Injective x) {σ : Equiv.Perm (Fin (n + 1))}
    (hσ : pm σ x ∈ Ord n) : sgnC x = ch .fer σ := by
  rw [sgnC, sum_sort (F := fun _ => (Ord n).indicator fun _ => (1 : ℝ))
    (fun _ y hy => indicator_of_notMem hy _) hx hσ, indicator_of_mem hσ, mul_one]

/-! ### The bosonic companion -/

/-- `B = alt_bos (1_C |Ψ|)`. -/
noncomputable def PhiB (Ψ : Cfg n → ℝ) : Cfg n → ℝ := alt .bos (uC Ψ)

/-- Its weak derivatives. -/
noncomputable def DPhiB (Ψ : Cfg n → ℝ) (k : Fin (n + 1)) (x : Cfg n) : ℝ :=
  ∑ σ, ch .bos σ * DuC Ψ (σ⁻¹ k) (pm σ x)

lemma PhiB_nonneg (Ψ : Cfg n → ℝ) (x : Cfg n) : 0 ≤ PhiB Ψ x :=
  Finset.sum_nonneg fun σ _ => by simp only [ch_bos, one_mul, uC]; exact abs_nonneg _

lemma PhiB_pm (Ψ : Cfg n → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    PhiB Ψ (pm σ x) = PhiB Ψ x := by
  simp only [PhiB, alt_pm, ch_bos, one_mul]

/-- At an injective configuration, `Φ = S·B` and `∂Φ = S·∂B`. -/
lemma PhiF_DPhi_sgnC {Ψ : Cfg n → ℝ} {x : Cfg n} (hx : Function.Injective x) (k : Fin (n + 1)) :
    PhiF Ψ x = sgnC x * PhiB Ψ x ∧ DPhi Ψ k x = sgnC x * DPhiB Ψ k x := by
  obtain ⟨σ, hσ⟩ := exists_strictMono hx
  have hσC : pm σ x ∈ Ord n := mem_Ord_iff.2 hσ
  have hu : ∀ (_ : Equiv.Perm (Fin (n + 1))) y, y ∉ Ord n → uC Ψ y = 0 := fun _ y hy =>
    (uC_of_notMem hy).1
  have hd : ∀ (ρ : Equiv.Perm (Fin (n + 1))) y, y ∉ Ord n → DuC Ψ (ρ⁻¹ k) y = 0 :=
    fun ρ y hy => (uC_of_notMem hy).2 _
  rw [sgnC_sort hx hσC]
  refine ⟨?_, ?_⟩
  · simp only [PhiF, PhiB, alt]
    rw [sum_sort (F := fun _ => uC Ψ) hu hx hσC, sum_sort (F := fun _ => uC Ψ) hu hx hσC]
    simp
  · simp only [DPhi, DPhiB]
    rw [sum_sort (F := fun ρ => DuC Ψ (ρ⁻¹ k)) hd hx hσC,
      sum_sort (F := fun ρ => DuC Ψ (ρ⁻¹ k)) hd hx hσC]
    simp

lemma sgnC_mul_self {x : Cfg n} (hx : Function.Injective x) : sgnC x * sgnC x = 1 := by
  obtain ⟨σ, hσ⟩ := exists_strictMono hx
  rw [sgnC_sort hx (mem_Ord_iff.2 hσ), ch_mul_self]

section state

variable {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW .fer n)
include hΨ

lemma sum_PhiB (k : Fin (n + 1)) :
    MemLp (PhiB Ψ) 2 (μN n) ∧ IsWD k (PhiB Ψ) (DPhiB Ψ k) :=
  IsWD.sum (k := k) Finset.univ (Φs := fun σ x => ch .bos σ * uC Ψ (pm σ x))
    (Gs := fun σ x => ch .bos σ * DuC Ψ (σ⁻¹ k) (pm σ x))
    (fun σ _ => ((memLp_uC hΨ).comp_measurePreserving (mpN σ)).const_mul _)
    (fun σ _ => ((isWD_uC hΨ (σ⁻¹ k)).comp_pm σ).const_mul _)

lemma isWD_PhiB (k : Fin (n + 1)) : IsWD k (PhiB Ψ) (DPhiB Ψ k) := (sum_PhiB hΨ k).2

/-- **`B` is a bosonic `H¹₀` state.** -/
theorem PhiB_mem : PhiB Ψ ∈ DomW .bos n :=
  ⟨(sum_PhiB hΨ 0).1, fun k => ⟨_, isWD_PhiB hΨ k⟩,
    fun σ => ae_of_all _ fun x => by rw [PhiB_pm, ch_bos, one_mul]⟩

/-- **`B = |Ψ|` a.e.** -/
theorem PhiB_ae_eq_abs : ∀ᵐ x ∂μN n, PhiB Ψ x = |Ψ x| := by
  filter_upwards [ae_injective, abs_PhiF hΨ] with x hx habs
  rw [← habs, (PhiF_DPhi_sgnC (Ψ := Ψ) hx 0).1, abs_mul, abs_of_nonneg (PhiB_nonneg Ψ x)]
  obtain ⟨σ, hσ⟩ := exists_strictMono hx
  rw [sgnC_sort hx (mem_Ord_iff.2 hσ), abs_ch, one_mul]

end state

/-! ### Fermionic test functions from symmetric ones -/

/-- `alt_fer (1_C φ)`. -/
noncomputable def phiF (φ : Cfg n → ℝ) : Cfg n → ℝ := alt .fer ((Ord n).indicator φ)

/-- Its weak derivatives. -/
noncomputable def DphiF (φ : Cfg n → ℝ) (k : Fin (n + 1)) (x : Cfg n) : ℝ :=
  ∑ σ, ch .fer σ * (Ord n).indicator (dW (σ⁻¹ k) φ) (pm σ x)

section test

variable {φ : Cfg n → ℝ} (hφ : H1W φ) (hφs : ∀ σ x, φ (pm σ x) = φ x) {L : ℝ} (hL0 : 0 ≤ L)
  (hL : ∀ j : Fin n, ∀ᵐ x ∂μN n, |φ x| ≤ L * |x j.succ - x j.castSucc|)

include hφ hL0 hL in
lemma sum_phiF (k : Fin (n + 1)) : MemLp (phiF φ) 2 (μN n) ∧ IsWD k (phiF φ) (DphiF φ k) :=
  IsWD.sum (k := k) Finset.univ (Φs := fun σ x => ch .fer σ * (Ord n).indicator φ (pm σ x))
    (Gs := fun σ x => ch .fer σ * (Ord n).indicator (dW (σ⁻¹ k) φ) (pm σ x))
    (fun σ _ => ((hφ.1.indicator (measurableSet_OrdS _).nullMeasurableSet).comp_measurePreserving
      (mpN σ)).const_mul _)
    (fun σ _ =>
      ((isWD_chamber_of_bound hφ.1 (dW_spec (hφ.2 (σ⁻¹ k))) hL0 hL).comp_pm σ).const_mul _)

include hφ hL0 hL in
/-- **`alt_fer (1_C φ)` is a fermionic `H¹₀` state.** -/
theorem phiF_mem : phiF φ ∈ DomW .fer n :=
  ⟨(sum_phiF hφ hL0 hL 0).1, fun k => ⟨_, (sum_phiF hφ hL0 hL k).2⟩,
    fun σ => ae_of_all _ fun x => alt_pm .fer _ σ x⟩

include hφs in
lemma phiF_sgnC {x : Cfg n} (hx : Function.Injective x) : phiF φ x = sgnC x * φ x := by
  obtain ⟨σ, hσ⟩ := exists_strictMono hx
  have hσC : pm σ x ∈ Ord n := mem_Ord_iff.2 hσ
  rw [phiF, alt, sum_sort (F := fun _ => (Ord n).indicator φ)
    (fun _ y hy => indicator_of_notMem hy _) hx hσC, indicator_of_mem hσC, hφs, sgnC_sort hx hσC]

include hφ hφs in
/-- `∂_{σ⁻¹k}φ(σx) = ∂ₖφ(x)` for all `σ`, `k`, a.e. -/
lemma ae_dW_pm_sym : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ k : Fin (n + 1),
    dW (σ⁻¹ k) φ (pm σ x) = dW k φ x := by
  rw [ae_all_iff]; intro σ
  rw [ae_all_iff]; intro k
  have h1 := (dW_spec (hφ.2 (σ⁻¹ k))).comp_pm σ
  have he : (fun x => φ (pm σ x)) = φ := funext fun x => hφs σ x
  rw [he] at h1
  exact IsWD.unique h1 (dW_spec (hφ.2 k))

include hφ hφs hL0 hL in
/-- `∂ₖ(alt_fer (1_C φ)) = S·∂ₖφ` a.e. -/
lemma dW_phiF_ae (k : Fin (n + 1)) : ∀ᵐ x ∂μN n, dW k (phiF φ) x = sgnC x * dW k φ x := by
  filter_upwards [dW_ae_eq (sum_phiF hφ hL0 hL k).2, ae_injective, ae_dW_pm_sym hφ hφs]
    with x hd hx hsym
  obtain ⟨σ, hσ⟩ := exists_strictMono hx
  have hσC : pm σ x ∈ Ord n := mem_Ord_iff.2 hσ
  rw [hd, DphiF, sum_sort (F := fun ρ => (Ord n).indicator (dW (ρ⁻¹ k) φ))
    (fun _ y hy => indicator_of_notMem hy _) hx hσC, indicator_of_mem hσC, hsym, sgnC_sort hx hσC]

end test

/-! ### The weak equation for the bosonic companion -/

section equation

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}

/-- **The bosonic companion satisfies the weak equation** against symmetric test functions
vanishing linearly on the adjacent diagonals, with the energy `E` of the fermionic ground state. -/
theorem eq_PhiB (hΨ : IsGS (settingW .fer n w hw) v Ψ) {φ : Cfg n → ℝ} (hφ : H1W φ)
    (hφs : ∀ σ x, φ (pm σ x) = φ x) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ j : Fin n, ∀ᵐ x ∂μN n, |φ x| ≤ L * |x j.succ - x j.castSucc|) :
    h0W n w (PhiB Ψ) φ + ∫ x, LN n v x * (PhiB Ψ x * φ x) ∂μN n =
      Q (settingW .fer n w hw) v (PhiF Ψ) / ip (μ := μN n) (PhiF Ψ) (PhiF Ψ) *
        ∫ x, PhiB Ψ x * φ x ∂μN n := by
  have hel := euler_lagrange (isGS_PhiF hΨ) (phiF_mem hφ hL0 hL)
  change h0W n w (PhiF Ψ) (phiF φ) + ∫ x, LN n v x * (PhiF Ψ x * phiF φ x) ∂μN n =
    _ * ∫ x, PhiF Ψ x * phiF φ x ∂μN n at hel
  have hp : ∀ᵐ x ∂μN n, PhiF Ψ x * phiF φ x = PhiB Ψ x * φ x := by
    filter_upwards [ae_injective] with x hx
    rw [(PhiF_DPhi_sgnC (Ψ := Ψ) hx 0).1, phiF_sgnC hφs hx]
    linear_combination (PhiB Ψ x * φ x) * sgnC_mul_self hx
  have hd : ∀ k, ∀ᵐ x ∂μN n, dW k (PhiF Ψ) x * dW k (phiF φ) x =
      dW k (PhiB Ψ) x * dW k φ x := fun k => by
    filter_upwards [ae_injective, dW_ae_eq (isWD_PhiF hΨ.1 k), dW_ae_eq (isWD_PhiB hΨ.1 k),
      dW_phiF_ae hφ hφs hL0 hL k] with x hx h1 h2 h3
    rw [h1, h2, h3, (PhiF_DPhi_sgnC (Ψ := Ψ) hx k).2]
    linear_combination (DPhiB Ψ k x * dW k φ x) * sgnC_mul_self hx
  have e1 : ∫ x, PhiF Ψ x * phiF φ x ∂μN n = ∫ x, PhiB Ψ x * φ x ∂μN n := integral_congr_ae hp
  have e2 : ∫ x, LN n v x * (PhiF Ψ x * phiF φ x) ∂μN n =
      ∫ x, LN n v x * (PhiB Ψ x * φ x) ∂μN n :=
    integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx])
  have e3 : h0W n w (PhiF Ψ) (phiF φ) = h0W n w (PhiB Ψ) φ := by
    simp only [h0W]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => integral_congr_ae (hd k)
    · exact integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx])
  rw [e1, e2, e3] at hel
  exact hel

/-! ### The estimate -/

/-- A `C¹` function vanishing on the plane `xᵢ = xⱼ` is `O(|xⱼ - xᵢ|)` on the cube. -/
lemma abs_le_of_plane' {P : Cfg n → ℝ} (hP : ContDiff ℝ 1 P) {i j : Fin (n + 1)} (hij : i ≠ j)
    (hplane : ∀ x, x i = x j → P x = 0) :
    ∃ C, 0 ≤ C ∧ ∀ᵐ x ∂μN n, |P x| ≤ C * |x j - x i| := by
  obtain ⟨C1, hC1, h1⟩ := abs_le_of_plane hP hij hplane
  obtain ⟨C2, hC2, h2⟩ := abs_le_of_plane hP hij.symm fun x hx => hplane x hx.symm
  refine ⟨max C1 C2, le_max_of_le_left hC1, ?_⟩
  filter_upwards [ae_cube] with x hx
  rcases le_total (x i) (x j) with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact (h1 x (cube_subset hx) h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.2 h))
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact (h2 x (cube_subset hx) h).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sub_nonneg.2 h))

/-- **The logarithmic estimate for fermions.** Let `Ψ` be a fermionic `H¹₀` ground state, `B` its
bosonic companion (`= |Ψ|` a.e.), `E` the energy, `|E - V| ≤ C` a.e., and `η` a symmetric `C¹`
cutoff vanishing on the walls and on the diagonals. Then for every `ε > 0`,
`Σ_k ∫ η² (∂ₖB/(B+ε))² ≤ 4 Σ_k ∫ (∂ₖη)² + 2C ∫ η²`. -/
theorem log_estimate_fer (hΨ : IsGS (settingW .fer n w hw) v Ψ)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η) (hηs : ∀ σ x, η (pm σ x) = η x)
    (hηw : ∀ x k, (x k = 0 ∨ x k = 1) → η x = 0)
    (hηd : ∀ x i j, i ≠ j → x i = x j → η x = 0) {ε : ℝ} (hε : 0 < ε) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂μN n, |Q (settingW .fer n w hw) v (PhiF Ψ) / ip (μ := μN n) (PhiF Ψ) (PhiF Ψ) -
      (LN n v x + w x)| ≤ C) :
    ∑ k, ∫ x, (η x * (dW k (PhiB Ψ) x / (PhiB Ψ x + ε))) ^ 2 ∂μN n ≤
      4 * ∑ k, ∫ x, dk k η x ^ 2 ∂μN n + 2 * C * ∫ x, η x ^ 2 ∂μN n := by
  have hD := PhiB_mem hΨ.1
  set u := PhiB Ψ
  have hu0 : ∀ x, 0 ≤ u x := PhiB_nonneg Ψ
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  set φ := logTest η u ε
  have hφs : ∀ σ x, φ (pm σ x) = φ x := fun σ x => by
    simp only [φ, logTest, hηs, u, PhiB_pm]
  -- `|φ| ≤ (Bη/ε) |η|`, and `|η| ≤ Lⱼ |x_{j+1} - x_j|`
  have hφη : ∀ᵐ x ∂μN n, |φ x| ≤ max Bη 0 / ε * |η x| := by
    filter_upwards [hBη] with x hx
    rw [Real.norm_eq_abs] at hx
    have hp : 0 < u x + ε := by linarith [hu0 x]
    have e : φ x = η x * η x / (u x + ε) := by
      simp only [φ, logTest, Gr_of_nonneg (hu0 x)]; field_simp; ring
    rw [e, abs_div, abs_of_pos hp, abs_mul, div_le_iff₀ hp]
    have h1 : |η x| ≤ max Bη 0 := hx.trans (le_max_left _ _)
    have h2 : max Bη 0 / ε * |η x| * ε ≤ max Bη 0 / ε * |η x| * (u x + ε) :=
      mul_le_mul_of_nonneg_left (by linarith [hu0 x])
        (mul_nonneg (div_nonneg (le_max_right _ _) hε.le) (abs_nonneg _))
    have h3 : max Bη 0 / ε * |η x| * ε = max Bη 0 * |η x| := by field_simp
    nlinarith [abs_nonneg (η x)]
  have hplane : ∀ j : Fin n, ∃ Lj, 0 ≤ Lj ∧
      ∀ᵐ x ∂μN n, |η x| ≤ Lj * |x j.succ - x j.castSucc| := fun j =>
    abs_le_of_plane' hη (Fin.castSucc_lt_succ (i := j)).ne
      fun x hx => hηd x _ _ (Fin.castSucc_lt_succ (i := j)).ne hx
  choose Lj hLj0 hLj using hplane
  set L := max Bη 0 / ε * ∑ j, Lj j
  have hL0 : 0 ≤ L :=
    mul_nonneg (div_nonneg (le_max_right _ _) hε.le) (Finset.sum_nonneg fun j _ => hLj0 j)
  have hL : ∀ j : Fin n, ∀ᵐ x ∂μN n, |φ x| ≤ L * |x j.succ - x j.castSucc| := fun j => by
    filter_upwards [hφη, hLj j] with x h1 h2
    have hs : Lj j ≤ ∑ i, Lj i :=
      Finset.single_le_sum (fun i _ => hLj0 i) (Finset.mem_univ j)
    calc |φ x| ≤ max Bη 0 / ε * |η x| := h1
      _ ≤ max Bη 0 / ε * (Lj j * |x j.succ - x j.castSucc|) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (le_max_right _ _) hε.le)
      _ ≤ max Bη 0 / ε * ((∑ i, Lj i) * |x j.succ - x j.castSucc|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (abs_nonneg _))
            (div_nonneg (le_max_right _ _) hε.le)
      _ = L * |x j.succ - x j.castSucc| := by ring
  have hφ : H1W φ := h1W_logTest (h1W_of_mem hD) hη hηw hε
  exact log_estimate_of_eq hw hD (ae_of_all _ hu0) hη hηw hε hC0 hC
    (eq_PhiB hΨ hφ hφs hL0 hL)

end equation

end DFT.Continuum.Line
