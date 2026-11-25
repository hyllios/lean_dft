/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.HK.YoungChamber
import DFT.Continuum.Line.Symmetry.HardCore
import DFT.Continuum.Line.UCP.AbsW

/-!
# Ground states of mixed symmetry: the chamber state and the logarithmic estimate

The chamber construction for the Young symmetry. For `Ψ ∈ DomWS (ymix a)` let
`u = 1_{RY} |Ψ|`, `Φ = Σ_{σ ∈ YG a} sgn σ · u ∘ σ` (`PhiY`) and `B = Σ_{σ ∈ YG a} u ∘ σ`
(`PhiBY`, `= |Ψ|` a.e.).

* `sumY`: sums over the Young group, `isWD_sumY`, `sumY_sort` (at an injective point of the cube
  only the sorting relabelling contributes);
* `PhiY_mem`, `abs_PhiY`, `kinW_PhiY_le`, **`isGS_PhiY`**: `Φ` is again a ground state;
* `phiY φ = Σ sgn σ · (1_{RY} φ) ∘ σ` is a test function of mixed symmetry for `YG a`-symmetric
  `φ` vanishing linearly on same-group planes, with derivatives `S · ∂φ`;
* `eq_PhiBY`: `B` satisfies the weak equation (with the energy of `Φ`) against such `φ`;
* **`log_estimate_Y`**: Moser's logarithmic estimate for `B`, for `YG a`-symmetric cutoffs
  vanishing on the walls and on the same-group diagonals.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {a : ℕ}

/-! ### Sums over the Young group -/

open Classical in
/-- `Σ_{σ ∈ YG a} c(σ) · F(σ) ∘ σ`. -/
noncomputable def sumY (a : ℕ) (c : Equiv.Perm (Fin (n + 1)) → ℝ)
    (F : Equiv.Perm (Fin (n + 1)) → Cfg n → ℝ) (x : Cfg n) : ℝ :=
  ∑ σ, if YG a σ then c σ * F σ (pm σ x) else 0

lemma altY_eq_sumY (f : Cfg n → ℝ) : altY a f = sumY a sgn (fun _ => f) := rfl

/-- At an injective point of the cube, only the sorting relabelling contributes. -/
lemma sumY_sort {c : Equiv.Perm (Fin (n + 1)) → ℝ} {F : Equiv.Perm (Fin (n + 1)) → Cfg n → ℝ}
    (hF : ∀ ρ y, y ∉ RY a n → F ρ y = 0) {x : Cfg n} (hx : x ∈ Cube n)
    (hinj : Function.Injective x) {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ)
    (hσR : pm σ x ∈ RY a n) : sumY a c F x = c σ * F σ (pm σ x) := by
  classical
  unfold sumY
  rw [Finset.sum_eq_single σ (fun ρ _ hρ => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · simp only [hσ, ↓reduceIte]
  · by_cases hρY : YG a ρ
    · simp only [hρY, ↓reduceIte]
      rw [hF ρ _ (fun hR => hρ (YG_eq_of_mem_RY hx hinj hρY hσ hR hσR)), mul_zero]
    · simp only [hρY, ↓reduceIte]

/-- Weak derivatives of Young sums. -/
lemma isWD_sumY (c : Equiv.Perm (Fin (n + 1)) → ℝ) {F G : Equiv.Perm (Fin (n + 1)) → Cfg n → ℝ}
    {k : Fin (n + 1)} (hF : ∀ σ, YG a σ → MemLp (F σ) 2 (μN n))
    (hG : ∀ σ, YG a σ → IsWD (σ⁻¹ k) (F σ) (G σ)) :
    MemLp (sumY a c F) 2 (μN n) ∧ IsWD k (sumY a c F) (sumY a c G) := by
  classical
  exact IsWD.sum (k := k) Finset.univ
    (Φs := fun σ x => if YG a σ then c σ * F σ (pm σ x) else 0)
    (Gs := fun σ x => if YG a σ then c σ * G σ (pm σ x) else 0)
    (fun σ _ => by
      by_cases hσ : YG a σ
      · simp only [hσ, ↓reduceIte]
        exact ((hF σ hσ).comp_measurePreserving (mpN σ)).const_mul _
      · simp only [hσ, ↓reduceIte]; exact MemLp.zero)
    (fun σ _ => by
      by_cases hσ : YG a σ
      · simp only [hσ, ↓reduceIte]; exact ((hG σ hσ).comp_pm σ).const_mul _
      · simp only [hσ, ↓reduceIte]; exact IsWD.zero k)

/-- The symmetrisation over the Young group is `YG a`-invariant. -/
lemma sumY_one_pm (f : Cfg n → ℝ) {ρ : Equiv.Perm (Fin (n + 1))} (hρ : YG a ρ) (x : Cfg n) :
    sumY a (fun _ => 1) (fun _ => f) (pm ρ x) = sumY a (fun _ => 1) (fun _ => f) x := by
  classical
  simp only [sumY]
  refine Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, ← pm_mul]
  have hiff : YG a (ρ * σ) ↔ YG a σ :=
    ⟨fun h => by simpa using YG_mul (YG_inv hρ) h, fun h => YG_mul hρ h⟩
  simp only [hiff]

/-! ### The chamber state -/

/-- `u = 1_{RY} |Ψ|`. -/
noncomputable def uY (a : ℕ) (Ψ : Cfg n → ℝ) (x : Cfg n) : ℝ := |(RY a n).indicator Ψ x|

/-- Its weak derivatives. -/
noncomputable def DuY (a : ℕ) (Ψ : Cfg n → ℝ) (l : Fin (n + 1)) (x : Cfg n) : ℝ :=
  rsgn ((RY a n).indicator Ψ x) * dW l ((RY a n).indicator Ψ) x

/-- `Φ = Σ_{σ ∈ YG a} sgn σ · u ∘ σ`. -/
noncomputable def PhiY (a : ℕ) (Ψ : Cfg n → ℝ) : Cfg n → ℝ := altY a (uY a Ψ)

noncomputable def DPhiY (a : ℕ) (Ψ : Cfg n → ℝ) (k : Fin (n + 1)) : Cfg n → ℝ :=
  sumY a sgn fun σ => DuY a Ψ (σ⁻¹ k)

/-- The companion `B = Σ_{σ ∈ YG a} u ∘ σ`. -/
noncomputable def PhiBY (a : ℕ) (Ψ : Cfg n → ℝ) : Cfg n → ℝ := sumY a (fun _ => 1) fun _ => uY a Ψ

noncomputable def DPhiBY (a : ℕ) (Ψ : Cfg n → ℝ) (k : Fin (n + 1)) : Cfg n → ℝ :=
  sumY a (fun _ => 1) fun σ => DuY a Ψ (σ⁻¹ k)

/-- The Young chamber sign. -/
noncomputable def sgnY (a : ℕ) : Cfg n → ℝ := sumY a sgn fun _ => (RY a n).indicator fun _ => 1

lemma uY_of_notMem {Ψ : Cfg n → ℝ} {y : Cfg n} (hy : y ∉ RY a n) :
    uY a Ψ y = 0 ∧ ∀ l, DuY a Ψ l y = 0 := by
  simp [uY, DuY, indicator_of_notMem hy, rsgn]

/-- The sorted forms. -/
lemma sorted_Y {Ψ : Cfg n → ℝ} {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x)
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG a σ) (hσR : pm σ x ∈ RY a n) (k : Fin (n + 1)) :
    PhiY a Ψ x = sgn σ * uY a Ψ (pm σ x) ∧ DPhiY a Ψ k x = sgn σ * DuY a Ψ (σ⁻¹ k) (pm σ x) ∧
      PhiBY a Ψ x = uY a Ψ (pm σ x) ∧ DPhiBY a Ψ k x = DuY a Ψ (σ⁻¹ k) (pm σ x) ∧
      sgnY a x = sgn σ := by
  have hu : ∀ (_ : Equiv.Perm (Fin (n + 1))) y, y ∉ RY a n → uY a Ψ y = 0 :=
    fun _ _ hy => (uY_of_notMem hy).1
  have hd : ∀ (ρ : Equiv.Perm (Fin (n + 1))) y, y ∉ RY a n → DuY a Ψ (ρ⁻¹ k) y = 0 :=
    fun _ _ hy => (uY_of_notMem hy).2 _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [PhiY, altY_eq_sumY]; exact sumY_sort hu hx hinj hσ hσR
  · exact sumY_sort hd hx hinj hσ hσR
  · rw [PhiBY, sumY_sort hu hx hinj hσ hσR, one_mul]
  · rw [DPhiBY, sumY_sort hd hx hinj hσ hσR, one_mul]
  · rw [sgnY, sumY_sort (F := fun _ => (RY a n).indicator fun _ => (1 : ℝ))
      (fun _ y hy => indicator_of_notMem hy _) hx hinj hσ hσR, indicator_of_mem hσR, mul_one]

section state

variable {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomWS (ymix a))
include hΨ

lemma h1W_RY : H1W ((RY a n).indicator Ψ) :=
  ⟨hΨ.1.indicator measurableSet_RY.nullMeasurableSet, fun k => ⟨_, isWD_RY hΨ k⟩⟩

lemma memLp_uY : MemLp (uY a Ψ) 2 (μN n) := (h1W_RY hΨ).1.abs

lemma isWD_uY (l : Fin (n + 1)) : IsWD l (uY a Ψ) (DuY a Ψ l) := isWD_abs (h1W_RY hΨ) l

lemma sum_PhiY (k : Fin (n + 1)) :
    MemLp (PhiY a Ψ) 2 (μN n) ∧ IsWD k (PhiY a Ψ) (DPhiY a Ψ k) :=
  isWD_sumY sgn (fun _ _ => memLp_uY hΨ) (fun σ _ => isWD_uY hΨ (σ⁻¹ k))

lemma sum_PhiBY (k : Fin (n + 1)) :
    MemLp (PhiBY a Ψ) 2 (μN n) ∧ IsWD k (PhiBY a Ψ) (DPhiBY a Ψ k) :=
  isWD_sumY _ (fun _ _ => memLp_uY hΨ) (fun σ _ => isWD_uY hΨ (σ⁻¹ k))

/-- **`Φ` is a state of mixed symmetry.** -/
theorem PhiY_mem : PhiY a Ψ ∈ DomWS (ymix a) :=
  ⟨(sum_PhiY hΨ 0).1, fun k => ⟨_, (sum_PhiY hΨ k).2⟩,
    fun _ hρ => ae_of_all _ fun x => altY_pm _ hρ x⟩

lemma h1W_PhiBY : H1W (PhiBY a Ψ) := ⟨(sum_PhiBY hΨ 0).1, fun k => ⟨_, (sum_PhiBY hΨ k).2⟩⟩

lemma ae_abs_pmY : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG a σ →
    |Ψ (pm σ x)| = |Ψ x| := by
  rw [ae_all_iff]
  intro σ
  by_cases hσ : YG a σ
  · filter_upwards [hΨ.2.2 σ hσ] with x hx _
    change Ψ (pm σ x) = sgn σ * Ψ x at hx
    rw [hx, abs_mul, abs_sgn, one_mul]
  · exact ae_of_all _ fun _ h => absurd h hσ

lemma ae_abs_dW_pmY : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG a σ → ∀ k : Fin (n + 1),
    |dW (σ⁻¹ k) Ψ (pm σ x)| = |dW k Ψ x| := by
  rw [ae_all_iff]; intro σ
  by_cases hσ : YG a σ
  · have H : ∀ k : Fin (n + 1), ∀ᵐ x ∂μN n, |dW (σ⁻¹ k) Ψ (pm σ x)| = |dW k Ψ x| := fun k => by
      have h1 := (dW_spec (hΨ.2.1 (σ⁻¹ k))).comp_pm σ
      have h2 : IsWD k (fun x => sgn σ * Ψ x) (fun x => sgn σ * dW k Ψ x) :=
        (dW_spec (hΨ.2.1 k)).const_mul _
      have h3 := h1.congr (hΨ.2.2 σ hσ)
      filter_upwards [IsWD.unique h3 h2] with x hx
      rw [hx, abs_mul, abs_sgn, one_mul]
    filter_upwards [ae_all_iff.2 H] with x hx _ k using hx k
  · exact ae_of_all _ fun _ h => absurd h hσ

lemma ae_abs_DuY_pm : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ l : Fin (n + 1),
    |DuY a Ψ l (pm σ x)| ≤ |dW l Ψ (pm σ x)| := by
  rw [ae_all_iff]; intro σ
  rw [ae_all_iff]; intro l
  have hd := dW_ae_eq (isWD_RY hΨ l)
  filter_upwards [ae_pm hd σ] with x hx
  simp only [DuY]
  rw [hx, abs_mul]
  have hs : |rsgn ((RY a n).indicator Ψ (pm σ x))| ≤ 1 := abs_rsgn_le _
  have hi : |(RY a n).indicator (dW l Ψ) (pm σ x)| ≤ |dW l Ψ (pm σ x)| := by
    by_cases h : pm σ x ∈ RY a n
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, abs_zero]; exact abs_nonneg _
  calc |rsgn ((RY a n).indicator Ψ (pm σ x))| * |(RY a n).indicator (dW l Ψ) (pm σ x)|
      ≤ 1 * |dW l Ψ (pm σ x)| := mul_le_mul hs hi (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **`|Φ| = |Ψ|` a.e.** -/
theorem abs_PhiY : ∀ᵐ x ∂μN n, |PhiY a Ψ x| = |Ψ x| := by
  filter_upwards [ae_cube, ae_injective, ae_abs_pmY hΨ] with x hx hinj habs
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
  rw [(sorted_Y hx hinj hσ hσR 0).1, abs_mul, abs_sgn, one_mul]
  simp only [uY, indicator_of_mem hσR, abs_abs]
  exact habs σ hσ

/-- **`B = |Ψ|` a.e.** -/
theorem PhiBY_ae_eq_abs : ∀ᵐ x ∂μN n, PhiBY a Ψ x = |Ψ x| := by
  filter_upwards [ae_cube, ae_injective, ae_abs_pmY hΨ] with x hx hinj habs
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
  rw [(sorted_Y hx hinj hσ hσR 0).2.2.1]
  simp only [uY, indicator_of_mem hσR]
  exact habs σ hσ

/-- **`|∂ₖΦ| ≤ |∂ₖΨ|` a.e.** -/
theorem abs_DPhiY_le (k : Fin (n + 1)) : ∀ᵐ x ∂μN n, |DPhiY a Ψ k x| ≤ |dW k Ψ x| := by
  filter_upwards [ae_cube, ae_injective, ae_abs_dW_pmY hΨ, ae_abs_DuY_pm hΨ]
    with x hx hinj hdW hDu
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
  rw [(sorted_Y hx hinj hσ hσR k).2.1, abs_mul, abs_sgn, one_mul]
  exact (hDu σ (σ⁻¹ k)).trans (hdW σ hσ k).le

/-- **`T(Φ) ≤ T(Ψ)`.** -/
theorem kinW_PhiY_le : kinW (PhiY a Ψ) ≤ kinW Ψ := by
  refine Finset.sum_le_sum fun k _ => ?_
  have hd := dW_ae_eq (sum_PhiY hΨ k).2
  have hm := memLp_dW_H (h1W_of_mem hΨ) k
  rw [integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx])]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_self_nonneg _) (int_mul_L2 hm hm) ?_
  filter_upwards [abs_DPhiY_le hΨ k] with x hx
  rw [← abs_mul_abs_self (DPhiY a Ψ k x), ← abs_mul_abs_self (dW k Ψ x)]
  exact mul_le_mul hx hx (abs_nonneg _) (abs_nonneg _)

end state

lemma PhiBY_nonneg (Ψ : Cfg n → ℝ) (x : Cfg n) : 0 ≤ PhiBY a Ψ x := by
  classical
  refine Finset.sum_nonneg fun σ _ => ?_
  split_ifs
  · rw [one_mul]; exact abs_nonneg _
  · exact le_rfl

lemma PhiBY_pm (Ψ : Cfg n → ℝ) {ρ : Equiv.Perm (Fin (n + 1))} (hρ : YG a ρ) (x : Cfg n) :
    PhiBY a Ψ (pm ρ x) = PhiBY a Ψ x :=
  sumY_one_pm _ hρ x

/-- **The chamber ground state.** -/
theorem isGS_PhiY {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingWS (ymix a) w hw) v Ψ) :
    IsGS (settingWS (ymix a) w hw) v (PhiY a Ψ) := by
  have hD := PhiY_mem hΨ.1
  have habs := abs_PhiY hΨ.1
  have hsq : ∀ᵐ x ∂μN n, PhiY a Ψ x * PhiY a Ψ x = Ψ x * Ψ x := by
    filter_upwards [habs] with x hx
    rw [← abs_mul_abs_self, hx, abs_mul_abs_self]
  have hip : ip (μ := μN n) (PhiY a Ψ) (PhiY a Ψ) = ip (μ := μN n) Ψ Ψ := integral_congr_ae hsq
  have hQ : Q (settingWS (ymix a) w hw) v (PhiY a Ψ) ≤ Q (settingWS (ymix a) w hw) v Ψ := by
    rw [QW_eq v hD, QW_eq v hΨ.1]
    have e : ∫ x, (LN n v x + w x) * (PhiY a Ψ x * PhiY a Ψ x) ∂μN n =
        ∫ x, (LN n v x + w x) * (Ψ x * Ψ x) ∂μN n :=
      integral_congr_ae (by filter_upwards [hsq] with x hx; rw [hx])
    rw [e]
    linarith [kinW_PhiY_le hΨ.1]
  refine ⟨hD, hip ▸ hΨ.2.1, fun φ hφ => ?_⟩
  rw [hip]
  have h0 : 0 ≤ ip (μ := μN n) φ φ := integral_nonneg fun x => mul_self_nonneg (φ x)
  exact (mul_le_mul_of_nonneg_right hQ h0).trans (hΨ.2.2 φ hφ)

/-! ### Test functions of mixed symmetry -/

/-- `Σ_{σ ∈ YG a} sgn σ · (1_{RY} φ) ∘ σ`. -/
noncomputable def phiY (a : ℕ) (φ : Cfg n → ℝ) : Cfg n → ℝ := altY a ((RY a n).indicator φ)

noncomputable def DphiY (a : ℕ) (φ : Cfg n → ℝ) (k : Fin (n + 1)) : Cfg n → ℝ :=
  sumY a sgn fun σ => (RY a n).indicator (dW (σ⁻¹ k) φ)

section test

variable {φ : Cfg n → ℝ} (hφ : H1W φ) (hφs : ∀ σ, YG a σ → ∀ x, φ (pm σ x) = φ x)
  (hL : ∀ p ∈ pY a n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1|)

include hφ hL in
lemma isWD_RY_of_bound (k : Fin (n + 1)) :
    IsWD k ((RY a n).indicator φ) ((RY a n).indicator (dW k φ)) :=
  ((isWD_pairs_of_bound hφ.1 (dW_spec (hφ.2 k)) (pY a n)
    (fun _ hp => (Finset.mem_filter.1 hp).2.1.ne) hL).congr (indicator_RY_ae φ)).congr_right
    (indicator_RY_ae _)

include hφ hL in
lemma sum_phiY (k : Fin (n + 1)) : MemLp (phiY a φ) 2 (μN n) ∧ IsWD k (phiY a φ) (DphiY a φ k) :=
  isWD_sumY sgn (fun _ _ => hφ.1.indicator measurableSet_RY.nullMeasurableSet)
    (fun σ _ => isWD_RY_of_bound hφ hL (σ⁻¹ k))

include hφ hL in
/-- **`phiY φ` is a state of mixed symmetry.** -/
theorem phiY_mem : phiY a φ ∈ DomWS (ymix a) :=
  ⟨(sum_phiY hφ hL 0).1, fun k => ⟨_, (sum_phiY hφ hL k).2⟩,
    fun _ hρ => ae_of_all _ fun x => altY_pm _ hρ x⟩

include hφs in
lemma phiY_sgnY {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x) :
    phiY a φ x = sgnY a x * φ x := by
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
  rw [phiY, altY_eq_sumY, sumY_sort (F := fun _ => (RY a n).indicator φ)
    (fun _ y hy => indicator_of_notMem hy _) hx hinj hσ hσR, indicator_of_mem hσR, hφs σ hσ,
    (sorted_Y (Ψ := φ) hx hinj hσ hσR 0).2.2.2.2]

include hφ hφs in
lemma ae_dW_pm_symY : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG a σ →
    ∀ k : Fin (n + 1), dW (σ⁻¹ k) φ (pm σ x) = dW k φ x := by
  rw [ae_all_iff]; intro σ
  by_cases hσ : YG a σ
  · have H : ∀ k : Fin (n + 1), ∀ᵐ x ∂μN n, dW (σ⁻¹ k) φ (pm σ x) = dW k φ x := fun k => by
      have h1 := (dW_spec (hφ.2 (σ⁻¹ k))).comp_pm σ
      have he : (fun x => φ (pm σ x)) = φ := funext fun x => hφs σ hσ x
      rw [he] at h1
      exact IsWD.unique h1 (dW_spec (hφ.2 k))
    filter_upwards [ae_all_iff.2 H] with x hx _ k using hx k
  · exact ae_of_all _ fun _ h => absurd h hσ

include hφ hφs hL in
lemma dW_phiY_ae (k : Fin (n + 1)) : ∀ᵐ x ∂μN n, dW k (phiY a φ) x = sgnY a x * dW k φ x := by
  filter_upwards [dW_ae_eq (sum_phiY hφ hL k).2, ae_cube, ae_injective, ae_dW_pm_symY hφ hφs]
    with x hd hx hinj hsym
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
  rw [hd, DphiY, sumY_sort (F := fun ρ => (RY a n).indicator (dW (ρ⁻¹ k) φ))
    (fun _ y hy => indicator_of_notMem hy _) hx hinj hσ hσR, indicator_of_mem hσR, hsym σ hσ,
    (sorted_Y (Ψ := φ) hx hinj hσ hσR 0).2.2.2.2]

end test

/-! ### The weak equation for the companion, and the estimate -/

section equation

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}

lemma sgnY_mul_self {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x) :
    sgnY a x * sgnY a x = 1 := by
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
  rw [(sorted_Y (Ψ := fun _ => (0 : ℝ)) hx hinj hσ hσR 0).2.2.2.2, sgn_mul_self]

lemma PhiY_sgnY {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x) (k : Fin (n + 1)) :
    PhiY a Ψ x = sgnY a x * PhiBY a Ψ x ∧ DPhiY a Ψ k x = sgnY a x * DPhiBY a Ψ k x := by
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
  obtain ⟨h1, h2, h3, h4, h5⟩ := sorted_Y (Ψ := Ψ) hx hinj hσ hσR k
  rw [h1, h2, h3, h4, h5]
  exact ⟨rfl, rfl⟩

/-- **The companion satisfies the weak equation** against `YG a`-symmetric test functions
vanishing linearly on the same-group planes, with the energy of the chamber ground state. -/
theorem eq_PhiBY (hΨ : IsGS (settingWS (ymix a) w hw) v Ψ) {φ : Cfg n → ℝ} (hφ : H1W φ)
    (hφs : ∀ σ, YG a σ → ∀ x, φ (pm σ x) = φ x)
    (hL : ∀ p ∈ pY a n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1|) :
    h0W n w (PhiBY a Ψ) φ + ∫ x, LN n v x * (PhiBY a Ψ x * φ x) ∂μN n =
      Q (settingWS (ymix a) w hw) v (PhiY a Ψ) / ip (μ := μN n) (PhiY a Ψ) (PhiY a Ψ) *
        ∫ x, PhiBY a Ψ x * φ x ∂μN n := by
  have hel := euler_lagrange (isGS_PhiY hΨ) (phiY_mem hφ hL)
  change h0W n w (PhiY a Ψ) (phiY a φ) + ∫ x, LN n v x * (PhiY a Ψ x * phiY a φ x) ∂μN n =
    _ * ∫ x, PhiY a Ψ x * phiY a φ x ∂μN n at hel
  have hp : ∀ᵐ x ∂μN n, PhiY a Ψ x * phiY a φ x = PhiBY a Ψ x * φ x := by
    filter_upwards [ae_cube, ae_injective] with x hx hinj
    rw [(PhiY_sgnY (Ψ := Ψ) hx hinj 0).1, phiY_sgnY hφs hx hinj]
    linear_combination (PhiBY a Ψ x * φ x) * sgnY_mul_self hx hinj
  have hd : ∀ k, ∀ᵐ x ∂μN n, dW k (PhiY a Ψ) x * dW k (phiY a φ) x =
      dW k (PhiBY a Ψ) x * dW k φ x := fun k => by
    filter_upwards [ae_cube, ae_injective, dW_ae_eq (sum_PhiY hΨ.1 k).2,
      dW_ae_eq (sum_PhiBY hΨ.1 k).2, dW_phiY_ae hφ hφs hL k] with x hx hinj h1 h2 h3
    rw [h1, h2, h3, (PhiY_sgnY (Ψ := Ψ) hx hinj k).2]
    linear_combination (DPhiBY a Ψ k x * dW k φ x) * sgnY_mul_self hx hinj
  have e1 : ∫ x, PhiY a Ψ x * phiY a φ x ∂μN n = ∫ x, PhiBY a Ψ x * φ x ∂μN n :=
    integral_congr_ae hp
  have e2 : ∫ x, LN n v x * (PhiY a Ψ x * phiY a φ x) ∂μN n =
      ∫ x, LN n v x * (PhiBY a Ψ x * φ x) ∂μN n :=
    integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx])
  have e3 : h0W n w (PhiY a Ψ) (phiY a φ) = h0W n w (PhiBY a Ψ) φ := by
    simp only [h0W]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => integral_congr_ae (hd k)
    · exact integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx])
  rw [e1, e2, e3] at hel
  exact hel

/-- **The logarithmic estimate for ground states of mixed symmetry.** For a `C¹` cutoff `η`,
`YG a`-symmetric and vanishing on the walls and on the same-group diagonals, and `|E - V| ≤ C`
a.e., `Σ_k ∫ η² (∂ₖB/(B+ε))² ≤ 4 Σ_k ∫ (∂ₖη)² + 2C ∫ η²` for every `ε > 0`. -/
theorem log_estimate_Y (hΨ : IsGS (settingWS (ymix a) w hw) v Ψ)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η) (hηs : ∀ σ, YG a σ → ∀ x, η (pm σ x) = η x)
    (hηw : ∀ x k, (x k = 0 ∨ x k = 1) → η x = 0)
    (hηd : ∀ x i j, i ≠ j → SameB a i j → x i = x j → η x = 0) {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂μN n, |Q (settingWS (ymix a) w hw) v (PhiY a Ψ) /
      ip (μ := μN n) (PhiY a Ψ) (PhiY a Ψ) - (LN n v x + w x)| ≤ C) :
    ∑ k, ∫ x, (η x * (dW k (PhiBY a Ψ) x / (PhiBY a Ψ x + ε))) ^ 2 ∂μN n ≤
      4 * ∑ k, ∫ x, dk k η x ^ 2 ∂μN n + 2 * C * ∫ x, η x ^ 2 ∂μN n := by
  set u := PhiBY a Ψ
  have hu0 : ∀ x, 0 ≤ u x := PhiBY_nonneg Ψ
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  set φ := logTest η u ε
  have hφs : ∀ σ, YG a σ → ∀ x, φ (pm σ x) = φ x := fun σ hσ x => by
    simp only [φ, logTest, hηs σ hσ, u, PhiBY_pm Ψ hσ]
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
  have hL : ∀ p ∈ pY a n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1| := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    obtain ⟨Lp, hLp0, hLp⟩ := abs_le_of_plane' hη hp'.1.ne
      fun x hx => hηd x _ _ hp'.1.ne hp'.2 hx
    refine ⟨max Bη 0 / ε * Lp, mul_nonneg (div_nonneg (le_max_right _ _) hε.le) hLp0, ?_⟩
    filter_upwards [hφη, hLp] with x h1 h2
    calc |φ x| ≤ max Bη 0 / ε * |η x| := h1
      _ ≤ max Bη 0 / ε * (Lp * |x p.2 - x p.1|) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (le_max_right _ _) hε.le)
      _ = _ := by ring
  exact log_estimate_of_eq hw (h1W_PhiBY hΨ.1) (ae_of_all _ hu0) hη hηw hε hC0 hC
    (eq_PhiBY hΨ (h1W_logTest (h1W_PhiBY hΨ.1) hη hηw hε) hφs hL)

end equation

end DFT.Continuum.Line
