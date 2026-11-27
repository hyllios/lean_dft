/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.NeuEL
import DFT.Continuum.Line.Neumann.NeuHalf

/-!
# The fermionic chamber state with Neumann walls

The chamber construction of `Line/YoungGS` for fermions (`a = N`, the whole symmetric group) with
Neumann walls. For a fermionic Neumann state `Ψ` let `u = 1_R |Ψ|`, `Φ = Σ_σ sgn σ · u ∘ σ`
(`PhiY`) and `B = Σ_σ u ∘ σ` (`PhiBY`, `= |Ψ|` a.e.). The pointwise definitions are those of
`Line/YoungGS`; the derivatives are now Neumann weak derivatives (`DuYN`, `DPhiYN`, `DPhiBYN`).

* `isWDN_sumY`, `sorted_YN`;
* `PhiY_memN`, `abs_DPhiYN_le`, `kinN_PhiY_le`, **`isGSNH_PhiY`**: `Φ` is again a ground state;
* `phiY_memN`, `dWN_phiY_ae`: test functions of fermionic symmetry from symmetric `φ` vanishing
  linearly on the diagonals;
* **`eq_PhiBY_H`**: `B` satisfies the weak equation against such `φ`, with potential term `v(e)`
  for an `e ∈ H1E` having the integrals of `B φ`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

/-- Weak derivatives of Young sums, Neumann walls. -/
lemma isWDN_sumY {a : ℕ} (c : Equiv.Perm (Fin (n + 1)) → ℝ)
    {F G : Equiv.Perm (Fin (n + 1)) → Cfg n → ℝ} {k : Fin (n + 1)}
    (hF : ∀ σ, YG a σ → MemLp (F σ) 2 (μN n))
    (hG : ∀ σ, YG a σ → IsWDN (σ⁻¹ k) (F σ) (G σ)) :
    MemLp (sumY a c F) 2 (μN n) ∧ IsWDN k (sumY a c F) (sumY a c G) := by
  classical
  exact IsWDN.sum (k := k) Finset.univ
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
      · simp only [hσ, ↓reduceIte]; exact IsWDN.zero k)

/-! ### Neumann derivatives of the chamber states -/

/-- The Neumann weak derivatives of `u = 1_R |Ψ|`. -/
noncomputable def DuYN (Ψ : Cfg n → ℝ) (l : Fin (n + 1)) (x : Cfg n) : ℝ :=
  rsgn ((RY (n + 1) n).indicator Ψ x) * dWN l ((RY (n + 1) n).indicator Ψ) x

noncomputable def DPhiYN (Ψ : Cfg n → ℝ) (k : Fin (n + 1)) : Cfg n → ℝ :=
  sumY (n + 1) sgn fun σ => DuYN Ψ (σ⁻¹ k)

noncomputable def DPhiBYN (Ψ : Cfg n → ℝ) (k : Fin (n + 1)) : Cfg n → ℝ :=
  sumY (n + 1) (fun _ => 1) fun σ => DuYN Ψ (σ⁻¹ k)

lemma DuYN_of_notMem {Ψ : Cfg n → ℝ} {y : Cfg n} (hy : y ∉ RY (n + 1) n) (l : Fin (n + 1)) :
    DuYN Ψ l y = 0 := by
  simp [DuYN, indicator_of_notMem hy, rsgn]

lemma sorted_YN {Ψ : Cfg n → ℝ} {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x)
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : YG (n + 1) σ) (hσR : pm σ x ∈ RY (n + 1) n)
    (k : Fin (n + 1)) :
    DPhiYN Ψ k x = sgn σ * DuYN Ψ (σ⁻¹ k) (pm σ x) ∧
      DPhiBYN Ψ k x = DuYN Ψ (σ⁻¹ k) (pm σ x) := by
  have hd : ∀ (ρ : Equiv.Perm (Fin (n + 1))) y, y ∉ RY (n + 1) n → DuYN Ψ (ρ⁻¹ k) y = 0 :=
    fun _ _ hy => DuYN_of_notMem hy _
  exact ⟨sumY_sort hd hx hinj hσ hσR, by rw [DPhiBYN, sumY_sort hd hx hinj hσ hσR, one_mul]⟩

section state

variable {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomN .fer n)
include hΨ

lemma h1NW_RY : H1NW ((RY (n + 1) n).indicator Ψ) :=
  ⟨hΨ.1.indicator measurableSet_RY.nullMeasurableSet, fun k => ⟨_, isWDN_RY hΨ k⟩⟩

lemma memLp_uYN : MemLp (uY (n + 1) Ψ) 2 (μN n) := (h1NW_RY hΨ).1.abs

lemma isWDN_uY (l : Fin (n + 1)) : IsWDN l (uY (n + 1) Ψ) (DuYN Ψ l) :=
  isWDN_abs (mem_symT1 (h1NW_RY hΨ)) l

lemma sum_PhiYN (k : Fin (n + 1)) :
    MemLp (PhiY (n + 1) Ψ) 2 (μN n) ∧ IsWDN k (PhiY (n + 1) Ψ) (DPhiYN Ψ k) :=
  isWDN_sumY sgn (fun _ _ => memLp_uYN hΨ) (fun σ _ => isWDN_uY hΨ (σ⁻¹ k))

lemma sum_PhiBYN (k : Fin (n + 1)) :
    MemLp (PhiBY (n + 1) Ψ) 2 (μN n) ∧ IsWDN k (PhiBY (n + 1) Ψ) (DPhiBYN Ψ k) :=
  isWDN_sumY _ (fun _ _ => memLp_uYN hΨ) (fun σ _ => isWDN_uY hΨ (σ⁻¹ k))

/-- **`Φ` is a fermionic Neumann state.** -/
theorem PhiY_memN : PhiY (n + 1) Ψ ∈ DomN .fer n :=
  ⟨(sum_PhiYN hΨ 0).1, fun k => ⟨_, (sum_PhiYN hΨ k).2⟩,
    fun σ _ => ae_of_all _ fun x => altY_pm _ (YG_all σ) x⟩

/-- **`B` is a bosonic Neumann state.** -/
theorem PhiBY_memN : PhiBY (n + 1) Ψ ∈ DomN .bos n :=
  ⟨(sum_PhiBYN hΨ 0).1, fun k => ⟨_, (sum_PhiBYN hΨ k).2⟩,
    fun σ _ => ae_of_all _ fun x => by
      change _ = 1 * _
      rw [one_mul]; exact sumY_one_pm _ (YG_all σ) x⟩

lemma ae_abs_pmYN : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG (n + 1) σ →
    |Ψ (pm σ x)| = |Ψ x| := by
  rw [ae_all_iff]
  intro σ
  filter_upwards [hΨ.2.2 σ trivial] with x hx _
  change Ψ (pm σ x) = sgn σ * Ψ x at hx
  rw [hx, abs_mul, abs_sgn, one_mul]

lemma ae_abs_dWN_pmY : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG (n + 1) σ →
    ∀ k : Fin (n + 1), |dWN (σ⁻¹ k) Ψ (pm σ x)| = |dWN k Ψ x| := by
  rw [ae_all_iff]; intro σ
  have H : ∀ k : Fin (n + 1), ∀ᵐ x ∂μN n, |dWN (σ⁻¹ k) Ψ (pm σ x)| = |dWN k Ψ x| := fun k => by
    have h1 := (dWN_spec (hΨ.2.1 (σ⁻¹ k))).comp_pm σ
    have h2 : IsWDN k (fun x => sgn σ * Ψ x) (fun x => sgn σ * dWN k Ψ x) :=
      (dWN_spec (hΨ.2.1 k)).const_mul _
    have h3 := h1.congr_ae (hΨ.2.2 σ trivial)
    filter_upwards [IsWDN.unique h3 h2] with x hx
    rw [hx, abs_mul, abs_sgn, one_mul]
  filter_upwards [ae_all_iff.2 H] with x hx _ k using hx k

lemma ae_abs_DuYN_pm : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ l : Fin (n + 1),
    |DuYN Ψ l (pm σ x)| ≤ |dWN l Ψ (pm σ x)| := by
  rw [ae_all_iff]; intro σ
  rw [ae_all_iff]; intro l
  have hd := dWN_ae_eq (isWDN_RY hΨ l)
  filter_upwards [ae_pm hd σ] with x hx
  simp only [DuYN]
  rw [hx, abs_mul]
  have hs : |rsgn ((RY (n + 1) n).indicator Ψ (pm σ x))| ≤ 1 := abs_rsgn_le _
  have hi : |(RY (n + 1) n).indicator (dWN l Ψ) (pm σ x)| ≤ |dWN l Ψ (pm σ x)| := by
    by_cases h : pm σ x ∈ RY (n + 1) n
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, abs_zero]; exact abs_nonneg _
  calc |rsgn ((RY (n + 1) n).indicator Ψ (pm σ x))| *
        |(RY (n + 1) n).indicator (dWN l Ψ) (pm σ x)|
      ≤ 1 * |dWN l Ψ (pm σ x)| := mul_le_mul hs hi (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **`|Φ| = |Ψ|` a.e.** -/
theorem abs_PhiYN : ∀ᵐ x ∂μN n, |PhiY (n + 1) Ψ x| = |Ψ x| := by
  filter_upwards [ae_cube, ae_injective, ae_abs_pmYN hΨ] with x hx hinj habs
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := n + 1) hx hinj
  rw [(sorted_Y hx hinj hσ hσR 0).1, abs_mul, abs_sgn, one_mul]
  simp only [uY, indicator_of_mem hσR, abs_abs]
  exact habs σ hσ

/-- **`B = |Ψ|` a.e.** -/
theorem PhiBY_ae_eq_absN : ∀ᵐ x ∂μN n, PhiBY (n + 1) Ψ x = |Ψ x| := by
  filter_upwards [ae_cube, ae_injective, ae_abs_pmYN hΨ] with x hx hinj habs
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := n + 1) hx hinj
  rw [(sorted_Y hx hinj hσ hσR 0).2.2.1]
  simp only [uY, indicator_of_mem hσR]
  exact habs σ hσ

/-- **`|∂ₖΦ| ≤ |∂ₖΨ|` a.e.** -/
theorem abs_DPhiYN_le (k : Fin (n + 1)) : ∀ᵐ x ∂μN n, |DPhiYN Ψ k x| ≤ |dWN k Ψ x| := by
  filter_upwards [ae_cube, ae_injective, ae_abs_dWN_pmY hΨ, ae_abs_DuYN_pm hΨ]
    with x hx hinj hdW hDu
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := n + 1) hx hinj
  rw [(sorted_YN hx hinj hσ hσR k).1, abs_mul, abs_sgn, one_mul]
  exact (hDu σ (σ⁻¹ k)).trans (hdW σ hσ k).le

/-- **`T(Φ) ≤ T(Ψ)`.** -/
theorem kinN_PhiY_le : kinN (PhiY (n + 1) Ψ) ≤ kinN Ψ := by
  refine Finset.sum_le_sum fun k _ => ?_
  have hd := dWN_ae_eq (sum_PhiYN hΨ k).2
  have hm := memLp_dWN (h1NW_of_mem hΨ) k
  rw [integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx])]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_self_nonneg _) (int_mul_L2 hm hm) ?_
  filter_upwards [abs_DPhiYN_le hΨ k] with x hx
  rw [← abs_mul_abs_self (DPhiYN Ψ k x), ← abs_mul_abs_self (dWN k Ψ x)]
  exact mul_le_mul hx hx (abs_nonneg _) (abs_nonneg _)

end state

/-- **The chamber state of a fermionic Neumann ground state is a ground state.** -/
theorem isGSNH_PhiY {w : Cfg n → ℝ} {v : PotH} {Ψ : Cfg n → ℝ} (hΨ : IsGSNH .fer w v Ψ) :
    IsGSNH .fer w v (PhiY (n + 1) Ψ) := by
  have hD := PhiY_memN hΨ.1
  have hsq : ∀ᵐ x ∂μN n, PhiY (n + 1) Ψ x * PhiY (n + 1) Ψ x = Ψ x * Ψ x := by
    filter_upwards [abs_PhiYN hΨ.1] with x hx
    rw [← abs_mul_abs_self, hx, abs_mul_abs_self]
  have hn : ∫ x, PhiY (n + 1) Ψ x ^ 2 ∂μN n = 1 := by
    rw [← hΨ.2.1]; exact integral_congr_ae (by filter_upwards [hsq] with x hx; rw [sq, sq, hx])
  have hρ : rhoE .fer (PhiY (n + 1) Ψ) = rhoE .fer Ψ := eq_of_int fun u => by
    rw [int_rhoE hD, int_rhoE hΨ.1]
    exact integral_congr_ae (by filter_upwards [hsq] with x hx; rw [hx])
  have hQ : QNH .fer w v (PhiY (n + 1) Ψ) ≤ QNH .fer w v Ψ := by
    simp only [QNH, hρ]
    have e : ∫ x, w x * (PhiY (n + 1) Ψ x * PhiY (n + 1) Ψ x) ∂μN n =
        ∫ x, w x * (Ψ x * Ψ x) ∂μN n :=
      integral_congr_ae (by filter_upwards [hsq] with x hx; rw [hx])
    rw [e]; linarith [kinN_PhiY_le hΨ.1]
  exact ⟨hD, hn, fun Φ hΦ hΦn => hQ.trans (hΨ.2.2 Φ hΦ hΦn)⟩

/-! ### Test functions of fermionic symmetry -/

noncomputable def DphiYN (φ : Cfg n → ℝ) (k : Fin (n + 1)) : Cfg n → ℝ :=
  sumY (n + 1) sgn fun σ => (RY (n + 1) n).indicator (dWN (σ⁻¹ k) φ)

section test

variable {φ : Cfg n → ℝ} (hφ : H1NW φ) (hφs : ∀ σ x, φ (pm σ x) = φ x)
  (hL : ∀ p ∈ pY (n + 1) n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1|)

include hφ hL in
lemma isWDN_RY_of_bound (k : Fin (n + 1)) :
    IsWDN k ((RY (n + 1) n).indicator φ) ((RY (n + 1) n).indicator (dWN k φ)) :=
  ((isWDN_pairs_of_bound hφ.1 (dWN_spec (hφ.2 k)) (pY (n + 1) n)
    (fun _ hp => (Finset.mem_filter.1 hp).2.1.ne) hL).congr_ae (indicator_RY_ae φ)).congr_right
    (indicator_RY_ae _)

include hφ hL in
lemma sum_phiYN (k : Fin (n + 1)) :
    MemLp (phiY (n + 1) φ) 2 (μN n) ∧ IsWDN k (phiY (n + 1) φ) (DphiYN φ k) :=
  isWDN_sumY sgn (fun _ _ => hφ.1.indicator measurableSet_RY.nullMeasurableSet)
    (fun σ _ => isWDN_RY_of_bound hφ hL (σ⁻¹ k))

include hφ hL in
/-- **`phiY φ` is a fermionic Neumann state.** -/
theorem phiY_memN : phiY (n + 1) φ ∈ DomN .fer n :=
  ⟨(sum_phiYN hφ hL 0).1, fun k => ⟨_, (sum_phiYN hφ hL k).2⟩,
    fun σ _ => ae_of_all _ fun x => altY_pm _ (YG_all σ) x⟩

include hφ hφs in
lemma ae_dWN_pm_symY : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), YG (n + 1) σ →
    ∀ k : Fin (n + 1), dWN (σ⁻¹ k) φ (pm σ x) = dWN k φ x := by
  rw [ae_all_iff]; intro σ
  have H : ∀ k : Fin (n + 1), ∀ᵐ x ∂μN n, dWN (σ⁻¹ k) φ (pm σ x) = dWN k φ x := fun k => by
    have h1 := (dWN_spec (hφ.2 (σ⁻¹ k))).comp_pm σ
    have he : (fun x => φ (pm σ x)) = φ := funext fun x => hφs σ x
    rw [he] at h1
    exact IsWDN.unique h1 (dWN_spec (hφ.2 k))
  filter_upwards [ae_all_iff.2 H] with x hx _ k using hx k

include hφ hφs hL in
lemma dWN_phiY_ae (k : Fin (n + 1)) :
    ∀ᵐ x ∂μN n, dWN k (phiY (n + 1) φ) x = sgnY (n + 1) x * dWN k φ x := by
  filter_upwards [dWN_ae_eq (sum_phiYN hφ hL k).2, ae_cube, ae_injective, ae_dWN_pm_symY hφ hφs]
    with x hd hx hinj hsym
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := n + 1) hx hinj
  rw [hd, DphiYN, sumY_sort (F := fun ρ => (RY (n + 1) n).indicator (dWN (ρ⁻¹ k) φ))
    (fun _ y hy => indicator_of_notMem hy _) hx hinj hσ hσR, indicator_of_mem hσR, hsym σ hσ,
    (sorted_Y (Ψ := φ) hx hinj hσ hσR 0).2.2.2.2]

end test

lemma PhiY_sgnYN {Ψ : Cfg n → ℝ} {x : Cfg n} (hx : x ∈ Cube n) (hinj : Function.Injective x)
    (k : Fin (n + 1)) :
    PhiY (n + 1) Ψ x = sgnY (n + 1) x * PhiBY (n + 1) Ψ x ∧
      DPhiYN Ψ k x = sgnY (n + 1) x * DPhiBYN Ψ k x := by
  obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := n + 1) hx hinj
  obtain ⟨h1, -, h3, -, h5⟩ := sorted_Y (Ψ := Ψ) hx hinj hσ hσR k
  obtain ⟨h2, h4⟩ := sorted_YN (Ψ := Ψ) hx hinj hσ hσR k
  rw [h1, h2, h3, h4, h5]
  exact ⟨rfl, rfl⟩

/-- **The companion satisfies the weak equation** against symmetric test functions vanishing
linearly on the diagonals, with the energy of the chamber ground state and a potential term
`v(e)`, `e ∈ H1E` having the integrals of `B φ`. -/
theorem eq_PhiBY_H {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH .fer w v Ψ) {φ : Cfg n → ℝ} (hφ : H1NW φ) (hφs : ∀ σ x, φ (pm σ x) = φ x)
    (hL : ∀ p ∈ pY (n + 1) n, ∃ L, 0 ≤ L ∧ ∀ᵐ x ∂μN n, |φ x| ≤ L * |x p.2 - x p.1|) :
    ∃ e : H1E, (∀ u' : C01, ∫ t, iccExt u' t * iccExt (evE e) t ∂vol01 =
        ∫ x, (∑ k, iccExt u' (x k)) * (PhiBY (n + 1) Ψ x * φ x) ∂μN n) ∧
      kinN2 (PhiBY (n + 1) Ψ) φ + ∫ x, w x * (PhiBY (n + 1) Ψ x * φ x) ∂μN n + v e =
        QNH .fer w v (PhiY (n + 1) Ψ) * ∫ x, PhiBY (n + 1) Ψ x * φ x ∂μN n := by
  have hG := isGSNH_PhiY hΨ
  have hφD : phiY (n + 1) φ ∈ DomN .fer n := phiY_memN hφ hL
  have hel := euler_lagrangeNH hw hG hφD
  have hp : ∀ᵐ x ∂μN n, PhiY (n + 1) Ψ x * phiY (n + 1) φ x = PhiBY (n + 1) Ψ x * φ x := by
    filter_upwards [ae_cube, ae_injective] with x hx hinj
    rw [(PhiY_sgnYN (Ψ := Ψ) hx hinj 0).1, phiY_sgnY (fun σ _ x => hφs σ x) hx hinj]
    linear_combination (PhiBY (n + 1) Ψ x * φ x) * sgnY_mul_self hx hinj
  have hd : ∀ k, ∀ᵐ x ∂μN n, dWN k (PhiY (n + 1) Ψ) x * dWN k (phiY (n + 1) φ) x =
      dWN k (PhiBY (n + 1) Ψ) x * dWN k φ x := fun k => by
    filter_upwards [ae_cube, ae_injective, dWN_ae_eq (sum_PhiYN hΨ.1 k).2,
      dWN_ae_eq (sum_PhiBYN hΨ.1 k).2, dWN_phiY_ae hφ hφs hL k] with x hx hinj h1 h2 h3
    rw [h1, h2, h3, (PhiY_sgnYN (Ψ := Ψ) hx hinj k).2]
    linear_combination (DPhiBYN Ψ k x * dWN k φ x) * sgnY_mul_self hx hinj
  have e1 : ∫ x, PhiY (n + 1) Ψ x * phiY (n + 1) φ x ∂μN n =
      ∫ x, PhiBY (n + 1) Ψ x * φ x ∂μN n := integral_congr_ae hp
  have e2 : ∫ x, w x * (PhiY (n + 1) Ψ x * phiY (n + 1) φ x) ∂μN n =
      ∫ x, w x * (PhiBY (n + 1) Ψ x * φ x) ∂μN n :=
    integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx])
  have e3 : kinN2 (PhiY (n + 1) Ψ) (phiY (n + 1) φ) = kinN2 (PhiBY (n + 1) Ψ) φ :=
    Finset.sum_congr rfl fun k _ => integral_congr_ae (hd k)
  refine ⟨rhoE2 .fer (PhiY (n + 1) Ψ) (phiY (n + 1) φ), fun u' => ?_, ?_⟩
  · rw [int_rhoE2 hG.1 hφD, pfN]
    exact integral_congr_ae (by filter_upwards [hp] with x hx; rw [hx])
  · rw [e1, e2, e3] at hel; exact hel

end DFT.Continuum.Line
