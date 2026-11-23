/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Nondeg
import DFT.Continuum.Line.LiebCont

/-!
# Hard-core bosons on `H¹₀` for continuous potentials

Girardeau's map `Ψ ↦ A Ψ`, `A = sign ∏_{i<j}(x_j - x_i)`, on states of finite kinetic energy.

* `gA_of_strictMono`, `gA_sort`: `A = 1` on the ordered chamber, `A(x) = sgn σ` for the sorting
  relabelling `σ` of `x`;
* **`isWD_mulA`**: for a fermionic `H¹₀` state `Ψ`, `A Ψ` has weak derivatives `A ∂ₖΨ` (it is a.e.
  the symmetrisation of `1_C Ψ`, `C` the ordered chamber); `mulA_memW`: `A Ψ` is a bosonic `H¹₀`
  state; `h0W_mulA`, `ip_mulA_W`, `pf_mulA_W`: the map preserves energies, norms and densities;
* `DomHCW`, `settingHCW`: hard-core bosons on `H¹₀`, the Girardeau image of the fermionic states,
  with the weak kinetic energy;
* `isGS_mulA_W_iff`, `gsE_hcW`, `liebF_hcW`: ground states, ground-state energies and the Lieb
  functional correspond to those of fermions;
* **`exists_unique_gs_hcW`**, **`gs_ne_zero_hcW`**, **`hk_hardcore_W`**, **`lieb_hardcore_W_of`**:
  existence and uniqueness, unique continuation, Hohenberg–Kohn and the Lieb functional for
  hard-core bosons, with continuous `v` and `w`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### Girardeau's sign at sorted configurations -/

lemma gA_of_strictMono {x : Cfg n} (hx : StrictMono x) : gA x = 1 := by
  have h : 0 < vdm x := by
    rw [vdm, Matrix.det_vandermonde]
    exact Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      sub_pos.2 (hx (Finset.mem_Ioi.1 hj))
  simp [gA, Real.sign_of_pos h]

/-- In the Young chamber with one group, every pair is ordered. -/
lemma strictMono_of_RY {x : Cfg n} (hx : x ∈ RY (n + 1) n) : StrictMono x := fun i j hij =>
  hx.2 i j hij ⟨fun _ => j.isLt, fun _ => i.isLt⟩

lemma YG_all (σ : Equiv.Perm (Fin (n + 1))) : YG (n + 1) σ := fun i =>
  ⟨fun _ => i.isLt, fun _ => (σ i).isLt⟩

lemma gA_sort {x : Cfg n} {σ : Equiv.Perm (Fin (n + 1))} (hσR : pm σ x ∈ RY (n + 1) n) :
    gA x = sgn σ := by
  have h := gA_pm σ x
  rw [gA_of_strictMono (strictMono_of_RY hσR)] at h
  linear_combination (-sgn σ) * h - gA x * sgn_mul_self σ

/-! ### The Girardeau map on `H¹₀` -/

section map

variable {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW .fer n)
include hΨ

lemma memY_of_fer : Ψ ∈ DomWS (ymix (n := n) (n + 1)) := by rw [← DomW_fer_eq]; exact hΨ

lemma ae_pm_fer : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), Ψ (pm σ x) = sgn σ * Ψ x :=
  ae_all_iff.2 fun σ => hΨ.2.2 σ trivial

lemma ae_dW_pm_fer : ∀ᵐ x ∂μN n, ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ k : Fin (n + 1),
    dW (σ⁻¹ k) Ψ (pm σ x) = sgn σ * dW k Ψ x := by
  rw [ae_all_iff]; intro σ
  rw [ae_all_iff]; intro k
  have h1 := (dW_spec (hΨ.2.1 (σ⁻¹ k))).comp_pm σ
  have h2 : IsWD k (fun x => sgn σ * Ψ x) (fun x => sgn σ * dW k Ψ x) :=
    (dW_spec (hΨ.2.1 k)).const_mul _
  exact IsWD.unique (h1.congr (hΨ.2.2 σ trivial)) h2

/-- `A Ψ` is a.e. the symmetrisation of `1_C Ψ`. -/
lemma mulA_ae_sumY : (mulA Ψ : Cfg n → ℝ) =ᵐ[μN n]
    sumY (n + 1) (fun _ => 1) fun _ => (RY (n + 1) n).indicator Ψ := by
  filter_upwards [ae_cube, ae_injective, ae_pm_fer hΨ] with x hx hinj hpm
  obtain ⟨σ, -, hσR⟩ := exists_YG_sort (a := n + 1) hx hinj
  rw [sumY_sort (fun _ y hy => indicator_of_notMem hy _) hx hinj (YG_all σ) hσR,
    indicator_of_mem hσR, one_mul, hpm σ, mulA_apply, gA_sort hσR]

/-- **The Girardeau map on `H¹₀`**: `∂ₖ(A Ψ) = A ∂ₖΨ`. -/
theorem isWD_mulA (k : Fin (n + 1)) : IsWD k (mulA Ψ) (fun x => gA x * dW k Ψ x) := by
  have hY := memY_of_fer hΨ
  have h := isWD_sumY (a := n + 1) (k := k) (fun _ => 1)
    (F := fun _ => (RY (n + 1) n).indicator Ψ)
    (G := fun σ => (RY (n + 1) n).indicator (dW (σ⁻¹ k) Ψ))
    (fun _ _ => hΨ.1.indicator measurableSet_RY.nullMeasurableSet)
    (fun σ _ => isWD_RY hY (σ⁻¹ k))
  refine (h.2.congr (mulA_ae_sumY hΨ).symm).congr_right ?_
  filter_upwards [ae_cube, ae_injective, ae_dW_pm_fer hΨ] with x hx hinj hd
  obtain ⟨σ, -, hσR⟩ := exists_YG_sort (a := n + 1) hx hinj
  rw [sumY_sort (F := fun σ => (RY (n + 1) n).indicator (dW (σ⁻¹ k) Ψ))
    (fun _ y hy => indicator_of_notMem hy _) hx hinj (YG_all σ) hσR, indicator_of_mem hσR,
    one_mul, hd σ k, gA_sort hσR]

lemma memLp_mulA : MemLp (mulA Ψ) 2 (μN n) :=
  (isWD_sumY (a := n + 1) (k := 0) (fun _ => 1) (F := fun _ => (RY (n + 1) n).indicator Ψ)
    (G := fun σ => (RY (n + 1) n).indicator (dW (σ⁻¹ 0) Ψ))
    (fun _ _ => hΨ.1.indicator measurableSet_RY.nullMeasurableSet)
    (fun σ _ => isWD_RY (memY_of_fer hΨ) (σ⁻¹ 0))).1.ae_eq (mulA_ae_sumY hΨ).symm

/-- **`A Ψ` is a bosonic `H¹₀` state.** -/
theorem mulA_memW : mulA Ψ ∈ DomW .bos n := by
  refine ⟨memLp_mulA hΨ, fun k => ⟨_, isWD_mulA hΨ k⟩, fun σ _ => ?_⟩
  filter_upwards [ae_pm_fer hΨ] with x hpm
  change gA (pm σ x) * Ψ (pm σ x) = ch .bos σ * (gA x * Ψ x)
  rw [gA_pm, hpm σ, ch_bos]
  linear_combination (gA x * Ψ x) * sgn_mul_self σ

lemma dW_mulA_ae (k : Fin (n + 1)) : dW k (mulA Ψ) =ᵐ[μN n] fun x => gA x * dW k Ψ x :=
  dW_ae_eq (isWD_mulA hΨ k)

end map

/-- `A² = 1` off collisions. -/
lemma gA_sq_ae : ∀ᵐ x ∂μN n, gA x * gA x = 1 := by
  filter_upwards [ae_injective] with x hx using gA_mul_self hx

lemma mulA_mulA_ae (Ψ : Cfg n → ℝ) : (mulA (mulA Ψ) : Cfg n → ℝ) =ᵐ[μN n] Ψ := by
  filter_upwards [gA_sq_ae] with x hx
  rw [mulA_apply, mulA_apply, ← mul_assoc, hx, one_mul]

lemma mulA_mul_mulA_ae (Ψ Φ : Cfg n → ℝ) :
    ∀ᵐ x ∂μN n, mulA Ψ x * mulA Φ x = Ψ x * Φ x := by
  filter_upwards [gA_sq_ae] with x hx
  rw [mulA_apply, mulA_apply]
  linear_combination (Ψ x * Φ x) * hx

/-! ### The hard-core setting on `H¹₀` -/

/-- **Hard-core bosonic `H¹₀` states**: Girardeau images of fermionic `H¹₀` states. -/
noncomputable def DomHCW (n : ℕ) : Submodule ℝ (Cfg n → ℝ) := (DomW .fer n).map mulA

lemma DomHCW_le : DomHCW n ≤ DomW .bos n := by
  rintro _ ⟨Ψ, hΨ, rfl⟩
  exact mulA_memW hΨ

section setting

variable {w : Cfg n → ℝ} {hw : Continuous w}

variable (n w hw) in
/-- **Hard-core bosons on `H¹₀`**, with the weak kinetic energy plus interaction `w`. -/
noncomputable def settingHCW : Setting (μN n) Pot where
  D := DomHCW n
  h0 := h0W n w
  h0_add a ha b hb c hc :=
    (settingW .bos n w hw).h0_add a (DomHCW_le ha) b (DomHCW_le hb) c (DomHCW_le hc)
  h0_smul r a ha c hc := (settingW .bos n w hw).h0_smul r a (DomHCW_le ha) c (DomHCW_le hc)
  h0_symm a ha c hc := (settingW .bos n w hw).h0_symm a (DomHCW_le ha) c (DomHCW_le hc)
  L := LN n
  int_L v a b ha hb := (settingW .bos n w hw).int_L v a b (DomHCW_le ha) (DomHCW_le hb)
  int_sq a b ha hb := (settingW .bos n w hw).int_sq a b (DomHCW_le ha) (DomHCW_le hb)

variable {Ψ Φ : Cfg n → ℝ}

lemma ip_mulA_W : ip (μ := μN n) (mulA Ψ) (mulA Φ) = ip (μ := μN n) Ψ Φ :=
  integral_congr_ae (mulA_mul_mulA_ae Ψ Φ)

lemma pf_mulA_W (v : Pot) :
    pf (settingHCW n w hw) v (mulA Ψ) (mulA Φ) = pf (settingW .fer n w hw) v Ψ Φ :=
  integral_congr_ae (by filter_upwards [mulA_mul_mulA_ae Ψ Φ] with x hx; rw [hx]; rfl)

lemma dens_mulA_W :
    dens (settingHCW n w hw) (mulA Ψ) = dens (settingW .fer n w hw) Ψ :=
  funext fun v => pf_mulA_W v

lemma h0W_mulA (hΨ : Ψ ∈ DomW .fer n) (hΦ : Φ ∈ DomW .fer n) :
    h0W n w (mulA Ψ) (mulA Φ) = h0W n w Ψ Φ := by
  simp only [h0W]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
    filter_upwards [dW_mulA_ae hΨ k, dW_mulA_ae hΦ k, gA_sq_ae] with x h1 h2 h3
    rw [h1, h2]
    linear_combination (dW k Ψ x * dW k Φ x) * h3
  · exact integral_congr_ae (by filter_upwards [mulA_mul_mulA_ae Ψ Φ] with x hx; rw [hx])

lemma Q_mulA_W (hΨ : Ψ ∈ DomW .fer n) (v : Pot) :
    Q (settingHCW n w hw) v (mulA Ψ) = Q (settingW .fer n w hw) v Ψ := by
  change h0W n w (mulA Ψ) (mulA Ψ) + pf (settingHCW n w hw) v (mulA Ψ) (mulA Ψ) =
    h0W n w Ψ Ψ + pf (settingW .fer n w hw) v Ψ Ψ
  rw [h0W_mulA hΨ hΨ, pf_mulA_W]

/-- **Ground states correspond** under the Girardeau map. -/
theorem isGS_mulA_W_iff (hΨ : Ψ ∈ DomW .fer n) (v : Pot) :
    IsGS (settingHCW n w hw) v (mulA Ψ) ↔ IsGS (settingW .fer n w hw) v Ψ := by
  constructor
  · rintro ⟨-, hpos, hmin⟩
    rw [ip_mulA_W] at hpos
    refine ⟨hΨ, hpos, fun χ hχ => ?_⟩
    have := hmin (mulA χ) ⟨χ, hχ, rfl⟩
    rwa [Q_mulA_W hΨ, Q_mulA_W hχ, ip_mulA_W, ip_mulA_W] at this
  · rintro ⟨-, hpos, hmin⟩
    refine ⟨⟨Ψ, hΨ, rfl⟩, by rwa [ip_mulA_W], fun χ hχ => ?_⟩
    obtain ⟨χ, hχ, rfl⟩ := hχ
    rw [Q_mulA_W hΨ, Q_mulA_W hχ, ip_mulA_W, ip_mulA_W]
    exact hmin χ hχ

/-- The ground-state energies of hard-core bosons and fermions agree. -/
theorem gsE_hcW (v : Pot) : gsE (settingHCW n w hw) v = gsE (settingW .fer n w hw) v := by
  refine le_antisymm (le_iInf₂ fun ψ hψ => ?_) (le_iInf₂ fun Φ hΦ => ?_)
  · rw [← Q_mulA_W hψ.1]
    exact iInf₂_le _ ⟨⟨ψ, hψ.1, rfl⟩, by rw [ip_mulA_W]; exact hψ.2⟩
  · obtain ⟨χ, hχ, rfl⟩ := hΦ.1
    rw [Q_mulA_W hχ]
    exact iInf₂_le _ ⟨hχ, by rw [← ip_mulA_W]; exact hΦ.2⟩

/-- **The Lieb functionals of hard-core bosons and of fermions coincide** on `H¹₀`. -/
theorem liebF_hcW (ρ : Pot → ℝ) :
    liebF (settingHCW n w hw) ρ = liebF (settingW .fer n w hw) ρ := by
  simp only [liebF, gsE_hcW]

end setting

/-! ### The theorems -/

section theorems

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

/-- **Hard-core ground states are nonzero almost everywhere.** -/
theorem gs_ne_zero_hcW {Φ : Cfg n → ℝ} (hΦ : IsGS (settingHCW n w hw) v Φ) :
    ∀ᵐ x ∂μN n, Φ x ≠ 0 := by
  obtain ⟨χ, hχ, rfl⟩ := hΦ.1
  filter_upwards [gs_ne_zero_W_fer ((isGS_mulA_W_iff hχ v).1 hΦ), ae_injective] with x h1 h2
  rw [mulA_apply]
  exact mul_ne_zero (fun h => by have := gA_mul_self h2; rw [h, zero_mul] at this; simp at this) h1

/-- **Existence and uniqueness of the hard-core ground state on `H¹₀`**, continuous `v` and `w`. -/
theorem exists_unique_gs_hcW (hw : Continuous w) (v : Pot) :
    ∃ Φ, IsGS (settingHCW n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (settingHCW n w hw) v Ψ → ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ := by
  obtain ⟨χ, hχ, h1, huniq⟩ := exists_unique_gs_W_cont (τ := .fer) hw v
  refine ⟨mulA χ, (isGS_mulA_W_iff hχ.1 v).2 hχ, by rw [ip_mulA_W]; exact h1, fun Ψ hΨ => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := hΨ.1
  obtain ⟨c, hc⟩ := huniq ψ ((isGS_mulA_W_iff hψ v).1 hΨ)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  simp only [mulA_apply, hx, Pi.smul_apply, smul_eq_mul]; ring

/-- **Hohenberg–Kohn for hard-core bosons on `H¹₀`**, continuous `v` and `w`. -/
theorem hk_hardcore_W {v' : Pot} {Φ Φ' : Cfg n → ℝ} (hΦ : IsGS (settingHCW n w hw) v Φ)
    (hΦ' : IsGS (settingHCW n w hw) v' Φ') (hn : ip (μ := μN n) Φ Φ = ip (μ := μN n) Φ' Φ')
    (hd : dens (settingHCW n w hw) Φ = dens (settingHCW n w hw) Φ') :
    ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨χ, hχ, rfl⟩ := hΦ.1
  obtain ⟨χ', hχ', rfl⟩ := hΦ'.1
  rw [ip_mulA_W, ip_mulA_W] at hn
  rw [dens_mulA_W, dens_mulA_W] at hd
  exact (hk_line_W_cont_stat (τ := .fer) v v').2 χ χ' ((isGS_mulA_W_iff hχ v).1 hΦ)
    ((isGS_mulA_W_iff hχ' v').1 hΦ') hn hd

/-- **The Lieb functional for hard-core bosons on `H¹₀`**: at the density of a normalised ground
state it equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and it is the only one up to constants. -/
theorem lieb_hardcore_W_of {ψ : Cfg n → ℝ} (hψ : IsNGS (settingHCW n w hw) v ψ) :
    liebF (settingHCW n w hw) (dens (settingHCW n w hw) ψ) =
        (((settingHCW n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingHCW n w hw).h0 ψ ψ + dens (settingHCW n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (settingHCW n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((settingHCW n w hw).h0 ψ ψ + dens (settingHCW n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingHCW n w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  refine ⟨liebF_of_isNGS hψ, subgrad_of_isNGS hψ, fun v' hsub => ?_⟩
  obtain ⟨χ, hχ, rfl⟩ := hψ.1.1
  have hF : IsNGS (settingW .fer n w hw) v χ := by
    refine ⟨⟨hχ, by rw [← ip_mulA_W]; exact hψ.1.2⟩, fun φ hφ => ?_⟩
    have := hψ.2 (mulA φ) ⟨⟨φ, hφ.1, rfl⟩, by rw [ip_mulA_W]; exact hφ.2⟩
    rwa [Q_mulA_W hχ, Q_mulA_W hφ.1] at this
  refine (lieb_line_W_cont_of hF).2.2 v' fun ρ => ?_
  have := hsub ρ
  rwa [liebF_hcW, show (settingHCW n w hw).h0 (mulA χ) (mulA χ) = h0W n w χ χ from
    h0W_mulA hχ hχ, dens_mulA_W] at this

end theorems

end DFT.Continuum.Line
