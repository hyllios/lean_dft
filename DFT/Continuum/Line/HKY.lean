/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.UcpY
import DFT.Continuum.Line.LiebCont

/-!
# Hohenberg–Kohn and the Lieb functional in a spin sector

For the Young symmetry `ymix a` (the spatial part of `N` spin-½ fermions with `a` spins up, i.e.
the sector `S_z = a - N/2`), with continuous `v` and continuous `w`:

* `DomY_le_DomWS`: `C²` states of mixed symmetry are `H¹₀` states;
* `ae_eq_zero_of_integral_altY_L1`: an integrable function of mixed antisymmetry orthogonal to all
  `H¹₀` states of that symmetry vanishes a.e.; `sep_lineWY`, `rigidL_lineWY`;
* **`hk_line_WY`**: Hohenberg–Kohn in the sector;
* **`lieb_line_WY_of`**, **`lieb_line_WY`**: the Lieb functional of the sector at the density of a
  normalised ground state: value, subgradient, uniqueness of the subgradient up to constants.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {a : ℕ}

/-- `C²` states of mixed symmetry are `H¹₀` states. -/
lemma DomY_le_DomWS : DomY a n ≤ DomWS (ymix (n := n) a) := fun _ hΦ =>
  ⟨memLp_cont hΦ.1.continuous, fun k => ⟨_, isWD_of_C1 (hΦ.1.of_le (by norm_num)) hΦ.2.2 k⟩,
    fun σ hσ => ae_of_all _ fun x => hΦ.2.1 σ hσ x⟩

/-- **Fundamental lemma for mixed antisymmetry.** -/
lemma ae_eq_zero_of_integral_altY_L1 {g : Cfg n → ℝ} (hg : Integrable g (μN n))
    (hgs : ∀ σ, YG a σ → ∀ᵐ x ∂μN n, g (pm σ x) = sgn σ * g x)
    (h : ∀ φ ∈ DomWS (ymix (n := n) a), ∫ x, g x * φ x ∂μN n = 0) : g =ᵐ[μN n] 0 := by
  classical
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Cube n) (μ := volume)
    (f := g) isOpen_cube
    ((show IntegrableOn g (Cube n) volume from hg).locallyIntegrableOn)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Cube n) => ?_)
  · exact (ae_restrict_iff' measurableSet_cube).2 hae
  have hout : ∀ x, x ∉ Cube n → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hsub h')
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 := h (altY a φ) (DomY_le_DomWS (altY_mem hφ2 hout))
  have hint : ∀ σ : Equiv.Perm (Fin (n + 1)),
      Integrable (fun x => g x * (if YG a σ then sgn σ * φ (pm σ x) else 0)) (μN n) := fun σ => by
    by_cases hσ : YG a σ
    · simp only [hσ, ↓reduceIte]
      obtain ⟨C, hC⟩ := ae_bound_cont (n := n)
        (continuous_const.mul (hφ.continuous.comp (continuous_pm σ)))
      exact hg.mul_bdd
        (continuous_const.mul (hφ.continuous.comp (continuous_pm σ))).aestronglyMeasurable hC
    · simp only [hσ, ↓reduceIte, mul_zero]; exact integrable_zero _ _ _
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∫ x, g x * (if YG a σ then sgn σ * φ (pm σ x) else 0) ∂μN n =
        if YG a σ then ∫ x, g x * φ x ∂μN n else 0 := by
    intro σ
    by_cases hσ : YG a σ
    · simp only [hσ, ↓reduceIte]
      have := integral_pm σ (fun y => g (pm σ⁻¹ y) * (sgn σ * φ y))
      simp only [pm_inv_pm] at this
      rw [this]
      refine integral_congr_ae ?_
      filter_upwards [hgs σ⁻¹ (YG_inv hσ)] with y hy
      rw [hy]
      have hi : sgn σ⁻¹ = sgn σ := ch_inv .fer σ
      rw [hi]
      linear_combination (g y * φ y) * sgn_mul_self σ
    · simp only [hσ, ↓reduceIte, mul_zero, integral_zero]
  have hsum : ∫ x, g x * altY a φ x ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        ∫ x, g x * (if YG a σ then sgn σ * φ (pm σ x) else 0) ∂μN n := by
    simp only [altY, Finset.mul_sum]
    exact integral_finsetSum _ fun σ _ => hint σ
  rw [hsum] at h1
  simp only [hterm] at h1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at h1
  have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => YG a σ).card : ℝ) ≠ 0 := by
    have : (1 : Equiv.Perm (Fin (n + 1))) ∈ Finset.univ.filter fun σ => YG a σ :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, YG_one a⟩
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  have hμ : ∫ x, g x * φ x ∂μN n = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · exact h
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n)]
  · simpa [smul_eq_mul, mul_comm] using hμ
  · intro x hx; rw [hout x hx, zero_smul]

/-- **Separation in a spin sector.** -/
theorem sep_lineWY (w : Cfg n → ℝ) (hw : Continuous w) :
    Sep (settingWS (ymix (n := n) a) w hw) := by
  intro v c ψ hψ h
  set g : Cfg n → ℝ := fun x => (LN n v x - c) * ψ x
  have hgc : Continuous fun x => LN n v x - c := (continuous_LN v).sub continuous_const
  obtain ⟨C, hC⟩ := ae_bound_cont hgc
  have hg : Integrable g (μN n) :=
    (hψ.1.integrable one_le_two).bdd_mul hgc.aestronglyMeasurable hC
  have hgs : ∀ σ, YG a σ → ∀ᵐ x ∂μN n, g (pm σ x) = sgn σ * g x := fun σ hσ => by
    filter_upwards [hψ.2.2 σ hσ] with x hx
    change ψ (pm σ x) = sgn σ * ψ x at hx
    simp only [g, LN_pm, hx]; ring
  exact ae_eq_zero_of_integral_altY_L1 hg hgs h

lemma rigidL_lineWY (w : Cfg n → ℝ) (hw : Continuous w) :
    RigidL (settingWS (ymix (n := n) a) w hw) one :=
  fun v c h => rigidL_line (τ := .bos) w hw v c h

variable {w : Cfg n → ℝ} {hw : Continuous w}

/-- **Hohenberg–Kohn in a spin sector**, continuous `v` and `w`: ground states exist, and ground
states of `v` and `v'` with the same norm and density force `v - v'` to be constant. -/
theorem hk_line_WY (v v' : Pot) :
    (∃ Φ, IsGS (settingWS (ymix a) w hw) v Φ) ∧ ∀ Ψ Ψ', IsGS (settingWS (ymix a) w hw) v Ψ →
      IsGS (settingWS (ymix a) w hw) v' Ψ' → ip (μ := μN n) Ψ Ψ = ip (μ := μN n) Ψ' Ψ' →
      dens (settingWS (ymix a) w hw) Ψ = dens (settingWS (ymix a) w hw) Ψ' →
        ∃ k : ℝ, v - v' = k • one :=
  ⟨(exists_isNGS_WY_cont a hw v).imp fun _ h => isGS_WS_of_isNGS h,
    fun _ _ hΨ hΨ' hn hd => hk_of_ucp (sep_lineWY w hw) (rigidL_lineWY w hw) hΨ hΨ' hn hd
      (gs_ne_zero_WY hΨ)⟩

/-- **The Lieb functional of a spin sector at a v-representable density.** -/
theorem lieb_line_WY_of {v : Pot} {ψ : Cfg n → ℝ} (hψ : IsNGS (settingWS (ymix a) w hw) v ψ) :
    liebF (settingWS (ymix a) w hw) (dens (settingWS (ymix a) w hw) ψ) =
        (((settingWS (ymix a) w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingWS (ymix a) w hw).h0 ψ ψ +
        dens (settingWS (ymix a) w hw) ψ v - ρ v : ℝ) : EReal) ≤
          liebF (settingWS (ymix a) w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ, (((settingWS (ymix a) w hw).h0 ψ ψ +
        dens (settingWS (ymix a) w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingWS (ymix a) w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  have hnull : ∀ φ ∈ (settingWS (ymix a) w hw).D, ip (μ := μN n) φ φ = 0 →
      0 ≤ (settingWS (ymix a) w hw).h0 φ φ := fun _ hφ h => h0WS_null hw hφ h
  refine ⟨liebF_of_isNGS hψ, subgrad_of_isNGS hψ, fun v' hsub => ?_⟩
  exact subgrad_unique (sep_lineWY w hw) (rigidL_lineWY w hw) hnull hψ
    (gs_ne_zero_WY (isGS_of_isNGS hnull hψ))
    (fun φ _ => hsub (dens (settingWS (ymix a) w hw) φ))

/-- **The Lieb functional of a spin sector**, continuous `v` and `w`: a normalised ground state
exists, and at its density the conclusions of `lieb_line_WY_of` hold. -/
theorem lieb_line_WY (hw : Continuous w) (v : Pot) :
    ∃ ψ, IsNGS (settingWS (ymix a) w hw) v ψ ∧
      liebF (settingWS (ymix a) w hw) (dens (settingWS (ymix a) w hw) ψ) =
        (((settingWS (ymix a) w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingWS (ymix a) w hw).h0 ψ ψ +
        dens (settingWS (ymix a) w hw) ψ v - ρ v : ℝ) : EReal) ≤
          liebF (settingWS (ymix a) w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ, (((settingWS (ymix a) w hw).h0 ψ ψ +
        dens (settingWS (ymix a) w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingWS (ymix a) w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψ⟩ := exists_isNGS_WY_cont a hw v
  exact ⟨ψ, hψ, lieb_line_WY_of hψ⟩

end DFT.Continuum.Line
