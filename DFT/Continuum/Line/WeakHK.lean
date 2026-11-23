/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.WeakNec
import DFT.Continuum.Sine.General

/-!
# Hohenberg–Kohn and the Lieb functional on `H¹₀`

The `C²` setting and the `H¹₀` setting `settingW` of `N` particles on a line have the same
physics:

* `gsE_W_eq`, `liebF_W_eq`: **the ground-state energies and the Lieb functionals agree**, for
  every continuous potential. The sine truncations of an `H¹₀` state are `C²` states whose energy
  converges to at most that of the state (`gsE_le_QW`).
* `gsW_ae_eq`: for `Σ_k v(x_k) + w` smooth (`C^{2N}`) on the closed cube, **every `H¹₀` ground
  state is a.e. a `C²` ground state.** Its sine coefficients minimise the coefficient-space energy
  (`Fn_le_QW`), so the regularity theory of `Sine/Mixed` applies.
* `sep_lineW`: separation for `H¹₀` states.

With these, `exists_isGS_W`, `exists_unique_gs_W`, `hk_line_W` and `lieb_line_W` give existence,
uniqueness (a.e., up to a constant), Hohenberg–Kohn and the Lieb functional on `H¹₀`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-! ### Generalities -/

lemma ip_smul_self (c : ℝ) (ψ : Cfg n → ℝ) :
    ip (μ := μN n) (c • ψ) (c • ψ) = c * c * ip (μ := μN n) ψ ψ := by
  simp only [ip, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]; congr 1; funext x; ring

lemma isGS_smul {S : Setting (μN n) Pot} {v : Pot} {ψ : Cfg n → ℝ} (h : IsGS S v ψ) {c : ℝ}
    (hc : c ≠ 0) : IsGS S v (c • ψ) := by
  have hcc : 0 < c * c := mul_self_pos.2 hc
  refine ⟨S.D.smul_mem c h.1, by rw [ip_smul_self]; exact mul_pos hcc h.2.1, fun φ hφ => ?_⟩
  rw [Q_smul_self (S := S) v c h.1, ip_smul_self]
  have := mul_le_mul_of_nonneg_left (h.2.2 φ hφ) hcc.le
  linarith

section setting

variable {w : Cfg n → ℝ} {hw : Continuous w}

lemma QW_eq_Q (v : Pot) {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) :
    Q (settingW τ n w hw) v φ = Q (setting τ n w hw) v φ := by
  change h0W n w φ φ + pf (settingW τ n w hw) v φ φ = h0N n w φ φ + pf (setting τ n w hw) v φ φ
  rw [h0W_eq hφ hφ]; rfl

/-- The weak kinetic energy. -/
noncomputable def kinW (Ψ : Cfg n → ℝ) : ℝ := ∑ k, ∫ x, dW k Ψ x * dW k Ψ x ∂μN n

lemma kinW_nonneg (Ψ : Cfg n → ℝ) : 0 ≤ kinW Ψ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => mul_self_nonneg _

/-- `Q = T + ∫ V ψ²` with `V = Σ_k v(x_k) + w`. -/
lemma QW_eq (v : Pot) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) :
    Q (settingW τ n w hw) v Ψ = kinW Ψ + ∫ x, (LN n v x + w x) * (Ψ x * Ψ x) ∂μN n := by
  change h0W n w Ψ Ψ + ∫ x, LN n v x * (Ψ x * Ψ x) ∂μN n = _
  have hsq := int_mul_L2 hΨ.1 hΨ.1
  obtain ⟨C1, hC1⟩ := ae_bound_cont (n := n) (continuous_LN v)
  obtain ⟨C2, hC2⟩ := ae_bound_cont (n := n) hw
  rw [show (fun x => (LN n v x + w x) * (Ψ x * Ψ x)) =
      fun x => LN n v x * (Ψ x * Ψ x) + w x * (Ψ x * Ψ x) from funext fun x => by ring,
    integral_add (hsq.bdd_mul (continuous_LN v).aestronglyMeasurable hC1)
      (hsq.bdd_mul hw.aestronglyMeasurable hC2)]
  simp only [h0W, kinW]; ring

lemma Q_le_trunc (v : Pot) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) (M : ℕ) :
    Q (setting τ n w hw) v (trunc M Ψ) ≤
      kinW Ψ + ∫ x, (LN n v x + w x) * (trunc M Ψ x * trunc M Ψ x) ∂μN n := by
  have hP := trunc_mem hΨ M
  rw [← QW_eq_Q v hP, QW_eq v (Dom_le_DomW hP)]
  gcongr
  have h := kin_trunc_le (h1W_of_mem hΨ) M
  rw [kinW]
  refine le_trans (le_of_eq ?_) h
  rw [integral_finsetSum (f := fun k x => dk k (trunc M Ψ) x * dk k (trunc M Ψ) x) _
    fun k _ => integrableN ((cont_dk hP k).mul (cont_dk hP k))]
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [dW_ae_eq_dk hP k] with x hx
  rw [hx]

end setting

/-! ### Convergence of potential energies along the truncations -/

lemma tendsto_pot_trunc {V Ψ : Cfg n → ℝ} (hV : Continuous V) (hΨ : MemLp Ψ 2 (μN n)) :
    Tendsto (fun M => ∫ x, V x * (trunc M Ψ x * trunc M Ψ x) ∂μN n) atTop
      (𝓝 (∫ x, V x * (Ψ x * Ψ x) ∂μN n)) := by
  obtain ⟨C, hC⟩ := ae_bound_cont hV
  set C' := max C 0
  have hC' : ∀ᵐ x ∂μN n, ‖V x‖ ≤ C' := hC.mono fun x hx => hx.trans (le_max_left _ _)
  have hsq := int_mul_L2 hΨ hΨ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ M, ‖∫ x, V x * (trunc M Ψ x * trunc M Ψ x) ∂μN n - ∫ x, V x * (Ψ x * Ψ x) ∂μN n‖
      ≤ C' * ∫ x, |trunc M Ψ x ^ 2 - Ψ x ^ 2| ∂μN n := by
    intro M
    have hP := continuous_trunc M Ψ
    rw [← integral_sub (f := fun x => V x * (trunc M Ψ x * trunc M Ψ x))
      (g := fun x => V x * (Ψ x * Ψ x)) (integrableN (hV.mul (hP.mul hP)))
      (hsq.bdd_mul hV.aestronglyMeasurable hC), Real.norm_eq_abs, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae ?_ ?_ ?_)
    · exact ((integrableN (hV.mul (hP.mul hP))).sub (hsq.bdd_mul hV.aestronglyMeasurable hC)).abs
    · exact (((int_sq (memLp_cont hP)).sub (int_sq hΨ)).abs).const_mul _
    · filter_upwards [hC'] with x hx
      rw [show V x * (trunc M Ψ x * trunc M Ψ x) - V x * (Ψ x * Ψ x) =
        V x * (trunc M Ψ x ^ 2 - Ψ x ^ 2) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa using hx) (abs_nonneg _)
  have hl := (tendsto_abs_sq_trunc hΨ).const_mul C'
  rw [mul_zero] at hl
  exact squeeze_zero (fun M => norm_nonneg _) hb hl

/-! ### The ground-state energies agree -/

section energy

variable {w : Cfg n → ℝ} {hw : Continuous w}

/-- **The `C²` ground-state energy is at most the energy of every `H¹₀` state.** -/
theorem gsE_le_QW (v : Pot) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ Nst (settingW τ n w hw)) :
    gsE (setting τ n w hw) v ≤ ((Q (settingW τ n w hw) v Ψ : ℝ) : EReal) := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hV : Continuous V := (continuous_LN v).add hw
  have h1 : ∫ x, Ψ x * Ψ x ∂μN n = 1 := hΨ.2
  set a : ℕ → ℝ := fun M => ∫ x, trunc M Ψ x * trunc M Ψ x ∂μN n
  have ha : Tendsto a atTop (𝓝 1) := by
    have := tendsto_pot_trunc (V := fun _ => (1 : ℝ)) continuous_const hΨ.1.1
    simp only [one_mul, h1] at this
    exact this
  set b : ℕ → ℝ := fun M => kinW Ψ + ∫ x, V x * (trunc M Ψ x * trunc M Ψ x) ∂μN n
  have hb : Tendsto (fun M => b M / a M) atTop (𝓝 (Q (settingW τ n w hw) v Ψ)) := by
    rw [QW_eq v hΨ.1, ← div_one (kinW Ψ + _)]
    exact ((tendsto_pot_trunc hV hΨ.1.1).const_add _).div ha one_ne_zero
  have hev : ∀ᶠ M in atTop, gsE (setting τ n w hw) v ≤ ((b M / a M : ℝ) : EReal) := by
    filter_upwards [ha.eventually (lt_mem_nhds one_pos)] with M hM
    have hP := trunc_mem hΨ.1 M
    have haM : ip (μ := μN n) (trunc M Ψ) (trunc M Ψ) = a M := by simp [ip, a]
    set c := (√(a M))⁻¹
    have hcc : c * c = (a M)⁻¹ := by
      simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hM.le]
    have hN : c • trunc M Ψ ∈ Nst (setting τ n w hw) :=
      ⟨(Dom τ n).smul_mem c hP, by rw [ip_smul_self, haM, hcc, inv_mul_cancel₀ hM.ne']⟩
    refine (gsE_le hN).trans (EReal.coe_le_coe_iff.2 ?_)
    rw [Q_smul_self v c hP, hcc, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (Q_le_trunc v hΨ.1 M) hM.le
  exact ge_of_tendsto ((continuous_coe_real_ereal.tendsto _).comp hb) hev

/-- **The ground-state energies of the `C²` and `H¹₀` settings agree.** -/
theorem gsE_W_eq (v : Pot) : gsE (settingW τ n w hw) v = gsE (setting τ n w hw) v := by
  refine le_antisymm (le_iInf₂ fun ψ hψ => ?_) (le_iInf₂ fun ψ hψ => gsE_le_QW v hψ)
  have hψW : ψ ∈ Nst (settingW τ n w hw) := ⟨Dom_le_DomW hψ.1, hψ.2⟩
  refine (gsE_le hψW).trans (le_of_eq ?_)
  rw [QW_eq_Q v hψ.1]

/-- **The Lieb functionals of the `C²` and `H¹₀` settings agree.** -/
theorem liebF_W_eq : liebF (settingW τ n w hw) = liebF (setting τ n w hw) := by
  funext ρ; simp only [liebF, gsE_W_eq]

end energy

/-! ### Separation on `H¹₀` -/

/-- The fundamental lemma for integrable functions of a.e. exchange symmetry `τ`. -/
lemma ae_eq_zero_of_integral_alt {g : Cfg n → ℝ} (hg : Integrable g (μN n))
    (hgs : ∀ σ, ∀ᵐ x ∂μN n, g (pm σ x) = ch τ σ * g x)
    (h : ∀ φ ∈ Dom τ n, ∫ x, g x * φ x ∂μN n = 0) : g =ᵐ[μN n] 0 := by
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Cube n) (μ := volume)
    (f := g) isOpen_cube
    ((show IntegrableOn g (Cube n) volume from hg).locallyIntegrableOn)
    (fun φ hφ _ (hsub : tsupport φ ⊆ Cube n) => ?_)
  · exact (ae_restrict_iff' measurableSet_cube).2 hae
  have hout : ∀ x, x ∉ Cube n → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hsub h')
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 := h (alt τ φ) (alt_mem hφ2 hout)
  have hint : ∀ σ : Equiv.Perm (Fin (n + 1)),
      Integrable (fun x => g x * (ch τ σ * φ (pm σ x))) (μN n) := fun σ => by
    obtain ⟨C, hC⟩ := ae_bound_cont (n := n)
      (continuous_const.mul (hφ.continuous.comp (continuous_pm σ)))
    exact hg.mul_bdd
      (continuous_const.mul (hφ.continuous.comp (continuous_pm σ))).aestronglyMeasurable hC
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∫ x, g x * (ch τ σ * φ (pm σ x)) ∂μN n = ∫ x, g x * φ x ∂μN n := by
    intro σ
    have := integral_pm σ (fun y => g (pm σ⁻¹ y) * (ch τ σ * φ y))
    simp only [pm_inv_pm] at this
    rw [this]
    refine integral_congr_ae ?_
    filter_upwards [hgs σ⁻¹] with y hy
    rw [hy, ch_inv τ]
    linear_combination (g y * φ y) * ch_mul_self τ σ
  have hsum : ∫ x, g x * alt τ φ x ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∫ x, g x * (ch τ σ * φ (pm σ x)) ∂μN n := by
    simp only [alt, Finset.mul_sum]
    exact integral_finsetSum (f := fun σ x => g x * (ch τ σ * φ (pm σ x))) _ fun σ _ => hint σ
  rw [hsum] at h1
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  have hc : (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hμ : ∫ x, g x * φ x ∂μN n = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · exact h
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n)]
  · simpa [smul_eq_mul, mul_comm] using hμ
  · intro x hx; rw [hout x hx, zero_smul]

/-- **Separation on `H¹₀`.** -/
theorem sep_lineW (w : Cfg n → ℝ) (hw : Continuous w) : Sep (settingW τ n w hw) := by
  intro v c ψ hψ h
  set g : Cfg n → ℝ := fun x => (LN n v x - c) * ψ x
  have hgc : Continuous fun x => LN n v x - c := (continuous_LN v).sub continuous_const
  obtain ⟨C, hC⟩ := ae_bound_cont hgc
  have hg : Integrable g (μN n) :=
    (hψ.1.integrable one_le_two).bdd_mul hgc.aestronglyMeasurable hC
  have hgs : ∀ σ, ∀ᵐ x ∂μN n, g (pm σ x) = ch τ σ * g x := fun σ => by
    filter_upwards [hψ.2.2 σ] with x hx
    simp only [g, LN_pm, hx]; ring
  refine ae_eq_zero_of_integral_alt hg hgs fun φ hφ => ?_
  exact h φ (Dom_le_DomW hφ)

lemma rigidL_lineW (w : Cfg n → ℝ) (hw : Continuous w) : RigidL (settingW τ n w hw) one :=
  fun v c h => rigidL_line (τ := τ) w hw v c h

/-! ### Coefficients of `H¹₀` states -/

/-- **Parseval for pairs** of `L²` functions on the cube. -/
lemma parsevalW_pair {f g : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hg : MemLp g 2 (μN n)) :
    HasSum (fun m => cN m f * cN m g) (∫ x, f x * g x ∂μN n) := by
  have h := (bN (n := n)).hasSum_inner_mul_inner (hf.toLp f) (hg.toLp g)
  simp only [bN_apply, real_inner_comm (eN _) (hf.toLp f), inner_eN_toLp hf, inner_eN_toLp hg,
    inner_toLp_left hf] at h
  convert h using 1
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hg] with x hx
  rw [hx]

lemma memLp_mul_cont {V Ψ : Cfg n → ℝ} (hV : Continuous V) (hΨ : MemLp Ψ 2 (μN n)) :
    MemLp (fun x => V x * Ψ x) 2 (μN n) := by
  obtain ⟨C, hC⟩ := ae_bound_cont hV
  refine hΨ.of_le_mul (c := C) (hV.aestronglyMeasurable.mul hΨ.aestronglyMeasurable) ?_
  filter_upwards [hC] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- **The potential energy in coefficients**, for `L²` states. -/
lemma Bf_cNW {V Ψ : Cfg n → ℝ} (hV : Continuous V) (hΨ : MemLp Ψ 2 (μN n)) :
    Bf V (fun m => cN m Ψ) (fun m => cN m Ψ) = ∫ x, V x * (Ψ x * Ψ x) ∂μN n := by
  have hK : ∀ m', Kc V (fun m => cN m Ψ) m' = cN m' (fun x => V x * Ψ x) := fun m' => by
    rw [Kc]
    simp only [Ker_eq_cN]
    rw [(parsevalW_pair (f := fun x => V x * smd m' x) (memLp_cont (hV.mul (continuous_smd m')))
      hΨ).tsum_eq, cN_eq]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  simp only [Bf, hK]
  rw [(parsevalW_pair hΨ (memLp_mul_cont hV hΨ)).tsum_eq]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- Bessel for the kinetic energy: every partial sum of `Σ λ_m c_m²` is at most `T`. -/
lemma sum_lam_le {Ψ : Cfg n → ℝ} (hΨ : H1W Ψ) (s : Finset (Fin (n + 1) → ℕ)) :
    ∑ m ∈ s, lam m * cN m Ψ ^ 2 ≤ kinW Ψ := by
  set M := (s.sup fun m => Finset.univ.sup m) + 1
  have hsub : s ⊆ boxI n M := fun m hm => mem_boxI.2 fun j => by
    have h1 : m j ≤ Finset.univ.sup m := Finset.le_sup (f := m) (Finset.mem_univ j)
    have h2 : Finset.univ.sup m ≤ s.sup fun m => Finset.univ.sup m :=
      Finset.le_sup (f := fun m => Finset.univ.sup m) hm
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
    mul_nonneg (lam_nonneg m) (sq_nonneg _)).trans ?_
  have h := kin_trunc_le hΨ M
  rw [kin_trunc Ψ] at h
  simpa [lam, kinW] using h

lemma adm_cNW {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) (h1 : ∫ x, Ψ x ^ 2 ∂μN n = 1) :
    Adm τ.toSym fun m => cN m Ψ :=
  { sq := (parsevalW hΨ.1).summable
    kin := summable_of_sum_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _))
      (sum_lam_le (h1W_of_mem hΨ))
    sym := fun σ _ m => cN_pmW hΨ σ m
    norm := by rw [(parsevalW hΨ.1).tsum_eq, h1] }

lemma Fn_le_QW {w : Cfg n → ℝ} {hw : Continuous w} (v : Pot) {Ψ : Cfg n → ℝ}
    (hΨ : Ψ ∈ DomW τ n) :
    Fn (fun x => LN n v x + w x) (fun m => cN m Ψ) ≤ Q (settingW τ n w hw) v Ψ := by
  rw [Fn, Bf_cNW (V := fun x => LN n v x + w x) ((continuous_LN v).add hw) hΨ.1, QW_eq v hΨ]
  gcongr
  exact Summable.tsum_le_of_sum_le (summable_of_sum_le
    (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _)) (sum_lam_le (h1W_of_mem hΨ)))
    (sum_lam_le (h1W_of_mem hΨ))

/-- `L²` functions with the same sine coefficients agree a.e. -/
lemma ae_eq_of_cN_eq {f g : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hg : MemLp g 2 (μN n))
    (h : ∀ m, cN m f = cN m g) : f =ᵐ[μN n] g := by
  have hz : hf.toLp f - hg.toLp g = 0 := eN_complete _ fun m => by
    rw [inner_sub_right, inner_eN_toLp, inner_eN_toLp, h, sub_self]
  rw [sub_eq_zero] at hz
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x h1 h2
  rw [← h1, ← h2, hz]

/-! ### Ground states on `H¹₀` -/

section gs

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **Regularity**: every `H¹₀` ground state is a.e. a `C²` ground state. -/
theorem gsW_ae_eq {Ψ : Cfg n → ℝ} (hΨ : IsGS (settingW τ n w hw) v Ψ) :
    ∃ Φ, IsGS (setting τ n w hw) v Φ ∧ Ψ =ᵐ[μN n] Φ := by
  set V : Cfg n → ℝ := fun x => LN n v x + w x
  have hVs : ∀ σ x, V (pm σ x) = V x := fun σ x => by simp only [V, LN_pm, hws]
  obtain ⟨b, hb0, hbS, hK, hG⟩ := kernel_of_smooth ((continuous_LN v).add hw) hF hVF
  -- the coefficient-space minimiser and its `C²` state
  obtain ⟨a0, ha0, hmin0⟩ := (kBd_of_kernel hb0 hbS hK).exists_min (V := V) (exists_adm τ)
  obtain ⟨hΦ0, hc0⟩ := ser_min2 hb0 hbS hK hVs ha0 hmin0 (by norm_num) (by norm_num) hG
  have hc0' : (fun m => cN m (ser a0)) = a0 := funext hc0
  have hip0 : ip (μ := μN n) (ser a0) (ser a0) = 1 := by
    rw [ip_eq_tsum hΦ0.1.continuous]; simp only [hc0]; exact ha0.norm
  have hQ0 : Q (settingW τ n w hw) v (ser a0) = E0 V τ.toSym := by
    rw [QW_eq_Q v hΦ0, Q_eq_Fn hw v hΦ0, hc0', hmin0]
  -- normalise `Ψ`
  have hs := hΨ.2.1
  set c := (√(ip (μ := μN n) Ψ Ψ))⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hs).ne'
  have hcc : c * c * ip (μ := μN n) Ψ Ψ = 1 := by
    simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hs.le, inv_mul_cancel₀ hs.ne']
  have hΨ1 := isGS_smul hΨ hc
  have hip1 : ip (μ := μN n) (c • Ψ) (c • Ψ) = 1 := by rw [ip_smul_self, hcc]
  have hsq1 : ∫ x, (c • Ψ) x ^ 2 ∂μN n = 1 := by rw [← hip1]; simp only [ip, sq]
  set a := fun m => cN m (c • Ψ)
  have ha := adm_cNW hΨ1.1 hsq1
  -- `E₀ ≤ Fn a ≤ Q(cΨ) ≤ Q(Φ₀) = E₀`
  have hE1 : E0 V τ.toSym ≤ Fn V a := csInf_le ((kBd_of_kernel hb0 hbS hK).bddBelow_Fn τ.toSym) ⟨a, ha, rfl⟩
  have hE2 : Fn V a ≤ Q (settingW τ n w hw) v (c • Ψ) := Fn_le_QW v hΨ1.1
  have hE3 : Q (settingW τ n w hw) v (c • Ψ) ≤ E0 V τ.toSym := by
    have := hΨ1.2.2 (ser a0) (Dom_le_DomW hΦ0)
    rwa [hip0, hip1, mul_one, mul_one, hQ0] at this
  have hmin : Fn V a = E0 V τ.toSym := le_antisymm (hE2.trans hE3) hE1
  have hQ1 : Q (settingW τ n w hw) v (c • Ψ) = E0 V τ.toSym := le_antisymm hE3 (hE1.trans hE2)
  obtain ⟨hΦ1, hc1⟩ := ser_min2 hb0 hbS hK hVs ha hmin (by norm_num) (by norm_num) hG
  have hc1' : (fun m => cN m (ser a)) = a := funext hc1
  have hip' : ip (μ := μN n) (ser a) (ser a) = 1 := by
    rw [ip_eq_tsum hΦ1.1.continuous]; simp only [hc1]; exact ha.norm
  -- `ser a` is a `C²` ground state
  have hGS : IsGS (setting τ n w hw) v (ser a) := by
    refine ⟨hΦ1, by rw [hip']; exact one_pos, fun φ hφ => ?_⟩
    have h := hΨ1.2.2 φ (Dom_le_DomW hφ)
    rw [hip1, mul_one, hQ1, QW_eq_Q v hφ] at h
    rw [Q_eq_Fn hw v hΦ1, hc1', hmin, hip', mul_one]
    exact h
  -- `cΨ = ser a` a.e.
  have hae : (c • Ψ) =ᵐ[μN n] ser a :=
    ae_eq_of_cN_eq hΨ1.1.1 (memLp_cont hΦ1.1.continuous) fun m => (hc1 m).symm
  refine ⟨c⁻¹ • ser a, isGS_smul hGS (inv_ne_zero hc), ?_⟩
  filter_upwards [hae] with x hx
  simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
  rw [← hx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

omit hws hF hVF in
/-- A `C²` normalised ground state minimises the energy over all `H¹₀` states (any continuous
`v`). -/
lemma isNGS_le_QW {Φ : Cfg n → ℝ} (hΦ : IsNGS (setting τ n w hw) v Φ) {φ : Cfg n → ℝ}
    (hφ : φ ∈ DomW τ n) :
    Q (setting τ n w hw) v Φ * ip (μ := μN n) φ φ ≤ Q (settingW τ n w hw) v φ := by
  have hip0 : 0 ≤ ip (μ := μN n) φ φ := integral_nonneg fun x => mul_self_nonneg _
  rcases hip0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, QW_eq v hφ]
    have hz : (fun x => φ x * φ x) =ᵐ[μN n] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _)
        (int_mul_L2 hφ.1 hφ.1)).1 h0.symm
    have : ∫ x, (LN n v x + w x) * (φ x * φ x) ∂μN n = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [hz] with x hx
      simp [hx]
    rw [this, add_zero]; exact kinW_nonneg φ
  · set c := (√(ip (μ := μN n) φ φ))⁻¹
    have hcc : c * c = (ip (μ := μN n) φ φ)⁻¹ := by
      simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hpos.le]
    have hN : c • φ ∈ Nst (settingW τ n w hw) :=
      ⟨(DomW τ n).smul_mem c hφ, by rw [ip_smul_self, hcc, inv_mul_cancel₀ hpos.ne']⟩
    have h := gsE_le_QW v hN
    rw [gsE_of_isNGS hΦ, EReal.coe_le_coe_iff, Q_smul_self v c hφ, hcc] at h
    rw [← le_div_iff₀ hpos, div_eq_inv_mul]
    exact h

/-- **Existence of a normalised ground state on `H¹₀`.** -/
theorem exists_isNGS_W : ∃ Φ, IsNGS (settingW τ n w hw) v Φ ∧ Φ ∈ Dom τ n := by
  obtain ⟨Φ, hΦ⟩ := exists_isNGS_smooth (τ := τ) (hw := hw) hws hF hVF
  refine ⟨Φ, ⟨⟨Dom_le_DomW hΦ.1.1, hΦ.1.2⟩, fun φ hφ => ?_⟩, hΦ.1.1⟩
  have h := isNGS_le_QW hΦ hφ.1
  rw [hφ.2, mul_one, ← QW_eq_Q v hΦ.1.1] at h
  exact h

omit hws hF hVF in
lemma isNGS_of_W {Φ : Cfg n → ℝ} (hΦ : IsNGS (settingW τ n w hw) v Φ) (hD : Φ ∈ Dom τ n) :
    IsNGS (setting τ n w hw) v Φ :=
  ⟨⟨hD, hΦ.1.2⟩, fun ψ hψ => by
    have := hΦ.2 ψ ⟨Dom_le_DomW hψ.1, hψ.2⟩
    rwa [QW_eq_Q v hD, QW_eq_Q v hψ.1] at this⟩

omit hws hF hVF in
lemma isGS_W_of_isNGS {Φ : Cfg n → ℝ} (hΦ : IsNGS (setting τ n w hw) v Φ) :
    IsGS (settingW τ n w hw) v Φ := by
  refine ⟨Dom_le_DomW hΦ.1.1, by rw [hΦ.1.2]; exact one_pos, fun φ hφ => ?_⟩
  rw [hΦ.1.2, mul_one, QW_eq_Q v hΦ.1.1]
  exact isNGS_le_QW hΦ hφ

theorem exists_isGS_W : ∃ Φ, IsGS (settingW τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 := by
  obtain ⟨Φ, hΦ, hD⟩ := exists_isNGS_W hws hF hVF (τ := τ) (hw := hw)
  exact ⟨Φ, isGS_W_of_isNGS (isNGS_of_W hΦ hD), hΦ.1.2⟩

/-- **Existence and uniqueness on `H¹₀`**: a normalised ground state exists, and every ground
state is a.e. a constant multiple of it. -/
theorem exists_unique_gs_W :
    ∃ Φ, IsGS (settingW τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (settingW τ n w hw) v Ψ → ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ := by
  obtain ⟨Φ, hΦ, hD⟩ := exists_isNGS_W hws hF hVF (τ := τ) (hw := hw)
  have hn := isNGS_of_W hΦ hD
  have hGS : IsGS (setting τ n w hw) v Φ := by
    refine ⟨hD, by rw [hΦ.1.2]; exact one_pos, fun φ hφ => ?_⟩
    have h := isNGS_le_QW hn (Dom_le_DomW hφ)
    rw [QW_eq_Q v hφ] at h
    rw [hΦ.1.2, mul_one]; exact h
  refine ⟨Φ, isGS_W_of_isNGS hn, hΦ.1.2, fun Ψ hΨ => ?_⟩
  obtain ⟨Φ'', h1, h2⟩ := gsW_ae_eq hws hF hVF hΨ
  obtain ⟨c, hc⟩ := gs_unique_line hws h1 hGS
  refine ⟨c, ?_⟩
  filter_upwards [h2, ae_restrict_mem measurableSet_cube] with x hx hxC
  rw [hx, hc x (cube_subset hxC)]; rfl

/-- **Hohenberg–Kohn on `H¹₀`**: the ground state of `v` exists, and ground states of `v` and of
any continuous `v'` with the same norm and density force `v - v'` to be constant. -/
theorem hk_line_W (v' : Pot) :
    (∃ Φ, IsGS (settingW τ n w hw) v Φ) ∧ ∀ Ψ Ψ', IsGS (settingW τ n w hw) v Ψ →
      IsGS (settingW τ n w hw) v' Ψ' → ip (μ := μN n) Ψ Ψ = ip (μ := μN n) Ψ' Ψ' →
      dens (settingW τ n w hw) Ψ = dens (settingW τ n w hw) Ψ' → ∃ k : ℝ, v - v' = k • one := by
  refine ⟨(exists_isGS_W hws hF hVF).imp fun _ h => h.1, fun Ψ Ψ' hΨ hΨ' hn hd => ?_⟩
  obtain ⟨Φ, hΦ, hae⟩ := gsW_ae_eq hws hF hVF hΨ
  have hucp : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
    filter_upwards [hae, ucp_line_stat hws hΦ] with x h1 h2
    rw [h1]; exact h2
  exact hk_of_ucp (sep_lineW w hw) (rigidL_lineW w hw) hΨ hΨ' hn hd hucp

/-- **The Lieb functional on `H¹₀`**: a normalised `C²` ground state `ψ` is a ground state on
`H¹₀`; at its density the Lieb functional equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every
other subgradient `-v'` has `v - v'` constant. -/
theorem lieb_line_W :
    ∃ ψ, IsNGS (settingW τ n w hw) v ψ ∧
      liebF (settingW τ n w hw) (dens (settingW τ n w hw) ψ) =
        (((settingW τ n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (settingW τ n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingW τ n w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψW, hD⟩ := exists_isNGS_W hws hF hVF (τ := τ) (hw := hw)
  have hψ : IsNGS (setting τ n w hw) v ψ :=
    ⟨⟨hD, hψW.1.2⟩, fun φ hφ => by
      have := hψW.2 φ ⟨Dom_le_DomW hφ.1, hφ.2⟩
      rwa [QW_eq_Q v hD, QW_eq_Q v hφ.1] at this⟩
  have hL := lieb_line hws hψ
  have hh : (settingW τ n w hw).h0 ψ ψ = (setting τ n w hw).h0 ψ ψ := h0W_eq hD hD
  have hd : dens (settingW τ n w hw) ψ = dens (setting τ n w hw) ψ := rfl
  refine ⟨ψ, hψW, ?_⟩
  rw [liebF_W_eq, hh, hd]
  exact hL

end gs

end DFT.Continuum.Line
