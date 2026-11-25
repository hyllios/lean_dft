/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.H1.WeakNec
import DFT.Continuum.Sine.Min

/-!
# Hohenberg–Kohn and the Lieb functional on `H¹₀`

The `C²` setting and the `H¹₀` setting `settingW` of `N` particles on a line have the same
physics:

* `gsE_W_eq`, `liebF_W_eq`: **the ground-state energies and the Lieb functionals agree**, for
  every continuous potential. The sine truncations of an `H¹₀` state are `C²` states whose energy
  converges to at most that of the state (`gsE_le_QW`).
* `sep_lineW`: separation for `H¹₀` states.
* `adm_cNW`, `Fn_le_QW`: the sine coefficients of an `H¹₀` state are admissible, and their
  coefficient-space energy is at most the energy.

Existence, uniqueness, Hohenberg–Kohn and the Lieb functional on `H¹₀` hold for all continuous
potentials (`Line/Realize`, `Line/Nondeg`, `Line/LiebCont`).
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
lemma QW_eq {s : SymT n} (v : Pot) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomWS s) :
    Q (settingWS s w hw) v Ψ = kinW Ψ + ∫ x, (LN n v x + w x) * (Ψ x * Ψ x) ∂μN n := by
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
    filter_upwards [hψ.2.2 σ trivial] with x hx
    simp only [g, LN_pm, hx]; ring
  refine ae_eq_zero_of_integral_alt hg hgs fun φ hφ => ?_
  exact h φ (Dom_le_DomW hφ)

lemma rigidL_lineW {s : SymT n} (w : Cfg n → ℝ) (hw : Continuous w) :
    RigidL (settingWS s w hw) one :=
  fun v c h => rigidL_line (τ := .bos) w hw v c h

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

lemma adm_cNW {s : SymT n} {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomWS s) (h1 : ∫ x, Ψ x ^ 2 ∂μN n = 1) :
    Adm s fun m => cN m Ψ :=
  { sq := (parsevalW hΨ.1).summable
    kin := summable_of_sum_le (fun m => mul_nonneg (lam_nonneg m) (sq_nonneg _))
      (sum_lam_le (h1W_of_mem hΨ))
    sym := fun σ hσ m => cN_pmWS hΨ hσ m
    norm := by rw [(parsevalW hΨ.1).tsum_eq, h1] }

lemma Fn_le_QW {s : SymT n} {w : Cfg n → ℝ} {hw : Continuous w} (v : Pot) {Ψ : Cfg n → ℝ}
    (hΨ : Ψ ∈ DomWS s) :
    Fn (fun x => LN n v x + w x) (fun m => cN m Ψ) ≤ Q (settingWS s w hw) v Ψ := by
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


end DFT.Continuum.Line
