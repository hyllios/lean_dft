/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.NEL

/-!
# Unique continuation for bosonic ground states of measure potentials

For `N` bosons on the line with a measure potential `ν ∈ C([0, 1])*` and a continuous interaction
`w`, every `H¹₀` ground state is nonzero almost everywhere (**`gsN_ne_zero_bos`**).

The proof is that of `Line/UcpBos`. The only place where the potential enters is Moser's
logarithmic estimate, through a lower bound on `Σ_k ∫ ∂ₖu ∂ₖφ` for the test function
`φ = η²/(u + ε)`; `log_estimate_core` isolates this. For a measure potential the bound comes from
`0 ≤ u φ ≤ η² ≤ 1`: the mixed density `ρ̂(u, φ)` then lies between `0` and `N`
(`norm_rhoHat2_le`), so `|ν(ρ̂(u, φ))| ≤ N ‖ν‖`.

* `log_estimate_core`; `pot_le_of_int`, `pot_nonneg_of_int`, `norm_rhoHat2_le`;
  `logData_meas`; **`gsN_ne_zero_bos`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ}

/-! ### Moser's estimate from a lower bound -/

/-- **The logarithmic estimate from a lower bound** `-K ≤ Σ_k ∫ ∂ₖu ∂ₖφ`, `φ = logTest η u ε`. -/
theorem log_estimate_core {u : Cfg n → ℝ} (hD : H1W u) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η)
    (hηw : ∀ x k, (x k = 0 ∨ x k = 1) → η x = 0) {ε : ℝ} (hε : 0 < ε) {K : ℝ}
    (hlow : -K ≤ ∑ k, ∫ x, dW k u x * dW k (logTest η u ε) x ∂μN n) :
    ∑ k, ∫ x, (η x * (dW k u x / (u x + ε))) ^ 2 ∂μN n ≤
      4 * ∑ k, ∫ x, dk k η x ^ 2 ∂μN n + 2 * K := by
  have hum := hD.1
  set ζ : Cfg n → ℝ := fun x => η x * η x with hζdef
  have hζ : ContDiff ℝ 1 ζ := hη.mul hη
  have hζw : ∀ x k, (x k = 0 ∨ x k = 1) → ζ x = 0 := fun x k h => by simp [ζ, hηw x k h]
  have hdζ : ∀ k x, dk k ζ x = 2 * η x * dk k η x := fun k x => by
    rw [dk_mul (hη.differentiable one_ne_zero) (hη.differentiable one_ne_zero)]; ring
  have hGc : Continuous (Gr ε) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_Gr hε t).continuousAt
  set g : Cfg n → ℝ := fun x => Gr ε (u x)
  have hgL : MemLp g 2 (μN n) := MemLp.of_bound (hGc.comp_aestronglyMeasurable
    hum.aestronglyMeasurable) (1 / ε) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact abs_Gr_le hε _)
  have hg : ∀ k, IsWD k g (fun x => 1 / (|u x| + ε) ^ 2 * dW k u x) := fun k =>
    isWD_comp hD (hasDerivAt_Gr hε) (continuous_Gr' hε) (Gr'_le hε) Gr_zero k
  set φ : Cfg n → ℝ := fun x => ε⁻¹ * ζ x + (-1) * (ζ x * g x)
  have hφe : logTest η u ε = φ := rfl
  rw [hφe] at hlow
  have hL1 : MemLp (fun x => ε⁻¹ * ζ x) 2 (μN n) := memLp_cont (continuous_const.mul hζ.continuous)
  have hL2 : MemLp (fun x => -1 * (ζ x * g x)) 2 (μN n) :=
    (memLp_mul_cont hζ.continuous hgL).const_mul (-1)
  have hφWD : ∀ k, IsWD k φ (fun x => ε⁻¹ * dk k ζ x +
      (-1) * (ζ x * (1 / (|u x| + ε) ^ 2 * dW k u x) + dk k ζ x * g x)) := fun k =>
    IsWD.add hL1 hL2 ((isWD_of_C1 hζ hζw k).const_mul ε⁻¹)
      (((hg k).mul_C1 hgL hζ).const_mul (-1))
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  set A : Fin (n + 1) → Cfg n → ℝ := fun k x => η x * (dW k u x / (u x + ε))
  have hAL : ∀ k, MemLp (A k) 2 (μN n) := fun k => by
    refine (dW_spec (hD.2 k)).1.of_le_mul (c := Bη / ε) (hη.continuous.aemeasurable.mul
      ((dW_spec (hD.2 k)).1.aestronglyMeasurable.aemeasurable.div
        (hum.aestronglyMeasurable.aemeasurable.add_const ε))).aestronglyMeasurable ?_
    filter_upwards [hBη, hu0] with x hx h0
    have hp : 0 < u x + ε := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at *
    simp only [A, abs_mul, abs_div, abs_of_pos hp]
    rw [mul_div_assoc', div_le_iff₀ hp]
    have h1 : |η x| * |dW k u x| ≤ Bη * |dW k u x| :=
      mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have h2 : Bη / ε * |dW k u x| * ε ≤ Bη / ε * |dW k u x| * (u x + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (div_nonneg ((abs_nonneg _).trans hx)
        hε.le) (abs_nonneg _))
    have h3 : Bη / ε * |dW k u x| * ε = Bη * |dW k u x| := by field_simp
    linarith
  have hdη : ∀ k, Continuous (dk k η) := fun k => continuous_dk_of_C1 hη k
  have hpt : ∀ k, ∀ᵐ x ∂μN n, dW k u x * dW k φ x = 2 * (A k x * dk k η x) - A k x ^ 2 := by
    intro k
    filter_upwards [dW_ae_eq (hφWD k), hu0] with x hx h0
    have hp : 0 < u x + ε := by linarith
    rw [hx]
    simp only [A, hdζ, g, ζ, Gr_of_nonneg h0, abs_of_nonneg h0]
    field_simp
    ring
  have hk : ∀ k, ∫ x, dW k u x * dW k φ x ∂μN n =
      2 * ∫ x, A k x * dk k η x ∂μN n - ∫ x, A k x ^ 2 ∂μN n := fun k => by
    rw [integral_congr_ae (hpt k), integral_sub ((int_mul_cont (hAL k) (hdη k)).const_mul 2)
      (hAL k).integrable_sq, integral_const_mul]
  have hAB : ∀ k, ∫ x, A k x * dk k η x ∂μN n ≤
      (1 / 4) * ∫ x, A k x ^ 2 ∂μN n + ∫ x, dk k η x ^ 2 ∂μN n := fun k => by
    rw [← integral_const_mul, ← integral_add (f := fun x => 1 / 4 * A k x ^ 2)
      (g := fun x => dk k η x ^ 2) ((hAL k).integrable_sq.const_mul _)
      (integrableN ((hdη k).pow 2))]
    refine integral_mono (int_mul_cont (hAL k) (hdη k))
      (((hAL k).integrable_sq.const_mul _).add (integrableN ((hdη k).pow 2))) fun x => ?_
    nlinarith [sq_nonneg (A k x - 2 * dk k η x)]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hAB k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hid : ∑ k, ∫ x, dW k u x * dW k φ x ∂μN n =
      2 * ∑ k, ∫ x, A k x * dk k η x ∂μN n - ∑ k, ∫ x, A k x ^ 2 ∂μN n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hk k
  change ∑ k, ∫ x, A k x ^ 2 ∂μN n ≤ _
  linarith

/-! ### Bounds on continuous functions from their integrals -/

lemma le_of_int_nonneg_zero {g : ℝ → ℝ} (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    (hint : ∫ t, g t ∂vol01 ≤ 0) : ∀ t ∈ Icc (0 : ℝ) 1, g t = 0 := by
  have hi : Integrable g vol01 := (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set
    Ioo_subset_Icc_self
  have hz : g =ᵐ[vol01] 0 := (integral_eq_zero_iff_of_nonneg h0 hi).1
    (le_antisymm hint (integral_nonneg h0))
  have hIoo : EqOn g 0 (Ioo 0 1) := Measure.eqOn_of_ae_eq hz hg.continuousOn
    continuousOn_const (by rw [interior_Ioo]; exact subset_closure)
  exact hIoo.of_subset_closure hg.continuousOn continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo zero_ne_one])

lemma ext_le_norm (p : C01) (t : ℝ) : |iccExt p t| ≤ ‖p‖ := by
  simpa [SturmLiouville.iccExt] using p.norm_coe_le_norm _

/-- A continuous `p` with `∫ v p ≤ M ∫ v` for all `v ≥ 0` is at most `M`. -/
lemma pot_le_of_int {p : C01} {M : ℝ}
    (h : ∀ v : C01, (∀ t, 0 ≤ v t) → ∫ t, iccExt v t * iccExt p t ∂vol01 ≤ M * ∫ t, iccExt v t ∂vol01) :
    ∀ t, p t ≤ M := by
  set v : C01 := ⟨fun t => max (p t - M) 0, by fun_prop⟩
  have hv := h v fun t => le_max_right _ _
  have hiv : Integrable (iccExt v) vol01 := (continuous_iccExt v).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self
  rw [← integral_const_mul, ← sub_nonpos, ← integral_sub (integrable_ext_mul v p)
    (hiv.const_mul M)] at hv
  have hz := le_of_int_nonneg_zero (g := fun t => iccExt v t * iccExt p t - M * iccExt v t)
    (((continuous_iccExt v).mul (continuous_iccExt p)).sub (continuous_const.mul (continuous_iccExt v)))
    (fun t => by
      have : iccExt v t * iccExt p t - M * iccExt v t = max (iccExt p t - M) 0 * (iccExt p t - M) := by
        simp only [v, SturmLiouville.iccExt, ContinuousMap.coe_mk]; ring
      rw [this]
      rcases le_total (iccExt p t - M) 0 with h' | h'
      · rw [max_eq_right h']; simp
      · rw [max_eq_left h']; positivity) hv
  intro t
  have := hz t t.2
  have e : iccExt v t * iccExt p t - M * iccExt v t = max (p t - M) 0 * (p t - M) := by
    simp only [v, SturmLiouville.iccExt, ContinuousMap.coe_mk, projIcc_of_mem _ t.2]; ring
  rw [e] at this
  by_contra hc; push Not at hc
  have : 0 < max (p t - M) 0 * (p t - M) := by
    rw [max_eq_left (by linarith)]; nlinarith
  linarith

/-- A continuous `p` with `∫ v p ≥ 0` for all `v ≥ 0` is nonnegative. -/
lemma pot_nonneg_of_int {p : C01}
    (h : ∀ v : C01, (∀ t, 0 ≤ v t) → 0 ≤ ∫ t, iccExt v t * iccExt p t ∂vol01) : ∀ t, 0 ≤ p t := by
  have h' := pot_le_of_int (p := -p) (M := 0) fun v hv => by
    have := h v hv
    have e : ∫ t, iccExt v t * iccExt (-p) t ∂vol01 = -∫ t, iccExt v t * iccExt p t ∂vol01 := by
      rw [← integral_neg]; congr 1; funext t; simp [SturmLiouville.iccExt]
    rw [e, zero_mul]; linarith
  intro t; have := h' t; simp at this; linarith

lemma integral_LN (v : C01) : ∫ x, LN n v x ∂μN n = (n + 1) * ∫ t, iccExt v t ∂vol01 := by
  have := integral_LN_mul (n := n) v (F := fun _ => 1) continuous_const
  simp only [mul_one] at this
  rw [this]
  have hk : ∀ k : Fin (n + 1), ∫ x, iccExt v (x k) ∂μN n = ∫ t, iccExt v t ∂vol01 := fun k => by
    have e : (fun x : Cfg n => iccExt v (x k)) = fun x =>
        ∏ i, (if i = k then iccExt v else fun _ => (1 : ℝ)) (x i) := by
      funext x
      rw [Finset.prod_eq_single k (fun i _ hi => by simp [hi])
        (fun h => absurd (Finset.mem_univ k) h)]
      simp
    rw [e, integral_prod_cube]
    rw [Finset.prod_eq_single k (fun i _ hi => by simp [hi])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- A continuous `p` with the integrals of `F`, `0 ≤ F ≤ M`, has `‖p‖ ≤ N M`. -/
lemma norm_pot_le_of_int {p : C01} {F : Cfg n → ℝ} (hFi : Integrable F (μN n)) {M : ℝ}
    (hM : 0 ≤ M) (h0 : ∀ᵐ x ∂μN n, 0 ≤ F x) (h1 : ∀ᵐ x ∂μN n, F x ≤ M)
    (hint : ∀ v : C01, ∫ t, iccExt v t * iccExt p t ∂vol01 = ∫ x, LN n v x * F x ∂μN n) :
    ‖p‖ ≤ (n + 1) * M := by
  have hLN : ∀ v : C01, (∀ t, 0 ≤ v t) → ∀ x, 0 ≤ LN n v x := fun v hv x => by
    change 0 ≤ ∑ k, SturmLiouville.iccExt v (x k)
    exact Finset.sum_nonneg fun k _ => hv _
  have iL : ∀ v : C01, Integrable (fun x => LN n v x * F x) (μN n) := fun v => by
    obtain ⟨C, hC⟩ := ae_bound_cont (n := n) (continuous_LN v)
    exact hFi.bdd_mul (continuous_LN v).aestronglyMeasurable hC
  have hupper := pot_le_of_int (p := p) (M := (n + 1) * M) fun v hv => by
    rw [hint]
    calc ∫ x, LN n v x * F x ∂μN n ≤ ∫ x, M * LN n v x ∂μN n := by
          refine integral_mono_ae (iL v) ((integrableN (continuous_LN v)).const_mul M) ?_
          filter_upwards [h1] with x hx
          nlinarith [hLN v hv x]
      _ = (n + 1) * M * ∫ t, iccExt v t ∂vol01 := by rw [integral_const_mul, integral_LN]; ring
  have hlower := pot_nonneg_of_int (p := p) fun v hv => by
    rw [hint]
    exact integral_nonneg_of_ae (by filter_upwards [h0] with x hx; exact mul_nonneg (hLN v hv x) hx)
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hlower t, (by positivity : (0 : ℝ) ≤ (n + 1) * M)], hupper t⟩

/-- If `0 ≤ u φ ≤ M`, then `0 ≤ ρ̂(u, φ) ≤ N M`. -/
lemma norm_rhoHat2_le {w : Cfg n → ℝ} (hw : Continuous w) {τ : Stat} {u φ : Cfg n → ℝ}
    (hu : u ∈ DomW τ n) (hφ : φ ∈ DomW τ n) {M : ℝ} (hM : 0 ≤ M)
    (h0 : ∀ᵐ x ∂μN n, 0 ≤ u x * φ x) (h1 : ∀ᵐ x ∂μN n, u x * φ x ≤ M) :
    ‖rhoHat2 τ u φ‖ ≤ (n + 1) * M :=
  norm_pot_le_of_int (int_mul_L2 hu.1 hφ.1) hM h0 h1 fun v => int_rhoHat2 (w := w) hw hu hφ v

/-! ### The logarithmic data and unique continuation -/

lemma abs_etaS_le_one (x : Cfg n) : |etaS x| ≤ 1 := by
  rw [etaS, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => abs_sin_le_one _

variable {w : Cfg n → ℝ}

/-- A nonnegative bosonic ground state of a measure potential gives the logarithmic data on
`[a, 1 - a]ᴺ`. -/
theorem logData_meas (hw : Continuous w) {ν : PotM} {u : Cfg n → ℝ} (hu : IsGSN .bos w ν u)
    (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    LogData u (Qa n a) := by
  set E := QMN .bos w ν u
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  set K := |E| + max B 0 + ‖ν‖ * (n + 1)
  have hc : 0 < Real.sin (π * a) ^ (n + 1) := pow_pos (Real.sin_pos_of_pos_of_lt_pi
    (by positivity) (by nlinarith [Real.pi_pos])) _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨h1W_of_mem hu.1, hu0, measurableSet_Qa a, Qa_sub_cube ha, convex_Qa a, etaS,
    contDiff_etaS.continuous, _, hc, fun x hx => (etaS_ge ha ha2 hx).trans (le_abs_self _),
    4 * ∑ k, ∫ x, dk k etaS x ^ 2 ∂μN n + 2 * K, ?_, fun ε hε => ?_⟩
  · have : 0 ≤ ∑ k, ∫ x, dk k (etaS (n := n)) x ^ 2 ∂μN n :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
    positivity
  refine log_estimate_core (h1W_of_mem hu.1) hu0 contDiff_etaS etaS_wall hε ?_
  -- the test function and the Euler–Lagrange equation
  set φ := logTest etaS u ε
  have hφD : φ ∈ DomW .bos n := by
    refine ⟨(h1W_logTest (h1W_of_mem hu.1) contDiff_etaS etaS_wall hε).1,
      (h1W_logTest (h1W_of_mem hu.1) contDiff_etaS etaS_wall hε).2, fun σ _ => ?_⟩
    filter_upwards [hu.1.2.2 σ trivial] with x hx
    simp only [ch_bos, one_mul] at hx ⊢
    simp only [φ, logTest, etaS_pm, hx]
  have hel := euler_lagrangeN hw hu hφD
  rw [h0W] at hel
  -- `0 ≤ u φ ≤ η² ≤ 1`
  have hb : ∀ᵐ x ∂μN n, 0 ≤ u x * φ x ∧ u x * φ x ≤ etaS x ^ 2 := by
    filter_upwards [hu0] with x h0
    have hp : 0 < u x + ε := by linarith
    have hφx : φ x = etaS x * etaS x / (u x + ε) := by
      simp only [φ, logTest, Gr_of_nonneg h0]
      field_simp; ring
    constructor
    · rw [hφx]; exact mul_nonneg h0 (div_nonneg (mul_self_nonneg _) hp.le)
    · rw [hφx, mul_div_assoc', div_le_iff₀ hp]
      nlinarith [mul_self_nonneg (etaS x)]
  have hb1 : ∀ᵐ x ∂μN n, 0 ≤ u x * φ x ∧ u x * φ x ≤ 1 := by
    filter_upwards [hb] with x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    have := abs_etaS_le_one x
    rw [← sq_abs]; nlinarith [abs_nonneg (etaS x)]
  have iuφ := int_mul_L2 hu.1.1 hφD.1
  have hI : 0 ≤ ∫ x, u x * φ x ∂μN n ∧ ∫ x, u x * φ x ∂μN n ≤ 1 := by
    refine ⟨integral_nonneg_of_ae (hb1.mono fun x hx => hx.1), ?_⟩
    calc ∫ x, u x * φ x ∂μN n ≤ ∫ _x, (1 : ℝ) ∂μN n :=
          integral_mono_ae iuφ (integrable_const _) (hb1.mono fun x hx => hx.2)
      _ = 1 := by simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ, volume_cube]
  have hW : |∫ x, w x * (u x * φ x) ∂μN n| ≤ max B 0 := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, w x * (u x * φ x) ∂μN n‖ ≤ ∫ x, max B 0 * (u x * φ x) ∂μN n := by
          refine norm_integral_le_of_norm_le (iuφ.const_mul _) ?_
          filter_upwards [hB, hb1] with x hx hx'
          rw [norm_mul, Real.norm_eq_abs (u x * φ x), abs_of_nonneg hx'.1]
          exact mul_le_mul_of_nonneg_right (hx.trans (le_max_left _ _)) hx'.1
      _ = max B 0 * ∫ x, u x * φ x ∂μN n := integral_const_mul _ _
      _ ≤ max B 0 * 1 := mul_le_mul_of_nonneg_left hI.2 (le_max_right _ _)
      _ = max B 0 := mul_one _
  have hN := norm_rhoHat2_le hw hu.1 hφD zero_le_one (hb1.mono fun x hx => hx.1)
    (hb1.mono fun x hx => hx.2)
  have hν : |ν (rhoHat2 .bos u φ)| ≤ ‖ν‖ * (n + 1) := by
    have := ν.le_opNorm (rhoHat2 .bos u φ)
    rw [Real.norm_eq_abs] at this
    calc |ν (rhoHat2 .bos u φ)| ≤ ‖ν‖ * ‖rhoHat2 .bos u φ‖ := this
      _ ≤ ‖ν‖ * ((n + 1) * 1) := mul_le_mul_of_nonneg_left hN (norm_nonneg ν)
      _ = ‖ν‖ * (n + 1) := by ring
  have hE : |E * ∫ x, u x * φ x ∂μN n| ≤ |E| := by
    rw [abs_mul, abs_of_nonneg hI.1]
    calc |E| * ∫ x, u x * φ x ∂μN n ≤ |E| * 1 := mul_le_mul_of_nonneg_left hI.2 (abs_nonneg _)
      _ = |E| := mul_one _
  simp only [K]
  linarith [neg_abs_le (E * ∫ x, u x * φ x ∂μN n), le_abs_self (∫ x, w x * (u x * φ x) ∂μN n),
    le_abs_self (ν (rhoHat2 .bos u φ))]

/-- **Bosonic ground states of measure potentials are nonzero almost everywhere.** -/
theorem gsN_ne_zero_bos (hw : Continuous w) {ν : PotM} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSN .bos w ν Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  set u : Cfg n → ℝ := fun x => |Ψ x|
  have hu : IsGSN .bos w ν u := isGSN_abs hw hΨ
  have hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x := ae_of_all _ fun x => abs_nonneg _
  have hum := hu.1.1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  set Z : Set (Cfg n) := {x | u' x = 0}
  have hZ : MeasurableSet Z := hu'm (measurableSet_singleton 0)
  have hv : ∀ᵐ x ∂volume, x ∈ Cube n → u x = u' x := (ae_restrict_iff' measurableSet_cube).1 hue
  have hinv : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ k (h : ℝ), 0 ≤ h →
      ∀ᵐ x ∂volume, x ∈ Sa n a h k → (x ∈ Z ↔ x + h • ek k ∈ Z) := by
    intro a ha ha2 k h hh
    have hQc := Qa_sub_cube (n := n) ha
    have hv' := (measurePreserving_add_right volume (h • ek k)).quasiMeasurePreserving.ae hv
    filter_upwards [(logData_meas hw hu hu0 ha ha2).zero_set_translate k hh, hv, hv']
      with x hx h1 h2 hxS
    simp only [Z, mem_ofPred_eq]
    rw [← h1 (hQc hxS.1), ← h2 (hQc hxS.2)]
    exact hx hxS
  rcases null_or_conull hZ hinv with h | h
  · exfalso
    have hz : ∀ᵐ x ∂μN n, u x ^ 2 = 0 := by
      filter_upwards [h, hue] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rw [he, hx]; ring
    have : ∫ x, u x ^ 2 ∂μN n = 0 := integral_eq_zero_of_ae hz
    rw [hu.2.1] at this; exact one_ne_zero this
  · filter_upwards [h, hue] with x hx he
    simp only [Z, mem_ofPred_eq] at hx
    rw [← he] at hx
    exact abs_ne_zero.1 hx

end DFT.Continuum.Line
