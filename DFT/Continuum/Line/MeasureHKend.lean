/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasureHKgen
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Hohenberg–Kohn for interacting particles in measure potentials

Steps (E)–(H) of the argument in the formalization log. Let `Φ` be a common normalised ground state
of the measure potentials `ν` and `ν'`, `D = ν - ν' - c dx` with `c` chosen so that `D` annihilates
every mixed density `ρ̂(Φ, Ψ)` (Euler–Lagrange).

* (E) `D_rhoHat_ac`: `D(f ρ̂) = -∫ f R` for continuous `f`, with `R ∈ L¹` (`exists_pair_density`,
  then Weierstrass polynomials times a smooth cutoff).
* (F) `D_eq_integral`: `D(q) = ∫ q e`, `e = -R/ρ̂`, for `q` vanishing outside `[a, 1 - a]`
  (`ρ̂ > 0` inside, `rhoHat_pos_gs`).
* (G) `integrable_x0_sq` (Tonelli on the cube), `int_rhoHat2_L1` (mixed densities against `L¹`
  weights), `rhoHat2_vanish`, `sum_ae_zero` (symmetrised tests and the fundamental lemma give
  `Σₖ e(xₖ) Φ² = 0` a.e.), `product_identity` (product tests give `∫ φ e + n ∫ φ ∫ η e = 0`).
* (H) `D_vanish`, `D_vanish_walls`; **`hk_meas_N`**: two measure potentials with a common ground
  state differ by `C dx + a δ₀ + b δ₁`; **`hk_meas_N_dens`**: the same if they only have ground
  states with the same density. This is the Hohenberg–Kohn theorem for `N` interacting bosons or
  fermions (continuous interaction) in measure potentials on a line.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-! ### `intCLM` is additive in the measure -/

lemma intCLM_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    intCLM (μ + ν) = intCLM μ + intCLM ν := by
  ext h
  simp only [intCLM_apply, add_apply]
  exact integral_add_measure (integrable_ext μ h) (integrable_ext ν h)

/-! ### The pair density for every `N` -/

lemma TG_zero {w0 : Cfg 0 → ℝ} (hw : Continuous w0) {Φ : Cfg 0 → ℝ} (hΦ : Φ ∈ DomW τ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) : TG τ Φ hf.continuous = 0 := by
  have hfc := hf.continuous
  rw [TG, sub_eq_zero]
  refine pot_eq_of_integral fun v => ?_
  rw [int_rhoHat2 hw hΦ (mem_FF_mul hΦ hf)]
  have e : ∀ t, ext v t * ext (fP hfc * rhoHat τ Φ) t = ext (v * fP hfc) t * ext (rhoHat τ Φ) t :=
    fun t => by simp only [Box.ext, ContinuousMap.mul_apply]; ring
  simp only [e]
  rw [int_rhoHat hw hΦ]
  simp only [pf]
  refine integral_congr_ae ?_
  filter_upwards [ae_cube_x0] with x hx
  change LN 0 v x * (Φ x * (FF f x * Φ x)) = LN 0 (v * fP hfc) x * (Φ x * Φ x)
  simp only [LN, LinearMap.coe_mk, AddHom.coe_mk, FF, Box.ext, ContinuousMap.mul_apply,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [show (fP hfc) (projIcc 0 1 zero_le_one (x 0)) = f (x 0) by simp [fP, projIcc_of_mem _ hx]]
  ring

/-- The pair density against a measure, for every `N`. -/
theorem exists_pair_density' (hw : Continuous w) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    (ρ : Measure ℝ) [IsMeas01 ρ] :
    ∃ R : ℝ → ℝ, Integrable R μ1 ∧ ∀ (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (Cf Cd : ℝ),
      (∀ t, |f t| ≤ Cf) → (∀ t, |deriv f t| ≤ Cd) →
        intCLM ρ (TG τ Φ hf.continuous) = ∫ u, f u * R u ∂μ1 := by
  cases n with
  | zero =>
    refine ⟨0, integrable_zero _ _ _, fun f hf _ _ _ _ => ?_⟩
    rw [TG_zero hw hΦ hf, map_zero]; simp
  | succ m => exact exists_pair_density hw hΦ ρ

/-! ### (E) The Euler–Lagrange identities -/

section E

variable {μp μm μp' μm' : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] [IsMeas01 μp'] [IsMeas01 μm']

lemma intCLM_mu1_rhoHat2 (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    (hΨ : Ψ ∈ DomW τ n) :
    intCLM μ1 (rhoHat2 τ Φ Ψ) = (n + 1) * ∫ x, Φ x * Ψ x ∂μN n := by
  set one : Pot := ⟨fun _ => 1, continuous_const⟩
  have h := int_rhoHat2 hw hΦ hΨ one
  have h1 : ∫ t, ext one t * ext (rhoHat2 τ Φ Ψ) t ∂μ1 = intCLM μ1 (rhoHat2 τ Φ Ψ) := by
    rw [intCLM_apply]; congr 1; funext t; simp [one, Box.ext]
  rw [h1] at h
  rw [h]
  change ∫ x, LN n one x * (Φ x * Ψ x) ∂μN n = _
  have hL : ∀ x, LN n one x = n + 1 := fun x => by
    simp [LN, one, Box.ext]
  simp only [hL]
  rw [integral_const_mul]

/-- **The difference functional annihilates all mixed densities of the common ground state.** -/
theorem D_rhoHat2 (hw : Continuous w) {Φ : Cfg n → ℝ} (h : IsGSN τ w (nuOf μp μm) Φ)
    (h' : IsGSN τ w (nuOf μp' μm') Φ) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) :
    (nuOf μp μm - nuOf μp' μm' - ((QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) /
      (n + 1)) • intCLM μ1) (rhoHat2 τ Φ Ψ) = 0 := by
  have e1 := euler_lagrangeN hw h hΨ
  have e2 := euler_lagrangeN hw h' hΨ
  rw [sub_apply, sub_apply,
    smul_apply, smul_eq_mul, intCLM_mu1_rhoHat2 hw h.1 hΨ]
  have hN : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

end E

/-! ### A smooth cutoff equal to `1` on `[0, 1]` -/

/-- A smooth bump, `1` on `[0, 1]`, compactly supported. -/
noncomputable def bump01 : ContDiffBump (1 / 2 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

lemma bump01_eq_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : bump01 t = 1 :=
  bump01.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> simp only [bump01] <;> linarith [ht.1, ht.2])

/-- Every polynomial, cut off by `bump01`, is a bounded `C¹` function with bounded derivative. -/
lemma cut_poly (p : Polynomial ℝ) :
    ContDiff ℝ 1 (fun t => bump01 t * p.eval t) ∧ (∃ C, ∀ t, |bump01 t * p.eval t| ≤ C) ∧
      ∃ C, ∀ t, |deriv (fun t => bump01 t * p.eval t) t| ≤ C := by
  have hp : ContDiff ℝ 1 fun t => p.eval t := by simpa using p.contDiff_aeval (𝕜 := ℝ) 1
  have hb : ContDiff ℝ 1 fun t => bump01 t := bump01.contDiff
  have hf := hb.mul hp
  have hcs : HasCompactSupport fun t => bump01 t * p.eval t := bump01.hasCompactSupport.mul_right
  refine ⟨hf, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hcs
    exact ⟨C, fun t => by simpa using hC t⟩
  · obtain ⟨C, hC⟩ := (hf.continuous_deriv le_rfl).bounded_above_of_compact_support hcs.deriv
    exact ⟨C, fun t => by simpa using hC t⟩

/-! ### (E) `D(f ρ̂) = -∫ f R` -/

section E2

variable {μp μm μp' μm' : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] [IsMeas01 μp'] [IsMeas01 μm']

/-- **`D ρ̂` is absolutely continuous**: for a common ground state `Φ`, there is `R ∈ L¹` with
`D(f ρ̂_Φ) = -∫ f R` for every continuous `f`. -/
theorem D_rhoHat_ac (hw : Continuous w) {Φ : Cfg n → ℝ} (h : IsGSN τ w (nuOf μp μm) Φ)
    (h' : IsGSN τ w (nuOf μp' μm') Φ) :
    ∃ R : ℝ → ℝ, Integrable R μ1 ∧ ∀ (g : ℝ → ℝ) (hg : Continuous g),
      (nuOf μp μm - nuOf μp' μm' - ((QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) /
        (n + 1)) • intCLM μ1) (fP hg * rhoHat τ Φ) = -∫ u, g u * R u ∂μ1 := by
  set c := (QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) / (n + 1)
  set D := nuOf μp μm - nuOf μp' μm' - c • intCLM μ1
  obtain ⟨R1, hR1, hR1f⟩ := exists_pair_density' hw h.1 μp
  obtain ⟨R2, hR2, hR2f⟩ := exists_pair_density' hw h.1 μm
  obtain ⟨R3, hR3, hR3f⟩ := exists_pair_density' hw h.1 μp'
  obtain ⟨R4, hR4, hR4f⟩ := exists_pair_density' hw h.1 μm'
  obtain ⟨R5, hR5, hR5f⟩ := exists_pair_density' hw h.1 μ1
  set R : ℝ → ℝ := fun u => R1 u - R2 u - (R3 u - R4 u) - c * R5 u
  have hR : Integrable R μ1 := ((hR1.sub hR2).sub (hR3.sub hR4)).sub (hR5.const_mul c)
  -- the identity for bounded `C¹` functions
  have hnice : ∀ (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (Cf Cd : ℝ), (∀ t, |f t| ≤ Cf) →
      (∀ t, |deriv f t| ≤ Cd) → D (fP hf.continuous * rhoHat τ Φ) = -∫ u, f u * R u ∂μ1 := by
    intro f hf Cf Cd hCf hCd
    have hD0 := D_rhoHat2 hw h h' (mem_FF_mul h.1 hf)
    have e : rhoHat2 τ Φ (fun x => FF f x * Φ x) =
        fP hf.continuous * rhoHat τ Φ + TG τ Φ hf.continuous := by rw [TG]; ring
    rw [e, map_add] at hD0
    have hT : D (TG τ Φ hf.continuous) = ∫ u, f u * R u ∂μ1 := by
      have i : ∀ {Q : ℝ → ℝ}, Integrable Q μ1 → Integrable (fun u => f u * Q u) μ1 := fun hQ =>
        hQ.bdd_mul hf.continuous.aestronglyMeasurable (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs]; exact hCf u)
      simp only [D, nuOf, sub_apply, smul_apply, smul_eq_mul, hR1f f hf Cf Cd hCf hCd,
        hR2f f hf Cf Cd hCf hCd, hR3f f hf Cf Cd hCf hCd, hR4f f hf Cf Cd hCf hCd,
        hR5f f hf Cf Cd hCf hCd]
      have e : (fun u => f u * R u) = fun u => ((f u * R1 u - f u * R2 u) -
          (f u * R3 u - f u * R4 u)) - c * (f u * R5 u) := funext fun u => by simp only [R]; ring
      have h12 : Integrable (fun u => f u * R1 u - f u * R2 u) μ1 := (i hR1).sub (i hR2)
      have h34 : Integrable (fun u => f u * R3 u - f u * R4 u) μ1 := (i hR3).sub (i hR4)
      have h1234 : Integrable (fun u => (f u * R1 u - f u * R2 u) -
          (f u * R3 u - f u * R4 u)) μ1 := h12.sub h34
      have h5 : Integrable (fun u => c * (f u * R5 u)) μ1 := (i hR5).const_mul c
      rw [e, integral_sub h1234 h5, integral_sub h12 h34, integral_sub (i hR1) (i hR2),
        integral_sub (i hR3) (i hR4), integral_const_mul]
    linarith
  refine ⟨R, hR, fun g hg => ?_⟩
  -- approximate `g` on `[0, 1]` by cut-off polynomials
  have happ : ∀ k : ℕ, ∃ p : Polynomial ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      |p.eval t - g t| < 1 / ((k : ℝ) + 1) := fun k =>
    exists_polynomial_near_of_continuousOn 0 1 g hg.continuousOn _ (by positivity)
  choose p hp using happ
  have hcut := fun k => cut_poly (p k)
  set f : ℕ → ℝ → ℝ := fun k t => bump01 t * (p k).eval t
  have hfI : ∀ k t, t ∈ Icc (0 : ℝ) 1 → f k t = (p k).eval t := fun k t ht => by
    simp only [f, bump01_eq_one ht, one_mul]
  have hk : ∀ k, D (fP (hcut k).1.continuous * rhoHat τ Φ) = -∫ u, f k u * R u ∂μ1 := fun k => by
    obtain ⟨hf, ⟨Cf, hCf⟩, ⟨Cd, hCd⟩⟩ := hcut k
    exact hnice _ hf Cf Cd hCf hCd
  have hclose : ∀ k, ‖fP (hcut k).1.continuous - fP hg‖ ≤ 1 / ((k : ℝ) + 1) := fun k =>
    (ContinuousMap.norm_le _ (by positivity)).2 fun t => by
      simp only [ContinuousMap.sub_apply, fP, ContinuousMap.coe_mk, Real.norm_eq_abs]
      rw [bump01_eq_one t.2, one_mul]; exact (hp k t t.2).le
  have hzero : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hL : Tendsto (fun k => D (fP (hcut k).1.continuous * rhoHat τ Φ)) atTop
      (𝓝 (D (fP hg * rhoHat τ Φ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (by simpa using (hzero.const_mul (‖D‖ * ‖rhoHat τ Φ‖)))
    rw [← map_sub, ← sub_mul]
    refine (D.le_opNorm _).trans ?_
    calc ‖D‖ * ‖(fP (hcut k).1.continuous - fP hg) * rhoHat τ Φ‖
        ≤ ‖D‖ * (‖fP (hcut k).1.continuous - fP hg‖ * ‖rhoHat τ Φ‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg D)
      _ ≤ ‖D‖ * (1 / ((k : ℝ) + 1) * ‖rhoHat τ Φ‖) := by
          gcongr; exact hclose k
      _ = ‖D‖ * ‖rhoHat τ Φ‖ * ((k : ℝ) + 1)⁻¹ := by ring
  have hRk : Tendsto (fun k => -∫ u, f k u * R u ∂μ1) atTop (𝓝 (-∫ u, g u * R u ∂μ1)) := by
    refine Tendsto.neg ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (by simpa using hzero.mul_const (∫ u, |R u| ∂μ1))
    obtain ⟨hf, ⟨Cf, hCf⟩, -⟩ := hcut k
    have i1 : Integrable (fun u => f k u * R u) μ1 := hR.bdd_mul hf.continuous.aestronglyMeasurable
      (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hCf u)
    obtain ⟨Cg, hCg⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hg.continuousOn
    have i2 : Integrable (fun u => g u * R u) μ1 := hR.bdd_mul hg.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hCg u (Ioo_subset_Icc_self hu))
    rw [← integral_sub i1 i2, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae (i1.sub i2).norm
      (hR.abs.const_mul _) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul, hfI k u (Ioo_subset_Icc_self hu), mul_comm]
    have := mul_le_mul_of_nonneg_left (hp k u (Ioo_subset_Icc_self hu)).le (abs_nonneg (R u))
    rw [one_div] at this; linarith [mul_comm (|R u|) (((k : ℝ) + 1)⁻¹)]
  exact tendsto_nhds_unique (hL.congr hk) hRk

end E2

/-! ### (F) Dividing by the density -/

lemma rhoHat_pos_gs (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN τ w ν Φ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < ext (rhoHat τ Φ) t := by
  cases τ with
  | bos => exact rhoHat_pos_bos hw h ht
  | fer => exact rhoHat_pos_fer hw h ht

lemma fP_ext (h : Pot) : fP (continuous_ext h) = h := by
  ext t; simp [fP, Box.ext]

/-- `ρ̂ ≥ c > 0` on `[a, 1 - a]`. -/
lemma exists_rhoHat_ge (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN τ w ν Φ)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    ∃ c > 0, ∀ t ∈ Icc a (1 - a), c ≤ ext (rhoHat τ Φ) t := by
  obtain ⟨t0, ht0, hmin⟩ := (isCompact_Icc : IsCompact (Icc a (1 - a))).exists_isMinOn
    ⟨a, le_rfl, by linarith⟩ (continuous_ext (rhoHat τ Φ)).continuousOn
  exact ⟨_, rhoHat_pos_gs hw h ⟨by linarith [ht0.1], by linarith [ht0.2]⟩, fun t ht => hmin ht⟩

/-- **`D` on functions vanishing near the walls**: `D(h) = -∫ h R / ρ̂`. -/
theorem D_eq_integral (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN τ w ν Φ)
    {D : PotM} {R : ℝ → ℝ}
    (hD : ∀ (g : ℝ → ℝ) (hg : Continuous g), D (fP hg * rhoHat τ Φ) = -∫ u, g u * R u ∂μ1)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {q : Pot}
    (hq : ∀ t : Icc (0 : ℝ) 1, (t : ℝ) ∉ Icc a (1 - a) → q t = 0) :
    D q = ∫ u, ext q u * (-R u / ext (rhoHat τ Φ) u) ∂μ1 := by
  obtain ⟨c, hc, hcle⟩ := exists_rhoHat_ge hw h ha ha2
  set ρ := ext (rhoHat τ Φ)
  have hρc := continuous_ext (rhoHat τ Φ)
  set g : ℝ → ℝ := fun t => ext q t / max (ρ t) c
  have hg : Continuous g := (continuous_ext q).div (hρc.max continuous_const)
    fun t => (lt_max_of_lt_right hc).ne'
  have hq0 : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ Icc a (1 - a) → ext q t = 0 := fun t ht htn => by
    simp only [Box.ext, projIcc_of_mem _ ht]; exact hq ⟨t, ht⟩ htn
  have hmul : fP hg * rhoHat τ Φ = q := by
    ext t
    have htI := t.2
    simp only [ContinuousMap.mul_apply, fP, ContinuousMap.coe_mk, g]
    have hρt : ρ t = rhoHat τ Φ t := by simp [ρ, Box.ext, projIcc_of_mem _ htI]
    have hqt : ext q t = q t := by simp [Box.ext, projIcc_of_mem _ htI]
    by_cases hin : (t : ℝ) ∈ Icc a (1 - a)
    · rw [max_eq_left (hcle t hin), hqt, hρt, div_mul_cancel₀]
      exact (hc.trans_le (hρt ▸ hcle t hin)).ne'
    · rw [hq0 t htI hin, zero_div, zero_mul, hq t hin]
  conv_lhs => rw [← hmul]
  rw [hD g hg, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have huI := Ioo_subset_Icc_self hu
  by_cases hin : u ∈ Icc a (1 - a)
  · simp only [g, max_eq_left (hcle u hin)]; ring
  · simp only [g, hq0 u huI hin, zero_div, zero_mul, neg_zero]

/-! ### (G1) Weights in `L¹` -/

/-- The converse of `integrable_cons_prod`. -/
lemma integrable_of_cons_prod {F : Cfg n → ℝ}
    (hF : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Cube' n)))) :
    Integrable F (μN n) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Cfg n)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hcomp : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth 0 p.1 p.2 := by
    rintro ⟨t, y⟩; rfl
  have hpre : e.symm ⁻¹' Cube n = Ioo (0 : ℝ) 1 ×ˢ Cube' n := by
    ext ⟨t, y⟩
    simp only [mem_preimage, hcomp, mem_prod]
    exact insertNth_mem_cube 0 t y
  have hr := he.restrict_preimage_emb e.symm.measurableEmbedding (Cube n)
  rw [hpre, ← Measure.prod_restrict] at hr
  refine (hr.integrable_comp_emb e.symm.measurableEmbedding).1 ?_
  simpa [Function.comp_def, hcomp, Fin.insertNth_zero'] using hF

/-- **Tonelli on the cube**: for `u ∈ L¹(0, 1)`, `u(x₀) Φ²` is integrable and
`∫ |u(x₀)| Φ² ≤ ‖ρ̂‖ / N ∫ |u|`. -/
theorem integrable_x0_sq {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) {u : ℝ → ℝ}
    (hu : Integrable u μ1) :
    Integrable (fun x => u (x 0) * Φ x ^ 2) (μN n) ∧
      ∫ x, |u (x 0)| * Φ x ^ 2 ∂μN n ≤ ‖rhoHat τ Φ‖ / (n + 1) * ∫ t, |u t| ∂μ1 := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hΦ2 := integrable_cons_prod (int_sq hΦ.1)
  have hslice := hΦ2.prod_right_ae
  -- the slice integrals are the marginal, bounded by `‖ρ̂‖ / N`
  have hmarg : ∀ᵐ t ∂μ1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 ≤ ‖rhoHat τ Φ‖ / (n + 1) := by
    filter_upwards [ae_ext_rhoHat hΦ, ae_restrict_mem measurableSet_Ioo] with t h1 ht
    have hb : ext (rhoHat τ Φ) t ≤ ‖rhoHat τ Φ‖ := (le_abs_self _).trans (ext_le_norm _ _)
    rw [h1] at hb
    rw [le_div_iff₀ hN]
    simp only [rhoN, marg] at hb
    linarith
  have hGm : AEStronglyMeasurable (fun p : ℝ × (Fin n → ℝ) => u p.1 * Φ (Fin.cons p.1 p.2) ^ 2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Cube' n))) :=
    (hu.1.comp_fst (ν := volume.restrict (Cube' n))).mul hΦ2.1
  have hG : Integrable (fun p : ℝ × (Fin n → ℝ) => u p.1 * Φ (Fin.cons p.1 p.2) ^ 2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Cube' n))) := by
    rw [integrable_prod_iff hGm]
    refine ⟨hslice.mono fun t ht => ht.const_mul (u t), ?_⟩
    refine ((hu.norm.mul_const (‖rhoHat τ Φ‖ / (n + 1)))).mono' hGm.norm.integral_prod_right' ?_
    filter_upwards [hmarg] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hI : Integrable (fun x => u (x 0) * Φ x ^ 2) (μN n) :=
    integrable_of_cons_prod (F := fun x => u (x 0) * Φ x ^ 2) (by simpa using hG)
  refine ⟨hI, ?_⟩
  have hIa : Integrable (fun x => |u (x 0)| * Φ x ^ 2) (μN n) :=
    hI.norm.congr (ae_of_all _ fun x => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Φ x))])
  rw [integral_cube_cons' hIa]
  simp only [Fin.cons_zero]
  rw [← integral_const_mul]
  refine integral_mono_ae ?_ ((hu.abs.const_mul _)) ?_
  · exact (integrable_cons_prod hIa).integral_prod_left.congr (ae_of_all _ fun t => by
      simp only [Fin.cons_zero])
  · filter_upwards [hmarg] with t ht
    rw [integral_const_mul, mul_comm (‖rhoHat τ Φ‖ / (n + 1))]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)

lemma integral_xk_ae {G : Cfg n → ℝ} (hG : ∀ σ, ∀ᵐ x ∂μN n, G (pm σ x) = G x) (g : ℝ → ℝ)
    (k : Fin (n + 1)) : ∫ x, g (x k) * G x ∂μN n = ∫ x, g (x 0) * G x ∂μN n := by
  rw [← integral_pm (Equiv.swap 0 k) (fun x => g (x 0) * G x)]
  refine integral_congr_ae ?_
  filter_upwards [hG (Equiv.swap 0 k)] with x hx
  simp only [pm_apply, Equiv.swap_apply_left, hx]

lemma mem_mul_sym {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) {χ : Cfg n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχs : ∀ σ x, χ (pm σ x) = χ x) : (fun x => χ x * Φ x) ∈ DomW τ n := by
  refine ⟨memLp_mul_cont hχ.continuous hΦ.1, fun k => ⟨_, (dW_spec (hΦ.2.1 k)).mul_C1 hΦ.1 hχ⟩,
    fun σ _ => ?_⟩
  filter_upwards [hΦ.2.2 σ trivial] with x hx
  simp only [hχs, hx]; ring

lemma sq_sym_ae {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) {χ : Cfg n → ℝ}
    (hχs : ∀ σ x, χ (pm σ x) = χ x) (σ : Equiv.Perm (Fin (n + 1))) :
    ∀ᵐ x ∂μN n, χ (pm σ x) * Φ (pm σ x) ^ 2 = χ x * Φ x ^ 2 := by
  filter_upwards [hΦ.2.2 σ trivial] with x hx
  rw [hχs, hx, mul_pow, sq (ch τ σ), ch_mul_self, one_mul]

/-- **The mixed density against an `L¹` weight**:
`∫ e ρ̂(Φ, χΦ) = N ∫ e(x₀) χ Φ²` for a bounded symmetric `C¹` function `χ`. -/
theorem int_rhoHat2_L1 (hw : Continuous w) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    {χ : Cfg n → ℝ} (hχ : ContDiff ℝ 1 χ) {Cχ : ℝ} (hχb : ∀ x, |χ x| ≤ Cχ)
    (hχs : ∀ σ x, χ (pm σ x) = χ x) {e : ℝ → ℝ} (he : Integrable e μ1) :
    ∫ t, e t * ext (rhoHat2 τ Φ (fun x => χ x * Φ x)) t ∂μ1 =
      (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hCχ : 0 ≤ Cχ := (abs_nonneg _).trans (hχb 0)
  have hχΦ := mem_mul_sym hΦ hχ hχs
  set p := rhoHat2 τ Φ (fun x => χ x * Φ x)
  have hG := sq_sym_ae hΦ hχs
  -- integrability of `u(x₀) χ Φ²` for `u ∈ L¹`
  have hint : ∀ {u : ℝ → ℝ}, Integrable u μ1 → Integrable (fun x => u (x 0) * (χ x * Φ x ^ 2))
      (μN n) := fun {u} hu => by
    have := (integrable_x0_sq hΦ hu).1.bdd_mul (c := Cχ) hχ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hχb x)
    exact this.congr (ae_of_all _ fun x => by ring)
  -- the identity for continuous compactly supported weights
  have hcont : ∀ (v : ℝ → ℝ), Continuous v → HasCompactSupport v →
      ∫ t, v t * ext p t ∂μ1 = (n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n := by
    intro v hv hvs
    obtain ⟨Cv, hCv⟩ := hv.bounded_above_of_compact_support hvs
    have h1 : ∫ t, v t * ext p t ∂μ1 = ∫ t, ext (fP hv) t * ext p t ∂μ1 :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [ext_fP hv (Ioo_subset_Icc_self ht)])
    rw [h1, int_rhoHat2 hw hΦ hχΦ]
    change ∫ x, LN n (fP hv) x * (Φ x * (χ x * Φ x)) ∂μN n = _
    have hGi : Integrable (fun x => χ x * Φ x ^ 2) (μN n) :=
      (int_sq hΦ.1).bdd_mul hχ.continuous.aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact hχb x)
    have hb : ∀ t, ‖ext (fP hv) t‖ ≤ ‖fP hv‖ := fun t => by
      rw [Real.norm_eq_abs]; exact ext_le_norm _ _
    have hk : ∀ k : Fin (n + 1), Integrable (fun x => ext (fP hv) (x k) * (χ x * Φ x ^ 2))
        (μN n) := fun k =>
      hGi.bdd_mul ((continuous_ext _).comp (continuous_apply k)).aestronglyMeasurable
        (ae_of_all _ fun x => hb _)
    have e1 : (fun x => LN n (fP hv) x * (Φ x * (χ x * Φ x))) =
        fun x => ∑ k, ext (fP hv) (x k) * (χ x * Φ x ^ 2) := by
      funext x
      change (∑ k, ext (fP hv) (x k)) * _ = _
      rw [Finset.sum_mul]; congr 1; funext k; ring
    rw [e1, integral_finsetSum _ fun k _ => hk k]
    simp only [integral_xk_ae (G := fun x => χ x * Φ x ^ 2) hG (ext (fP hv)), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_cube_x0] with x hx
    rw [ext_fP hv hx]
  -- approximation of `L¹` weights
  have hpb : ∀ t, |ext p t| ≤ ‖p‖ := fun t => ext_le_norm _ _
  have hint1 : ∀ {u : ℝ → ℝ}, Integrable u μ1 → Integrable (fun t => u t * ext p t) μ1 :=
    fun hu => (hu.bdd_mul (c := ‖p‖) (continuous_ext p).aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hpb t)).congr
        (ae_of_all _ fun t => by ring)
  set K := ‖p‖ + Cχ * ‖rhoHat τ Φ‖
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ j : ℕ, |∫ t, e t * ext p t ∂μ1 -
      (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n| ≤ K * (1 / ((j : ℝ) + 1)) := by
    intro j
    obtain ⟨v, hvs, hvl, hvc, hvi⟩ := Integrable.exists_hasCompactSupport_integral_sub_le he
      (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))
    have hev : Integrable (fun t => e t - v t) μ1 := he.sub hvi
    have hl : |∫ t, e t * ext p t ∂μ1 - ∫ t, v t * ext p t ∂μ1| ≤ ‖p‖ * (1 / ((j : ℝ) + 1)) := by
      rw [← integral_sub (hint1 he) (hint1 hvi)]
      calc |∫ t, (e t * ext p t - v t * ext p t) ∂μ1| ≤ ∫ t, ‖p‖ * ‖e t - v t‖ ∂μ1 := by
            rw [← Real.norm_eq_abs]
            refine norm_integral_le_of_norm_le (hev.norm.const_mul _) (ae_of_all _ fun t => ?_)
            rw [← sub_mul, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (hpb t) (abs_nonneg _)
        _ ≤ ‖p‖ * (1 / ((j : ℝ) + 1)) := by
            rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hvl (norm_nonneg _)
    have hr : |(n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n -
        (n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n| ≤
          Cχ * ‖rhoHat τ Φ‖ * (1 / ((j : ℝ) + 1)) := by
      rw [← mul_sub, ← integral_sub (hint he) (hint hvi), abs_mul, abs_of_pos hN]
      have hT := (integrable_x0_sq hΦ hev).2
      have hbd : |∫ x, (e (x 0) * (χ x * Φ x ^ 2) - v (x 0) * (χ x * Φ x ^ 2)) ∂μN n| ≤
          Cχ * ∫ x, |e (x 0) - v (x 0)| * Φ x ^ 2 ∂μN n := by
        rw [← Real.norm_eq_abs, ← integral_const_mul]
        refine norm_integral_le_of_norm_le (((integrable_x0_sq hΦ hev).1.norm).const_mul Cχ
          |>.congr (ae_of_all _ fun x => by
            simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Φ x))])) ?_
        refine ae_of_all _ fun x => ?_
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
        nlinarith [hχb x, abs_nonneg (e (x 0) - v (x 0)), sq_nonneg (Φ x), abs_nonneg (χ x),
          mul_nonneg (abs_nonneg (e (x 0) - v (x 0))) (sq_nonneg (Φ x))]
      calc (n + 1) * |∫ x, (e (x 0) * (χ x * Φ x ^ 2) - v (x 0) * (χ x * Φ x ^ 2)) ∂μN n|
          ≤ (n + 1) * (Cχ * (‖rhoHat τ Φ‖ / (n + 1) * ∫ t, |e t - v t| ∂μ1)) :=
            mul_le_mul_of_nonneg_left (hbd.trans (mul_le_mul_of_nonneg_left hT hCχ)) hN.le
        _ = Cχ * ‖rhoHat τ Φ‖ * ∫ t, ‖e t - v t‖ ∂μ1 := by
            simp only [Real.norm_eq_abs]; field_simp
        _ ≤ Cχ * ‖rhoHat τ Φ‖ * (1 / ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hvl (by positivity)
    rw [hcont v hvc hvs] at hl
    calc _ ≤ |∫ t, e t * ext p t ∂μ1 - (n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n| +
          |(n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n -
            (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n| := abs_sub_le _ _ _
      _ ≤ ‖p‖ * (1 / ((j : ℝ) + 1)) + Cχ * ‖rhoHat τ Φ‖ * (1 / ((j : ℝ) + 1)) := by
          rw [abs_sub_comm ((n + 1) * ∫ x, v (x 0) * _ ∂μN n)]; exact add_le_add hl hr
      _ = K * (1 / ((j : ℝ) + 1)) := by simp only [K]; ring
  have hlim : Tendsto (fun j : ℕ => K * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K
  have h0 := ge_of_tendsto' hlim hbound
  have := abs_nonneg (∫ t, e t * ext p t ∂μ1 - (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n)
  linarith [abs_eq_zero.1 (le_antisymm h0 this), sub_eq_zero.1 (abs_eq_zero.1
    (le_antisymm h0 this))]

/-! ### (G2) Localised test states -/

/-- `∫ v ρ̂(Φ, χΦ) = N ∫ v(x₀) χ Φ²` for continuous `v`. -/
lemma int_rhoHat2_sym (hw : Continuous w) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    {χ : Cfg n → ℝ} (hχ : ContDiff ℝ 1 χ) {Cχ : ℝ} (hχb : ∀ x, |χ x| ≤ Cχ)
    (hχs : ∀ σ x, χ (pm σ x) = χ x) (v : Pot) :
    ∫ t, ext v t * ext (rhoHat2 τ Φ (fun x => χ x * Φ x)) t ∂μ1 =
      (n + 1) * ∫ x, ext v (x 0) * (χ x * Φ x ^ 2) ∂μN n := by
  rw [int_rhoHat2 hw hΦ (mem_mul_sym hΦ hχ hχs)]
  change ∫ x, LN n v x * (Φ x * (χ x * Φ x)) ∂μN n = _
  have hGi : Integrable (fun x => χ x * Φ x ^ 2) (μN n) :=
    (int_sq hΦ.1).bdd_mul hχ.continuous.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hχb x)
  have hk : ∀ k : Fin (n + 1), Integrable (fun x => ext v (x k) * (χ x * Φ x ^ 2)) (μN n) :=
    fun k => hGi.bdd_mul ((continuous_ext _).comp (continuous_apply k)).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact ext_le_norm _ _)
  have e1 : (fun x => LN n v x * (Φ x * (χ x * Φ x))) =
      fun x => ∑ k, ext v (x k) * (χ x * Φ x ^ 2) := by
    funext x
    change (∑ k, ext v (x k)) * _ = _
    rw [Finset.sum_mul]; congr 1; funext k; ring
  rw [e1, integral_finsetSum _ fun k _ => hk k]
  simp only [integral_xk_ae (G := fun x => χ x * Φ x ^ 2) (sq_sym_ae hΦ hχs) (ext v),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- If `χ` vanishes unless all coordinates are in `[a, 1 - a]`, then `ρ̂(Φ, χΦ)` vanishes outside
`[a, 1 - a]`. -/
lemma rhoHat2_vanish (hw : Continuous w) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    {χ : Cfg n → ℝ} (hχ : ContDiff ℝ 1 χ) {Cχ : ℝ} (hχb : ∀ x, |χ x| ≤ Cχ)
    (hχs : ∀ σ x, χ (pm σ x) = χ x) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ x, χ x ≠ 0 → x 0 ∈ Icc a (1 - a)) (t : Icc (0 : ℝ) 1)
    (ht : (t : ℝ) ∉ Icc a (1 - a)) : rhoHat2 τ Φ (fun x => χ x * Φ x) t = 0 := by
  set p := rhoHat2 τ Φ (fun x => χ x * Φ x)
  set φ : ℝ → ℝ := fun s => max 0 (a - s) + max 0 (s - (1 - a))
  have hφc : Continuous φ := by fun_prop
  have hφ0 : ∀ s ∈ Icc a (1 - a), φ s = 0 := fun s hs => by
    simp only [φ, max_eq_left (by linarith [hs.1] : a - s ≤ 0),
      max_eq_left (by linarith [hs.2] : s - (1 - a) ≤ 0)]; ring
  have hφpos : ∀ s, s ∉ Icc a (1 - a) → 0 < φ s := fun s hs => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    have h1 : a - s ≤ max 0 (a - s) := le_max_right _ _
    have h2 : 0 ≤ max 0 (s - (1 - a)) := le_max_left _ _
    have h3 : s - (1 - a) ≤ max 0 (s - (1 - a)) := le_max_right _ _
    have h4 : 0 ≤ max 0 (a - s) := le_max_left _ _
    simp only [φ]
    rcases hs with h | h <;> linarith
  set v : Pot := ⟨fun s => φ s * p s, (hφc.comp continuous_subtype_val).mul p.continuous⟩
  have hv := int_rhoHat2_sym hw hΦ hχ hχb hχs v
  have hz : ∫ x, ext v (x 0) * (χ x * Φ x ^ 2) ∂μN n = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
    change ext v (x 0) * (χ x * Φ x ^ 2) = 0
    by_cases hx : χ x = 0
    · simp [hx]
    · have h0 := hsupp x hx
      have hI : x 0 ∈ Icc (0 : ℝ) 1 := ⟨ha.trans h0.1, h0.2.trans (by linarith)⟩
      simp only [Box.ext, projIcc_of_mem _ hI, v, ContinuousMap.coe_mk, hφ0 _ h0, zero_mul]
  rw [hz, mul_zero] at hv
  -- `φ p² = 0` on `[0, 1]`
  have hz2 := le_of_int_nonneg_zero (g := fun s => ext v s * ext p s)
    ((continuous_ext v).mul (continuous_ext p)) (fun s => by
      simp only [Box.ext, v, ContinuousMap.coe_mk]
      have := hφpos (projIcc 0 1 zero_le_one s)
      have h0 : 0 ≤ φ (projIcc 0 1 zero_le_one s) := by
        simp only [φ]; positivity
      nlinarith [sq_nonneg (p (projIcc 0 1 zero_le_one s))]) hv.le t t.2
  simp only [Box.ext, projIcc_of_mem _ t.2, v, ContinuousMap.coe_mk] at hz2
  have := hφpos t ht
  have : p t * p t = 0 := by
    have h' : φ t * (p t * p t) = 0 := by rw [← mul_assoc]; simpa using hz2
    rcases mul_eq_zero.1 h' with h | h
    · linarith
    · exact h
  exact mul_self_eq_zero.1 this

/-! ### (G3) The fundamental lemma -/

lemma mp_pm_cube (σ : Equiv.Perm (Fin (n + 1))) : MeasurePreserving (pm σ) (μN n) (μN n) := by
  have h := (mp_pm (n := n) σ).restrict_preimage measurableSet_cube
  have hpre : pm σ ⁻¹' Cube n = Cube n := by ext x; exact pm_mem_cube
  rwa [hpre] at h

lemma integrable_comp_pm {F : Cfg n → ℝ} (hF : Integrable F (μN n)) (σ : Equiv.Perm (Fin (n + 1))) :
    Integrable (fun x => F (pm σ x)) (μN n) := by
  have hme : MeasurableEmbedding (pm σ : Cfg n → Cfg n) := by
    rw [← coe_pmE]; exact (pmE σ).measurableEmbedding
  exact ((mp_pm_cube (n := n) σ).integrable_comp_emb hme (g := F)).2 hF

/-- The open box `(a, 1 - a)ᴺ`. -/
def boxU (n : ℕ) (a : ℝ) : Set (Cfg n) := univ.pi fun _ => Ioo a (1 - a)

lemma isOpen_boxU (a : ℝ) : IsOpen (boxU n a) := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

lemma boxU_sub_cube {a : ℝ} (ha : 0 ≤ a) : boxU n a ⊆ Cube n := fun x hx => fun i _ =>
  ⟨ha.trans_lt (hx i trivial).1, (hx i trivial).2.trans_le (by linarith)⟩

lemma pm_mem_boxU {σ : Equiv.Perm (Fin (n + 1))} {x : Cfg n} {a : ℝ} :
    pm σ x ∈ boxU n a ↔ x ∈ boxU n a := by
  simp only [boxU, Set.mem_pi, mem_univ, true_implies, pm_apply]
  exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

/-- **From symmetric tests to an a.e. statement**: if `∫ e(x₀) χ Φ² = 0` for all smooth
symmetric `χ` supported in the box, then `Σₖ e(xₖ) Φ² = 0` a.e. in the box. -/
theorem sum_ae_zero {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) {e : ℝ → ℝ} (he : Integrable e μ1)
    {a : ℝ} (ha : 0 ≤ a)
    (htest : ∀ χ : Cfg n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ boxU n a →
      (∀ σ x, χ (pm σ x) = χ x) → ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n = 0) :
    ∀ᵐ x ∂(volume : Measure (Cfg n)), x ∈ boxU n a → (∑ k, e (x k)) * Φ x ^ 2 = 0 := by
  set G : Cfg n → ℝ := fun x => (∑ k, e (x k)) * Φ x ^ 2
  have hT := (integrable_x0_sq hΦ he).1
  have hk : ∀ k : Fin (n + 1), Integrable (fun x => e (x k) * Φ x ^ 2) (μN n) := fun k => by
    refine (integrable_comp_pm hT (Equiv.swap 0 k)).congr ?_
    filter_upwards [hΦ.2.2 (Equiv.swap 0 k) trivial] with x hx
    simp only [pm_apply, Equiv.swap_apply_left, hx, mul_pow, sq (ch τ _), ch_mul_self, one_mul]
  have hGi : Integrable G (μN n) :=
    (integrable_finsetSum Finset.univ fun k _ => hk k).congr (ae_of_all _ fun x => by
      simp only [G, Finset.sum_mul])
  have hGs : ∀ σ, ∀ᵐ x ∂μN n, G (pm σ x) = G x := fun σ => by
    filter_upwards [hΦ.2.2 σ trivial] with x hx
    simp only [G, pm_apply, hx, mul_pow, sq (ch τ σ), ch_mul_self, one_mul]
    congr 1
    exact Equiv.sum_comp σ fun k => e (x k)
  have hloc : LocallyIntegrableOn G (boxU n a) volume :=
    IntegrableOn.locallyIntegrableOn
      (hGi.mono_measure (Measure.restrict_mono (boxU_sub_cube ha) le_rfl))
  refine (isOpen_boxU a).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgU => ?_
  obtain ⟨Cg, hCg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hgcube : ∀ x, x ∉ Cube n → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (boxU_sub_cube ha (hgU h))
  have hvol : ∫ x, g x • G x = ∫ x, g x * G x ∂μN n := by
    rw [← integral_indicator measurableSet_cube]
    congr 1; funext x
    by_cases hx : x ∈ Cube n
    · simp [indicator_of_mem hx, smul_eq_mul]
    · simp [indicator_of_notMem hx, hgcube x hx]
  rw [hvol]
  -- the symmetrised test function
  set χ : Cfg n → ℝ := fun x => ∑ σ : Equiv.Perm (Fin (n + 1)), g (pm σ x)
  have hgi : ∀ σ : Equiv.Perm (Fin (n + 1)), Integrable (fun x => g (pm σ x) * G x) (μN n) :=
    fun σ => hGi.bdd_mul ((hg.continuous.comp (continuous_pm σ)).aestronglyMeasurable)
      (ae_of_all _ fun x => hCg _)
  have hsym : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∫ x, g (pm σ x) * G x ∂μN n = ∫ x, g x * G x ∂μN n := fun σ => by
    rw [← integral_pm σ (fun x => g x * G x)]
    refine integral_congr_ae ?_
    filter_upwards [hGs σ] with x hx
    rw [hx]
  have hχG : ∫ x, χ x * G x ∂μN n =
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) * ∫ x, g x * G x ∂μN n := by
    simp only [χ, Finset.sum_mul]
    rw [integral_finsetSum _ fun σ _ => hgi σ]
    simp only [hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hχs : ∀ σ x, χ (pm σ x) = χ x := fun σ x => by
    simp only [χ, ← pm_mul]
    exact Equiv.sum_comp (Equiv.mulLeft σ) fun ρ => g (pm ρ x)
  set pmH : Equiv.Perm (Fin (n + 1)) → (Cfg n ≃ₜ Cfg n) := fun σ =>
    { toFun := pm σ, invFun := pm σ⁻¹, left_inv := pm_inv_pm σ, right_inv := pm_pm_inv σ,
      continuous_toFun := continuous_pm σ, continuous_invFun := continuous_pm σ⁻¹ }
  have hpmc : ∀ σ : Equiv.Perm (Fin (n + 1)), ContDiff ℝ (⊤ : ℕ∞) fun x : Cfg n => pm σ x :=
    fun σ => contDiff_pi.2 fun i => by unfold pm; fun_prop
  have hχc : ContDiff ℝ (⊤ : ℕ∞) χ := ContDiff.sum fun σ _ => hg.comp (hpmc σ)
  set K := ⋃ σ : Equiv.Perm (Fin (n + 1)), pm σ ⁻¹' tsupport g
  have hK : IsClosed K :=
    isClosed_iUnion_of_finite fun σ => (isClosed_tsupport g).preimage (continuous_pm σ)
  have hKc : IsCompact K :=
    isCompact_iUnion fun σ => (pmH σ).isCompact_preimage.2 hgc
  have hχK : tsupport χ ⊆ K := by
    refine closure_minimal (fun x hx => ?_) hK
    by_contra hno
    simp only [K, mem_iUnion, mem_preimage, not_exists] at hno
    exact hx (Finset.sum_eq_zero fun σ _ => image_eq_zero_of_notMem_tsupport (hno σ))
  have hχcs : HasCompactSupport χ := hKc.of_isClosed_subset (isClosed_tsupport χ) hχK
  have hχU : tsupport χ ⊆ boxU n a :=
    hχK.trans (iUnion_subset fun σ x hx => pm_mem_boxU.1 (hgU hx))
  have h0 := htest χ hχc hχcs hχU hχs
  -- `∫ χ G = N ∫ e(x₀) χ Φ²`
  obtain ⟨Cχ, hCχ⟩ := hχc.continuous.bounded_above_of_compact_support hχcs
  have hχk : ∀ k : Fin (n + 1), Integrable (fun x => e (x k) * (χ x * Φ x ^ 2)) (μN n) :=
    fun k => ((hk k).bdd_mul hχc.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => hCχ x)).congr (ae_of_all _ fun x => by ring)
  have hGχ : ∫ x, χ x * G x ∂μN n = (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n := by
    have e1 : (fun x => χ x * G x) = fun x => ∑ k, e (x k) * (χ x * Φ x ^ 2) := by
      funext x; simp only [G, Finset.sum_mul, Finset.mul_sum]; congr 1; funext k; ring
    rw [e1, integral_finsetSum _ fun k _ => hχk k]
    have hs : ∀ σ, ∀ᵐ x ∂μN n, χ (pm σ x) * Φ (pm σ x) ^ 2 = χ x * Φ x ^ 2 :=
      sq_sym_ae hΦ hχs
    simp only [integral_xk_ae (G := fun x => χ x * Φ x ^ 2) hs e, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  rw [h0, mul_zero] at hGχ
  rw [hGχ] at hχG
  have hcard : (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.1 hχG.symm).resolve_left hcard

/-! ### (G4) Product test functions -/

lemma integrable_prod_cube {ψ : Fin (n + 1) → ℝ → ℝ} (hψ : ∀ i, Integrable (ψ i) μ1) :
    Integrable (fun x : Cfg n => ∏ i, ψ i (x i)) (μN n) := by
  rw [Sine.muN_eq]
  exact Integrable.fintype_prod (μ := fun _ : Fin (n + 1) => μ1) hψ

lemma integrable_cont_vanish {φ : ℝ → ℝ} (hφ : Continuous φ) {a : ℝ}
    (hφ0 : ∀ t, t ∉ Ioo a (1 - a) → φ t = 0) : ∃ C, ∀ t, |φ t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a (1 - a))).exists_bound_of_continuousOn
    hφ.continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Ioo a (1 - a)
  · exact (by simpa using hC t (Ioo_subset_Icc_self ht) : |φ t| ≤ C).trans (le_max_left _ _)
  · rw [hφ0 t ht, abs_zero]; exact le_max_right _ _

/-- **Product tests**: if `Σₖ e(xₖ) = 0` a.e. in the box, then
`∫ φ e + n (∫ φ)(∫ η e) = 0` for continuous `φ`, `η` vanishing outside `(a, 1 - a)`, `∫ η = 1`. -/
theorem product_identity {e : ℝ → ℝ} (he : Integrable e μ1) {a : ℝ}
    (hsum : ∀ᵐ x ∂μN n, x ∈ boxU n a → ∑ k, e (x k) = 0) {φ η : ℝ → ℝ}
    (hφ : Continuous φ) (hη : Continuous η) (hφ0 : ∀ t, t ∉ Ioo a (1 - a) → φ t = 0)
    (hη0 : ∀ t, t ∉ Ioo a (1 - a) → η t = 0) (hη1 : ∫ t, η t ∂μ1 = 1) :
    ∫ t, φ t * e t ∂μ1 + n * ((∫ t, φ t ∂μ1) * ∫ t, η t * e t ∂μ1) = 0 := by
  obtain ⟨Cφ, hCφ⟩ := integrable_cont_vanish hφ hφ0
  obtain ⟨Cη, hCη⟩ := integrable_cont_vanish hη hη0
  set ψ : Fin (n + 1) → ℝ → ℝ := fun i => if i = 0 then φ else η
  have hψi : ∀ i, Integrable (ψ i) μ1 := fun i => by
    by_cases h : i = 0
    · simp only [ψ, h, ↓reduceIte]
      exact Integrable.of_bound hφ.aestronglyMeasurable Cφ (ae_of_all _ fun t => hCφ t)
    · simp only [ψ, h, ↓reduceIte]
      exact Integrable.of_bound hη.aestronglyMeasurable Cη (ae_of_all _ fun t => hCη t)
  have hψe : ∀ i, Integrable (fun t => e t * ψ i t) μ1 := fun i => by
    by_cases h : i = 0
    · simp only [ψ, h, ↓reduceIte]
      exact (he.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ fun t => hCφ t)).congr
        (ae_of_all _ fun t => by ring)
    · simp only [ψ, h, ↓reduceIte]
      exact (he.bdd_mul hη.aestronglyMeasurable (ae_of_all _ fun t => hCη t)).congr
        (ae_of_all _ fun t => by ring)
  set ψk : Fin (n + 1) → Fin (n + 1) → ℝ → ℝ := fun k i => if i = k then fun t => e t * ψ i t
    else ψ i
  have hψki : ∀ k i, Integrable (ψk k i) μ1 := fun k i => by
    by_cases h : i = k
    · simp only [ψk, h, ↓reduceIte]; exact hψe k
    · simp only [ψk, h, ↓reduceIte]; exact hψi i
  have hterm : ∀ k, Integrable (fun x : Cfg n => ∏ i, ψk k i (x i)) (μN n) := fun k =>
    integrable_prod_cube (hψki k)
  -- the integrand vanishes a.e.
  have hz : ∫ x, ∑ k, ∏ i, ψk k i (x i) ∂μN n = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hsum] with x hx
    have e1 : ∑ k, ∏ i, ψk k i (x i) = (∑ k, e (x k)) * ∏ i, ψ i (x i) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ (fun i => ψ i (x i)) (Finset.mem_univ k)]
      have hpe : ∏ i ∈ Finset.univ.erase k, ψk k i (x i) =
          ∏ i ∈ Finset.univ.erase k, ψ i (x i) :=
        Finset.prod_congr rfl fun i hi => by simp [ψk, Finset.ne_of_mem_erase hi]
      rw [hpe]
      simp only [ψk, ↓reduceIte]
      ring
    rw [e1]
    by_cases hU : x ∈ boxU n a
    · rw [hx hU, zero_mul]; rfl
    · simp only [boxU, Set.mem_pi, mem_univ, true_implies, not_forall] at hU
      obtain ⟨i, hi⟩ := hU
      have : ψ i (x i) = 0 := by
        by_cases h : i = 0
        · simp only [ψ, h, ↓reduceIte]; exact hφ0 _ (h ▸ hi)
        · simp only [ψ, h, ↓reduceIte]; exact hη0 _ hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) this, mul_zero]; rfl
  rw [integral_finsetSum _ fun k _ => hterm k] at hz
  simp only [integral_prod_cube] at hz
  -- evaluate the products
  have hψint : ∀ i, ∫ t, ψ i t ∂μ1 = if i = 0 then ∫ t, φ t ∂μ1 else 1 := fun i => by
    by_cases h : i = 0 <;> simp [ψ, h, hη1]
  have hk0 : ∏ i, ∫ t, ψk 0 i t ∂μ1 = ∫ t, φ t * e t ∂μ1 := by
    rw [Finset.prod_eq_single 0 (fun i _ hi => by simp [ψk, hi, hψint i])
      (fun h => absurd (Finset.mem_univ 0) h)]
    simp only [ψk, ψ, ↓reduceIte]
    congr 1; funext t; ring
  have hks : ∀ j : Fin n, ∏ i, ∫ t, ψk j.succ i t ∂μ1 =
      (∫ t, φ t ∂μ1) * ∫ t, η t * e t ∂μ1 := fun j => by
    rw [Finset.prod_eq_mul (0 : Fin (n + 1)) j.succ (Fin.succ_ne_zero j).symm
      (fun i _ hi => by simp [ψk, hi.1, hi.2, hψint i])
      (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
    simp only [ψk, ψ, (Fin.succ_ne_zero j).symm, Fin.succ_ne_zero j, ↓reduceIte]
    congr 1
    congr 1; funext t; ring
  rw [Fin.sum_univ_succ, hk0] at hz
  simp only [hks, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hz
  exact hz

/-! ### (H) Hohenberg–Kohn -/

lemma integral_pos_of_cont {T : ℝ → ℝ} (hT : Continuous T) (h0 : ∀ t, 0 ≤ T t) {t0 : ℝ}
    (ht0 : t0 ∈ Icc (0 : ℝ) 1) (hpos : 0 < T t0) : 0 < ∫ t, T t ∂μ1 := by
  by_contra hle
  push Not at hle
  have := le_of_int_nonneg_zero hT h0 hle t0 ht0
  linarith

/-- A continuous function on `[0, 1]` vanishing outside `[a, 1 - a]` extends by zero outside
`(a, 1 - a)`. -/
lemma ext_vanish {q : Pot} {a : ℝ} (ha : 0 < a) (_ha2 : a < 1 / 2)
    (hq : ∀ t : Icc (0 : ℝ) 1, (t : ℝ) ∉ Icc a (1 - a) → q t = 0) :
    ∀ t, t ∉ Ioo a (1 - a) → ext q t = 0 := by
  have hc := continuous_ext q
  have hS : IsClosed {t | ext q t = 0} := isClosed_eq hc continuous_const
  have hval : ∀ t, t < a ∨ 1 - a < t → ext q t = 0 := fun t ht => by
    simp only [Box.ext]
    refine hq _ fun hm => ?_
    have h1 := hm.1; have h2 := hm.2
    simp only [Set.coe_projIcc] at h1 h2
    rcases ht with h | h
    · have : max 0 (min 1 t) < a := max_lt ha (lt_of_le_of_lt (min_le_right _ _) h)
      linarith
    · have : 1 - a < max 0 (min 1 t) :=
        lt_max_of_lt_right (lt_min (by linarith) h)
      linarith
  intro t ht
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
  rcases ht with h | h
  · have hsub : Iio a ⊆ {t | ext q t = 0} := fun s hs => hval s (Or.inl hs)
    have := hS.closure_subset_iff.2 hsub
    rw [closure_Iio' ⟨a - 1, by simp⟩] at this
    exact this h
  · have hsub : Ioi (1 - a) ⊆ {t | ext q t = 0} := fun s hs => hval s (Or.inr hs)
    have := hS.closure_subset_iff.2 hsub
    rw [closure_Ioi' ⟨1 - a + 1, by simp⟩] at this
    exact this h

section final

variable {μp μm μp' μm' : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] [IsMeas01 μp'] [IsMeas01 μm']

/-- **`D` vanishes on functions supported in `[a, 1 - a]`.** -/
theorem D_vanish (hw : Continuous w) {Φ : Cfg n → ℝ} (h : IsGSN τ w (nuOf μp μm) Φ)
    (h' : IsGSN τ w (nuOf μp' μm') Φ) {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) {q : Pot}
    (hq : ∀ t : Icc (0 : ℝ) 1, (t : ℝ) ∉ Icc a (1 - a) → q t = 0) :
    (nuOf μp μm - nuOf μp' μm' - ((QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) /
      (n + 1)) • intCLM μ1) q = 0 := by
  set D := nuOf μp μm - nuOf μp' μm' - ((QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) /
      (n + 1)) • intCLM μ1
  have hN : (0 : ℝ) < n + 1 := by positivity
  obtain ⟨R, hR, hDR⟩ := D_rhoHat_ac hw h h'
  obtain ⟨c0, hc0, hc0le⟩ := exists_rhoHat_ge hw h ha ha2.le
  set ρ := ext (rhoHat τ Φ)
  set e : ℝ → ℝ := fun t => -R t / ρ t
  set ea := (Icc a (1 - a)).indicator e
  have hea : Integrable ea μ1 := by
    have hem : AEStronglyMeasurable e μ1 :=
      (hR.1.neg.mul ((continuous_ext (rhoHat τ Φ)).measurable.inv).aestronglyMeasurable).congr
        (ae_of_all _ fun t => by
          simp only [e, Pi.mul_apply, Pi.neg_apply, div_eq_mul_inv]; rfl)
    have hon : IntegrableOn e (Icc a (1 - a)) μ1 := by
      refine ((hR.restrict (s := Icc a (1 - a))).abs.div_const c0).mono' hem.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_div, abs_neg]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hc0
        ((hc0le t ht).trans (le_abs_self _))
    exact hon.integrable_indicator measurableSet_Icc
  -- `D` as an integral against `ea`
  have hDq : ∀ q' : Pot, (∀ t : Icc (0 : ℝ) 1, (t : ℝ) ∉ Icc a (1 - a) → q' t = 0) →
      D q' = ∫ t, ext q' t * ea t ∂μ1 := fun q' hq' => by
    rw [D_eq_integral hw h hDR ha ha2.le hq']
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    by_cases hin : t ∈ Icc a (1 - a)
    · simp only [ea, indicator_of_mem hin, e]; rfl
    · have : ext q' t = 0 := by
        simp only [Box.ext, projIcc_of_mem _ (Ioo_subset_Icc_self ht)]
        exact hq' ⟨t, Ioo_subset_Icc_self ht⟩ hin
      simp [this]
  -- the symmetric tests
  have htest : ∀ χ : Cfg n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ boxU n a → (∀ σ x, χ (pm σ x) = χ x) →
      ∫ x, ea (x 0) * (χ x * Φ x ^ 2) ∂μN n = 0 := by
    intro χ hχ hχc hχU hχs
    have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
    obtain ⟨Cχ, hCχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    have hCχ' : ∀ x, |χ x| ≤ Cχ := fun x => by simpa using hCχ x
    have hsupp : ∀ x, χ x ≠ 0 → x 0 ∈ Icc a (1 - a) := fun x hx =>
      Ioo_subset_Icc_self (hχU (subset_tsupport _ hx) 0 trivial)
    have hvan := rhoHat2_vanish hw h.1 hχ1 hCχ' hχs ha.le hsupp
    have h0 := D_rhoHat2 hw h h' (mem_mul_sym h.1 hχ1 hχs)
    rw [hDq _ hvan] at h0
    have hL1 := int_rhoHat2_L1 hw h.1 hχ1 hCχ' hχs hea
    have e1 : ∫ t, ext (rhoHat2 τ Φ (fun x => χ x * Φ x)) t * ea t ∂μ1 =
        ∫ t, ea t * ext (rhoHat2 τ Φ (fun x => χ x * Φ x)) t ∂μ1 := by
      congr 1; funext t; ring
    rw [e1, hL1] at h0
    exact (mul_eq_zero.1 h0).resolve_left hN.ne'
  have hG := sum_ae_zero h.1 hea ha.le htest
  have hsum : ∀ᵐ x ∂μN n, x ∈ boxU n a → ∑ k, ea (x k) = 0 := by
    filter_upwards [ae_restrict_of_ae hG, gsN_ne_zero hw h] with x h1 h2 hxU
    have := h1 hxU
    rcases mul_eq_zero.1 this with h3 | h3
    · exact h3
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h3) h2
  -- a normalised tent
  set T : ℝ → ℝ := tentF (1 / 2) (1 / 2 - a)
  have hw2 : 0 < 1 / 2 - a := by linarith
  have hTc : Continuous T := (lipschitz_tent hw2).continuous
  have hT0 : ∀ t, t ∉ Ioo a (1 - a) → T t = 0 := fun t ht => by
    refine tent_far hw2 ?_
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have hTnn : ∀ t, 0 ≤ T t := fun t => le_max_left _ _
  have hTpos : 0 < ∫ t, T t ∂μ1 :=
    integral_pos_of_cont hTc hTnn (t0 := 1 / 2) ⟨by norm_num, by norm_num⟩
      (by simp only [T, tentF, sub_self, abs_zero, zero_div, sub_zero]; norm_num)
  set η : ℝ → ℝ := fun t => T t / ∫ t, T t ∂μ1
  have hηc : Continuous η := hTc.div_const _
  have hη0 : ∀ t, t ∉ Ioo a (1 - a) → η t = 0 := fun t ht => by simp [η, hT0 t ht]
  have hη1 : ∫ t, η t ∂μ1 = 1 := by
    simp only [η]; rw [integral_div]; exact div_self hTpos.ne'
  have hκ : ∫ t, η t * ea t ∂μ1 = 0 := by
    have := product_identity hea hsum hηc hηc hη0 hη0 hη1
    rw [hη1, one_mul] at this
    have : ((n : ℝ) + 1) * ∫ t, η t * ea t ∂μ1 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hN.ne'
  have := product_identity hea hsum (continuous_ext q) hηc (ext_vanish ha ha2 hq) hη0 hη1
  rw [hκ, mul_zero, mul_zero, add_zero] at this
  rw [hDq q hq, this]

/-- **`D` vanishes on all continuous functions vanishing at the walls.** -/
theorem D_vanish_walls (hw : Continuous w) {Φ : Cfg n → ℝ} (h : IsGSN τ w (nuOf μp μm) Φ)
    (h' : IsGSN τ w (nuOf μp' μm') Φ) {q : Pot} (h0 : q ⟨0, le_rfl, zero_le_one⟩ = 0)
    (h1 : q ⟨1, zero_le_one, le_rfl⟩ = 0) :
    (nuOf μp μm - nuOf μp' μm' - ((QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) /
      (n + 1)) • intCLM μ1) q = 0 := by
  set D := nuOf μp μm - nuOf μp' μm' - ((QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) /
      (n + 1)) • intCLM μ1
  by_contra hne
  set r := |D q|
  have hr : 0 < r := abs_pos.2 hne
  set ε := r / (2 * (‖D‖ + 1))
  have hε : 0 < ε := by positivity
  set H := ext q
  have hHc : Continuous H := continuous_ext q
  have hH0 : H 0 = 0 := by simp only [H, Box.ext]; rw [projIcc_left]; exact h0
  have hH1 : H 1 = 0 := by simp only [H, Box.ext]; rw [projIcc_right]; exact h1
  obtain ⟨δ0, hδ0, hb0⟩ := Metric.continuousAt_iff.1 hHc.continuousAt ε hε
  obtain ⟨δ1, hδ1, hb1⟩ := Metric.continuousAt_iff.1 (hHc.continuousAt (x := 1)) ε hε
  set a := min (1 / 4) (min δ0 δ1) / 3
  have hpos : 0 < min (1 / 4 : ℝ) (min δ0 δ1) := by positivity
  have ha : 0 < a := by positivity
  have ha4 : a ≤ 1 / 12 := by
    have := min_le_left (1 / 4 : ℝ) (min δ0 δ1); simp only [a]; linarith
  have ha0 : 2 * a < δ0 := by
    have := (min_le_right (1 / 4 : ℝ) (min δ0 δ1)).trans (min_le_left δ0 δ1)
    simp only [a]; linarith
  have ha1 : 2 * a < δ1 := by
    have := (min_le_right (1 / 4 : ℝ) (min δ0 δ1)).trans (min_le_right δ0 δ1)
    simp only [a]; linarith
  set qa : Pot := ⟨fun t => q t * cutF a t,
    q.continuous.mul ((lipschitz_cutF ha).continuous.comp continuous_subtype_val)⟩
  have hqa : D qa = 0 := D_vanish hw h h' ha (by linarith) fun t ht => by
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    simp only [qa, ContinuousMap.coe_mk]
    rw [cutF_out ha (ht.elim (fun h => Or.inl h.le) fun h => Or.inr h.le), mul_zero]
  have hclose : ‖q - qa‖ ≤ ε := by
    refine (ContinuousMap.norm_le _ hε.le).2 fun t => ?_
    simp only [qa, ContinuousMap.sub_apply, ContinuousMap.coe_mk, Real.norm_eq_abs]
    have htI := t.2
    have hqt : q t = H t := by simp [H, Box.ext, projIcc_of_mem _ htI]
    by_cases hmid : 2 * a ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 - 2 * a
    · rw [cutF_mid ha hmid.1 hmid.2]; simp [hε.le]
    · rw [not_and_or, not_le, not_le] at hmid
      have hsmall : |H t| < ε := by
        rcases hmid with h' | h'
        · have := hb0 (x := t) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg htI.1]; linarith)
          rwa [Real.dist_eq, hH0, sub_zero] at this
        · have := hb1 (x := t) (by
            rw [Real.dist_eq, abs_of_nonpos (by linarith [htI.2])]; linarith)
          rwa [Real.dist_eq, hH1, sub_zero] at this
      have hc0 := cutF_nonneg a t
      have hc1 := cutF_le_one a t
      rw [show q t - q t * cutF a t = q t * (1 - cutF a t) by ring, abs_mul, hqt]
      have : |1 - cutF a t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (H t), abs_nonneg (1 - cutF a t)]
  have hDd : |D q| ≤ ‖D‖ * ε := by
    have := D.le_opNorm (q - qa)
    rw [map_sub, hqa, sub_zero, Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left hclose (norm_nonneg D))
  have : ‖D‖ * ε < r := by
    simp only [ε]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg D]
  linarith

/-- **Hohenberg–Kohn for interacting particles in measure potentials**: if two measure potentials
have a common ground state (bosons or fermions, continuous interaction), they differ by
`C dx + a δ₀ + b δ₁`. -/
theorem hk_meas_N (hw : Continuous w) {Φ : Cfg n → ℝ} (h : IsGSN τ w (nuOf μp μm) Φ)
    (h' : IsGSN τ w (nuOf μp' μm') Φ) :
    ∃ C a b : ℝ, nuOf μp μm - nuOf μp' μm' = C • intCLM μ1 +
      a • deltaM ⟨0, le_rfl, zero_le_one⟩ + b • deltaM ⟨1, zero_le_one, le_rfl⟩ := by
  set c := (QMN τ w (nuOf μp μm) Φ - QMN τ w (nuOf μp' μm') Φ) / (n + 1)
  set D := nuOf μp μm - nuOf μp' μm' - c • intCLM μ1
  set z : Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  set o : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have key : ∀ q : Pot, D q = q z * D (linP 1) + q o * D (linP 0) := fun q => by
    set q' := q - q z • linP 1 - q o • linP 0
    have hz : q' z = 0 := by simp [q', linP, z]
    have ho : q' o = 0 := by simp [q', linP, o]; norm_num
    have := D_vanish_walls hw h h' hz ho
    simp only [q', map_sub, map_smul, smul_eq_mul] at this
    linarith
  refine ⟨c, D (linP 1), D (linP 0), ?_⟩
  ext q
  have hDq : D q = nuOf μp μm q - nuOf μp' μm' q - c * intCLM μ1 q := by simp [D]
  rw [key q] at hDq
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, deltaM,
    ContinuousMap.evalCLM_apply]
  linarith

/-- **Hohenberg–Kohn for interacting particles in measure potentials, from densities**: if two
measure potentials have ground states with the same density, they differ by
`C dx + a δ₀ + b δ₁`. -/
theorem hk_meas_N_dens (hw : Continuous w) {Φ Φ' : Cfg n → ℝ} (h : IsGSN τ w (nuOf μp μm) Φ)
    (h' : IsGSN τ w (nuOf μp' μm') Φ') (hρ : rhoHat τ Φ = rhoHat τ Φ') :
    ∃ C a b : ℝ, nuOf μp μm - nuOf μp' μm' = C • intCLM μ1 +
      a • deltaM ⟨0, le_rfl, zero_le_one⟩ + b • deltaM ⟨1, zero_le_one, le_rfl⟩ :=
  hk_meas_N hw h (isGSN_of_same_dens h h' hρ).1

end final

end DFT.Continuum.Line
