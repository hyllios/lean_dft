/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Complete

/-!
# Lieb's characterisation of `N`-representable densities on a line

**Necessity** (`sqrt_dens_H1W`): for every `H¹₀` state `Φ` (`DomW`), the density
`ρ(t) = N ∫ Φ(t, y)² dy` is `g²` for some `g ∈ H10` with `∫₀¹ g'² ≤ Σ_k ∫ |∂ₖΦ|²`, and the
density functional of `Φ` is `v ↦ ∫₀¹ v g²`.

The proof approximates `Φ` by its sine truncations `P_M` (`Line/Complete`), which are `C²` states
with kinetic energy at most that of `Φ`. For each `P_M`, `u_M = √(ρ_M + ε_M) - √ε_M` is `C¹`,
vanishes at `0` and `1`, and has `∫ u_M'² ≤ ∫ ρ_M'² / (4ρ_M) ≤ T(P_M)` (`Line/Density`). As
`M → ∞`, `ρ_M → ρ` in `L¹` and `u_M → √ρ` in `L²`, and the closure lemma `h1_closure` gives
`g`.

**The characterisation** (`lieb_characterisation`): a density functional `ρ` is the density of a
normalised `H¹₀` state of `N` bosons or fermions iff `ρ(v) = ∫₀¹ v g²` for some `g ∈ H10` with
`∫₀¹ g² = N`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Spectral

variable {n : ℕ} {τ : Stat}

/-! ### Fubini with the first particle outermost -/

lemma integrable_cons_prod {F : Cfg n → ℝ} (hF : Integrable F (μN n)) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Cube' n))) := by
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
  have := (hr.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  simpa [Function.comp_def, hcomp, Fin.insertNth_zero'] using this

lemma integral_cube_cons' {F : Cfg n → ℝ} (hF : Integrable F (μN n)) :
    ∫ x, F x ∂μN n = ∫ t in Ioo (0 : ℝ) 1, ∫ y in Cube' n, F (Fin.cons t y) := by
  have hP := integrable_cons_prod hF
  rw [integral_cube_ins 0 hF, ← integral_prod _ hP]
  simp only [Fin.insertNth_zero']
  exact (integral_prod_symm _ hP).symm

/-! ### The density of an `H¹₀` state -/

lemma int_sq {f : Cfg n → ℝ} (h : MemLp f 2 (μN n)) : Integrable (fun x => f x ^ 2) (μN n) :=
  (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h

lemma integrable_marg {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) : Integrable (marg Φ) μ1 :=
  (integrable_cons_prod (F := fun x => Φ x ^ 2)
    (int_sq hΦ)).integral_prod_left

lemma integral_rhoN {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) :
    ∫ t, rhoN Φ t ∂μ1 = (n + 1) * ∫ x, Φ x ^ 2 ∂μN n := by
  rw [integral_cube_cons' (int_sq hΦ), ← integral_const_mul]
  rfl

/-- `rhoN` is the density of an `H¹₀` state. -/
theorem dens_eq_rhoNW {w : Cfg n → ℝ} {hw : Continuous w} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    (v : Pot) : dens (settingW τ n w hw) Φ v = ∫ t, ext v t * rhoN Φ t ∂μ1 := by
  have hv := continuous_ext v
  have hsq : Integrable (fun x => Φ x * Φ x) (μN n) := int_mul_L2 hΦ.1 hΦ.1
  have hint : ∀ k : Fin (n + 1), Integrable (fun x => ext v (x k) * (Φ x * Φ x)) (μN n) := by
    intro k
    obtain ⟨C, hC⟩ := ae_bound_cont (n := n) (hv.comp (continuous_apply k))
    exact hsq.bdd_mul (hv.comp (continuous_apply k)).aestronglyMeasurable hC
  have swapsq : ∀ k : Fin (n + 1), ∫ x, ext v (x k) * (Φ x * Φ x) ∂μN n =
      ∫ x, ext v (x 0) * (Φ x * Φ x) ∂μN n := by
    intro k
    rw [← integral_pm (Equiv.swap 0 k) (fun x => ext v (x 0) * (Φ x * Φ x))]
    refine integral_congr_ae ?_
    filter_upwards [hΦ.2.2 (Equiv.swap 0 k)] with x hx
    simp only [pm, Equiv.swap_apply_left] at hx ⊢
    rw [hx]
    have := ch_mul_self τ (Equiv.swap 0 k)
    linear_combination (-(ext v (x k) * (Φ x * Φ x))) * this
  simp only [dens, pf]
  change ∫ x, (∑ k, ext v (x k)) * (Φ x * Φ x) ∂μN n = _
  have hpt : (fun x : Cfg n => (∑ k, ext v (x k)) * (Φ x * Φ x)) =
      fun x => ∑ k, ext v (x k) * (Φ x * Φ x) := by
    funext x; rw [Finset.sum_mul]
  rw [hpt, integral_finsetSum (f := fun k x => ext v (x k) * (Φ x * Φ x)) _ fun k _ => hint k]
  simp only [swapsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_cube_cons' (hint 0), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  simp only [Fin.cons_zero, rhoN, marg, ← integral_const_mul]
  push_cast
  congr 1; funext y; ring

/-! ### `L¹` convergence of the densities of the truncations -/

lemma abs_sq_sub_sq_le (a b : ℝ) : |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by
  rw [← abs_mul]; ring_nf

/-- `∫ |ρ_P - ρ_Φ| ≤ N ∫ |P² - Φ²|`. -/
lemma integral_abs_rhoN_sub {P Φ : Cfg n → ℝ} (hP : MemLp P 2 (μN n)) (hΦ : MemLp Φ 2 (μN n)) :
    ∫ t, |rhoN P t - rhoN Φ t| ∂μ1 ≤ (n + 1) * ∫ x, |P x ^ 2 - Φ x ^ 2| ∂μN n := by
  have iP := int_sq hP
  have iΦ := int_sq hΦ
  have hD : Integrable (fun x => |P x ^ 2 - Φ x ^ 2|) (μN n) := (iP.sub iΦ).abs
  have e : ∀ t, |rhoN P t - rhoN Φ t| = (n + 1) * |marg P t - marg Φ t| := fun t => by
    simp only [rhoN]; rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  simp only [e]
  rw [integral_const_mul, integral_cube_cons' hD]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine integral_mono_ae ((integrable_marg hP).sub (integrable_marg hΦ)).abs
    (integrable_cons_prod hD).integral_prod_left ?_
  filter_upwards [(integrable_cons_prod iP).prod_right_ae,
    (integrable_cons_prod iΦ).prod_right_ae] with t h1 h2
  simp only [marg]
  rw [← integral_sub h1 h2]
  exact abs_integral_le_integral_abs

/-- **The densities of the truncations converge in `L¹`.** -/
lemma tendsto_rhoN_trunc {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) :
    Tendsto (fun M => ∫ t, |rhoN (trunc M Φ) t - rhoN Φ t| ∂μ1) atTop (𝓝 0) := by
  set D : ℕ → ℝ := fun M => ∫ x, (Φ x - trunc M Φ x) ^ 2 ∂μN n
  set S := ∫ x, Φ x ^ 2 ∂μN n
  have hD := tendsto_trunc hΦ
  have hPm : ∀ M, MemLp (trunc M Φ) 2 (μN n) := fun M => memLp_cont (continuous_trunc M Φ)
  have bound : ∀ M, ∫ t, |rhoN (trunc M Φ) t - rhoN Φ t| ∂μ1 ≤
      (n + 1) * (√(D M) * √(2 * D M + 8 * S)) := by
    intro M
    refine (integral_abs_rhoN_sub (hPm M) hΦ).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hd : MemLp (fun x => trunc M Φ x - Φ x) 2 (μN n) := (hPm M).sub hΦ
    have hs : MemLp (fun x => trunc M Φ x + Φ x) 2 (μN n) := (hPm M).add hΦ
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μN n) Real.HolderConjugate.two_two
      (f := fun x => |trunc M Φ x - Φ x|) (g := fun x => |trunc M Φ x + Φ x|)
      (ae_of_all _ fun x => abs_nonneg _) (ae_of_all _ fun x => abs_nonneg _)
      (by rw [ENNReal.ofReal_ofNat]; exact hd.abs) (by rw [ENNReal.ofReal_ofNat]; exact hs.abs)
    have e1 : (∫ x, |trunc M Φ x - Φ x| ^ (2 : ℝ) ∂μN n) = D M := by
      simp only [D]; congr 1; funext x; rw [Real.rpow_two, sq_abs]; ring
    have e2 : ∫ x, |trunc M Φ x + Φ x| ^ (2 : ℝ) ∂μN n ≤ 2 * D M + 8 * S := by
      simp only [D, S, Real.rpow_two, sq_abs]
      have iD : Integrable (fun x => (Φ x - trunc M Φ x) ^ 2) (μN n) :=
        int_sq (hΦ.sub (hPm M))
      have iS := int_sq hΦ
      have iA := int_sq hs
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (f := fun x => 2 * (Φ x - trunc M Φ x) ^ 2) (g := fun x => 8 * Φ x ^ 2)
          (iD.const_mul _) (iS.const_mul _)]
      refine integral_mono iA ((iD.const_mul _).add (iS.const_mul _)) fun x => ?_
      nlinarith [sq_nonneg (trunc M Φ x - Φ x - 2 * Φ x)]
    calc ∫ x, |trunc M Φ x ^ 2 - Φ x ^ 2| ∂μN n
        = ∫ x, |trunc M Φ x - Φ x| * |trunc M Φ x + Φ x| ∂μN n := by
          congr 1; funext x; exact abs_sq_sub_sq_le _ _
      _ ≤ _ := h
      _ ≤ √(D M) * √(2 * D M + 8 * S) := by
          rw [e1, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          gcongr
  have hlim : Tendsto (fun M => (n + 1 : ℝ) * (√(D M) * √(2 * D M + 8 * S))) atTop (𝓝 0) := by
    have := ((hD.sqrt).mul (((hD.const_mul 2).add_const (8 * S)).sqrt)).const_mul ((n : ℝ) + 1)
    simpa using this
  exact squeeze_zero (fun M => integral_nonneg fun t => abs_nonneg _) bound hlim

/-! ### The regularised square roots -/

lemma sq_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (√a - √b) ^ 2 ≤ |a - b| := by
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have h1 : |√a - √b| ≤ √a + √b := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h2 : (√a - √b) ^ 2 = |√a - √b| * |√a - √b| := by rw [← sq, sq_abs]
  have h3 : a - b = (√a - √b) * (√a + √b) := by
    linear_combination (-1 : ℝ) * Real.sq_sqrt ha + Real.sq_sqrt hb
  rw [h2, h3, abs_mul, abs_of_nonneg (add_nonneg hx hy)]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

section reg

variable {P : Cfg n → ℝ} (hP : P ∈ Dom τ n) {ε : ℝ} (hε : 0 < ε)
include hP hε

lemma rhoN_add_pos (t : ℝ) : 0 < rhoN P t + ε :=
  add_pos_of_nonneg_of_pos ((sqrt_dens_H1 hP).1 t) hε

lemma hasDerivAt_ureg (t : ℝ) :
    HasDerivAt (fun s => √(rhoN P s + ε) - √ε)
      (rhoD P t / (2 * √(rhoN P t + ε))) t :=
  ((((sqrt_dens_H1 hP).2.2.2.2.1 t).add_const ε).sqrt (rhoN_add_pos hP hε t).ne').sub_const _

lemma contDiff_ureg : ContDiff ℝ 1 fun s => √(rhoN P s + ε) - √ε := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_ureg hP hε t).differentiableAt, ?_⟩
  rw [show deriv (fun s => √(rhoN P s + ε) - √ε) =
    fun t => rhoD P t / (2 * √(rhoN P t + ε)) from funext fun t => (hasDerivAt_ureg hP hε t).deriv]
  have hcρ : Continuous (rhoN P) := continuous_const.mul (continuous_marg hP)
  exact (sqrt_dens_H1 hP).2.2.2.2.2.1.div (continuous_const.mul (hcρ.add continuous_const).sqrt)
    fun t => by have := Real.sqrt_pos.2 (rhoN_add_pos hP hε t); positivity

/-- `∫ u'² ≤ T(P)` for the regularised square root. -/
lemma integral_deriv_ureg_le :
    ∫ t, deriv (fun s => √(rhoN P s + ε) - √ε) t ^ 2 ∂μ1 ≤
      ∫ x, ∑ k, dk k P x * dk k P x ∂μN n := by
  have hd : ∀ t, deriv (fun s => √(rhoN P s + ε) - √ε) t =
      rhoD P t / (2 * √(rhoN P t + ε)) := fun t => (hasDerivAt_ureg hP hε t).deriv
  have hK : Integrable (fun t => (n + 1 : ℝ) * margK P t) μ1 :=
    integrable_of_continuous (continuous_const.mul (continuous_margK hP))
  have hpt : ∀ t, (rhoD P t / (2 * √(rhoN P t + ε))) ^ 2 ≤ (n + 1) * margK P t := by
    intro t
    have hpos := rhoN_add_pos hP hε t
    have hs : (2 * √(rhoN P t + ε)) ^ 2 = 4 * (rhoN P t + ε) := by
      rw [mul_pow, Real.sq_sqrt hpos.le]; ring
    rw [div_pow, hs, div_le_iff₀ (by positivity)]
    have h := margD_sq_le hP t
    have hK0 := margK_nonneg (Φ := P) t
    have hm0 := marg_nonneg (Φ := P) t
    have hN : (0 : ℝ) ≤ n + 1 := by positivity
    simp only [rhoD, rhoN]
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n : ℝ) + 1)),
      mul_nonneg (mul_nonneg hN hK0) hε.le, mul_nonneg hN hK0]
  simp only [hd]
  calc ∫ t, (rhoD P t / (2 * √(rhoN P t + ε))) ^ 2 ∂μ1 ≤ ∫ t, (n + 1 : ℝ) * margK P t ∂μ1 := by
        refine integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hK
          (ae_of_all _ hpt)
    _ = ∫ x, ∑ k, dk k P x * dk k P x ∂μN n := by
        rw [kin_eq hP, integral_cube_cons (F := fun x => dk 0 P x ^ 2) ((cont_dk hP 0).pow 2),
          integral_const_mul]
        rfl

end reg

/-! ### Necessity -/

/-- **Necessity of `√ρ ∈ H¹₀`**: for every `H¹₀` state `Φ`, `√ρ` has an `H10` representative `g`
with `∫ g'² ≤ Σ_k ∫ |∂ₖΦ|²`. -/
theorem sqrt_dens_H1W {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) :
    ∃ g : ℝ → ℝ, H10 g ∧ (∀ᵐ t ∂μ1, g t ^ 2 = rhoN Φ t) ∧
      ∫ t, deriv g t ^ 2 ∂μ1 ≤ ∑ k, ∫ x, dW k Φ x * dW k Φ x ∂μN n := by
  set ε : ℕ → ℝ := fun M => 1 / ((M : ℝ) + 1)
  have hε : ∀ M, 0 < ε M := fun M => by positivity
  have hP : ∀ M, trunc M Φ ∈ Dom τ n := trunc_mem hΦ
  set u : ℕ → ℝ → ℝ := fun M s => √(rhoN (trunc M Φ) s + ε M) - √(ε M)
  have hu : ∀ M, ContDiff ℝ 1 (u M) := fun M => contDiff_ureg (hP M) (hε M)
  have hρm := integrable_marg hΦ.1
  have hρ0 : ∀ t, 0 ≤ rhoN Φ t := fun t => mul_nonneg (by positivity) (marg_nonneg t)
  have hint : Integrable (rhoN Φ) μ1 := hρm.const_mul _
  have hfm : MemLp (fun t => √(rhoN Φ t)) 2 μ1 := by
    have hm : AEStronglyMeasurable (fun t => √(rhoN Φ t)) μ1 :=
      (continuous_sqrt.comp_aestronglyMeasurable hint.1)
    refine (memLp_two_iff_integrable_sq hm).2 (hint.congr (ae_of_all _ fun t => ?_))
    simp [Real.sq_sqrt (hρ0 t)]
  set f : HL := hfm.toLp
  have hu0 : ∀ M, u M 0 = 0 := fun M => by
    simp [u, (sqrt_dens_H1 (hP M)).2.1]
  have hu1 : ∀ M, u M 1 = 0 := fun M => by
    simp [u, (sqrt_dens_H1 (hP M)).2.2.1]
  have hC : ∀ M, ∫ t, deriv (u M) t ^ 2 ∂μ1 ≤ ∑ k, ∫ x, dW k Φ x * dW k Φ x ∂μN n :=
    fun M => (integral_deriv_ureg_le (hP M) (hε M)).trans (kin_trunc_le hΦ M)
  -- `u_M → √ρ` in `L²`
  have hlim : Tendsto (fun M => toHL (hu M).continuous) atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hL1 := tendsto_rhoN_trunc hΦ.1
    have hnorm : ∀ M, ‖toHL (hu M).continuous - f‖ ^ 2 =
        ∫ t, (u M t - √(rhoN Φ t)) ^ 2 ∂μ1 := fun M => by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (toHL (hu M).continuous) f, toHL_ae (hu M).continuous,
        MemLp.coeFn_toLp hfm] with t h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]; simp [sq]
    have hbound : ∀ M, ∫ t, (u M t - √(rhoN Φ t)) ^ 2 ∂μ1 ≤
        2 * ∫ t, |rhoN (trunc M Φ) t - rhoN Φ t| ∂μ1 + 4 * ε M := by
      intro M
      have hρP : ∀ t, 0 ≤ rhoN (trunc M Φ) t := (sqrt_dens_H1 (hP M)).1
      have iL : Integrable (fun t => |rhoN (trunc M Φ) t - rhoN Φ t|) μ1 :=
        ((integrable_marg (memLp_cont (continuous_trunc M Φ))).const_mul _ |>.sub hint).abs
      have hpt : ∀ t, (u M t - √(rhoN Φ t)) ^ 2 ≤
          2 * |rhoN (trunc M Φ) t - rhoN Φ t| + 4 * ε M := by
        intro t
        have h1 := sq_sqrt_sub_sqrt_le (add_pos_of_nonneg_of_pos (hρP t) (hε M)).le (hρ0 t)
        have h3 : |rhoN (trunc M Φ) t + ε M - rhoN Φ t| ≤
            |rhoN (trunc M Φ) t - rhoN Φ t| + ε M := by
          calc |rhoN (trunc M Φ) t + ε M - rhoN Φ t|
              = |(rhoN (trunc M Φ) t - rhoN Φ t) + ε M| := by ring_nf
            _ ≤ |rhoN (trunc M Φ) t - rhoN Φ t| + |ε M| := abs_add_le _ _
            _ = _ := by rw [abs_of_pos (hε M)]
        have hc := Real.sq_sqrt (hε M).le
        simp only [u]
        nlinarith [sq_nonneg (√(rhoN (trunc M Φ) t + ε M) - √(rhoN Φ t) + √(ε M))]
      calc ∫ t, (u M t - √(rhoN Φ t)) ^ 2 ∂μ1
          ≤ ∫ t, (2 * |rhoN (trunc M Φ) t - rhoN Φ t| + 4 * ε M) ∂μ1 :=
            integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _)
              ((iL.const_mul 2).add (integrable_const _)) (ae_of_all _ hpt)
        _ = _ := by
            rw [integral_add (iL.const_mul 2) (integrable_const _), integral_const_mul,
              integral_const]
            simp
    have hsq : Tendsto (fun M => ‖toHL (hu M).continuous - f‖ ^ 2) atTop (𝓝 0) := by
      simp only [hnorm]
      have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have := (hL1.const_mul 2).add (hε0.const_mul 4)
      simp only [mul_zero, add_zero] at this
      exact squeeze_zero (fun M => integral_nonneg fun t => sq_nonneg _) hbound this
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  obtain ⟨g, hg, hgf, hgd⟩ := h1_closure hu hu0 hu1 hC hlim
  refine ⟨g, hg, ?_, hgd⟩
  filter_upwards [hgf, MemLp.coeFn_toLp hfm] with t h1 h2
  rw [h1, h2, Real.sq_sqrt (hρ0 t)]

/-! ### Lieb's characterisation -/

lemma H10.const_mul {g : ℝ → ℝ} (hg : H10 g) (c : ℝ) : H10 fun t => c * g t := by
  refine ⟨hg.1.const_mul c, by simp [hg.2.1], by simp [hg.2.2.1], ?_⟩
  have e : (fun t => deriv (fun t => c * g t) t ^ 2) = fun t => c ^ 2 * deriv g t ^ 2 := by
    funext t; simp only [deriv_const_mul_field', mul_pow]
  rw [e]; exact hg.2.2.2.const_mul _

/-- **Lieb's characterisation of `N`-representable densities on a line**: a density functional
`ρ` is the density of a normalised finite-kinetic-energy state of `N` bosons or fermions iff
`ρ(v) = ∫₀¹ v g²` for some `g ∈ H¹₀(0, 1)` with `∫₀¹ g² = N`. -/
theorem lieb_characterisation {w : Cfg n → ℝ} {hw : Continuous w} (ρ : Pot → ℝ) :
    (∃ ψ ∈ Nst (settingW τ n w hw), dens (settingW τ n w hw) ψ = ρ) ↔
      ∃ g : ℝ → ℝ, H10 g ∧ ∫ t, g t ^ 2 ∂μ1 = n + 1 ∧
        ρ = fun v => ∫ t, ext v t * g t ^ 2 ∂μ1 := by
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg, hg2, -⟩ := sqrt_dens_H1W hψ.1
    refine ⟨g, hg, ?_, ?_⟩
    · rw [integral_congr_ae hg2, integral_rhoN hψ.1.1]
      have h1 : ∫ x, ψ x ^ 2 ∂μN n = 1 := by
        rw [← hψ.2]; simp only [ip, sq]
      rw [h1, mul_one]
    · funext v
      rw [dens_eq_rhoNW hψ.1 v]
      refine integral_congr_ae ?_
      filter_upwards [hg2] with t ht
      rw [ht]
  · rintro ⟨g, hg, hn, rfl⟩
    have hNp : (0 : ℝ) < n + 1 := by positivity
    set c := (√((n : ℝ) + 1))⁻¹
    have hc2 : c ^ 2 * ((n : ℝ) + 1) = 1 := by
      simp only [c, inv_pow, Real.sq_sqrt hNp.le, inv_mul_cancel₀ hNp.ne']
    have hnorm : ∫ t, (c * g t) ^ 2 ∂μ1 = 1 := by
      simp only [mul_pow]
      rw [integral_const_mul, hn, hc2]
    obtain ⟨ψ, hψ, hd⟩ := nrepW (τ := τ) (w := w) (hw := hw) (hg.const_mul c) hnorm
    refine ⟨ψ, hψ, funext fun v => ?_⟩
    rw [hd v]
    congr 1; funext t
    linear_combination (Box.ext v t * g t ^ 2) * hc2

end DFT.Continuum.Line
