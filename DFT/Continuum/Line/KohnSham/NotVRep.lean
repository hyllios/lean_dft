/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.HK.LiebCont
import DFT.Continuum.Line.HK.Nondeg

/-!
# `N`-representable densities that are not `v`-representable

For `N` bosons or fermions on `(0, 1)` with continuous `v` and `w`, every `H¹₀` ground state is
nonzero almost everywhere (`ucpW_cont`), so its density is positive almost everywhere. A density
that vanishes on an interval is therefore never a ground-state density, although it is
`N`-representable as soon as `√ρ ∈ H¹₀`.

* `dens_pos_of_isGS`: `∫ u ρ > 0` for the density `ρ` of any ground state and any continuous
  `u ≥ 0` that is positive somewhere in `(0, 1)`;
* `not_pureVRep_of_dens_zero`, `not_ensVRep_of_dens_zero`: a density functional with `ρ(u) = 0`
  for such a `u` is neither pure- nor ensemble-`v`-representable;
* **`nrep_not_vrep`**: `ρ = c² max(sin 2πx, 0)²`, normalised to `N` and vanishing on `[½, 1]`, is
  `N`-representable but not `v`-representable, for every continuous interaction `w`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-! ### Ground-state densities are positive -/

/-- The density of an `H¹₀` ground state charges every continuous `u ≥ 0` that is positive at an
interior point. -/
theorem dens_pos_of_isGS {v : C01} {ψ : Cfg n → ℝ} (hψ : IsGS (settingW τ n w hw) v ψ)
    {u : C01} (hu0 : ∀ t, 0 ≤ u t) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hpos : 0 < iccExt u c) :
    0 < dens (settingW τ n w hw) ψ u := by
  set F : Cfg n → ℝ := fun x => ∑ k, iccExt u (x k) with hFdef
  have hF : Continuous F :=
    continuous_finsetSum _ fun k _ => (continuous_iccExt u).comp (continuous_apply k)
  have hF0 : ∀ x, 0 ≤ F x := fun x => Finset.sum_nonneg fun k _ => hu0 _
  have hD : dens (settingW τ n w hw) ψ u = ∫ x, F x * (ψ x * ψ x) ∂μN n := rfl
  have hnn : ∀ x, 0 ≤ F x * (ψ x * ψ x) := fun x => mul_nonneg (hF0 x) (mul_self_nonneg _)
  have hint : Integrable (fun x => F x * (ψ x * ψ x)) (μN n) := by
    obtain ⟨C, hC⟩ := ae_bound_cont hF
    exact (int_mul_L2 hψ.1.1 hψ.1.1).bdd_mul hF.aestronglyMeasurable hC
  rw [hD]
  refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ?_
  have hz := (integral_eq_zero_iff_of_nonneg hnn hint).1 h0.symm
  have hFz : F =ᵐ[μN n] fun _ => 0 := by
    filter_upwards [hz, ucpW_cont (τ := τ) w hw v ψ hψ] with x h1 h2
    have h1' : F x * (ψ x * ψ x) = 0 := h1
    rcases mul_eq_zero.1 h1' with h | h
    · exact h
    · exact absurd (mul_self_eq_zero.1 h) h2
  have heq := Measure.eqOn_open_of_ae_eq hFz isOpen_cube hF.continuousOn continuousOn_const
  have hmem : (fun _ => c : Cfg n) ∈ Cube n := by
    simp only [Set.mem_pi, mem_univ, true_implies]
    exact fun _ => hc
  have h := heq hmem
  simp only [hFdef, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have : (0 : ℝ) < (n + 1 : ℕ) * iccExt u c := mul_pos (by positivity) hpos
  push_cast at this h
  linarith

/-- A density functional that vanishes on a continuous `u ≥ 0`, positive at an interior point, is
not the density of any ground state. -/
theorem not_pureVRep_of_dens_zero {ρ : C01 → ℝ} {u : C01} (hu0 : ∀ t, 0 ≤ u t) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hpos : 0 < iccExt u c) (hρ : ρ u = 0) :
    ¬ PureVRep (settingW τ n w hw) ρ := by
  rintro ⟨v, ψ, hψ, -, rfl⟩
  have := dens_pos_of_isGS hψ hu0 hc hpos
  linarith

/-- The same for ground-state ensembles. -/
theorem not_ensVRep_of_dens_zero {ρ : C01 → ℝ} {u : C01} (hu0 : ∀ t, 0 ≤ u t) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hpos : 0 < iccExt u c) (hρ : ρ u = 0) :
    ¬ EnsVRep (settingW τ n w hw) ρ := fun h =>
  not_pureVRep_of_dens_zero hu0 hc hpos hρ ((ensVRep_iff_W_cont ρ).1 h)

/-! ### An explicit counterexample -/

/-- `max(sin 2πt, 0)`: a hump on `[0, ½]`, zero on `[½, 1]`. -/
noncomputable def gHalf (t : ℝ) : ℝ := max (sin (2 * π * t)) 0

lemma lipschitz_gHalf : LipschitzWith ⟨2 * π, by positivity⟩ gHalf := by
  have hl : LipschitzWith ⟨2 * π, by positivity⟩ fun t : ℝ => 2 * π * t :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos two_pi_pos]
      exact le_rfl
  have := (Real.lipschitzWith_sin.comp hl).max_const 0
  have e : (1 : NNReal) * ⟨2 * π, by positivity⟩ = ⟨2 * π, by positivity⟩ := one_mul _
  rw [e] at this
  exact this

lemma continuous_gHalf : Continuous gHalf := lipschitz_gHalf.continuous

lemma gHalf_nonneg (t : ℝ) : 0 ≤ gHalf t := le_max_right _ _

lemma gHalf_eq_zero {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) : gHalf t = 0 := by
  have hs : sin (2 * π * t) ≤ 0 := by
    have := sin_nonneg_of_nonneg_of_le_pi (x := 2 * π * t - π) (by nlinarith [pi_pos])
      (by nlinarith [pi_pos])
    rw [sin_sub_pi] at this
    linarith
  exact max_eq_right hs

lemma gHalf_pos {t : ℝ} (h1 : 0 < t) (h2 : t < 1 / 2) : 0 < gHalf t :=
  lt_max_of_lt_left (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos]))

lemma h10_gHalf : H10 gHalf := by
  refine ⟨(lipschitz_gHalf.lipschitzOnWith).absolutelyContinuousOnInterval, ?_, ?_, ?_⟩
  · simp [gHalf]
  · simp [gHalf]
  · refine Integrable.of_bound ((measurable_deriv gHalf).pow_const 2).aestronglyMeasurable
      ((2 * π) ^ 2) (ae_of_all _ fun t => ?_)
    have hd : ‖deriv gHalf t‖ ≤ 2 * π := norm_deriv_le_of_lipschitz lipschitz_gHalf
    rw [Real.norm_eq_abs] at hd
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2

lemma integral_gHalf_sq_pos : 0 < ∫ t, gHalf t ^ 2 ∂vol01 := by
  have hint : Integrable (fun t => gHalf t ^ 2) vol01 :=
    ((continuous_gHalf.pow 2).integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  rw [integral_pos_iff_support_of_nonneg (fun t => sq_nonneg _) hint]
  have hsub : Ioo (0 : ℝ) (1 / 2) ⊆ Function.support fun t => gHalf t ^ 2 :=
    fun t ht => (pow_pos (gHalf_pos ht.1 ht.2) 2).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioo]
  norm_num

/-- The normalisation constant `c` with `∫ (c gHalf)² = N`. -/
noncomputable def cHalf (n : ℕ) : ℝ := √((n + 1) / ∫ t, gHalf t ^ 2 ∂vol01)

/-- The density functional `ρ(v) = ∫₀¹ v (c gHalf)²`, which vanishes on `[½, 1]`. -/
noncomputable def rhoHalf (n : ℕ) (v : C01) : ℝ := ∫ t, iccExt v t * (cHalf n * gHalf t) ^ 2 ∂vol01

/-- **An `N`-representable density that is not `v`-representable** on `H¹₀`, bosons or fermions,
for every continuous interaction `w`: `rhoHalf` is the density of a normalised `H¹₀` state, but
not of a ground state (nor a ground-state ensemble) of any continuous potential. -/
theorem nrep_not_vrep :
    (∃ ψ ∈ Nst (settingW τ n w hw), dens (settingW τ n w hw) ψ = rhoHalf n) ∧
      ¬ PureVRep (settingW τ n w hw) (rhoHalf n) ∧ ¬ EnsVRep (settingW τ n w hw) (rhoHalf n) := by
  -- the test potential `u(t) = max(t - ½, 0)`
  set u : C01 := ⟨fun t => max ((t : ℝ) - 1 / 2) 0, by fun_prop⟩
  have hu0 : ∀ t, 0 ≤ u t := fun t => le_max_right _ _
  have hc : (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hpos : 0 < iccExt u (3 / 4) := by
    simp only [SturmLiouville.iccExt, u, ContinuousMap.coe_mk]
    rw [projIcc_of_mem _ (by norm_num : (3 / 4 : ℝ) ∈ Icc (0 : ℝ) 1)]
    norm_num
  have hρ : rhoHalf n u = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    rcases le_or_gt t (1 / 2) with h | h
    · have : iccExt u t = 0 := by
        simp only [SturmLiouville.iccExt, u, ContinuousMap.coe_mk]
        rw [projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩]
        exact max_eq_right (by linarith)
      rw [this, zero_mul]
    · rw [gHalf_eq_zero h.le ht.2.le]; simp
  refine ⟨?_, not_pureVRep_of_dens_zero hu0 hc hpos hρ, not_ensVRep_of_dens_zero hu0 hc hpos hρ⟩
  refine (lieb_characterisation (rhoHalf n)).2 ⟨fun t => cHalf n * gHalf t,
    h10_gHalf.const_mul _, ?_, rfl⟩
  have hI := integral_gHalf_sq_pos
  have hN : (0 : ℝ) ≤ (n + 1) / ∫ t, gHalf t ^ 2 ∂vol01 := by positivity
  simp only [mul_pow, cHalf, Real.sq_sqrt hN]
  rw [integral_const_mul, div_mul_cancel₀ _ hI.ne']

end Line

end DFT.Continuum
