/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.KohnSham.Dense
import DFT.Continuum.Line.KohnSham.NotVRep

/-!
# Non-`v`-representable densities are dense too

For `N` bosons or fermions on `H¹₀` with continuous `v` and `w`, the densities that are **not**
`v`-representable (pure or ensemble) are dense, in the dual norm of `C([0, 1])`, among the
`N`-representable ones. Multiply `√ρ` by a smooth cutoff vanishing on `[1 - ε, 1]` and renormalise:
the result is `N`-representable, vanishes on an interval, hence is not `v`-representable
(`not_ensVRep_of_dens_zero`), and is `L¹`-close to `ρ` (dominated convergence).

Together with `dense_pureVRepW`: both the `v`-representable and the non-`v`-representable densities
are dense; with `w = 0` the same for Kohn–Sham.

* `cutoff`: a `C^∞` function, `1` on `(-∞, 1 - 2ε]`, `0` on `[1 - ε, ∞)`.
* `exists_nonvrep_near`: the construction, in terms of `g = √ρ`.
* **`nonvrep_dense`**, **`vrep_nonvrep_dense`**, **`ks_vrep_nonvrep_dense`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-! ### A smooth cutoff -/

/-- `1` on `(-∞, 1 - 2ε]`, `0` on `[1 - ε, ∞)`, smooth. -/
noncomputable def cutoff (ε t : ℝ) : ℝ := smoothTransition ((1 - ε - t) / ε)

lemma contDiff_cutoff (ε : ℝ) : ContDiff ℝ 1 (cutoff ε) :=
  (Real.smoothTransition.contDiff (n := 1)).comp (by fun_prop)

lemma cutoff_nonneg (ε t : ℝ) : 0 ≤ cutoff ε t := smoothTransition.nonneg _

lemma cutoff_le_one (ε t : ℝ) : cutoff ε t ≤ 1 := smoothTransition.le_one _

lemma cutoff_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : 1 - ε ≤ t) : cutoff ε t = 0 :=
  smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma cutoff_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 1 - 2 * ε) : cutoff ε t = 1 :=
  smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)

/-! ### The construction -/

/-- **Near every `N`-representable density there is one that is not `v`-representable.** Given
`g ∈ H¹₀` with `∫ g² = N` and `η > 0`, there is `g' ∈ H¹₀` with `∫ g'² = N`, whose density is within
`η` of that of `g` in the dual norm of `C([0, 1])`, and which is not (ensemble)
`v`-representable. -/
theorem exists_nonvrep_near {g : ℝ → ℝ} (hg : H10 g) (hN : ∫ t, g t ^ 2 ∂vol01 = n + 1) {η : ℝ}
    (hη : 0 < η) :
    ∃ g' : ℝ → ℝ, H10 g' ∧ ∫ t, g' t ^ 2 ∂vol01 = n + 1 ∧
      (∀ u : C01, |∫ t, iccExt u t * g' t ^ 2 ∂vol01 - ∫ t, iccExt u t * g t ^ 2 ∂vol01| ≤ η * ‖u‖) ∧
      ¬ EnsVRep (settingW τ n w hw) (fun u => ∫ t, iccExt u t * g' t ^ 2 ∂vol01) := by
  set G := H10.clamp g
  have hG : H10 G := H10.clamp_H10 hg
  have hGc : Continuous G := H10.continuous_clamp hg
  have hG2 : Integrable (fun t => G t ^ 2) vol01 := H10.int_sq_of_contOn hGc.continuousOn
  have hGN : ∫ t, G t ^ 2 ∂vol01 = n + 1 := by
    rw [← hN]
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
      simp only [G, H10.clamp_eq (Ioo_subset_Icc_self ht)]
  have hNp : (0 : ℝ) < n + 1 := by positivity
  -- the cutoffs `ε_k = 1 / (k + 3)`
  set e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 3)
  have he : ∀ k, 0 < e k := fun k => by positivity
  have he0 : Tendsto e atTop (𝓝 0) :=
    squeeze_zero (fun k => (he k).le) (fun k => one_div_le_one_div_of_le (by positivity)
      (by linarith)) tendsto_one_div_add_atTop_nhds_zero_nat
  set h : ℕ → ℝ → ℝ := fun k t => G t * cutoff (e k) t
  set F : ℕ → ℝ → ℝ := fun k t => G t ^ 2 - h k t ^ 2
  have hF0 : ∀ k t, 0 ≤ F k t ∧ F k t ≤ G t ^ 2 := fun k t => by
    have c0 := cutoff_nonneg (e k) t
    have c1 := cutoff_le_one (e k) t
    have : h k t ^ 2 = G t ^ 2 * cutoff (e k) t ^ 2 := by simp only [h]; ring
    simp only [F, this]
    have hc2 : cutoff (e k) t ^ 2 ≤ 1 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (G t), sq_nonneg (cutoff (e k) t)]
  have hhc : ∀ k, Continuous (h k) := fun k => hGc.mul (contDiff_cutoff _).continuous
  have hFm : ∀ k, AEStronglyMeasurable (F k) vol01 := fun k =>
    ((hGc.pow 2).sub ((hhc k).pow 2)).aestronglyMeasurable
  have hFlim : Tendsto (fun k => ∫ t, F k t ∂vol01) atTop (𝓝 0) := by
    have hpt : ∀ᵐ t ∂vol01, Tendsto (fun k => F k t) atTop (𝓝 0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpos : 0 < (1 - t) / 2 := by linarith [ht.2]
      have hev := (tendsto_order.1 he0).2 _ hpos
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with k hk
      simp only [F, h, cutoff_eq_one (he k) (by linarith : t ≤ 1 - 2 * e k), mul_one, sub_self]
    have := tendsto_integral_of_dominated_convergence (fun t => G t ^ 2) hFm hG2
      (fun k => ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 k t).1]; exact (hF0 k t).2) hpt
    simpa using this
  set δ := min (η / 2) ((n + 1 : ℝ) / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  obtain ⟨K, hK⟩ := ((tendsto_order.1 hFlim).2 δ hδ).exists
  set ε := e K
  set H := h K
  have hH2 : Integrable (fun t => H t ^ 2) vol01 := H10.int_sq_of_contOn (hhc K).continuousOn
  set I := ∫ t, H t ^ 2 ∂vol01
  have hFK : ∫ t, F K t ∂vol01 = (n + 1) - I := by
    simp only [F]; rw [integral_sub hG2 hH2, hGN]
  have hFK0 : 0 ≤ ∫ t, F K t ∂vol01 := integral_nonneg fun t => (hF0 K t).1
  have hI : (n + 1 : ℝ) / 2 ≤ I := by
    have := min_le_right (η / 2) ((n + 1 : ℝ) / 2); linarith
  have hIpos : 0 < I := by linarith
  have hIN : I ≤ n + 1 := by linarith
  set c := √((n + 1) / I)
  have hc2 : c ^ 2 = (n + 1) / I := Real.sq_sqrt (by positivity)
  set g' : ℝ → ℝ := fun t => c * H t
  have hHH : H10 H := H10.mul_C1 hG hGc (contDiff_cutoff ε)
  refine ⟨g', hHH.const_mul c, ?_, fun u => ?_, ?_⟩
  · simp only [g', mul_pow]; rw [integral_const_mul, hc2, div_mul_cancel₀ _ hIpos.ne']
  · -- dual-norm estimate
    have hgG : ∫ t, iccExt u t * g t ^ 2 ∂vol01 = ∫ t, iccExt u t * G t ^ 2 ∂vol01 :=
      setIntegral_congr_fun measurableSet_Ioo fun t ht => by
        simp only [G, H10.clamp_eq (Ioo_subset_Icc_self ht)]
    have hbd : ∀ f : ℝ → ℝ, Continuous f → Integrable (fun t => iccExt u t * f t) vol01 := fun f hf =>
      ((((continuous_iccExt u).mul hf).continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioo_subset_Icc_self)
    have hg'c : Continuous fun t => g' t ^ 2 := (continuous_const.mul (hhc K)).pow 2
    rw [hgG, ← integral_sub (hbd (fun t => g' t ^ 2) hg'c) (hbd (fun t => G t ^ 2) (hGc.pow 2)),
      ← Real.norm_eq_abs]
    have hpt : ∀ t, ‖iccExt u t * g' t ^ 2 - iccExt u t * G t ^ 2‖ ≤
        ‖u‖ * ((c ^ 2 - 1) * H t ^ 2 + F K t) := fun t => by
      have e1 : iccExt u t * g' t ^ 2 - iccExt u t * G t ^ 2 =
          iccExt u t * ((c ^ 2 - 1) * H t ^ 2 - F K t) := by
        simp only [g', F, H, mul_pow]; ring
      have hc1 : 0 ≤ c ^ 2 - 1 := by
        rw [hc2, sub_nonneg, le_div_iff₀ hIpos, one_mul]; exact hIN
      rw [e1, norm_mul, Real.norm_eq_abs]
      refine mul_le_mul (abs_ext_le u t) ?_ (norm_nonneg _) (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [(hF0 K t).1, sq_nonneg (H t)]
    have hFi : Integrable (F K) vol01 := hG2.sub hH2
    have hint : Integrable (fun t => ‖u‖ * ((c ^ 2 - 1) * H t ^ 2 + F K t)) vol01 :=
      ((hH2.const_mul _).add hFi).const_mul _
    refine (norm_integral_le_of_norm_le hint (ae_of_all _ hpt)).trans ?_
    rw [integral_const_mul, integral_add (hH2.const_mul _) hFi, integral_const_mul]
    change ‖u‖ * ((c ^ 2 - 1) * I + ∫ t, F K t ∂vol01) ≤ η * ‖u‖
    rw [hc2, sub_mul, div_mul_cancel₀ _ hIpos.ne', one_mul]
    have : (n + 1 : ℝ) - I + ∫ t, F K t ∂vol01 ≤ η := by
      have := min_le_left (η / 2) ((n + 1 : ℝ) / 2); linarith
    nlinarith [norm_nonneg u]
  · -- vanishing on `[1 - ε, 1]`: not `v`-representable
    have hε := he K
    have hε1 : ε < 1 := by
      simp only [ε, e]; rw [div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    set u0 : C01 := ⟨fun t => max ((t : ℝ) - (1 - ε)) 0, by fun_prop⟩
    have hu0 : ∀ t, 0 ≤ u0 t := fun t => le_max_right _ _
    have hc0 : (1 - ε / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hpos : 0 < iccExt u0 (1 - ε / 2) := by
      simp only [SturmLiouville.iccExt, u0, ContinuousMap.coe_mk]
      rw [projIcc_of_mem _ (Ioo_subset_Icc_self hc0)]
      exact lt_max_of_lt_left (by linarith)
    refine not_ensVRep_of_dens_zero hu0 hc0 hpos ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    rcases le_or_gt t (1 - ε) with h1 | h1
    · have : iccExt u0 t = 0 := by
        simp only [SturmLiouville.iccExt, u0, ContinuousMap.coe_mk]
        rw [projIcc_of_mem _ (Ioo_subset_Icc_self ht)]
        exact max_eq_right (by linarith)
      rw [this, zero_mul]
    · simp [g', H, h, cutoff_eq_zero hε h1.le]

/-! ### Density -/

/-- **Non-`v`-representable densities are dense**: every `N`-representable density is, within any
`η > 0` in the dual norm of `C([0, 1])`, the density of a normalised `H¹₀` state that is not
(ensemble) `v`-representable. -/
theorem nonvrep_dense {φ : Cfg n → ℝ} (hφ : φ ∈ Nst (settingW τ n w hw)) {η : ℝ} (hη : 0 < η) :
    ∃ ψ, ∃ hψ : ψ ∈ Nst (settingW τ n w hw), ‖densLW hψ - densLW hφ‖ ≤ η ∧
      ¬ EnsVRep (settingW τ n w hw) (dens (settingW τ n w hw) ψ) := by
  obtain ⟨g, hg, hgN, hρ⟩ := (lieb_characterisation (dens (settingW τ n w hw) φ)).1 ⟨φ, hφ, rfl⟩
  obtain ⟨g', hg', hg'N, hclose, hnot⟩ :=
    exists_nonvrep_near (τ := τ) (w := w) (hw := hw) hg hgN hη
  obtain ⟨ψ, hψ, hψd⟩ := (lieb_characterisation (τ := τ) (w := w) (hw := hw)
    (fun u => ∫ t, iccExt u t * g' t ^ 2 ∂vol01)).2 ⟨g', hg', hg'N, rfl⟩
  refine ⟨ψ, hψ, ContinuousLinearMap.opNorm_le_bound _ hη.le fun u => ?_, by rwa [hψd]⟩
  change ‖densLW hψ u - densLW hφ u‖ ≤ η * ‖u‖
  rw [densLW_apply, densLW_apply, hψd, hρ, Real.norm_eq_abs]
  exact hclose u

/-- **Both the `v`-representable and the non-`v`-representable densities are dense** among the
`N`-representable ones, in the dual norm of `C([0, 1])`. -/
theorem vrep_nonvrep_dense {φ : Cfg n → ℝ} (hφ : φ ∈ Nst (settingW τ n w hw)) {η : ℝ}
    (hη : 0 < η) :
    (∃ (v : C01) (ρ' : StrongDual ℝ C01), ‖ρ' - densLW hφ‖ ≤ η ∧
        PureDens (settingW τ n w hw) v ρ') ∧
      ∃ ψ, ∃ hψ : ψ ∈ Nst (settingW τ n w hw), ‖densLW hψ - densLW hφ‖ ≤ η ∧
        ¬ EnsVRep (settingW τ n w hw) (dens (settingW τ n w hw) ψ) :=
  ⟨dense_pureVRepW_of_nst hφ hη, nonvrep_dense hφ hη⟩

/-- **Kohn–Sham**: both the Kohn–Sham `v`-representable and the non-Kohn–Sham-`v`-representable
densities are dense among the `N`-representable ones. -/
theorem ks_vrep_nonvrep_dense {φ : Cfg n → ℝ} (hφ : φ ∈ Nst (ksS τ n)) {η : ℝ} (hη : 0 < η) :
    (∃ (vs : C01) (ρ' : StrongDual ℝ C01), ‖ρ' - densLW hφ‖ ≤ η ∧ PureDens (ksS τ n) vs ρ') ∧
      ∃ ψ, ∃ hψ : ψ ∈ Nst (ksS τ n), ‖densLW hψ - densLW hφ‖ ≤ η ∧
        ¬ KSRep τ n (dens (ksS τ n) ψ) := by
  obtain ⟨h1, ψ, hψ, hn, hnot⟩ := vrep_nonvrep_dense hφ hη
  exact ⟨h1, ψ, hψ, hn, fun h => hnot ((ensVRep_iff_W_cont _).2 h)⟩

end DFT.Continuum.Line
