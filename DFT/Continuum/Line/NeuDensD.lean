/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeuEL

/-!
# The derivative of a marginal

If `p` has a weak derivative `G ∈ L²` in the first coordinate (Neumann walls), then the marginal
`mF p (t) = ∫ p(t, y) dy` has weak derivative `mF G` on `(0, 1)` (`marg_wd`). Hence an element
`e ∈ H1E` with the integrals of `N mF p` has `e' = N mF G` (`snd_marg`), and
`‖e‖² ≤ 2N² (∫ p² + ∫ G²)` (`norm_sq_le_marg`). This controls `v(ρ)` for `v ∈ H⁻¹` by the `L²`
norm of the derivative of `p`, the input of Moser's estimate for `H⁻¹` potentials.

* `Test1`, `ae_eq_zero_of_test1`, `ae_eq_of_int_pot`: fundamental lemmas on `(0, 1)`.
* `integral_fnE_mul_deriv`: integration by parts for `fnE e`; `snd_ae_eq`.
* `mF`, `integrable_mF`, `sq_mF_le`, `integral_sq_mF_le`, `marg_wd`.
* `int_mF`: `∫ u N mF F = ∫ Σ_k u(x_k) F` for symmetric `F`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### Fundamental lemmas on `(0, 1)` -/

/-- `C¹` test functions vanishing at `0` and `1`. -/
def Test1 (χ : ℝ → ℝ) : Prop := ContDiff ℝ 1 χ ∧ χ 0 = 0 ∧ χ 1 = 0

lemma ae_eq_zero_of_test1 {f : ℝ → ℝ} (hf : Integrable f μ1)
    (h : ∀ χ, Test1 χ → ∫ t, f t * χ t ∂μ1 = 0) : f =ᵐ[μ1] 0 := by
  have hloc : LocallyIntegrableOn f (Ioo (0 : ℝ) 1) volume :=
    (show IntegrableOn f (Ioo (0 : ℝ) 1) volume from hf).locallyIntegrableOn
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Ioo (0 : ℝ) 1)
    (μ := volume) (f := f) isOpen_Ioo hloc
    (fun φ hφ _ (hsub : tsupport φ ⊆ Ioo (0 : ℝ) 1) => ?_)
  · exact (ae_restrict_iff' measurableSet_Ioo).2 hae
  · have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h0 => (lt_irrefl _ (hsub h0).1)
    have h1 : φ 1 = 0 := image_eq_zero_of_notMem_tsupport fun h1 => (lt_irrefl _ (hsub h1).2)
    have h2 : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have := h φ ⟨hφ.of_le h2, h0, h1⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (0 : ℝ) 1)]
    · simpa [smul_eq_mul, mul_comm] using this
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hsub h'), zero_smul]

/-- A continuous function as an element of `C([0, 1])`. -/
noncomputable def potOf (χ : ℝ → ℝ) (hχ : Continuous χ) : Pot :=
  ⟨fun t => χ t, hχ.comp continuous_subtype_val⟩

lemma ext_potOf {χ : ℝ → ℝ} (hχ : Continuous χ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ext (potOf χ hχ) t = χ t := by
  simp [Box.ext, potOf, projIcc_of_mem _ ht]

lemma integrable_ext_mul_of {f : ℝ → ℝ} (hf : Integrable f μ1) (u : Pot) :
    Integrable (fun t => ext u t * f t) μ1 :=
  hf.bdd_mul (continuous_ext u).aestronglyMeasurable
    (ae_of_all _ fun t => by simpa using abs_ext_le u t)

lemma integral_ext_potOf {f : ℝ → ℝ} {χ : ℝ → ℝ} (hχ : Continuous χ) :
    ∫ t, ext (potOf χ hχ) t * f t ∂μ1 = ∫ t, f t * χ t ∂μ1 :=
  setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    rw [ext_potOf hχ (Ioo_subset_Icc_self ht), mul_comm]

lemma integrable_mul_cont1 {f : ℝ → ℝ} (hf : Integrable f μ1) {χ : ℝ → ℝ}
    (hχ : Continuous χ) : Integrable (fun t => f t * χ t) μ1 := by
  have h := integrable_ext_mul_of hf (potOf χ hχ)
  refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_)
  show ext (potOf χ hχ) t * f t = f t * χ t
  rw [ext_potOf hχ (Ioo_subset_Icc_self ht), mul_comm]

/-- An integrable function on `(0, 1)` is determined by its integrals against `C([0, 1])`. -/
lemma ae_eq_of_int_pot {f g : ℝ → ℝ} (hf : Integrable f μ1) (hg : Integrable g μ1)
    (h : ∀ u : Pot, ∫ t, ext u t * f t ∂μ1 = ∫ t, ext u t * g t ∂μ1) : f =ᵐ[μ1] g := by
  have hz := ae_eq_zero_of_test1 (hf.sub hg) fun χ hχ => by
    have e := h (potOf χ hχ.1.continuous)
    rw [integral_ext_potOf, integral_ext_potOf] at e
    rw [show (fun t => (f - g) t * χ t) = fun t => f t * χ t - g t * χ t from
        funext fun t => by simp only [Pi.sub_apply]; ring,
      integral_sub (integrable_mul_cont1 hf hχ.1.continuous)
        (integrable_mul_cont1 hg hχ.1.continuous), e, sub_self]
  filter_upwards [hz] with t ht
  simpa [sub_eq_zero] using ht

/-! ### Integration by parts for `fnE e` -/

lemma integral_fnE_mul_deriv (e : H1E) {χ : ℝ → ℝ} (hχ : Test1 χ) :
    ∫ t, fnE e t * deriv χ t ∂μ1 = -∫ t, (e.snd : ℝ → ℝ) t * χ t ∂μ1 := by
  have hAC := (h1N_fnE e).1
  have hχAC : AbsolutelyContinuousOnInterval χ 0 1 :=
    hχ.1.contDiffOn.absolutelyContinuousOnInterval
  have ibp := hAC.integral_mul_deriv_eq_deriv_mul hχAC
  rw [hχ.2.1, hχ.2.2, mul_zero, mul_zero, sub_zero, zero_sub] at ibp
  rw [integral_mu1, integral_mu1, ibp]
  congr 1
  rw [← integral_mu1, ← integral_mu1]
  refine integral_congr_ae ?_
  filter_upwards [ae_deriv_prim e.snd] with t ht
  rw [deriv_fnE, ht]

/-- The derivative part of `e` is the weak derivative of `fnE e`. -/
lemma snd_ae_eq {e : H1E} {g : ℝ → ℝ} (hg : Integrable g μ1)
    (h : ∀ χ, Test1 χ → ∫ t, fnE e t * deriv χ t ∂μ1 = -∫ t, g t * χ t ∂μ1) :
    (e.snd : ℝ → ℝ) =ᵐ[μ1] g := by
  have hs : Integrable (e.snd : ℝ → ℝ) μ1 := integrable_L2I e.snd
  have hz := ae_eq_zero_of_test1 (hs.sub hg) fun χ hχ => by
    have h1 := h χ hχ
    rw [integral_fnE_mul_deriv e hχ, neg_inj] at h1
    rw [show (fun t => ((e.snd : ℝ → ℝ) - g) t * χ t) =
        fun t => (e.snd : ℝ → ℝ) t * χ t - g t * χ t from funext fun t => by
      simp only [Pi.sub_apply]; ring,
      integral_sub (integrable_mul_cont1 hs hχ.1.continuous)
        (integrable_mul_cont1 hg hχ.1.continuous), h1, sub_self]
  filter_upwards [hz] with t ht
  simpa [sub_eq_zero] using ht

/-! ### Marginals -/

/-- The marginal `∫ F(t, y) dy`. -/
noncomputable def mF (F : Cfg n → ℝ) (t : ℝ) : ℝ := ∫ y in Cube' n, F (Fin.cons t y)

lemma integrable_mF {F : Cfg n → ℝ} (hF : Integrable F (μN n)) : Integrable (mF F) μ1 :=
  (integrable_cons_prod hF).integral_prod_left

lemma sq_integral_le_of_prob {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] (hν : ν univ = 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f ν) (hf2 : Integrable (fun y => f y ^ 2) ν) :
    (∫ y, f y ∂ν) ^ 2 ≤ ∫ y, f y ^ 2 ∂ν := by
  set m := ∫ y, f y ∂ν
  have h0 : 0 ≤ ∫ y, (f y - m) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have i1 : Integrable (fun y => f y ^ 2 - 2 * m * f y) ν := hf2.sub (hf.const_mul _)
  have e : ∫ y, (f y - m) ^ 2 ∂ν = ∫ y, f y ^ 2 ∂ν - 2 * m * m + m ^ 2 := by
    calc ∫ y, (f y - m) ^ 2 ∂ν = ∫ y, ((f y ^ 2 - 2 * m * f y) + m ^ 2) ∂ν := by
          congr 1; funext y; ring
      _ = ∫ y, (f y ^ 2 - 2 * m * f y) ∂ν + ∫ _y, m ^ 2 ∂ν :=
          integral_add i1 (integrable_const _)
      _ = _ := by
          rw [integral_sub hf2 (hf.const_mul _), integral_const_mul, integral_const]
          simp [measureReal_def, hν, m]
  nlinarith

/-- `(∫ G(t, y) dy)² ≤ ∫ G(t, y)² dy` for a.e. `t`. -/
lemma sq_mF_le {G : Cfg n → ℝ} (hG : MemLp G 2 (μN n)) :
    ∀ᵐ t ∂μ1, mF G t ^ 2 ≤ mF (fun x => G x ^ 2) t := by
  have : IsFiniteMeasure (volume.restrict (Cube' n)) :=
    isFiniteMeasure_restrict.2 (by rw [volume_cube']; exact ENNReal.one_ne_top)
  have h1 := (integrable_cons_prod (hG.integrable one_le_two)).prod_right_ae
  have h2 := (integrable_cons_prod (int_sq hG)).prod_right_ae
  filter_upwards [h1, h2] with t ht1 ht2
  exact sq_integral_le_of_prob (by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
    volume_cube']) ht1 ht2

lemma integral_sq_mF_le {G : Cfg n → ℝ} (hG : MemLp G 2 (μN n)) :
    Integrable (fun t => mF G t ^ 2) μ1 ∧ ∫ t, mF G t ^ 2 ∂μ1 ≤ ∫ x, G x ^ 2 ∂μN n := by
  have hm := integrable_mF (int_sq hG)
  have hi : Integrable (fun t => mF G t ^ 2) μ1 :=
    hm.mono' ((integrable_mF (hG.integrable one_le_two)).aestronglyMeasurable.pow 2)
      (by filter_upwards [sq_mF_le hG] with t ht
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact ht)
  refine ⟨hi, (integral_mono_ae hi hm (sq_mF_le hG)).trans (le_of_eq ?_)⟩
  rw [integral_cube_cons' (int_sq hG)]
  rfl

lemma dk_coord0 {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (x : Cfg n) :
    dk 0 (fun x : Cfg n => χ (x 0)) x = deriv χ (x 0) := by
  have h : HasFDerivAt (fun x : Cfg n => χ (x 0))
      ((deriv χ (x 0)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)
      x :=
    (hχ (x 0)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply 0 x)
  simp [dk, h.fderiv]

/-- **The marginal of `F` has weak derivative the marginal of `∂₀F`.** -/
theorem marg_wd {F G : Cfg n → ℝ} (hF : MemLp F 2 (μN n)) (hG : IsWDN 0 F G) {χ : ℝ → ℝ}
    (hχ : Test1 χ) :
    ∫ t, mF F t * deriv χ t ∂μ1 = -∫ t, mF G t * χ t ∂μ1 := by
  have hφ : TestN 0 (fun x : Cfg n => χ (x 0)) :=
    ⟨hχ.1.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0).contDiff,
      fun x hx => by
      rcases hx with h | h <;> simp [h, hχ.2.1, hχ.2.2]⟩
  have h := hG.2 _ hφ
  simp only [dk_coord0 (hχ.1.differentiable one_ne_zero)] at h
  have hdχ : Continuous (deriv χ) := hχ.1.continuous_deriv le_rfl
  have i1 : Integrable (fun x : Cfg n => F x * deriv χ (x 0)) (μN n) :=
    int_mul_cont hF (hdχ.comp (continuous_apply 0))
  have i2 : Integrable (fun x : Cfg n => G x * χ (x 0)) (μN n) :=
    int_mul_cont hG.1 (hχ.1.continuous.comp (continuous_apply 0))
  rw [integral_cube_cons' i1, integral_cube_cons' i2] at h
  simp only [Fin.cons_zero, integral_mul_const] at h
  exact h

/-! ### Elements of `H1E` given by marginals -/

/-- If `e ∈ H1E` has the integrals of `N mF p`, then `fnE e = N mF p` and `e' = N mF (∂₀p)`. -/
theorem snd_marg {e : H1E} {p G : Cfg n → ℝ} (hp : MemLp p 2 (μN n)) (hG : IsWDN 0 p G)
    (he : ∀ u : Pot, ∫ t, ext u t * ext (evE e) t ∂μ1 =
      ∫ t, ext u t * ((n + 1) * mF p t) ∂μ1) :
    (fnE e =ᵐ[μ1] fun t => (n + 1) * mF p t) ∧
      (e.snd : ℝ → ℝ) =ᵐ[μ1] fun t => (n + 1) * mF G t := by
  have hpi : Integrable (fun t => (n + 1 : ℝ) * mF p t) μ1 :=
    (integrable_mF (hp.integrable one_le_two)).const_mul _
  have hGi : Integrable (fun t => (n + 1 : ℝ) * mF G t) μ1 :=
    (integrable_mF (hG.1.integrable one_le_two)).const_mul _
  have hfn : ∀ u : Pot, ∫ t, ext u t * ext (evE e) t ∂μ1 = ∫ t, ext u t * fnE e t ∂μ1 :=
    fun u => setIntegral_congr_fun measurableSet_Ioo fun t ht => by
      rw [ext_evE (Ioo_subset_Icc_self ht)]
  have hfi : Integrable (fnE e) μ1 := ((h1N_fnE e).memLp).integrable one_le_two
  refine ⟨ae_eq_of_int_pot hfi hpi fun u => by rw [← hfn, he], snd_ae_eq hGi fun χ hχ => ?_⟩
  have hdχ : Continuous (deriv χ) := hχ.1.continuous_deriv le_rfl
  have h1 := he (potOf _ hdχ)
  rw [hfn, integral_ext_potOf, integral_ext_potOf] at h1
  rw [h1]
  have h2 := marg_wd hp hG hχ
  simp only [mul_assoc, integral_const_mul, h2]
  ring

/-- **`‖e‖² ≤ 2N² (∫ p² + ∫ (∂₀p)²)`** for `e` with the integrals of `N mF p`. -/
theorem norm_sq_le_marg {e : H1E} {p G : Cfg n → ℝ} (hp : MemLp p 2 (μN n)) (hG : IsWDN 0 p G)
    (he : ∀ u : Pot, ∫ t, ext u t * ext (evE e) t ∂μ1 =
      ∫ t, ext u t * ((n + 1) * mF p t) ∂μ1) :
    ‖e‖ ^ 2 ≤ 2 * (n + 1) ^ 2 * (∫ x, p x ^ 2 ∂μN n + ∫ x, G x ^ 2 ∂μN n) := by
  obtain ⟨hf, hs⟩ := snd_marg hp hG he
  have hsnd : ‖e.snd‖ ^ 2 ≤ (n + 1) ^ 2 * ∫ x, G x ^ 2 ∂μN n := by
    rw [norm_sq_L2I]
    have hG2 := integral_sq_mF_le hG.1
    calc ∫ t, (e.snd : ℝ → ℝ) t ^ 2 ∂μ1 = ∫ t, (n + 1 : ℝ) ^ 2 * mF G t ^ 2 ∂μ1 :=
          integral_congr_ae (by filter_upwards [hs] with t ht; rw [ht]; ring)
      _ = (n + 1) ^ 2 * ∫ t, mF G t ^ 2 ∂μ1 := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hG2.2 (by positivity)
  have hnrm : nrmE e ≤ (n + 1) ^ 2 * ∫ x, p x ^ 2 ∂μN n := by
    have hp2 := integral_sq_mF_le hp
    calc nrmE e = ∫ t, (n + 1 : ℝ) ^ 2 * mF p t ^ 2 ∂μ1 :=
          integral_congr_ae (by filter_upwards [hf] with t ht; rw [ht]; ring)
      _ = (n + 1) ^ 2 * ∫ t, mF p t ^ 2 ∂μ1 := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hp2.2 (by positivity)
  have hfst := sq_fst_le e
  rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  nlinarith

/-- `∫ u N mF F = ∫ Σ_k u(x_k) F` for exchange-symmetric integrable `F`. -/
theorem int_mF {F : Cfg n → ℝ} (hF : Integrable F (μN n))
    (hsym : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ᵐ x ∂μN n, F (pm σ x) = F x) (v : Pot) :
    ∫ t, ext v t * ((n + 1) * mF F t) ∂μ1 = ∫ x, (∑ k, ext v (x k)) * F x ∂μN n := by
  have hv := continuous_ext v
  have hint : ∀ k : Fin (n + 1), Integrable (fun x => ext v (x k) * F x) (μN n) := by
    intro k
    obtain ⟨C, hC⟩ := ae_bound_cont (n := n) (hv.comp (continuous_apply k))
    exact hF.bdd_mul (hv.comp (continuous_apply k)).aestronglyMeasurable hC
  have swapsq : ∀ k : Fin (n + 1), ∫ x, ext v (x k) * F x ∂μN n =
      ∫ x, ext v (x 0) * F x ∂μN n := by
    intro k
    rw [← integral_pm (Equiv.swap 0 k) (fun x => ext v (x 0) * F x)]
    refine integral_congr_ae ?_
    filter_upwards [hsym (Equiv.swap 0 k)] with x hx
    simp only [pm, Equiv.swap_apply_left] at hx ⊢
    rw [hx]
  have hpt : (fun x : Cfg n => (∑ k, ext v (x k)) * F x) =
      fun x => ∑ k, ext v (x k) * F x := by
    funext x; rw [Finset.sum_mul]
  rw [hpt, integral_finsetSum (f := fun k x => ext v (x k) * F x) _ fun k _ => hint k]
  simp only [swapsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_cube_cons' (hint 0), ← integral_const_mul]
  refine (setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_).symm
  simp only [Fin.cons_zero, mF, ← integral_const_mul]
  push_cast
  congr 1; funext y; ring

end DFT.Continuum.Line
