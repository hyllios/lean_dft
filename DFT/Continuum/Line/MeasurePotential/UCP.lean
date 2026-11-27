/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.Trap

/-!
# Ground states of measure potentials have no interior zeros

Here the potential is a signed measure `ν = μ₊ - μ₋`, with `μ±` finite measures on `[0, 1]`
(`nuOf`), acting on `C([0, 1])` by `h ↦ ∫ h dμ₊ - ∫ h dμ₋`.

* `integral_mul_eq_neg` (Fubini): `∫ ψ φ dρ = -∫ φ'(t) G_ρ(t) dt`, `G_ρ(t) = ∫_{x < t} ψ dρ`.
* `ae_eq_const_of_orth` (du Bois-Reymond): `h ∈ L²` with `∫ h φ' = 0` for all `φ ∈ H¹₀` is
  a.e. constant.
* `deriv_ae_eq_R`: a solution of the weak equation has `ψ' = R` a.e., where
  `R = c + G₊ - G₋ - E G_L` (`G_L` for Lebesgue measure on `[0, 1]`).
* `R_zero_of_min`: at an interior zero of a nonnegative solution, `R = 0`.
* `eq_zero_of_R_zero`: if `ψ(a) = R(a) = 0` then `ψ ≡ 0` on `[0, 1]`. On an interval of length
  `δ = 1 / (2Λ + 2)` (`Λ` the total mass of `μ₊ + μ₋ + |E| dt`), `sup |ψ| ≤ δ Λ sup |ψ|`; repeat.
* **`gs_ne_zero`**: a ground state of a measure potential has no zero in `(0, 1)`;
  **`gs_pos_or_neg`**: it has a strict sign there.
* **`vrepM_meas_iff`**: the `N = 1` characterisation. A normalised `ρ` is the ground-state density
  of a measure potential iff `ρ = g²`, `g ∈ H¹₀` positive on `(0, 1)`, and `-g'' + ν g = E g` weakly
  for some measure `ν` and some `E`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

/-! ### Measure potentials -/

/-- `ρ` is a finite measure carried by `[0, 1]`. -/
class IsMeas01 (ρ : Measure ℝ) : Prop extends IsFiniteMeasure ρ where
  compl_zero : ρ (Icc (0 : ℝ) 1)ᶜ = 0

instance : IsMeas01 (volume.restrict (Icc (0 : ℝ) 1)) where
  compl_zero := by rw [Measure.restrict_apply' measurableSet_Icc]; simp

lemma IsMeas01.ae_mem (ρ : Measure ℝ) [IsMeas01 ρ] : ∀ᵐ x ∂ρ, x ∈ Icc (0 : ℝ) 1 :=
  measure_eq_zero_iff_ae_notMem.1 (IsMeas01.compl_zero (ρ := ρ)) |>.mono fun _ h => not_not.1 h

lemma integrable_ext (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : C01) : Integrable (SturmLiouville.iccExt h) ρ :=
  Integrable.of_bound (continuous_iccExt h).aestronglyMeasurable ‖h‖
    (ae_of_all _ fun x => by simpa [SturmLiouville.iccExt] using h.norm_coe_le_norm _)

/-- `h ↦ ∫ h dρ` on `C([0, 1])`. -/
noncomputable def intCLM (ρ : Measure ℝ) [IsFiniteMeasure ρ] : PotM :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ x, SturmLiouville.iccExt h x ∂ρ
      map_add' := fun h h' => by
        rw [← integral_add (integrable_ext ρ h) (integrable_ext ρ h')]; rfl
      map_smul' := fun c h => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]; rfl }
    (ρ.real univ) fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const
        (ae_of_all _ fun x => by simpa [SturmLiouville.iccExt] using h.norm_coe_le_norm _)

lemma intCLM_apply (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h : C01) :
    intCLM ρ h = ∫ x, SturmLiouville.iccExt h x ∂ρ := rfl

/-- The measure potential `μ₊ - μ₋`. -/
noncomputable def nuOf (μp μm : Measure ℝ) [IsFiniteMeasure μp] [IsFiniteMeasure μm] : PotM :=
  intCLM μp - intCLM μm

lemma intCLM_mulP (ρ : Measure ℝ) [IsMeas01 ρ] {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) :
    intCLM ρ (mulP hψ hφ) = ∫ x, ψ x * φ x ∂ρ := by
  rw [intCLM_apply]
  refine integral_congr_ae ((IsMeas01.ae_mem ρ).mono fun x hx => ?_)
  rw [SturmLiouville.iccExt, projIcc_of_mem _ hx, mulP_apply]

/-! ### Fubini -/

/-- `G_ρ(t) = ∫_{x < t} ψ dρ`. -/
noncomputable def Gρ (ρ : Measure ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in Iio t, ψ x ∂ρ

lemma phi_eq_neg {φ : ℝ → ℝ} (hφ : H10 φ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    φ x = -∫ t, (Ioi x).indicator (deriv φ) t ∂vol01 := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    show Ioi x ∩ Ioo (0 : ℝ) 1 = Ioo x 1 by
      ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [hx.1], h3⟩,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2]
  have hac : AbsolutelyContinuousOnInterval φ x 1 := hφ.1.mono (by
    rw [uIcc01, uIcc_of_le hx.2]; exact Icc_subset_Icc hx.1 le_rfl)
  rw [hac.integral_deriv_eq_sub, hφ.2.2.1]; ring

lemma integrable_deriv_mu1 {φ : ℝ → ℝ} (hφ : H10 φ) : Integrable (deriv φ) vol01 :=
  (memLp_deriv hφ).integrable one_le_two

/-- **Fubini**: `∫ ψ φ dρ = -∫ φ'(t) G_ρ(t) dt` for `φ ∈ H¹₀`. -/
theorem integral_mul_eq_neg (ρ : Measure ℝ) [IsMeas01 ρ] {ψ : ℝ → ℝ} (hψc : Continuous ψ)
    {φ : ℝ → ℝ} (hφ : H10 φ) :
    ∫ x, ψ x * φ x ∂ρ = -∫ t, deriv φ t * Gρ ρ ψ t ∂vol01 := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hψc.continuousOn
  have hψi : Integrable ψ ρ := Integrable.of_bound hψc.aestronglyMeasurable B
    ((IsMeas01.ae_mem ρ).mono fun x hx => hB x hx)
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 < p.2}.indicator fun p => ψ p.1 * deriv φ p.2
  have hF : Integrable F (ρ.prod vol01) :=
    (hψi.mul_prod (integrable_deriv_mu1 hφ)).indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have e1 : ∀ x ∈ Icc (0 : ℝ) 1, ψ x * φ x = -∫ t, F (x, t) ∂vol01 := fun x hx => by
    rw [phi_eq_neg hφ hx, mul_neg, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [F, indicator, mem_Ioi, mem_ofPred_eq]
    split_ifs <;> simp
  have e2 : ∀ t, ∫ x, F (x, t) ∂ρ = deriv φ t * Gρ ρ ψ t := fun t => by
    rw [Gρ, ← integral_indicator measurableSet_Iio, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [F, indicator, mem_Iio, mem_ofPred_eq]
    split_ifs <;> ring
  rw [integral_congr_ae ((IsMeas01.ae_mem ρ).mono fun x hx => e1 x hx), integral_neg,
    integral_integral_swap (f := fun x t => F (x, t)) hF]
  simp only [e2]

/-! ### du Bois-Reymond -/

/-- **du Bois-Reymond**: `h ∈ L²(0, 1)` with `∫ h φ' = 0` for all `φ ∈ H¹₀` is a.e. constant. -/
theorem ae_eq_const_of_orth {h : ℝ → ℝ} (hm : MemLp h 2 vol01)
    (h0 : ∀ φ (_hφ : H10 φ), ∫ t, deriv φ t * h t ∂vol01 = 0) :
    h =ᵐ[vol01] fun _ => ∫ t, h t ∂vol01 := by
  set m := ∫ t, h t ∂vol01
  have hmc : MemLp (fun t => h t - m) 2 vol01 := hm.sub (memLp_const m)
  set f : L2I := hmc.toLp _
  have hf : (f : ℝ → ℝ) =ᵐ[vol01] fun t => h t - m := MemLp.coeFn_toLp hmc
  have hi : Integrable h vol01 := hm.integrable one_le_two
  have h1 : prim f 1 = 0 := by
    rw [prim, integral_congr_mu1 hf ⟨zero_le_one, le_rfl⟩, ← integral_vol01,
      integral_sub hi (integrable_const m)]
    simp [m]
  have hd : deriv (prim f) =ᵐ[vol01] fun t => h t - m := by
    have hd := (intervalIntegrable_of_mu1 (integrable_L2I f)
      ⟨zero_le_one, le_rfl⟩).ae_hasDerivAt_integral
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo, hf] with t h ht hft
    have := (h (by rw [uIcc01]; exact Ioo_subset_Icc_self ht) 0 (by simp)).deriv
    change deriv (fun x => ∫ s in (0 : ℝ)..x, (f : ℝ → ℝ) s) t = _
    rw [this, hft]
  have hz := h0 _ (h10_prim h1)
  have hz' : ∫ t, (h t - m) * h t ∂vol01 = 0 := by
    rw [← hz]; exact integral_congr_ae (hd.mono fun t ht => by simp only [ht])
  have hsq : Integrable (fun t => (h t - m) ^ 2) vol01 :=
    (memLp_two_iff_integrable_sq hmc.aestronglyMeasurable).1 hmc
  have hzero : ∫ t, (h t - m) ^ 2 ∂vol01 = 0 := by
    have e : (fun t => (h t - m) ^ 2) = fun t => (h t - m) * h t - m * (h t - m) := by
      funext t; ring
    have i0 : Integrable (fun t => h t - m) vol01 := hi.sub (integrable_const m)
    have i2 : Integrable (fun t => m * (h t - m)) vol01 := i0.const_mul m
    have i1 : Integrable (fun t => (h t - m) * h t) vol01 := by
      refine (hsq.add i2).congr (ae_of_all _ fun t => ?_)
      simp only [Pi.add_apply]; ring
    have hc : ∫ t, h t - m ∂vol01 = 0 := by rw [integral_sub hi (integrable_const m)]; simp [m]
    rw [e, integral_sub i1 i2, hz', integral_const_mul, hc]
    simp
  have := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hsq).1 hzero
  filter_upwards [this] with t ht
  simpa [sub_eq_zero] using ht

/-! ### The derivative of a solution -/

instance : IsMeas01 vol01 where
  compl_zero := by
    have e : (Icc (0 : ℝ) 1)ᶜ ∩ Ioo 0 1 = ∅ :=
      eq_empty_iff_forall_notMem.2 fun x hx => hx.1 (Ioo_subset_Icc_self hx.2)
    rw [Measure.restrict_apply' measurableSet_Ioo, e, measure_empty]

lemma bound_of_cont {ψ : ℝ → ℝ} (hψc : Continuous ψ) :
    ∃ B, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) 1, |ψ x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hψc.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x hx => (by simpa using hB x hx : |ψ x| ≤ B).trans
    (le_max_left _ _)⟩

lemma abs_setIntegral_le (ρ : Measure ℝ) [IsMeas01 ρ] {ψ : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ s ∩ Icc (0 : ℝ) 1, |ψ x| ≤ M) :
    |∫ x in s, ψ x ∂ρ| ≤ M * ρ.real univ := by
  have h1 : ∀ᵐ x ∂ρ.restrict s, ‖ψ x‖ ≤ M := by
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae (IsMeas01.ae_mem ρ)] with x h1 h2
    simpa using hM x ⟨h1, h2⟩
  have h2 := norm_integral_le_of_norm_le_const h1
  rw [Real.norm_eq_abs, measureReal_restrict_apply_univ] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ s)) hM0)

lemma Gρ_bdd (ρ : Measure ℝ) [IsMeas01 ρ] {ψ : ℝ → ℝ} (hψc : Continuous ψ) :
    ∃ C, ∀ t, |Gρ ρ ψ t| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := bound_of_cont hψc
  exact ⟨B * ρ.real univ, fun t => abs_setIntegral_le ρ measurableSet_Iio hB0 fun x hx => hB x hx.2⟩

lemma measurable_Gρ (ρ : Measure ℝ) [IsMeas01 ρ] {ψ : ℝ → ℝ} (hψc : Continuous ψ) :
    StronglyMeasurable (Gρ ρ ψ) := by
  have e : Gρ ρ ψ =
      fun t => ∫ x, ({p : ℝ × ℝ | p.2 < p.1}.indicator (fun p => ψ p.2)) (t, x) ∂ρ := by
    funext t
    rw [Gρ, ← integral_indicator measurableSet_Iio]
    rfl
  rw [e]
  exact StronglyMeasurable.integral_prod_right
    ((hψc.measurable.comp measurable_snd).indicator
      (measurableSet_lt measurable_snd measurable_fst)).stronglyMeasurable

lemma integrable_dG (ρ : Measure ℝ) [IsMeas01 ρ] {ψ : ℝ → ℝ} (hψc : Continuous ψ) {φ : ℝ → ℝ}
    (hφ : H10 φ) : Integrable (fun t => deriv φ t * Gρ ρ ψ t) vol01 := by
  obtain ⟨C, hC⟩ := Gρ_bdd ρ hψc
  refine ((integrable_deriv_mu1 hφ).norm.const_mul C).mono'
    ((measurable_deriv φ).aestronglyMeasurable.mul
      (measurable_Gρ ρ hψc).aestronglyMeasurable) (ae_of_all _ fun t => ?_)
  rw [norm_mul, Real.norm_eq_abs (Gρ ρ ψ t), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)

/-- `R = c + G₊ - G₋ - E G_L`. -/
noncomputable def Rψ (μp μm : Measure ℝ) (ψ : ℝ → ℝ) (E c t : ℝ) : ℝ :=
  c + Gρ μp ψ t - Gρ μm ψ t - E * Gρ vol01 ψ t

section rep

variable {μp μm : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] {ψ : ℝ → ℝ} {E : ℝ}

/-- **The derivative of a solution**: if `-ψ'' + νψ = Eψ` weakly with `ν = μ₊ - μ₋`, then
`ψ' = R = c + G₊ - G₋ - E G_L` a.e. -/
theorem deriv_ae_eq_R (hψ : H10 ψ) (hψc : Continuous ψ)
    (hE : ∀ φ (hφ : H10 φ), ∫ t, deriv ψ t * deriv φ t ∂vol01 + nuOf μp μm (mulP hψ hφ) =
      E * ∫ t, ψ t * φ t ∂vol01) :
    ∃ c, deriv ψ =ᵐ[vol01] Rψ μp μm ψ E c := by
  set h : ℝ → ℝ := fun t => deriv ψ t - Gρ μp ψ t + Gρ μm ψ t + E * Gρ vol01 ψ t
  have hm : MemLp h 2 vol01 := by
    obtain ⟨C1, hC1⟩ := Gρ_bdd μp hψc
    obtain ⟨C2, hC2⟩ := Gρ_bdd μm hψc
    obtain ⟨C3, hC3⟩ := Gρ_bdd vol01 hψc
    have b : ∀ (ρ : Measure ℝ) [IsMeas01 ρ] (C : ℝ), (∀ t, |Gρ ρ ψ t| ≤ C) →
        MemLp (Gρ ρ ψ) 2 vol01 := fun ρ _ C hC =>
      MemLp.of_bound (measurable_Gρ ρ hψc).aestronglyMeasurable C
        (ae_of_all _ fun t => by simpa using hC t)
    exact (((memLp_deriv hψ).sub (b μp C1 hC1)).add (b μm C2 hC2)).add
      ((b vol01 C3 hC3).const_mul E)
  have h0 : ∀ φ (_hφ : H10 φ), ∫ t, deriv φ t * h t ∂vol01 = 0 := fun φ hφ => by
    have hw := hE φ hφ
    rw [nuOf, sub_apply, intCLM_mulP, intCLM_mulP,
      integral_mul_eq_neg μp hψc hφ, integral_mul_eq_neg μm hψc hφ,
      show ∫ t, ψ t * φ t ∂vol01 = -∫ t, deriv φ t * Gρ vol01 ψ t ∂vol01 from
        integral_mul_eq_neg vol01 hψc hφ] at hw
    have i0 : Integrable (fun t => deriv φ t * deriv ψ t) vol01 := integrable_dd hφ hψ
    have i1 := integrable_dG μp hψc hφ
    have i2 := integrable_dG μm hψc hφ
    have i3 := (integrable_dG vol01 hψc hφ).const_mul E
    have e : (fun t => deriv φ t * h t) = fun t => deriv φ t * deriv ψ t -
        deriv φ t * Gρ μp ψ t + deriv φ t * Gρ μm ψ t + E * (deriv φ t * Gρ vol01 ψ t) := by
      funext t; simp only [h]; ring
    have i01 : Integrable (fun t => deriv φ t * deriv ψ t - deriv φ t * Gρ μp ψ t) vol01 := i0.sub i1
    have i012 : Integrable (fun t => deriv φ t * deriv ψ t - deriv φ t * Gρ μp ψ t +
      deriv φ t * Gρ μm ψ t) vol01 := i01.add i2
    rw [e, integral_add i012 i3, integral_add i01 i2, integral_sub i0 i1, integral_const_mul]
    have e2 : ∫ t, deriv φ t * deriv ψ t ∂vol01 = ∫ t, deriv ψ t * deriv φ t ∂vol01 := by
      simp_rw [mul_comm (deriv φ _)]
    rw [e2]; linarith
  refine ⟨∫ t, h t ∂vol01, (ae_eq_const_of_orth hm h0).mono fun t ht => ?_⟩
  simp only [h] at ht
  simp only [Rψ]; linarith

end rep

/-! ### Increments -/

/-- The total mass `Λ` of `μ₊ + μ₋ + |E| dt`. -/
noncomputable def LamM (μp μm : Measure ℝ) (E : ℝ) : ℝ :=
  μp.real univ + μm.real univ + |E| * vol01.real univ

lemma LamM_nonneg (μp μm : Measure ℝ) (E : ℝ) : 0 ≤ LamM μp μm E := by
  unfold LamM; positivity

lemma integrable_of_meas01 (ρ : Measure ℝ) [IsMeas01 ρ] {ψ : ℝ → ℝ} (hψc : Continuous ψ) :
    Integrable ψ ρ := by
  obtain ⟨B, -, hB⟩ := bound_of_cont hψc
  exact Integrable.of_bound hψc.aestronglyMeasurable B
    ((IsMeas01.ae_mem ρ).mono fun x hx => by simpa using hB x hx)

lemma Gρ_sub (ρ : Measure ℝ) [IsMeas01 ρ] {ψ : ℝ → ℝ} (hψc : Continuous ψ) {a t : ℝ}
    (hat : a ≤ t) : Gρ ρ ψ t - Gρ ρ ψ a = ∫ x in Ico a t, ψ x ∂ρ := by
  have hi := integrable_of_meas01 ρ hψc
  have hd : Disjoint (Iio a) (Ico a t) :=
    Set.disjoint_left.2 fun x (h1 : x < a) (h2 : x ∈ Ico a t) => absurd h2.1 (not_le.2 h1)
  rw [Gρ, Gρ, ← Iio_union_Ico_eq_Iio hat, setIntegral_union hd measurableSet_Ico hi.integrableOn
    hi.integrableOn]
  ring

section incr

variable {μp μm : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] {ψ : ℝ → ℝ} {E c : ℝ}

lemma R_sub_le_of_le (hψc : Continuous ψ) {a t M : ℝ} (hat : a ≤ t) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc a t, |ψ x| ≤ M) :
    |Rψ μp μm ψ E c t - Rψ μp μm ψ E c a| ≤ M * LamM μp μm E := by
  have hb : ∀ (ρ : Measure ℝ) [IsMeas01 ρ], |Gρ ρ ψ t - Gρ ρ ψ a| ≤ M * ρ.real univ :=
    fun ρ _ => by
      rw [Gρ_sub ρ hψc hat]
      exact abs_setIntegral_le ρ measurableSet_Ico hM0 fun x hx => hM x (Ico_subset_Icc_self hx.1)
  have e : Rψ μp μm ψ E c t - Rψ μp μm ψ E c a = (Gρ μp ψ t - Gρ μp ψ a) -
      (Gρ μm ψ t - Gρ μm ψ a) - E * (Gρ vol01 ψ t - Gρ vol01 ψ a) := by simp only [Rψ]; ring
  rw [e, LamM]
  have h1 := hb μp
  have h2 := hb μm
  have h3 := hb vol01
  calc _ ≤ |Gρ μp ψ t - Gρ μp ψ a| + |Gρ μm ψ t - Gρ μm ψ a| +
        |E * (Gρ vol01 ψ t - Gρ vol01 ψ a)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
    _ ≤ M * μp.real univ + M * μm.real univ + |E| * (M * vol01.real univ) := by
          rw [abs_mul]; gcongr
    _ = M * (μp.real univ + μm.real univ + |E| * vol01.real univ) := by ring

lemma R_sub_le (hψc : Continuous ψ) {a t M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ uIcc a t, |ψ x| ≤ M) :
    |Rψ μp μm ψ E c t - Rψ μp μm ψ E c a| ≤ M * LamM μp μm E := by
  rcases le_total a t with h | h
  · exact R_sub_le_of_le hψc h hM0 fun x hx => hM x (by rw [uIcc_of_le h]; exact hx)
  · rw [abs_sub_comm]
    exact R_sub_le_of_le hψc h hM0 fun x hx => hM x (by rw [uIcc_of_ge h]; exact hx)

lemma ae_ne_pt' (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]; simp

omit [IsMeas01 μp] [IsMeas01 μm] in
lemma intervalIntegrable_R (hψ : H10 ψ) (hR : deriv ψ =ᵐ[vol01] Rψ μp μm ψ E c) {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (Rψ μp μm ψ E c) volume a t := by
  have hi : IntegrableOn (Rψ μp μm ψ E c) (Ioo (0 : ℝ) 1) :=
    (integrable_deriv_mu1 hψ).congr hR
  rw [← integrableOn_Icc_iff_integrableOn_Ioo] at hi
  exact (hi.mono_set (uIcc_subset_Icc ha ht)).intervalIntegrable

omit [IsMeas01 μp] [IsMeas01 μm] in
lemma psi_sub (hψ : H10 ψ) (hR : deriv ψ =ᵐ[vol01] Rψ μp μm ψ E c) {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψ t - ψ a = ∫ x in a..t, Rψ μp μm ψ E c x := by
  have hac : AbsolutelyContinuousOnInterval ψ a t := hψ.1.mono (by
    rw [uIcc01]; exact uIcc_subset_Icc ha ht)
  rw [← hac.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hR, ae_ne_pt' 0, ae_ne_pt' 1]
    with x hx h0 h1 hxI
  have hx' := uIcc_subset_Icc ha ht (uIoc_subset_uIcc hxI)
  exact hx ⟨lt_of_le_of_ne hx'.1 (Ne.symm h0), lt_of_le_of_ne hx'.2 h1⟩

/-! ### Propagation of zeros -/

/-- **One step**: if `ψ(a) = R(a) = 0` and `|t - a| Λ ≤ ½`, then `ψ = 0` between `a` and `t`
and `R(t) = 0`. -/
theorem step_zero (hψ : H10 ψ) (hψc : Continuous ψ) (hR : deriv ψ =ᵐ[vol01] Rψ μp μm ψ E c)
    {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hψa : ψ a = 0)
    (hRa : Rψ μp μm ψ E c a = 0) (hd : |t - a| * LamM μp μm E ≤ 1 / 2) :
    (∀ x ∈ uIcc a t, ψ x = 0) ∧ Rψ μp μm ψ E c t = 0 := by
  set Λ := LamM μp μm E
  have hK : uIcc a t ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc ha ht
  obtain ⟨x0, hx0, hmax⟩ := isCompact_uIcc.exists_isMaxOn nonempty_uIcc
    (hψc.abs.continuousOn (s := uIcc a t))
  set M := |ψ x0|
  have hM : ∀ x ∈ uIcc a t, |ψ x| ≤ M := fun x hx => hmax hx
  have hM0 : 0 ≤ M := abs_nonneg _
  have hsub : uIcc a x0 ⊆ uIcc a t := uIcc_subset_uIcc_left hx0
  have hRb : ∀ s ∈ uIcc a x0, ‖Rψ μp μm ψ E c s‖ ≤ M * Λ := fun s hs => by
    have := R_sub_le (μp := μp) (μm := μm) (E := E) (c := c) hψc (a := a) (t := s) hM0
      fun x hx => hM x (hsub (uIcc_subset_uIcc_left hs hx))
    rwa [hRa, sub_zero, ← Real.norm_eq_abs] at this
  have h1 : M ≤ M * Λ * |x0 - a| := by
    have e := psi_sub hψ hR ha (hK hx0)
    rw [hψa, sub_zero] at e
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s hs => hRb s (uIoc_subset_uIcc hs))
    rwa [← e, Real.norm_eq_abs] at this
  have h2 : |x0 - a| ≤ |t - a| := abs_sub_left_of_mem_uIcc hx0
  have h3 : M * Λ * |x0 - a| ≤ M / 2 := by
    calc M * Λ * |x0 - a| ≤ M * (|t - a| * Λ) := by
          rw [mul_assoc, mul_comm Λ]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2 (LamM_nonneg _ _ _)) hM0
      _ ≤ M * (1 / 2) := mul_le_mul_of_nonneg_left hd hM0
      _ = M / 2 := by ring
  have hM' : M = 0 := le_antisymm (by linarith) hM0
  have hz : ∀ x ∈ uIcc a t, ψ x = 0 := fun x hx => abs_eq_zero.1 (le_antisymm
    ((hM x hx).trans hM'.le) (abs_nonneg _))
  refine ⟨hz, ?_⟩
  have := R_sub_le (μp := μp) (μm := μm) (E := E) (c := c) hψc (a := a) (t := t) le_rfl
    fun x hx => by rw [hz x hx]; simp
  rw [zero_mul, hRa, sub_zero] at this
  exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))

/-- **Unique continuation**: if `ψ(a) = R(a) = 0` for some `a ∈ [0, 1]`, then `ψ ≡ 0` on
`[0, 1]`. -/
theorem eq_zero_of_R_zero (hψ : H10 ψ) (hψc : Continuous ψ) (hR : deriv ψ =ᵐ[vol01] Rψ μp μm ψ E c)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hψa : ψ a = 0) (hRa : Rψ μp μm ψ E c a = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ψ t = 0 := by
  set Λ := LamM μp μm E
  have hΛ := LamM_nonneg μp μm E
  set δ := 1 / (2 * Λ + 2)
  have hδ : 0 < δ := by positivity
  have hδΛ : δ * Λ ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) two_pos]; linarith
  have key : ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, |t - a| ≤ k * δ →
      ψ t = 0 ∧ Rψ μp μm ψ E c t = 0 := by
    intro k
    induction k with
    | zero =>
      intro t _ h
      simp only [Nat.cast_zero, zero_mul] at h
      have : t = a := by have := abs_nonneg (t - a); linarith [abs_eq_zero.1 (le_antisymm h this)]
      subst this; exact ⟨hψa, hRa⟩
    | succ k ih =>
      intro t ht h
      set w : ℝ := k / (k + 1)
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      have hw0 : 0 ≤ w := by positivity
      have hw1 : w ≤ 1 := by rw [div_le_one hk1]; linarith
      set t' := a + (t - a) * w
      have ht' : t' ∈ Icc (0 : ℝ) 1 := by
        constructor
        · nlinarith [mul_nonneg ha.1 (sub_nonneg.2 hw1), mul_nonneg ht.1 hw0]
        · nlinarith [mul_nonneg (sub_nonneg.2 ha.2) (sub_nonneg.2 hw1),
            mul_nonneg (sub_nonneg.2 ht.2) hw0]
      have e1 : |t' - a| = |t - a| * w := by
        rw [show t' - a = (t - a) * w by ring, abs_mul, abs_of_nonneg hw0]
      have e2 : |t - t'| = |t - a| / (k + 1) := by
        rw [show t - t' = (t - a) * (1 / (k + 1)) by simp only [t', w]; field_simp; ring,
          abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (k + 1))]
        ring
      have h' : |t' - a| ≤ k * δ := by
        rw [e1]
        calc |t - a| * w ≤ ((k + 1 : ℕ) * δ) * w := mul_le_mul_of_nonneg_right h hw0
          _ = k * δ := by simp only [w]; push_cast; field_simp
      obtain ⟨h1, h2⟩ := ih t' ht' h'
      have hd : |t - t'| * Λ ≤ 1 / 2 := by
        rw [e2]
        have : |t - a| / (k + 1) ≤ δ := by
          rw [div_le_iff₀ hk1]; push_cast at h; linarith
        calc |t - a| / (k + 1) * Λ ≤ δ * Λ := mul_le_mul_of_nonneg_right this hΛ
          _ ≤ 1 / 2 := hδΛ
      obtain ⟨h3, h4⟩ := step_zero hψ hψc hR ht' ht h1 h2 hd
      exact ⟨h3 t right_mem_uIcc, h4⟩
  intro t ht
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / δ)
  refine (key k t ht ?_).1
  have : |t - a| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ha.1, ha.2]
  calc |t - a| ≤ 1 := this
    _ = 1 / δ * δ := by field_simp
    _ ≤ k * δ := mul_le_mul_of_nonneg_right hk hδ.le

/-- **At an interior zero of a nonnegative solution, `R` vanishes.** -/
theorem R_zero_of_min (hψ : H10 ψ) (hψc : Continuous ψ) (hR : deriv ψ =ᵐ[vol01] Rψ μp μm ψ E c)
    (hψ0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ ψ x) {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1) (hz : ψ t0 = 0) :
    Rψ μp μm ψ E c t0 = 0 := by
  set R := Rψ μp μm ψ E c
  set Λ := LamM μp μm E
  have hΛ := LamM_nonneg μp μm E
  by_contra hne
  set r := |R t0|
  have hr : 0 < r := abs_pos.2 hne
  set ε := r / (2 * (Λ + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hψc.continuousAt ε hε
  set η' := min (η / 2) (min t0 (1 - t0))
  have hη' : 0 < η' := lt_min (by positivity) (lt_min ht0.1 (by linarith [ht0.2]))
  have hη'η : η' < η := (min_le_left _ _).trans_lt (by linarith)
  have hη't : η' ≤ t0 := (min_le_right _ _).trans (min_le_left _ _)
  have hη't1 : η' ≤ 1 - t0 := (min_le_right _ _).trans (min_le_right _ _)
  have ht0I : t0 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht0
  -- `R` stays within `r/2` of `R(t0)` on `[t0 - η', t0 + η']`
  have hclose : ∀ s, |s - t0| ≤ η' → |R s - R t0| < r / 2 := fun s hs => by
    have hb : ∀ x ∈ uIcc t0 s, |ψ x| ≤ ε := fun x hx => by
      have hx' : |x - t0| ≤ |s - t0| := abs_sub_left_of_mem_uIcc hx
      have := hηb (x := x) (by rw [Real.dist_eq]; linarith)
      rw [Real.dist_eq, hz, sub_zero] at this; exact this.le
    have := R_sub_le (μp := μp) (μm := μm) (E := E) (c := c) hψc (a := t0) (t := s) hε.le hb
    calc |R s - R t0| ≤ ε * Λ := this
      _ < r / 2 := by
        simp only [ε]
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
        nlinarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `R(t0) < 0`: `ψ` becomes negative to the right
    set b := t0 + η'
    have hb : b ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht0.1], by linarith⟩
    have hRb : ∀ s ∈ Icc t0 b, R s ≤ -(r / 2) := fun s hs => by
      have := hclose s (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
      have hr' : r = -R t0 := abs_of_neg hneg
      rw [abs_lt] at this; linarith [this.2]
    have e := psi_sub hψ hR ht0I hb
    rw [hz, sub_zero] at e
    have hle : ∫ x in t0..b, R x ≤ ∫ x in t0..b, -(r / 2) :=
      intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_R hψ hR ht0I hb)
        intervalIntegrable_const hRb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    have : ψ b < 0 := by rw [e]; nlinarith
    linarith [hψ0 b hb]
  · -- `R(t0) > 0`: `ψ` becomes negative to the left
    set b := t0 - η'
    have hb : b ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht0.2]⟩
    have hRb : ∀ s ∈ Icc b t0, r / 2 ≤ R s := fun s hs => by
      have := hclose s (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
      have hr' : r = R t0 := abs_of_pos hpos
      rw [abs_lt] at this; linarith [this.1]
    have e := psi_sub hψ hR ht0I hb
    rw [hz, sub_zero, intervalIntegral.integral_symm] at e
    have hle : ∫ x in b..t0, r / 2 ≤ ∫ x in b..t0, R x :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (intervalIntegrable_R hψ hR hb ht0I) hRb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    have : ψ b < 0 := by rw [e]; nlinarith
    linarith [hψ0 b hb]

end incr

/-! ### Ground states have no interior zeros -/

lemma kinM_clamp {g : ℝ → ℝ} : kinM (H10.clamp g) = kinM g := by
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have : H10.clamp g =ᶠ[𝓝 t] g := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
    fun s hs => H10.clamp_eq (Ioo_subset_Icc_self hs)
  simp only [this.deriv_eq]

lemma QM_clamp (ν : PotM) {g : ℝ → ℝ} (hg : H10 g) : QM ν (H10.clamp_H10 hg) = QM ν hg := by
  have : sqP (H10.clamp_H10 hg) = sqP hg := by ext t; simp [H10.clamp_eq t.2]
  rw [QM, QM, kinM_clamp, this]

/-- A normalised ground state has energy `E₀`. -/
lemma QM_eq_EM_of_isGSM {ν : PotM} {ψ : ℝ → ℝ} (h : IsGSM ν ψ) (hn : ∫ t, ψ t ^ 2 ∂vol01 = 1)
    (hψ : H10 ψ) : QM ν hψ = EM ν := by
  obtain ⟨hψ', -, hmin⟩ := h
  refine le_antisymm ?_ (EM_le ν hψ hn)
  obtain ⟨φ0, hφ0, hn0⟩ := exists_norm_one
  refine le_csInf ⟨_, φ0, hφ0, hn0, rfl⟩ fun e ⟨φ, hφ, hφn, he⟩ => ?_
  have := hmin φ hφ
  rw [hφn, hn, mul_one, mul_one] at this
  exact he ▸ this

/-- **A ground state of a measure potential has no zero in `(0, 1)`.** -/
theorem gs_ne_zero {μp μm : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] {ψ : ℝ → ℝ}
    (h : IsGSM (nuOf μp μm) ψ) : ∀ t ∈ Ioo (0 : ℝ) 1, ψ t ≠ 0 := by
  set ν := nuOf μp μm
  have hψ := h.1
  have hpos := h.2.1
  set m := ∫ t, ψ t ^ 2 ∂vol01
  set c := 1 / √m
  have hc2 : c ^ 2 = 1 / m := by rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
  have hc : c ≠ 0 := by
    intro h0; rw [h0] at hc2; have : (0 : ℝ) < 1 / m := by positivity
    simp at hc2; linarith
  have hn1 : ∫ t, (c * ψ t) ^ 2 ∂vol01 = 1 := by rw [norm2_smul, hc2, one_div_mul_cancel hpos.ne']
  have hQ1 := QM_eq_EM_of_isGSM (h.const_mul hc) hn1 (hψ.const_mul c)
  have hχ1 := (hψ.const_mul c).abs
  have hχ := H10.clamp_H10 hχ1
  set χ := H10.clamp fun t => |c * ψ t|
  have hχc : Continuous χ := H10.continuous_clamp hχ1
  have hnχ : ∫ t, χ t ^ 2 ∂vol01 = 1 := by
    rw [integral_mu1_clamp (F := fun _ y => y ^ 2)]; simp only [sq_abs]; exact hn1
  have hQ : QM ν hχ = EM ν := le_antisymm
    ((QM_clamp ν hχ1).trans_le ((QM_abs_le ν _).trans hQ1.le)) (EM_le ν hχ hnχ)
  obtain ⟨c', hR⟩ := deriv_ae_eq_R (μp := μp) (μm := μm) hχ hχc
    fun φ hφ => euler_lagrange hχ hnχ hQ hφ
  have hχx : ∀ x ∈ Icc (0 : ℝ) 1, χ x = |c * ψ x| := fun x hx => H10.clamp_eq hx
  have hχ0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ χ x := fun x hx => by
    rw [hχx x hx]; exact abs_nonneg _
  intro t0 ht0 hz
  have hzχ : χ t0 = 0 := by rw [hχx t0 (Ioo_subset_Icc_self ht0), hz, mul_zero, abs_zero]
  have hR0 := R_zero_of_min hχ hχc hR hχ0 ht0 hzχ
  have hall := eq_zero_of_R_zero hχ hχc hR (Ioo_subset_Icc_self ht0) hzχ hR0
  have : ∫ t, χ t ^ 2 ∂vol01 = 0 := by
    rw [integral_congr_ae ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => by
      simp only [hall t (Ioo_subset_Icc_self ht)] : (fun t => χ t ^ 2) =ᵐ[vol01] fun _ => (0 : ℝ) ^ 2)]
    simp
  rw [hnχ] at this; exact one_ne_zero this

/-- **A ground state of a measure potential has a strict sign on `(0, 1)`.** -/
theorem gs_pos_or_neg {μp μm : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] {ψ : ℝ → ℝ}
    (h : IsGSM (nuOf μp μm) ψ) :
    (∀ t ∈ Ioo (0 : ℝ) 1, 0 < ψ t) ∨ ∀ t ∈ Ioo (0 : ℝ) 1, ψ t < 0 := by
  have hne := gs_ne_zero h
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha, hA⟩, ⟨b, hb, hB⟩⟩ := hc
  have hA' : ψ a < 0 := lt_of_le_of_ne hA (hne a ha)
  have hB' : 0 < ψ b := lt_of_le_of_ne hB (hne b hb).symm
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := ordConnected_Ioo.uIcc_subset ha hb
  have hcont : ContinuousOn ψ (uIcc a b) :=
    h.1.continuousOn.mono (hsub.trans Ioo_subset_Icc_self)
  obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hcont (mem_uIcc.2 (Or.inl ⟨hA'.le, hB'.le⟩))
  exact hne x (hsub hx) hx0

/-! ### The `N = 1` characterisation -/

/-- `ρ ∈ C([0, 1])` is the density of a normalised ground state of a measure potential
`μ₊ - μ₋`. -/
def VRepMeas (ρ : C01) : Prop :=
  ∃ (μp μm : Measure ℝ) (_ : IsMeas01 μp) (_ : IsMeas01 μm) (ψ : ℝ → ℝ),
    IsGSM (nuOf μp μm) ψ ∧ ∫ t, ψ t ^ 2 ∂vol01 = 1 ∧ ∀ t : Icc (0 : ℝ) 1, ρ t = ψ t ^ 2

/-- **`v`-representability with measure potentials, one particle**: a density is the ground-state
density of a measure potential iff `ρ = g²` with `g ∈ H¹₀` normalised, positive on `(0, 1)`, and
solving `-g'' + ν g = E g` weakly for some measure `ν` and some `E`. -/
theorem vrepMeas_iff (ρ : C01) : VRepMeas ρ ↔
    ∃ g : ℝ → ℝ, ∃ hg : H10 g, ∫ t, g t ^ 2 ∂vol01 = 1 ∧ (∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) ∧
      (∀ t : Icc (0 : ℝ) 1, ρ t = g t ^ 2) ∧
      ∃ (μp μm : Measure ℝ) (_ : IsMeas01 μp) (_ : IsMeas01 μm) (E : ℝ),
        ∀ φ (hφ : H10 φ), ∫ t, deriv g t * deriv φ t ∂vol01 + nuOf μp μm (mulP hg hφ) =
          E * ∫ t, g t * φ t ∂vol01 := by
  constructor
  · rintro ⟨μp, μm, _, _, ψ, hgs, hn, hρ⟩
    have hψ := hgs.1
    rcases gs_pos_or_neg hgs with hp | hneg
    · exact ⟨ψ, hψ, hn, hp, hρ, μp, μm, inferInstance, inferInstance, EM (nuOf μp μm),
        fun φ hφ => euler_lagrange hψ hn (QM_eq_EM_of_isGSM hgs hn hψ) hφ⟩
    · have hgs' := hgs.const_mul (c := -1) (by norm_num)
      have hn' : ∫ t, (-1 * ψ t) ^ 2 ∂vol01 = 1 := by rw [norm2_smul, hn]; norm_num
      have hg := hψ.const_mul (-1)
      refine ⟨fun t => -1 * ψ t, hg, hn', fun t ht => by linarith [hneg t ht],
        fun t => by rw [hρ t]; ring, μp, μm, inferInstance, inferInstance, EM (nuOf μp μm),
        fun φ hφ => euler_lagrange hg hn' (QM_eq_EM_of_isGSM hgs' hn' hg) hφ⟩
  · rintro ⟨g, hg, hn, hpos, hρ, μp, μm, _, _, E, hE⟩
    exact ⟨μp, μm, inferInstance, inferInstance, g, (isGSM_of_pos_weak hg hpos hE).1, hn, hρ⟩

end DFT.Continuum.Line
