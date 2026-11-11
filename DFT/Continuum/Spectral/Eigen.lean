/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Spectral.Injective
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Eigenvectors of the Green operator are classical eigenfunctions

If `f ∈ L²(0, 1)` satisfies `G f = μ f` with `μ ≠ 0`, then `f` agrees almost everywhere with a
`C²` function `e` on `ℝ` vanishing at `0` and `1` and solving `e'' = (W - 1/μ) e` on `[0, 1]`;
moreover `μ > 0`.

The continuous representative `φ = μ⁻¹ G f` satisfies `φ = μ⁻¹ G φ`, so `y = G φ` solves
`y'' = W y - φ = (W - μ⁻¹) y` on `[0, 1]`; by uniqueness for this ODE on `[0, 1]`, `y` is a multiple
of the shooting solution, which is `C²` and extends to `ℝ`. Integrating `e'' e` by parts gives
`μ⁻¹ ∫ e² = ∫ e'² + ∫ W e² ≥ 0`.

* `eigen_regular`: the classical eigenfunction.
* `eigenvalue_pos`: eigenvalues of `G` are positive.
-/

namespace DFT.Continuum.Spectral

open MeasureTheory Set Filter Topology Box

variable {W : ℝ → ℝ} (hWc : Continuous W) (hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t)

lemma continuous_Gk_proj {f : ℝ → ℝ} (hf : Integrable f μ1) :
    Continuous fun x : ℝ => Gk hWc f (projIcc (0 : ℝ) 1 zero_le_one x) :=
  (continuousOn_Gk hWc hf).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun x => (projIcc (0 : ℝ) 1 zero_le_one x).2

lemma Gk_congr {f g : ℝ → ℝ} (h : f =ᵐ[μ1] g) (x : ℝ) : Gk hWc f x = Gk hWc g x :=
  integral_congr_ae (h.mono fun y hy => by simp only [hy])

include hW0 in
/-- **Eigenvectors are classical eigenfunctions.** -/
theorem eigen_regular {f : HL} {μ : ℝ} (hμ : μ ≠ 0) (hf : Gop hWc f = μ • f) :
    ∃ e : ℝ → ℝ, e ∈ Box.Dom ∧ (f : ℝ → ℝ) =ᵐ[μ1] e ∧
      ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv e) x = (W x - μ⁻¹) * e x := by
  set lam := μ⁻¹
  have hfi := integrable_HL f
  -- the continuous representative
  set φ : ℝ → ℝ := fun x => lam * Gk hWc f (projIcc 0 1 zero_le_one x) with hφd
  have hφc : Continuous φ := continuous_const.mul (continuous_Gk_proj hWc hfi)
  have hfφ : (f : ℝ → ℝ) =ᵐ[μ1] φ := by
    have h1 : (Gop hWc f : ℝ → ℝ) =ᵐ[μ1] fun x => μ * (f : ℝ → ℝ) x := by
      rw [hf]; exact (Lp.coeFn_smul μ f)
    filter_upwards [h1, Gop_ae hWc f, ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
    simp only [φ, projIcc_of_mem _ (Ioo_subset_Icc_self hx)]
    rw [← h2, h1, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  -- `φ = μ⁻¹ G φ` on `[0, 1]`
  have hφfix : ∀ x ∈ Icc (0 : ℝ) 1, φ x = lam * Gf hWc φ x := by
    intro x hx
    simp only [φ, projIcc_of_mem _ hx]
    rw [Gk_congr hWc hfφ, Gk_eq_Gf hWc hφc hx]
  set y := Gf hWc φ
  set dy := dGf hWc φ
  have hy : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt y (dy t) t := fun t ht => hasDerivAt_Gf hWc hφc ht
  have hdy : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt dy (W t * y t - φ t) t := fun t ht =>
    hasDerivAt_dGf hWc hφc hW0 ht
  -- the shooting solution for the coefficient `W - μ⁻¹`
  set W' : ℝ → ℝ := fun t => W t - lam
  have hW'c : Continuous W' := hWc.sub continuous_const
  obtain ⟨s, hs0, hsd⟩ := exists_sol hW'c
  set a := dy 0
  -- uniqueness on `[0, 1]`
  obtain ⟨B, -, hB⟩ := exists_bound_W hW'c
  have hBI : ∀ t ∈ Icc (0 : ℝ) 1, |W' t| ≤ B := fun t ht =>
    hB t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have huniq := ODE_solution_unique_of_mem_Icc_right (v := fun t => field W' t)
    (s := fun _ => univ) (K := Real.toNNReal (1 + B)) (a := 0) (b := 1)
    (f := fun t => (y t, dy t)) (g := fun t => a • s t)
    (fun t ht => lipschitz_field hBI (Ico_subset_Icc_self ht))
    (fun t ht => ((hy t (Icc_sub_Ioo' ht)).continuousAt.prodMk
      (hdy t (Icc_sub_Ioo' ht)).continuousAt).continuousWithinAt)
    (fun t ht => by
      have h := (hy t (Icc_sub_Ioo' (Ico_subset_Icc_self ht))).prodMk
        (hdy t (Icc_sub_Ioo' (Ico_subset_Icc_self ht)))
      refine (h.congr_deriv ?_).hasDerivWithinAt
      have := hφfix t (Ico_subset_Icc_self ht)
      simp only [field, W', Prod.mk.injEq, true_and]
      rw [this]; ring)
    (fun _ _ => mem_univ _)
    (fun t ht => ((hsd t (Icc_sub_Ioo' ht)).continuousAt.const_smul a).continuousWithinAt)
    (fun t ht => by
      have h := (hsd t (Icc_sub_Ioo' (Ico_subset_Icc_self ht))).const_smul a
      refine (h.congr_deriv ?_).hasDerivWithinAt
      simp only [field, Prod.smul_mk, smul_eq_mul, Prod.smul_fst, Prod.smul_snd]
      ring_nf)
    (fun _ _ => mem_univ _)
    (by simp [y, Gf_zero, a, hs0])
  have hys : ∀ t ∈ Icc (0 : ℝ) 1, y t = a * (s t).1 := fun t ht => by
    have := congrArg Prod.fst (huniq ht)
    simpa using this
  -- the `C²` extension
  obtain ⟨ψe, hψe, hψeq⟩ := exists_contDiff_ext (contDiffOn_sol hW'c hsd)
  set e : ℝ → ℝ := fun x => lam * a * ψe x with hed
  have hIcc : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he_eq : ∀ t ∈ Icc (0 : ℝ) 1, e t = φ t := fun t ht => by
    simp only [e, hψeq t (hIcc t ht)]
    rw [hφfix t ht, hys t ht]; ring
  refine ⟨e, ⟨contDiff_const.mul hψe, ?_, ?_⟩, ?_, ?_⟩
  · rw [he_eq 0 ⟨le_rfl, zero_le_one⟩, hφfix 0 ⟨le_rfl, zero_le_one⟩]
    simp only [y, Gf_zero, mul_zero]
  · rw [he_eq 1 ⟨zero_le_one, le_rfl⟩, hφfix 1 ⟨zero_le_one, le_rfl⟩]
    simp only [y, Gf_one, mul_zero]
  · filter_upwards [hfφ, ae_restrict_mem measurableSet_Ioo] with x h1 hx
    rw [h1, he_eq x (Ioo_subset_Icc_self hx)]
  · intro x hx
    have hxo : x ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := hIcc x hx
    have hx2 : x ∈ Ioo (-1 : ℝ) 2 := Icc_sub_Ioo' hx
    have hev : e =ᶠ[𝓝 x] fun t => lam * a * (s t).1 :=
      Filter.eventually_of_mem (Ioo_mem_nhds hxo.1 hxo.2) fun t ht => by
        simp only [e, hψeq t ht]
    have hdev : deriv e =ᶠ[𝓝 x] fun t => lam * a * (s t).2 := by
      filter_upwards [hev.eventuallyEq_nhds, Ioo_mem_nhds hx2.1 hx2.2] with t ht ht2
      rw [ht.deriv_eq]
      exact ((hasDerivAt_fst_of hsd ht2).const_mul (lam * a)).deriv
    rw [hdev.deriv_eq, ((hasDerivAt_snd_of hsd hx2).const_mul (lam * a)).deriv,
      hev.eq_of_nhds]
    simp only [W']; ring

lemma integral_unit_mu1 {F : ℝ → ℝ} : ∫ x in (0 : ℝ)..1, F x = ∫ x, F x ∂μ1 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

include hW0 in
/-- **Eigenvalues of the Green operator are positive.** -/
theorem eigenvalue_pos {f : HL} (hf0 : f ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) (hf : Gop hWc f = μ • f) :
    0 < μ := by
  obtain ⟨e, he, hfe, hode⟩ := eigen_regular hWc hW0 hμ hf
  set lam := μ⁻¹
  have h2 : ContDiff ℝ 2 e := he.1
  have hd1 : ∀ t, HasDerivAt e (deriv e t) t := fun t =>
    ((h2.differentiable (by norm_num)) t).hasDerivAt
  have hdd : ContDiff ℝ 1 (deriv e) := (contDiff_succ_iff_deriv.1 h2).2.2
  have hd2 : ∀ t, HasDerivAt (deriv e) (deriv (deriv e) t) t := fun t =>
    ((hdd.differentiable one_ne_zero) t).hasDerivAt
  have hc0 := h2.continuous
  have hc1 : Continuous (deriv e) := hdd.continuous
  have hc2 : Continuous (deriv (deriv e)) := hdd.continuous_deriv le_rfl
  -- integration by parts: `∫ e e'' = -∫ e'²`
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := e) (u' := deriv e) (v := deriv e) (v' := deriv (deriv e))
    (fun t _ => hd1 t) (fun t _ => hd2 t) (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _)
  rw [he.2.1, he.2.2, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  -- `∫ e e'' = ∫ (W - λ) e²`
  have hode' : ∫ x in (0 : ℝ)..1, e x * deriv (deriv e) x =
      ∫ x in (0 : ℝ)..1, (W x - lam) * (e x * e x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    rw [hode x hx]; ring
  -- `λ ∫ e² = ∫ e'² + ∫ W e²`
  have hW2 : 0 ≤ ∫ x in (0 : ℝ)..1, W x * (e x * e x) :=
    intervalIntegral.integral_nonneg zero_le_one fun x hx =>
      mul_nonneg (hW0 x hx) (mul_self_nonneg _)
  have hD2 : 0 ≤ ∫ x in (0 : ℝ)..1, deriv e x * deriv e x :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => mul_self_nonneg _
  have hsplit : ∫ x in (0 : ℝ)..1, (W x - lam) * (e x * e x) =
      (∫ x in (0 : ℝ)..1, W x * (e x * e x)) - lam * ∫ x in (0 : ℝ)..1, e x * e x := by
    have e1 : (fun x => (W x - lam) * (e x * e x)) =
        fun x => W x * (e x * e x) - lam * (e x * e x) := by funext x; ring
    have i1 : IntervalIntegrable (fun x => W x * (e x * e x)) volume 0 1 :=
      (hWc.mul (hc0.mul hc0)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => lam * (e x * e x)) volume 0 1 :=
      (continuous_const.mul (hc0.mul hc0)).intervalIntegrable _ _
    rw [e1, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
  -- `∫ e² > 0`
  have hpos : 0 < ∫ x in (0 : ℝ)..1, e x * e x := by
    rw [integral_unit_mu1]
    have hn : 0 < inner ℝ f f := real_inner_self_pos.2 hf0
    rw [L2.inner_def] at hn
    calc (0 : ℝ) < ∫ x, inner ℝ ((f : ℝ → ℝ) x) ((f : ℝ → ℝ) x) ∂μ1 := hn
      _ = ∫ x, e x * e x ∂μ1 := by
        refine integral_congr_ae ?_
        filter_upwards [hfe] with x hx
        simp only [hx, RCLike.inner_apply, conj_trivial]
  -- `λ ∫ e² = ∫ e'² + ∫ W e² ≥ 0`
  have hkey : lam * (∫ x in (0 : ℝ)..1, e x * e x) =
      (∫ x in (0 : ℝ)..1, deriv e x * deriv e x) + ∫ x in (0 : ℝ)..1, W x * (e x * e x) := by
    linarith
  set I := ∫ x in (0 : ℝ)..1, e x * e x
  have hlam : 0 < lam := by
    by_contra hneg
    push Not at hneg
    have hlI : lam * I ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hpos.le
    have hl0 : lam ≠ 0 := inv_ne_zero hμ
    have : lam * I < 0 := mul_neg_of_neg_of_pos (lt_of_le_of_ne hneg hl0) hpos
    linarith
  exact inv_pos.1 hlam

end DFT.Continuum.Spectral
