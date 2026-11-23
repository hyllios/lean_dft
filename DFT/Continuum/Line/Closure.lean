/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.WeakRep
import DFT.Continuum.Sine.OneD

/-!
# A closure property of `H¹₀(0, 1)`

If `C¹` functions `u_j` vanishing at `0` and `1` have `∫₀¹ u_j'² ≤ C` and converge in `L²(0, 1)`
to `f`, then `f` has a representative `g ∈ H10` with `∫₀¹ g'² ≤ C` (`h1_closure`).

The proof uses the sine Hilbert basis `sb` of `L²(0, 1)` and the orthonormal cosines
`cs_k = √2 cos(π(k+1)x)`. Integration by parts gives `⟨cs_k, u'⟩ = π(k+1) ⟨sb_k, u⟩`, so Bessel's
inequality bounds `Σ (π(k+1) b_k)² ≤ C` for the sine coefficients `b_k` of `f`. The cosine series
`h = Σ π(k+1) b_k cs_k` converges in `L²`, its primitive `g(x) = ∫₀ˣ h` is absolutely continuous
with `g' = h` a.e. (Lebesgue differentiation), vanishes at `1` because `h ⊥ 1`, and has the same
sine coefficients as `f`, so `g = f` a.e. by completeness of the sines.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Spectral

/-! ### The cosines -/

/-- `√2 cos(π(k+1)x)`. -/
noncomputable def cs (k : ℕ) (x : ℝ) : ℝ := √2 * Real.cos (π * (k + 1) * x)

lemma continuous_cs (k : ℕ) : Continuous (cs k) := by unfold cs; fun_prop

lemma two_cos_mul_cos (a b : ℝ) :
    2 * (Real.cos a * Real.cos b) = Real.cos (a - b) + Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]; ring

lemma cs_orthonormal (k l : ℕ) : ∫ x, cs k x * cs l x ∂μ1 = if k = l then 1 else 0 := by
  rw [integral_mu1]
  have e : ∀ x, cs k x * cs l x =
      Real.cos (π * ((k : ℤ) - l : ℤ) * x) + Real.cos (π * ((k : ℤ) + l + 2 : ℤ) * x) := by
    intro x
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    simp only [cs]
    push_cast
    rw [show π * ((k : ℝ) - l) * x = π * (k + 1) * x - π * (l + 1) * x by ring,
      show π * ((k : ℝ) + l + 2) * x = π * (k + 1) * x + π * (l + 1) * x by ring,
      ← two_cos_mul_cos]
    linear_combination (Real.cos (π * (k + 1) * x) * Real.cos (π * (l + 1) * x)) * h2
  simp only [e]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_cos_int, integral_cos_int]
  have hkl : ((k : ℤ) + l + 2) ≠ 0 := by omega
  by_cases h : k = l
  · subst h; simp; omega
  · have : ((k : ℤ) - l) ≠ 0 := by omega
    simp [h, this, hkl]

lemma integral_cs (k : ℕ) : ∫ x, cs k x ∂μ1 = 0 := by
  rw [integral_mu1]
  have e : (fun x => cs k x) = fun x => √2 * Real.cos (π * ((k + 1 : ℕ) : ℤ) * x) := by
    funext x; simp [cs]
  rw [e, intervalIntegral.integral_const_mul, integral_cos_int]
  simp; omega

lemma cs_orthonormal_HL : Orthonormal ℝ fun k : ℕ => toHL (continuous_cs k) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [inner_toHL_toHL, cs_orthonormal]

lemma norm_sq_toHL {w : ℝ → ℝ} (hw : Continuous w) : ‖toHL hw‖ ^ 2 = ∫ x, w x ^ 2 ∂μ1 := by
  rw [← real_inner_self_eq_norm_sq, inner_toHL_toHL]
  simp only [sq]

/-! ### Sine coefficients by parts -/

/-- `∫ sin · u = (π(k+1))⁻¹ ∫ cos · u'` for absolutely continuous `u` vanishing at `0` and `1`. -/
lemma sn_ibp {u : ℝ → ℝ} (hu : AbsolutelyContinuousOnInterval u 0 1) (h0 : u 0 = 0)
    (h1 : u 1 = 0) (k : ℕ) :
    ∫ x, sn (k + 1) x * u x ∂μ1 = (π * (k + 1))⁻¹ * ∫ x, cs k x * deriv u x ∂μ1 := by
  have hω : π * ((k : ℝ) + 1) ≠ 0 := by positivity
  set v : ℝ → ℝ := fun x => -(cs k x) / (π * (k + 1))
  have hv : ∀ x, HasDerivAt v (sn (k + 1) x) x := by
    intro x
    have h := ((((hasDerivAt_id x).const_mul (π * (k + 1))).cos).const_mul √2).neg.div_const
      (π * (k + 1))
    refine h.congr_deriv ?_
    simp only [sn, id]; push_cast; field_simp
  have hvC : ContDiff ℝ 1 v := by unfold v cs; fun_prop
  have hvAC : AbsolutelyContinuousOnInterval v 0 1 :=
    ContDiffOn.absolutelyContinuousOnInterval hvC.contDiffOn
  have ibp := hu.integral_mul_deriv_eq_deriv_mul hvAC
  rw [h0, h1, zero_mul, zero_mul, sub_zero, zero_sub] at ibp
  simp only [(hv _).deriv] at ibp
  rw [integral_mu1, integral_mu1,
    show (fun x => sn (k + 1) x * u x) = fun x => u x * sn (k + 1) x from
      funext fun x => mul_comm _ _, ibp, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg]
  congr 1; funext x; simp only [v]; field_simp

/-! ### The closure lemma -/

/-- **Closure of `H¹₀(0, 1)`**: an `L²` limit of `C¹` functions vanishing at the ends with
`∫ u'² ≤ C` has an `H10` representative `g` with `∫ g'² ≤ C`. -/
theorem h1_closure {u : ℕ → ℝ → ℝ} {f : HL} {C : ℝ} (hu : ∀ j, ContDiff ℝ 1 (u j))
    (h0 : ∀ j, u j 0 = 0) (h1 : ∀ j, u j 1 = 0)
    (hC : ∀ j, ∫ t, deriv (u j) t ^ 2 ∂μ1 ≤ C)
    (hlim : Tendsto (fun j => toHL (hu j).continuous) atTop (𝓝 f)) :
    ∃ g : ℝ → ℝ, H10 g ∧ g =ᵐ[μ1] f ∧ ∫ t, deriv g t ^ 2 ∂μ1 ≤ C := by
  set ω : ℕ → ℝ := fun k => π * (k + 1)
  have hω : ∀ k, ω k ≠ 0 := fun k => by simp only [ω]; positivity
  set b : ℕ → ℝ := fun k => inner ℝ (sb k) f
  have hinner_sb : ∀ k {w : ℝ → ℝ} (hw : Continuous w),
      inner ℝ (sb k) (toHL hw) = ∫ x, sn (k + 1) x * w x ∂μ1 := fun k w hw => by
    rw [sb_apply, inner_toHL_toHL]
  have huAC : ∀ j, AbsolutelyContinuousOnInterval (u j) 0 1 := fun j =>
    ContDiffOn.absolutelyContinuousOnInterval (hu j).contDiffOn
  have hdu : ∀ j, Continuous (deriv (u j)) := fun j => (hu j).continuous_deriv le_rfl
  -- the cosine coefficients of `u_j'`
  set a : ℕ → ℕ → ℝ := fun j k => ∫ x, cs k x * deriv (u j) x ∂μ1
  have ha : ∀ j k, a j k = ω k * ∫ x, sn (k + 1) x * u j x ∂μ1 := fun j k => by
    rw [sn_ibp (huAC j) (h0 j) (h1 j), ← mul_assoc, mul_inv_cancel₀ (hω k), one_mul]
  set α : ℕ → ℝ := fun k => ω k * b k
  have hα : ∀ k, Tendsto (fun j => a j k) atTop (𝓝 (α k)) := fun k => by
    simp only [ha]
    refine Tendsto.const_mul _ ?_
    have := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := sb k)) hlim
    simpa only [hinner_sb] using this
  -- Bessel
  have hbes : ∀ (s : Finset ℕ) j, ∑ k ∈ s, a j k ^ 2 ≤ C := fun s j => by
    have h := cs_orthonormal_HL.sum_inner_products_le (x := toHL (hdu j)) (s := s)
    simp only [inner_toHL_toHL, Real.norm_eq_abs, sq_abs, norm_sq_toHL] at h
    exact h.trans (hC j)
  have hbesα : ∀ s : Finset ℕ, ∑ k ∈ s, α k ^ 2 ≤ C := fun s =>
    le_of_tendsto' (tendsto_finsetSum s fun k _ => (hα k).pow 2) fun j => hbes s j
  have hsum : Summable fun k => α k ^ 2 :=
    summable_of_sum_le (fun k => sq_nonneg _) hbesα
  -- the cosine series `h = Σ α_k cs_k`
  set A : lp (fun _ : ℕ => ℝ) 2 := ⟨α, memℓp_gen (by simpa [Real.norm_eq_abs, sq_abs] using hsum)⟩
  have hV := cs_orthonormal_HL.orthogonalFamily
  set h : HL := hV.linearIsometry A
  have hh : HasSum (fun k => α k • toHL (continuous_cs k)) h := by
    have := hV.hasSum_linearIsometry A
    simpa [LinearIsometry.toSpanSingleton_apply, A] using this
  have hinner_h : ∀ (x : HL), HasSum (fun k => α k * inner ℝ x (toHL (continuous_cs k)))
      (inner ℝ x h) := fun x => by
    simpa [inner_smul_right] using hh.mapL (innerSL ℝ x)
  have hcs_h : ∀ k, inner ℝ (toHL (continuous_cs k)) h = α k := fun k => by
    refine (hinner_h _).unique ?_
    have : (fun i => α i * inner ℝ (toHL (continuous_cs k)) (toHL (continuous_cs i))) =
        fun i => if i = k then α k else 0 := by
      funext i
      rw [inner_toHL_toHL, cs_orthonormal]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik, Ne.symm hik]
    rw [this]; exact hasSum_ite_eq k (α k)
  have hone_h : inner ℝ (toHL (continuous_const (y := (1 : ℝ)))) h = 0 := by
    refine (hinner_h _).unique ?_
    simp [inner_toHL_toHL, integral_cs]
  have hnorm_h : ‖h‖ ^ 2 ≤ C := by
    rw [LinearIsometry.norm_map, ← real_inner_self_eq_norm_sq, ← (lp.hasSum_inner A A).tsum_eq]
    have e : (fun i => inner ℝ (A i) (A i)) = fun i => α i ^ 2 := by
      funext i; simp [A, sq]
    rw [e]
    exact hsum.tsum_le_of_sum_le hbesα
  -- the primitive `g`
  set hf : ℝ → ℝ := (h : ℝ → ℝ)
  have hfint : Integrable hf μ1 := integrable_HL h
  have hII : IntervalIntegrable hf volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hfint
  set g : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, hf t
  have hgAC : AbsolutelyContinuousOnInterval g 0 1 :=
    hII.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hg0 : g 0 = 0 := intervalIntegral.integral_same
  have hg1 : g 1 = 0 := by
    simp only [g]
    rw [← integral_mu1, ← hone_h, real_inner_comm, inner_toHL_right]
    simp [hf]
  have hderiv : ∀ᵐ x ∂μ1, deriv g x = hf x := by
    have := hII.ae_hasDerivAt_integral
    rw [uIcc01] at this
    filter_upwards [ae_restrict_of_ae this, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact (hx (Ioo_subset_Icc_self hxI) 0 ⟨le_rfl, zero_le_one⟩).deriv
  have hsq_int : Integrable (fun x => hf x ^ 2) μ1 :=
    (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable h)).1 (Lp.memLp h)
  have hgd2 : ∫ t, deriv g t ^ 2 ∂μ1 = ‖h‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hderiv] with x hx
    simp [hx, hf, sq]
  have hgH : H10 g := ⟨hgAC, hg0, hg1, hsq_int.congr (by
    filter_upwards [hderiv] with x hx; rw [hx])⟩
  refine ⟨g, hgH, ?_, hgd2 ▸ hnorm_h⟩
  -- `g = f` a.e., by comparing sine coefficients
  set gc := H10.clamp g
  have hgc := H10.continuous_clamp hgH
  have hcoef : ∀ k, inner ℝ (sb k) (toHL hgc) = b k := fun k => by
    rw [hinner_sb]
    have e1 : ∫ x, sn (k + 1) x * gc x ∂μ1 = ∫ x, sn (k + 1) x * g x ∂μ1 :=
      setIntegral_congr_fun measurableSet_Ioo fun x hx => by
        simp only [gc, H10.clamp_eq (Ioo_subset_Icc_self hx)]
    have e2 : ∫ x, cs k x * deriv g x ∂μ1 = α k := by
      rw [← hcs_h k, real_inner_comm, inner_toHL_right]
      refine integral_congr_ae ?_
      filter_upwards [hderiv] with x hx
      rw [hx]; ring
    rw [e1, sn_ibp hgAC hg0 hg1, e2]
    simp only [α]
    rw [← mul_assoc, inv_mul_cancel₀ (hω k), one_mul]
  have heq : toHL hgc = f := by
    rw [← sub_eq_zero]
    refine sn_complete _ fun k hk => ?_
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1' := hinner_sb k' (w := fun x => ((toHL hgc - f : HL) : ℝ → ℝ) x)
    have : inner ℝ (sb k') (toHL hgc - f) = 0 := by
      rw [inner_sub_right, hcoef]; simp [b]
    rw [sb_apply, real_inner_comm, inner_toHL_right] at this
    rw [← this]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  have hae : gc =ᵐ[μ1] f := by
    rw [← heq]; exact (toHL_ae hgc).symm
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [← hx]; exact (H10.clamp_eq (Ioo_subset_Icc_self hxI)).symm

end DFT.Continuum.Line
