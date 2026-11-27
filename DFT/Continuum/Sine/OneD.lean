/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.Analysis.SturmLiouville.Expand

/-!
# The sine basis of `L²(0, 1)`

The functions `sₖ(x) = √2 sin(πkx)`, `k ≥ 1`, are orthonormal and complete in `L²(0, 1)`.

Orthonormality is the integral `∫₀¹ cos(πjx) dx = [j = 0]` for integers `j`. Completeness comes from
the eigenbasis of the Green operator of `-d²/dx²` (`Continuum/Spectral`). Every eigenfunction solves
`g'' = -ω² g` with `g(0) = g(1) = 0`, and two Wronskians, with `sin(ωx)` and with `cos(ωx)`,
show that `g` is a multiple of `sin(ωx)`, so `ω = πk`. A function orthogonal to every sine is
therefore orthogonal to every eigenvector, hence zero.

* `sn`, `integral_cos_int`, `sn_orthonormal`.
* `eq_sin_of_ode`: a solution of `g'' = -ω² g` with `g(0) = 0` is `g'(0) sin(ωx) / ω` on `[0, 1]`.
* `sn_complete`: **completeness**.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology SturmLiouville Real

/-- The sine `√2 sin(πkx)`. -/
noncomputable def sn (k : ℕ) (x : ℝ) : ℝ := √2 * Real.sin (π * k * x)

lemma continuous_sn (k : ℕ) : Continuous (sn k) := by unfold sn; fun_prop

/-- `∫₀¹ cos(πjx) dx = [j = 0]` for integers `j`. -/
lemma integral_cos_int (j : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (π * j * x) = if j = 0 then 1 else 0 := by
  split_ifs with hj
  · simp [hj]
  · have hc : (π * j : ℝ) ≠ 0 := mul_ne_zero pi_ne_zero (by exact_mod_cast hj)
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have := Real.sin_int_mul_pi j
    rw [mul_comm] at this
    simp [this]

lemma two_sin_mul_sin (a b : ℝ) :
    2 * (Real.sin a * Real.sin b) = Real.cos (a - b) - Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- **Orthonormality.** -/
lemma sn_orthonormal {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    ∫ x, sn k x * sn l x ∂μ1 = if k = l then 1 else 0 := by
  rw [integral_mu1]
  have e : ∀ x, sn k x * sn l x =
      Real.cos (π * ((k : ℤ) - l : ℤ) * x) - Real.cos (π * ((k : ℤ) + l : ℤ) * x) := by
    intro x
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    simp only [sn]
    push_cast
    rw [show π * ((k : ℝ) - l) * x = π * k * x - π * l * x by ring,
      show π * ((k : ℝ) + l) * x = π * k * x + π * l * x by ring, ← two_sin_mul_sin]
    linear_combination (Real.sin (π * k * x) * Real.sin (π * l * x)) * h2
  simp only [e]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_cos_int, integral_cos_int]
  have hkl : ((k : ℤ) + l) ≠ 0 := by omega
  by_cases h : k = l
  · subst h; simp; omega
  · have : ((k : ℤ) - l) ≠ 0 := by omega
    simp [h, this, hkl]

/-! ### Solutions of `g'' = -ω² g` -/

/-- A `C²` solution of `g'' = -ω² g` on `[0, 1]` with `g(0) = 0` is `g'(0) sin(ωx) / ω`. -/
lemma eq_sin_of_ode {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {ω : ℝ} (hω : 0 < ω) (h0 : g 0 = 0)
    (hode : ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv g) x = -ω ^ 2 * g x) :
    ∀ x ∈ Icc (0 : ℝ) 1, g x = deriv g 0 / ω * Real.sin (ω * x) := by
  have hd1 : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    ((hg.differentiable (by norm_num)) x).hasDerivAt
  have hdd : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.1 hg).2.2
  have hd2 : ∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x := fun x =>
    ((hdd.differentiable one_ne_zero) x).hasDerivAt
  have hs : ∀ x, HasDerivAt (fun x => Real.sin (ω * x)) (ω * Real.cos (ω * x)) x := fun x => by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul ω).sin
  have hc : ∀ x, HasDerivAt (fun x => Real.cos (ω * x)) (-(ω * Real.sin (ω * x))) x := fun x => by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul ω).cos
  -- the two Wronskians are constant on `[0, 1]`
  set F1 : ℝ → ℝ := fun x => deriv g x * Real.sin (ω * x) - ω * g x * Real.cos (ω * x)
  set F2 : ℝ → ℝ := fun x => deriv g x * Real.cos (ω * x) + ω * g x * Real.sin (ω * x)
  have hcont1 : Continuous F1 := by
    have := hdd.continuous; have := hg.continuous; simp only [F1]; fun_prop
  have hcont2 : Continuous F2 := by
    have := hdd.continuous; have := hg.continuous; simp only [F2]; fun_prop
  have hF1 : ∀ x ∈ Icc (0 : ℝ) 1, F1 x = F1 0 := by
    refine constant_of_has_deriv_right_zero hcont1.continuousOn fun x hx => ?_
    have h := ((hd2 x).mul (hs x)).sub (((hd1 x).const_mul ω).mul (hc x))
    refine (h.congr_deriv ?_).hasDerivWithinAt
    rw [hode x (Ico_subset_Icc_self hx)]; ring
  have hF2 : ∀ x ∈ Icc (0 : ℝ) 1, F2 x = F2 0 := by
    refine constant_of_has_deriv_right_zero hcont2.continuousOn fun x hx => ?_
    have h := ((hd2 x).mul (hc x)).add (((hd1 x).const_mul ω).mul (hs x))
    refine (h.congr_deriv ?_).hasDerivWithinAt
    rw [hode x (Ico_subset_Icc_self hx)]; ring
  intro x hx
  have e1 := hF1 x hx
  have e2 := hF2 x hx
  simp only [F1, F2, mul_zero, Real.sin_zero, Real.cos_zero, h0, mul_one, sub_zero,
    add_zero] at e1 e2
  have hsc := Real.sin_sq_add_cos_sq (ω * x)
  have key : ω * g x = deriv g 0 * Real.sin (ω * x) := by
    have : ω * g x = F2 x * Real.sin (ω * x) - F1 x * Real.cos (ω * x) := by
      simp only [F1, F2]; linear_combination (-(ω * g x)) * hsc
    rw [this]; simp only [F1, F2] at e1 e2 ⊢; rw [e1, e2]; ring
  field_simp
  linarith

/-! ### Completeness -/

lemma inner_eB_HL {W : ℝ → ℝ} (hWc : Continuous W) (hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t)
    (i : SturmLiouville.Idx hWc) (f : SturmLiouville.HL) :
    inner ℝ (SturmLiouville.eB hWc hW0 i) f = ∫ x, SturmLiouville.rep hWc hW0 i x * f x ∂μ1 := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SturmLiouville.rep_ae hWc hW0 i] with x hx
  rw [hx]; simp [mul_comm]

/-- **The sines are complete in `L²(0, 1)`.** -/
theorem sn_complete (f : SturmLiouville.HL) (h : ∀ k : ℕ, 0 < k → ∫ x, sn k x * f x ∂μ1 = 0) :
    f = 0 := by
  set W : ℝ → ℝ := fun _ => 0
  have hWc : Continuous W := continuous_const
  have hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t := fun _ _ => le_rfl
  set b := SturmLiouville.eB hWc hW0
  have horth : ∀ i, inner ℝ (b i) f = 0 := by
    intro i
    rw [inner_eB_HL]
    set g := SturmLiouville.rep hWc hW0 i
    have hgD : g ∈ SturmLiouville.Dom := SturmLiouville.rep_mem hWc hW0 i
    have hμ := SturmLiouville.mu_pos hWc hW0 i
    set ω := √((SturmLiouville.mu hWc i)⁻¹)
    have hω : 0 < ω := Real.sqrt_pos.2 (inv_pos.2 hμ)
    have hω2 : ω ^ 2 = (SturmLiouville.mu hWc i)⁻¹ := Real.sq_sqrt (inv_pos.2 hμ).le
    have hsin := eq_sin_of_ode hgD.1 hω hgD.2.1 fun x hx => by
      rw [SturmLiouville.rep_ode hWc hW0 i x hx, hω2]; simp [W, g]
    -- either `g'(0) = 0` and `g = 0`, or `sin ω = 0`
    have hzero : ∀ x ∈ Ioo (0 : ℝ) 1, g x = 0 ∨ ∃ k : ℕ, 0 < k ∧
        ∀ y ∈ Ioo (0 : ℝ) 1, g y = deriv g 0 / ω / √2 * sn k y := by
      intro x hx
      by_cases hd : deriv g 0 = 0
      · left; rw [hsin x (Ioo_subset_Icc_self hx), hd]; simp
      · right
        have h1 := hsin 1 ⟨zero_le_one, le_rfl⟩
        rw [hgD.2.2, mul_one] at h1
        have hs0 : Real.sin ω = 0 := by
          rcases mul_eq_zero.1 h1.symm with h | h
          · exact absurd h (div_ne_zero hd hω.ne')
          · exact h
        obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 hs0
        have hmpos : 0 < m := by
          have : (0 : ℝ) < m * π := hm ▸ hω
          exact_mod_cast (pos_of_mul_pos_left this pi_pos.le)
        refine ⟨m.toNat, by omega, fun y hy => ?_⟩
        rw [hsin y (Ioo_subset_Icc_self hy), sn, ← hm]
        have hmn : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hmpos.le
        rw [hmn]
        have h2 : √2 ≠ 0 := by positivity
        field_simp
    by_cases hall : ∀ x ∈ Ioo (0 : ℝ) 1, g x = 0
    · refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [hall x hx, zero_mul]; rfl
    · push Not at hall
      obtain ⟨x0, hx0, hgx0⟩ := hall
      obtain ⟨k, hk, hgk⟩ := (hzero x0 hx0).resolve_left hgx0
      rw [show ∫ x, g x * f x ∂μ1 = ∫ x, (deriv g 0 / ω / √2) * (sn k x * f x) ∂μ1 from
        integral_congr_ae (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
          rw [hgk y hy]; ring),
        integral_const_mul, h k hk, mul_zero]
  have hsum := b.hasSum_repr f
  have : (fun i => b.repr f i • b i) = fun _ => 0 := by
    funext i; rw [b.repr_apply_apply, horth i, zero_smul]
  rw [this] at hsum
  exact hsum.unique hasSum_zero

/-! ### The sine Hilbert basis and Parseval -/

lemma sn_orthonormal_succ : Orthonormal ℝ fun k : ℕ => SturmLiouville.toHL (continuous_sn (k + 1)) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [SturmLiouville.inner_toHL_toHL, sn_orthonormal (Nat.succ_pos k) (Nat.succ_pos l)]
  exact if_congr (by omega) rfl rfl

lemma sn_span_orthogonal :
    (Submodule.span ℝ (Set.range fun k : ℕ => SturmLiouville.toHL (continuous_sn (k + 1))))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  refine sn_complete f fun k hk => ?_
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self (f := fun k : ℕ =>
      SturmLiouville.toHL (continuous_sn (k + 1))) k')) hf
  rw [real_inner_comm, SturmLiouville.inner_toHL_right] at h
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- **The sine Hilbert basis** `(√2 sin(π(k+1)x))ₖ` of `L²(0, 1)`. -/
noncomputable def sb : HilbertBasis ℕ ℝ SturmLiouville.HL :=
  HilbertBasis.mkOfOrthogonalEqBot sn_orthonormal_succ sn_span_orthogonal

lemma sb_apply (k : ℕ) : sb k = SturmLiouville.toHL (continuous_sn (k + 1)) := by
  rw [sb, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- **Parseval** for a continuous function, in `ℝ≥0∞`. -/
theorem parseval1 {g : ℝ → ℝ} (hg : Continuous g) :
    ∑' k : ℕ, ENNReal.ofReal ((∫ x, sn (k + 1) x * g x ∂μ1) ^ 2) =
      ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ1 := by
  have h := sb.hasSum_inner_mul_inner (SturmLiouville.toHL hg) (SturmLiouville.toHL hg)
  simp only [sb_apply, SturmLiouville.inner_toHL_toHL] at h
  have e : ∀ k, (∫ x, g x * sn (k + 1) x ∂μ1) * ∫ x, sn (k + 1) x * g x ∂μ1 =
      (∫ x, sn (k + 1) x * g x ∂μ1) ^ 2 := fun k => by
    rw [sq]; congr 1; exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  simp only [e] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) h.summable, h.tsum_eq,
    ofReal_integral_eq_lintegral_ofReal (f := fun x => g x * g x)
      (SturmLiouville.integrable_of_continuous (hg.mul hg)) (ae_of_all _ fun x => mul_self_nonneg _)]
  simp only [sq]

end DFT.Continuum.Sine
