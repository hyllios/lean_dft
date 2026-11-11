/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Spectral.Operator
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The Green operator is injective

For a smooth `φ` with compact support in `(0, 1)`, `φ = G(-φ'' + W φ)` (uniqueness for the
Dirichlet problem). Hence if `G f = 0` then `⟪f, φ⟫ = ⟪G f, -φ'' + W φ⟫ = 0` for all such `φ`,
and `f = 0` by the fundamental lemma of the calculus of variations.

* `Gk_test`: `G(-φ'' + W φ) = φ` on `[0, 1]`.
* `Gop_injective`: `G f = 0 → f = 0`.
-/

namespace DFT.Continuum.Spectral

open MeasureTheory Set Filter Topology Box

variable {W : ℝ → ℝ} (hWc : Continuous W) (hW0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ W t)

section test

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
  (hsupp : tsupport φ ⊆ Ioo (0 : ℝ) 1)
include hφ hsupp

omit hφ in
lemma test_out : ∀ x, x ∉ Ioo (0 : ℝ) 1 → φ x = 0 := fun _ hx =>
  image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)

omit hsupp in
lemma test_c2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)

/-- The source `-φ'' + W φ`. -/
noncomputable def src (φ : ℝ → ℝ) (x : ℝ) : ℝ := -deriv (deriv φ) x + W x * φ x

include hWc in
omit hsupp in
lemma continuous_src : Continuous (src (W := W) φ) := by
  have h2 : ContDiff ℝ 2 φ := test_c2 hφ
  have hd : ContDiff ℝ 1 (deriv φ) := (contDiff_succ_iff_deriv.1 h2).2.2
  exact ((hd.continuous_deriv le_rfl).neg).add (hWc.mul h2.continuous)

include hW0 in
/-- **`G(-φ'' + W φ) = φ`** on `[0, 1]`. -/
lemma Gk_test {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Gk hWc (src (W := W) φ) x = φ x := by
  have h2 : ContDiff ℝ 2 φ := test_c2 hφ
  have hd1 : Differentiable ℝ φ := h2.differentiable (by norm_num)
  have hdd : ContDiff ℝ 1 (deriv φ) := (contDiff_succ_iff_deriv.1 h2).2.2
  have hd2 : Differentiable ℝ (deriv φ) := hdd.differentiable one_ne_zero
  rw [Gk_eq_Gf hWc (continuous_src hWc hφ) hx]
  have := eq_Gf hWc hW0 (continuous_src hWc hφ) (y := φ) (dy := deriv φ)
    (fun t _ => (hd1 t).hasDerivAt)
    (fun t _ => by
      have h := (hd2 t).hasDerivAt
      refine h.congr_deriv ?_
      simp only [src]; ring)
    (test_out hsupp 0 (fun h => lt_irrefl _ h.1))
    (test_out hsupp 1 (fun h => lt_irrefl _ h.2))
    x (Icc_sub_Ioo' hx)
  exact this.symm

end test

/-- Continuous functions are in `L²(0, 1)`. -/
lemma memLp_of_continuous {g : ℝ → ℝ} (hg : Continuous g) : MemLp g 2 μ1 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_mem_Icc.mono fun y hy => hC y hy)

include hW0 in
/-- **The Green operator is injective.** -/
theorem Gop_injective {f : HL} (hf : Gop hWc f = 0) : f = 0 := by
  -- `∫ φ • f = 0` for every smooth `φ` with compact support in `(0, 1)`
  have horth : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 → ∫ x, φ x • (f : ℝ → ℝ) x = 0 := by
    intro φ hφ _ hsupp
    have hout := test_out hsupp
    have hc := (test_c2 hφ).continuous
    have hsc := continuous_src (W := W) hWc hφ
    set φL : HL := (memLp_of_continuous hc).toLp
    set gL : HL := (memLp_of_continuous hsc).toLp
    -- `G g = φ`
    have hG : Gop hWc gL = φL := by
      refine Lp.ext_iff.2 ?_
      filter_upwards [Gop_ae hWc gL, MemLp.coeFn_toLp (memLp_of_continuous hc),
        ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
      rw [h1, h2, ← Gk_test hWc hW0 hφ hsupp (Ioo_subset_Icc_self hx)]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_of_continuous hsc)] with y hy
      rw [hy]
    have h0 : inner ℝ f φL = 0 := by
      rw [← hG, ← Gop_symm, hf, inner_zero_left]
    rw [L2.inner_def] at h0
    have hμ : ∫ x, φ x * (f : ℝ → ℝ) x ∂μ1 = 0 := by
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_of_continuous hc)] with y hy
      rw [hy]
      simp
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (0 : ℝ) 1)]
    · simpa [smul_eq_mul] using hμ
    · intro x hx; rw [hout x hx, zero_smul]
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (U := Ioo (0 : ℝ) 1)
    (μ := volume) (f := (f : ℝ → ℝ)) isOpen_Ioo
    ((show IntegrableOn (f : ℝ → ℝ) (Ioo (0 : ℝ) 1) volume from
      integrable_HL f).locallyIntegrableOn)
    fun φ hφ hcs hsupp =>
      horth φ hφ hcs hsupp
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact (ae_restrict_iff' measurableSet_Ioo).2 hae

end DFT.Continuum.Spectral
