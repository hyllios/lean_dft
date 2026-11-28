/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Pittalis
-/
import DFT.Continuum.Line.HK.YoungChamber
import DFT.Continuum.Line.UCP.CollisionTrace
import ForMathlib.Analysis.Sobolev.CubeChamber

/-!
# Weak derivatives on an ordering chamber

Dirichlet and collision traces remove both boundary terms on almost every coordinate line.
-/

namespace DFT.Continuum.Line.CollisionTrace

open MeasureTheory MeasureTheory.UnitCube Set SturmLiouville Filter Topology

variable {n : ℕ}

private theorem line_parts {Φ φ : Cfg n → ℝ} {k : Fin (n + 1)} {y : Fin n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hG : Integrable (fun t => dW k Φ (line k y t)) vol01)
    (hr : ∀ᵐ t ∂vol01, primitive k (dW k Φ) y t = Φ (line k y t))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hz₁ : primitive k (dW k Φ) y a = 0) (hz₂ : primitive k (dW k Φ) y b = 0) :
    (∫ t in Ioo a b, (Φ (line k y t) * dk k φ (line k y t) +
      dW k Φ (line k y t) * φ (line k y t))) = 0 := by
  let F := primitive k (dW k Φ) y
  let g := fun t => φ (line k y t)
  have hg t : HasDerivAt g (dk k φ (line k y t)) t := hasDerivAt_ins hφ.differentiable_one k y t
  have hgc : ContDiff ℝ 1 g := by
    apply hφ.comp
    exact contDiff_pi.2 fun i => by
      rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
      · simp only [line, Fin.insertNth_apply_same]
        exact contDiff_id
      · simp only [line, Fin.insertNth_apply_succAbove]
        exact contDiff_const
  have hsub : uIcc a b ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hab, uIcc01]
    exact Icc_subset_Icc ha hb
  have hI := interval_of_line hG
  have hder : ∀ᵐ t ∂vol01, deriv F t = dW k Φ (line k y t) := by
    have hd := hI.ae_hasDerivAt_integral
    rw [uIcc01] at hd
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t ht hti
    exact (ht (Ioo_subset_Icc_self hti) 0 ⟨le_rfl, zero_le_one⟩).deriv
  have he := ((line_ac hG).mono hsub).integral_deriv_mul_eq_sub
    (hgc.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b))
  rw [hz₁, hz₂, zero_mul, zero_mul, sub_self, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo] at he
  refine Eq.trans (integral_congr_ae ?_) he
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha hb) hr,
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha hb) hder] with t ht hd
  change _ = deriv F t * g t + F t * deriv g t
  change F t = _ at ht
  rw [ht, hd, (hg t).deriv, add_comm]

/-- Multiplication by a chamber indicator preserves weak differentiability when the
Sobolev trace on each possible internal endpoint vanishes. -/
theorem chamber_derivative {Φ : Cfg n → ℝ} (h : H1W Φ)
    (hz : ∀ k j, trace k j Φ h = 0) (k : Fin (n + 1))
    (s : Finset (Fin (n + 1) × Fin (n + 1))) :
    IsWD k ((PairS s).indicator Φ) ((PairS s).indicator (dW k Φ)) := by
  have hs := measurableSet_PairS s
  have hd := memLp_dW_H h k
  refine ⟨hd.indicator hs.nullMeasurableSet, fun φ hφ => ?_⟩
  let W := fun x => Φ x * dk k φ x + dW k Φ x * φ x
  have h₁ := int_mul_cont h.1 (continuous_dk_of_C1 hφ k)
  have h₂ := int_mul_cont hd hφ.continuous
  have hi : Integrable W (μN n) := h₁.add h₂
  have he : (∫ x, (PairS s).indicator W x ∂μN n) = 0 := by
    rw [← line_fubini k (hi.indicator hs)]
    apply integral_eq_zero_of_ae
    obtain ⟨r, hr⟩ := slice_approx h k
    have hz' := ae_all_iff.2 (fun j => (trace_zero h k j).1 (hz k j))
    filter_upwards [hr, hz', ae_all_iff.2 (fun j : Fin n => coordinate_interior j),
      UnitCube.slice_mem k hd] with y hy hzero hcoord hG
    have hbounds (v : ℝ) (hv : Endpoint y v) : v ∈ Icc (0 : ℝ) 1 := by
      rcases hv with rfl | rfl | ⟨j, rfl⟩
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
      · exact Ioo_subset_Icc_self (hcoord j)
    have vanish (v : ℝ) (hv : Endpoint y v) : primitive k (dW k Φ) y v = 0 := by
      rcases hv with rfl | rfl | ⟨j, rfl⟩
      · exact intervalIntegral.integral_same
      · apply tendsto_nhds_unique (hy.1 _ ⟨zero_le_one, le_rfl⟩)
        exact tendsto_const_nhds.congr fun m => (trunc_wall (r m) Φ _ k
          (Or.inr (Fin.insertNth_apply_same ..))).symm
      · exact hzero j
    obtain ⟨a, b, ha, hb, hab⟩ := segment_pairs k y s
    change ∀ t ∈ Ioo (0 : ℝ) 1, line k y t ∈ PairS s ↔ t ∈ Ioo a b at hab
    have heq : (fun t => (PairS s).indicator W (line k y t)) =ᵐ[vol01]
        (Ioo a b).indicator (fun t => W (line k y t)) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))]
        with t ht
      by_cases hm : t ∈ Ioo a b
      · simp [hm, (hab t ht).2 hm]
      · simp [hm, (hab t ht).not.2 hm]
    rw [integral_congr_ae heq, integral_indicator measurableSet_Ioo]
    change (∫ t, W (line k y t) ∂(volume.restrict (Ioo 0 1)).restrict (Ioo a b)) = 0
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2
      (Ioo_subset_Ioo (hbounds a ha).1 (hbounds b hb).2)]
    by_cases hle : a ≤ b
    · exact line_parts hφ (hG.integrable one_le_two) hy.2 (hbounds a ha).1 hle
        (hbounds b hb).2 (vanish a ha) (vanish b hb)
    · simp [Ioo_eq_empty_of_le (le_of_not_ge hle)]
  apply eq_neg_of_add_eq_zero_left
  rw [← integral_add (int_mul_cont (h.1.indicator hs.nullMeasurableSet) (continuous_dk_of_C1 hφ k))
    (int_mul_cont (hd.indicator hs.nullMeasurableSet) hφ.continuous)]
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) he
  by_cases hx : x ∈ PairS s <;> simp [hx, W]

end DFT.Continuum.Line.CollisionTrace
