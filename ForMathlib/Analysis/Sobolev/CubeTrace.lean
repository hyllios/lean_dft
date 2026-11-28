/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Pittalis
-/
import ForMathlib.Analysis.SturmLiouville.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Traces of coordinate primitives on the unit cube

The face measure uses the remaining coordinates. The primitive of a square-integrable
field has an L² face value with operator norm at most one.
-/

namespace MeasureTheory.UnitCube

open Set Filter Topology SturmLiouville

/-- Lebesgue measure restricted to the open unit cube. -/
noncomputable abbrev cubeVolume (d : ℕ) : Measure (Fin d → ℝ) :=
  volume.restrict (univ.pi fun _ => Ioo (0 : ℝ) 1)

/-- Product Lebesgue measure in the free face coordinates. -/
noncomputable abbrev productVolume (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => vol01

local instance : IsProbabilityMeasure vol01 := ⟨by simp⟩

private theorem cubeVolume_eq (d : ℕ) : cubeVolume d = productVolume d := by
  rw [productVolume, ← Measure.restrict_pi_pi, ← volume_pi]

local instance (d : ℕ) : IsFiniteMeasure (cubeVolume d) := by
  rw [cubeVolume_eq]
  infer_instance

variable {n : ℕ}

/-- Insert the free coordinate into a coordinate line of the cube. -/
abbrev line (k : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) : (Fin (n + 1) → ℝ) := Fin.insertNth k t y

private noncomputable def split (k : Fin (n + 1)) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm

private theorem split_mp (k : Fin (n + 1)) :
    MeasurePreserving (split k) ((productVolume n).prod vol01) (cubeVolume (n + 1)) := by
  rw [cubeVolume_eq]
  exact ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => vol01) k).symm).comp
    (Measure.measurePreserving_swap)

theorem line_int {F : (Fin (n + 1) → ℝ) → ℝ} (k : Fin (n + 1))
    (h : Integrable F (cubeVolume (n + 1))) :
    Integrable (fun p : (Fin n → ℝ) × ℝ => F (line k p.1 p.2)) ((productVolume n).prod vol01) :=
  ((split_mp k).integrable_comp_emb (split k).measurableEmbedding).2 h

theorem line_fubini {F : (Fin (n + 1) → ℝ) → ℝ} (k : Fin (n + 1))
    (h : Integrable F (cubeVolume (n + 1))) :
    (∫ y, ∫ t, F (line k y t) ∂vol01 ∂productVolume n) = ∫ x, F x ∂cubeVolume (n + 1) :=
  (integral_prod _ (line_int k h)).symm.trans
    ((split_mp k).integral_comp (split k).measurableEmbedding F)

theorem line_ae {p : (Fin (n + 1) → ℝ) → Prop} (k : Fin (n + 1))
    (h : ∀ᵐ x ∂cubeVolume (n + 1), p x) :
    ∀ᵐ y ∂productVolume n, ∀ᵐ t ∂vol01, p (line k y t) :=
  Measure.ae_ae_of_ae_prod ((split_mp k).quasiMeasurePreserving.ae h)

theorem coordinate_interior (j : Fin n) : ∀ᵐ y ∂productVolume n, y j ∈ Ioo (0 : ℝ) 1 :=
  (measurePreserving_eval (fun _ : Fin n => vol01) j).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Ioo)

theorem vanishing_subsequence {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {e : ℕ → α → ℝ} (hi : ∀ m, Integrable (e m) μ) (hn : ∀ m x, 0 ≤ e m x)
    (hl : Tendsto (fun m => ∫ x, e m x ∂μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ x ∂μ, Tendsto (fun m => e (s m) x) atTop (𝓝 0) := by
  apply TendstoInMeasure.exists_seq_tendsto_ae (g := fun _ => 0)
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
  have eqn m : eLpNorm (e m - fun _ => 0) 1 μ = ENNReal.ofReal (∫ x, e m x ∂μ) := by
    change eLpNorm (e m - 0) 1 μ = _
    rw [sub_zero, eLpNorm_one_eq_lintegral_eNorm (hi m).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_eNorm (hi m)]
    simp [Real.norm_eq_abs, abs_of_nonneg (hn m _)]
  simpa only [eqn, ENNReal.ofReal_zero] using (ENNReal.tendsto_ofReal hl :
    Tendsto (fun m => ENNReal.ofReal (∫ x, e m x ∂μ)) atTop (𝓝 (ENNReal.ofReal 0)))

theorem interval_of_line {g : ℝ → ℝ} (h : Integrable g vol01) :
    IntervalIntegrable g volume 0 1 := by
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 h

theorem abs_primitive_le {g : ℝ → ℝ} (h : Integrable g vol01) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |∫ t in a..b, g t| ≤ ∫ t, |g t| ∂vol01 := by
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_set h.abs (ae_of_all _ fun _ => abs_nonneg _)
    (Eventually.of_forall (fun _ ht => Ioo_subset_Ioo ha hb ht))

/-- Integrate from the Dirichlet wall with particle k moving and the others fixed. -/
noncomputable def primitive (k : Fin (n + 1)) (G : (Fin (n + 1) → ℝ) → ℝ) (y : Fin n → ℝ) (t : ℝ) :=
  ∫ s in (0 : ℝ)..t, G (line k y s)

/-- Evaluate the primitive where the moving coordinate equals the fixed coordinate indexed by j. -/
noncomputable def face (k : Fin (n + 1)) (j : Fin n) (G : (Fin (n + 1) → ℝ) → ℝ) (y : Fin n → ℝ) :=
  primitive k G y (y j)

theorem slice_mem {G : (Fin (n + 1) → ℝ) → ℝ} (k : Fin (n + 1))
    (h : MemLp G 2 (cubeVolume (n + 1))) :
    ∀ᵐ y ∂productVolume n, MemLp (fun t => G (line k y t)) 2 vol01 := by
  filter_upwards [(line_int k (h.integrable one_le_two)).prod_right_ae,
    (line_int k ((memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h)).prod_right_ae]
    with y h1 h2
  exact (memLp_two_iff_integrable_sq h1.aestronglyMeasurable).2 h2

theorem face_bound {G : (Fin (n + 1) → ℝ) → ℝ} (k : Fin (n + 1)) (j : Fin n)
    (h : MemLp G 2 (cubeVolume (n + 1))) :
    ∀ᵐ y ∂productVolume n, (face k j G y) ^ 2 ≤ ∫ t, G (line k y t) ^ 2 ∂vol01 := by
  filter_upwards [slice_mem k h, coordinate_interior j] with y hy ht
  have hle := abs_primitive_le (hy.integrable one_le_two) le_rfl ht.1.le ht.2.le
  have hv := ProbabilityTheory.variance_nonneg (fun t => |G (line k y t)|) vol01
  rw [ProbabilityTheory.variance_eq_sub
    (show MemLp (fun t => |G (line k y t)|) 2 vol01 from hy.norm)] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  change |face k j G y| ≤ ∫ t, |G (line k y t)| ∂vol01 at hle
  have hs := mul_self_le_mul_self (abs_nonneg _) hle
  rw [← sq, sq_abs, ← sq] at hs
  exact hs.trans (sub_nonneg.mp hv)
theorem line_ac {G : (Fin (n + 1) → ℝ) → ℝ} {k : Fin (n + 1)} {y : Fin n → ℝ}
    (hi : Integrable (fun t => G (line k y t)) vol01) :
    AbsolutelyContinuousOnInterval (primitive k G y) 0 1 :=
  (interval_of_line hi).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)

/-- Face evaluation of the primitive is measurable for every square-integrable field. -/
theorem face_meas {G : (Fin (n + 1) → ℝ) → ℝ} (k : Fin (n + 1)) (j : Fin n)
    (h : MemLp G 2 (cubeVolume (n + 1))) : AEStronglyMeasurable (face k j G) (productVolume n) := by
  let H := {x : Fin (n + 1) → ℝ | x k < x (k.succAbove j)}
  have hm : MeasurableSet H := measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)
  have hi := (line_int k ((h.integrable one_le_two).indicator hm)).integral_prod_left
  apply hi.aestronglyMeasurable.congr
  filter_upwards [coordinate_interior j] with y hy
  change (∫ t, H.indicator G (line k y t) ∂vol01) = ∫ t in (0 : ℝ)..y j, G (line k y t)
  have eqn : (fun t => H.indicator G (line k y t)) =
      (Iio (y j)).indicator (fun t => G (line k y t)) := by
    funext t
    by_cases ht : t < y j <;> simp [H, Set.indicator, line, ht]
  rw [eqn, integral_indicator measurableSet_Iio, intervalIntegral.integral_of_le hy.1.le,
    integral_Ioc_eq_integral_Ioo]
  change (∫ t, G (line k y t) ∂(volume.restrict (Ioo 0 1)).restrict (Iio (y j))) = _
  rw [Measure.restrict_restrict measurableSet_Iio]
  congr 2
  ext t
  simp only [mem_inter_iff, mem_Iio, mem_Ioo]
  grind

/-- Restrict the primitive of an L² field to a coordinate coincidence face. -/
theorem face_mem {G : (Fin (n + 1) → ℝ) → ℝ} (k : Fin (n + 1)) (j : Fin n)
    (h : MemLp G 2 (cubeVolume (n + 1))) : MemLp (face k j G) 2 (productVolume n) := by
  have hm := face_meas k j h
  apply (memLp_two_iff_integrable_sq hm).2
  have hi := (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h
  refine (line_int k hi).integral_prod_left.mono' (hm.pow 2) ?_
  filter_upwards [face_bound k j h] with y hy
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hy

/-- The L² face value of the primitive based at the left wall. -/
noncomputable def faceTrace (k : Fin (n + 1)) (j : Fin n) (G : (Fin (n + 1) → ℝ) → ℝ)
    (h : MemLp G 2 (cubeVolume (n + 1))) : Lp ℝ 2 (productVolume n) :=
  (face_mem k j h).toLp _

private lemma interval_to {g : ℝ → ℝ} (hg : Integrable g vol01) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable g volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).2
    ((show IntegrableOn g (Ioo (0 : ℝ) 1) volume from hg).mono_set (Ioo_subset_Ioo_right ht.2))

/-- The face operator is a contraction in squared L² norm. -/
theorem faceTrace_sub_bound (k : Fin (n + 1)) (j : Fin n) {F J : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (cubeVolume (n + 1))) (hJ : MemLp J 2 (cubeVolume (n + 1))) :
    (∫ y, (faceTrace k j F hF y - faceTrace k j J hJ y) ^ 2 ∂productVolume n) ≤
      ∫ x, (F x - J x) ^ 2 ∂cubeVolume (n + 1) := by
  let G := F - J
  have hG : MemLp G 2 (cubeVolume (n + 1)) := hF.sub hJ
  change _ ≤ ∫ x, G x ^ 2 ∂cubeVolume (n + 1)
  have hi := (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).1 hG
  rw [← line_fubini (F := fun x => G x ^ 2) k hi]
  have hm := (Lp.memLp (faceTrace k j F hF)).sub (Lp.memLp (faceTrace k j J hJ))
  refine integral_mono_ae ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1 hm)
    (line_int k hi).integral_prod_left ?_
  have hf : ⇑(faceTrace k j F hF) =ᵐ[productVolume n] face k j F := MemLp.coeFn_toLp _
  have hf' : ⇑(faceTrace k j J hJ) =ᵐ[productVolume n] face k j J := MemLp.coeFn_toLp _
  filter_upwards [face_bound k j hG, hf, hf', coordinate_interior j,
    slice_mem k hF, slice_mem k hJ] with y hb hf₁ hf₂ ht hd hd'
  rw [hf₁, hf₂]
  convert hb using 2
  unfold face primitive
  exact (intervalIntegral.integral_sub
    (interval_to (hd.integrable one_le_two) (Ioo_subset_Icc_self ht))
    (interval_to (hd'.integrable one_le_two) (Ioo_subset_Icc_self ht))).symm

end MeasureTheory.UnitCube
