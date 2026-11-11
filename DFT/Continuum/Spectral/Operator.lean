/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Spectral.Kernel
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Green operator on `L²(0, 1)`: compact and symmetric

On the Hilbert space `HL = L²(0, 1)` the Green kernel defines a bounded operator
`Gop f (x) = ⟪K(x, ·), f⟫`. It factors as `HL → C([0, 1]) → HL`, and the first factor maps the unit
ball to a bounded equicontinuous family (the kernel is uniformly continuous), so by Arzelà–Ascoli
`Gop` is compact. By Fubini and the symmetry of the kernel it is symmetric.

* `HL`: the Hilbert space `L²(0, 1)`.
* `Ksl`: the kernel slices `K(x, ·) ∈ HL`, continuous in `x`.
* `Bop : HL →L[ℝ] C([0, 1])`, `Jop : C([0, 1]) →L[ℝ] HL`, `Gop = Jop ∘ Bop`.
* `isCompactOperator_Bop`, `isCompactOperator_Gop`: compactness (Arzelà–Ascoli).
* `Gop_symm`: symmetry.
-/

namespace DFT.Continuum.Spectral

open MeasureTheory Set Filter Topology Box Metric BoundedContinuousFunction

/-- The Hilbert space `L²(0, 1)`. -/
noncomputable abbrev HL := Lp ℝ 2 μ1

instance : IsFiniteMeasure μ1 := isFiniteMeasure_restrict.2 (by simp)

lemma mu1_univ : μ1 univ = 1 := by simp [Measure.restrict_apply MeasurableSet.univ]

lemma measureUnivNNReal_mu1 : measureUnivNNReal μ1 = 1 := by
  simp [measureUnivNNReal]

lemma integrable_HL (f : HL) : Integrable f μ1 := (Lp.memLp f).integrable one_le_two

variable {W : ℝ → ℝ} (hWc : Continuous W)

/-! ### Kernel slices -/

/-- The kernel slice `K(x, ·)` as an element of `L²(0, 1)`. -/
noncomputable def Ksl (x : Icc (0 : ℝ) 1) : HL :=
  MemLp.toLp (fun y => Kg hWc x y)
    (MemLp.of_bound (aestronglyMeasurable_Kg hWc x.2) (Classical.choose (exists_Kg_bound hWc))
      ((ae_mem_Icc).mono fun y hy => by
        rw [Real.norm_eq_abs]; exact (Classical.choose_spec (exists_Kg_bound hWc)).2 x x.2 y hy))

lemma Ksl_ae (x : Icc (0 : ℝ) 1) : (Ksl hWc x : ℝ → ℝ) =ᵐ[μ1] fun y => Kg hWc x y :=
  MemLp.coeFn_toLp _

/-- `‖K(x, ·) - K(x', ·)‖ ≤ ε` for `x` close to `x'`. -/
lemma norm_Ksl_sub_le (ε : ℝ) (hε : 0 < ε) : ∃ δ, 0 < δ ∧ ∀ x x' : Icc (0 : ℝ) 1,
    |(x : ℝ) - x'| < δ → ‖Ksl hWc x - Ksl hWc x'‖ ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := Kg_unif hWc ε hε
  refine ⟨δ, hδ, fun x x' hxx => ?_⟩
  have hb := Lp.norm_le_of_ae_bound (f := Ksl hWc x - Ksl hWc x') (p := 2) hε.le (by
    filter_upwards [Lp.coeFn_sub (Ksl hWc x) (Ksl hWc x'), Ksl_ae hWc x, Ksl_ae hWc x',
      ae_mem_Icc] with y h1 h2 h3 hy
    rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
    exact (h x x.2 x' x'.2 hxx y hy).le)
  simpa [measureUnivNNReal_mu1] using hb

lemma continuous_Ksl : Continuous (Ksl hWc) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨δ, hδ, h⟩ := norm_Ksl_sub_le hWc (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun x' hx' => ?_⟩
  rw [dist_eq_norm]
  have : |(x' : ℝ) - x| < δ := by
    rw [Subtype.dist_eq, Real.dist_eq] at hx'; exact hx'
  linarith [h x' x this]

lemma norm_Ksl_le : ∃ C, 0 ≤ C ∧ ∀ x : Icc (0 : ℝ) 1, ‖Ksl hWc x‖ ≤ C := by
  obtain ⟨C, hC0, hCb⟩ := exists_Kg_bound hWc
  refine ⟨C, hC0, fun x => ?_⟩
  have hb := Lp.norm_le_of_ae_bound (f := Ksl hWc x) (p := 2) hC0 (by
    filter_upwards [Ksl_ae hWc x, ae_mem_Icc] with y h1 hy
    rw [h1, Real.norm_eq_abs]; exact hCb x x.2 y hy)
  simpa [measureUnivNNReal_mu1] using hb

/-- The Green operator is the inner product with the kernel slice. -/
lemma Gk_eq_inner (f : HL) (x : Icc (0 : ℝ) 1) : Gk hWc f x = inner ℝ (Ksl hWc x) f := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Ksl_ae hWc x] with y hy
  rw [hy]
  simp [mul_comm]

/-! ### The factorisation through continuous functions -/

/-- `f ↦ (x ↦ ⟪K(x, ·), f⟫)` into bounded continuous functions on `[0, 1]`. -/
noncomputable def Bop : HL →L[ℝ] (Icc (0 : ℝ) 1 →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.mkOfCompact
        ⟨fun x => inner ℝ (Ksl hWc x) f, (continuous_Ksl hWc).inner continuous_const⟩
      map_add' := fun f g => by ext x; simp [inner_add_right]
      map_smul' := fun r f => by ext x; simp [inner_smul_right] }
    (Classical.choose (norm_Ksl_le hWc)) fun f => by
      have hC := Classical.choose_spec (norm_Ksl_le hWc)
      refine (BoundedContinuousFunction.norm_le (mul_nonneg hC.1 (norm_nonneg f))).2 fun x => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, BoundedContinuousFunction.mkOfCompact_apply,
        ContinuousMap.coe_mk, Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hC.2 x) (norm_nonneg _))

lemma Bop_apply (f : HL) (x : Icc (0 : ℝ) 1) : Bop hWc f x = inner ℝ (Ksl hWc x) f := rfl

lemma memLp_comp_projIcc (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    MemLp (fun x => g (projIcc 0 1 zero_le_one x)) 2 μ1 :=
  MemLp.of_bound ((g.continuous.comp continuous_projIcc).aestronglyMeasurable) ‖g‖
    (ae_of_all _ fun _ => g.norm_coe_le_norm _)

/-- The embedding of continuous functions on `[0, 1]` into `L²(0, 1)`. -/
noncomputable def Jop : (Icc (0 : ℝ) 1 →ᵇ ℝ) →L[ℝ] HL :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_comp_projIcc g).toLp
      map_add' := fun g h => by
        rw [← MemLp.toLp_add]; rfl
      map_smul' := fun r g => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]; rfl }
    1 fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have hb := Lp.norm_le_of_ae_bound (f := (memLp_comp_projIcc g).toLp) (p := 2)
        (norm_nonneg g) (by
          filter_upwards [MemLp.coeFn_toLp (memLp_comp_projIcc g)] with x hx
          rw [hx]; exact g.norm_coe_le_norm _)
      simpa [measureUnivNNReal_mu1] using hb

/-- **The Green operator on `L²(0, 1)`.** -/
noncomputable def Gop : HL →L[ℝ] HL := (Jop).comp (Bop hWc)

lemma Gop_ae (f : HL) : (Gop hWc f : ℝ → ℝ) =ᵐ[μ1] Gk hWc f := by
  filter_upwards [MemLp.coeFn_toLp (memLp_comp_projIcc (Bop hWc f)),
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  change (Jop (Bop hWc f) : ℝ → ℝ) x = _
  simp only [Jop, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
  rw [hx, Bop_apply, ← Gk_eq_inner]
  congr 1
  simp [projIcc_of_mem _ (Ioo_subset_Icc_self hxI)]

/-! ### Compactness -/

/-- **`Bop` is compact** (Arzelà–Ascoli). -/
theorem isCompactOperator_Bop : IsCompactOperator (Bop hWc) := by
  obtain ⟨C, hC0, hC⟩ := norm_Ksl_le hWc
  set A := Bop hWc '' closedBall 0 1
  have hcpt : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (Icc (-C) C) isCompact_Icc A
      (fun g x hg => ?_) ?_
    · obtain ⟨f, hf, rfl⟩ := hg
      rw [mem_closedBall, dist_zero_right] at hf
      rw [Bop_apply, mem_Icc, ← abs_le]
      have h1 := abs_real_inner_le_norm (Ksl hWc x) f
      have h2 : ‖Ksl hWc x‖ * ‖f‖ ≤ C := by
        nlinarith [hC x, norm_nonneg f, norm_nonneg (Ksl hWc x)]
      linarith
    · intro x0
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      have hcx := (continuous_Ksl hWc).continuousAt (x := x0)
      rw [Metric.continuousAt_iff] at hcx
      obtain ⟨δ, hδ, hδc⟩ := hcx (ε / 2) (by positivity)
      refine ⟨δ, hδ, fun x hx g => ?_⟩
      obtain ⟨_, ⟨f, hf, rfl⟩⟩ := g
      rw [mem_closedBall, dist_zero_right] at hf
      simp only [Real.dist_eq, Bop_apply]
      rw [← inner_sub_left]
      have h1 := hδc hx
      rw [dist_eq_norm] at h1
      rw [← norm_neg, neg_sub] at h1
      calc |inner ℝ (Ksl hWc x0 - Ksl hWc x) f| ≤ ‖Ksl hWc x0 - Ksl hWc x‖ * ‖f‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ε / 2 * 1 := mul_le_mul h1.le hf (norm_nonneg _) (by positivity)
        _ < ε := by linarith
  refine ⟨closure A, hcpt, ?_⟩
  refine Filter.mem_of_superset (closedBall_mem_nhds 0 one_pos) fun f hf => ?_
  exact subset_closure ⟨f, hf, rfl⟩

/-- **The Green operator is compact.** -/
theorem isCompactOperator_Gop : IsCompactOperator (Gop hWc) :=
  (isCompactOperator_Bop hWc).clm_comp Jop

/-! ### Symmetry -/

lemma prod_mu1 :
    (μ1.prod μ1 : Measure (ℝ × ℝ)) = volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

lemma integrable_kernel_prod {f g : ℝ → ℝ} (hf : Integrable f μ1) (hg : Integrable g μ1) :
    Integrable (fun z : ℝ × ℝ => Kg hWc z.1 z.2 * (g z.1 * f z.2)) (μ1.prod μ1) := by
  obtain ⟨C, -, hC⟩ := exists_Kg_bound hWc
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => Kg hWc z.1 z.2) (μ1.prod μ1) := by
    rw [prod_mu1]
    exact ((continuousOn_Kg hWc).mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
      |>.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)
  have hb : ∀ᵐ z ∂(μ1.prod μ1), ‖Kg hWc z.1 z.2‖ ≤ C := by
    rw [prod_mu1]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    rw [Real.norm_eq_abs]
    exact hC _ (Ioo_subset_Icc_self hz.1) _ (Ioo_subset_Icc_self hz.2)
  exact (hg.mul_prod hf).bdd_mul hm hb

lemma inner_Gop (f g : HL) :
    inner ℝ (Gop hWc f) g = ∫ x, (∫ y, Kg hWc x y * f y ∂μ1) * g x ∂μ1 := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Gop_ae hWc f] with x hx
  rw [hx]
  simp [Gk, mul_comm]

/-- **The Green operator is symmetric.** -/
theorem Gop_symm (f g : HL) : inner ℝ (Gop hWc f) g = inner ℝ f (Gop hWc g) := by
  rw [real_inner_comm (Gop hWc g) f, inner_Gop, inner_Gop]
  have hF := integrable_kernel_prod hWc (integrable_HL f) (integrable_HL g)
  have hG := integrable_kernel_prod hWc (integrable_HL g) (integrable_HL f)
  have e1 : ∫ x, (∫ y, Kg hWc x y * f y ∂μ1) * g x ∂μ1 =
      ∫ z, Kg hWc z.1 z.2 * (g z.1 * f z.2) ∂(μ1.prod μ1) := by
    rw [integral_prod _ hF]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← integral_mul_const]
    congr 1; funext y; ring
  have e2 : ∫ x, (∫ y, Kg hWc x y * g y ∂μ1) * f x ∂μ1 =
      ∫ z, Kg hWc z.1 z.2 * (f z.1 * g z.2) ∂(μ1.prod μ1) := by
    rw [integral_prod _ hG]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← integral_mul_const]
    congr 1; funext y; ring
  rw [e1, e2, ← integral_prod_swap]
  congr 1; funext z
  simp only [Prod.fst_swap, Prod.snd_swap, Kg_symm hWc z.2 z.1]
  ring

/-- `Gop` as a symmetric linear map. -/
theorem isSymmetric_Gop : (Gop hWc : HL →ₗ[ℝ] HL).IsSymmetric := fun f g => Gop_symm hWc f g

end DFT.Continuum.Spectral
