/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeuGS
import DFT.Continuum.Line.Complete

/-!
# The cosine basis: Neumann walls

The functions `c₀ = 1`, `c_{k+1}(x) = √2 cos(π(k+1)x)` are orthonormal and complete in
`L²(0, 1)`, and their products are a Hilbert basis of `L²` of the cube. They play for Neumann walls
the role the sines play for Dirichlet walls.

* `cn`, `cn_orthonormal`.
* **`cn_complete`**: completeness. If `f ⊥ c_k` for all `k`, then `F = ∫₀ᵗ f` vanishes at `0` and
  `1` (`c₀ = 1`), and integration by parts gives `⟨s_{k+1}, F⟩ = ⟨c_{k+1}, f⟩ / (π(k+1)) = 0`;
  by completeness of the sines `F = 0`, so `f = F' = 0`.
* `cb`, `parsevalC1`: the cosine Hilbert basis of `L²(0, 1)` and Parseval for continuous functions.
* `cmd`, `cmd_orthonormal`, `parsevalC`: products on the cube and Parseval for continuous
  functions; `eC`, `eC_complete`, `bC`, **`parsevalCW`**: Parseval for `L²` functions on the cube.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Spectral

/-! ### One dimension -/

/-- The cosines `c₀ = 1`, `c_{k+1} = √2 cos(π(k+1)x)`. -/
noncomputable def cn : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | k + 1 => cs k

lemma continuous_cn (k : ℕ) : Continuous (cn k) := by
  cases k with
  | zero => exact continuous_const
  | succ k => exact continuous_cs k

lemma cn_orthonormal (k l : ℕ) : ∫ x, cn k x * cn l x ∂μ1 = if k = l then 1 else 0 := by
  cases k with
  | zero =>
    cases l with
    | zero => simp [cn]
    | succ l =>
      simp only [cn, one_mul, integral_cs, Nat.zero_ne_add_one, ite_false]
  | succ k =>
    cases l with
    | zero =>
      simp only [cn, mul_one, integral_cs, Nat.add_one_ne_zero, ite_false]
    | succ l =>
      simp only [cn, cs_orthonormal, add_left_inj]

/-- **The cosines are complete in `L²(0, 1)`.** -/
theorem cn_complete (f : L2I) (h : ∀ k : ℕ, ∫ x, cn k x * f x ∂μ1 = 0) : f = 0 := by
  have hF1 : prim f 1 = 0 := by
    have := h 0
    simp only [cn, one_mul] at this
    rw [prim, ← integral_mu1]; exact this
  have hF := h10_prim hF1
  have hc := H10.continuous_clamp hF
  have hcl : ∀ x ∈ Icc (0 : ℝ) 1, H10.clamp (prim f) x = prim f x := fun x hx => H10.clamp_eq hx
  -- `F ⊥` every sine
  have hsin : ∀ k : ℕ, 0 < k → ∫ x, sn k x * (toHL hc : ℝ → ℝ) x ∂μ1 = 0 := by
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e1 : ∫ x, sn (k + 1) x * (toHL hc : ℝ → ℝ) x ∂μ1 = ∫ x, sn (k + 1) x * prim f x ∂μ1 := by
      refine integral_congr_ae ?_
      filter_upwards [toHL_ae hc, ae_restrict_mem measurableSet_Ioo] with x h1 h2
      rw [h1, hcl x (Ioo_subset_Icc_self h2)]
    rw [e1, sn_ibp hF.1 hF.2.1 hF1 k]
    have e2 : ∫ x, cs k x * deriv (prim f) x ∂μ1 = ∫ x, cn (k + 1) x * f x ∂μ1 := by
      refine integral_congr_ae ?_
      filter_upwards [ae_deriv_prim f] with x hx
      rw [hx]; rfl
    rw [e2, h (k + 1), mul_zero]
  have h0 := sn_complete (toHL hc) hsin
  have hae : H10.clamp (prim f) =ᵐ[μ1] fun _ => 0 := by
    filter_upwards [toHL_ae hc, Lp.coeFn_zero ℝ 2 μ1] with x h1 h2
    rw [← h1, h0]; exact h2
  have hEq : EqOn (H10.clamp (prim f)) (fun _ => (0 : ℝ)) (Ioo 0 1) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hc.continuousOn continuousOn_const
  -- `F = 0` on `(0, 1)`, so `f = F' = 0` a.e.
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [ae_deriv_prim f, ae_restrict_mem measurableSet_Ioo] with x h1 h2
  change (f : ℝ → ℝ) x = 0
  rw [← h1]
  have : prim f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds h2] with y hy
    rw [← hcl y (Ioo_subset_Icc_self hy)]; exact hEq hy
  rw [this.deriv_eq]; simp

/-! ### The cosine Hilbert basis and Parseval in one dimension -/

lemma cn_orthonormal_HL : Orthonormal ℝ fun k : ℕ => toHL (continuous_cn k) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [inner_toHL_toHL, cn_orthonormal]

lemma cn_span_orthogonal :
    (Submodule.span ℝ (Set.range fun k : ℕ => toHL (continuous_cn k)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  refine cn_complete f fun k => ?_
  have h := Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self (f := fun k : ℕ => toHL (continuous_cn k)) k)) hf
  rw [real_inner_comm, inner_toHL_right] at h
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- **The cosine Hilbert basis** of `L²(0, 1)`. -/
noncomputable def cb : HilbertBasis ℕ ℝ HL :=
  HilbertBasis.mkOfOrthogonalEqBot cn_orthonormal_HL cn_span_orthogonal

lemma cb_apply (k : ℕ) : cb k = toHL (continuous_cn k) := by
  rw [cb, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- **Parseval** for a continuous function, cosine version, in `ℝ≥0∞`. -/
theorem parsevalC1 {g : ℝ → ℝ} (hg : Continuous g) :
    ∑' k : ℕ, ENNReal.ofReal ((∫ x, cn k x * g x ∂μ1) ^ 2) =
      ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ1 := by
  have h := cb.hasSum_inner_mul_inner (toHL hg) (toHL hg)
  simp only [cb_apply, inner_toHL_toHL] at h
  have e : ∀ k, (∫ x, g x * cn k x ∂μ1) * ∫ x, cn k x * g x ∂μ1 =
      (∫ x, cn k x * g x ∂μ1) ^ 2 := fun k => by
    rw [sq]; congr 1; exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  simp only [e] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) h.summable, h.tsum_eq,
    ofReal_integral_eq_lintegral_ofReal (f := fun x => g x * g x)
      (Box.integrable_of_continuous (hg.mul hg)) (ae_of_all _ fun x => mul_self_nonneg _)]
  simp only [sq]

/-! ### Products on the cube -/

/-- The product cosine `Π_j c_{m_j}(x_j)`. -/
noncomputable def cP {d : ℕ} (m : Fin d → ℕ) (x : Fin d → ℝ) : ℝ := ∏ j, cn (m j) (x j)

lemma continuous_cP {d : ℕ} (m : Fin d → ℕ) : Continuous (cP m) :=
  continuous_finsetProd _ fun j _ => (continuous_cn (m j)).comp (continuous_apply j)

lemma cP_orthonormal {d : ℕ} (m m' : Fin d → ℕ) :
    ∫ x, cP m x * cP m' x ∂piM d = if m = m' then 1 else 0 := by
  have e : (fun x => cP m x * cP m' x) =
      fun x => ∏ j, (cn (m j) (x j) * cn (m' j) (x j)) := by
    funext x; simp only [cP, Finset.prod_mul_distrib]
  rw [e, integral_fintype_prod_eq_prod (f := fun j t => cn (m j) t * cn (m' j) t)]
  simp only [cn_orthonormal]
  by_cases h : m = m'
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

lemma cP_cons {d : ℕ} (k : ℕ) (m : Fin d → ℕ) (t : ℝ) (y : Fin d → ℝ) :
    cP (Fin.cons k m : Fin (d + 1) → ℕ) (Fin.cons t y) = cn k t * cP m y := by
  simp only [cP, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **Parseval** for continuous functions on the cube, cosine version. -/
theorem parsevalC : ∀ (d : ℕ) {f : (Fin d → ℝ) → ℝ}, Continuous f →
    ∑' m : Fin d → ℕ, ENNReal.ofReal ((∫ x, cP m x * f x ∂piM d) ^ 2) =
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂piM d := by
  intro d
  induction d with
  | zero =>
    intro f _
    have hpi : piM 0 = Measure.dirac (isEmptyElim : Fin 0 → ℝ) := Measure.pi_of_empty _ _
    rw [hpi, tsum_fintype, Finset.univ_unique, Finset.sum_singleton, lintegral_dirac,
      integral_dirac]
    simp [cP]
  | succ d ih =>
    intro f hf
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hmp : MeasurePreserving e (piM (d + 1)) (μ1.prod (piM d)) :=
      measurePreserving_piFinSuccAbove (fun _ => μ1) 0
    have hsymm : ∀ p : ℝ × (Fin d → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    set F : ℝ → (Fin d → ℝ) → ℝ := fun t y => f (Fin.cons t y)
    have hFc : Continuous (Function.uncurry F) :=
      hf.comp (Continuous.finCons (A := fun _ : Fin (d + 1) => ℝ) continuous_fst continuous_snd)
    have hFt : ∀ t, Continuous (F t) := fun t => hFc.comp (continuous_const.prodMk continuous_id)
    set a : (Fin d → ℕ) → ℝ → ℝ := fun m t => ∫ y, cP m y * F t y ∂piM d
    have ha : ∀ m, Continuous (a m) := fun m =>
      continuous_param (G := fun t y => cP m y * F t y)
        (((continuous_cP m).comp continuous_snd).mul hFc)
    have hint : ∀ G : (Fin (d + 1) → ℝ) → ℝ, Continuous G →
        ∫ x, G x ∂piM (d + 1) = ∫ t, ∫ y, G (Fin.cons t y) ∂piM d ∂μ1 := by
      intro G hG
      rw [← hmp.symm.integral_comp' (f := e.symm) (g := G)]
      have hi : Integrable (fun p : ℝ × (Fin d → ℝ) => G (e.symm p)) (μ1.prod (piM d)) :=
        (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 (integrable_piM hG)
      rw [integral_prod _ hi]
      simp only [hsymm]
    have hlint : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂piM (d + 1) =
        ∫⁻ t, ∫⁻ y, ENNReal.ofReal (F t y ^ 2) ∂piM d ∂μ1 := by
      rw [← hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding, lintegral_prod]
      · simp only [hsymm, F]
      · exact ((hf.measurable.comp e.symm.measurable).pow_const 2).ennreal_ofReal.aemeasurable
    rw [hlint]
    have hslice : ∀ t, ∫⁻ y, ENNReal.ofReal (F t y ^ 2) ∂piM d =
        ∑' m, ENNReal.ofReal ((a m t) ^ 2) := fun t => (ih (hFt t)).symm
    simp only [hslice]
    rw [lintegral_tsum (f := fun m t => ENNReal.ofReal (a m t ^ 2))
      fun m => ((ha m).measurable.pow_const 2).ennreal_ofReal.aemeasurable]
    have h1 : ∀ m, ∫⁻ t, ENNReal.ofReal ((a m t) ^ 2) ∂μ1 =
        ∑' k, ENNReal.ofReal ((∫ t, cn k t * a m t ∂μ1) ^ 2) := fun m =>
      (parsevalC1 (ha m)).symm
    simp only [h1]
    have hcoef : ∀ k m, ∫ t, cn k t * a m t ∂μ1 =
        ∫ x, cP (Fin.cons k m : Fin (d + 1) → ℕ) x * f x ∂piM (d + 1) := by
      intro k m
      rw [hint (fun x => cP (Fin.cons k m : Fin (d + 1) → ℕ) x * f x)
        ((continuous_cP _).mul hf)]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [a, cP_cons, ← integral_const_mul, F, mul_assoc]
    simp only [hcoef]
    set g : (Fin (d + 1) → ℕ) → ENNReal :=
      fun m => ENNReal.ofReal ((∫ x, cP m x * f x ∂piM (d + 1)) ^ 2)
    rw [tsum_comm, ← tsum_prod' (f := fun p : ℕ × (Fin d → ℕ) =>
      g (Fin.cons p.1 p.2))]
    exact ((Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)).tsum_eq g).symm

/-- **Parseval**, real form, for continuous functions on the cube. -/
theorem hasSum_sq_cubeC {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    HasSum (fun m => (∫ x, cP m x * f x ∂piM d) ^ 2) (∫ x, f x * f x ∂piM d) := by
  have hP := parsevalC d hf
  have hI : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂piM d = ENNReal.ofReal (∫ x, f x * f x ∂piM d) := by
    rw [ofReal_integral_eq_lintegral_ofReal (f := fun x => f x * f x)
      (integrable_piM (hf.mul hf)) (ae_of_all _ fun x => mul_self_nonneg _)]
    simp only [sq]
  rw [hI] at hP
  have hne : ∑' m, ENNReal.ofReal ((∫ x, cP m x * f x ∂piM d) ^ 2) ≠ ⊤ := by
    rw [hP]; exact ENNReal.ofReal_ne_top
  have hs := ENNReal.summable_toReal hne
  have e : ∀ m, (ENNReal.ofReal ((∫ x, cP m x * f x ∂piM d) ^ 2)).toReal =
      (∫ x, cP m x * f x ∂piM d) ^ 2 := fun m => ENNReal.toReal_ofReal (sq_nonneg _)
  simp only [e] at hs
  convert hs.hasSum using 1
  rw [← ENNReal.toReal_ofReal (integral_nonneg fun x => mul_self_nonneg (f x)), ← hP,
    ENNReal.tsum_toReal_eq fun m => ENNReal.ofReal_ne_top]
  congr 1; funext m; exact ENNReal.toReal_ofReal (sq_nonneg _)

/-! ### The cosine Hilbert basis of `L²` of the cube -/

variable {n : ℕ}

/-- The product cosine as an element of `L²` of the cube. -/
noncomputable def eC (m : Fin (n + 1) → ℕ) : HN n := (memLp_cont (continuous_cP m)).toLp

/-- The cosine coefficient `⟨c_m, Φ⟩`. -/
noncomputable def cC (m : Fin (n + 1) → ℕ) (Φ : Cfg n → ℝ) : ℝ := ∫ x, cP m x * Φ x ∂μN n

lemma coeFn_eC (m : Fin (n + 1) → ℕ) : (eC m : Cfg n → ℝ) =ᵐ[μN n] cP m := MemLp.coeFn_toLp _

lemma inner_eC (m : Fin (n + 1) → ℕ) (F : HN n) :
    inner ℝ (eC m) F = ∫ x, cP m x * F x ∂μN n := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_eC m] with x hx
  rw [hx]; simp [mul_comm]

lemma eC_orthonormal : Orthonormal ℝ (eC (n := n)) := by
  rw [orthonormal_iff_ite]
  intro m m'
  rw [inner_eC, show ∫ x, cP m x * (eC m' : Cfg n → ℝ) x ∂μN n = ∫ x, cP m x * cP m' x ∂μN n
    from integral_congr_ae (by filter_upwards [coeFn_eC m'] with x hx; rw [hx]),
    muN_eq, cP_orthonormal]

/-- An element orthogonal to every product cosine is orthogonal to every continuous function. -/
lemma integral_cont_mul_eq_zeroC {F : HN n} (hF : ∀ m, inner ℝ (eC m) F = 0) {ψ : Cfg n → ℝ}
    (hψ : Continuous ψ) : ∫ x, ψ x * F x ∂μN n = 0 := by
  set x0 : HN n := (memLp_cont hψ).toLp
  set a : (Fin (n + 1) → ℕ) → ℝ := fun m => inner ℝ (eC m) x0
  have ea : ∀ m, a m = ∫ x, cP m x * ψ x ∂piM (n + 1) := fun m => by
    simp only [a, inner_eC, ← muN_eq]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_cont hψ)] with x hx
    simp only [x0] at *; rw [hx]
  have hpar : HasSum (fun m => a m ^ 2) (‖x0‖ ^ 2) := by
    rw [norm_sq_toLp]
    have h := hasSum_sq_cubeC (d := n + 1) hψ
    rw [← muN_eq] at h
    simp only [ea]
    rw [← muN_eq]
    convert h using 1
    exact integral_congr_ae (ae_of_all _ fun x => sq _)
  have hS : Tendsto (fun s : Finset _ => ∑ m ∈ s, a m • eC m) atTop (𝓝 x0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have key : ∀ s : Finset _, ‖∑ m ∈ s, a m • eC m - x0‖ =
        √(‖x0‖ ^ 2 - ∑ m ∈ s, a m ^ 2) := fun s => by
      rw [← orthonormal_norm_sub_sq eC_orthonormal x0 s, norm_sub_rev, Real.sqrt_sq (norm_nonneg _)]
    simp only [key]
    have h := (tendsto_const_nhds (x := ‖x0‖ ^ 2)).sub hpar
    rw [sub_self] at h
    simpa using h.sqrt
  have hlim := Filter.Tendsto.inner (𝕜 := ℝ) hS (tendsto_const_nhds (x := F))
  have hz : ∀ s : Finset _, inner ℝ (∑ m ∈ s, a m • eC m) F = 0 := fun s => by
    simp [sum_inner, inner_smul_left, hF]
  simp only [hz] at hlim
  have h0 := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [inner_toLp_left] at h0
  exact h0.symm

/-- **Completeness of the product cosines in `L²` of the cube.** -/
lemma eC_complete (F : HN n) (hF : ∀ m, inner ℝ (eC m) F = 0) : F = 0 := by
  have hint : IntegrableOn (fun x => (F : Cfg n → ℝ) x) (Cube n) volume :=
    (Lp.memLp F).integrable one_le_two
  have h := isOpen_cube.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    hint.locallyIntegrableOn (fun g hg _ hsupp => by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h), zero_smul]]
      simpa [smul_eq_mul] using integral_cont_mul_eq_zeroC hF hg.continuous)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [(ae_restrict_iff' measurableSet_cube).2 h] with x hx
  exact hx

lemma eC_span_orthogonal : (Submodule.span ℝ (Set.range (eC (n := n))))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  exact eC_complete F fun m =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self m)) hF

/-- **The product-cosine Hilbert basis** of `L²` of the cube. -/
noncomputable def bC : HilbertBasis (Fin (n + 1) → ℕ) ℝ (HN n) :=
  HilbertBasis.mkOfOrthogonalEqBot eC_orthonormal eC_span_orthogonal

lemma bC_apply (m : Fin (n + 1) → ℕ) : bC m = eC m := by
  rw [bC, HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma inner_eC_toLp {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (m : Fin (n + 1) → ℕ) :
    inner ℝ (eC m) (hΦ.toLp Φ) = cC m Φ := by
  rw [inner_eC, cC]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hΦ] with x hx
  rw [hx]

/-- **Parseval** for `L²` functions on the cube, cosine version. -/
theorem parsevalCW {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) :
    HasSum (fun m => cC m Φ ^ 2) (∫ x, Φ x ^ 2 ∂μN n) := by
  have h := (bC (n := n)).hasSum_inner_mul_inner (hΦ.toLp Φ) (hΦ.toLp Φ)
  simp only [bC_apply, real_inner_comm (eC _) (hΦ.toLp Φ), inner_eC_toLp hΦ,
    real_inner_self_eq_norm_sq, norm_sq_toLp hΦ] at h
  simpa [sq] using h

/-- **Parseval for pairs**, cosine version. -/
theorem parsevalCW_pair {Φ Ψ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n)) :
    HasSum (fun m => cC m Φ * cC m Ψ) (∫ x, Φ x * Ψ x ∂μN n) := by
  have h := (bC (n := n)).hasSum_inner_mul_inner (hΦ.toLp Φ) (hΨ.toLp Ψ)
  simp only [bC_apply, real_inner_comm (eC _) (hΦ.toLp Φ), inner_eC_toLp hΦ, inner_eC_toLp hΨ,
    inner_toLp_left] at h
  convert h using 1
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hΨ] with x hx
  rw [hx]

end DFT.Continuum.Line
