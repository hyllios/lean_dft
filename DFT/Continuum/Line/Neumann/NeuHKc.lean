/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureHKend
import DFT.Continuum.Line.Neumann.NeuHKb
import DFT.Continuum.Line.Neumann.NeuRep

/-!
# Hohenberg–Kohn with Neumann walls and `H⁻¹` potentials: the pair-density identity

Let `D ∈ H⁻¹` annihilate every mixed density `ρ(Φ, χ)` of a state `Φ`. Then there is
`R ∈ L¹(0, 1)` with `D(g ρ_Φ) + ∫ g R = 0` for every compactly supported `C¹` function `g`
(**`exists_R`**). For `N ≥ 2` this is the limit of `D_smooth` along the cosine truncations of `Φ`,
whose pair densities `R_X` form an `L¹` Cauchy sequence. For `N = 1` it holds with `R = 0`.

* `dE2` (products in `H1E`): `fnE_dE2`, `norm_dE2_le`, bilinearity; `LgD_eq`.
* `mul_memN`, `SHN_mul_le`, `rhoE2_sub_left`, `rhoE_sub_eq`, `integrable_RfD`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n m : ℕ} {τ : Stat}

/-! ### Products in `H1E` -/

lemma h1N_of_C1 {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) : H1N g :=
  ⟨hg.contDiffOn.absolutelyContinuousOnInterval,
    integrable_cont_mu1 ((hg.continuous_deriv le_rfl).pow 2)⟩

lemma eq_of_fnE {e e' : H1E} (h : ∀ t ∈ Icc (0 : ℝ) 1, fnE e t = fnE e' t) : e = e' :=
  evE_inj (ContinuousMap.ext fun t => by rw [evE_apply, evE_apply]; exact h t t.2)

lemma fnE_dE2 (e h : H1E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fnE (dE2 e h) t = fnE e t * fnE h t := by
  have := toE_mul_eq_dE2 (h1N_fnE e) (h1N_fnE h)
  rw [toE_fnE, toE_fnE] at this
  rw [← this, fnE_toE _ ht]

lemma fnE_smul' (c : ℝ) (e : H1E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fnE (c • e) t = c * fnE e t := by
  have := congrArg (fun P : Pot => P ⟨t, ht⟩) (map_smul evE c e)
  simpa only [ContinuousMap.smul_apply, evE_apply, smul_eq_mul] using this

lemma fnE_sub' (e e' : H1E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fnE (e - e') t = fnE e t - fnE e' t := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ e', fnE_add _ _ ht, fnE_smul' _ _ ht]; ring

lemma dE2_comm (e h : H1E) : dE2 e h = dE2 h e :=
  eq_of_fnE fun t ht => by rw [fnE_dE2 _ _ ht, fnE_dE2 _ _ ht, mul_comm]

lemma dE2_add_left (e e' h : H1E) : dE2 (e + e') h = dE2 e h + dE2 e' h :=
  eq_of_fnE fun t ht => by
    rw [fnE_add _ _ ht, fnE_dE2 _ _ ht, fnE_dE2 _ _ ht, fnE_dE2 _ _ ht, fnE_add _ _ ht]; ring

lemma dE2_smul_left (c : ℝ) (e h : H1E) : dE2 (c • e) h = c • dE2 e h :=
  eq_of_fnE fun t ht => by
    rw [fnE_smul' _ _ ht, fnE_dE2 _ _ ht, fnE_dE2 _ _ ht, fnE_smul' _ _ ht]; ring

lemma dE2_sub_right (e h h' : H1E) : dE2 e (h - h') = dE2 e h - dE2 e h' :=
  eq_of_fnE fun t ht => by
    rw [fnE_dE2 _ _ ht, fnE_sub' _ _ ht, fnE_sub' _ _ ht, fnE_dE2 _ _ ht, fnE_dE2 _ _ ht]; ring

/-- **Products are bounded in `H1E`.** -/
lemma norm_dE2_le (e h : H1E) : ‖dE2 e h‖ ≤ (1 + 2 * ‖evE‖) * ‖e‖ * ‖h‖ := by
  have h1 : ‖(dE2 e h).fst‖ ≤ ‖e‖ * ‖h‖ := by
    change |e.fst * h.fst| ≤ _
    rw [abs_mul]; exact mul_le_mul (norm_fst_le e) (norm_fst_le h) (abs_nonneg _) (norm_nonneg _)
  have h2 : ‖(dE2 e h).snd‖ ≤ 2 * ‖evE‖ * ‖e‖ * ‖h‖ := by
    change ‖mulL (evE e) h.snd + mulL (evE h) e.snd‖ ≤ _
    have a1 := (norm_mulL_le (evE e) h.snd).trans
      (mul_le_mul (evE.le_opNorm e) (norm_snd_le h) (norm_nonneg _) (by positivity))
    have a2 := (norm_mulL_le (evE h) e.snd).trans
      (mul_le_mul (evE.le_opNorm h) (norm_snd_le e) (norm_nonneg _) (by positivity))
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add a1 a2
      _ = _ := by ring
  rw [WithLp.prod_norm_eq_of_L2]
  have hf0 := norm_nonneg (dE2 e h).fst
  have hs0 := norm_nonneg (dE2 e h).snd
  have hfs : √(‖(dE2 e h).fst‖ ^ 2 + ‖(dE2 e h).snd‖ ^ 2) ≤ ‖(dE2 e h).fst‖ + ‖(dE2 e h).snd‖ := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  refine hfs.trans ?_
  nlinarith

/-- `D(g e)` through the product in `H1E`. -/
lemma LgD_eq (D : PotH) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (e : H1E) :
    LgD D g e = D (dE2 (toE (h1N_of_C1 hg)) e) := by
  set hE := toE (h1N_of_C1 hg)
  rw [D_apply, LgD]
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h0 : fnE (dE2 hE e) 0 = g 0 * fnE e 0 := by
    rw [fnE_dE2 _ _ h01, fnE_toE _ h01]
  rw [h0]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [mulL_ae (evE hE) e.snd, mulL_ae (evE e) hE.snd,
    Lp.coeFn_add (mulL (evE hE) e.snd) (mulL (evE e) hE.snd), dN_ae (h1N_of_C1 hg),
    ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3 h4 ht
  have htI := Ioo_subset_Icc_self ht
  change _ = _ * ((mulL (evE hE) e.snd + mulL (evE e) hE.snd : L2I) t)
  rw [h3, Pi.add_apply, h1, h2, ext_evE htI, ext_evE htI, fnE_toE _ htI]
  change _ = _ * (g t * _ + fnE e t * (dN (h1N_of_C1 hg) : ℝ → ℝ) t)
  rw [h4]; ring

/-! ### States multiplied by symmetric functions -/

lemma mul_memN {X : Cfg n → ℝ} (hX : X ∈ DomN τ n) {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hζs : ∀ σ x, ζ (pm σ x) = ζ x) : (fun x => ζ x * X x) ∈ DomN τ n :=
  ⟨memLp_mul_cont hζ.continuous hX.1, fun k => ⟨_, (dWN_spec (hX.2.1 k)).mul_C1 hX.1 hζ⟩,
    fun σ _ => by
      filter_upwards [hX.2.2 σ trivial] with x hx
      simp only [hζs, hx]; ring⟩

lemma SHN_mul_le {Y : Cfg n → ℝ} (hY : H1NW Y) {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ)
    {Z Z' : ℝ} (hZ : ∀ x, |ζ x| ≤ Z) (hZ' : ∀ k x, |dk k ζ x| ≤ Z') :
    SHN (fun x => ζ x * Y x) ≤ 2 * (Z ^ 2 + Z' ^ 2) * SHN Y := by
  have hk := kinN_mul_le hY hζ hZ hZ'
  have hi : ∫ x, (ζ x * Y x) ^ 2 ∂μN n ≤ Z ^ 2 * ∫ x, Y x ^ 2 ∂μN n := by
    rw [← integral_const_mul]
    refine integral_mono (int_sq (memLp_mul_cont hζ.continuous hY.1)) ((int_sq hY.1).const_mul _)
      fun x => ?_
    have h1 : ζ x ^ 2 ≤ Z ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ x) 2
    change (ζ x * Y x) ^ 2 ≤ Z ^ 2 * Y x ^ 2
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hY0 : 0 ≤ ∫ x, Y x ^ 2 ∂μN n := integral_nonneg fun _ => sq_nonneg _
  have hK0 := kinN_nonneg Y
  have hN : (0 : ℝ) ≤ n + 1 := by positivity
  unfold SHN
  nlinarith [mul_le_mul_of_nonneg_left hi hN, mul_nonneg (sq_nonneg Z) hK0,
    mul_nonneg (mul_nonneg hN (sq_nonneg Z)) hY0, mul_nonneg (mul_nonneg hN (sq_nonneg Z')) hY0]

lemma SHN_sub_le {X Y : Cfg n → ℝ} (hX : X ∈ DomN τ n) (hY : Y ∈ DomN τ n) :
    SHN (X - Y) ≤ 2 * SHN X + 2 * SHN Y := by
  have h := SHN_add_le (h1NW_of_mem hX) (h1NW_of_mem (Submodule.smul_mem _ (-1 : ℝ) hY))
  have e : X + (-1 : ℝ) • Y = X - Y := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [SHN_smul (h1NW_of_mem hY), e] at h
  linarith

lemma rhoE2_sub_left {A B C : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n)
    (hC : C ∈ DomN τ n) : rhoE2 τ (A - B) C = rhoE2 τ A C - rhoE2 τ B C := by
  rw [sub_eq_add_neg A B, ← neg_one_smul ℝ B, rhoE2_add_left hA (Submodule.smul_mem _ _ hB) hC,
    rhoE2_smul_left hB hC, neg_one_smul, sub_eq_add_neg]

lemma rhoE2_sub_right {A B C : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n)
    (hC : C ∈ DomN τ n) : rhoE2 τ C (A - B) = rhoE2 τ C A - rhoE2 τ C B := by
  rw [rhoE2_comm hC (sub_mem hA hB), rhoE2_sub_left hA hB hC, rhoE2_comm hA hC, rhoE2_comm hB hC]

lemma rhoE_sub_eq {A B : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n) :
    rhoE τ A - rhoE τ B = rhoE2 τ (A - B) (A + B) := by
  rw [rhoE2_sub_left hA hB (add_mem hA hB), rhoE2_comm hA (add_mem hA hB),
    rhoE2_comm hB (add_mem hA hB), rhoE2_add_left hA hB hA, rhoE2_add_left hA hB hB,
    rhoE2_self hA, rhoE2_self hB, rhoE2_comm hB hA]
  abel

/-! ### The pair densities converge in `L¹` -/

lemma integrable_hQ_beta {β : ℝ → ℝ} (hβ : Integrable β μ1) {F : Cfg (m + 1) → ℝ}
    (hF : Continuous F) (j : Fin (m + 1)) :
    Integrable (fun u => ∫ t, β t * hQ F j t u ∂μ1) μ1 := by
  obtain ⟨CF, -, hCF⟩ := exists_bound_cubeC hF
  have hb : ∀ᵐ z ∂(μ1.prod μ1), ‖hQ F j z.1 z.2‖ ≤ CF := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    rw [Real.norm_eq_abs]
    exact abs_hQ_le hCF j (Ioo_subset_Icc_self hz.1) (Ioo_subset_Icc_self hz.2)
  have hint : Integrable (fun z : ℝ × ℝ => β z.1 * hQ F j z.1 z.2) (μ1.prod μ1) := by
    have h1 := (hβ.mul_prod (integrable_const (1 : ℝ) (μ := μ1))).bdd_mul
      (continuous_hQ hF j).aestronglyMeasurable hb
    refine h1.congr (ae_of_all _ fun z => ?_)
    simp only [mul_one]; ring
  exact hint.integral_prod_right

lemma integrable_RfD (D : PotH) {X : Cfg (m + 1) → ℝ} (hX1 : ContDiff ℝ 1 X) :
    Integrable (RfD D X) μ1 := by
  unfold RfD
  apply Integrable.const_mul
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  refine (Integrable.const_mul (integrable_cont_mu1 ((continuous_hQ (hX1.continuous.mul
    hX1.continuous) j).comp (f := fun u : ℝ => ((0 : ℝ), u))
      (Continuous.prodMk continuous_const continuous_id))) _).add ?_
  exact integrable_hQ_beta (integrable_L2I _) (continuous_dk_of_C1 (hX1.mul hX1) 0) j

lemma cauchySeq_of_dist_le_add {α : Type*} [PseudoMetricSpace α] {s : ℕ → α} {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (h : ∀ M K, dist (s M) (s K) ≤ f M + f K) : CauchySeq s := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hf) (ε / 2) (half_pos hε)
  refine ⟨N, fun M hM K hK => (h M K).trans_lt ?_⟩
  have h1 := hN M hM
  have h2 := hN K hK
  rw [Real.dist_eq, sub_zero] at h1 h2
  linarith [le_abs_self (f M), le_abs_self (f K)]

lemma sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

lemma tendsto_sqrt_mul {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun M => √(a M * c)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M => a M * c) atTop (𝓝 0) := by simpa using ha.mul_const c
  have := (Real.continuous_sqrt.tendsto 0).comp h1
  rw [Real.sqrt_zero] at this
  exact this

/-- **The pair-density identity for `N ≥ 2`.** -/
theorem exists_R_succ (D : PotH) {Φ : Cfg (m + 1) → ℝ} (hΦ : Φ ∈ DomN τ (m + 1))
    (hD : ∀ χ ∈ DomN τ (m + 1), D (rhoE2 τ Φ χ) = 0) :
    ∃ R : ℝ → ℝ, Integrable R μ1 ∧ ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g), HasCompactSupport g →
      D (dE2 (toE (h1N_of_C1 hg)) (rhoE τ Φ)) + ∫ t, g t * R t ∂μ1 = 0 := by
  set X : ℕ → Cfg (m + 1) → ℝ := fun M => truncC M Φ
  have hXD : ∀ M, X M ∈ DomN τ (m + 1) := truncC_memN hΦ
  have hX2 : ∀ M, ContDiff ℝ 2 (X M) := fun M => contDiff_truncC M Φ
  have hX1 : ∀ M, ContDiff ℝ 1 (X M) := fun M => (hX2 M).of_le (by norm_num)
  set a : ℕ → ℝ := fun M => SHN (Φ - X M)
  have ha : Tendsto a atTop (𝓝 0) := by
    have h := ((tendsto_sq_sub_truncC hΦ).const_mul ((↑(m + 1) : ℝ) + 1)).add
      (tendsto_kinN_sub_truncC hΦ)
    rw [mul_zero, add_zero] at h
    exact h
  have ha0 : ∀ M, 0 ≤ a M := fun M => SHN_nonneg _
  obtain ⟨B, hB⟩ : ∃ B, ∀ M, a M ≤ B := by
    obtain ⟨B, hB⟩ := ha.bddAbove_range
    exact ⟨B, fun M => hB ⟨M, rfl⟩⟩
  set S0 := 2 * SHN Φ + 2 * B
  have hS0 : 0 ≤ S0 := by
    have := SHN_nonneg Φ; have := (ha0 0).trans (hB 0); positivity
  have hXb : ∀ M, SHN (X M) ≤ S0 := fun M => by
    have := SHN_sub_le hΦ (sub_mem hΦ (hXD M))
    rw [sub_sub_cancel] at this
    linarith [hB M]
  have hneg : ∀ M, SHN (X M - Φ) = a M := fun M => by
    have e : X M - Φ = (-1 : ℝ) • (Φ - X M) := by rw [neg_one_smul, neg_sub]
    rw [e, SHN_smul (h1NW_of_mem (sub_mem hΦ (hXD M)))]; norm_num; rfl
  -- the Cauchy sequence of pair densities
  set α := ((InnerProductSpace.toDual ℝ H1E).symm D).fst
  set nb := √(∫ t, ((InnerProductSpace.toDual ℝ H1E).symm D).snd t ^ 2 ∂μ1)
  set CR : ℝ := ((↑(m + 1) : ℝ) + 1) * (m + 1) * (2 * |α| + 3 * nb)
  have hCR : 0 ≤ CR := by positivity
  set R : ℕ → ℝ → ℝ := fun M => RfD D (X M)
  have hRi : ∀ M, Integrable (R M) μ1 := fun M => integrable_RfD D (hX1 M)
  set f : ℕ → ℝ := fun M => CR * (4 * √S0) * √(2 * a M)
  have hf : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun M => √(2 * a M)) atTop (𝓝 0) := by
      have := tendsto_sqrt_mul ha 2
      refine this.congr fun M => ?_
      rw [mul_comm]
    simpa [f] using h1.const_mul (CR * (4 * √S0))
  have hdist : ∀ M K, ∫ u, |R M u - R K u| ∂μ1 ≤ f M + f K := fun M K => by
    have h := integral_abs_RfD_sub_le D (hXD M) (hXD K) (hX1 M) (hX1 K)
    have e1 : X M - X K = (Φ - X K) - (Φ - X M) := by abel
    have hmk : SHN (X M - X K) ≤ 2 * a M + 2 * a K := by
      rw [e1]
      have := SHN_sub_le (sub_mem hΦ (hXD K)) (sub_mem hΦ (hXD M))
      linarith
    have hsq1 : √(SHN (X M - X K)) ≤ √(2 * a M) + √(2 * a K) :=
      (Real.sqrt_le_sqrt hmk).trans (sqrt_add_le' (by linarith [ha0 M]) (by linarith [ha0 K]))
    have hpk : SHN (X M + X K) ≤ 4 * S0 := by
      have := SHN_add_le (h1NW_of_mem (hXD M)) (h1NW_of_mem (hXD K))
      linarith [hXb M, hXb K]
    have hsq2 : √(SHN (X M + X K)) + √(SHN (X M)) + √(SHN (X K)) ≤ 4 * √S0 := by
      have a1 : √(SHN (X M + X K)) ≤ 2 * √S0 := by
        calc √(SHN (X M + X K)) ≤ √(4 * S0) := Real.sqrt_le_sqrt hpk
          _ = 2 * √S0 := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
      have a2 := Real.sqrt_le_sqrt (hXb M)
      have a3 := Real.sqrt_le_sqrt (hXb K)
      linarith
    have hfac0 : 0 ≤ √(SHN (X M + X K)) + √(SHN (X M)) + √(SHN (X K)) := by positivity
    have hfin : √(SHN (X M - X K)) * (√(SHN (X M + X K)) + √(SHN (X M)) + √(SHN (X K))) ≤
        (√(2 * a M) + √(2 * a K)) * (4 * √S0) :=
      mul_le_mul hsq1 hsq2 hfac0 (by positivity)
    calc _ ≤ _ := h
      _ ≤ ((↑(m + 1) : ℝ) + 1) * (m + 1) * ((2 * |α| + 3 * nb) *
          ((√(2 * a M) + √(2 * a K)) * (4 * √S0))) := by gcongr
      _ = f M + f K := by simp only [f, CR]; ring
  set r : ℕ → Lp ℝ 1 μ1 := fun M => (hRi M).toL1 (R M)
  have hrd : ∀ M K, dist (r M) (r K) ≤ f M + f K := fun M K => by
    rw [dist_eq_norm, ← Integrable.toL1_sub, L1.norm_eq_integral_norm]
    refine le_trans (le_of_eq ?_) (hdist M K)
    refine integral_congr_ae ?_
    filter_upwards [Integrable.coeFn_toL1 ((hRi M).sub (hRi K))] with u hu
    rw [hu, Real.norm_eq_abs, Pi.sub_apply]
  obtain ⟨Rt, hRt⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_add hf hrd)
  refine ⟨Rt, L1.integrable_coeFn Rt, fun g hg hgc => ?_⟩
  obtain ⟨Cg, hCg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨Cg', hCg'⟩ := (hg.continuous_deriv le_rfl).bounded_above_of_compact_support hgc.deriv
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
  -- `∫ g R_M → ∫ g R`
  have hgR : Tendsto (fun M => ∫ t, g t * R M t ∂μ1) atTop (𝓝 (∫ t, g t * Rt t ∂μ1)) := by
    have hn : Tendsto (fun M => ‖r M - Rt‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hRt
    have hgi : ∀ {F : ℝ → ℝ}, Integrable F μ1 → Integrable (fun t => g t * F t) μ1 :=
      fun hF => hF.bdd_mul hg.continuous.aestronglyMeasurable (ae_of_all _ fun t => hCg t)
    have hb : ∀ M, ‖∫ t, g t * R M t ∂μ1 - ∫ t, g t * Rt t ∂μ1‖ ≤ Cg * ‖r M - Rt‖ := fun M => by
      rw [← integral_sub (hgi (hRi M)) (hgi (L1.integrable_coeFn Rt))]
      calc ‖∫ t, (g t * R M t - g t * Rt t) ∂μ1‖ ≤ ∫ t, Cg * |R M t - Rt t| ∂μ1 :=
            norm_integral_le_of_norm_le
              ((((hRi M).sub (L1.integrable_coeFn Rt)).abs).const_mul Cg)
              (ae_of_all _ fun t => by
                rw [← mul_sub, Real.norm_eq_abs, abs_mul]
                exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm ▸ hCg t)
                  (abs_nonneg _))
        _ = Cg * ‖r M - Rt‖ := by
            rw [integral_const_mul, L1.norm_eq_integral_norm]
            congr 1
            refine integral_congr_ae ?_
            filter_upwards [Lp.coeFn_sub (r M) Rt, (hRi M).coeFn_toL1] with t h1 h2
            rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun M => norm_nonneg _) hb ?_
    simpa using hn.const_mul Cg
  -- `D(g ρ_M) → D(g ρ)`
  set hE := toE (h1N_of_C1 hg)
  set S1 := 2 * SHN Φ + 2 * S0
  have hρ : ∀ M, ‖rhoE τ (X M) - rhoE τ Φ‖ ≤ 8 * √(a M * S1) := fun M => by
    rw [norm_sub_rev, rhoE_sub_eq hΦ (hXD M)]
    refine (norm_rhoE2_le (sub_mem hΦ (hXD M)) (add_mem hΦ (hXD M))).trans ?_
    have := SHN_add_le (h1NW_of_mem hΦ) (h1NW_of_mem (hXD M))
    gcongr
    · exact SHN_nonneg _
    · linarith [hXb M]
  have hDρ : Tendsto (fun M => D (dE2 hE (rhoE τ (X M)))) atTop
      (𝓝 (D (dE2 hE (rhoE τ Φ)))) := by
    refine (D.continuous.tendsto _).comp ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_)
      (by simpa using (tendsto_sqrt_mul ha S1).const_mul ((1 + 2 * ‖evE‖) * ‖hE‖ * 8))
    rw [← dE2_sub_right]
    refine (norm_dE2_le _ _).trans ?_
    rw [mul_assoc _ 8]
    exact mul_le_mul_of_nonneg_left (hρ M) (by positivity)
  -- `D(ρ(X_M, FF g X_M)) → 0`
  set ζ : Cfg (m + 1) → ℝ := FF g
  have hζ : ContDiff ℝ 1 ζ := contDiff_FF hg
  have hζs : ∀ σ x, ζ (pm σ x) = ζ x := fun σ x => FF_pm g σ x
  set Z : ℝ := (m + 1 + 1) * Cg
  have hZ : ∀ x, |ζ x| ≤ Z := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |g (x k)| ≤ ∑ _k : Fin (m + 1 + 1), Cg :=
          Finset.sum_le_sum fun k _ => (Real.norm_eq_abs _).symm ▸ hCg _
      _ = Z := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hZ' : ∀ k x, |dk k ζ x| ≤ Cg' := fun k x => by
    rw [dk_FF (hg.differentiable one_ne_zero)]; exact (Real.norm_eq_abs _).symm ▸ hCg' _
  set Cζ := 2 * (Z ^ 2 + Cg' ^ 2)
  have hCζ : 0 ≤ Cζ := by positivity
  have hZΦ := mul_memN hΦ hζ hζs
  have hZX : ∀ M, (fun x => ζ x * X M x) ∈ DomN τ (m + 1) := fun M => mul_memN (hXD M) hζ hζs
  have hK : ∀ M, |D (rhoE2 τ (X M) (fun x => ζ x * X M x))| ≤
      ‖D‖ * (8 * √(a M * (Cζ * S0)) + 8 * √(SHN Φ * (Cζ * a M))) := fun M => by
    have e1 : (fun x => ζ x * X M x) - (fun x => ζ x * Φ x) = fun x => ζ x * (X M - Φ) x := by
      funext x; simp only [Pi.sub_apply]; ring
    have hsplit : rhoE2 τ (X M) (fun x => ζ x * X M x) =
        rhoE2 τ (X M - Φ) (fun x => ζ x * X M x) +
          (rhoE2 τ Φ (fun x => ζ x * X M x - ζ x * Φ x) + rhoE2 τ Φ (fun x => ζ x * Φ x)) := by
      rw [rhoE2_sub_left (hXD M) hΦ (hZX M)]
      have := rhoE2_sub_right (hZX M) hZΦ hΦ
      rw [show (fun x => ζ x * X M x - ζ x * Φ x) =
        (fun x => ζ x * X M x) - (fun x => ζ x * Φ x) from rfl, this]
      abel
    rw [hsplit, map_add, map_add, hD _ hZΦ, add_zero]
    have hm1 : SHN (fun x => ζ x * X M x) ≤ Cζ * S0 :=
      (SHN_mul_le (h1NW_of_mem (hXD M)) hζ hZ hZ').trans
        (mul_le_mul_of_nonneg_left (hXb M) hCζ)
    have hm2 : SHN (fun x => ζ x * X M x - ζ x * Φ x) ≤ Cζ * a M := by
      rw [show (fun x => ζ x * X M x - ζ x * Φ x) = fun x => ζ x * (X M - Φ) x from e1,
        ← hneg M]
      exact SHN_mul_le (h1NW_of_mem (sub_mem (hXD M) hΦ)) hζ hZ hZ'
    have n1 := norm_rhoE2_le (sub_mem (hXD M) hΦ) (hZX M)
    have n2 := norm_rhoE2_le hΦ (sub_mem (hZX M) hZΦ)
    rw [hneg M] at n1
    have b1 : √(a M * SHN (fun x => ζ x * X M x)) ≤ √(a M * (Cζ * S0)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm1 (ha0 M))
    have b2 : √(SHN Φ * SHN ((fun x => ζ x * X M x) - fun x => ζ x * Φ x)) ≤
        √(SHN Φ * (Cζ * a M)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm2 (SHN_nonneg _))
    calc |D (rhoE2 τ (X M - Φ) (fun x => ζ x * X M x)) +
          D (rhoE2 τ Φ (fun x => ζ x * X M x - ζ x * Φ x))|
        ≤ ‖D‖ * ‖rhoE2 τ (X M - Φ) (fun x => ζ x * X M x)‖ +
          ‖D‖ * ‖rhoE2 τ Φ (fun x => ζ x * X M x - ζ x * Φ x)‖ := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
            exact (Real.norm_eq_abs _).symm ▸ D.le_opNorm _
      _ ≤ ‖D‖ * (8 * √(a M * (Cζ * S0))) + ‖D‖ * (8 * √(SHN Φ * (Cζ * a M))) := by
          gcongr
          · exact n1.trans (by linarith)
          · exact n2.trans (by linarith)
      _ = _ := by ring
  have hlim1 : Tendsto (fun M => D (rhoE2 τ (X M) (fun x => ζ x * X M x))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun M => abs_nonneg _) hK ?_
    have h1 := tendsto_sqrt_mul ha (Cζ * S0)
    have h2 : Tendsto (fun M => √(SHN Φ * (Cζ * a M))) atTop (𝓝 0) := by
      refine (tendsto_sqrt_mul ha (SHN Φ * Cζ)).congr fun M => ?_
      ring_nf
    simpa using ((h1.const_mul 8).add (h2.const_mul 8)).const_mul ‖D‖
  have hlim2 : Tendsto (fun M => D (rhoE2 τ (X M) (fun x => ζ x * X M x))) atTop
      (𝓝 (D (dE2 hE (rhoE τ Φ)) + ∫ t, g t * Rt t ∂μ1)) := by
    refine (hDρ.add hgR).congr fun M => ?_
    rw [D_smooth D (hXD M) (hX2 M) hg, LgD_eq D hg]
  exact tendsto_nhds_unique hlim2 hlim1

/-- For one particle, the mixed density of `Φ` and `FF g Φ` is the product `g ρ_Φ`. -/
lemma dE2_rhoE_one {Φ : Cfg 0 → ℝ} (hΦ : Φ ∈ DomN τ 0) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    dE2 (toE (h1N_of_C1 hg)) (rhoE τ Φ) = rhoE2 τ Φ (fun x => FF g x * Φ x) := by
  have hχ := mul_memN hΦ (contDiff_FF hg) (fun σ x => FF_pm g σ x)
  refine eq_of_int fun u => ?_
  have hwc : Continuous fun t => ext u t * g t := (continuous_ext u).mul hg.continuous
  have e1 : ∫ t, ext u t * ext (evE (dE2 (toE (h1N_of_C1 hg)) (rhoE τ Φ))) t ∂μ1 =
      ∫ t, ext (potOf _ hwc) t * ext (evE (rhoE τ Φ)) t ∂μ1 := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htI := Ioo_subset_Icc_self ht
    rw [ext_evE htI, ext_evE htI, fnE_dE2 _ _ htI, fnE_toE _ htI, ext_potOf hwc htI]; ring
  rw [e1, int_rhoE hΦ, int_rhoE2 hΦ hχ, pfN, pfN]
  refine integral_congr_ae ?_
  filter_upwards [ae_cube_x0] with x hx
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, FF]
  rw [ext_potOf hwc hx]
  ring

/-- **The pair-density identity.** If `D` annihilates every mixed density `ρ(Φ, χ)`, then
`D(g ρ_Φ) + ∫ g R = 0` for all compactly supported `C¹` functions `g`, for some `R ∈ L¹`. -/
theorem exists_R (D : PotH) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n)
    (hD : ∀ χ ∈ DomN τ n, D (rhoE2 τ Φ χ) = 0) :
    ∃ R : ℝ → ℝ, Integrable R μ1 ∧ ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g), HasCompactSupport g →
      D (dE2 (toE (h1N_of_C1 hg)) (rhoE τ Φ)) + ∫ t, g t * R t ∂μ1 = 0 := by
  cases n with
  | zero =>
    refine ⟨0, integrable_zero _ _ _, fun g hg _ => ?_⟩
    rw [dE2_rhoE_one hΦ hg, hD _ (mul_memN hΦ (contDiff_FF hg) (fun σ x => FF_pm g σ x))]
    simp
  | succ m => exact exists_R_succ D hΦ hD

/-! ### `D` against products with the density -/

lemma integrable_fnE_mulR (e : H1E) {R : ℝ → ℝ} (hR : Integrable R μ1) :
    Integrable (fun t => fnE e t * R t) μ1 :=
  hR.bdd_mul (c := ‖evE‖ * ‖e‖)
    (((continuousOn_fnE e).mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs]; exact abs_fnE_le e (Ioo_subset_Icc_self ht))

lemma bump01_eventually_one {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (fun s => bump01 s) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
  filter_upwards [Ioo_mem_nhds (show (-1 / 2 : ℝ) < t by linarith [ht.1])
    (show t < 3 / 2 by linarith [ht.2])] with s hs
  exact bump01.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> simp only [bump01] <;> linarith [hs.1, hs.2])

lemma contDiff_prim {f : ℝ → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (fun t => ∫ s in (0 : ℝ)..t, f s) := by
  have hd : ∀ t, deriv (fun t => ∫ s in (0 : ℝ)..t, f s) t = f t := fun t => Continuous.deriv_integral f hf 0 t
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt, ?_⟩
  rw [show deriv (fun t => ∫ s in (0 : ℝ)..t, f s) = f from funext hd]
  exact hf

/-- **`D` on products with `ρ`**: from the pair-density identity for compactly supported `C¹`
functions to `D(h ρ) = -∫ h R` for all `h ∈ H¹`. -/
theorem D_dE2_eq (D : PotH) (ρ : H1E) {R : ℝ → ℝ} (hR : Integrable R μ1)
    (hK : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g), HasCompactSupport g →
      D (dE2 (toE (h1N_of_C1 hg)) ρ) + ∫ t, g t * R t ∂μ1 = 0) (h : H1E) :
    D (dE2 h ρ) = -∫ t, fnE h t * R t ∂μ1 := by
  set I : H1E → ℝ := fun h => ∫ t, fnE h t * R t ∂μ1
  have hIadd : ∀ h h', I (h + h') = I h + I h' := fun h h' => by
    simp only [I]; rw [← integral_add (integrable_fnE_mulR h hR) (integrable_fnE_mulR h' hR)]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [fnE_add _ _ (Ioo_subset_Icc_self ht)]; ring
  have hIsmul : ∀ (c : ℝ) h, I (c • h) = c * I h := fun c h => by
    simp only [I]; rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [fnE_smul' _ _ (Ioo_subset_Icc_self ht)]; ring
  have hIb : ∀ h, |I h| ≤ ‖evE‖ * (∫ t, |R t| ∂μ1) * ‖h‖ := fun h => by
    simp only [I]; rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hR.abs.const_mul (‖evE‖ * ‖h‖)) ?_).trans (le_of_eq ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_fnE_le h (Ioo_subset_Icc_self ht)) (abs_nonneg _)
    · rw [integral_const_mul]; ring
  let Λl : H1E →ₗ[ℝ] ℝ :=
    { toFun := fun h => D (dE2 h ρ) + I h
      map_add' := fun h h' => by simp only [dE2_add_left, map_add, hIadd]; ring
      map_smul' := fun c h => by
        simp only [dE2_smul_left, map_smul, hIsmul, smul_eq_mul, RingHom.id_apply]; ring }
  let Λ : PotH := Λl.mkContinuous (‖D‖ * ((1 + 2 * ‖evE‖) * ‖ρ‖) + ‖evE‖ * ∫ t, |R t| ∂μ1)
    (fun h => by
      rw [Real.norm_eq_abs]
      change |D (dE2 h ρ) + I h| ≤ _
      have h1 : |D (dE2 h ρ)| ≤ ‖D‖ * ((1 + 2 * ‖evE‖) * ‖ρ‖) * ‖h‖ := by
        rw [← Real.norm_eq_abs]
        refine (D.le_opNorm _).trans ?_
        calc ‖D‖ * ‖dE2 h ρ‖ ≤ ‖D‖ * ((1 + 2 * ‖evE‖) * ‖h‖ * ‖ρ‖) :=
              mul_le_mul_of_nonneg_left (norm_dE2_le h ρ) (norm_nonneg _)
          _ = _ := by ring
      calc |D (dE2 h ρ) + I h| ≤ |D (dE2 h ρ)| + |I h| := abs_add_le _ _
        _ ≤ _ := by rw [add_mul]; exact add_le_add h1 (hIb h))
  have hΛ : ∀ h, Λ h = D (dE2 h ρ) + I h := fun h => rfl
  have hΛg : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g), HasCompactSupport g →
      Λ (toE (h1N_of_C1 hg)) = 0 := fun g hg hgc => by
    rw [hΛ]
    have e : I (toE (h1N_of_C1 hg)) = ∫ t, g t * R t ∂μ1 :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [fnE_toE _ (Ioo_subset_Icc_self ht)])
    rw [e]; exact hK g hg hgc
  set lam := (InnerProductSpace.toDual ℝ H1E).symm Λ
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the constant `1`
  have hb1 : ContDiff ℝ 1 (fun t => bump01 t) := bump01.contDiff
  have hfst : lam.fst = 0 := by
    have h0 := hΛg _ hb1 bump01.hasCompactSupport
    rw [D_apply, fnE_toE _ h01, bump01_eq_one h01, mul_one] at h0
    have hz : ∫ t, lam.snd t * (toE (h1N_of_C1 hb1)).snd t ∂μ1 = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [dN_ae (h1N_of_C1 hb1), ae_restrict_mem measurableSet_Ioo] with t h1 ht
      change lam.snd t * (dN (h1N_of_C1 hb1) : ℝ → ℝ) t = 0
      rw [h1, (bump01_eventually_one ht).deriv_eq, deriv_const, mul_zero]
    rw [hz, add_zero] at h0
    exact h0
  -- primitives of continuous functions
  have hsnd : (lam.snd : ℝ → ℝ) =ᵐ[μ1] 0 := by
    refine ae_eq_of_int_pot (integrable_L2I _) (integrable_zero _ _ _) fun u => ?_
    have hu := continuous_ext u
    set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ext u s
    have hG := contDiff_prim hu
    have hgu : ContDiff ℝ 1 (fun t => bump01 t * G t) := hb1.mul hG
    have h0 := hΛg _ hgu bump01.hasCompactSupport.mul_right
    rw [D_apply, hfst, zero_mul, zero_add] at h0
    simp only [Pi.zero_apply, mul_zero, integral_zero]
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [dN_ae (h1N_of_C1 hgu), ae_restrict_mem measurableSet_Ioo] with t h1 ht
    change ext u t * lam.snd t = lam.snd t * (dN (h1N_of_C1 hgu) : ℝ → ℝ) t
    have hev : (fun s => bump01 s * G s) =ᶠ[𝓝 t] G := by
      filter_upwards [bump01_eventually_one ht] with s hs
      rw [hs, one_mul]
    rw [h1, hev.deriv_eq, Continuous.deriv_integral _ hu 0 t, mul_comm]
  have hΛ0 : Λ h = 0 := by
    rw [D_apply, hfst, zero_mul, zero_add]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hsnd] with t ht
    rw [ht, Pi.zero_apply, zero_mul]
  rw [hΛ] at hΛ0
  linarith

/-! ### `D` as an integral against an `L¹` function -/

/-- `1 / f ∈ H¹` for `f ∈ H¹` bounded below by `c > 0`. -/
lemma h1N_inv {f : ℝ → ℝ} (hf : H1N f) {c : ℝ} (hc : 0 < c)
    (hfc : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ f t) : H1N fun t => (f t)⁻¹ := by
  have hLip : LipschitzOnWith ⟨(c ^ 2)⁻¹, by positivity⟩ (fun x : ℝ => x⁻¹) (Ici c) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hx0 : 0 < x := hc.trans_le hx
    have hy0 : 0 < y := hc.trans_le hy
    simp only [Real.dist_eq]
    rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm,
      div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact inv_anti₀ (by positivity) (by rw [sq]; exact mul_le_mul hx hy hc.le hx0.le)
  have hmap : MapsTo f (uIcc 0 1) (Ici c) := fun t ht => hfc t (by rwa [uIcc01] at ht)
  refine ⟨hLip.comp_absolutelyContinuousOnInterval hmap hf.1, ?_⟩
  have hdf := hf.1.ae_differentiableAt
  rw [uIcc01] at hdf
  refine (hf.int_dsq.const_mul (c ^ 4)⁻¹).mono' ((measurable_deriv _).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae hdf, ae_restrict_mem measurableSet_Ioo] with t h1 ht
  have htI := Ioo_subset_Icc_self ht
  have hft := hfc t htI
  have hf0 : f t ≠ 0 := (hc.trans_le hft).ne'
  have hd : HasDerivAt (fun y => (f y)⁻¹) (-(deriv f t) / f t ^ 2) t :=
    (h1 htI).hasDerivAt.inv hf0
  rw [hd.deriv, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [div_pow, neg_sq, ← pow_mul, div_eq_mul_inv, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact inv_anti₀ (by positivity) (by
    norm_num
    exact pow_le_pow_left₀ hc.le hft 4)

lemma integrable_div_rho {R : ℝ → ℝ} (hR : Integrable R μ1) (ρ : H1E) {c : ℝ} (hc : 0 < c)
    (hρc : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ fnE ρ t) :
    Integrable (fun t => -(R t * (fnE ρ t)⁻¹)) μ1 := by
  have hm : AEStronglyMeasurable (fun t => (fnE ρ t)⁻¹) μ1 :=
    ((((continuousOn_fnE ρ).inv₀ fun t ht => (hc.trans_le (hρc t ht)).ne').mono
      Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
  have h := hR.bdd_mul (c := c⁻¹) hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hft := hρc t (Ioo_subset_Icc_self ht)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hc.trans_le hft)]
    exact inv_anti₀ hc hft)
  exact (h.neg).congr (ae_of_all _ fun t => by simp only [Pi.neg_apply]; ring)

/-- **`D` is an integral**: `D(e) = ∫ e d` with `d = -R/ρ`. -/
theorem D_eq_integral_d (D : PotH) (ρ : H1E) {c : ℝ} (hc : 0 < c)
    (hρc : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ fnE ρ t) {R : ℝ → ℝ} (hR : Integrable R μ1)
    (hK : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g), HasCompactSupport g →
      D (dE2 (toE (h1N_of_C1 hg)) ρ) + ∫ t, g t * R t ∂μ1 = 0) (e : H1E) :
    D e = ∫ t, fnE e t * -(R t * (fnE ρ t)⁻¹) ∂μ1 := by
  have hq : H1N fun t => fnE e t * (fnE ρ t)⁻¹ :=
    (h1N_fnE e).mul (h1N_inv (h1N_fnE ρ) hc hρc)
  have he : dE2 (toE hq) ρ = e := eq_of_fnE fun t ht => by
    rw [fnE_dE2 _ _ ht, fnE_toE _ ht, mul_assoc, inv_mul_cancel₀ (hc.trans_le (hρc t ht)).ne',
      mul_one]
  rw [← he, D_dE2_eq D ρ hR hK, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have htI := Ioo_subset_Icc_self ht
  have hne := (hc.trans_le (hρc t htI)).ne'
  simp only [fnE_dE2 _ _ htI, fnE_toE _ htI]
  field_simp

/-! ### Mixed densities against `L¹` weights -/

/-- The marginal of `Φ²` is at most `‖evE‖ ‖ρ_Φ‖ / N`. -/
lemma marg_le_N {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) :
    ∀ᵐ t ∂μ1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 ≤ ‖evE‖ * ‖rhoE τ Φ‖ / (n + 1) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  filter_upwards [(gNH_spec hΦ).2.1, ae_restrict_mem measurableSet_Ioo] with t h1 ht
  have htI := Ioo_subset_Icc_self ht
  have e : fnE (rhoE τ Φ) t = rhoN Φ t := by rw [rhoE, sqE, fnE_toE _ htI, ← sq, h1]
  have hb := (le_abs_self _).trans (abs_fnE_le (rhoE τ Φ) htI)
  rw [e] at hb
  rw [le_div_iff₀ hN]
  simp only [rhoN, marg] at hb
  linarith

/-- **The mixed density against an `L¹` weight**:
`∫ e ρ(Φ, χΦ) = N ∫ e(x₀) χ Φ²` for a bounded symmetric `C¹` function `χ`. -/
theorem int_rhoE2_L1N {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n)
    {χ : Cfg n → ℝ} (hχ : ContDiff ℝ 1 χ) {Cχ : ℝ} (hχb : ∀ x, |χ x| ≤ Cχ)
    (hχs : ∀ σ x, χ (pm σ x) = χ x) {e : ℝ → ℝ} (he : Integrable e μ1) :
    ∫ t, e t * ext (evE (rhoE2 τ Φ (fun x => χ x * Φ x))) t ∂μ1 =
      (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hCχ : 0 ≤ Cχ := (abs_nonneg _).trans (hχb 0)
  have hχΦ := mul_memN hΦ hχ hχs
  set p := evE (rhoE2 τ Φ (fun x => χ x * Φ x))
  have hG := sq_sym_ae_of (fun σ => hΦ.2.2 σ trivial) hχs
  -- integrability of `u(x₀) χ Φ²` for `u ∈ L¹`
  have hint : ∀ {u : ℝ → ℝ}, Integrable u μ1 → Integrable (fun x => u (x 0) * (χ x * Φ x ^ 2))
      (μN n) := fun {u} hu => by
    have := (integrable_x0_sq_of hΦ.1 (marg_le_N hΦ) hu).1.bdd_mul (c := Cχ) hχ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hχb x)
    exact this.congr (ae_of_all _ fun x => by ring)
  -- the identity for continuous compactly supported weights
  have hcont : ∀ (v : ℝ → ℝ), Continuous v → HasCompactSupport v →
      ∫ t, v t * ext p t ∂μ1 = (n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n := by
    intro v hv hvs
    obtain ⟨Cv, hCv⟩ := hv.bounded_above_of_compact_support hvs
    have h1 : ∫ t, v t * ext p t ∂μ1 = ∫ t, ext (potOf v hv) t * ext p t ∂μ1 :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [ext_potOf hv (Ioo_subset_Icc_self ht)])
    rw [h1]
    refine (int_rhoE2 hΦ hχΦ (potOf v hv)).trans ?_
    rw [pfN]
    have hGi : Integrable (fun x => χ x * Φ x ^ 2) (μN n) :=
      (int_sq hΦ.1).bdd_mul hχ.continuous.aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact hχb x)
    have hb : ∀ t, ‖ext (potOf v hv) t‖ ≤ ‖potOf v hv‖ := fun t => by
      rw [Real.norm_eq_abs]; exact ext_le_norm _ _
    have hk : ∀ k : Fin (n + 1), Integrable (fun x => ext (potOf v hv) (x k) * (χ x * Φ x ^ 2))
        (μN n) := fun k =>
      hGi.bdd_mul ((continuous_ext _).comp (continuous_apply k)).aestronglyMeasurable
        (ae_of_all _ fun x => hb _)
    have e1 : (fun x => (∑ k, ext (potOf v hv) (x k)) * (Φ x * (χ x * Φ x))) =
        fun x => ∑ k, ext (potOf v hv) (x k) * (χ x * Φ x ^ 2) := by
      funext x
      rw [Finset.sum_mul]; congr 1; funext k; ring
    rw [e1, integral_finsetSum _ fun k _ => hk k]
    simp only [integral_xk_ae (G := fun x => χ x * Φ x ^ 2) hG (ext (potOf v hv)), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_cube_x0] with x hx
    rw [ext_potOf hv hx]
  -- approximation of `L¹` weights
  have hpb : ∀ t, |ext p t| ≤ ‖p‖ := fun t => ext_le_norm _ _
  have hint1 : ∀ {u : ℝ → ℝ}, Integrable u μ1 → Integrable (fun t => u t * ext p t) μ1 :=
    fun hu => (hu.bdd_mul (c := ‖p‖) (continuous_ext p).aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hpb t)).congr
        (ae_of_all _ fun t => by ring)
  set K := ‖p‖ + Cχ * (‖evE‖ * ‖rhoE τ Φ‖)
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ j : ℕ, |∫ t, e t * ext p t ∂μ1 -
      (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n| ≤ K * (1 / ((j : ℝ) + 1)) := by
    intro j
    obtain ⟨v, hvs, hvl, hvc, hvi⟩ := Integrable.exists_hasCompactSupport_integral_sub_le he
      (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))
    have hev : Integrable (fun t => e t - v t) μ1 := he.sub hvi
    have hl : |∫ t, e t * ext p t ∂μ1 - ∫ t, v t * ext p t ∂μ1| ≤ ‖p‖ * (1 / ((j : ℝ) + 1)) := by
      rw [← integral_sub (hint1 he) (hint1 hvi)]
      calc |∫ t, (e t * ext p t - v t * ext p t) ∂μ1| ≤ ∫ t, ‖p‖ * ‖e t - v t‖ ∂μ1 := by
            rw [← Real.norm_eq_abs]
            refine norm_integral_le_of_norm_le (hev.norm.const_mul _) (ae_of_all _ fun t => ?_)
            rw [← sub_mul, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (hpb t) (abs_nonneg _)
        _ ≤ ‖p‖ * (1 / ((j : ℝ) + 1)) := by
            rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hvl (norm_nonneg _)
    have hr : |(n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n -
        (n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n| ≤
          Cχ * (‖evE‖ * ‖rhoE τ Φ‖) * (1 / ((j : ℝ) + 1)) := by
      rw [← mul_sub, ← integral_sub (hint he) (hint hvi), abs_mul, abs_of_pos hN]
      have hT := (integrable_x0_sq_of hΦ.1 (marg_le_N hΦ) hev).2
      have hbd : |∫ x, (e (x 0) * (χ x * Φ x ^ 2) - v (x 0) * (χ x * Φ x ^ 2)) ∂μN n| ≤
          Cχ * ∫ x, |e (x 0) - v (x 0)| * Φ x ^ 2 ∂μN n := by
        rw [← Real.norm_eq_abs, ← integral_const_mul]
        refine norm_integral_le_of_norm_le (((integrable_x0_sq_of hΦ.1 (marg_le_N hΦ) hev).1.norm).const_mul Cχ
          |>.congr (ae_of_all _ fun x => by
            simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Φ x))])) ?_
        refine ae_of_all _ fun x => ?_
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
        nlinarith [hχb x, abs_nonneg (e (x 0) - v (x 0)), sq_nonneg (Φ x), abs_nonneg (χ x),
          mul_nonneg (abs_nonneg (e (x 0) - v (x 0))) (sq_nonneg (Φ x))]
      calc (n + 1) * |∫ x, (e (x 0) * (χ x * Φ x ^ 2) - v (x 0) * (χ x * Φ x ^ 2)) ∂μN n|
          ≤ (n + 1) * (Cχ * ((‖evE‖ * ‖rhoE τ Φ‖) / (n + 1) * ∫ t, |e t - v t| ∂μ1)) :=
            mul_le_mul_of_nonneg_left (hbd.trans (mul_le_mul_of_nonneg_left hT hCχ)) hN.le
        _ = Cχ * (‖evE‖ * ‖rhoE τ Φ‖) * ∫ t, ‖e t - v t‖ ∂μ1 := by
            simp only [Real.norm_eq_abs]; field_simp
        _ ≤ Cχ * (‖evE‖ * ‖rhoE τ Φ‖) * (1 / ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hvl (by positivity)
    rw [hcont v hvc hvs] at hl
    calc _ ≤ |∫ t, e t * ext p t ∂μ1 - (n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n| +
          |(n + 1) * ∫ x, v (x 0) * (χ x * Φ x ^ 2) ∂μN n -
            (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n| := abs_sub_le _ _ _
      _ ≤ ‖p‖ * (1 / ((j : ℝ) + 1)) + Cχ * (‖evE‖ * ‖rhoE τ Φ‖) * (1 / ((j : ℝ) + 1)) := by
          rw [abs_sub_comm ((n + 1) * ∫ x, v (x 0) * _ ∂μN n)]; exact add_le_add hl hr
      _ = K * (1 / ((j : ℝ) + 1)) := by simp only [K]; ring
  have hlim : Tendsto (fun j : ℕ => K * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K
  have h0 := ge_of_tendsto' hlim hbound
  have := abs_nonneg (∫ t, e t * ext p t ∂μ1 - (n + 1) * ∫ x, e (x 0) * (χ x * Φ x ^ 2) ∂μN n)
  linarith [abs_eq_zero.1 (le_antisymm h0 this), sub_eq_zero.1 (abs_eq_zero.1
    (le_antisymm h0 this))]


/-! ### Hohenberg–Kohn -/

/-- **`D` vanishes** if it annihilates every mixed density of a ground state. -/
theorem D_eq_zero_of_gs {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Φ : Cfg n → ℝ}
    (hgs : IsGSNH τ w v Φ) (D : PotH) (hD : ∀ χ ∈ DomN τ n, D (rhoE2 τ Φ χ) = 0) : D = 0 := by
  have hΦ := hgs.1
  have hN : (0 : ℝ) < n + 1 := by positivity
  obtain ⟨R, hR, hK⟩ := exists_R D hΦ hD
  set ρ := rhoE τ Φ
  obtain ⟨c, hc, hρc⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) 1, c ≤ fnE ρ t := by
    obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
      (continuousOn_fnE ρ)
    exact ⟨fnE ρ t0, rhoE_pos hw hgs ht0, fun t ht => hmin ht⟩
  set d : ℝ → ℝ := fun t => -(R t * (fnE ρ t)⁻¹)
  have hd : Integrable d μ1 := integrable_div_rho hR ρ hc hρc
  have hrep : ∀ e, D e = ∫ t, fnE e t * d t ∂μ1 := D_eq_integral_d D ρ hc hρc hR hK
  -- the symmetric tests
  have htest : ∀ χ : Cfg n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ boxU n 0 → (∀ σ x, χ (pm σ x) = χ x) →
      ∫ x, d (x 0) * (χ x * Φ x ^ 2) ∂μN n = 0 := by
    intro χ hχ hχc _ hχs
    have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
    obtain ⟨Cχ, hCχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    have hCχ' : ∀ x, |χ x| ≤ Cχ := fun x => by simpa using hCχ x
    have h0 := hD _ (mul_memN hΦ hχ1 hχs)
    rw [hrep] at h0
    have hL1 := int_rhoE2_L1N hΦ hχ1 hCχ' hχs hd
    have e1 : ∫ t, fnE (rhoE2 τ Φ (fun x => χ x * Φ x)) t * d t ∂μ1 =
        ∫ t, d t * ext (evE (rhoE2 τ Φ (fun x => χ x * Φ x))) t ∂μ1 := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [ext_evE (Ioo_subset_Icc_self ht), mul_comm]
    rw [e1, hL1] at h0
    exact (mul_eq_zero.1 h0).resolve_left hN.ne'
  have hT := (integrable_x0_sq_of hΦ.1 (marg_le_N hΦ) hd).1
  have hG := sum_ae_zero_of (fun σ => hΦ.2.2 σ trivial) hT le_rfl htest
  have hsum : ∀ᵐ x ∂μN n, x ∈ boxU n 0 → ∑ k, d (x k) = 0 := by
    filter_upwards [ae_restrict_of_ae hG, gsNH_ne_zero hw hgs] with x h1 h2 hxU
    rcases mul_eq_zero.1 (h1 hxU) with h3 | h3
    · exact h3
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h3) h2
  -- a normalised tent
  set T : ℝ → ℝ := tentF (1 / 2) (1 / 2 - 0)
  have hw2 : (0 : ℝ) < 1 / 2 - 0 := by norm_num
  have hTc : Continuous T := (lipschitz_tent hw2).continuous
  have hT0 : ∀ t, t ∉ Ioo 0 (1 - 0) → T t = 0 := fun t ht => by
    refine tent_far hw2 ?_
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have hTnn : ∀ t, 0 ≤ T t := fun t => le_max_left _ _
  have hTpos : 0 < ∫ t, T t ∂μ1 :=
    integral_pos_of_cont hTc hTnn (t0 := 1 / 2) ⟨by norm_num, by norm_num⟩
      (by simp only [T, tentF, sub_self, abs_zero, zero_div, sub_zero]; norm_num)
  set η : ℝ → ℝ := fun t => T t / ∫ t, T t ∂μ1
  have hηc : Continuous η := hTc.div_const _
  have hη0 : ∀ t, t ∉ Ioo 0 (1 - 0) → η t = 0 := fun t ht => by simp [η, hT0 t ht]
  have hη1 : ∫ t, η t ∂μ1 = 1 := by
    simp only [η]; rw [integral_div]; exact div_self hTpos.ne'
  have hκ : ∫ t, η t * d t ∂μ1 = 0 := by
    have := product_identity hd hsum hηc hηc hη0 hη0 hη1
    rw [hη1, one_mul] at this
    have : ((n : ℝ) + 1) * ∫ t, η t * d t ∂μ1 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hN.ne'
  -- `d = 0`
  have hd0 : d =ᵐ[μ1] 0 := by
    refine ae_eq_zero_of_test1 hd fun χ hχ => ?_
    set φ : ℝ → ℝ := fun t => χ (max 0 (min 1 t))
    have hφc : Continuous φ :=
      hχ.1.continuous.comp (continuous_const.max (continuous_const.min continuous_id))
    have hφ0 : ∀ t, t ∉ Ioo 0 (1 - 0) → φ t = 0 := fun t ht => by
      rw [sub_zero, mem_Ioo, not_and_or, not_lt, not_lt] at ht
      rcases ht with h | h
      · have e : max 0 (min 1 t) = (0 : ℝ) := by
          rw [min_eq_right (by linarith), max_eq_left h]
        simp only [φ, e, hχ.2.1]
      · have e : max 0 (min 1 t) = (1 : ℝ) := by rw [min_eq_left h, max_eq_right zero_le_one]
        simp only [φ, e, hχ.2.2]
    have h1 := product_identity hd hsum hφc hηc hφ0 hη0 hη1
    rw [hκ, mul_zero, mul_zero, add_zero] at h1
    calc ∫ t, d t * χ t ∂μ1 = ∫ t, φ t * d t ∂μ1 := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          have e : max 0 (min 1 t) = t := by rw [min_eq_right ht.2.le, max_eq_right ht.1.le]
          simp only [φ, e]; ring
      _ = 0 := h1
  ext e
  rw [hrep, zero_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hd0] with t ht
  rw [ht, Pi.zero_apply, mul_zero]

/-- The mass of a mixed density. -/
lemma ellE_rhoE2 {A B : Cfg n → ℝ} (hA : A ∈ DomN τ n) (hB : B ∈ DomN τ n) :
    ellE (rhoE2 τ A B) = (n + 1) * ∫ x, A x * B x ∂μN n := by
  have h := int_rhoE2 hA hB 1
  have e1 : ∀ t, ext (1 : Pot) t = 1 := fun t => by simp [Box.ext]
  simp only [e1, one_mul, pfN, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [integral_const_mul] at h
  push_cast at h
  rw [ellE_apply, ← h]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [ext_evE (Ioo_subset_Icc_self ht)]

/-- **Hohenberg–Kohn with Neumann walls and `H⁻¹` potentials** (Corso, Thm 2.9). If ground
states of `v` and `v'` have the same density, then `v - v'` is a constant potential. -/
theorem hkNH {w : Cfg n → ℝ} (hw : Continuous w) {v v' : PotH} {Ψ Φ : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) (hΦ : IsGSNH τ w v' Φ) (hρ : rhoE τ Ψ = rhoE τ Φ) :
    ∃ c : ℝ, v - v' = c • ellE := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have h1 := hΨ.2.2 Φ hΦ.1 hΦ.2.1
  have h2 := hΦ.2.2 Ψ hΨ.1 hΨ.2.1
  simp only [QNH, hρ] at h1 h2
  have hΦv : IsGSNH τ w v Φ := ⟨hΦ.1, hΦ.2.1, fun Ξ hΞ hn => by
    have := hΨ.2.2 Ξ hΞ hn
    simp only [QNH, hρ] at this ⊢
    linarith⟩
  set E := QNH τ w v Φ
  set E' := QNH τ w v' Φ
  refine ⟨(E - E') / (n + 1), sub_eq_zero.1 (D_eq_zero_of_gs hw hΦv _ fun χ hχ => ?_)⟩
  have e1 := euler_lagrangeNH hw hΦv hχ
  have e2 := euler_lagrangeNH hw hΦ hχ
  have e3 := ellE_rhoE2 hΦ.1 hχ
  have e4 : (E - E') / (n + 1) * ((n + 1) * ∫ x, Φ x * χ x ∂μN n) =
      (E - E') * ∫ x, Φ x * χ x ∂μN n := by field_simp
  simp only [sub_apply, smul_apply, smul_eq_mul, e3, e4]
  linarith

end DFT.Continuum.Line
