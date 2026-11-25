/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeuSeries

/-!
# `√ρ ∈ H¹` for Neumann states

For every `H¹` state `Φ` of the cube (Neumann walls), `√ρ_Φ` has a representative `g ∈ H¹(0, 1)`
with `∫ g'² ≤ T(Φ)` (**`sqrt_dens_H1N`**), the Neumann version of Hoffmann-Ostenhof's inequality.

* **`h1N_closure`**: if `u_j ∈ H¹(0, 1)` have `∫ u_j'² ≤ C` and `u_j → f` in `L²`, then `f` has a
  representative `g ∈ H¹(0, 1)` with `∫ g'² ≤ C`. Proof through `H1E = ℝ × L²` as in `Line/NeuGS`:
  the constants are bounded, the derivatives converge weakly, the functions uniformly.
* `truncC M Φ = Σ_{m ∈ [0, M)ᴺ} ⟨c_m, Φ⟩ c_m`: `C²`, of the exchange symmetry of `Φ`
  (`truncC_mem`), converging to `Φ` in `L²` (`tendsto_truncC`), with classical kinetic energy
  `Σ_{box} λᶜ_m ⟨c_m, Φ⟩² ≤ T(Φ)` (`kin_truncC_le`).
* Then `u_M = √(ρ_M + ε_M) - √ε_M` (`Line/WeakNec`, on `DomC`) and the closure lemma.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine Spectral

variable {n : ℕ} {τ : Stat}

/-! ### The closure lemma -/

lemma sq_sub_le_two (a b c : ℝ) : (a - c) ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * (b - c) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b + c)]

lemma H1N.memLp {g : ℝ → ℝ} (hg : H1N g) : MemLp g 2 μ1 :=
  (memLp_two_iff_integrable_sq (H10.aesm_of_contOn hg.continuousOn)).2 hg.int_sq

/-- **Closure**: `L²` limits of functions bounded in `H¹(0, 1)` are in `H¹(0, 1)`. -/
theorem h1N_closure {u : ℕ → ℝ → ℝ} (hu : ∀ j, H1N (u j)) {C : ℝ} (hC : ∀ j, kinM (u j) ≤ C)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ1)
    (hL2 : Tendsto (fun j => ∫ t, (u j t - f t) ^ 2 ∂μ1) atTop (𝓝 0)) :
    ∃ g : ℝ → ℝ, H1N g ∧ g =ᵐ[μ1] f ∧ kinM g ≤ C := by
  have hC0 : 0 ≤ C := (integral_nonneg fun _ => sq_nonneg _).trans (hC 0)
  obtain ⟨B, hB⟩ := hL2.bddAbove_range
  have hB' : ∀ j, ∫ t, (u j t - f t) ^ 2 ∂μ1 ≤ B := fun j => hB ⟨j, rfl⟩
  have if2 : Integrable (fun t => f t ^ 2) μ1 := 
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have iD : ∀ j, Integrable (fun t => (u j t - f t) ^ 2) μ1 := fun j =>
    (memLp_two_iff_integrable_sq ((hu j).memLp.sub hf).aestronglyMeasurable).1
      ((hu j).memLp.sub hf)
  set F := ∫ t, f t ^ 2 ∂μ1
  have hnorm : ∀ j, ∫ t, u j t ^ 2 ∂μ1 ≤ 2 * B + 2 * F := fun j => by
    have h1 : ∫ t, u j t ^ 2 ∂μ1 ≤ ∫ t, (2 * (u j t - f t) ^ 2 + 2 * f t ^ 2) ∂μ1 :=
      integral_mono (hu j).int_sq (((iD j).const_mul 2).add (if2.const_mul 2)) fun t => by
        nlinarith [sq_nonneg (u j t - 2 * f t)]
    rw [integral_add ((iD j).const_mul 2) (if2.const_mul 2), integral_const_mul,
      integral_const_mul] at h1
    linarith [hB' j]
  -- the `H1E` representatives
  set e : ℕ → H1E := fun j => toE (hu j)
  have hR : ∀ j, ‖(e j).snd‖ ≤ √C := fun j => by
    have h : ‖(e j).snd‖ ^ 2 ≤ C := by
      change ‖dN (hu j)‖ ^ 2 ≤ C; rw [norm_dN_sq]; exact hC j
    have := Real.abs_le_sqrt h
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  set K := √(2 * (2 * B + 2 * F) + C)
  have hF : ∀ j, |(e j).fst| ≤ K := fun j => by
    refine Real.abs_le_sqrt ?_
    have h1 := sq_le_H1N (hu j) one_pos (t := 0) ⟨le_rfl, zero_le_one⟩
    change u j 0 ^ 2 ≤ _
    linarith [hnorm j, hC j]
  obtain ⟨c, -, φ₁, hφ₁, hc⟩ := tendsto_subseq_of_bounded (x := fun k => (e k).fst)
    (Metric.isBounded_Icc (-K) K) fun k => abs_le.1 (hF k)
  obtain ⟨G, φ₂, hφ₂, hw⟩ := exists_weak_subseq (f := fun k => (e (φ₁ k)).snd) fun k => hR _
  set φ := φ₁ ∘ φ₂
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  set e₀ : H1E := WithLp.toLp 2 (c, G)
  have hfst : Tendsto (fun k => (e (φ k)).fst) atTop (𝓝 e₀.fst) := hc.comp hφ₂.tendsto_atTop
  have hP : Tendsto (fun k => evE (e (φ k))) atTop (𝓝 (evE e₀)) := by
    simp only [evE_eq]
    exact ((ContinuousMap.continuous_const').tendsto _ |>.comp hfst).add
      (tendsto_primP (fun k => hR _) hw)
  -- the limit is `f`
  have hlim0 : ∫ t, (fnE e₀ t - f t) ^ 2 ∂μ1 ≤ 0 := by
    have i0 : Integrable (fun t => (fnE e₀ t - f t) ^ 2) μ1 :=
      (memLp_two_iff_integrable_sq ((h1N_fnE e₀).memLp.sub hf).aestronglyMeasurable).1
        ((h1N_fnE e₀).memLp.sub hf)
    have hbd : ∀ k, ∫ t, (fnE e₀ t - f t) ^ 2 ∂μ1 ≤
        2 * ‖evE e₀ - evE (e (φ k))‖ ^ 2 + 2 * ∫ t, (u (φ k) t - f t) ^ 2 ∂μ1 := fun k => by
      have h1 : ∫ t, (fnE e₀ t - f t) ^ 2 ∂μ1 ≤
          ∫ t, (2 * ‖evE e₀ - evE (e (φ k))‖ ^ 2 + 2 * (u (φ k) t - f t) ^ 2) ∂μ1 := by
        refine integral_mono_ae i0 ((integrable_const _).add ((iD _).const_mul 2)) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have htI := Ioo_subset_Icc_self ht
        have hdiff : |fnE e₀ t - u (φ k) t| ≤ ‖evE e₀ - evE (e (φ k))‖ := by
          have := (evE e₀ - evE (e (φ k))).norm_coe_le_norm ⟨t, htI⟩
          rw [ContinuousMap.sub_apply, evE_apply, evE_apply, Real.norm_eq_abs] at this
          simp only [e] at this
          rwa [fnE_toE (hu _) htI] at this
        have := sq_sub_le_two (fnE e₀ t) (u (φ k) t) (f t)
        have h2 : (fnE e₀ t - u (φ k) t) ^ 2 ≤ ‖evE e₀ - evE (e (φ k))‖ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
        linarith
      rw [integral_add (integrable_const _) ((iD _).const_mul 2), integral_const_mul] at h1
      simpa [integral_const_mul] using h1
    have hz : Tendsto (fun k => 2 * ‖evE e₀ - evE (e (φ k))‖ ^ 2 +
        2 * ∫ t, (u (φ k) t - f t) ^ 2 ∂μ1) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => ‖evE e₀ - evE (e (φ k))‖) atTop (𝓝 0) := by
        have := tendsto_iff_norm_sub_tendsto_zero.1 hP
        simpa [norm_sub_rev] using this
      have := ((h1.pow 2).const_mul 2).add ((hL2.comp hφ.tendsto_atTop).const_mul 2)
      simpa using this
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hz hbd
  have hae : fnE e₀ =ᵐ[μ1] f := by
    have i0 : Integrable (fun t => (fnE e₀ t - f t) ^ 2) μ1 :=
      (memLp_two_iff_integrable_sq ((h1N_fnE e₀).memLp.sub hf).aestronglyMeasurable).1
        ((h1N_fnE e₀).memLp.sub hf)
    have h0 : ∫ t, (fnE e₀ t - f t) ^ 2 ∂μ1 = 0 :=
      le_antisymm hlim0 (integral_nonneg fun _ => sq_nonneg _)
    have := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) i0).1 h0
    filter_upwards [this] with t ht
    have : (fnE e₀ t - f t) ^ 2 = 0 := ht
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  -- the kinetic energy, by weak lower semicontinuity
  have hGG : ‖G‖ ^ 2 ≤ √C * ‖G‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact le_of_tendsto' (hw G) fun k =>
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR _) (norm_nonneg _))
  have hGC : ‖G‖ ^ 2 ≤ C := by
    have : ‖G‖ ≤ √C := by
      rcases (norm_nonneg G).eq_or_lt with h | h
      · rw [← h]; exact Real.sqrt_nonneg _
      · nlinarith
    calc ‖G‖ ^ 2 ≤ √C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = C := Real.sq_sqrt hC0
  refine ⟨fnE e₀, h1N_fnE e₀, hae, ?_⟩
  rw [kinM_fnE]; exact hGC

/-! ### `L¹` convergence of squares -/

/-- `L²` convergence `P_M → Φ` gives `L¹` convergence `P_M² → Φ²`. -/
lemma tendsto_abs_sq_of_L2 {P : ℕ → Cfg n → ℝ} {Φ : Cfg n → ℝ} (hPm : ∀ M, MemLp (P M) 2 (μN n))
    (hΦ : MemLp Φ 2 (μN n)) (hD : Tendsto (fun M => ∫ x, (Φ x - P M x) ^ 2 ∂μN n) atTop (𝓝 0)) :
    Tendsto (fun M => ∫ x, |P M x ^ 2 - Φ x ^ 2| ∂μN n) atTop (𝓝 0) := by
  set D : ℕ → ℝ := fun M => ∫ x, (Φ x - P M x) ^ 2 ∂μN n
  set S := ∫ x, Φ x ^ 2 ∂μN n
  have bound : ∀ M, ∫ x, |P M x ^ 2 - Φ x ^ 2| ∂μN n ≤ √(D M) * √(2 * D M + 8 * S) := by
    intro M
    have hd : MemLp (fun x => P M x - Φ x) 2 (μN n) := (hPm M).sub hΦ
    have hs : MemLp (fun x => P M x + Φ x) 2 (μN n) := (hPm M).add hΦ
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μN n) Real.HolderConjugate.two_two
      (f := fun x => |P M x - Φ x|) (g := fun x => |P M x + Φ x|)
      (ae_of_all _ fun x => abs_nonneg _) (ae_of_all _ fun x => abs_nonneg _)
      (by rw [ENNReal.ofReal_ofNat]; exact hd.abs) (by rw [ENNReal.ofReal_ofNat]; exact hs.abs)
    have e1 : (∫ x, |P M x - Φ x| ^ (2 : ℝ) ∂μN n) = D M := by
      simp only [D]; congr 1; funext x; rw [Real.rpow_two, sq_abs]; ring
    have e2 : ∫ x, |P M x + Φ x| ^ (2 : ℝ) ∂μN n ≤ 2 * D M + 8 * S := by
      simp only [D, S, Real.rpow_two, sq_abs]
      have iD : Integrable (fun x => (Φ x - P M x) ^ 2) (μN n) := int_sq (hΦ.sub (hPm M))
      have iS := int_sq hΦ
      have iA := int_sq hs
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (f := fun x => 2 * (Φ x - P M x) ^ 2) (g := fun x => 8 * Φ x ^ 2)
          (iD.const_mul _) (iS.const_mul _)]
      refine integral_mono iA ((iD.const_mul _).add (iS.const_mul _)) fun x => ?_
      nlinarith [sq_nonneg (P M x - Φ x - 2 * Φ x)]
    calc ∫ x, |P M x ^ 2 - Φ x ^ 2| ∂μN n
        = ∫ x, |P M x - Φ x| * |P M x + Φ x| ∂μN n := by
          congr 1; funext x; exact abs_sq_sub_sq_le _ _
      _ ≤ _ := h
      _ ≤ √(D M) * √(2 * D M + 8 * S) := by
          rw [e1, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          gcongr
  have hlim : Tendsto (fun M => √(D M) * √(2 * D M + 8 * S)) atTop (𝓝 0) := by
    have := (hD.sqrt).mul (((hD.const_mul 2).add_const (8 * S)).sqrt)
    simpa using this
  exact squeeze_zero (fun M => integral_nonneg fun x => abs_nonneg _) bound hlim

/-! ### Cosine truncations -/

lemma contDiff_cn_top (k : ℕ) : ContDiff ℝ 2 (cn k) := by
  cases k with
  | zero => exact contDiff_const
  | succ k => unfold cn cs; fun_prop

lemma contDiff_cP2 (m : Fin (n + 1) → ℕ) : ContDiff ℝ 2 (cP m) :=
  contDiff_prod fun j _ => (contDiff_cn_top (m j)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).contDiff

/-- The truncated cosine series. -/
noncomputable def truncC (M : ℕ) (Φ : Cfg n → ℝ) (x : Cfg n) : ℝ :=
  ∑ m ∈ boxI n M, cC m Φ * cP m x

lemma continuous_truncC (M : ℕ) (Φ : Cfg n → ℝ) : Continuous (truncC M Φ) :=
  continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_cP m)

lemma contDiff_truncC (M : ℕ) (Φ : Cfg n → ℝ) : ContDiff ℝ 2 (truncC M Φ) :=
  ContDiff.sum fun m _ => contDiff_const.mul (contDiff_cP2 m)

lemma coeFn_sum_eC (s : Finset (Fin (n + 1) → ℕ)) (c : (Fin (n + 1) → ℕ) → ℝ) :
    ((∑ m ∈ s, c m • eC m : HN n) : Cfg n → ℝ) =ᵐ[μN n] fun x => ∑ m ∈ s, c m * cP m x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 (μN n)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • eC a) (∑ m ∈ s, c m • eC m),
      Lp.coeFn_smul (c a) (eC a), coeFn_eC a, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Finset.sum_insert ha, smul_eq_mul]

lemma integral_sub_truncC_sq {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (M : ℕ) :
    ∫ x, (Φ x - truncC M Φ x) ^ 2 ∂μN n = ∫ x, Φ x ^ 2 ∂μN n - ∑ m ∈ boxI n M, cC m Φ ^ 2 := by
  have h := orthonormal_norm_sub_sq eC_orthonormal (hΦ.toLp Φ) (boxI n M)
  simp only [inner_eC_toLp hΦ, norm_sq_toLp hΦ] at h
  rw [← h, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hΦ.toLp Φ) (∑ m ∈ boxI n M, cC m Φ • eC m),
    MemLp.coeFn_toLp hΦ, coeFn_sum_eC (boxI n M) (fun m => cC m Φ)] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  simp [truncC, sq]

theorem tendsto_truncC {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) :
    Tendsto (fun M => ∫ x, (Φ x - truncC M Φ x) ^ 2 ∂μN n) atTop (𝓝 0) := by
  simp only [integral_sub_truncC_sq hΦ]
  have h := (parsevalCW hΦ).comp tendsto_boxI
  have := (tendsto_const_nhds (x := ∫ x, Φ x ^ 2 ∂μN n)).sub h
  rwa [sub_self] at this

lemma cP_pm' (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    cP m (pm σ x) = cP (pmI σ⁻¹ m) x := by
  have h := cP_pm σ (pmI σ⁻¹ m) x
  rwa [pmI_pmI, inv_mul_cancel, pmI_one] at h

/-- **The truncations are `C²` functions** of the same exchange symmetry. -/
theorem truncC_mem {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (M : ℕ) : truncC M Φ ∈ DomC τ n := by
  refine ⟨contDiff_truncC M Φ, fun σ x => ?_⟩
  simp only [truncC, cP_pm', Finset.mul_sum]
  refine Finset.sum_nbij' (pmI σ⁻¹) (pmI σ) (fun m hm => (pmI_mem_boxI σ⁻¹).2 hm)
    (fun m hm => (pmI_mem_boxI σ).2 hm) (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
  · rw [pmI_pmI, inv_mul_cancel, pmI_one]
  · rw [pmI_pmI, mul_inv_cancel, pmI_one]
  · have h := cC_pmNS hΦ (σ := σ) trivial (pmI σ⁻¹ m)
    rw [pmI_pmI, inv_mul_cancel, pmI_one] at h
    rw [h]; change _ = τ.toSym.χ σ * _; ring

lemma cC_truncC (Φ : Cfg n → ℝ) (M : ℕ) (m' : Fin (n + 1) → ℕ) :
    cC m' (truncC M Φ) = if m' ∈ boxI n M then cC m' Φ else 0 := by
  rw [cC]
  have e : (fun x => cP m' x * truncC M Φ x) =
      fun x => ∑ m ∈ boxI n M, cC m Φ * (cP m' x * cP m x) := by
    funext x; simp only [truncC, Finset.mul_sum]; congr 1; funext m; ring
  rw [e, integral_finsetSum (f := fun m x => cC m Φ * (cP m' x * cP m x)) _
    fun m _ => integrableN (continuous_const.mul ((continuous_cP m').mul (continuous_cP m)))]
  simp only [integral_const_mul, muN_eq, cP_orthonormal, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- Neumann weak derivatives only see `Φ` up to a.e. equality. -/
lemma IsWDN.congr_ae {k : Fin (n + 1)} {Φ Ψ G : Cfg n → ℝ} (h : IsWDN k Φ G)
    (hΦΨ : Φ =ᵐ[μN n] Ψ) : IsWDN k Ψ G :=
  ⟨h.1, fun φ hφ => by
    rw [← h.2 φ hφ]
    exact integral_congr_ae (by filter_upwards [hΦΨ] with x hx; rw [hx])⟩

/-- **The truncations have kinetic energy at most `T(Φ)`.** -/
theorem kin_truncC_le {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) (M : ℕ) :
    ∫ x, ∑ k, dk k (truncC M Φ) x * dk k (truncC M Φ) x ∂μN n ≤ kinN Φ := by
  classical
  set a : (Fin (n + 1) → ℕ) → ℝ := fun m => if m ∈ boxI n M then cC m Φ else 0
  have hfin : ∀ m, m ∉ boxI n M → a m = 0 := fun m hm => by simp [a, hm]
  have ha : DirN τ.toSym a :=
    { sq := summable_of_ne_finset_zero (s := boxI n M) fun m hm => by simp [hfin m hm]
      kin := summable_of_ne_finset_zero (s := boxI n M) fun m hm => by simp [hfin m hm]
      sym := fun σ _ m => by
        simp only [a, pmI_mem_boxI]
        split_ifs
        · exact cC_pmNS hΦ trivial m
        · simp }
  have hae : serN a =ᵐ[μN n] truncC M Φ :=
    ae_eq_of_cC_eq memLp_serN (memLp_cont (continuous_truncC M Φ)) fun m => by
      rw [cC_serN ha.sq, cC_truncC]
  have hk : ∀ k, dWN k (serN a) =ᵐ[μN n] dk k (truncC M Φ) := fun k =>
    dWN_ae_eq ((isWDN_of_C1 ((contDiff_truncC M Φ).of_le (by norm_num)) k).congr_ae hae.symm)
  have hkin : kinN (serN a) = ∫ x, ∑ k, dk k (truncC M Φ) x * dk k (truncC M Φ) x ∂μN n := by
    rw [kinN, integral_finsetSum (f := fun k x => dk k (truncC M Φ) x * dk k (truncC M Φ) x) _
      fun k _ => integrableN
      ((continuous_dk_of_C1 ((contDiff_truncC M Φ).of_le (by norm_num)) k).mul
        (continuous_dk_of_C1 ((contDiff_truncC M Φ).of_le (by norm_num)) k))]
    refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
    filter_upwards [hk k] with x hx; rw [hx]
  rw [← hkin, kinN_serN ha, tsum_eq_sum (s := boxI n M) fun m hm => by simp [hfin m hm]]
  calc ∑ m ∈ boxI n M, lamC m * a m ^ 2 = ∑ m ∈ boxI n M, lamC m * cC m Φ ^ 2 :=
        Finset.sum_congr rfl fun m hm => by simp [a, hm]
    _ ≤ kinN Φ := sum_lamC_le (h1NW_of_mem hΦ) _

/-! ### `√ρ ∈ H¹` -/

/-- **`√ρ ∈ H¹` with Neumann walls**: for every `H¹` state `Φ`, `√ρ_Φ` has a representative
`g ∈ H¹(0, 1)` with `∫ g'² ≤ T(Φ)`. -/
theorem sqrt_dens_H1N {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n) :
    ∃ g : ℝ → ℝ, H1N g ∧ (∀ᵐ t ∂μ1, g t ^ 2 = rhoN Φ t) ∧ kinM g ≤ kinN Φ := by
  set ε : ℕ → ℝ := fun M => 1 / ((M : ℝ) + 1)
  have hε : ∀ M, 0 < ε M := fun M => by positivity
  have hP : ∀ M, truncC M Φ ∈ DomC τ n := truncC_mem hΦ
  set u : ℕ → ℝ → ℝ := fun M s => √(rhoN (truncC M Φ) s + ε M) - √(ε M)
  have hu : ∀ M, ContDiff ℝ 1 (u M) := fun M => contDiff_ureg (hP M) (hε M)
  have hu1 : ∀ M, H1N (u M) := fun M => ⟨(hu M).contDiffOn.absolutelyContinuousOnInterval,
    integrable_of_continuous (((hu M).continuous_deriv le_rfl).pow 2)⟩
  have hρm := integrable_marg hΦ.1
  have hρ0 : ∀ t, 0 ≤ rhoN Φ t := fun t => mul_nonneg (by positivity) (marg_nonneg t)
  have hint : Integrable (rhoN Φ) μ1 := hρm.const_mul _
  have hfm : MemLp (fun t => √(rhoN Φ t)) 2 μ1 := by
    have hm : AEStronglyMeasurable (fun t => √(rhoN Φ t)) μ1 :=
      (continuous_sqrt.comp_aestronglyMeasurable hint.1)
    refine (memLp_two_iff_integrable_sq hm).2 (hint.congr (ae_of_all _ fun t => ?_))
    simp [Real.sq_sqrt (hρ0 t)]
  have hC : ∀ M, kinM (u M) ≤ kinN Φ := fun M =>
    (integral_deriv_ureg_le (hP M) (hε M)).trans (kin_truncC_le hΦ M)
  have hL1 : Tendsto (fun M => ∫ t, |rhoN (truncC M Φ) t - rhoN Φ t| ∂μ1) atTop (𝓝 0) := by
    have h := (tendsto_abs_sq_of_L2 (fun M => memLp_cont (continuous_truncC M Φ)) hΦ.1
      (tendsto_truncC hΦ.1)).const_mul ((n : ℝ) + 1)
    rw [mul_zero] at h
    exact squeeze_zero (fun M => integral_nonneg fun t => abs_nonneg _)
      (fun M => integral_abs_rhoN_sub (memLp_cont (continuous_truncC M Φ)) hΦ.1) h
  have hbound : ∀ M, ∫ t, (u M t - √(rhoN Φ t)) ^ 2 ∂μ1 ≤
      2 * ∫ t, |rhoN (truncC M Φ) t - rhoN Φ t| ∂μ1 + 4 * ε M := by
    intro M
    have hρP : ∀ t, 0 ≤ rhoN (truncC M Φ) t := (rho_propsC (hP M)).1
    have iL : Integrable (fun t => |rhoN (truncC M Φ) t - rhoN Φ t|) μ1 :=
      ((integrable_marg (memLp_cont (continuous_truncC M Φ))).const_mul _ |>.sub hint).abs
    have hpt : ∀ t, (u M t - √(rhoN Φ t)) ^ 2 ≤
        2 * |rhoN (truncC M Φ) t - rhoN Φ t| + 4 * ε M := by
      intro t
      have h1 := sq_sqrt_sub_sqrt_le (add_pos_of_nonneg_of_pos (hρP t) (hε M)).le (hρ0 t)
      have h3 : |rhoN (truncC M Φ) t + ε M - rhoN Φ t| ≤
          |rhoN (truncC M Φ) t - rhoN Φ t| + ε M := by
        calc |rhoN (truncC M Φ) t + ε M - rhoN Φ t|
            = |(rhoN (truncC M Φ) t - rhoN Φ t) + ε M| := by ring_nf
          _ ≤ |rhoN (truncC M Φ) t - rhoN Φ t| + |ε M| := abs_add_le _ _
          _ = _ := by rw [abs_of_pos (hε M)]
      have hc := Real.sq_sqrt (hε M).le
      simp only [u]
      nlinarith [sq_nonneg (√(rhoN (truncC M Φ) t + ε M) - √(rhoN Φ t) + √(ε M))]
    calc ∫ t, (u M t - √(rhoN Φ t)) ^ 2 ∂μ1
        ≤ ∫ t, (2 * |rhoN (truncC M Φ) t - rhoN Φ t| + 4 * ε M) ∂μ1 :=
          integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _)
            ((iL.const_mul 2).add (integrable_const _)) (ae_of_all _ hpt)
      _ = _ := by
          rw [integral_add (iL.const_mul 2) (integrable_const _), integral_const_mul,
            integral_const]
          simp
  have hsq : Tendsto (fun M => ∫ t, (u M t - √(rhoN Φ t)) ^ 2 ∂μ1) atTop (𝓝 0) := by
    have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have := (hL1.const_mul 2).add (hε0.const_mul 4)
    simp only [mul_zero, add_zero] at this
    exact squeeze_zero (fun M => integral_nonneg fun t => sq_nonneg _) hbound this
  obtain ⟨g, hg, hgf, hgd⟩ := h1N_closure hu1 hC hfm hsq
  refine ⟨g, hg, ?_, hgd⟩
  filter_upwards [hgf] with t h1
  rw [h1, Real.sq_sqrt (hρ0 t)]

end DFT.Continuum.Line
