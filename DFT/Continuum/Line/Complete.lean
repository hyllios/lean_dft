/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Closure

/-!
# Sine truncations of `H¹₀` states

The product sines `s_m` form a Hilbert basis of `L²` of the cube (`bN`). For an `H¹₀` state `Φ`
the truncations `P_M = Σ_{m ∈ [0, M)ᴺ} ⟨s_m, Φ⟩ s_m`
* converge to `Φ` in `L²` (`tendsto_trunc`),
* are `C²` states of the same exchange symmetry (`trunc_mem`), and
* have kinetic energy at most the weak kinetic energy of `Φ` (`kin_trunc_le`).

The last point is Bessel's inequality for the orthonormal functions
`c^k_m = √2 cos(π(m_k+1)x_k) Π_{j≠k} s_{m_j}(x_j)`: since `∂ₖ c^k_m = -π(m_k+1) s_m`, the weak
derivative gives `⟨c^k_m, ∂ₖΦ⟩ = π(m_k+1) ⟨s_m, Φ⟩`. Testing against `c^k_m`, which does not
vanish on the walls `x_k ∈ {0, 1}`, is where the zero boundary values of `Φ` enter.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-! ### An identity for orthonormal projections -/

lemma orthonormal_norm_sub_sq {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : ι → E} (hv : Orthonormal ℝ v) (x : E) (s : Finset ι) :
    ‖x - ∑ i ∈ s, inner ℝ (v i) x • v i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i ∈ s, inner ℝ (v i) x ^ 2 := by
  have h1 : inner ℝ x (∑ i ∈ s, inner ℝ (v i) x • v i) = ∑ i ∈ s, inner ℝ (v i) x ^ 2 := by
    simp only [inner_sum, inner_smul_right, real_inner_comm x, sq]
  have h2 : ‖∑ i ∈ s, inner ℝ (v i) x • v i‖ ^ 2 = ∑ i ∈ s, inner ℝ (v i) x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hv.inner_sum]
    simp [sq]
  rw [norm_sub_sq_real, h1, h2]; ring

/-! ### The Hilbert space and the sine basis -/

/-- `L²` of the cube. -/
noncomputable abbrev HN (n : ℕ) := Lp ℝ 2 (μN n)

/-- The product sine as an element of `L²`. -/
noncomputable def eN (m : Fin (n + 1) → ℕ) : HN n := (memLp_cont (continuous_smd m)).toLp

lemma inner_eN (m : Fin (n + 1) → ℕ) (F : HN n) :
    inner ℝ (eN m) F = ∫ x, smd m x * F x ∂μN n := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_cont (continuous_smd (d := n + 1) m))] with x hx
  simp only [eN] at *
  rw [hx]; simp [mul_comm]

lemma inner_toLp_left {f : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (F : HN n) :
    inner ℝ (hf.toLp f) F = ∫ x, f x * F x ∂μN n := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx]; simp [mul_comm]

lemma coeFn_eN (m : Fin (n + 1) → ℕ) : (eN m : Cfg n → ℝ) =ᵐ[μN n] smd m :=
  MemLp.coeFn_toLp _

lemma eN_orthonormal : Orthonormal ℝ (eN (n := n)) := by
  rw [orthonormal_iff_ite]
  intro m m'
  rw [inner_eN, show ∫ x, smd m x * (eN m' : Cfg n → ℝ) x ∂μN n = ∫ x, smd m x * smd m' x ∂μN n
    from integral_congr_ae (by filter_upwards [coeFn_eN m'] with x hx; rw [hx]),
    muN_eq, smd_orthonormal]

lemma norm_sq_toLp {f : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μN n := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx, sq]

/-- An element orthogonal to every sine is orthogonal to every continuous function. -/
lemma integral_cont_mul_eq_zero {F : HN n} (hF : ∀ m, inner ℝ (eN m) F = 0) {ψ : Cfg n → ℝ}
    (hψ : Continuous ψ) : ∫ x, ψ x * F x ∂μN n = 0 := by
  set x0 : HN n := (memLp_cont hψ).toLp
  set a : (Fin (n + 1) → ℕ) → ℝ := fun m => inner ℝ (eN m) x0
  have ea : ∀ m, a m = cf m ψ := fun m => by
    simp only [a, inner_eN, cf, ← muN_eq]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_cont hψ)] with x hx
    simp only [x0] at *; rw [hx]
  have hpar : HasSum (fun m => a m ^ 2) (‖x0‖ ^ 2) := by
    rw [norm_sq_toLp]
    have h := hasSum_sq_cube (d := n + 1) hψ
    rw [← muN_eq] at h
    simp only [ea]
    convert h using 1
    exact integral_congr_ae (ae_of_all _ fun x => sq _)
  have hS : Tendsto (fun s : Finset _ => ∑ m ∈ s, a m • eN m) atTop (𝓝 x0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have key : ∀ s : Finset _, ‖∑ m ∈ s, a m • eN m - x0‖ =
        √(‖x0‖ ^ 2 - ∑ m ∈ s, a m ^ 2) := fun s => by
      rw [← orthonormal_norm_sub_sq eN_orthonormal x0 s, norm_sub_rev, Real.sqrt_sq (norm_nonneg _)]
    simp only [key]
    have h := (tendsto_const_nhds (x := ‖x0‖ ^ 2)).sub hpar
    rw [sub_self] at h
    simpa using h.sqrt
  have hlim := Filter.Tendsto.inner (𝕜 := ℝ) hS (tendsto_const_nhds (x := F))
  have hz : ∀ s : Finset _, inner ℝ (∑ m ∈ s, a m • eN m) F = 0 := fun s => by
    simp [sum_inner, inner_smul_left, hF]
  simp only [hz] at hlim
  have h0 := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [inner_toLp_left] at h0
  exact h0.symm

/-- **Completeness of the product sines in `L²` of the cube.** -/
lemma eN_complete (F : HN n) (hF : ∀ m, inner ℝ (eN m) F = 0) : F = 0 := by
  have hint : IntegrableOn (fun x => (F : Cfg n → ℝ) x) (Cube n) volume :=
    (Lp.memLp F).integrable one_le_two
  have h := isOpen_cube.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    hint.locallyIntegrableOn (fun g hg _ hsupp => by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Cube n) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h), zero_smul]]
      simpa [smul_eq_mul] using integral_cont_mul_eq_zero hF hg.continuous)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [(ae_restrict_iff' measurableSet_cube).2 h] with x hx
  exact hx

lemma eN_span_orthogonal : (Submodule.span ℝ (Set.range (eN (n := n))))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  exact eN_complete F fun m =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self m)) hF

/-- **The product-sine Hilbert basis** of `L²` of the cube. -/
noncomputable def bN : HilbertBasis (Fin (n + 1) → ℕ) ℝ (HN n) :=
  HilbertBasis.mkOfOrthogonalEqBot eN_orthonormal eN_span_orthogonal

lemma bN_apply (m : Fin (n + 1) → ℕ) : bN m = eN m := by
  rw [bN, HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma inner_eN_toLp {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (m : Fin (n + 1) → ℕ) :
    inner ℝ (eN m) (hΦ.toLp Φ) = cN m Φ := by
  rw [inner_eN, cN_eq]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hΦ] with x hx
  rw [hx]

/-- **Parseval** for `L²` functions on the cube. -/
theorem parsevalW {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) :
    HasSum (fun m => cN m Φ ^ 2) (∫ x, Φ x ^ 2 ∂μN n) := by
  have h := (bN (n := n)).hasSum_inner_mul_inner (hΦ.toLp Φ) (hΦ.toLp Φ)
  simp only [bN_apply, real_inner_comm (eN _) (hΦ.toLp Φ), inner_eN_toLp hΦ,
    real_inner_self_eq_norm_sq, norm_sq_toLp hΦ] at h
  simpa [sq] using h

/-! ### Truncations -/

/-- The box `[0, M)ᴺ` of multi-indices. -/
def boxI (n M : ℕ) : Finset (Fin (n + 1) → ℕ) := Fintype.piFinset fun _ => Finset.range M

lemma mem_boxI {M : ℕ} {m : Fin (n + 1) → ℕ} : m ∈ boxI n M ↔ ∀ j, m j < M := by
  simp [boxI, Fintype.mem_piFinset]

lemma tendsto_boxI : Tendsto (boxI n) atTop atTop :=
  tendsto_atTop_finset_of_monotone
    (fun a b hab m hm => mem_boxI.2 fun j => (mem_boxI.1 hm j).trans_le hab)
    (fun m => ⟨Finset.univ.sup m + 1, mem_boxI.2 fun j => by
      have := Finset.le_sup (f := m) (Finset.mem_univ j); omega⟩)

/-- The truncated sine series. -/
noncomputable def trunc (M : ℕ) (Φ : Cfg n → ℝ) (x : Cfg n) : ℝ :=
  ∑ m ∈ boxI n M, cN m Φ * smd m x

lemma continuous_trunc (M : ℕ) (Φ : Cfg n → ℝ) : Continuous (trunc M Φ) :=
  continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_smd m)

lemma coeFn_sum_eN (s : Finset (Fin (n + 1) → ℕ)) (c : (Fin (n + 1) → ℕ) → ℝ) :
    ((∑ m ∈ s, c m • eN m : HN n) : Cfg n → ℝ) =ᵐ[μN n] fun x => ∑ m ∈ s, c m * smd m x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 (μN n)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • eN a) (∑ m ∈ s, c m • eN m),
      Lp.coeFn_smul (c a) (eN a), coeFn_eN a, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Finset.sum_insert ha, smul_eq_mul]

/-- `∫ (Φ - P_M)² = ∫ Φ² - Σ_{m ∈ box} ⟨s_m, Φ⟩²`. -/
lemma integral_sub_trunc_sq {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (M : ℕ) :
    ∫ x, (Φ x - trunc M Φ x) ^ 2 ∂μN n = ∫ x, Φ x ^ 2 ∂μN n - ∑ m ∈ boxI n M, cN m Φ ^ 2 := by
  have h := orthonormal_norm_sub_sq eN_orthonormal (hΦ.toLp Φ) (boxI n M)
  simp only [inner_eN_toLp hΦ, norm_sq_toLp hΦ] at h
  rw [← h, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hΦ.toLp Φ) (∑ m ∈ boxI n M, cN m Φ • eN m),
    MemLp.coeFn_toLp hΦ, coeFn_sum_eN (boxI n M) (fun m => cN m Φ)] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  simp [trunc, sq]

/-- **The truncations converge in `L²`.** -/
theorem tendsto_trunc {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) :
    Tendsto (fun M => ∫ x, (Φ x - trunc M Φ x) ^ 2 ∂μN n) atTop (𝓝 0) := by
  simp only [integral_sub_trunc_sq hΦ]
  have h := (parsevalW hΦ).comp tendsto_boxI
  have := (tendsto_const_nhds (x := ∫ x, Φ x ^ 2 ∂μN n)).sub h
  rwa [sub_self] at this

/-! ### The truncations are `C²` states -/

lemma pmI_pmI (σ ρ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) :
    pmI σ (pmI ρ m) = pmI (ρ * σ) m := by
  funext i; simp [pmI]

lemma pmI_one (m : Fin (n + 1) → ℕ) : pmI 1 m = m := rfl

lemma pmI_mem_boxI {M : ℕ} (σ : Equiv.Perm (Fin (n + 1))) {m : Fin (n + 1) → ℕ} :
    pmI σ m ∈ boxI n M ↔ m ∈ boxI n M := by
  simp only [mem_boxI, pmI]
  exact ⟨fun h j => by simpa using h (σ⁻¹ j), fun h j => h (σ j)⟩

lemma cN_pmW {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) (σ : Equiv.Perm (Fin (n + 1)))
    (m : Fin (n + 1) → ℕ) : cN (pmI σ m) Φ = ch τ σ * cN m Φ := by
  rw [cN_eq, cN_eq, ← integral_pm σ, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hΦ.2.2 σ] with x hx
  simp only [smd_pm, hx]; ring

lemma smd_pm' (σ : Equiv.Perm (Fin (n + 1))) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    smd m (pm σ x) = smd (pmI σ⁻¹ m) x := by
  have h := smd_pm σ (pmI σ⁻¹ m) x
  rwa [pmI_pmI, inv_mul_cancel, pmI_one] at h

/-- **The truncations are `C²` states** of the same exchange symmetry. -/
theorem trunc_mem {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) (M : ℕ) : trunc M Φ ∈ Dom τ n := by
  refine ⟨ContDiff.sum fun m _ => contDiff_const.mul (contDiff_smd m), fun σ x => ?_,
    fun x k hk => ?_⟩
  · simp only [trunc, smd_pm', Finset.mul_sum]
    refine Finset.sum_nbij' (pmI σ⁻¹) (pmI σ) (fun m hm => (pmI_mem_boxI σ⁻¹).2 hm)
      (fun m hm => (pmI_mem_boxI σ).2 hm) (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
    · rw [pmI_pmI, inv_mul_cancel, pmI_one]
    · rw [pmI_pmI, mul_inv_cancel, pmI_one]
    · have h := cN_pmW hΦ σ (pmI σ⁻¹ m)
      rw [pmI_pmI, inv_mul_cancel, pmI_one] at h
      rw [h]; ring
  · simp only [trunc, smd_face _ x k hk, mul_zero, Finset.sum_const_zero]

lemma cN_trunc (Φ : Cfg n → ℝ) (M : ℕ) (m' : Fin (n + 1) → ℕ) :
    cN m' (trunc M Φ) = if m' ∈ boxI n M then cN m' Φ else 0 := by
  rw [cN_eq]
  have e : (fun x => smd m' x * trunc M Φ x) =
      fun x => ∑ m ∈ boxI n M, cN m Φ * (smd m' x * smd m x) := by
    funext x; simp only [trunc, Finset.mul_sum]; congr 1; funext m; ring
  rw [e, integral_finsetSum (f := fun m x => cN m Φ * (smd m' x * smd m x)) _
    fun m _ => integrableN (continuous_const.mul
    ((continuous_smd m').mul (continuous_smd m)))]
  simp only [integral_const_mul, muN_eq, smd_orthonormal, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- The kinetic energy of a truncation, in coefficients. -/
lemma kin_trunc {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) (M : ℕ) :
    ∫ x, ∑ k, dk k (trunc M Φ) x * dk k (trunc M Φ) x ∂μN n =
      ∑ m ∈ boxI n M, π ^ 2 * ksq m * cN m Φ ^ 2 := by
  have hF : (fun m => π ^ 2 * (ksq m : ℝ) * cN m (trunc M Φ) ^ 2) =
      fun m => if m ∈ boxI n M then π ^ 2 * (ksq m : ℝ) * cN m Φ ^ 2 else 0 := by
    funext m; rw [cN_trunc]; split_ifs <;> simp
  have h : HasSum (fun m => if m ∈ boxI n M then π ^ 2 * (ksq m : ℝ) * cN m Φ ^ 2 else 0)
      (∑ m ∈ boxI n M, if m ∈ boxI n M then π ^ 2 * (ksq m : ℝ) * cN m Φ ^ 2 else 0) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by simp [hm]
  rw [Finset.sum_ite_mem, Finset.inter_self] at h
  exact (hasSum_kin (trunc_mem hΦ M)).unique (by rw [hF]; exact h)

/-! ### Bessel's inequality for the weak derivatives -/

/-- The factors of `c^k_m`. -/
noncomputable def cfac (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (j : Fin (n + 1)) : ℝ → ℝ :=
  if j = k then cs (m k) else sn (m j + 1)

/-- `c^k_m = √2 cos(π(m_k+1)x_k) Π_{j≠k} s_{m_j}(x_j)`. -/
noncomputable def cmd (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : Cfg n) : ℝ :=
  ∏ j, cfac k m j (x j)

lemma continuous_cfac (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    Continuous (cfac k m j) := by
  unfold cfac; split_ifs
  · exact continuous_cs _
  · exact continuous_sn _

lemma contDiff_cfac (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    ContDiff ℝ 1 (cfac k m j) := by
  unfold cfac cs sn; split_ifs <;> fun_prop

lemma contDiff_cmd (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) : ContDiff ℝ 1 (cmd k m) :=
  contDiff_prod fun j _ => (contDiff_cfac k m j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).contDiff

lemma cmd_orthonormal (k : Fin (n + 1)) (m m' : Fin (n + 1) → ℕ) :
    ∫ x, cmd k m x * cmd k m' x ∂μN n = if m = m' then 1 else 0 := by
  have e : (fun x => cmd k m x * cmd k m' x) =
      fun x => ∏ j, (cfac k m j (x j) * cfac k m' j (x j)) := by
    funext x; simp only [cmd, Finset.prod_mul_distrib]
  rw [e, muN_eq, integral_fintype_prod_eq_prod (f := fun j t => cfac k m j t * cfac k m' j t)]
  have hj : ∀ j, ∫ t, cfac k m j t * cfac k m' j t ∂μ1 = if m j = m' j then 1 else 0 := by
    intro j
    by_cases hjk : j = k
    · subst hjk; simp only [cfac, ↓reduceIte, cs_orthonormal]
    · simp only [cfac, hjk, ↓reduceIte, sn_orthonormal (Nat.succ_pos _) (Nat.succ_pos _)]
      exact if_congr (by omega) rfl rfl
  simp only [hj]
  by_cases h : m = m'
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- `∂ₖ c^k_m = -π(m_k+1) s_m`. -/
lemma dk_cmd (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) (x : Cfg n) :
    dk k (cmd k m) x = -(π * (m k + 1)) * smd m x := by
  have h1 := hasDerivAt_slice ((contDiff_cmd k m).differentiable one_ne_zero) x k (x k)
  rw [Function.update_eq_self] at h1
  set R := ∏ j ∈ Finset.univ.erase k, sn (m j + 1) (x j)
  have hslice : (fun s => cmd k m (Function.update x k s)) = fun s => cs (m k) s * R := by
    funext s
    simp only [cmd]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    simp only [cfac, ↓reduceIte, Function.update_self, R]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk := Finset.ne_of_mem_erase hj
    simp [hjk]
  have hcs : HasDerivAt (cs (m k)) (-(π * (m k + 1)) * sn (m k + 1) (x k)) (x k) := by
    have h := (((hasDerivAt_id (x k)).const_mul (π * (m k + 1))).cos).const_mul √2
    refine h.congr_deriv ?_
    simp only [sn, id]; push_cast; ring
  have h2 : HasDerivAt (fun s => cmd k m (Function.update x k s))
      (-(π * (m k + 1)) * sn (m k + 1) (x k) * R) (x k) := by
    rw [hslice]; exact hcs.mul_const R
  rw [h1.unique h2, smd, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  ring

/-- **Bessel for the weak derivative**: `Σ_{m ∈ s} (π(m_k+1) ⟨s_m, Φ⟩)² ≤ ∫ |∂ₖΦ|²`. -/
lemma bessel_dW {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) (k : Fin (n + 1))
    (s : Finset (Fin (n + 1) → ℕ)) :
    ∑ m ∈ s, (π * (m k + 1) * cN m Φ) ^ 2 ≤ ∫ x, dW k Φ x * dW k Φ x ∂μN n := by
  have hW := dW_spec (hΦ.2.1 k)
  set v : (Fin (n + 1) → ℕ) → HN n := fun m => (memLp_cont (contDiff_cmd k m).continuous).toLp
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro m m'
    simp only [v]
    rw [inner_toLp_left, ← cmd_orthonormal k m m']
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_cont (contDiff_cmd k m').continuous)] with x hx
    rw [hx]
  set G : HN n := hW.1.toLp (dW k Φ)
  have hinner : ∀ m, inner ℝ (v m) G = π * (m k + 1) * cN m Φ := fun m => by
    simp only [v, G]
    rw [inner_toLp_left]
    have e : ∫ x, cmd k m x * (hW.1.toLp (dW k Φ) : Cfg n → ℝ) x ∂μN n =
        ∫ x, dW k Φ x * cmd k m x ∂μN n := integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp hW.1] with x hx; rw [hx, mul_comm])
    rw [e, ← neg_neg (∫ x, dW k Φ x * cmd k m x ∂μN n), ← hW.2 _ (contDiff_cmd k m)]
    simp only [dk_cmd]
    rw [cN_eq, ← integral_neg, ← integral_const_mul]
    congr 1; funext x; ring
  have h := hv.sum_inner_products_le (x := G) (s := s)
  simp only [hinner, Real.norm_eq_abs, sq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [norm_sq_toLp]; congr 1; funext x; ring

/-- **The truncations have kinetic energy at most the weak kinetic energy.** -/
theorem kin_trunc_le {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) (M : ℕ) :
    ∫ x, ∑ k, dk k (trunc M Φ) x * dk k (trunc M Φ) x ∂μN n ≤
      ∑ k, ∫ x, dW k Φ x * dW k Φ x ∂μN n := by
  rw [kin_trunc hΦ]
  have e : ∑ m ∈ boxI n M, π ^ 2 * (ksq m : ℝ) * cN m Φ ^ 2 =
      ∑ k, ∑ m ∈ boxI n M, (π * (m k + 1) * cN m Φ) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [ksq]; push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e]
  exact Finset.sum_le_sum fun k _ => bessel_dW hΦ k _

end DFT.Continuum.Line
