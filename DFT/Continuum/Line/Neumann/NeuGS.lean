/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Topology.MetricSpace.Sequences
import DFT.Continuum.Line.Neumann.NeuPot

/-!
# Neumann walls and `H⁻¹` potentials: one-particle ground states

For one particle on `[0, 1]` with Neumann walls and `v ∈ H⁻¹`, the energy
`QH v ψ = ∫ ψ'² + v(ψ²)` has a normalised minimiser on `H¹(0, 1)`.

States are parametrised by `e ∈ H1E = ℝ × L²` through `fnE e = e.1 + ∫₀ᵗ e.2`
(`toE_fnE`, `fnE_toE`). The density of `fnE e` is `dE e = (e.1², 2 (fnE e) e.2)` (`sqE_eq_dE`).

* `mulL P f`: multiplication of `f ∈ L²` by a continuous `P`; `norm_mulL_le`.
* **`tendsto_inner_mulL`**: if `P_k → P` uniformly and `f_k ⇀ g` weakly (bounded), then
  `P_k f_k ⇀ P g`. This is what makes `v(ψ_k²) → v(ψ²)` along a minimising sequence, although
  `v` sees the derivative `2ψψ'` of the density.
* `EH v`, the ground-state energy; **`exists_isGSH`**: every `H⁻¹` potential has a normalised
  ground state.
* **`euler_lagrangeH`**: `∫ ψ'φ' + v(ψφ) = E₀ ∫ ψφ` for all `φ ∈ H¹(0, 1)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

/-! ### Functions represented by `H1E` -/

lemma ae_deriv_prim (f : L2I) : deriv (prim f) =ᵐ[μ1] f := by
  have hd := (intervalIntegrable_of_mu1 (integrable_L2I f)
    ⟨zero_le_one, le_rfl⟩).ae_hasDerivAt_integral
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t h ht
  have := (h (by rw [uIcc01]; exact Ioo_subset_Icc_self ht) 0 (by simp)).deriv
  rw [show prim f = fun x => ∫ s in (0 : ℝ)..x, (f : ℝ → ℝ) s from rfl, this]

/-- The function `t ↦ e.1 + ∫₀ᵗ e.2` represented by `e ∈ H1E`. -/
noncomputable def fnE (e : H1E) (t : ℝ) : ℝ := e.fst + prim e.snd t

lemma deriv_fnE (e : H1E) : deriv (fnE e) = deriv (prim e.snd) := by
  funext t
  change deriv (fun x => e.fst + prim e.snd x) t = _
  rw [deriv_const_add]

lemma h1N_fnE (e : H1E) : H1N (fnE e) := by
  refine ⟨?_, ?_⟩
  · have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => e.fst) 0 1 :=
      (contDiffOn_const (c := e.fst) (s := uIcc 0 1)).absolutelyContinuousOnInterval
    exact hc.add (ac_prim e.snd)
  · rw [deriv_fnE]
    refine (integrable_sq_L2I e.snd).congr ?_
    filter_upwards [ae_deriv_prim e.snd] with t ht
    rw [ht]

lemma dN_fnE (e : H1E) : dN (h1N_fnE e) = e.snd := by
  refine Lp.ext ((dN_ae _).trans ?_)
  rw [deriv_fnE]; exact ae_deriv_prim e.snd

@[simp] lemma toE_fnE (e : H1E) : toE (h1N_fnE e) = e := by
  rw [toE, dN_fnE]
  simp [fnE, prim_zero]
  rfl

lemma fnE_toE {g : ℝ → ℝ} (hg : H1N g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fnE (toE hg) t = g t := (eq_toE hg ht).symm

lemma continuousOn_fnE (e : H1E) : ContinuousOn (fnE e) (Icc 0 1) := (h1N_fnE e).continuousOn

lemma evE_apply (e : H1E) (t : Icc (0 : ℝ) 1) : evE e t = fnE e t := by
  simp only [evE, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousMap.add_apply, ContinuousMap.const_apply, primP_apply, fnE]

lemma ext_evE {e : H1E} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ext (evE e) t = fnE e t := by
  rw [SturmLiouville.ext, projIcc_of_mem _ ht, evE_apply]

/-! ### Multiplication by continuous functions on `L²` -/

lemma abs_ext_le (P : Pot) (t : ℝ) : |ext P t| ≤ ‖P‖ := by
  rw [← Real.norm_eq_abs]; exact P.norm_coe_le_norm _

lemma memLp_mulL (P : Pot) (f : L2I) : MemLp (fun t => ext P t * (f : ℝ → ℝ) t) 2 μ1 := by
  refine (memLp_two_iff_integrable_sq
    ((continuous_ext P).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))).2 ?_
  refine ((integrable_sq_L2I f).const_mul (‖P‖ ^ 2)).mono'
    (((continuous_ext P).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).pow 2)
    (ae_of_all _ fun t => ?_)
  change ‖(ext P t * (f : ℝ → ℝ) t) ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
  exact mul_le_mul_of_nonneg_right
    (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_ext_le P t) 2) (sq_nonneg _)

/-- Multiplication of `f ∈ L²(0, 1)` by a continuous function `P` on `[0, 1]`. -/
noncomputable def mulL (P : Pot) (f : L2I) : L2I := (memLp_mulL P f).toLp _

lemma mulL_ae (P : Pot) (f : L2I) :
    (mulL P f : ℝ → ℝ) =ᵐ[μ1] fun t => ext P t * (f : ℝ → ℝ) t := MemLp.coeFn_toLp _

lemma norm_mulL_le (P : Pot) (f : L2I) : ‖mulL P f‖ ≤ ‖P‖ * ‖f‖ := by
  have h : ‖mulL P f‖ ^ 2 ≤ (‖P‖ * ‖f‖) ^ 2 := by
    rw [norm_sq_L2I, mul_pow, norm_sq_L2I, ← integral_const_mul]
    refine integral_mono_ae ((memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable _)).1
      (Lp.memLp _)) ((integrable_sq_L2I f).const_mul _) ?_
    filter_upwards [mulL_ae P f] with t ht
    rw [ht, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_ext_le P t) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

lemma inner_mulL (P : Pot) (f β : L2I) : inner ℝ (mulL P f) β = inner ℝ f (mulL P β) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL_ae P f, mulL_ae P β] with t h1 h2
  simp only [Real.inner_apply, h1, h2]; ring

lemma mulL_sub_left (P Q : Pot) (f : L2I) : mulL (P - Q) f = mulL P f - mulL Q f := by
  refine Lp.ext ?_
  filter_upwards [mulL_ae (P - Q) f, mulL_ae P f, mulL_ae Q f, Lp.coeFn_sub (mulL P f) (mulL Q f)]
    with t h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3]
  simp only [SturmLiouville.ext, ContinuousMap.sub_apply]; ring

/-- **Weak continuity of multiplication**: `P_k → P` uniformly and `f_k ⇀ g` (bounded) give
`P_k f_k ⇀ P g`. -/
theorem tendsto_inner_mulL {P : ℕ → Pot} {P₀ : Pot} (hP : Tendsto P atTop (𝓝 P₀))
    {f : ℕ → L2I} {g : L2I} {R : ℝ} (hR : ∀ k, ‖f k‖ ≤ R)
    (hw : ∀ h : L2I, Tendsto (fun k => inner ℝ (f k) h) atTop (𝓝 (inner ℝ g h))) (β : L2I) :
    Tendsto (fun k => inner ℝ (mulL (P k) (f k)) β) atTop (𝓝 (inner ℝ (mulL P₀ g) β)) := by
  have e : ∀ k, inner ℝ (mulL (P k) (f k)) β =
      inner ℝ (mulL (P k - P₀) (f k)) β + inner ℝ (f k) (mulL P₀ β) := fun k => by
    rw [mulL_sub_left, inner_sub_left, inner_mulL P₀ (f k)]; ring
  simp only [e]
  rw [show inner ℝ (mulL P₀ g) β = 0 + inner ℝ g (mulL P₀ β) by rw [inner_mulL, zero_add]]
  refine Tendsto.add ?_ (hw _)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  have hd : Tendsto (fun k => ‖P k - P₀‖ * R * ‖β‖) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 hP).mul_const R).mul_const ‖β‖
    simpa using this
  refine squeeze_zero_norm (fun k => ?_) hd
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ((norm_mulL_le _ _).trans ?_) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (hR k) (norm_nonneg _)

/-! ### The density of a state -/

/-- The density `(fnE e)²` as an element of `H1E`: `(e.1², 2 (fnE e) e.2)`. -/
noncomputable def dE (e : H1E) : H1E := WithLp.toLp 2 (e.fst ^ 2, (2 : ℝ) • mulL (evE e) e.snd)

lemma sqE_eq_dE {ψ : ℝ → ℝ} (hψ : H1N ψ) : sqE hψ = dE (toE hψ) := by
  rw [sqE, toE, dE]
  congr 1
  refine Prod.ext (by simp [toE, sq]) ?_
  change dN (hψ.mul hψ) = (2 : ℝ) • mulL (evE (toE hψ)) (dN hψ)
  refine Lp.ext ((dN_ae _).trans ?_)
  filter_upwards [ae_restrict_of_ae (H1N.ae_deriv_mul hψ hψ), ae_restrict_mem measurableSet_Ioo,
    Lp.coeFn_smul (2 : ℝ) (mulL (evE (toE hψ)) (dN hψ)), mulL_ae (evE (toE hψ)) (dN hψ), dN_ae hψ]
    with t h1 htI h2 h3 h4
  have htI' := Ioo_subset_Icc_self htI
  rw [h1 htI', h2, Pi.smul_apply, h3, ext_evE htI', fnE_toE hψ htI', h4, smul_eq_mul]
  ring

/-! ### Weak continuity of the potential energy -/

lemma evE_eq (e : H1E) : evE e = ContinuousMap.const _ e.fst + primP e.snd := rfl

/-- `v(dE e_k) → v(dE e₀)` when `e_k.1 → e₀.1` and `e_k.2 ⇀ e₀.2` (bounded). -/
theorem tendsto_v_dE (v : PotH) {e : ℕ → H1E} {e₀ : H1E}
    (hfst : Tendsto (fun k => (e k).fst) atTop (𝓝 e₀.fst)) {R : ℝ} (hR : ∀ k, ‖(e k).snd‖ ≤ R)
    (hw : ∀ h : L2I, Tendsto (fun k => inner ℝ (e k).snd h) atTop (𝓝 (inner ℝ e₀.snd h))) :
    Tendsto (fun k => v (dE (e k))) atTop (𝓝 (v (dE e₀))) := by
  have hP : Tendsto (fun k => evE (e k)) atTop (𝓝 (evE e₀)) := by
    simp only [evE_eq]
    refine Tendsto.add ?_ (tendsto_primP hR hw)
    exact (ContinuousMap.continuous_const').tendsto _ |>.comp hfst
  set r := (InnerProductSpace.toDual ℝ H1E).symm v
  have e1 : ∀ x : H1E, v (dE x) = r.fst * x.fst ^ 2 +
      2 * inner ℝ (mulL (evE x) x.snd) r.snd := fun x => by
    rw [← InnerProductSpace.toDual_symm_apply, WithLp.prod_inner_apply]
    simp only [dE, WithLp.ofLp_toLp, Real.inner_apply, inner_smul_right, real_inner_comm r.snd]
    rfl
  simp only [e1]
  exact ((hfst.pow 2).const_mul _).add
    ((tendsto_inner_mulL hP hR hw r.snd).const_mul 2)

/-! ### Energy and normalisation on `H1E` -/

/-- `∫ (fnE e)²`. -/
noncomputable def nrmE (e : H1E) : ℝ := ∫ t, fnE e t ^ 2 ∂μ1

/-- The energy `∫ ψ'² + v(ψ²)` of `ψ = fnE e`. -/
noncomputable def QE (v : PotH) (e : H1E) : ℝ := ‖e.snd‖ ^ 2 + v (dE e)

lemma nrmE_nonneg (e : H1E) : 0 ≤ nrmE e := integral_nonneg fun _ => sq_nonneg _

lemma kinM_fnE (e : H1E) : kinM (fnE e) = ‖e.snd‖ ^ 2 := by
  rw [← norm_dN_sq (h1N_fnE e), dN_fnE]

lemma dE_eq_sqE (e : H1E) : dE e = sqE (h1N_fnE e) := by rw [sqE_eq_dE, toE_fnE]

theorem QE_ge (v : PotH) (e : H1E) : ‖e.snd‖ ^ 2 / 2 - cH v * nrmE e ≤ QE v e := by
  have := abs_v_sq_le v (h1N_fnE e)
  rw [kinM_fnE, ← dE_eq_sqE] at this
  rw [QE, nrmE]; linarith [neg_abs_le (v (dE e))]

lemma sq_fst_le (e : H1E) : e.fst ^ 2 ≤ 2 * nrmE e + ‖e.snd‖ ^ 2 := by
  have := sq_le_H1N (h1N_fnE e) one_pos (t := 0) ⟨le_rfl, zero_le_one⟩
  rw [kinM_fnE] at this
  simpa [fnE, prim_zero, one_add_one_eq_two, nrmE] using this

lemma exists_nrmE_one : ∃ e : H1E, nrmE e = 1 :=
  ⟨WithLp.toLp 2 (1, 0), by simp [nrmE, fnE, prim]⟩

lemma QE_ge_neg (v : PotH) {e : H1E} (hn : nrmE e = 1) : -cH v ≤ QE v e := by
  have := QE_ge v e
  rw [hn, mul_one] at this
  linarith [sq_nonneg ‖e.snd‖]

/-- The ground-state energy of `-d²/dt² + v` with Neumann walls. -/
noncomputable def EH (v : PotH) : ℝ := sInf {x | ∃ e : H1E, nrmE e = 1 ∧ QE v e = x}

lemma EH_le (v : PotH) {e : H1E} (hn : nrmE e = 1) : EH v ≤ QE v e :=
  csInf_le ⟨-cH v, fun _ ⟨_, he, hx⟩ => hx ▸ QE_ge_neg v he⟩ ⟨e, hn, rfl⟩

/-- Uniform convergence of `evE` makes the normalisation converge. -/
lemma tendsto_nrmE {e : ℕ → H1E} {e₀ : H1E} (hP : Tendsto (fun k => evE (e k)) atTop (𝓝 (evE e₀)))
    {B : ℝ} (hB : ∀ k, ‖evE (e k)‖ ≤ B) : Tendsto (fun k => nrmE (e k)) atTop (𝓝 (nrmE e₀)) := by
  have hc : ∀ x : H1E, nrmE x = ∫ t, ext (evE x) t ^ 2 ∂μ1 := fun x =>
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [ext_evE (Ioo_subset_Icc_self ht)]
  simp only [hc]
  refine tendsto_integral_of_dominated_convergence (fun _ => B ^ 2)
    (fun k => ((continuous_ext _).pow 2).aestronglyMeasurable) (integrable_const _)
    (fun k => ae_of_all _ fun t => ?_) (ae_of_all _ fun t => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_ext_le _ t).trans (hB k)) 2
  · have := ((ContinuousMap.evalCLM ℝ (projIcc (0 : ℝ) 1 zero_le_one t)).continuous.tendsto _).comp hP
    exact this.pow 2

/-- **The energy has a normalised minimiser on `H¹(0, 1)`.** -/
theorem exists_minE (v : PotH) : ∃ e : H1E, nrmE e = 1 ∧ QE v e = EH v := by
  set S := {x | ∃ e : H1E, nrmE e = 1 ∧ QE v e = x}
  have hne : S.Nonempty := by obtain ⟨e, he⟩ := exists_nrmE_one; exact ⟨_, e, he, rfl⟩
  have hseq : ∀ k : ℕ, ∃ e : H1E, nrmE e = 1 ∧ QE v e < EH v + 1 / ((k : ℝ) + 1) := fun k => by
    obtain ⟨_, ⟨e, he, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt hne (lt_add_of_pos_right (EH v) (by positivity : (0 : ℝ) < 1 / (k + 1)))
    exact ⟨e, he, hlt⟩
  choose e hn hQ using hseq
  set R := √(2 * (EH v + 1 + cH v))
  have hR : ∀ k, ‖(e k).snd‖ ≤ R := fun k => by
    have h1 := QE_ge v (e k)
    rw [hn k, mul_one] at h1
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h3 : ‖(e k).snd‖ ^ 2 ≤ 2 * (EH v + 1 + cH v) := by linarith [hQ k]
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hF : ∀ k, |(e k).fst| ≤ √(2 + R ^ 2) := fun k => by
    refine Real.abs_le_sqrt ?_
    have := sq_fst_le (e k)
    rw [hn k] at this
    nlinarith [hR k, norm_nonneg (e k).snd]
  -- Bolzano–Weierstrass for the constants, Banach–Alaoglu for the derivatives
  obtain ⟨c, -, φ₁, hφ₁, hc⟩ := tendsto_subseq_of_bounded (x := fun k => (e k).fst)
    (Metric.isBounded_Icc (-√(2 + R ^ 2)) √(2 + R ^ 2)) fun k => abs_le.1 (hF k)
  obtain ⟨g, φ₂, hφ₂, hw⟩ := exists_weak_subseq (f := fun k => (e (φ₁ k)).snd) fun k => hR _
  set φ := φ₁ ∘ φ₂
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  set e₀ : H1E := WithLp.toLp 2 (c, g)
  have hfst : Tendsto (fun k => (e (φ k)).fst) atTop (𝓝 e₀.fst) := hc.comp hφ₂.tendsto_atTop
  have hP : Tendsto (fun k => evE (e (φ k))) atTop (𝓝 (evE e₀)) := by
    simp only [evE_eq]
    exact ((ContinuousMap.continuous_const').tendsto _ |>.comp hfst).add
      (tendsto_primP (fun k => hR _) hw)
  have hB : ∀ k, ‖evE (e (φ k))‖ ≤ √(2 + R ^ 2) + R := fun k => by
    rw [evE_eq]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2 fun t => ?_
      rw [ContinuousMap.const_apply, Real.norm_eq_abs]; exact hF _
    · refine (ContinuousMap.norm_le _ ((norm_nonneg _).trans (hR (φ k)))).2 fun t => ?_
      rw [primP_apply, Real.norm_eq_abs]; exact (abs_prim_le _ t.2).trans (hR _)
  have hn₀ : nrmE e₀ = 1 := by
    have := tendsto_nrmE hP hB
    simp only [hn] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hQlim : Tendsto (fun k => QE v (e (φ k))) atTop (𝓝 (EH v)) := by
    have hz : Tendsto (fun k : ℕ => EH v + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 (EH v)) := by
      have := (tendsto_const_nhds (x := EH v)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      rw [add_zero] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun k => EH_le v (hn _)) fun k => (hQ _).le
  have hvlim := tendsto_v_dE v (e := fun k => e (φ k)) hfst (fun k => hR _) hw
  set L := EH v - v (dE e₀)
  have hkin : Tendsto (fun k => ‖(e (φ k)).snd‖ ^ 2) atTop (𝓝 L) := by
    refine (hQlim.sub hvlim).congr fun k => ?_
    simp only [QE]; ring
  have hL0 : 0 ≤ L := ge_of_tendsto' hkin fun _ => sq_nonneg _
  have hnorm : Tendsto (fun k => ‖(e (φ k)).snd‖) atTop (𝓝 √L) := by
    refine ((Real.continuous_sqrt.tendsto _).comp hkin).congr fun k => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  have hgg : ‖g‖ ^ 2 ≤ √L * ‖g‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact le_of_tendsto_of_tendsto' (hw g) (hnorm.mul_const ‖g‖)
      fun k => real_inner_le_norm _ _
  have hgL : ‖g‖ ^ 2 ≤ L := by
    have : ‖g‖ ≤ √L := by
      rcases (norm_nonneg g).eq_or_lt with h | h
      · rw [← h]; exact Real.sqrt_nonneg _
      · nlinarith
    calc ‖g‖ ^ 2 ≤ √L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = L := Real.sq_sqrt hL0
  refine ⟨e₀, hn₀, le_antisymm ?_ (EH_le v hn₀)⟩
  change ‖g‖ ^ 2 + v (dE e₀) ≤ EH v
  linarith

/-! ### Polarisation -/

lemma mulL_poly (P Q : Pot) (f g : L2I) (s : ℝ) :
    mulL (P + s • Q) (f + s • g) = mulL P f + s • (mulL P g + mulL Q f) + s ^ 2 • mulL Q g := by
  refine Lp.ext ?_
  filter_upwards [mulL_ae (P + s • Q) (f + s • g), mulL_ae P f, mulL_ae P g, mulL_ae Q f,
    mulL_ae Q g, Lp.coeFn_add f (s • g), Lp.coeFn_smul s g,
    Lp.coeFn_add (mulL P f + s • (mulL P g + mulL Q f)) (s ^ 2 • mulL Q g),
    Lp.coeFn_add (mulL P f) (s • (mulL P g + mulL Q f)),
    Lp.coeFn_smul s (mulL P g + mulL Q f), Lp.coeFn_add (mulL P g) (mulL Q f),
    Lp.coeFn_smul (s ^ 2) (mulL Q g)] with t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [h1, h6, h7, h8, h9, h10, h11, h12, h2, h3, h4, h5]
  simp only [SturmLiouville.ext, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- The overlap density `ψ φ` of `ψ = fnE e`, `φ = fnE h`, as an element of `H1E`. -/
noncomputable def dE2 (e h : H1E) : H1E :=
  WithLp.toLp 2 (e.fst * h.fst, mulL (evE e) h.snd + mulL (evE h) e.snd)

lemma dE_add (e h : H1E) (s : ℝ) :
    dE (e + s • h) = dE e + (2 * s) • dE2 e h + s ^ 2 • dE h := by
  have hm := mulL_poly (evE e) (evE h) e.snd h.snd s
  rw [← map_smul, ← map_add] at hm
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · simp only [dE, dE2, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_toLp, Prod.fst_add,
      Prod.smul_fst, smul_eq_mul, WithLp.add_fst, WithLp.smul_fst]
    ring
  · simp only [dE, dE2, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_toLp, Prod.snd_add,
      Prod.smul_snd, WithLp.add_snd, WithLp.smul_snd, hm]
    module

lemma mulL_smul_smul (P : Pot) (f : L2I) (c : ℝ) : mulL (c • P) (c • f) = c ^ 2 • mulL P f := by
  have := mulL_poly 0 P 0 f c
  simp only [zero_add] at this
  rw [this]
  have z1 : mulL 0 0 = 0 := Lp.ext <| by
    filter_upwards [mulL_ae 0 0, Lp.coeFn_zero ℝ 2 μ1] with t h1 h2
    rw [h1, h2]; simp
  have z2 : mulL 0 f = 0 := Lp.ext <| by
    filter_upwards [mulL_ae 0 f, Lp.coeFn_zero ℝ 2 μ1] with t h1 h2
    rw [h1, h2]; simp [SturmLiouville.ext]
  have z3 : mulL P 0 = 0 := Lp.ext <| by
    filter_upwards [mulL_ae P 0, Lp.coeFn_zero ℝ 2 μ1] with t h1 h2
    rw [h1, h2]; simp
  rw [z1, z2, z3]; simp

lemma dE_smul (e : H1E) (c : ℝ) : dE (c • e) = c ^ 2 • dE e := by
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · simp only [dE, WithLp.ofLp_smul, WithLp.ofLp_toLp, Prod.smul_fst, smul_eq_mul,
      WithLp.smul_fst]
    ring
  · simp only [dE, WithLp.ofLp_smul, WithLp.ofLp_toLp, Prod.smul_snd, WithLp.smul_snd, map_smul,
      mulL_smul_smul, smul_smul]
    rw [mul_comm]

lemma QE_smul (v : PotH) (e : H1E) (c : ℝ) : QE v (c • e) = c ^ 2 * QE v e := by
  rw [QE, QE, dE_smul, map_smul, smul_eq_mul, WithLp.smul_snd, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

lemma nrmE_smul (e : H1E) (c : ℝ) : nrmE (c • e) = c ^ 2 * nrmE e := by
  rw [nrmE, nrmE, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [fnE, WithLp.smul_fst, WithLp.smul_snd, prim_smul _ _ (Ioo_subset_Icc_self ht),
    smul_eq_mul]
  ring

lemma fnE_add_smul (e h : H1E) (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fnE (e + s • h) t = fnE e t + s * fnE h t := by
  simp only [fnE, WithLp.add_fst, WithLp.smul_fst, WithLp.add_snd, WithLp.smul_snd,
    prim_add _ _ ht, prim_smul _ _ ht, smul_eq_mul]
  ring

lemma integrable_fnE_mul (e h : H1E) : Integrable (fun t => fnE e t * fnE h t) μ1 :=
  (((continuousOn_fnE e).mul (continuousOn_fnE h)).integrableOn_compact isCompact_Icc).mono_set
    Ioo_subset_Icc_self

lemma nrmE_add (e h : H1E) (s : ℝ) :
    nrmE (e + s • h) = nrmE e + 2 * s * ∫ t, fnE e t * fnE h t ∂μ1 + s ^ 2 * nrmE h := by
  have i1 : Integrable (fun t => fnE e t ^ 2) μ1 := (h1N_fnE e).int_sq
  have i2 : Integrable (fun t => 2 * s * (fnE e t * fnE h t)) μ1 :=
    (integrable_fnE_mul e h).const_mul _
  have i3 : Integrable (fun t => s ^ 2 * fnE h t ^ 2) μ1 := (h1N_fnE h).int_sq.const_mul _
  have : nrmE (e + s • h) = ∫ t, (fnE e t ^ 2 + 2 * s * (fnE e t * fnE h t) +
      s ^ 2 * fnE h t ^ 2) ∂μ1 :=
    setIntegral_congr_fun measurableSet_Ioo fun t ht => by
      simp only [fnE_add_smul e h s (Ioo_subset_Icc_self ht)]; ring
  have a1 := integral_add (i1.add i2) i3
  have a2 := integral_add i1 i2
  simp only [Pi.add_apply] at a1 a2
  rw [this, a1, a2, integral_const_mul, integral_const_mul, nrmE, nrmE]

lemma QE_add (v : PotH) (e h : H1E) (s : ℝ) :
    QE v (e + s • h) = QE v e + 2 * s * (inner ℝ e.snd h.snd + v (dE2 e h)) + s ^ 2 * QE v h := by
  rw [QE, QE, QE, dE_add, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    WithLp.add_snd, WithLp.smul_snd, norm_add_sq_real, norm_smul, inner_smul_right,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-! ### Ground states -/

/-- `E₀ ∫ (fnE e)² ≤ QE v e` for all `e`. -/
theorem EH_mul_le (v : PotH) (e : H1E) : EH v * nrmE e ≤ QE v e := by
  have hm := nrmE_nonneg e
  rcases hm.eq_or_lt with h | h
  · rw [← h, mul_zero]
    have := QE_ge v e
    rw [← h, mul_zero] at this
    linarith [sq_nonneg ‖e.snd‖]
  · set c := 1 / √(nrmE e)
    have hc : c ^ 2 = 1 / nrmE e := by rw [div_pow, Real.sq_sqrt hm, one_pow]
    have hn' : nrmE (c • e) = 1 := by rw [nrmE_smul, hc, one_div_mul_cancel h.ne']
    have := EH_le v hn'
    rw [QE_smul, hc, div_mul_eq_mul_div, one_mul, le_div_iff₀ h] at this
    exact this

/-- **Euler–Lagrange on `H1E`**: a normalised minimiser satisfies
`⟨e', h'⟩ + v(ψ_e ψ_h) = E₀ ∫ ψ_e ψ_h` for every `h`. -/
theorem euler_lagrangeE {v : PotH} {e : H1E} (hn : nrmE e = 1) (hmin : QE v e = EH v) (h : H1E) :
    inner ℝ e.snd h.snd + v (dE2 e h) = EH v * ∫ t, fnE e t * fnE h t ∂μ1 := by
  have key := eq_zero_of_quad (a := inner ℝ e.snd h.snd + v (dE2 e h) -
      EH v * ∫ t, fnE e t * fnE h t ∂μ1) (c := QE v h - EH v * nrmE h) fun s => by
    have h1 := EH_mul_le v (e + s • h)
    rw [QE_add, nrmE_add, hn, hmin] at h1
    linarith
  linarith

/-! ### Ground states as functions -/

/-- The energy `∫ ψ'² + v(ψ²)` of `ψ ∈ H¹(0, 1)`. -/
noncomputable def QH (v : PotH) {ψ : ℝ → ℝ} (hψ : H1N ψ) : ℝ := kinM ψ + v (sqE hψ)

/-- `ψ` is a ground state of `-d²/dt² + v` with Neumann walls: a nonzero minimiser of the
Rayleigh quotient on `H¹(0, 1)`. -/
def IsGSH (v : PotH) (ψ : ℝ → ℝ) : Prop :=
  ∃ hψ : H1N ψ, 0 < ∫ t, ψ t ^ 2 ∂μ1 ∧
    ∀ φ (hφ : H1N φ), QH v hψ * ∫ t, φ t ^ 2 ∂μ1 ≤ QH v hφ * ∫ t, ψ t ^ 2 ∂μ1

/-- `ρ ∈ C([0, 1])` is the density of a normalised Neumann ground state of an `H⁻¹` potential. -/
def VRepH (ρ : Pot) : Prop :=
  ∃ v ψ, IsGSH v ψ ∧ ∫ t, ψ t ^ 2 ∂μ1 = 1 ∧ ∀ t : Icc (0 : ℝ) 1, ρ t = ψ t ^ 2

lemma QH_eq {v : PotH} {ψ : ℝ → ℝ} (hψ : H1N ψ) : QH v hψ = QE v (toE hψ) := by
  rw [QH, QE, ← sqE_eq_dE, ← norm_dN_sq hψ]; rfl

lemma nrm_eq {ψ : ℝ → ℝ} (hψ : H1N ψ) : ∫ t, ψ t ^ 2 ∂μ1 = nrmE (toE hψ) :=
  setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    rw [fnE_toE hψ (Ioo_subset_Icc_self ht)]

lemma EH_mul_le_QH (v : PotH) {φ : ℝ → ℝ} (hφ : H1N φ) :
    EH v * ∫ t, φ t ^ 2 ∂μ1 ≤ QH v hφ := by
  rw [QH_eq, nrm_eq]; exact EH_mul_le v _

/-- **Every `H⁻¹` potential has a normalised Neumann ground state**, with energy `EH v`. -/
theorem exists_isGSH (v : PotH) :
    ∃ ψ : ℝ → ℝ, ∃ hψ : H1N ψ, IsGSH v ψ ∧ ∫ t, ψ t ^ 2 ∂μ1 = 1 ∧ QH v hψ = EH v := by
  obtain ⟨e, hn, hmin⟩ := exists_minE v
  have hψ := h1N_fnE e
  have hn' : ∫ t, fnE e t ^ 2 ∂μ1 = 1 := hn
  have hQ : QH v hψ = EH v := by rw [QH_eq, toE_fnE, hmin]
  refine ⟨fnE e, hψ, ⟨hψ, by rw [hn']; exact one_pos, fun φ hφ => ?_⟩, hn', hQ⟩
  rw [hn', mul_one, hQ]
  exact EH_mul_le_QH v hφ

/-- A normalised ground state has energy `EH v`. -/
lemma QH_of_isGSH {v : PotH} {ψ : ℝ → ℝ} (hgs : IsGSH v ψ) (hn : ∫ t, ψ t ^ 2 ∂μ1 = 1) :
    QH v hgs.1 = EH v := by
  obtain ⟨φ, hφ, -, hφn, hφQ⟩ := exists_isGSH v
  obtain ⟨hψ, -, hmin⟩ := hgs
  have h1 := hmin φ hφ
  rw [hn, hφn, mul_one, mul_one, hφQ] at h1
  have h2 := EH_mul_le_QH v hψ
  rw [hn, mul_one] at h2
  exact le_antisymm h1 h2

/-- `toE (ψ φ)` is the overlap density `dE2 (toE ψ) (toE φ)`. -/
lemma toE_mul_eq_dE2 {ψ φ : ℝ → ℝ} (hψ : H1N ψ) (hφ : H1N φ) :
    toE (hψ.mul hφ) = dE2 (toE hψ) (toE hφ) := by
  rw [toE, dE2]
  congr 1
  refine Prod.ext (by simp [toE]) ?_
  change dN (hψ.mul hφ) = mulL (evE (toE hψ)) (dN hφ) + mulL (evE (toE hφ)) (dN hψ)
  refine Lp.ext ((dN_ae _).trans ?_)
  filter_upwards [ae_restrict_of_ae (H1N.ae_deriv_mul hψ hφ), ae_restrict_mem measurableSet_Ioo,
    Lp.coeFn_add (mulL (evE (toE hψ)) (dN hφ)) (mulL (evE (toE hφ)) (dN hψ)),
    mulL_ae (evE (toE hψ)) (dN hφ), mulL_ae (evE (toE hφ)) (dN hψ), dN_ae hψ, dN_ae hφ]
    with t h1 htI h2 h3 h4 h5 h6
  have htI' := Ioo_subset_Icc_self htI
  rw [h1 htI', h2, Pi.add_apply, h3, h4, ext_evE htI', ext_evE htI', fnE_toE hψ htI',
    fnE_toE hφ htI', h5, h6]
  ring

lemma inner_dN {ψ φ : ℝ → ℝ} (hψ : H1N ψ) (hφ : H1N φ) :
    inner ℝ (dN hψ) (dN hφ) = ∫ t, deriv ψ t * deriv φ t ∂μ1 := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [dN_ae hψ, dN_ae hφ] with t h1 h2
  simp only [Real.inner_apply, h1, h2]

/-- **The Euler–Lagrange equation**: a normalised Neumann ground state solves
`-ψ'' + vψ = E₀ψ` weakly: `∫ ψ'φ' + v(ψφ) = E₀ ∫ ψφ` for every `φ ∈ H¹(0, 1)`. -/
theorem euler_lagrangeH {v : PotH} {ψ : ℝ → ℝ} (hgs : IsGSH v ψ) (hn : ∫ t, ψ t ^ 2 ∂μ1 = 1)
    {φ : ℝ → ℝ} (hφ : H1N φ) :
    ∫ t, deriv ψ t * deriv φ t ∂μ1 + v (toE (hgs.1.mul hφ)) = EH v * ∫ t, ψ t * φ t ∂μ1 := by
  have hψ := hgs.1
  have hQ := QH_of_isGSH hgs hn
  rw [QH_eq] at hQ
  have := euler_lagrangeE (by rw [← nrm_eq]; exact hn) hQ (toE hφ)
  rw [← toE_mul_eq_dE2, show (toE hψ).snd = dN hψ from rfl, show (toE hφ).snd = dN hφ from rfl,
    inner_dN] at this
  rw [this]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    rw [fnE_toE hψ (Ioo_subset_Icc_self ht), fnE_toE hφ (Ioo_subset_Icc_self ht)]

end DFT.Continuum.Line
