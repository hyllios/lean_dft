/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.UniformSpace.Ascoli
import DFT.Continuum.Line.MeasurePotential.Pot

/-!
# Ground states for measure potentials

For one particle on `[0, 1]` with walls and a measure potential `ν ∈ C([0, 1])*`, the energy
`QM ν ψ = ∫ ψ'² + ν(ψ²)` has a normalised minimiser on `H¹₀(0, 1)`.

* `sq_le_H10`: `ψ(t)² ≤ a ∫ ψ² + (∫ ψ'²) / a` for every `a > 0` (so `‖ψ‖_∞² ≤ 2‖ψ‖‖ψ'‖`).
* `QM_ge`: `QM ν ψ ≥ ½ ∫ ψ'² - C_ν ∫ ψ²`: measure potentials are infinitesimally form bounded.
* `QM_smul`: `QM ν (cψ) = c² QM ν ψ`.
* `EM ν`, the ground-state energy; `EM_mul_le`: `E₀ ∫ φ² ≤ QM ν φ` on `H¹₀`.
* **`exists_isGSM`**: every measure potential has a normalised ground state.
* **`euler_lagrange`**: a ground state solves `-ψ'' + νψ = E₀ψ` weakly:
  `∫ ψ'φ' + ν(ψφ) = E₀ ∫ ψφ` for all `φ ∈ H¹₀(0, 1)`.

The proof is the direct method in `L²(0, 1)`, parametrising `ψ = ∫₀ᵗ f` (`Line/Prim`). A
minimising sequence has bounded `‖f‖`, so a subsequence converges weakly (sequential
Banach–Alaoglu, `L²` being separable). The primitives converge pointwise (`t ↦ ∫₀ᵗ f` is a
continuous functional) and are uniformly `½`-Hölder, hence converge uniformly (Arzelà–Ascoli), so
`ν(ψ²)` converges; `‖f‖` is weakly lower semicontinuous.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

/-! ### The sup bound and form boundedness -/

lemma ae_deriv_sq {ψ : ℝ → ℝ} (hψ : H10 ψ) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) 1 →
      deriv (fun t => ψ t * ψ t) s = 2 * ψ s * deriv ψ s := by
  have hd := hψ.1.ae_differentiableAt
  rw [uIcc01] at hd
  filter_upwards [hd] with s hs hsI
  change deriv (ψ * ψ) s = _
  rw [((hs hsI).hasDerivAt.mul (hs hsI).hasDerivAt).deriv]
  ring

/-- **The sup bound**: `ψ(t)² ≤ a ∫ ψ² + (∫ ψ'²) / a` for `ψ ∈ H¹₀(0, 1)` and `a > 0`. -/
theorem sq_le_H10 {ψ : ℝ → ℝ} (hψ : H10 ψ) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ψ t ^ 2 ≤ a * ∫ s, ψ s ^ 2 ∂vol01 + kinM ψ / a := by
  have hac2 : AbsolutelyContinuousOnInterval (fun s => ψ s * ψ s) 0 1 := hψ.1.fun_mul hψ.1
  have hacT : AbsolutelyContinuousOnInterval (fun s => ψ s * ψ s) 0 t := hac2.mono (by
    rw [uIcc01, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  have hFTC : ∫ s in (0 : ℝ)..t, deriv (fun s => ψ s * ψ s) s = ψ t ^ 2 := by
    rw [hacT.integral_deriv_eq_sub, hψ.2.1]; ring
  set g : ℝ → ℝ := fun s => a * ψ s ^ 2 + deriv ψ s ^ 2 / a
  have hsq : IntegrableOn (fun s => ψ s ^ 2) (Ioo (0 : ℝ) 1) :=
    H10.int_sq_of_contOn hψ.continuousOn
  have hg : IntegrableOn g (Ioo (0 : ℝ) 1) :=
    (hsq.const_mul a).add (hψ.2.2.2.div_const a)
  have hgi : ∀ {b : ℝ}, b ∈ Icc (0 : ℝ) 1 → IntervalIntegrable g volume 0 b := fun hb =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.1).2 (hg.mono_set (Ioo_subset_Ioo_right hb.2))
  have hle : ∫ s in (0 : ℝ)..t, deriv (fun s => ψ s * ψ s) s ≤ ∫ s in (0 : ℝ)..t, g s := by
    refine intervalIntegral.integral_mono_ae_restrict ht.1 hacT.intervalIntegrable_deriv (hgi ht) ?_
    filter_upwards [ae_restrict_of_ae (ae_deriv_sq hψ), ae_restrict_mem measurableSet_Icc]
      with s hs hsI
    rw [hs ⟨hsI.1, hsI.2.trans ht.2⟩]
    simp only [g]
    have : 2 * ψ s * deriv ψ s ≤ a * ψ s ^ 2 + deriv ψ s ^ 2 / a := by
      rw [← sub_nonneg]
      have e : a * ψ s ^ 2 + deriv ψ s ^ 2 / a - 2 * ψ s * deriv ψ s =
          (a * ψ s - deriv ψ s) ^ 2 / a := by field_simp; ring
      rw [e]; positivity
    exact this
  have hmono : ∫ s in (0 : ℝ)..t, g s ≤ ∫ s in (0 : ℝ)..1, g s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_of_all _ fun s => by simp only [g, Pi.zero_apply]; positivity)
      (hgi ⟨zero_le_one, le_rfl⟩)
  have htot : ∫ s in (0 : ℝ)..1, g s = a * ∫ s, ψ s ^ 2 ∂vol01 + kinM ψ / a := by
    rw [← integral_vol01, integral_add (hsq.const_mul a) (hψ.2.2.2.div_const a), integral_const_mul,
      integral_div, kinM]
  linarith

lemma norm_sqP_le {ψ : ℝ → ℝ} (hψ : H10 ψ) {a : ℝ} (ha : 0 < a) :
    ‖sqP hψ‖ ≤ a * ∫ s, ψ s ^ 2 ∂vol01 + kinM ψ / a := by
  have hk : 0 ≤ kinM ψ := integral_nonneg fun _ => sq_nonneg _
  have hn : 0 ≤ ∫ s, ψ s ^ 2 ∂vol01 := integral_nonneg fun _ => sq_nonneg _
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  rw [sqP_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_H10 hψ ha t.2

/-- The form-bound constant of a measure potential. -/
noncomputable def cM (ν : PotM) : ℝ := ‖ν‖ * (2 * ‖ν‖ + 1)

lemma cM_nonneg (ν : PotM) : 0 ≤ cM ν := by unfold cM; positivity

/-- **Form boundedness**: `|ν(ψ²)| ≤ ½ ∫ ψ'² + C_ν ∫ ψ²`. -/
theorem abs_nu_sq_le (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) :
    |ν (sqP hψ)| ≤ kinM ψ / 2 + cM ν * ∫ s, ψ s ^ 2 ∂vol01 := by
  have ha : 0 < 2 * ‖ν‖ + 1 := by positivity
  have hk : 0 ≤ kinM ψ := integral_nonneg fun _ => sq_nonneg _
  have h1 := ν.le_opNorm (sqP hψ)
  have h2 := norm_sqP_le hψ ha
  rw [Real.norm_eq_abs] at h1
  have h3 : ‖ν‖ * (kinM ψ / (2 * ‖ν‖ + 1)) ≤ kinM ψ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ ha two_pos]
    nlinarith [norm_nonneg ν]
  calc |ν (sqP hψ)| ≤ ‖ν‖ * ‖sqP hψ‖ := h1
    _ ≤ ‖ν‖ * ((2 * ‖ν‖ + 1) * ∫ s, ψ s ^ 2 ∂vol01 + kinM ψ / (2 * ‖ν‖ + 1)) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg ν)
    _ ≤ kinM ψ / 2 + cM ν * ∫ s, ψ s ^ 2 ∂vol01 := by rw [cM]; nlinarith

theorem QM_ge (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) :
    kinM ψ / 2 - cM ν * ∫ s, ψ s ^ 2 ∂vol01 ≤ QM ν hψ := by
  have := abs_nu_sq_le ν hψ
  rw [QM]; linarith [neg_abs_le (ν (sqP hψ))]

theorem kinM_le_QM (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) :
    kinM ψ ≤ 2 * (QM ν hψ + cM ν * ∫ s, ψ s ^ 2 ∂vol01) := by
  linarith [QM_ge ν hψ]

/-! ### Scaling -/

lemma kinM_smul (c : ℝ) (ψ : ℝ → ℝ) : kinM (fun t => c * ψ t) = c ^ 2 * kinM ψ := by
  simp only [kinM, deriv_const_mul_field', mul_pow, integral_const_mul]

lemma sqP_smul {ψ : ℝ → ℝ} (hψ : H10 ψ) (c : ℝ) : sqP (hψ.const_mul c) = c ^ 2 • sqP hψ := by
  ext t; simp [mul_pow]

lemma QM_smul (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) (c : ℝ) :
    QM ν (hψ.const_mul c) = c ^ 2 * QM ν hψ := by
  rw [QM, QM, kinM_smul, sqP_smul hψ c, map_smul, smul_eq_mul]; ring

lemma norm2_smul (c : ℝ) (ψ : ℝ → ℝ) :
    ∫ t, (c * ψ t) ^ 2 ∂vol01 = c ^ 2 * ∫ t, ψ t ^ 2 ∂vol01 := by
  simp only [mul_pow, integral_const_mul]

/-! ### The `L²` parametrisation -/

instance fact_two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

lemma memLp_deriv {ψ : ℝ → ℝ} (hψ : H10 ψ) : MemLp (deriv ψ) 2 vol01 :=
  (memLp_two_iff_integrable_sq (measurable_deriv ψ).aestronglyMeasurable).2 hψ.2.2.2

/-- The derivative of `ψ ∈ H¹₀` as an element of `L²(0, 1)`. -/
noncomputable def dL {ψ : ℝ → ℝ} (hψ : H10 ψ) : L2I := (memLp_deriv hψ).toLp (deriv ψ)

lemma prim_dL {ψ : ℝ → ℝ} (hψ : H10 ψ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    prim (dL hψ) t = ψ t := by
  rw [prim, dL, integral_congr_mu1 (MemLp.coeFn_toLp (memLp_deriv hψ)) ht]
  have hac : AbsolutelyContinuousOnInterval ψ 0 t := hψ.1.mono (by
    rw [uIcc01, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  rw [hac.integral_deriv_eq_sub, hψ.2.1, sub_zero]

lemma norm_dL_sq {ψ : ℝ → ℝ} (hψ : H10 ψ) : ‖dL hψ‖ ^ 2 = kinM ψ := by
  rw [norm_sq_L2I, kinM]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_deriv hψ)] with t ht
  simp only [dL, ht]

lemma kinM_prim (f : L2I) : kinM (prim f) = ‖f‖ ^ 2 := by
  rw [norm_sq_L2I, kinM]
  have hd := (intervalIntegrable_of_mu1 (integrable_L2I f)
    ⟨zero_le_one, le_rfl⟩).ae_hasDerivAt_integral
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t h ht
  have := (h (by rw [uIcc01]; exact Ioo_subset_Icc_self ht) 0 (by simp)).deriv
  change deriv (fun x => ∫ s in (0 : ℝ)..x, (f : ℝ → ℝ) s) t ^ 2 = (f : ℝ → ℝ) t ^ 2
  rw [this]

/-- `∫₀ᵗ f` as a continuous function on `[0, 1]`. -/
noncomputable def primP (f : L2I) : C01 := ⟨fun t => prim f t, (continuousOn_prim f).domRestrict⟩

@[simp] lemma primP_apply (f : L2I) (t : Icc (0 : ℝ) 1) : primP f t = prim f t := rfl

lemma sqP_eq_primP {ψ : ℝ → ℝ} (hψ : H10 ψ) {f : L2I} (h : ∀ t ∈ Icc (0 : ℝ) 1, prim f t = ψ t) :
    sqP hψ = primP f * primP f := by
  ext t; simp [h t t.2, sq]

/-- `f ↦ ∫₀ᵗ f` as a continuous linear functional on `L²(0, 1)`. -/
noncomputable def primCLM {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : StrongDual ℝ L2I :=
  LinearMap.mkContinuous
    { toFun := fun f => prim f t
      map_add' := fun f f' => prim_add f f' ht
      map_smul' := fun c f => by simpa using prim_smul c f ht } 1
    fun f => by simpa [Real.norm_eq_abs] using abs_prim_le f ht

/-- `½`-Hölder continuity of primitives. -/
lemma abs_prim_sub_le_sqrt (f : L2I) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |prim f s - prim f t| ≤ √|s - t| * ‖f‖ := by
  have hf := integrable_L2I f
  have hf2 := integrable_sq_L2I f
  have key : ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a ≤ b →
      (prim f b - prim f a) ^ 2 ≤ (b - a) * ‖f‖ ^ 2 := fun {a b} ha hb hab => by
    have ii : ∀ {g : ℝ → ℝ}, Integrable g vol01 → IntervalIntegrable g volume a b := fun hg =>
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
        ((show IntegrableOn _ (Ioo (0 : ℝ) 1) volume from hg).mono_set (Ioo_subset_Ioo ha.1 hb.2))
    have e : prim f b - prim f a = ∫ s in a..b, (f : ℝ → ℝ) s := by
      rw [prim, prim, intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_of_mu1 hf hb) (intervalIntegrable_of_mu1 hf ha)]
    have h1 := sq_le_interval hab (ii hf) (ii hf2)
    have h2 : ∫ s in a..b, (f : ℝ → ℝ) s ^ 2 ≤ ‖f‖ ^ 2 := by
      rw [norm_sq_L2I, integral_vol01]
      exact intervalIntegral.integral_mono_interval ha.1 hab hb.2
        (ae_of_all _ fun s => by simp only [Pi.zero_apply]; positivity)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hf2)
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hab))
  have hsq : (prim f s - prim f t) ^ 2 ≤ |s - t| * ‖f‖ ^ 2 := by
    rcases le_total t s with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact key ht hs h
    · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, ← neg_sub, neg_sq]; exact key hs ht h
  calc |prim f s - prim f t| = √((prim f s - prim f t) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(|s - t| * ‖f‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = √|s - t| * ‖f‖ := by rw [Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ### Weak compactness -/

/-- Bounded sequences in `L²(0, 1)` have weakly convergent subsequences. -/
theorem exists_weak_subseq {f : ℕ → L2I} {R : ℝ} (hR : ∀ k, ‖f k‖ ≤ R) :
    ∃ g : L2I, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ h : L2I, Tendsto (fun k => inner ℝ (f (φ k)) h) atTop (𝓝 (inner ℝ g h)) := by
  set F : ℕ → WeakDual ℝ L2I := fun k =>
    WeakDual.toStrongDual.symm (InnerProductSpace.toDual ℝ L2I (f k))
  have hmem : ∀ k, F k ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ L2I) R :=
    fun k => by simpa [F] using hR k
  obtain ⟨G, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ L2I 0 R hmem
  refine ⟨(InnerProductSpace.toDual ℝ L2I).symm (WeakDual.toStrongDual G), φ, hφ, fun h => ?_⟩
  have := ((WeakDual.eval_continuous h).tendsto G).comp hlim
  simpa [F, Function.comp_def, InnerProductSpace.toDual_apply_apply] using this

/-- Weak convergence of bounded sequences makes the primitives converge uniformly. -/
theorem tendsto_primP {f : ℕ → L2I} {g : L2I} {R : ℝ} (hR : ∀ k, ‖f k‖ ≤ R)
    (hw : ∀ h : L2I, Tendsto (fun k => inner ℝ (f k) h) atTop (𝓝 (inner ℝ g h))) :
    Tendsto (fun k => primP (f k)) atTop (𝓝 (primP g)) := by
  have hpt : ∀ t : Icc (0 : ℝ) 1, Tendsto (fun k => prim (f k) t) atTop (𝓝 (prim g t)) :=
    fun t => by
      have e : ∀ u : L2I, prim u t = inner ℝ u ((InnerProductSpace.toDual ℝ L2I).symm
          (primCLM t.2)) := fun u => by
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]; rfl
      simp only [e]; exact hw _
  have heq : Equicontinuous fun k (t : Icc (0 : ℝ) 1) => prim (f k) t := by
    intro t0
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    have hR0 : 0 < R + 1 := by linarith [(norm_nonneg (f 0)).trans (hR 0)]
    refine ⟨(ε / (R + 1)) ^ 2, by positivity, fun t ht k => ?_⟩
    rw [Real.dist_eq]
    have hd : |(t0 : ℝ) - t| < (ε / (R + 1)) ^ 2 := by
      rw [abs_sub_comm]; simpa [Subtype.dist_eq, Real.dist_eq] using ht
    have hs : √|(t0 : ℝ) - t| < ε / (R + 1) := by
      rw [Real.sqrt_lt' (by positivity)]; exact hd
    calc |prim (f k) t0 - prim (f k) t| ≤ √|(t0 : ℝ) - t| * ‖f k‖ :=
          abs_prim_sub_le_sqrt _ t0.2 t.2
      _ ≤ ε / (R + 1) * R :=
          mul_le_mul hs.le (hR k) (norm_nonneg _) (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hR0]
          nlinarith [(norm_nonneg (f 0)).trans (hR 0)]
  have hu := (heq.tendsto_uniformFun_iff_pi atTop fun t => prim g t).2 (tendsto_pi_nhds.2 hpt)
  rw [UniformFun.tendsto_iff_tendstoUniformly] at hu
  exact ContinuousMap.tendsto_iff_tendstoUniformly.2 hu

/-! ### The minimiser -/

lemma exists_norm_one : ∃ ψ : ℝ → ℝ, ∃ _ : H10 ψ, ∫ t, ψ t ^ 2 ∂vol01 = 1 := by
  have hI := integral_tentG_sq_pos
  have hc2 : cKink 0 ^ 2 = 1 / ∫ t, tentG t ^ 2 ∂vol01 := by
    rw [cKink, Real.sq_sqrt (by positivity)]; norm_num
  refine ⟨_, h10_tentG.const_mul (cKink 0), ?_⟩
  rw [norm2_smul, hc2, div_mul_cancel₀ _ hI.ne']

lemma QM_ge_neg (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) (hn : ∫ t, ψ t ^ 2 ∂vol01 = 1) :
    -cM ν ≤ QM ν hψ := by
  have := QM_ge ν hψ
  have hk : 0 ≤ kinM ψ := integral_nonneg fun _ => sq_nonneg _
  rw [hn, mul_one] at this; linarith

/-- The ground-state energy of `-d²/dt² + ν` on `H¹₀(0, 1)`. -/
noncomputable def EM (ν : PotM) : ℝ :=
  sInf {e | ∃ ψ : ℝ → ℝ, ∃ hψ : H10 ψ, ∫ t, ψ t ^ 2 ∂vol01 = 1 ∧ QM ν hψ = e}

lemma EM_le (ν : PotM) {ψ : ℝ → ℝ} (hψ : H10 ψ) (hn : ∫ t, ψ t ^ 2 ∂vol01 = 1) :
    EM ν ≤ QM ν hψ :=
  csInf_le ⟨-cM ν, fun _ ⟨_, hφ, hφn, he⟩ => he ▸ QM_ge_neg ν hφ hφn⟩ ⟨ψ, hψ, hn, rfl⟩

/-- **The energy has a normalised minimiser on `H¹₀(0, 1)`.** -/
theorem exists_min (ν : PotM) :
    ∃ ψ : ℝ → ℝ, ∃ hψ : H10 ψ, ∫ t, ψ t ^ 2 ∂vol01 = 1 ∧ QM ν hψ = EM ν := by
  set S := {e | ∃ ψ : ℝ → ℝ, ∃ hψ : H10 ψ, ∫ t, ψ t ^ 2 ∂vol01 = 1 ∧ QM ν hψ = e}
  have hne : S.Nonempty := by
    obtain ⟨ψ, hψ, hn⟩ := exists_norm_one; exact ⟨_, ψ, hψ, hn, rfl⟩
  have hseq : ∀ k : ℕ, ∃ ψ : ℝ → ℝ, ∃ hψ : H10 ψ, ∫ t, ψ t ^ 2 ∂vol01 = 1 ∧
      QM ν hψ < EM ν + 1 / ((k : ℝ) + 1) := fun k => by
    obtain ⟨_, ⟨ψ, hψ, hn, rfl⟩, he⟩ :=
      exists_lt_of_csInf_lt hne (lt_add_of_pos_right (EM ν) (by positivity : (0 : ℝ) < 1 / (k + 1)))
    exact ⟨ψ, hψ, hn, he⟩
  choose ψ hψ hn hQ using hseq
  set f : ℕ → L2I := fun k => dL (hψ k)
  set R := √(2 * (EM ν + 1 + cM ν))
  have hR : ∀ k, ‖f k‖ ≤ R := fun k => by
    have h1 := kinM_le_QM ν (hψ k)
    rw [hn k, mul_one] at h1
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h3 : ‖f k‖ ^ 2 ≤ 2 * (EM ν + 1 + cM ν) := by
      simp only [f]; rw [norm_dL_sq]; linarith [hQ k]
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  obtain ⟨g, φ, hφ, hw⟩ := exists_weak_subseq hR
  have hP := tendsto_primP (f := fun k => f (φ k)) (fun k => hR _) hw
  have hev : ∀ t : Icc (0 : ℝ) 1, Tendsto (fun k => ψ (φ k) t) atTop (𝓝 (prim g t)) := fun t => by
    have := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp hP
    refine this.congr fun k => ?_
    simp [f, prim_dL (hψ (φ k)) t.2]
  have h1 : prim g 1 = 0 := by
    have := hev ⟨1, zero_le_one, le_rfl⟩
    simp only [(hψ _).2.2.1] at this
    exact (tendsto_nhds_unique this tendsto_const_nhds)
  have hg := h10_prim h1
  -- normalisation of the limit
  have hgn : ∫ t, prim g t ^ 2 ∂vol01 = 1 := by
    have hlim : Tendsto (fun k => ∫ t, ψ (φ k) t ^ 2 ∂vol01) atTop (𝓝 (∫ t, prim g t ^ 2 ∂vol01)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => R ^ 2)
        (fun k => (H10.int_sq_of_contOn (hψ (φ k)).continuousOn).aestronglyMeasurable)
        (integrable_const _) (fun k => ?_) ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have htI := Ioo_subset_Icc_self ht
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← prim_dL (hψ (φ k)) htI, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_prim_le _ htI).trans (hR _)) 2
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact (hev ⟨t, Ioo_subset_Icc_self ht⟩).pow 2
    simp only [hn] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- convergence of the energies and of the potential term
  have hQlim : Tendsto (fun k => QM ν (hψ (φ k))) atTop (𝓝 (EM ν)) := by
    have hz : Tendsto (fun k : ℕ => EM ν + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 (EM ν)) := by
      have := (tendsto_const_nhds (x := EM ν)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      rw [add_zero] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun k => EM_le ν _ (hn _)) fun k => (hQ _).le
  have hsq : ∀ k, sqP (hψ (φ k)) = primP (f (φ k)) * primP (f (φ k)) := fun k =>
    sqP_eq_primP _ fun t ht => prim_dL _ ht
  have hνlim : Tendsto (fun k => ν (sqP (hψ (φ k)))) atTop (𝓝 (ν (sqP hg))) := by
    rw [sqP_eq_primP hg fun t _ => rfl]
    simp only [hsq]
    exact (ν.continuous.tendsto _).comp (hP.mul hP)
  set L := EM ν - ν (sqP hg)
  have hkin : Tendsto (fun k => ‖f (φ k)‖ ^ 2) atTop (𝓝 L) := by
    refine (hQlim.sub hνlim).congr fun k => ?_
    simp only [f, norm_dL_sq, QM]; ring
  have hL0 : 0 ≤ L := ge_of_tendsto' hkin fun _ => sq_nonneg _
  have hnorm : Tendsto (fun k => ‖f (φ k)‖) atTop (𝓝 √L) := by
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
  refine ⟨prim g, hg, hgn, le_antisymm ?_ (EM_le ν hg hgn)⟩
  rw [QM, kinM_prim]
  linarith

/-- `E₀ ∫ φ² ≤ QM ν φ` on all of `H¹₀`. -/
theorem EM_mul_le (ν : PotM) {φ : ℝ → ℝ} (hφ : H10 φ) :
    EM ν * ∫ t, φ t ^ 2 ∂vol01 ≤ QM ν hφ := by
  set m := ∫ t, φ t ^ 2 ∂vol01
  have hm : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  rcases hm.eq_or_lt with h | h
  · rw [← h, mul_zero]
    have := QM_ge ν hφ
    have hk : 0 ≤ kinM φ := integral_nonneg fun _ => sq_nonneg _
    change _ - cM ν * m ≤ _ at this
    rw [← h, mul_zero] at this; linarith
  · set c := 1 / √m
    have hc : c ^ 2 = 1 / m := by rw [div_pow, Real.sq_sqrt hm, one_pow]
    have hn' : ∫ t, (c * φ t) ^ 2 ∂vol01 = 1 := by
      rw [norm2_smul, hc, one_div_mul_cancel h.ne']
    have := EM_le ν (hφ.const_mul c) hn'
    rw [QM_smul ν hφ c, hc, div_mul_eq_mul_div, one_mul, le_div_iff₀ h] at this
    exact this

/-- A normalised minimiser is a ground state. -/
theorem isGSM_of_min {ν : PotM} {ψ : ℝ → ℝ} (hψ : H10 ψ) (hn : ∫ t, ψ t ^ 2 ∂vol01 = 1)
    (hmin : QM ν hψ = EM ν) : IsGSM ν ψ := by
  refine ⟨hψ, by rw [hn]; exact one_pos, fun φ hφ => ?_⟩
  rw [hn, mul_one, hmin]
  exact EM_mul_le ν hφ

/-- **Every measure potential has a normalised ground state**, with energy `EM ν`. -/
theorem exists_isGSM (ν : PotM) :
    ∃ ψ : ℝ → ℝ, ∃ hψ : H10 ψ, IsGSM ν ψ ∧ ∫ t, ψ t ^ 2 ∂vol01 = 1 ∧ QM ν hψ = EM ν := by
  obtain ⟨ψ, hψ, hn, hmin⟩ := exists_min ν
  exact ⟨ψ, hψ, isGSM_of_min hψ hn hmin, hn, hmin⟩

/-! ### The Euler–Lagrange equation -/

lemma integrable_mul_of_sq {u w : ℝ → ℝ} (hu : AEStronglyMeasurable u vol01)
    (hw : AEStronglyMeasurable w vol01) (hu2 : Integrable (fun t => u t ^ 2) vol01)
    (hw2 : Integrable (fun t => w t ^ 2) vol01) : Integrable (fun t => u t * w t) vol01 := by
  refine (hu2.add hw2).mono' (hu.mul hw) (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  change |u t| * |w t| ≤ u t ^ 2 + w t ^ 2
  nlinarith [sq_abs (u t), sq_abs (w t), sq_nonneg (|u t| - |w t|), abs_nonneg (u t),
    abs_nonneg (w t)]

lemma integrable_dd {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) :
    Integrable (fun t => deriv ψ t * deriv φ t) vol01 :=
  integrable_mul_of_sq (measurable_deriv ψ).aestronglyMeasurable
    (measurable_deriv φ).aestronglyMeasurable hψ.2.2.2 hφ.2.2.2

lemma integrable_pp {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) :
    Integrable (fun t => ψ t * φ t) vol01 :=
  integrable_mul_of_sq (H10.aesm_of_contOn hψ.continuousOn) (H10.aesm_of_contOn hφ.continuousOn)
    (H10.int_sq_of_contOn hψ.continuousOn) (H10.int_sq_of_contOn hφ.continuousOn)

lemma ae_deriv_add {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) (s : ℝ) :
    ∀ᵐ t ∂vol01, deriv (fun t => ψ t + s * φ t) t = deriv ψ t + s * deriv φ t := by
  have h1 := hψ.1.ae_differentiableAt
  have h2 := hφ.1.ae_differentiableAt
  rw [uIcc01] at h1 h2
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae h2, ae_restrict_mem measurableSet_Ioo]
    with t a b ht
  have hI := Ioo_subset_Icc_self ht
  exact ((a hI).hasDerivAt.add ((b hI).hasDerivAt.const_mul s)).deriv

lemma kinM_add {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) (s : ℝ) :
    kinM (fun t => ψ t + s * φ t) =
      kinM ψ + 2 * s * ∫ t, deriv ψ t * deriv φ t ∂vol01 + s ^ 2 * kinM φ := by
  have e : (fun t => deriv (fun t => ψ t + s * φ t) t ^ 2) =ᵐ[vol01] fun t => deriv ψ t ^ 2 +
      2 * s * (deriv ψ t * deriv φ t) + s ^ 2 * deriv φ t ^ 2 :=
    (ae_deriv_add hψ hφ s).mono fun t ht => by simp only [ht]; ring
  have i1 : Integrable (fun t => deriv ψ t ^ 2) vol01 := hψ.2.2.2
  have i2 : Integrable (fun t => 2 * s * (deriv ψ t * deriv φ t)) vol01 :=
    (integrable_dd hψ hφ).const_mul (2 * s)
  have i12 : Integrable (fun t => deriv ψ t ^ 2 + 2 * s * (deriv ψ t * deriv φ t)) vol01 := i1.add i2
  have i3 : Integrable (fun t => s ^ 2 * deriv φ t ^ 2) vol01 := hφ.2.2.2.const_mul _
  rw [kinM, integral_congr_ae e, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_const_mul]
  rfl

lemma norm2_add (ψ φ : ℝ → ℝ) (hψ : H10 ψ) (hφ : H10 φ) (s : ℝ) :
    ∫ t, (ψ t + s * φ t) ^ 2 ∂vol01 =
      ∫ t, ψ t ^ 2 ∂vol01 + 2 * s * ∫ t, ψ t * φ t ∂vol01 + s ^ 2 * ∫ t, φ t ^ 2 ∂vol01 := by
  have i1 : Integrable (fun t => ψ t ^ 2) vol01 := H10.int_sq_of_contOn hψ.continuousOn
  have i2 : Integrable (fun t => 2 * s * (ψ t * φ t)) vol01 := (integrable_pp hψ hφ).const_mul (2 * s)
  have i12 : Integrable (fun t => ψ t ^ 2 + 2 * s * (ψ t * φ t)) vol01 := i1.add i2
  have i3 : Integrable (fun t => s ^ 2 * φ t ^ 2) vol01 :=
    (H10.int_sq_of_contOn hφ.continuousOn).const_mul (s ^ 2)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2, ← integral_add i12 i3]
  congr 1; funext t; ring

/-- `ψ + s φ ∈ H¹₀`. -/
lemma H10.add_const_mul {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) (s : ℝ) :
    H10 fun t => ψ t + s * φ t := by
  refine ⟨hψ.1.add (hφ.const_mul s).1, by simp [hψ.2.1, hφ.2.1], by simp [hψ.2.2.1, hφ.2.2.1], ?_⟩
  have i1 : Integrable (fun t => deriv ψ t ^ 2) vol01 := hψ.2.2.2
  have i2 := (integrable_dd hψ hφ).const_mul (2 * s)
  have i3 : Integrable (fun t => s ^ 2 * deriv φ t ^ 2) vol01 := hφ.2.2.2.const_mul _
  refine ((i1.add i2).add i3).congr ((ae_deriv_add hψ hφ s).mono fun t ht => ?_)
  simp only [Pi.add_apply, ht]; ring

/-- `ψ φ` as a continuous function on `[0, 1]`. -/
noncomputable def mulP {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) : C01 :=
  ⟨fun t => ψ t * φ t, (hψ.continuousOn.mul hφ.continuousOn).domRestrict⟩

@[simp] lemma mulP_apply {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) (t : Icc (0 : ℝ) 1) :
    mulP hψ hφ t = ψ t * φ t := rfl

lemma QM_add {ν : PotM} {ψ φ : ℝ → ℝ} (hψ : H10 ψ) (hφ : H10 φ) (s : ℝ) :
    QM ν (hψ.add_const_mul hφ s) = QM ν hψ +
      2 * s * (∫ t, deriv ψ t * deriv φ t ∂vol01 + ν (mulP hψ hφ)) + s ^ 2 * QM ν hφ := by
  have e : sqP (hψ.add_const_mul hφ s) = sqP hψ + (2 * s) • mulP hψ hφ + s ^ 2 • sqP hφ := by
    ext t; simp; ring
  rw [QM, QM, QM, kinM_add hψ hφ, e, map_add, map_add, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul]
  ring

lemma eq_zero_of_quad {a c : ℝ} (h : ∀ s : ℝ, 0 ≤ 2 * s * a + s ^ 2 * c) : a = 0 := by
  set k := |c| + 1
  have hk : 0 < k := by positivity
  have h1 := h (-a / k)
  have e : 2 * (-a / k) * a + (-a / k) ^ 2 * c = a ^ 2 * (c - 2 * k) / k ^ 2 := by
    field_simp; ring
  rw [e] at h1
  have h2 : 0 ≤ a ^ 2 * (c - 2 * k) := by
    have := mul_nonneg h1 (sq_nonneg k)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  have h3 : c - 2 * k < 0 := by simp only [k]; linarith [le_abs_self c, abs_nonneg c]
  have : a ^ 2 ≤ 0 := by nlinarith [sq_nonneg a]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg a))

/-- **The Euler–Lagrange equation**: a normalised minimiser satisfies `-ψ'' + ν ψ = E₀ ψ` weakly,
`∫ ψ' φ' + ν(ψ φ) = E₀ ∫ ψ φ` for all `φ ∈ H¹₀(0, 1)`. -/
theorem euler_lagrange {ν : PotM} {ψ : ℝ → ℝ} (hψ : H10 ψ) (hn : ∫ t, ψ t ^ 2 ∂vol01 = 1)
    (hmin : QM ν hψ = EM ν) {φ : ℝ → ℝ} (hφ : H10 φ) :
    ∫ t, deriv ψ t * deriv φ t ∂vol01 + ν (mulP hψ hφ) = EM ν * ∫ t, ψ t * φ t ∂vol01 := by
  have key := eq_zero_of_quad (a := ∫ t, deriv ψ t * deriv φ t ∂vol01 + ν (mulP hψ hφ) -
      EM ν * ∫ t, ψ t * φ t ∂vol01) (c := QM ν hφ - EM ν * ∫ t, φ t ^ 2 ∂vol01) fun s => by
    have h := EM_mul_le ν (hψ.add_const_mul hφ s)
    rw [QM_add hψ hφ s, norm2_add ψ φ hψ hφ s, hn, hmin] at h
    linarith
  linarith

end DFT.Continuum.Line
