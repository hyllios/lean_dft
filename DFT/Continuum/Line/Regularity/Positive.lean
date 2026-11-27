/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Regularity.H2Bos
import DFT.Continuum.Line.UCP.Cut

/-!
# Interacting ground-state densities are positive

For `N` bosons or fermions on `H¹₀` with continuous `v` and continuous relabelling-invariant `w`,
the density profile `K` of a ground state (`Line/DensC1`) is positive on `(0, 1)`. Hence a density
with an interior zero is never `v`-representable, for any `N`.

The argument (after Corso, Lett. Math. Phys. 2026): if `K(t₀) = 0`, then `K'(t₀) = 0` (`K ≥ 0` is
`C¹`), so `K(t) ≤ |t - t₀|` near `t₀`, and `Ψ` is small near each plane `xᵢ = t₀`:
`(1/δ) ∫_{t₀-δ<xᵢ<t₀} |Ψ| = O(√δ)` (`slab_small`). So `Ψ_U = 1_U Ψ`, `U = {xᵢ < t₀ ∀ i}`, is an
`H¹₀` state of the same symmetry (`isWD_cutAll`), and so is `Ψ - Ψ_U`. The energy splits, both
pieces have Rayleigh quotient `≥ E`, so the nonzero one is a ground state vanishing on a set of
positive measure, contradicting unique continuation.

* `bumpF`, `bumpP`; `integral_xi_eq_x0`; **`slab_small`**.
* `Uset`, **`isWD_cutAll`**.
* **`gs_profile_pos`**: `K > 0` on `(0, 1)`.
* **`not_vrep_of_zero`**, **`sin_nrep_not_vrep`**: `2N sin²(2πt)/…` with its zero at `½` is
  `N`-representable but not `v`-representable, for any `N`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-! ### A bump -/

/-- `1` on `[t₀ - δ, t₀]`, `0` off `(t₀ - 2δ, t₀ + δ)`, piecewise linear. -/
noncomputable def bumpF (t0 δ t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - (t0 - 2 * δ)) / δ) ((t0 + δ - t) / δ)))

lemma continuous_bumpF (t0 δ : ℝ) : Continuous (bumpF t0 δ) := by unfold bumpF; fun_prop

lemma bumpF_nonneg (t0 δ t : ℝ) : 0 ≤ bumpF t0 δ t := le_max_left _ _

lemma bumpF_le_one (t0 δ t : ℝ) : bumpF t0 δ t ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma bumpF_eq_one {t0 δ t : ℝ} (hδ : 0 < δ) (h1 : t0 - δ ≤ t) (h2 : t ≤ t0) :
    bumpF t0 δ t = 1 := by
  have a : 1 ≤ (t - (t0 - 2 * δ)) / δ := by rw [le_div_iff₀ hδ]; linarith
  have b : 1 ≤ (t0 + δ - t) / δ := by rw [le_div_iff₀ hδ]; linarith
  simp only [bumpF, min_eq_left (le_min a b), max_eq_right zero_le_one]

lemma bumpF_eq_zero {t0 δ t : ℝ} (hδ : 0 < δ) (h : t ∉ Ioo (t0 - 2 * δ) (t0 + δ)) :
    bumpF t0 δ t = 0 := by
  simp only [mem_Ioo, not_and_or, not_lt] at h
  refine max_eq_left ?_
  rcases h with h | h
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))

lemma bumpF_le_indicator {t0 δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    bumpF t0 δ t ≤ (Icc (t0 - 2 * δ) (t0 + δ)).indicator 1 t := by
  by_cases ht : t ∈ Icc (t0 - 2 * δ) (t0 + δ)
  · rw [indicator_of_mem ht]; exact bumpF_le_one _ _ _
  · rw [indicator_of_notMem ht, bumpF_eq_zero hδ fun h => ht (Ioo_subset_Icc_self h)]

/-- The bump as a potential. -/
noncomputable def bumpP (t0 δ : ℝ) : Pot :=
  ⟨fun t => bumpF t0 δ t, (continuous_bumpF t0 δ).comp continuous_subtype_val⟩

lemma ext_bumpP {t0 δ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ext (bumpP t0 δ) t = bumpF t0 δ t := by
  simp [SturmLiouville.ext, bumpP, projIcc_of_mem _ ht]

lemma ext_bumpP_nonneg (t0 δ t : ℝ) : 0 ≤ ext (bumpP t0 δ) t := bumpF_nonneg _ _ _

lemma ext_bumpP_le_indicator {t0 δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ext (bumpP t0 δ) t ≤ (Icc (t0 - 2 * δ) (t0 + δ)).indicator 1 t := by
  rw [ext_bumpP ht]; exact bumpF_le_indicator hδ t

/-! ### Symmetric integrals -/

lemma integral_xi_eq_x0 {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) (f : ℝ → ℝ) (i : Fin (n + 1)) :
    ∫ x, f (x i) * (Ψ x * Ψ x) ∂μN n = ∫ x, f (x 0) * (Ψ x * Ψ x) ∂μN n := by
  rw [← integral_pm (Equiv.swap 0 i) (fun x => f (x 0) * (Ψ x * Ψ x))]
  refine integral_congr_ae ?_
  filter_upwards [hΨ.2.2 (Equiv.swap 0 i) trivial] with x hx
  simp only [pm_apply, Equiv.swap_apply_left] at hx ⊢
  rw [hx]
  have := ch_mul_self τ (Equiv.swap 0 i)
  linear_combination (-(f (x i) * (Ψ x * Ψ x))) * this

lemma integral_xi_eq_x0' (f : ℝ → ℝ) (i : Fin (n + 1)) :
    ∫ x, f (x i) ∂μN n = ∫ x, f (x 0) ∂μN n := by
  rw [← integral_pm (Equiv.swap 0 i) (fun x => f (x 0))]
  simp only [pm_apply, Equiv.swap_apply_left]

lemma integral_x0 {f : ℝ → ℝ} (hf : Continuous f) : ∫ x, f (x 0) ∂μN n = ∫ t, f t ∂μ1 := by
  have hF : Integrable (fun x : Cfg n => f (x 0)) (μN n) :=
    integrableN (hf.comp (continuous_apply 0))
  rw [integral_cube_cons' hF]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  simp only [Fin.cons_zero]
  rw [setIntegral_const, measureReal_def, volume_cube', ENNReal.toReal_one, one_smul]

/-! ### Smallness near the planes -/

/-- **`Ψ` is small near the plane `xᵢ = t₀`** when its density profile vanishes linearly at `t₀`. -/
theorem slab_small {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) {K : ℝ → ℝ}
    (hρ : ∀ v : Pot, dens (settingW τ n w hw) Ψ v = ∫ t, ext v t * K t ∂μ1)
    (hKi : Integrable K μ1) {t0 L η : ℝ} (hη : 0 < η) (hL : 0 ≤ L)
    (hKle : ∀ t, |t - t0| ≤ η → K t ≤ L * |t - t0|) {F : Cfg n → ℝ}
    (hF : ∀ᵐ x ∂μN n, |F x| ≤ |Ψ x|) (i : Fin (n + 1)) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 1) * ∫ x, slab i t0 (1 / ((m : ℝ) + 1)) x * |F x| ∂μN n)
      atTop (𝓝 0) := by
  set N : ℝ := n + 1
  have hN : 0 < N := by positivity
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set a : ℕ → ℝ := fun m => √(δ m)
  have ha : ∀ m, 0 < a m := fun m => Real.sqrt_pos.2 (hδ m)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have := hδ0.sqrt; rwa [Real.sqrt_zero] at this
  set B : ℕ → ℝ := fun m => 3 * L * a m / N + 3 / 2 * a m
  have hB : Tendsto B atTop (𝓝 0) := by
    have := ((ha0.const_mul (3 * L)).div_const N).add (ha0.const_mul (3 / 2))
    simpa using this
  have hsq := int_mul_L2 hΨ.1 hΨ.1
  have hev : ∀ᶠ m in atTop, 2 * δ m ≤ η := by
    have := (hδ0.const_mul 2).eventually (gt_mem_nhds (show (2 : ℝ) * 0 < η by linarith))
    filter_upwards [this] with m hm; exact hm.le
  refine squeeze_zero' (Eventually.of_forall fun m => mul_nonneg (by positivity)
    (integral_nonneg fun x => mul_nonneg (slab_nonneg _ _ _ _) (abs_nonneg _))) ?_ hB
  filter_upwards [hev] with m hm
  set d := δ m
  set aa := a m
  have hd := hδ m
  have haa := ha m
  have haa2 : aa ^ 2 = d := Real.sq_sqrt hd.le
  set vb := bumpP t0 d
  have hvbc : Continuous (ext vb) := continuous_ext vb
  -- pointwise bound
  have hvi : Integrable (fun x : Cfg n => ext vb (x i)) (μN n) :=
    integrableN (hvbc.comp (continuous_apply i))
  have hvΨ : Integrable (fun x : Cfg n => ext vb (x i) * (Ψ x * Ψ x)) (μN n) := by
    obtain ⟨C, hC⟩ := ae_bound_cont (n := n) (hvbc.comp (continuous_apply i))
    exact hsq.bdd_mul (hvbc.comp (continuous_apply i)).aestronglyMeasurable hC
  have hRi : Integrable (fun x : Cfg n => ext vb (x i) * (Ψ x * Ψ x) / (2 * aa) +
      aa / 2 * ext vb (x i)) (μN n) := (hvΨ.div_const _).add (hvi.const_mul _)
  have hpt : ∀ᵐ x ∂μN n, slab i t0 d x * |F x| ≤
      ext vb (x i) * (Ψ x * Ψ x) / (2 * aa) + aa / 2 * ext vb (x i) := by
    filter_upwards [hF, ae_restrict_mem measurableSet_cube] with x hx hcube
    have hxi : x i ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (hcube i trivial)
    have hv0 := ext_bumpP_nonneg t0 d (x i)
    by_cases hs : x i ∈ Ioo (t0 - d) t0
    · have hsl : slab i t0 d x = 1 := by simp [slab, hs]
      have hv1 : ext vb (x i) = 1 := by
        rw [ext_bumpP hxi]; exact bumpF_eq_one hd hs.1.le hs.2.le
      rw [hsl, hv1, one_mul, one_mul, mul_one]
      have hamgm : |Ψ x| ≤ Ψ x * Ψ x / (2 * aa) + aa / 2 := by
        rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (|Ψ x| - aa), sq_abs (Ψ x)]
      linarith
    · have hsl : slab i t0 d x = 0 := by simp [slab, hs]
      rw [hsl, zero_mul]
      exact add_nonneg (div_nonneg (mul_nonneg hv0 (mul_self_nonneg _)) (by positivity))
        (mul_nonneg (by positivity) hv0)
  have hint : ∫ x, slab i t0 d x * |F x| ∂μN n ≤
      ∫ x, (ext vb (x i) * (Ψ x * Ψ x) / (2 * aa) + aa / 2 * ext vb (x i)) ∂μN n := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
      mul_nonneg (slab_nonneg _ _ _ _) (abs_nonneg _)) hRi hpt
  -- the two integrals
  have hI1 : ∫ x, ext vb (x i) * (Ψ x * Ψ x) ∂μN n ≤ 6 * L * d ^ 2 / N := by
    rw [integral_xi_eq_x0 hΨ (ext vb) i]
    have h := hρ vb
    rw [dens_eq_x0 hΨ vb] at h
    have hK : ∫ t, ext vb t * K t ∂μ1 ≤ 6 * L * d ^ 2 := by
      have hb : ∀ t ∈ Ioo (0 : ℝ) 1, ext vb t * K t ≤
          2 * L * d * (Icc (t0 - 2 * d) (t0 + d)).indicator 1 t := fun t ht => by
        have hti := Ioo_subset_Icc_self ht
        have hle := ext_bumpP_le_indicator (t0 := t0) hd hti
        have hv0 := ext_bumpP_nonneg t0 d t
        by_cases hin : t ∈ Icc (t0 - 2 * d) (t0 + d)
        · rw [indicator_of_mem hin] at hle ⊢
          have hKt : K t ≤ 2 * L * d := by
            have h1 : |t - t0| ≤ 2 * d := by
              rw [abs_le]; constructor <;> linarith [hin.1, hin.2]
            have := hKle t (h1.trans hm)
            nlinarith
          simp only [Pi.one_apply, mul_one] at hle ⊢
          calc ext vb t * K t ≤ ext vb t * (2 * L * d) := mul_le_mul_of_nonneg_left hKt hv0
            _ ≤ 1 * (2 * L * d) := mul_le_mul_of_nonneg_right hle (by positivity)
            _ = 2 * L * d := one_mul _
        · rw [indicator_of_notMem hin] at hle ⊢
          have : ext vb t = 0 := le_antisymm hle hv0
          rw [this]; simp
      have hi1 : Integrable (fun t => ext vb t * K t) μ1 := by
        obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
          hvbc.continuousOn
        refine hKi.bdd_mul (c := C) hvbc.aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hC t (Ioo_subset_Icc_self ht)
      have hi2 : Integrable (fun t => 2 * L * d * (Icc (t0 - 2 * d) (t0 + d)).indicator 1 t) μ1 :=
        ((integrable_const (1 : ℝ)).indicator measurableSet_Icc).const_mul _
      calc ∫ t, ext vb t * K t ∂μ1
          ≤ ∫ t, 2 * L * d * (Icc (t0 - 2 * d) (t0 + d)).indicator 1 t ∂μ1 :=
            setIntegral_mono_on hi1 hi2 measurableSet_Ioo hb
        _ ≤ 2 * L * d * (t0 + d - (t0 - 2 * d)) := by
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left (integral_indicator_Icc_le (by linarith))
              (by positivity)
        _ = 6 * L * d ^ 2 := by ring
    rw [le_div_iff₀ hN]
    have : N * ∫ x, ext vb (x 0) * (Ψ x * Ψ x) ∂μN n = ∫ t, ext vb t * K t ∂μ1 := by
      rw [← h]
    linarith
  have hI2 : ∫ x, ext vb (x i) ∂μN n ≤ 3 * d := by
    rw [integral_xi_eq_x0' (ext vb) i, integral_x0 hvbc]
    have hb : ∀ t ∈ Ioo (0 : ℝ) 1, ext vb t ≤ (Icc (t0 - 2 * d) (t0 + d)).indicator 1 t :=
      fun t ht => ext_bumpP_le_indicator hd (Ioo_subset_Icc_self ht)
    calc ∫ t, ext vb t ∂μ1 ≤ ∫ t, (Icc (t0 - 2 * d) (t0 + d)).indicator 1 t ∂μ1 :=
          setIntegral_mono_on (integrable_mu1_cont hvbc)
            ((integrable_const (1 : ℝ)).indicator measurableSet_Icc) measurableSet_Ioo hb
      _ ≤ t0 + d - (t0 - 2 * d) := integral_indicator_Icc_le (by linarith)
      _ = 3 * d := by ring
  rw [integral_add (hvΨ.div_const _) (hvi.const_mul _), integral_div, integral_const_mul] at hint
  have hmd : ((m : ℝ) + 1) * d = 1 := by simp only [d, δ]; field_simp
  calc ((m : ℝ) + 1) * ∫ x, slab i t0 d x * |F x| ∂μN n
      ≤ ((m : ℝ) + 1) * ((6 * L * d ^ 2 / N) / (2 * aa) + aa / 2 * (3 * d)) := by
        refine mul_le_mul_of_nonneg_left (hint.trans ?_) (by positivity)
        gcongr
    _ = B m := by
        rw [← haa2] at hmd ⊢
        have key : ((m : ℝ) + 1) * ((6 * L * (aa ^ 2) ^ 2 / N) / (2 * aa) + aa / 2 * (3 * aa ^ 2)) =
            (3 * L * aa / N + 3 / 2 * aa) * (((m : ℝ) + 1) * aa ^ 2) := by
          field_simp; ring
        rw [key, hmd, mul_one]

/-! ### Cutting at all planes -/

/-- `{x | xᵢ < t₀ for i ∈ S}`. -/
def Uset (S : Finset (Fin (n + 1))) (t0 : ℝ) : Set (Cfg n) := ⋂ i ∈ S, HalfT i t0

lemma measurableSet_Uset (S : Finset (Fin (n + 1))) (t0 : ℝ) : MeasurableSet (Uset S t0) :=
  Finset.measurableSet_biInter S fun i _ => measurableSet_HalfT i t0

/-- **Cutting at the planes `xᵢ = t₀`, `i ∈ S`.** -/
theorem isWD_cutAll {Ψ : Cfg n → ℝ} (hΨ : H1W Ψ) (t0 : ℝ)
    (hslab : ∀ F : Cfg n → ℝ, AEStronglyMeasurable F (μN n) → (∀ᵐ x ∂μN n, |F x| ≤ |Ψ x|) →
      ∀ i, Tendsto (fun m : ℕ => ((m : ℝ) + 1) *
        ∫ x, slab i t0 (1 / ((m : ℝ) + 1)) x * |F x| ∂μN n) atTop (𝓝 0))
    (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    IsWD k ((Uset S t0).indicator Ψ) ((Uset S t0).indicator (dW k Ψ)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Uset, Finset.notMem_empty, iInter_of_empty, iInter_univ, indicator_univ]
    exact dW_spec (hΨ.2 k)
  | insert i S hi ih =>
    have e : Uset (insert i S) t0 = HalfT i t0 ∩ Uset S t0 := by
      simp only [Uset, Finset.set_biInter_insert]
    rw [e, ← indicator_indicator, ← indicator_indicator]
    have hm := hΨ.1.indicator (measurableSet_Uset S t0).nullMeasurableSet
    refine isWD_cut hm ih i t0 (hslab _ hm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_) i)
    by_cases hx : x ∈ Uset S t0 <;> simp [hx]

/-! ### Positivity -/

lemma pos_measure_pi {a b : Fin (n + 1) → ℝ} (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j)
    (hb : ∀ j, b j ≤ 1) : 0 < μN n (Set.pi univ fun j => Ioo (a j) (b j)) := by
  have hsub : (Set.pi univ fun j => Ioo (a j) (b j)) ⊆ Cube n :=
    pi_mono fun j _ => Ioo_subset_Ioo (ha j) (hb j)
  rw [Measure.restrict_apply' measurableSet_cube, inter_eq_left.2 hsub, Real.volume_pi_Ioo,
    pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun j _ => (ENNReal.ofReal_pos.2 (sub_pos.2 (hab j))).ne'

lemma not_ae_ne_of_zero_on {f : Cfg n → ℝ} {P : Set (Cfg n)} (hP : 0 < μN n P)
    (hz : ∀ x ∈ P, f x = 0) : ¬ ∀ᵐ x ∂μN n, f x ≠ 0 := by
  intro h
  have : μN n {x | ¬ f x ≠ 0} = 0 := ae_iff.1 h
  exact hP.ne' (measure_mono_null (fun x hx => by simpa using hz x hx) this)

/-- **The density profile of an interacting ground state is positive on `(0, 1)`.** -/
theorem gs_profile_pos (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW τ n w hw) v Ψ) :
    ∀ t0 ∈ Ioo (0 : ℝ) 1, 0 < KS (fun m => cN m Ψ) t0 := by
  intro t0 ht0
  set c : (Fin (n + 1) → ℕ) → ℝ := fun m => cN m Ψ
  have hcl := summable_lam_sq_stat hws hΨ
  set K := KS c
  have hK0 : ∀ t, 0 ≤ K t := fun t =>
    mul_nonneg (by positivity) (tsum_nonneg fun _ => sq_nonneg _)
  by_contra hcon
  have hKt0 : K t0 = 0 := le_antisymm (not_lt.1 hcon) (hK0 t0)
  -- `K'(t₀) = 0` and `K(t) ≤ |t - t₀|` near `t₀`
  have hmin : IsLocalMin K t0 := Eventually.of_forall fun t => by rw [hKt0]; exact hK0 t
  have hd := hasDerivAt_KS hcl t0
  have hd0 : KD c t0 = 0 := hmin.hasDerivAt_eq_zero hd
  rw [hd0] at hd
  have hlo := (hasDerivAt_iff_isLittleO.1 hd).bound (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.1 hlo
  have hKle : ∀ t, |t - t0| ≤ η / 2 → K t ≤ 1 * |t - t0| := fun t ht => by
    have h := hηb (show dist t t0 < η by rw [Real.dist_eq]; linarith)
    have h' : |K t - K t0| ≤ |t - t0| := by simpa using h
    rw [hKt0, sub_zero] at h'
    rw [one_mul]
    exact (le_abs_self _).trans h'
  -- the density is `∫ v K`
  have hρ := dens_eq_KS (w := w) (hw := hw) hΨ.1 hcl
  have hKi : Integrable K μ1 := integrable_mu1_cont (continuous_KS hcl)
  have hslab := fun (F : Cfg n → ℝ) (_ : AEStronglyMeasurable F (μN n)) hF i =>
    slab_small (w := w) (hw := hw) hΨ.1 (K := K) (fun v' => congrFun hρ v') hKi
      (by positivity : (0 : ℝ) < η / 2) zero_le_one hKle (F := F) hF i
  -- the cut state
  set U := Uset (Finset.univ : Finset (Fin (n + 1))) t0
  have hU : MeasurableSet U := measurableSet_Uset _ t0
  have hmemU : ∀ x, x ∈ U ↔ ∀ i, x i < t0 := fun x => by
    simp [U, Uset, HalfT]
  set ΨU := U.indicator Ψ
  have hWD : ∀ k, IsWD k ΨU (U.indicator (dW k Ψ)) :=
    isWD_cutAll (h1W_of_mem hΨ.1) t0 hslab Finset.univ
  have hUD : ΨU ∈ DomW τ n := by
    refine ⟨hΨ.1.1.indicator hU.nullMeasurableSet, fun k => ⟨_, hWD k⟩, fun σ _ => ?_⟩
    filter_upwards [hΨ.1.2.2 σ trivial] with x hx
    have hσ : pm σ x ∈ U ↔ x ∈ U := by
      rw [hmemU, hmemU]
      exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩
    by_cases hxU : x ∈ U
    · simp only [ΨU, indicator_of_mem hxU, indicator_of_mem (hσ.2 hxU), hx]
    · simp only [ΨU, indicator_of_notMem hxU, indicator_of_notMem (fun h => hxU (hσ.1 h)),
        mul_zero]
  set ΨV := Ψ - ΨU
  have hVD : ΨV ∈ DomW τ n := (DomW τ n).sub_mem hΨ.1 hUD
  have hsplit : Ψ = ΨU + (1 : ℝ) • ΨV := by simp [ΨV]
  have hUV : ∀ x, ΨU x * ΨV x = 0 := fun x => by
    by_cases hxU : x ∈ U <;> simp [ΨV, ΨU, hxU]
  -- the cross terms vanish
  have hdU : ∀ k, dW k ΨU =ᵐ[μN n] U.indicator (dW k Ψ) := fun k => dW_ae_eq (hWD k)
  have hdV : ∀ k, dW k ΨV =ᵐ[μN n] fun x => dW k Ψ x - U.indicator (dW k Ψ) x := fun k => by
    have h := IsWD.add hΨ.1.1 (hΨ.1.1.indicator hU.nullMeasurableSet |>.const_mul (-1))
      (dW_spec (hΨ.1.2.1 k)) (IsWD.const_mul (-1) (hWD k))
    have e1 : (fun x => Ψ x + -1 * ΨU x) = ΨV := funext fun x => by simp [ΨV]; ring
    have e2 : (fun x => dW k Ψ x + -1 * U.indicator (dW k Ψ) x) =
        fun x => dW k Ψ x - U.indicator (dW k Ψ) x := funext fun x => by ring
    rw [e1, e2] at h
    exact dW_ae_eq h
  have hcross_h0 : (settingW τ n w hw).h0 ΨU ΨV = 0 := by
    change h0W n w ΨU ΨV = 0
    simp only [h0W]
    have hk : ∀ k, ∫ x, dW k ΨU x * dW k ΨV x ∂μN n = 0 := fun k =>
      integral_eq_zero_of_ae (by
        filter_upwards [hdU k, hdV k] with x h1 h2
        rw [h1, h2]
        by_cases hxU : x ∈ U <;> simp [hxU])
    simp only [hk, Finset.sum_const_zero, zero_add]
    exact integral_eq_zero_of_ae (Eventually.of_forall fun x => by simp [hUV x])
  have hcross_pf : pf (settingW τ n w hw) v ΨU ΨV = 0 := by
    change ∫ x, LN n v x * (ΨU x * ΨV x) ∂μN n = 0
    exact integral_eq_zero_of_ae (Eventually.of_forall fun x => by simp [hUV x])
  have hcross_ip : ip (μ := μN n) ΨU ΨV = 0 :=
    integral_eq_zero_of_ae (Eventually.of_forall fun x => by simp [hUV x])
  have hQ : Q (settingW τ n w hw) v Ψ =
      Q (settingW τ n w hw) v ΨU + Q (settingW τ n w hw) v ΨV := by
    rw [congrArg (Q (settingW τ n w hw) v) hsplit]
    simp only [Q]
    rw [h0_expand hUD hVD, pf_expand v hUD hVD, hcross_h0, hcross_pf]
    ring
  have hip : ip (μ := μN n) Ψ Ψ = ip (μ := μN n) ΨU ΨU + ip (μ := μN n) ΨV ΨV := by
    rw [congrArg (fun φ => ip (μ := μN n) φ φ) hsplit]
    rw [ip_expand (S := settingW τ n w hw) hUD hVD, hcross_ip]; ring
  -- Rayleigh quotients
  set p := ip (μ := μN n) Ψ Ψ
  have hp : 0 < p := hΨ.2.1
  set E := Q (settingW τ n w hw) v Ψ / p
  have hge : ∀ φ ∈ DomW τ n, E * ip (μ := μN n) φ φ ≤ Q (settingW τ n w hw) v φ := fun φ hφ => by
    have := hΨ.2.2 φ hφ
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    linarith
  have hEp : Q (settingW τ n w hw) v Ψ = E * p := by simp only [E]; field_simp
  have h1 := hge ΨU hUD
  have h2 := hge ΨV hVD
  have hQU : Q (settingW τ n w hw) v ΨU = E * ip (μ := μN n) ΨU ΨU := by
    rw [hQ, hip] at hEp; linarith
  have hipU0 : 0 ≤ ip (μ := μN n) ΨU ΨU := integral_nonneg fun x => mul_self_nonneg _
  -- sets of positive measure
  have hPV : 0 < μN n (Set.pi univ fun j : Fin (n + 1) =>
      Ioo (if j = 0 then t0 else 0) 1) :=
    pos_measure_pi (fun j => by split_ifs <;> linarith [ht0.1])
      (fun j => by split_ifs <;> linarith [ht0.2]) (fun _ => le_rfl)
  have hPU : 0 < μN n (Set.pi univ fun _ : Fin (n + 1) => Ioo 0 t0) :=
    pos_measure_pi (fun _ => le_rfl) (fun _ => ht0.1) (fun _ => ht0.2.le)
  rcases hipU0.lt_or_eq with hpos | hzero
  · -- `Ψ_U` is a ground state vanishing on `{x₀ > t₀}`
    have hGS : IsGS (settingW τ n w hw) v ΨU := ⟨hUD, hpos, fun φ hφ => by
      rw [hQU]
      have := hge φ hφ
      nlinarith⟩
    refine not_ae_ne_of_zero_on hPV (fun x hx => ?_) (ucpW_cont (τ := τ) w hw v ΨU hGS)
    have hx0 : ¬ x 0 < t0 := by
      have := hx 0 trivial; simp only [↓reduceIte] at this; exact not_lt.2 this.1.le
    have hxU : x ∉ U := fun h => hx0 ((hmemU x).1 h 0)
    simp [ΨU, hxU]
  · -- `Ψ_U = 0`, so `Ψ = 0` on `U`
    have hz : ΨU =ᵐ[μN n] 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (ΨU x))
        (int_mul_L2 hUD.1 hUD.1)).1 hzero.symm
      filter_upwards [this] with x hx
      exact mul_self_eq_zero.1 hx
    have hucp := ucpW_cont (τ := τ) w hw v Ψ hΨ
    have hP : μN n (Set.pi univ fun _ : Fin (n + 1) => Ioo 0 t0) = 0 := by
      have : μN n {x | ¬ (Ψ x ≠ 0 ∧ ΨU x = 0)} = 0 := ae_iff.1 (hucp.and hz)
      refine measure_mono_null (fun x hx => ?_) this
      intro ⟨h1, h2⟩
      have hxU : x ∈ U := (hmemU x).2 fun i => (hx i trivial).2
      simp only [ΨU, indicator_of_mem hxU] at h2
      exact h1 h2
    exact hPU.ne' hP

/-! ### Densities with an interior zero -/

/-- **A density with an interior zero is not `v`-representable**, for any number of bosons or
fermions (continuous `v`, continuous relabelling-invariant `w`). -/
theorem not_vrep_of_zero (hws : ∀ σ x, w (pm σ x) = w x) {f : ℝ → ℝ} (hf : Continuous f)
    {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) 1) (hf0 : f t0 = 0) :
    ¬ EnsVRep (settingW τ n w hw) fun u => ∫ t, ext u t * f t ∂μ1 := by
  intro h
  obtain ⟨v, ψ, hψ, -, hd⟩ := (ensVRep_iff_W_cont _).1 h
  have hcl := summable_lam_sq_stat hws hψ
  have hρ := dens_eq_KS (w := w) (hw := hw) hψ.1 hcl
  have he := eqOn_of_integral_pot (f := KS fun m => cN m ψ) (g := f) (continuous_KS hcl) hf
    fun u => by
      have := congrFun (hρ.symm.trans hd) u
      exact this
  have := gs_profile_pos hws hψ t0 ht0
  rw [he ht0, hf0] at this
  exact lt_irrefl _ this

/-- **`N · 2 sin²(2πt)` is `N`-representable but not `v`-representable**, for any number of bosons
or fermions: it vanishes at `t = ½`. -/
theorem sin_nrep_not_vrep (hws : ∀ σ x, w (pm σ x) = w x) :
    (∃ ψ ∈ Nst (settingW τ n w hw), dens (settingW τ n w hw) ψ =
        fun u => ∫ t, ext u t * ((n + 1) * sinDens t) ∂μ1) ∧
      ¬ EnsVRep (settingW τ n w hw) fun u => ∫ t, ext u t * ((n + 1) * sinDens t) ∂μ1 := by
  have hsC : ContDiff ℝ 2 sinG := sinG_mem.1
  have hH : H10 sinG := by
    have h1 : ContDiff ℝ 1 sinG := hsC.of_le (by norm_num)
    refine ⟨ContDiffOn.absolutelyContinuousOnInterval h1.contDiffOn, sinG_mem.2.1, sinG_mem.2.2, ?_⟩
    exact (((h1.continuous_deriv le_rfl).pow 2).continuousOn.integrableOn_compact
      (K := Icc (0 : ℝ) 1) isCompact_Icc).mono_set Ioo_subset_Icc_self
  refine ⟨(lieb_characterisation _).2 ⟨fun t => √((n : ℝ) + 1) * sinG t, hH.const_mul _, ?_, ?_⟩,
    not_vrep_of_zero hws (by unfold sinDens sinG; fun_prop) (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
      ?_⟩
  · simp only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)]
    rw [integral_const_mul, sinG_norm, mul_one]
  · funext u
    simp only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1), sinDens]
  · simp only [sinDens, sinG]
    rw [show 2 * π * (1 / 2) = π by ring, sin_pi]
    simp

end DFT.Continuum.Line
