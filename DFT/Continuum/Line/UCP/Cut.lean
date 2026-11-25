/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.UCP.HalfSpace

/-!
# Restricting `H¹₀` functions to `{xᵢ < t₀}`

A weakly differentiable `F` restricts to the half-space `{xᵢ < t₀}` with weak derivatives
`1_{xᵢ < t₀} ∂ₖF`, provided `F` is small near the plane in the averaged sense
`(1/δ) ∫_{t₀ - δ < xᵢ < t₀} |F| → 0`. Proof with the cutoffs `θ((t₀ - xᵢ)/δ)`, `θ` the smooth step:
the boundary term is at most `sup|θ'| sup|φ| (1/δ) ∫_{slab} |F|`.

* `HalfT`, `cutT`, `dk_cutT`, `tendsto_cutT`.
* **`isWD_cut`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Real Filter Topology

variable {n : ℕ}

/-- The half-space `xᵢ < t₀`. -/
def HalfT (i : Fin (n + 1)) (t0 : ℝ) : Set (Cfg n) := {x | x i < t0}

lemma measurableSet_HalfT (i : Fin (n + 1)) (t0 : ℝ) : MeasurableSet (HalfT (n := n) i t0) :=
  measurableSet_lt (measurable_pi_apply i) measurable_const

/-- The cutoff `θ((t₀ - xᵢ)/δ)`. -/
noncomputable def cutT (i : Fin (n + 1)) (t0 δ : ℝ) (x : Cfg n) : ℝ :=
  smoothTransition ((t0 - x i) / δ)

lemma contDiff_cutT (i : Fin (n + 1)) (t0 δ : ℝ) : ContDiff ℝ 1 (cutT (n := n) i t0 δ) :=
  (smoothTransition.contDiff (n := 1)).comp
    (by fun_prop : ContDiff ℝ 1 fun x : Cfg n => (t0 - x i) / δ)

lemma dk_cutT (i : Fin (n + 1)) (t0 δ : ℝ) (k : Fin (n + 1)) (x : Cfg n) :
    dk k (cutT i t0 δ) x = deriv smoothTransition ((t0 - x i) / δ) *
      (-(Pi.single k (1 : ℝ) : Cfg n) i / δ) := by
  set L : Cfg n →L[ℝ] ℝ := δ⁻¹ • (-(ContinuousLinearMap.proj i : Cfg n →L[ℝ] ℝ))
  have hin : HasFDerivAt (fun y : Cfg n => (t0 - y i) / δ) L x := by
    have hi : HasFDerivAt (fun y : Cfg n => y i) (ContinuousLinearMap.proj i : Cfg n →L[ℝ] ℝ) x :=
      hasFDerivAt_apply i x
    have := ((hasFDerivAt_const t0 x).sub hi).const_mul δ⁻¹
    convert this using 1
    · funext y; rw [div_eq_inv_mul]; rfl
    · simp [L]
  have h := ((smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    ((t0 - x i) / δ)).hasDerivAt.comp_hasFDerivAt x hin
  change fderiv ℝ (smoothTransition ∘ fun y : Cfg n => (t0 - y i) / δ) x (Pi.single k 1) = _
  rw [h.fderiv]
  simp only [L, smul_apply, neg_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

lemma tendsto_cutT (i : Fin (n + 1)) (t0 : ℝ) (x : Cfg n) :
    Tendsto (fun m : ℕ => cutT i t0 (1 / ((m : ℝ) + 1)) x) atTop
      (𝓝 ((HalfT i t0).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x i < t0
  · rw [indicator_of_mem (show x ∈ HalfT i t0 from hx)]
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨m0, hm0⟩ := exists_nat_gt (1 / (t0 - x i))
    filter_upwards [eventually_ge_atTop m0] with m hm
    have hd : 0 < t0 - x i := by linarith
    refine (smoothTransition.one_of_one_le ?_).symm
    have h1 : (1 : ℝ) / (t0 - x i) < m + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hm; linarith
    rw [div_lt_iff₀ hd] at h1
    rw [div_div_eq_mul_div, div_one]
    linarith
  · rw [indicator_of_notMem (show x ∉ HalfT i t0 from hx)]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun m => ?_)
    refine (smoothTransition.zero_of_nonpos ?_).symm
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 hx]) (by positivity)

/-- The slab `t₀ - δ < xᵢ < t₀` as a function of `x`. -/
noncomputable def slab (i : Fin (n + 1)) (t0 δ : ℝ) (x : Cfg n) : ℝ :=
  (Ioo (t0 - δ) t0).indicator (fun _ => (1 : ℝ)) (x i)

lemma measurable_slab (i : Fin (n + 1)) (t0 δ : ℝ) : Measurable (slab (n := n) i t0 δ) :=
  (measurable_const.indicator measurableSet_Ioo).comp (measurable_pi_apply i)

lemma slab_nonneg (i : Fin (n + 1)) (t0 δ : ℝ) (x : Cfg n) : 0 ≤ slab i t0 δ x := by
  unfold slab; by_cases h : x i ∈ Ioo (t0 - δ) t0 <;> simp [h]

lemma slab_le_one (i : Fin (n + 1)) (t0 δ : ℝ) (x : Cfg n) : slab i t0 δ x ≤ 1 := by
  unfold slab; by_cases h : x i ∈ Ioo (t0 - δ) t0 <;> simp [h]

/-- **Restriction to `{xᵢ < t₀}`** for `F` small near the plane on average. -/
theorem isWD_cut {F G : Cfg n → ℝ} {k : Fin (n + 1)} (hF : MemLp F 2 (μN n)) (hG : IsWD k F G)
    (i : Fin (n + 1)) (t0 : ℝ)
    (hslab : Tendsto (fun m : ℕ => ((m : ℝ) + 1) *
      ∫ x, slab i t0 (1 / ((m : ℝ) + 1)) x * |F x| ∂μN n) atTop (𝓝 0)) :
    IsWD k ((HalfT i t0).indicator F) ((HalfT i t0).indicator G) := by
  set H := HalfT (n := n) i t0
  refine ⟨hG.1.indicator (measurableSet_HalfT i t0).nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ k
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  set θ : ℕ → Cfg n → ℝ := fun m => cutT i t0 (δ m)
  have hθc : ∀ m, ContDiff ℝ 1 (θ m) := fun m => contDiff_cutT i t0 _
  have hdθc : ∀ m, Continuous (dk k (θ m)) := fun m => continuous_dk_of_C1 (hθc m) k
  have hθ01 : ∀ m x, 0 ≤ θ m x ∧ θ m x ≤ 1 := fun m x =>
    ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  have hm : ∀ m, ∫ x, F x * (θ m x * dk k φ x) ∂μN n + ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n =
      -∫ x, G x * (θ m x * φ x) ∂μN n := fun m => by
    have h := hG.2 (fun x => θ m x * φ x) ((hθc m).mul hφ)
    simp only [dk_mul ((hθc m).differentiable one_ne_zero) (hφ.differentiable one_ne_zero)] at h
    rw [← integral_add (f := fun x => F x * (θ m x * dk k φ x))
      (g := fun x => F x * (dk k (θ m) x * φ x))
      (int_mul_cont hF ((hθc m).continuous.mul hdφ))
      (int_mul_cont hF ((hdθc m).mul hφ.continuous))]
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) h
    ring
  have L1 : Tendsto (fun m => ∫ x, F x * (θ m x * dk k φ x) ∂μN n) atTop
      (𝓝 (∫ x, H.indicator F x * dk k φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |F x * dk k φ x|)
      (fun m => hF.aestronglyMeasurable.mul ((hθc m).continuous.mul hdφ).aestronglyMeasurable)
      (int_mul_cont hF hdφ).abs (fun m => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, show F x * (θ m x * dk k φ x) = θ m x * (F x * dk k φ x) by ring,
        abs_mul, abs_of_nonneg (hθ01 m x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθ01 m x).2
    · have h := ((tendsto_cutT i t0 x).mul_const (dk k φ x)).const_mul (F x)
      convert h using 2
      by_cases hx : x ∈ H <;> simp [H, hx]
  have L3 : Tendsto (fun m => ∫ x, G x * (θ m x * φ x) ∂μN n) atTop
      (𝓝 (∫ x, H.indicator G x * φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |G x * φ x|)
      (fun m => hG.1.aestronglyMeasurable.mul
        ((hθc m).continuous.mul hφ.continuous).aestronglyMeasurable)
      (int_mul_cont hG.1 hφ.continuous).abs (fun m => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, show G x * (θ m x * φ x) = θ m x * (G x * φ x) by ring,
        abs_mul, abs_of_nonneg (hθ01 m x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθ01 m x).2
    · have h := ((tendsto_cutT i t0 x).mul_const (φ x)).const_mul (G x)
      convert h using 2
      by_cases hx : x ∈ H <;> simp [H, hx]
  obtain ⟨Mθ, hMθ⟩ := deriv_smoothTransition_bound
  obtain ⟨Bφ, hBφ⟩ := ae_bound_cont hφ.continuous
  have hMθ0 : 0 ≤ Mθ := (abs_nonneg _).trans (hMθ 0)
  have hFi : Integrable (fun x => |F x|) (μN n) := (hF.integrable one_le_two).abs
  have hsi : ∀ m, Integrable (fun x => slab i t0 (δ m) x * |F x|) (μN n) := fun m =>
    hFi.bdd_mul (c := 1) (measurable_slab i t0 _).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (slab_nonneg _ _ _ _)]; exact slab_le_one _ _ _ _)
  have L2 : Tendsto (fun m => ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n) atTop (𝓝 0) := by
    have hB0 : 0 ≤ max Bφ 0 := le_max_right _ _
    have hbound : ∀ m, ‖∫ x, F x * (dk k (θ m) x * φ x) ∂μN n‖ ≤
        Mθ * max Bφ 0 * (((m : ℝ) + 1) * ∫ x, slab i t0 (δ m) x * |F x| ∂μN n) := fun m => by
      have hpt : ∀ᵐ x ∂μN n, ‖F x * (dk k (θ m) x * φ x)‖ ≤
          Mθ * max Bφ 0 * ((m : ℝ) + 1) * (slab i t0 (δ m) x * |F x|) := by
        filter_upwards [hBφ] with x hx
        rw [Real.norm_eq_abs] at hx ⊢
        have hxB : |φ x| ≤ max Bφ 0 := hx.trans (le_max_left _ _)
        simp only [θ, dk_cutT]
        set s := (t0 - x i) / δ m
        by_cases hs : 0 < s ∧ s < 1
        · have hxi : x i ∈ Ioo (t0 - δ m) t0 := by
            obtain ⟨h1, h2⟩ := hs
            rw [div_pos_iff_of_pos_right (hδ m)] at h1
            rw [div_lt_one (hδ m)] at h2
            constructor <;> linarith
          have hsl : slab i t0 (δ m) x = 1 := by simp [slab, hxi]
          rw [hsl, one_mul]
          have he : |(Pi.single k (1 : ℝ) : Cfg n) i| ≤ 1 := by
            by_cases hk : i = k
            · subst hk; simp
            · simp [hk]
          have hinv : 1 / δ m = (m : ℝ) + 1 := by simp only [δ]; field_simp
          rw [abs_mul, abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (hδ m)]
          calc |F x| * (|deriv smoothTransition s| * (|(Pi.single k (1 : ℝ) : Cfg n) i| / δ m) *
                |φ x|) ≤ |F x| * (Mθ * (1 / δ m) * max Bφ 0) := by
                gcongr
                · exact hMθ _
            _ = Mθ * max Bφ 0 * ((m : ℝ) + 1) * |F x| := by rw [hinv]; ring
        · have hz : deriv smoothTransition s = 0 := by
            rw [not_and_or, not_lt, not_lt] at hs
            rcases hs with h | h
            · exact deriv_smoothTransition_of_nonpos h
            · exact deriv_smoothTransition_of_one_le h
          rw [hz]; simp only [zero_mul, mul_zero, abs_zero]
          exact mul_nonneg (by positivity) (mul_nonneg (slab_nonneg _ _ _ _) (abs_nonneg _))
      calc ‖∫ x, F x * (dk k (θ m) x * φ x) ∂μN n‖
          ≤ ∫ x, Mθ * max Bφ 0 * ((m : ℝ) + 1) * (slab i t0 (δ m) x * |F x|) ∂μN n :=
            norm_integral_le_of_norm_le ((hsi m).const_mul _) hpt
        _ = _ := by rw [integral_const_mul]; ring
    have hlim := hslab.const_mul (Mθ * max Bφ 0)
    rw [mul_zero] at hlim
    exact squeeze_zero_norm hbound hlim
  have hlim := L1.add L2
  rw [add_zero] at hlim
  have heq : (fun m => ∫ x, F x * (θ m x * dk k φ x) ∂μN n +
      ∫ x, F x * (dk k (θ m) x * φ x) ∂μN n) =
      fun m => -∫ x, G x * (θ m x * φ x) ∂μN n := funext hm
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim L3.neg

end DFT.Continuum.Line
