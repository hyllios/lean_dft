/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Invariant

/-!
# Restricting antisymmetric `H¹₀` states to a half-space

For a fermionic `H¹₀` state `Φ` and `i ≠ j`, the restriction `1_{xᵢ < xⱼ} Φ` (extended by zero) has
weak derivatives `1_{xᵢ < xⱼ} ∂ₖΦ` (`isWD_half`): antisymmetric states vanish on the collision
planes in the weak sense.

* `isWD_half_C1`: for a `C¹` function vanishing on the walls and on the plane `xᵢ = xⱼ`; proof
  with the cutoffs `θ((xⱼ - xᵢ)/δ)` (`θ` the smooth step), the boundary term being controlled by
  `|P(x)| ≤ L (xⱼ - xᵢ)` (mean value theorem towards the plane).
* `isWD_half`: the general case, through the `C²` truncations (`trunc_mem`), which converge in
  `L²` with weakly convergent derivatives (`tendsto_trunc`, `tendsto_trunc_dk`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ}

/-! ### The smooth step -/

lemma deriv_smoothTransition_of_nonpos {s : ℝ} (hs : s ≤ 0) : deriv smoothTransition s = 0 := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hneg : ∀ t < 0, deriv smoothTransition t = 0 := fun t ht => by
    have : smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with r hr
      exact smoothTransition.zero_of_nonpos (le_of_lt hr)
    rw [this.deriv_eq]; simp
  rcases hs.lt_or_eq with h | h
  · exact hneg s h
  · subst h
    have h1 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio 0))
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hneg t ht).symm

lemma deriv_smoothTransition_of_one_le {s : ℝ} (hs : 1 ≤ s) : deriv smoothTransition s = 0 := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hgt : ∀ t > 1, deriv smoothTransition t = 0 := fun t ht => by
    have : smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds ht] with r hr
      exact smoothTransition.one_of_one_le (le_of_lt hr)
    rw [this.deriv_eq]; simp
  rcases hs.lt_or_eq with h | h
  · exact hgt s h
  · subst h
    have h1 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hgt t ht).symm

lemma deriv_smoothTransition_bound : ∃ M, ∀ s, |deriv smoothTransition s| ≤ M := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc 0 1))
  refine ⟨max M 0, fun s => ?_⟩
  by_cases h0 : s ≤ 0
  · rw [deriv_smoothTransition_of_nonpos h0, abs_zero]; exact le_max_right _ _
  by_cases h1 : 1 ≤ s
  · rw [deriv_smoothTransition_of_one_le h1, abs_zero]; exact le_max_right _ _
  push Not at h0 h1
  exact (Real.norm_eq_abs _ ▸ hM s ⟨h0.le, h1.le⟩).trans (le_max_left _ _)

/-! ### The `C¹` case -/

/-- The half-space `xᵢ < xⱼ`. -/
def Hij (i j : Fin (n + 1)) : Set (Cfg n) := {x | x i < x j}

lemma measurableSet_Hij (i j : Fin (n + 1)) : MeasurableSet (Hij (n := n) i j) :=
  measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

/-- The cutoff `θ((xⱼ - xᵢ)/δ)`. -/
noncomputable def cutH (i j : Fin (n + 1)) (δ : ℝ) (x : Cfg n) : ℝ :=
  smoothTransition ((x j - x i) / δ)

lemma contDiff_cutH (i j : Fin (n + 1)) (δ : ℝ) : ContDiff ℝ 1 (cutH (n := n) i j δ) :=
  (smoothTransition.contDiff (n := 1)).comp
    (by fun_prop : ContDiff ℝ 1 fun x : Cfg n => (x j - x i) / δ)

lemma dk_cutH (i j : Fin (n + 1)) (δ : ℝ) (k : Fin (n + 1)) (x : Cfg n) :
    dk k (cutH i j δ) x = deriv smoothTransition ((x j - x i) / δ) *
      (((Pi.single k (1 : ℝ) : Cfg n) j - (Pi.single k (1 : ℝ) : Cfg n) i) / δ) := by
  set L : Cfg n →L[ℝ] ℝ :=
    δ⁻¹ • ((ContinuousLinearMap.proj j : Cfg n →L[ℝ] ℝ) - ContinuousLinearMap.proj i)
  have hin : HasFDerivAt (fun y : Cfg n => (y j - y i) / δ) L x := by
    have hj : HasFDerivAt (fun y : Cfg n => y j) (ContinuousLinearMap.proj j : Cfg n →L[ℝ] ℝ) x :=
      hasFDerivAt_apply j x
    have hi : HasFDerivAt (fun y : Cfg n => y i) (ContinuousLinearMap.proj i : Cfg n →L[ℝ] ℝ) x :=
      hasFDerivAt_apply i x
    have := (hj.sub hi).const_mul δ⁻¹
    convert this using 1
    funext y; simp only [Pi.sub_apply]; rw [div_eq_inv_mul]
  have h := ((smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    ((x j - x i) / δ)).hasDerivAt.comp_hasFDerivAt x hin
  change fderiv ℝ (smoothTransition ∘ fun y : Cfg n => (y j - y i) / δ) x (Pi.single k 1) = _
  rw [h.fderiv]
  simp only [L, smul_apply, sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

lemma tendsto_cutH (i j : Fin (n + 1)) (x : Cfg n) :
    Tendsto (fun m : ℕ => cutH i j (1 / ((m : ℝ) + 1)) x) atTop
      (𝓝 ((Hij i j).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x i < x j
  · rw [indicator_of_mem (show x ∈ Hij i j from hx)]
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨m0, hm0⟩ := exists_nat_gt (1 / (x j - x i))
    filter_upwards [eventually_ge_atTop m0] with m hm
    have hd : 0 < x j - x i := by linarith
    refine (smoothTransition.one_of_one_le ?_).symm
    have h1 : (1 : ℝ) / (x j - x i) < m + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hm; linarith
    rw [div_lt_iff₀ hd] at h1
    rw [div_div_eq_mul_div, div_one]
    linarith
  · rw [indicator_of_notMem (show x ∉ Hij i j from hx)]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun m => ?_)
    refine (smoothTransition.zero_of_nonpos ?_).symm
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 hx]) (by positivity)

/-- A `C¹` function vanishing on the plane `xᵢ = xⱼ` grows at most linearly away from it. -/
lemma abs_le_of_plane {P : Cfg n → ℝ} (hP : ContDiff ℝ 1 P) {i j : Fin (n + 1)} (hij : i ≠ j)
    (hplane : ∀ x, x i = x j → P x = 0) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ CubeC n, x i ≤ x j → |P x| ≤ C * (x j - x i) := by
  obtain ⟨C, hC⟩ := isCompact_cubeC.exists_bound_of_continuousOn
    (hP.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx hle => ?_⟩
  set c := (x i + x j) / 2 with hc
  set y : Cfg n := Function.update (Function.update x i c) j c
  have hyi : y i = c := by simp [y, Function.update_of_ne hij]
  have hyj : y j = c := by simp [y]
  have hy : y ∈ CubeC n := Set.mem_univ_pi.2 fun l => by
    have hxl := Set.mem_univ_pi.1 hx l
    have hxi := Set.mem_univ_pi.1 hx i
    have hxj := Set.mem_univ_pi.1 hx j
    by_cases hlj : l = j
    · subst hlj; rw [hyj]; exact ⟨by linarith [hxi.1, hxl.1, hc], by linarith [hxi.2, hxl.2, hc]⟩
    by_cases hli : l = i
    · subst hli; rw [hyi]; exact ⟨by linarith [hxj.1, hxl.1, hc], by linarith [hxj.2, hxl.2, hc]⟩
    simp only [y, Function.update_of_ne hlj, Function.update_of_ne hli]; exact hxl
  have hPy : P y = 0 := hplane y (by rw [hyi, hyj])
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (C := max C 0)
    (fun z _ => (hP.differentiable one_ne_zero) z)
    (fun z hz => (hC z hz).trans (le_max_left C 0))
    (convex_pi fun _ _ => convex_Icc (0 : ℝ) 1) hy hx
  rw [hPy, sub_zero, Real.norm_eq_abs] at hmv
  refine hmv.trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
  refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun l => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  by_cases hlj : l = j
  · subst hlj; rw [hyj, abs_le]; constructor <;> linarith [hc]
  by_cases hli : l = i
  · subst hli; rw [hyi, abs_le]; constructor <;> linarith [hc]
  simp only [y, Function.update_of_ne hlj, Function.update_of_ne hli, sub_self, abs_zero]
  linarith

lemma abs_single_sub_le (k i j : Fin (n + 1)) (hij : i ≠ j) :
    |(Pi.single k (1 : ℝ) : Cfg n) j - (Pi.single k (1 : ℝ) : Cfg n) i| ≤ 1 := by
  by_cases hkj : j = k
  · subst hkj; simp [Pi.single_eq_of_ne hij]
  · by_cases hki : i = k
    · subst hki; simp [Pi.single_eq_of_ne (Ne.symm hij)]
    · simp [Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hki]

/-- **The half-space restriction, `C¹` case.** -/
theorem isWD_half_C1 {P : Cfg n → ℝ} (hP : ContDiff ℝ 1 P)
    (hwall : ∀ x k, (x k = 0 ∨ x k = 1) → P x = 0) {i j : Fin (n + 1)} (hij : i ≠ j)
    (hplane : ∀ x, x i = x j → P x = 0) (k : Fin (n + 1)) :
    IsWD k ((Hij i j).indicator P) ((Hij i j).indicator (dk k P)) := by
  set H := Hij (n := n) i j
  have hdP := continuous_dk_of_C1 hP k
  refine ⟨(memLp_cont hdP).indicator (measurableSet_Hij i j).nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ k
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  set θ : ℕ → Cfg n → ℝ := fun m => cutH i j (δ m)
  have hθc : ∀ m, ContDiff ℝ 1 (θ m) := fun m => contDiff_cutH i j _
  have hdθc : ∀ m, Continuous (dk k (θ m)) := fun m => continuous_dk_of_C1 (hθc m) k
  have hθ01 : ∀ m x, 0 ≤ θ m x ∧ θ m x ≤ 1 := fun m x =>
    ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  -- the identity for each cutoff
  have hm : ∀ m, ∫ x, P x * (θ m x * dk k φ x) ∂μN n + ∫ x, P x * (dk k (θ m) x * φ x) ∂μN n =
      -∫ x, dk k P x * (θ m x * φ x) ∂μN n := fun m => by
    have h := (isWD_of_C1 hP hwall k).2 (fun x => θ m x * φ x) ((hθc m).mul hφ)
    simp only [dk_mul ((hθc m).differentiable one_ne_zero) (hφ.differentiable one_ne_zero)] at h
    rw [← integral_add (f := fun x => P x * (θ m x * dk k φ x))
      (g := fun x => P x * (dk k (θ m) x * φ x))
      (integrableN (hP.continuous.mul ((hθc m).continuous.mul hdφ)))
      (integrableN (hP.continuous.mul ((hdθc m).mul hφ.continuous)))]
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) h
    ring
  -- first limit
  have L1 : Tendsto (fun m => ∫ x, P x * (θ m x * dk k φ x) ∂μN n) atTop
      (𝓝 (∫ x, H.indicator P x * dk k φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |P x * dk k φ x|)
      (fun m => (hP.continuous.mul ((hθc m).continuous.mul hdφ)).aestronglyMeasurable)
      (integrableN (hP.continuous.mul hdφ).abs) (fun m => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, show P x * (θ m x * dk k φ x) = θ m x * (P x * dk k φ x) by ring,
        abs_mul, abs_of_nonneg (hθ01 m x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθ01 m x).2
    · have h := ((tendsto_cutH i j x).mul_const (dk k φ x)).const_mul (P x)
      convert h using 2
      by_cases hx : x ∈ H <;> simp [H, hx]
  -- third limit
  have L3 : Tendsto (fun m => ∫ x, dk k P x * (θ m x * φ x) ∂μN n) atTop
      (𝓝 (∫ x, H.indicator (dk k P) x * φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |dk k P x * φ x|)
      (fun m => (hdP.mul ((hθc m).continuous.mul hφ.continuous)).aestronglyMeasurable)
      (integrableN (hdP.mul hφ.continuous).abs) (fun m => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, show dk k P x * (θ m x * φ x) = θ m x * (dk k P x * φ x) by ring,
        abs_mul, abs_of_nonneg (hθ01 m x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθ01 m x).2
    · have h := ((tendsto_cutH i j x).mul_const (φ x)).const_mul (dk k P x)
      convert h using 2
      by_cases hx : x ∈ H <;> simp [H, hx]
  -- the boundary term vanishes
  obtain ⟨C, hC0, hC⟩ := abs_le_of_plane hP hij hplane
  obtain ⟨Mθ, hMθ⟩ := deriv_smoothTransition_bound
  obtain ⟨Bφ, hBφ⟩ := ae_bound_cont hφ.continuous
  have L2 : Tendsto (fun m => ∫ x, P x * (dk k (θ m) x * φ x) ∂μN n) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂μN n := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => C * Mθ * Bφ)
      (fun m => (hP.continuous.mul ((hdθc m).mul hφ.continuous)).aestronglyMeasurable)
      (integrable_const _) (fun m => ?_) (ae_of_all _ fun x => ?_)
    · filter_upwards [hBφ, ae_restrict_mem measurableSet_cube] with x hx hxc
      rw [Real.norm_eq_abs] at hx ⊢
      have hMθ0 : 0 ≤ Mθ := (abs_nonneg _).trans (hMθ 0)
      have hB0 : 0 ≤ Bφ := (abs_nonneg _).trans hx
      simp only [θ, dk_cutH]
      set d := x j - x i
      by_cases hd : 0 < d / δ m ∧ d / δ m < 1
      · have hdpos : 0 < d := by
          have := hd.1; rwa [div_pos_iff_of_pos_right (hδ m)] at this
        have hdlt : d < δ m := by
          have := hd.2; rwa [div_lt_one (hδ m)] at this
        have hPx := hC x (cube_subset hxc) (by linarith)
        rw [abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos (hδ m)]
        have h1 : |(Pi.single k (1 : ℝ) : Cfg n) j - (Pi.single k (1 : ℝ) : Cfg n) i| / δ m ≤
            1 / δ m := div_le_div_of_nonneg_right (abs_single_sub_le k i j hij) (hδ m).le
        calc |P x| * (|deriv smoothTransition (d / δ m)| *
              (|(Pi.single k (1 : ℝ) : Cfg n) j - (Pi.single k (1 : ℝ) : Cfg n) i| / δ m) * |φ x|)
            ≤ (C * δ m) * (Mθ * (1 / δ m) * Bφ) := by
              gcongr
              · exact hPx.trans (mul_le_mul_of_nonneg_left hdlt.le hC0)
              · exact hMθ _
          _ = C * Mθ * Bφ := by have := (hδ m).ne'; field_simp
      · have hz : deriv smoothTransition (d / δ m) = 0 := by
          rw [not_and_or, not_lt, not_lt] at hd
          rcases hd with h | h
          · exact deriv_smoothTransition_of_nonpos h
          · exact deriv_smoothTransition_of_one_le h
        rw [hz]; simp only [zero_mul, mul_zero, abs_zero]
        positivity
    · refine tendsto_const_nhds.congr' ?_
      simp only [θ, dk_cutH]
      by_cases hx : 0 < x j - x i
      · obtain ⟨m0, hm0⟩ := exists_nat_gt (1 / (x j - x i))
        filter_upwards [eventually_ge_atTop m0] with m hmm
        have h1 : (1 : ℝ) / (x j - x i) < m + 1 := by
          have := (Nat.cast_le (α := ℝ)).2 hmm; linarith
        rw [div_lt_iff₀ hx] at h1
        rw [deriv_smoothTransition_of_one_le (by
          simp only [δ]; rw [div_div_eq_mul_div, div_one]; linarith)]
        ring
      · refine Eventually.of_forall fun m => ?_
        beta_reduce
        rw [deriv_smoothTransition_of_nonpos (div_nonpos_of_nonpos_of_nonneg
          (show x j - x i ≤ 0 by linarith) (hδ m).le)]
        ring
  have hlim := L1.add L2
  rw [add_zero] at hlim
  have heq : (fun m => ∫ x, P x * (θ m x * dk k φ x) ∂μN n +
      ∫ x, P x * (dk k (θ m) x * φ x) ∂μN n) =
      fun m => -∫ x, dk k P x * (θ m x * φ x) ∂μN n := funext hm
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim L3.neg

/-! ### The fermionic case -/

/-- A fermionic `C²` state vanishes on the collision plane `xᵢ = xⱼ`. -/
lemma fer_plane {P : Cfg n → ℝ} (hP : P ∈ Dom .fer n) {i j : Fin (n + 1)} (hij : i ≠ j) (x : Cfg n)
    (hx : x i = x j) : P x = 0 := by
  have h := hP.2.1 (Equiv.swap i j) x
  have hpm : pm (Equiv.swap i j) x = x := by
    funext l
    simp only [pm_apply]
    by_cases hli : l = i
    · subst hli; simp [hx]
    · by_cases hlj : l = j
      · subst hlj; simp [hx]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
  rw [hpm, ch_fer, sgn, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  linarith

/-- **Antisymmetric `H¹₀` states restricted to a half-space.** For a fermionic `H¹₀` state `Φ`
and `i ≠ j`, `1_{xᵢ < xⱼ} Φ` has weak derivatives `1_{xᵢ < xⱼ} ∂ₖΦ`. -/
theorem isWD_half {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW .fer n) {i j : Fin (n + 1)} (hij : i ≠ j)
    (k : Fin (n + 1)) : IsWD k ((Hij i j).indicator Φ) ((Hij i j).indicator (dW k Φ)) := by
  set H := Hij (n := n) i j
  have hHm := measurableSet_Hij (n := n) i j
  refine ⟨(memLp_dW hΦ k).indicator hHm.nullMeasurableSet, fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ k
  have hM : ∀ M, ∫ x, H.indicator (trunc M Φ) x * dk k φ x ∂μN n =
      -∫ x, H.indicator (dk k (trunc M Φ)) x * φ x ∂μN n := fun M =>
    (isWD_half_C1 ((trunc_mem hΦ M).1.of_le (by norm_num)) (trunc_mem hΦ M).2.2 hij
      (fer_plane (trunc_mem hΦ M) hij) k).2 φ hφ
  have hg1 : MemLp (H.indicator (dk k φ)) 2 (μN n) :=
    (memLp_cont hdφ).indicator hHm.nullMeasurableSet
  have hg2 : MemLp (H.indicator φ) 2 (μN n) :=
    (memLp_cont hφ.continuous).indicator hHm.nullMeasurableSet
  have e1 : ∀ f : Cfg n → ℝ, ∫ x, H.indicator f x * dk k φ x ∂μN n =
      ∫ x, f x * H.indicator (dk k φ) x ∂μN n := fun f =>
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ H <;> simp [hx])
  have e2 : ∀ f : Cfg n → ℝ, ∫ x, H.indicator f x * φ x ∂μN n =
      ∫ x, H.indicator φ x * f x ∂μN n := fun f =>
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ H <;> simp [hx, mul_comm])
  have L1 := tendsto_integral_mul_of_L2 (fun M => memLp_cont (continuous_trunc M Φ)) hΦ.1 hg1
    (tendsto_trunc hΦ.1)
  have L2 := tendsto_trunc_dk hΦ k hg2
  simp only [← e1] at L1
  simp only [← e2] at L2
  have heq : (fun M => ∫ x, H.indicator (trunc M Φ) x * dk k φ x ∂μN n) =
      fun M => -∫ x, H.indicator (dk k (trunc M Φ)) x * φ x ∂μN n := funext hM
  rw [heq] at L1
  exact tendsto_nhds_unique L1 L2.neg

end DFT.Continuum.Line
