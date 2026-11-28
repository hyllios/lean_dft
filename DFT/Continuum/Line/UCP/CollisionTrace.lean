/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Pittalis
-/
import ForMathlib.Analysis.Sobolev.CubeTrace
import DFT.Continuum.Line.UCP.Chain

/-!
# Coordinate collision traces for weak Dirichlet states

Sine truncations identify the continuous coordinate-line representatives and give
strong L² convergence of the classical restrictions to each collision trace.
-/

namespace DFT.Continuum.Line.CollisionTrace

open MeasureTheory MeasureTheory.UnitCube Set SturmLiouville Filter Topology

variable {n : ℕ}

theorem derivative_trunc {Φ : Cfg n → ℝ} (h : H1W Φ) (j : Fin (n + 1)) :
    Tendsto (fun m => ∫ x, (dW j Φ x - dk j (trunc m Φ) x) ^ 2 ∂μN n) atTop (𝓝 0) := by
  let E := fun k => ∫ x, dW k Φ x * dW k Φ x ∂μN n
  let X := fun k m => ∫ x, dW k Φ x * dk k (trunc m Φ) x ∂μN n
  have lim (k) : Tendsto (X k) atTop (𝓝 (E k)) := tendsto_trunc_dk h k (memLp_dW_H h k)
  have limsum := tendsto_finsetSum Finset.univ (fun k _ => lim k)
  have bound : Tendsto (fun m => 2 * ((∑ k, E k) - ∑ k, X k m)) atTop (𝓝 0) := by
    simpa using (limsum.const_sub (∑ k, E k)).const_mul 2
  refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun m => ?_) bound
  let D := fun k => dk k (trunc m Φ)
  have hc k : Continuous (D k) := continuous_dk_of_C1 ((contDiff_trunc m Φ).of_le (by norm_num)) k
  let B := fun k => ∫ x, D k x * D k x ∂μN n
  let err := fun k => ∫ x, (dW k Φ x - D k x) ^ 2 ∂μN n
  have energy := kin_trunc_le h m
  change (∫ x, ∑ k, D k x * D k x ∂μN n) ≤ ∑ k, E k at energy
  rw [integral_finsetSum (f := fun k x => D k x * D k x) _
    (fun k _ => integrableN ((hc k).mul (hc k)))] at energy
  change ∑ k, B k ≤ ∑ k, E k at energy
  have expansion k : err k = E k + B k - 2 * X k m := by
    have hf := memLp_dW_H h k
    have hg := memLp_cont (hc k)
    dsimp only [err, E, B, X]
    rw [← integral_add (int_mul_L2 hf hf) (int_mul_L2 hg hg), ← integral_const_mul,
      ← integral_sub (f := fun x => dW k Φ x * dW k Φ x + D k x * D k x)
        (g := fun x => 2 * (dW k Φ x * D k x))
        ((int_mul_L2 hf hf).add (int_mul_L2 hg hg)) ((int_mul_L2 hf hg).const_mul 2)]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have le := Finset.single_le_sum (f := err)
    (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ j)
  change err j ≤ _
  refine le.trans ?_
  simp_rw [expansion]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

theorem smooth_primitive {P : Cfg n → ℝ} (hc : ContDiff ℝ 1 P)
    (hw : ∀ x k, x k = 0 → P x = 0) (k : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    primitive k (dk k P) y t = P (line k y t) := by
  unfold primitive
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_ins hc.differentiable_one k y s)
    (((continuous_dk_of_C1 hc k).comp (continuous_ins k y)).intervalIntegrable _ _),
    hw _ k (Fin.insertNth_apply_same ..), sub_zero]

/-- A common subsequence on almost every line converges at every point to the primitive,
and almost everywhere to the original state. -/
theorem slice_approx {Φ : Cfg n → ℝ} (h : H1W Φ) (k : Fin (n + 1)) :
    ∃ s : ℕ → ℕ, ∀ᵐ y ∂Sine.piM n,
      (∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun m => trunc (s m) Φ (line k y t)) atTop
        (𝓝 (primitive k (dW k Φ) y t))) ∧
      (∀ᵐ t ∂vol01, primitive k (dW k Φ) y t = Φ (line k y t)) := by
  obtain ⟨r, hr, hstate⟩ := exists_ae_subseq (fun m => memLp_cont (continuous_trunc m Φ))
    h.1 (tendsto_trunc h.1)
  let d := fun m x => dW k Φ x - dk k (trunc (r m) Φ) x
  have hd m : MemLp (d m) 2 (μN n) := (memLp_dW_H h k).sub (memLp_cont
    (continuous_dk_of_C1 ((contDiff_trunc _ Φ).of_le (by norm_num)) k))
  let e := fun (m : ℕ) (y : Fin n → ℝ) => ∫ t, |d m (line k y t)| ∂vol01
  have hp m := line_int k ((hd m).integrable one_le_two).abs
  have hi m : Integrable (e m) (Sine.piM n) := (hp m).integral_prod_left
  have hn m y : 0 ≤ e m y := integral_nonneg fun _ => abs_nonneg _
  have hl : Tendsto (fun m => ∫ y, e m y ∂Sine.piM n) atTop (𝓝 0) := by
    have lim := ((derivative_trunc h k).comp hr.tendsto_atTop).sqrt.mul_const
      (Real.sqrt (∫ _ : Cfg n, (1 : ℝ) ^ 2 ∂μN n))
    refine squeeze_zero (fun m => integral_nonneg (hn m)) (fun m => ?_) (by simpa using lim)
    change (∫ y, ∫ t, |d m (line k y t)| ∂vol01 ∂Sine.piM n) ≤ _
    rw [line_fubini (F := fun x => |d m x|) k ((hd m).integrable one_le_two).abs]
    have aux := abs_integral_mul_le ((hd m).norm) (memLp_const (1 : ℝ) (μ := μN n) (p := 2))
    simpa [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (d m x))), d]
      using aux
  obtain ⟨q, hq, hlim⟩ := vanishing_subsequence hi hn hl
  refine ⟨r ∘ q, ?_⟩
  have hG := (line_int k ((memLp_dW_H h k).integrable one_le_two)).prod_right_ae
  filter_upwards [hG, hlim, line_ae k hstate] with y hy hlimy hyP
  have uniform (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Tendsto
      (fun m => trunc (r (q m)) Φ (line k y t)) atTop (𝓝 (primitive k (dW k Φ) y t)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) hlimy
    let P := trunc (r (q m)) Φ
    have hc : ContDiff ℝ 1 P := (contDiff_trunc _ Φ).of_le (by norm_num)
    have hD : Continuous (fun s => dk k P (line k y s)) :=
      (continuous_dk_of_C1 hc k).comp (continuous_ins k y)
    have hyI : IntervalIntegrable (fun t => dW k Φ (line k y t)) volume 0 t :=
      (interval_of_line hy).mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl ht.2)
    change dist (P (line k y t)) _ ≤ _
    rw [Real.dist_eq, abs_sub_comm, ← smooth_primitive hc (fun x l hx =>
      trunc_wall _ Φ x l (Or.inl hx)) k y t]
    unfold primitive
    rw [← intervalIntegral.integral_sub hyI (hD.intervalIntegrable _ _)]
    apply abs_primitive_le _ le_rfl ht.1 ht.2
    exact hy.sub (hD.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  refine ⟨uniform, ?_⟩
  filter_upwards [hyP, ae_restrict_mem (μ := volume) (measurableSet_Ioo (α := ℝ) (a := 0) (b := 1))]
    with t hp ht
  exact tendsto_nhds_unique (uniform t (Ioo_subset_Icc_self ht)) (hp.comp hq.tendsto_atTop)

/-- The collision between particle k and particle k.succAbove j. -/
noncomputable def trace (k : Fin (n + 1)) (j : Fin n) (Φ : Cfg n → ℝ) (h : H1W Φ) :
    Lp ℝ 2 (Sine.piM n) := faceTrace k j (dW k Φ) (memLp_dW_H h k)

theorem trace_zero {Φ : Cfg n → ℝ} (h : H1W Φ) (k : Fin (n + 1)) (j : Fin n) :
    trace k j Φ h = 0 ↔ ∀ᵐ y ∂Sine.piM n, face k j (dW k Φ) y = 0 := by
  have he : ⇑(trace k j Φ h) =ᵐ[Sine.piM n] face k j (dW k Φ) :=
    MemLp.coeFn_toLp (UnitCube.face_mem k j (memLp_dW_H h k))
  constructor
  · intro hz
    exact he.symm.trans (hz ▸ Lp.coeFn_zero ℝ 2 _)
  · intro hz
    change face k j (dW k Φ) =ᵐ[Sine.piM n] 0 at hz
    exact Lp.ext (he.trans (hz.trans (Lp.coeFn_zero ℝ 2 _).symm))

/-- Girardeau images have the same absolute value on a collision face as their preimages. -/
theorem face_sq_congr {Φ Ψ : Cfg n → ℝ} (h : H1W Φ) (h' : H1W Ψ)
    (he : ∀ᵐ x ∂μN n, Φ x ^ 2 = Ψ x ^ 2) (k : Fin (n + 1)) (j : Fin n) :
    ∀ᵐ y ∂Sine.piM n, face k j (dW k Φ) y ^ 2 = face k j (dW k Ψ) y ^ 2 := by
  obtain ⟨_, hs⟩ := slice_approx h k
  obtain ⟨_, hs'⟩ := slice_approx h' k
  filter_upwards [hs, hs', line_ae k he, coordinate_interior j,
    UnitCube.slice_mem k (memLp_dW_H h k),
    UnitCube.slice_mem k (memLp_dW_H h' k)] with y hy hy' heq hj hG hG'
  apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure ℝ)) (U := Ioo 0 1)
    (f := fun t => primitive k (dW k Φ) y t ^ 2) (g := fun t => primitive k (dW k Ψ) y t ^ 2)
    _ isOpen_Ioo _ _ hj
  · filter_upwards [hy.2, hy'.2, heq] with t a b c
    simpa only [a, b] using c
  · exact ((line_ac (hG.integrable one_le_two)).continuousOn.pow 2).mono
      (by rw [uIcc01]; exact Ioo_subset_Icc_self)
  · exact ((line_ac (hG'.integrable one_le_two)).continuousOn.pow 2).mono
      (by rw [uIcc01]; exact Ioo_subset_Icc_self)

theorem trace_smooth {P : Cfg n → ℝ} (hc : ContDiff ℝ 1 P)
    (hw : ∀ x k, (x k = 0 ∨ x k = 1) → P x = 0) (h : H1W P) (k : Fin (n + 1)) (j : Fin n) :
    ⇑(trace k j P h) =ᵐ[Sine.piM n] fun y => P (line k y (y j)) := by
  refine (MemLp.coeFn_toLp (UnitCube.face_mem k j (memLp_dW_H h k))).trans ?_
  filter_upwards [line_ae k (dW_ae_eq (isWD_of_C1 hc hw k)), coordinate_interior j] with y hy ht
  change (∫ s in (0 : ℝ)..y j, dW k P (line k y s)) = _
  refine Eq.trans ?_ (smooth_primitive hc (fun x l hx => hw x l (Or.inl hx)) k y (y j))
  unfold primitive
  rw [intervalIntegral.integral_of_le ht.1.le, intervalIntegral.integral_of_le ht.1.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right ht.2.le) hy)

/-- Quantitative continuity in the directional Sobolev seminorm. -/
theorem trace_stability {Φ Ψ : Cfg n → ℝ} (h : H1W Φ) (h' : H1W Ψ) (k : Fin (n + 1)) (j : Fin n) :
    (∫ y, (trace k j Φ h y - trace k j Ψ h' y) ^ 2 ∂Sine.piM n) ≤
      ∫ x, (dW k Φ x - dW k Ψ x) ^ 2 ∂μN n := by
  exact faceTrace_sub_bound k j (memLp_dW_H h k) (memLp_dW_H h' k)

/-- The L² trace is the continuous extension of ordinary restriction, as witnessed by
the dense sequence of smooth Dirichlet sine truncations. -/
theorem restrictions_converge {Φ : Cfg n → ℝ} (h : H1W Φ) (k : Fin (n + 1)) (j : Fin n) :
    Tendsto (fun m => ∫ y, (trace k j Φ h y - trunc m Φ (line k y (y j))) ^ 2 ∂Sine.piM n)
      atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun m => ?_)
    (derivative_trunc h k)
  let P := trunc m Φ
  have hc : ContDiff ℝ 1 P := (contDiff_trunc m Φ).of_le (by norm_num)
  have hw := trunc_wall m Φ
  have hP : H1W P := ⟨memLp_cont hc.continuous, fun l => ⟨_, isWD_of_C1 hc hw l⟩⟩
  have hface := trace_smooth hc hw hP k j
  have hd := dW_ae_eq (isWD_of_C1 hc hw k)
  calc
    _ = ∫ y, (trace k j Φ h y - trace k j P hP y) ^ 2 ∂Sine.piM n := by
      apply integral_congr_ae
      filter_upwards [hface] with y hy
      rw [hy]
    _ ≤ _ := trace_stability h hP k j
    _ = _ := integral_congr_ae (hd.mono fun x hx => by simp only [hx, P])

end DFT.Continuum.Line.CollisionTrace
