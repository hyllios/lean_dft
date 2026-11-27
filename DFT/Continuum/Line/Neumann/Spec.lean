/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import ForMathlib.Analysis.InnerProductSpace.FormEigenbasis
import DFT.Continuum.Line.Neumann.HKc
import DFT.Continuum.Line.Neumann.Series

/-!
# Neumann orbitals for `H⁻¹` potentials

For `v ∈ H⁻¹`, the one-body Neumann operator `h_v = -d²/dx² + v` on `[0, 1]` has an orthonormal
eigenbasis of `L²(0, 1)` made of `H¹` functions, with eigenvalues `λ₀ ≤ λ₁ ≤ ⋯ → ∞`, and the
variational bound

`Σ_{j<N} λ_j ⟪φ_j, ψ⟫² + λ_N (‖ψ‖² - Σ_{j<N} ⟪φ_j, ψ⟫²) ≤ ∫ ψ'² + v(ψ²)`

(**`exists_neuOrbitals`**). This is `exists_formEigenbasis` for `V = H1E`, `H = L²(0, 1)` and the
form `q_v(e, h) = ⟪e', h'⟫ + v(e h)`.

* `bcfE`, `JE`: the embedding `H1E → C([0, 1]) → L²(0, 1)`; `JE_ae`, `norm_JE_sq`.
* `isCompactOperator_JE` (Arzelà–Ascoli: `|ψ(s) - ψ(t)| ≤ √|s - t| ‖ψ'‖`), `JE_injective`,
  `denseRange_JE` (the cosines are in the range), `not_finiteDimensional_HL`.
* `qvE`: the form; `qvE_self`, `qvE_symm`, `qvE_coercive` (`abs_v_sq_le`, `sq_le_H1N`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction

/-! ### The embedding `H¹(0, 1) → L²(0, 1)` -/

/-- `H1E` into bounded continuous functions on `[0, 1]`. -/
noncomputable def bcfE : H1E →L[ℝ] (Icc (0 : ℝ) 1 →ᵇ ℝ) :=
  (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) 1) ℝ ℝ).toLinearIsometry.toContinuousLinearMap.comp
    evE

lemma bcfE_apply (e : H1E) (t : Icc (0 : ℝ) 1) : bcfE e t = fnE e t := by
  simp [bcfE, evE_apply]

/-- **The embedding `H¹(0, 1) → L²(0, 1)`.** -/
noncomputable def JE : H1E →L[ℝ] HL := Jop.comp bcfE

lemma JE_ae (e : H1E) : (JE e : ℝ → ℝ) =ᵐ[vol01] fnE e := by
  filter_upwards [MemLp.coeFn_toLp (memLp_comp_projIcc (bcfE e)),
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  change (Jop (bcfE e) : ℝ → ℝ) x = _
  simp only [Jop, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
  rw [hx, bcfE_apply]
  simp [projIcc_of_mem _ (Ioo_subset_Icc_self hxI)]

lemma norm_JE_sq (e : H1E) : ‖JE e‖ ^ 2 = ∫ t, fnE e t ^ 2 ∂vol01 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [JE_ae e] with x hx
  simp [hx, sq]

lemma inner_JE (e h : H1E) : ⟪JE e, JE h⟫_ℝ = ∫ t, fnE e t * fnE h t ∂vol01 := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [JE_ae e, JE_ae h] with x hx hy
  simp [hx, hy, mul_comm]

/-- **The embedding is compact** (Arzelà–Ascoli). -/
theorem isCompactOperator_bcfE : IsCompactOperator bcfE := by
  set A := bcfE '' Metric.closedBall 0 1
  set R := ‖evE‖
  have hcpt : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (Icc (-R) R) isCompact_Icc A
      (fun g x hg => ?_) ?_
    · obtain ⟨e, he, rfl⟩ := hg
      rw [Metric.mem_closedBall, dist_zero_right] at he
      rw [bcfE_apply, mem_Icc, ← abs_le]
      exact (abs_fnE_le e x.2).trans (by nlinarith [norm_nonneg evE])
    · intro x0
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      refine ⟨ε ^ 2, by positivity, fun x hx g => ?_⟩
      obtain ⟨_, ⟨e, he, rfl⟩⟩ := g
      rw [Metric.mem_closedBall, dist_zero_right] at he
      simp only [Real.dist_eq, bcfE_apply, fnE]
      rw [add_sub_add_left_eq_sub]
      have h1 := abs_prim_sub_le_sqrt e.snd x0.2 x.2
      have h2 : ‖e.snd‖ ≤ 1 := (norm_snd_le e).trans he
      have hd : |(x0 : ℝ) - x| < ε ^ 2 := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] at hx; exact hx
      have h3 : √|(x0 : ℝ) - x| < ε := by
        rw [Real.sqrt_lt' hε]; exact hd
      calc |prim e.snd x0 - prim e.snd x| ≤ √|(x0 : ℝ) - x| * ‖e.snd‖ := h1
        _ ≤ √|(x0 : ℝ) - x| * 1 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
        _ < ε := by linarith
  refine ⟨closure A, hcpt, ?_⟩
  exact Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos)
    fun e he => subset_closure ⟨e, he, rfl⟩

theorem isCompactOperator_JE : IsCompactOperator JE := isCompactOperator_bcfE.clm_comp Jop

lemma fnE_zero_fn (t : ℝ) : fnE 0 t = 0 := by simp [fnE, prim]

/-- **The embedding is injective.** -/
theorem JE_injective : Function.Injective JE := by
  refine (injective_iff_map_eq_zero JE).2 fun e he => ?_
  have hae : fnE e =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun _ => 0 := by
    have h1 := JE_ae e
    have h2 : (JE e : ℝ → ℝ) =ᵐ[vol01] (0 : HL) := by
      rw [show JE e = 0 from he]
    filter_upwards [h1, h2, Lp.coeFn_zero ℝ 2 vol01] with x hx1 hx2 hx3
    rw [← hx1, hx2, hx3]; rfl
  have hc : ContinuousOn (fnE e) (Icc 0 1) := continuousOn_fnE e
  have hO : EqOn (fnE e) (fun _ => 0) (Ioo 0 1) :=
    Measure.eqOn_of_ae_eq hae (hc.mono Ioo_subset_Icc_self) continuousOn_const
      (by rw [interior_Ioo]; exact subset_closure)
  have hC : EqOn (fnE e) (fun _ => 0) (Icc 0 1) :=
    hO.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  exact eq_of_fnE fun t ht => by rw [hC ht, fnE_zero_fn]

/-- The cosine `c_k` as an element of `H1E`. -/
noncomputable def cnE (k : ℕ) : H1E := toE (h1N_of_C1 (contDiff_cn k))

lemma JE_cnE (k : ℕ) : JE (cnE k) = cb k := by
  rw [cb_apply]
  refine Lp.ext ?_
  filter_upwards [JE_ae (cnE k), toHL_ae (continuous_cn k), ae_restrict_mem measurableSet_Ioo]
    with x h1 h2 hx
  rw [h1, h2, cnE, fnE_toE _ (Ioo_subset_Icc_self hx)]

/-- **The embedding has dense range**: the cosines are in it. -/
theorem denseRange_JE : DenseRange JE := by
  have hsub : Submodule.span ℝ (range cb) ≤ LinearMap.range (JE : H1E →ₗ[ℝ] HL) :=
    Submodule.span_le.2 fun _ ⟨k, hk⟩ => ⟨cnE k, by rw [← hk]; exact JE_cnE k⟩
  have hd : Dense (Submodule.span ℝ (range cb) : Set HL) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 cb.dense_span
  exact hd.mono fun x hx => by
    obtain ⟨e, he⟩ := hsub hx
    exact ⟨e, he⟩

/-- `L²(0, 1)` is infinite-dimensional. -/
theorem not_finiteDimensional_HL : ¬ FiniteDimensional ℝ HL := fun _ => by
  have := cb.orthonormal.linearIndependent.finite
  exact not_finite ℕ

/-! ### The form `q_v(e, h) = ⟪e', h'⟫ + v(e h)` -/

lemma dE2_add_right (e h h' : H1E) : dE2 e (h + h') = dE2 e h + dE2 e h' := by
  rw [dE2_comm, dE2_add_left, dE2_comm h, dE2_comm h']

lemma dE2_smul_right (c : ℝ) (e h : H1E) : dE2 e (c • h) = c • dE2 e h := by
  rw [dE2_comm, dE2_smul_left, dE2_comm]

lemma dE2_self (e : H1E) : dE2 e e = dE e := by
  simp only [dE, dE2, sq, two_smul]

/-- **The one-body Neumann form** `q_v(e, h) = ⟪e', h'⟫ + v(e h)`. -/
noncomputable def qvE (v : PotH) : H1E →L[ℝ] H1E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun e h => ⟪e.snd, h.snd⟫_ℝ + v (dE2 e h))
      (fun e e' h => by
        simp only [WithLp.add_snd, inner_add_left, dE2_add_left, map_add]; ring)
      (fun c e h => by
        simp only [WithLp.smul_snd, real_inner_smul_left, dE2_smul_left, map_smul, smul_eq_mul]
        ring)
      (fun e h h' => by
        simp only [WithLp.add_snd, inner_add_right, dE2_add_right, map_add]; ring)
      (fun c e h => by
        simp only [WithLp.smul_snd, real_inner_smul_right, dE2_smul_right, map_smul, smul_eq_mul]
        ring))
    (1 + ‖v‖ * (1 + 2 * ‖evE‖)) fun e h => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      have h1 : |⟪e.snd, h.snd⟫_ℝ| ≤ ‖e‖ * ‖h‖ :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (norm_snd_le e) (norm_snd_le h) (norm_nonneg _) (norm_nonneg _))
      have h2 : |v (dE2 e h)| ≤ ‖v‖ * ((1 + 2 * ‖evE‖) * ‖e‖ * ‖h‖) := by
        rw [← Real.norm_eq_abs]
        exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_dE2_le e h) (norm_nonneg _))
      calc |⟪e.snd, h.snd⟫_ℝ + v (dE2 e h)| ≤ |⟪e.snd, h.snd⟫_ℝ| + |v (dE2 e h)| :=
            abs_add_le _ _
        _ ≤ (1 + ‖v‖ * (1 + 2 * ‖evE‖)) * ‖e‖ * ‖h‖ := by nlinarith

lemma qvE_apply (v : PotH) (e h : H1E) : qvE v e h = ⟪e.snd, h.snd⟫_ℝ + v (dE2 e h) := rfl

lemma qvE_self (v : PotH) (e : H1E) : qvE v e e = ‖e.snd‖ ^ 2 + v (dE e) := by
  rw [qvE_apply, real_inner_self_eq_norm_sq, dE2_self]

lemma qvE_symm (v : PotH) (e h : H1E) : qvE v e h = qvE v h e := by
  rw [qvE_apply, qvE_apply, real_inner_comm, dE2_comm]

/-- **Coercivity**: `q_v(e, e) ≥ (2/5) ‖e‖² - (2 + C_v) ‖J e‖²`. -/
lemma qvE_coercive (v : PotH) (e : H1E) :
    2 / 5 * ‖e‖ ^ 2 ≤ qvE v e e + (2 + cH v) * ‖JE e‖ ^ 2 := by
  have hψ := h1N_fnE e
  have hv := abs_v_sq_le v hψ
  rw [← dE_eq_sqE, kinM_fnE, ← norm_JE_sq] at hv
  have h0 := sq_le_H1N hψ (a := 4) (by norm_num) (t := 0) ⟨le_rfl, zero_le_one⟩
  rw [kinM_fnE, ← norm_JE_sq] at h0
  have hf0 : fnE e 0 = e.fst := by simp [fnE, prim_zero]
  rw [hf0] at h0
  have hn : ‖e‖ ^ 2 = e.fst ^ 2 + ‖e.snd‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [qvE_self, hn]
  have := neg_abs_le (v (dE e))
  nlinarith [cH_nonneg v, sq_nonneg ‖JE e‖]

/-! ### The orbitals -/

/-- **Neumann orbitals for an `H⁻¹` potential.** There are `φ_k ∈ H1E` whose images in
`L²(0, 1)` form a Hilbert basis, and `λ₀ ≤ λ₁ ≤ ⋯ → ∞`, with
`⟪φ_k', g'⟫ + v(φ_k g) = λ_k ⟪φ_k, g⟫` for all `g ∈ H¹`, and the variational bound. -/
theorem exists_neuOrbitals (v : PotH) :
    ∃ (φ : ℕ → H1E) (lam : ℕ → ℝ) (b : HilbertBasis ℕ ℝ HL), Monotone lam ∧
      Tendsto lam atTop atTop ∧ (∀ k, JE (φ k) = b k) ∧
      (∀ k g, ⟪(φ k).snd, g.snd⟫_ℝ + v (dE2 (φ k) g) = lam k * ⟪JE (φ k), JE g⟫_ℝ) ∧
      ∀ (N : ℕ) (ψ : H1E), ∑ j ∈ Finset.range N, lam j * ⟪b j, JE ψ⟫_ℝ ^ 2 +
        lam N * (‖JE ψ‖ ^ 2 - ∑ j ∈ Finset.range N, ⟪b j, JE ψ⟫_ℝ ^ 2) ≤
          ‖ψ.snd‖ ^ 2 + v (dE ψ) := by
  obtain ⟨φ, lam, b, hm, ht, hJ, heig, hbd⟩ := exists_formEigenbasis not_finiteDimensional_HL
    isCompactOperator_JE JE_injective denseRange_JE (qvE_symm v) (by norm_num : (0 : ℝ) < 2 / 5)
    (qvE_coercive v)
  exact ⟨φ, lam, b, hm, ht, hJ, fun k g => heig k g, fun N ψ => by
    rw [← qvE_self]; exact hbd N ψ⟩

end DFT.Continuum.Line
