/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.TDDFT.Dynamics
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Existence and uniqueness of lattice TDDFT (Farzanehpour–Tokatly Theorem 1)

Given a target density `n(t)` with continuous `n̈`, the potential is eliminated with the
force-balance equation: on `Ω = {ψ : det(K(ψ) + 𝟙𝟙ᵀ) ≠ 0}`, `v(ψ, s) = (K(ψ) + 𝟙𝟙ᵀ)⁻¹ (q(ψ) - s)`
(`vfb`) is the unique potential with `Σ_i v_i = 0` and `K(ψ) v = q(ψ) - s` (`vfb_spec`,
`vfb_unique`). Inserting it into the Schrödinger equation gives a nonlinear Schrödinger equation
(NLSE) whose right-hand side is smooth in `ψ` on `Ω` (Cramer's rule, `contDiffAt_field`).

* `td_existence`: from an initial state in `Ω` consistent with `n(t₀)` and `ṅ(t₀)`, there is a
  solution on an interval around `t₀` whose density is `n(t)` (Picard–Lindelöf, then `ρ̈ = n̈` with
  matching initial data).
* `td_uniqueness`: any trajectory with potential `v'` (gauge `Σ_i v'_i = 0`) and density `n(t)`
  starting from the same state coincides with it near `t₀`, and `v' = v(ψ, n̈)`.
-/

namespace DFT

open Matrix Set Filter Topology Metric

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

/-- The all-ones matrix `𝟙𝟙ᵀ` (gauge fixing). -/
def onesM : Matrix V V ℝ := Matrix.of fun _ _ => 1

/-- `K(ψ) + 𝟙𝟙ᵀ`. -/
def kJ (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Matrix V V ℝ :=
  kfb H0 n ψ + onesM

/-- The potential determined by the state and the second time derivative `s` of the density. -/
noncomputable def vfb (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (s : V → ℝ) :
    V → ℝ :=
  (kJ H0 n ψ)⁻¹ *ᵥ (fun i => qsrc H0 n ψ i - s i)

omit [DecidableEq V] in
lemma onesM_mulVec (v : V → ℝ) : (onesM : Matrix V V ℝ) *ᵥ v = fun _ => ∑ j, v j := by
  funext i; simp [onesM, mulVec, dotProduct]

section algebra

variable {H0 : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hH0 : H0.IsSymm)
  (hN : ∀ c, ∑ i, n i c = Ntot)
include hH0 hN

/-- **The force balance determines the potential** (gauge `Σ v = 0`). -/
theorem vfb_spec [Nonempty V] {ψ : (C → ℝ) × (C → ℝ)} {s : V → ℝ}
    (hdet : (kJ H0 n ψ).det ≠ 0) (hs : ∑ i, s i = 0) :
    ∑ j, vfb H0 n ψ s j = 0 ∧ ∀ i, ∑ j, kfb H0 n ψ i j * vfb H0 n ψ s j = qsrc H0 n ψ i - s i := by
  set v := vfb H0 n ψ s
  have hinv : kJ H0 n ψ *ᵥ v = fun i => qsrc H0 n ψ i - s i := by
    simp only [v, vfb, mulVec_mulVec]
    rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  have hsplit : ∀ i, (kJ H0 n ψ *ᵥ v) i = (∑ j, kfb H0 n ψ i j * v j) + ∑ j, v j := by
    intro i
    simp [kJ, mulVec, dotProduct, add_mul, Finset.sum_add_distrib, onesM]
  -- summing the equations: the `K` part drops out
  have hsum : (Fintype.card V : ℝ) * ∑ j, v j = 0 := by
    have h1 : ∑ i, (kJ H0 n ψ *ᵥ v) i = 0 := by
      rw [hinv]; simp only [Finset.sum_sub_distrib, qsrc_sum H0 hN, hs, sub_zero]
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      at h1
    rw [Finset.sum_comm] at h1
    simp only [← Finset.sum_mul, kfb_sum_left H0 hN hH0, zero_mul, Finset.sum_const_zero,
      zero_add] at h1
    exact h1
  have hv0 : ∑ j, v j = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h (by exact_mod_cast Fintype.card_ne_zero)
    · exact h
  refine ⟨hv0, fun i => ?_⟩
  have := congrFun hinv i
  rw [hsplit, hv0, add_zero] at this
  exact this

omit hH0 hN in
/-- **Uniqueness of the potential** in the gauge `Σ v = 0`. -/
theorem vfb_unique {ψ : (C → ℝ) × (C → ℝ)} {s v : V → ℝ} (hdet : (kJ H0 n ψ).det ≠ 0)
    (hv : ∑ j, v j = 0) (hK : ∀ i, ∑ j, kfb H0 n ψ i j * v j = qsrc H0 n ψ i - s i) :
    v = vfb H0 n ψ s := by
  have h : kJ H0 n ψ *ᵥ v = fun i => qsrc H0 n ψ i - s i := by
    funext i
    have h1 : ((onesM : Matrix V V ℝ) *ᵥ v) i = 0 := by rw [onesM_mulVec]; exact hv
    simp only [kJ, add_mulVec, Pi.add_apply, h1, add_zero]
    rw [← hK i]; simp [mulVec, dotProduct]
  rw [vfb, ← h, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]

end algebra

section smooth

variable (H0 : Matrix C C ℝ) (n : V → C → ℝ)

/-- Points of the extended phase space: state and second time derivative of the density. -/
abbrev PS (C V : Type*) := ((C → ℝ) × (C → ℝ)) × (V → ℝ)

omit [DecidableEq C] [DecidableEq V] in
lemma contDiff_Qf (A : Matrix C C ℝ) : ContDiff ℝ ⊤ (fun p : PS C V => Qf A p.1) := by
  unfold Qf
  simp only [dotProduct, mulVec]
  fun_prop

lemma contDiff_det_of_entries {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : X → Matrix V V ℝ) (h : ∀ i j, ContDiff ℝ ⊤ (fun x => M x i j)) :
    ContDiff ℝ ⊤ (fun x => (M x).det) := by
  simp only [Matrix.det_apply]
  fun_prop

omit [DecidableEq V] in
lemma contDiff_kJ_entry (i j : V) : ContDiff ℝ ⊤ (fun p : PS C V => kJ H0 n p.1 i j) := by
  simp only [kJ, kfb, onesM, Matrix.add_apply, Matrix.of_apply]
  have h := contDiff_Qf (V := V) (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i)
  fun_prop

/-- `vfb` by Cramer's rule. -/
lemma vfb_cramer (ψ : (C → ℝ) × (C → ℝ)) (s : V → ℝ) (j : V) :
    vfb H0 n ψ s j =
      ((kJ H0 n ψ).det)⁻¹ * ((kJ H0 n ψ).updateCol j (fun i => qsrc H0 n ψ i - s i)).det := by
  rw [vfb, inv_def, Ring.inverse_eq_inv', smul_mulVec, ← cramer_eq_adjugate_mulVec, Pi.smul_apply,
    cramer_apply, smul_eq_mul]

lemma contDiffAt_vfb {p0 : PS C V} (hdet : (kJ H0 n p0.1).det ≠ 0) (j : V) :
    ContDiffAt ℝ ⊤ (fun p : PS C V => vfb H0 n p.1 p.2 j) p0 := by
  simp only [vfb_cramer]
  have hd : ContDiff ℝ ⊤ (fun p : PS C V => (kJ H0 n p.1).det) :=
    contDiff_det_of_entries _ (contDiff_kJ_entry H0 n)
  have hc : ContDiff ℝ ⊤ (fun p : PS C V =>
      ((kJ H0 n p.1).updateCol j (fun i => qsrc H0 n p.1 i - p.2 i)).det) := by
    apply contDiff_det_of_entries
    intro a b
    by_cases hb : b = j
    · subst hb
      simp only [updateCol_self, qsrc]
      have h := contDiff_Qf (V := V) (H0 * Nmat n a * H0 - H0 * H0 * Nmat n a)
      fun_prop
    · simp only [updateCol_ne hb]
      exact contDiff_kJ_entry H0 n a b
  exact (hd.contDiffAt.inv hdet).mul hc.contDiffAt

/-- The NLSE vector field on the extended phase space. -/
noncomputable def field (p : PS C V) : (C → ℝ) × (C → ℝ) := schr H0 n (vfb H0 n p.1 p.2) p.1

lemma contDiffAt_field {p0 : PS C V} (hdet : (kJ H0 n p0.1).det ≠ 0) :
    ContDiffAt ℝ ⊤ (field H0 n) p0 := by
  have hv : ∀ j, ContDiffAt ℝ ⊤ (fun p : PS C V => vfb H0 n p.1 p.2 j) p0 :=
    contDiffAt_vfb H0 n hdet
  have hcomp : ∀ (w : PS C V → C → ℝ), (∀ c, ContDiffAt ℝ ⊤ (fun p => w p c) p0) →
      ∀ c, ContDiffAt ℝ ⊤ (fun p : PS C V => (hamN H0 n (vfb H0 n p.1 p.2) *ᵥ w p) c) p0 := by
    intro w hw c
    simp only [hamN_mulVec_apply]
    have hs : ContDiffAt ℝ ⊤ (fun p : PS C V => ∑ i, vfb H0 n p.1 p.2 i * n i c) p0 :=
      ContDiffAt.sum (fun i _ => (hv i).mul contDiffAt_const)
    exact (ContDiffAt.sum (fun d _ => contDiffAt_const.mul (hw d))).add (hs.mul (hw c))
  have h1 : ∀ c, ContDiffAt ℝ ⊤ (fun p : PS C V => p.1.1 c) p0 := fun c => by fun_prop
  have h2 : ∀ c, ContDiffAt ℝ ⊤ (fun p : PS C V => p.1.2 c) p0 := fun c => by fun_prop
  refine ContDiffAt.prodMk (contDiffAt_pi.2 (hcomp _ h2)) (contDiffAt_pi.2 fun c => ?_)
  exact (hcomp _ h1 c).neg

end smooth

section localSolution

open scoped NNReal

variable (H0 : Matrix C C ℝ) (n : V → C → ℝ)

/-- The NLSE vector field: Schrödinger with the potential eliminated by the force balance. -/
noncomputable def nlse (ndd : ℝ → V → ℝ) (t : ℝ) (ψ : (C → ℝ) × (C → ℝ)) : (C → ℝ) × (C → ℝ) :=
  field H0 n (ψ, ndd t)

/-- The v-representability set `Ω`. -/
def omega : Set ((C → ℝ) × (C → ℝ)) := {ψ | (kJ H0 n ψ).det ≠ 0}

lemma isOpen_omega : IsOpen (omega H0 n) := by
  have hc : Continuous (fun ψ : (C → ℝ) × (C → ℝ) => (kJ H0 n ψ).det) :=
    (contDiff_det_of_entries _ (contDiff_kJ_entry H0 n)).continuous.comp
      (continuous_id.prodMk (continuous_const (y := (0 : V → ℝ))))
  exact isOpen_ne_fun hc continuous_const

/-- **Local solution of the NLSE** (Picard–Lindelöf), with a uniform Lipschitz constant on a ball
inside `Ω`. -/
theorem exists_local {ndd : ℝ → V → ℝ} (hcont : Continuous ndd) {t0 : ℝ}
    {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omega H0 n) :
    ∃ ε > 0, ∃ a > 0, ∃ K : ℝ≥0, ∃ α : ℝ → (C → ℝ) × (C → ℝ), α t0 = ψ0 ∧
      closedBall ψ0 a ⊆ omega H0 n ∧
      (∀ t ∈ Ioo (t0 - ε) (t0 + ε), HasDerivAt α (nlse H0 n ndd t (α t)) t) ∧
      (∀ t ∈ Ioo (t0 - ε) (t0 + ε), LipschitzOnWith K (nlse H0 n ndd t) (closedBall ψ0 a)) := by
  set p0 : PS C V := (ψ0, ndd t0)
  obtain ⟨K, U, hU, hLip⟩ :=
    ((contDiffAt_field H0 n (p0 := p0) hψ0).of_le le_top).exists_lipschitzOnWith
  obtain ⟨ε1, hε1, hball1⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨ε2, hε2, hball2⟩ := Metric.isOpen_iff.mp (isOpen_omega H0 n) ψ0 hψ0
  set a : ℝ := min ε1 ε2 / 2
  have ha : 0 < a := by positivity
  have hm : 0 < min ε1 ε2 := lt_min hε1 hε2
  have ha_def : a = min ε1 ε2 / 2 := rfl
  have ha1 : a < ε1 := by have := min_le_left ε1 ε2; rw [ha_def]; linarith
  have ha2 : a < ε2 := by have := min_le_right ε1 ε2; rw [ha_def]; linarith
  have hU' : ∀ p : PS C V, dist p p0 ≤ a → p ∈ U := fun p hp =>
    hball1 (mem_ball.mpr (lt_of_le_of_lt hp ha1))
  have hΩ : closedBall ψ0 a ⊆ omega H0 n := fun ψ hψ =>
    hball2 (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hψ) ha2))
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.mp hcont t0 a ha
  set L : ℝ := ‖field H0 n p0‖ + K * a
  have hL : 0 ≤ L := by positivity
  have hbound : ∀ p : PS C V, dist p p0 ≤ a → ‖field H0 n p‖ ≤ L := by
    intro p hp
    have h1 := hLip.dist_le_mul p (hU' p hp) p0 (hU' p0 (by simp [ha.le]))
    calc ‖field H0 n p‖ ≤ ‖field H0 n p0‖ + dist (field H0 n p) (field H0 n p0) := by
          rw [dist_eq_norm]; exact norm_le_norm_add_norm_sub' _ _
      _ ≤ L := by
          simp only [L]; gcongr; exact h1.trans (by gcongr)
  set ε : ℝ := min (δ / 2) (a / (L + 1))
  have hε : 0 < ε := by positivity
  have hεδ : ε < δ := by have := min_le_left (δ / 2) (a / (L + 1)); linarith
  have hLε : L * ε ≤ a := by
    have h1 : ε ≤ a / (L + 1) := min_le_right _ _
    calc L * ε ≤ L * (a / (L + 1)) := by gcongr
      _ ≤ a := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  -- the time slices stay in `U`
  have hslice : ∀ t ∈ Icc (t0 - ε) (t0 + ε), ∀ ψ ∈ closedBall ψ0 a, (ψ, ndd t) ∈ U := by
    intro t ht ψ hψ
    apply hU'
    have hdt : dist t t0 < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    rw [Prod.dist_eq]
    exact max_le (mem_closedBall.mp hψ) (hδc t hdt).le
  have hlipt : ∀ t ∈ Icc (t0 - ε) (t0 + ε),
      LipschitzOnWith K (nlse H0 n ndd t) (closedBall ψ0 a) := by
    intro t ht
    have := hLip.comp (LipschitzWith.prodMk_right (ndd t)).lipschitzOnWith
      (fun ψ hψ => hslice t ht ψ hψ)
    rw [mul_one] at this
    exact this
  have hPL : IsPicardLindelof (nlse H0 n ndd) (tmin := t0 - ε) (tmax := t0 + ε)
      ⟨t0, by constructor <;> linarith⟩ ψ0 ⟨a, ha.le⟩ 0 ⟨L, hL⟩ K := {
    lipschitzOnWith := hlipt
    continuousOn := by
      intro ψ hψ
      have hc : ContinuousOn (field H0 n) U := hLip.continuousOn
      refine hc.comp (continuous_const.prodMk hcont).continuousOn ?_
      intro t ht; exact hslice t ht ψ hψ
    norm_le := by
      intro t ht ψ hψ
      apply hbound
      have hdt : dist t t0 < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
      rw [Prod.dist_eq]
      exact max_le (mem_closedBall.mp hψ) (hδc t hdt).le
    mul_max_le := by
      change L * max (t0 + ε - t0) (t0 - (t0 - ε)) ≤ a - 0
      rw [show t0 + ε - t0 = ε by ring, show t0 - (t0 - ε) = ε by ring, max_self, sub_zero]
      exact hLε }
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨ε, hε, a, ha, K, α, hα0, hΩ, fun t ht => ?_, fun t ht => hlipt t (Ioo_subset_Icc_self ht)⟩
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end localSolution

lemma const_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ} (h : ∀ s ∈ Ioo a b, HasDerivAt f 0 s)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : f x = f y :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (h s hs).differentiableAt.differentiableWithinAt)
        (fun s hs => (h s hs).deriv) hx hy

section main

variable {H0 : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hH0 : H0.IsSymm)
  (hN : ∀ c, ∑ i, n i c = Ntot) [Nonempty V]
  {nn nd ndd : ℝ → V → ℝ} (hnd : ∀ t, HasDerivAt nn (nd t) t)
  (hndd : ∀ t, HasDerivAt nd (ndd t) t) (hcont : Continuous ndd) (hsum : ∀ t, ∑ i, ndd t i = 0)
include hH0 hN hnd hndd hcont hsum

/-- **Lattice TDDFT, existence (Farzanehpour–Tokatly Theorem 1).** Let the target density `n(t)`
have a continuous second derivative with `Σ_i n̈_i = 0`, and let the initial state `ψ0 ∈ Ω`
reproduce `n(t₀)` and `ṅ(t₀)`. Then on an interval around `t₀` there is a solution of the
Schrödinger equation, driven by a potential `v(t)` with `Σ_i v_i(t) = 0`, whose density is `n(t)`.
-/
theorem td_existence {t0 : ℝ} {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omega H0 n)
    (hρ0 : ∀ i, tdens n ψ0 i = nn t0 i) (hj0 : ∀ i, tcur H0 n ψ0 i = nd t0 i) :
    ∃ ε > 0, ∃ ψ : ℝ → (C → ℝ) × (C → ℝ), ψ t0 = ψ0 ∧
      ∀ t ∈ Ioo (t0 - ε) (t0 + ε),
        HasDerivAt ψ (schr H0 n (vfb H0 n (ψ t) (ndd t)) (ψ t)) t ∧
        ∑ i, vfb H0 n (ψ t) (ndd t) i = 0 ∧ ∀ i, tdens n (ψ t) i = nn t i := by
  obtain ⟨ε, hε, a, ha, K, α, hα0, hΩ, hα, -⟩ := exists_local H0 n hcont hψ0
  have hαc : ContinuousAt α t0 :=
    (hα t0 ⟨by linarith, by linarith⟩).continuousAt
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.mp hαc a ha
  set ε' := min ε η
  have hε' : 0 < ε' := lt_min hε hη
  have hsub : ∀ t ∈ Ioo (t0 - ε') (t0 + ε'), t ∈ Ioo (t0 - ε) (t0 + ε) := fun t ht =>
    ⟨by linarith [ht.1, min_le_left ε η], by linarith [ht.2, min_le_left ε η]⟩
  have hin : ∀ t ∈ Ioo (t0 - ε') (t0 + ε'), α t ∈ omega H0 n := by
    intro t ht
    apply hΩ
    have hdt : dist t t0 < η := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2, min_le_right ε η]
    have := hηb hdt
    rw [hα0] at this
    exact mem_closedBall.mpr this.le
  have hderiv : ∀ t ∈ Ioo (t0 - ε') (t0 + ε'),
      HasDerivAt α (schr H0 n (vfb H0 n (α t) (ndd t)) (α t)) t := fun t ht => hα t (hsub t ht)
  have ht0 : t0 ∈ Ioo (t0 - ε') (t0 + ε') := ⟨by linarith, by linarith⟩
  refine ⟨ε', hε', α, hα0, fun t ht => ⟨hderiv t ht, (vfb_spec hH0 hN (hin t ht) (hsum t)).1,
    fun i => ?_⟩⟩
  -- the current mismatch has zero derivative, hence vanishes
  have hg : ∀ s ∈ Ioo (t0 - ε') (t0 + ε'),
      HasDerivAt (fun s => tcur H0 n (α s) i - nd s i) 0 s := by
    intro s hs
    have h1 := (tcur_hasDerivAt hH0 (hderiv s hs) i).sub (hasDerivAt_pi.1 (hndd s) i)
    convert h1 using 1
    rw [(vfb_spec hH0 hN (hin s hs) (hsum s)).2 i]; ring
  have hg0 : ∀ s ∈ Ioo (t0 - ε') (t0 + ε'), tcur H0 n (α s) i - nd s i = 0 := by
    intro s hs
    rw [const_of_hasDerivAt_zero hg hs ht0, hα0, hj0, sub_self]
  -- hence the density mismatch has zero derivative, and vanishes too
  have hf : ∀ s ∈ Ioo (t0 - ε') (t0 + ε'),
      HasDerivAt (fun s => tdens n (α s) i - nn s i) 0 s := by
    intro s hs
    have h1 := (tdens_hasDerivAt hH0 (hderiv s hs) i).sub (hasDerivAt_pi.1 (hnd s) i)
    convert h1 using 1
    rw [hg0 s hs]
  have := const_of_hasDerivAt_zero hf ht ht0
  rw [hα0, hρ0 i, sub_self] at this
  linarith

omit hN hcont hsum [Nonempty V] in
/-- **The density determines the potential.** Along any trajectory that produces the density `n(t)`
near `t₀` (gauge `Σ v = 0`), the potential is `v(ψ, n̈)` and the state stays in `Ω`. -/
theorem pot_eq_vfb {t0 : ℝ} {ψ : ℝ → (C → ℝ) × (C → ℝ)} {v : ℝ → V → ℝ}
    (h : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ (schr H0 n (v t) (ψ t)) t ∧ ∑ i, v t i = 0 ∧
      ∀ i, tdens n (ψ t) i = nn t i) (hψ0 : ψ t0 ∈ omega H0 n) :
    ∀ᶠ t in 𝓝 t0, v t = vfb H0 n (ψ t) (ndd t) ∧ ψ t ∈ omega H0 n := by
  have hc : ContinuousAt ψ t0 := h.self_of_nhds.1.continuousAt
  have hΩ : ∀ᶠ t in 𝓝 t0, ψ t ∈ omega H0 n :=
    hc.preimage_mem_nhds ((isOpen_omega H0 n).mem_nhds hψ0)
  -- first derivative: the current equals `ṅ`
  have hcur : ∀ᶠ t in 𝓝 t0, ∀ i, tcur H0 n (ψ t) i = nd t i := by
    filter_upwards [h.eventually_nhds] with t ht
    intro i
    have hd := tdens_hasDerivAt hH0 ht.self_of_nhds.1 i
    have heq : (fun s => tdens n (ψ s) i) =ᶠ[𝓝 t] (fun s => nn s i) :=
      ht.mono fun s hs => hs.2.2 i
    exact hd.unique ((hasDerivAt_pi.1 (hnd t) i).congr_of_eventuallyEq heq)
  -- second derivative: the force balance with `n̈`
  have hK : ∀ᶠ t in 𝓝 t0, ∀ i, ∑ j, kfb H0 n (ψ t) i j * v t j = qsrc H0 n (ψ t) i - ndd t i := by
    filter_upwards [h, hcur.eventually_nhds] with t ht hct
    intro i
    have hd := tcur_hasDerivAt hH0 ht.1 i
    have heq : (fun s => tcur H0 n (ψ s) i) =ᶠ[𝓝 t] (fun s => nd s i) := hct.mono fun s hs => hs i
    have := hd.unique ((hasDerivAt_pi.1 (hndd t) i).congr_of_eventuallyEq heq)
    linarith
  filter_upwards [h, hΩ, hK] with t ht hΩt hKt
  exact ⟨vfb_unique hΩt ht.2.1 hKt, hΩt⟩

omit hN hsum [Nonempty V] in
/-- **Lattice TDDFT, uniqueness (Farzanehpour–Tokatly Theorem 1).** Two trajectories starting from
the same state `ψ0 ∈ Ω` that both produce the density `n(t)` (potentials in the gauge `Σ_i v_i = 0`)
coincide near `t₀`, and so do their potentials. -/
theorem td_uniqueness {t0 : ℝ} {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omega H0 n)
    {ψ1 ψ2 : ℝ → (C → ℝ) × (C → ℝ)} {v1 v2 : ℝ → V → ℝ}
    (h1 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ1 (schr H0 n (v1 t) (ψ1 t)) t ∧ ∑ i, v1 t i = 0 ∧
      ∀ i, tdens n (ψ1 t) i = nn t i)
    (h2 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ2 (schr H0 n (v2 t) (ψ2 t)) t ∧ ∑ i, v2 t i = 0 ∧
      ∀ i, tdens n (ψ2 t) i = nn t i)
    (h10 : ψ1 t0 = ψ0) (h20 : ψ2 t0 = ψ0) :
    ψ1 =ᶠ[𝓝 t0] ψ2 ∧ v1 =ᶠ[𝓝 t0] v2 := by
  obtain ⟨ε, hε, a, ha, K, -, -, -, -, hLip⟩ := exists_local H0 n hcont hψ0 (t0 := t0)
  have hp1 := pot_eq_vfb hH0 hnd hndd h1 (h10 ▸ hψ0)
  have hp2 := pot_eq_vfb hH0 hnd hndd h2 (h20 ▸ hψ0)
  have hball : ∀ {ψ : ℝ → (C → ℝ) × (C → ℝ)}, ContinuousAt ψ t0 → ψ t0 = ψ0 →
      ∀ᶠ t in 𝓝 t0, ψ t ∈ closedBall ψ0 a := by
    intro ψ hc h0
    exact hc.preimage_mem_nhds (h0 ▸ closedBall_mem_nhds (ψ t0) ha)
  have hLip' : ∀ᶠ t in 𝓝 t0, LipschitzOnWith K (nlse H0 n ndd t) (closedBall ψ0 a) :=
    Filter.mem_of_superset (Ioo_mem_nhds (show t0 - ε < t0 by linarith)
      (show t0 < t0 + ε by linarith)) fun t ht => hLip t ht
  have hs1 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ1 (nlse H0 n ndd t (ψ1 t)) t ∧ ψ1 t ∈ closedBall ψ0 a := by
    filter_upwards [h1, hp1, hball h1.self_of_nhds.1.continuousAt h10] with t ht hpt hbt
    refine ⟨?_, hbt⟩
    have := ht.1
    rw [hpt.1] at this
    exact this
  have hs2 : ∀ᶠ t in 𝓝 t0, HasDerivAt ψ2 (nlse H0 n ndd t (ψ2 t)) t ∧ ψ2 t ∈ closedBall ψ0 a := by
    filter_upwards [h2, hp2, hball h2.self_of_nhds.1.continuousAt h20] with t ht hpt hbt
    refine ⟨?_, hbt⟩
    have := ht.1
    rw [hpt.1] at this
    exact this
  have hψ : ψ1 =ᶠ[𝓝 t0] ψ2 :=
    ODE_solution_unique_of_eventually hLip' hs1 hs2 (h10.trans h20.symm)
  refine ⟨hψ, ?_⟩
  filter_upwards [hψ, hp1, hp2] with t ht hpt1 hpt2
  rw [hpt1.1, hpt2.1, ht]

end main

end DFT
