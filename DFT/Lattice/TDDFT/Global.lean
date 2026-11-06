/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.TDDFT.KohnSham

/-!
# Lattice TDDFT: continuation in time (blow-up alternative)

The norm `Σ_c (x_c² + y_c²)` is conserved by the Schrödinger flow, so a solution of the TDDFT
equations can only stop by approaching the boundary `det(K + 𝟙𝟙ᵀ) = 0` of the v-representability
set `Ω`.

* `exists_local_unif`: Picard–Lindelöf with a step length that is uniform near a point of `Ω` and
  near a time.
* `exists_unif_step`: by compactness, a uniform step length for all starting times in `[a, b]` and
  all starting states in a compact subset of `Ω`.
* `nlse_global`: the NLSE solution from `ψ0 ∈ Ω` either exists on all of `[t₀, T]`, or for every
  `δ > 0` it reaches, before `T`, a state with `|det(K + 𝟙𝟙ᵀ)| < δ`.
* `td_global`: the same for the TDDFT problem, with the potential and the density `n(t)`.
-/

namespace DFT

open Matrix Set Filter Topology Metric
open scoped NNReal

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

/-- **Picard–Lindelöf** (from Mathlib's proof), also recording that the solution stays in the ball
where the vector field is controlled. -/
theorem exists_mem_closedBall_of_isPicardLindelof {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧
      ∀ t, α t ∈ closedBall x₀ a := by
  have hx : x₀ ∈ closedBall x₀ (0 : ℝ≥0) := mem_closedBall_self le_rfl
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t ht ↦ ?_, fun t => α.compProj_mem_closedBall hf.mul_max_le⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x₀ ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

section uniform

variable (H0 : Matrix C C ℝ) (n : V → C → ℝ)

/-- **Uniform local solution.** Near a point `(t₁, ψ₁)` with `ψ₁ ∈ Ω`, every starting time and
state has an NLSE solution, staying in `Ω`, on a time interval of one common length. -/
theorem exists_local_unif {ndd : ℝ → V → ℝ} (hcont : Continuous ndd) (t1 : ℝ)
    {ψ1 : (C → ℝ) × (C → ℝ)} (hψ1 : ψ1 ∈ omega H0 n) :
    ∃ ε > 0, ∃ η > 0, ∀ (t' : ℝ) (x : (C → ℝ) × (C → ℝ)), |t' - t1| < η → dist x ψ1 ≤ η →
      ∃ α : ℝ → (C → ℝ) × (C → ℝ), α t' = x ∧
        ∀ t ∈ Ioo (t' - ε) (t' + ε), HasDerivAt α (nlse H0 n ndd t (α t)) t ∧
          α t ∈ omega H0 n := by
  set p0 : PS C V := (ψ1, ndd t1)
  obtain ⟨K, U, hU, hLip⟩ :=
    ((contDiffAt_field H0 n (p0 := p0) hψ1).of_le le_top).exists_lipschitzOnWith
  obtain ⟨ε1, hε1, hball1⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨ε2, hε2, hball2⟩ := Metric.isOpen_iff.mp (isOpen_omega H0 n) ψ1 hψ1
  set a : ℝ := min ε1 ε2 / 2
  have ha : 0 < a := by positivity
  have ha_def : a = min ε1 ε2 / 2 := rfl
  have ha1 : a < ε1 := by have := min_le_left ε1 ε2; have := lt_min hε1 hε2; rw [ha_def]; linarith
  have ha2 : a < ε2 := by have := min_le_right ε1 ε2; have := lt_min hε1 hε2; rw [ha_def]; linarith
  have hU' : ∀ p : PS C V, dist p p0 ≤ a → p ∈ U := fun p hp =>
    hball1 (mem_ball.mpr (lt_of_le_of_lt hp ha1))
  have hΩ : closedBall ψ1 a ⊆ omega H0 n := fun ψ hψ =>
    hball2 (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hψ) ha2))
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.mp hcont t1 a ha
  set L : ℝ := ‖field H0 n p0‖ + K * a
  have hL : 0 ≤ L := by positivity
  have hbound : ∀ p : PS C V, dist p p0 ≤ a → ‖field H0 n p‖ ≤ L := by
    intro p hp
    have h1 := hLip.dist_le_mul p (hU' p hp) p0 (hU' p0 (by simp [ha.le]))
    calc ‖field H0 n p‖ ≤ ‖field H0 n p0‖ + dist (field H0 n p) (field H0 n p0) := by
          rw [dist_eq_norm]; exact norm_le_norm_add_norm_sub' _ _
      _ ≤ L := by
          simp only [L]; gcongr; exact h1.trans (by gcongr)
  set η : ℝ := min (δ / 2) (a / 2)
  have hη : 0 < η := by positivity
  set ε : ℝ := min (δ / 4) (a / 2 / (L + 1))
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, η, hη, fun t' x ht' hx => ?_⟩
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hηa : η ≤ a / 2 := min_le_right _ _
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hLε : L * ε ≤ a / 2 := by
    have h1 : ε ≤ a / 2 / (L + 1) := min_le_right _ _
    calc L * ε ≤ L * (a / 2 / (L + 1)) := by gcongr
      _ ≤ a / 2 := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  -- the ball around `x` of radius `a / 2` lies in the ball around `ψ1` of radius `a`
  have hsub : closedBall x (a / 2) ⊆ closedBall ψ1 a := by
    intro ψ hψ
    rw [mem_closedBall] at hψ ⊢
    calc dist ψ ψ1 ≤ dist ψ x + dist x ψ1 := dist_triangle _ _ _
      _ ≤ a := by linarith
  have hslice : ∀ t ∈ Icc (t' - ε) (t' + ε), ∀ ψ ∈ closedBall x (a / 2), (ψ, ndd t) ∈ U := by
    intro t ht ψ hψ
    apply hU'
    have hdt : dist t t1 < δ := by
      rw [Real.dist_eq, abs_lt]
      rw [abs_lt] at ht'
      constructor <;> linarith [ht.1, ht.2]
    rw [Prod.dist_eq]
    exact max_le (mem_closedBall.mp (hsub hψ)) (hδc t hdt).le
  have hlipt : ∀ t ∈ Icc (t' - ε) (t' + ε),
      LipschitzOnWith K (nlse H0 n ndd t) (closedBall x (a / 2)) := by
    intro t ht
    have := hLip.comp (LipschitzWith.prodMk_right (ndd t)).lipschitzOnWith
      (fun ψ hψ => hslice t ht ψ hψ)
    rw [mul_one] at this
    exact this
  have ha2' : (0 : ℝ) ≤ a / 2 := by positivity
  have hPL : IsPicardLindelof (nlse H0 n ndd) (tmin := t' - ε) (tmax := t' + ε)
      ⟨t', by constructor <;> linarith⟩ x ⟨a / 2, ha2'⟩ 0 ⟨L, hL⟩ K := {
    lipschitzOnWith := hlipt
    continuousOn := by
      intro ψ hψ
      have hc : ContinuousOn (field H0 n) U := hLip.continuousOn
      refine hc.comp (continuous_const.prodMk hcont).continuousOn ?_
      intro t ht; exact hslice t ht ψ hψ
    norm_le := by
      intro t ht ψ hψ
      apply hbound
      have hdt : dist t t1 < δ := by
        rw [Real.dist_eq, abs_lt]
        rw [abs_lt] at ht'
        constructor <;> linarith [ht.1, ht.2]
      rw [Prod.dist_eq]
      exact max_le (mem_closedBall.mp (hsub hψ)) (hδc t hdt).le
    mul_max_le := by
      change L * max (t' + ε - t') (t' - (t' - ε)) ≤ a / 2 - 0
      rw [show t' + ε - t' = ε by ring, show t' - (t' - ε) = ε by ring, max_self, sub_zero]
      exact hLε }
  obtain ⟨α, hα0, hα, hαb⟩ := exists_mem_closedBall_of_isPicardLindelof hPL
  refine ⟨α, hα0, fun t ht => ⟨?_, hΩ (hsub (hαb t))⟩⟩
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- **Uniform step length** on a compact set of starting data: for all starting times in `[a, b]`
and all starting states in a compact `S ⊆ Ω`, the NLSE has a solution, staying in `Ω`, on an
interval of one common length `2ε`. -/
theorem exists_unif_step {ndd : ℝ → V → ℝ} (hcont : Continuous ndd)
    {S : Set ((C → ℝ) × (C → ℝ))} (hS : IsCompact S) (hSΩ : S ⊆ omega H0 n) (a b : ℝ) :
    ∃ ε > 0, ∀ t' ∈ Icc a b, ∀ x ∈ S, ∃ α : ℝ → (C → ℝ) × (C → ℝ), α t' = x ∧
      ∀ t ∈ Ioo (t' - ε) (t' + ε), HasDerivAt α (nlse H0 n ndd t (α t)) t ∧
        α t ∈ omega H0 n := by
  have hloc : ∀ p : ℝ × ((C → ℝ) × (C → ℝ)), ∃ ε > 0, ∃ η > 0, p.2 ∈ omega H0 n →
      ∀ (t' : ℝ) (x : (C → ℝ) × (C → ℝ)), |t' - p.1| < η → dist x p.2 ≤ η →
        ∃ α : ℝ → (C → ℝ) × (C → ℝ), α t' = x ∧
          ∀ t ∈ Ioo (t' - ε) (t' + ε), HasDerivAt α (nlse H0 n ndd t (α t)) t ∧
            α t ∈ omega H0 n := by
    intro p
    by_cases hp : p.2 ∈ omega H0 n
    · obtain ⟨ε, hε, η, hη, h⟩ := exists_local_unif H0 n hcont p.1 hp
      exact ⟨ε, hε, η, hη, fun _ => h⟩
    · exact ⟨1, one_pos, 1, one_pos, fun h => absurd h hp⟩
  choose ε hε η hη hP using hloc
  have hK : IsCompact (Icc a b ×ˢ S) := isCompact_Icc.prod hS
  obtain ⟨F, hFK, hcover⟩ := hK.elim_nhds_subcover
    (fun p => ball p.1 (η p) ×ˢ ball p.2 (η p))
    (fun p _ => prod_mem_nhds (ball_mem_nhds _ (hη p)) (ball_mem_nhds _ (hη p)))
  by_cases hne : F.Nonempty
  · obtain ⟨p0, -, hmin⟩ := F.exists_min_image ε hne
    refine ⟨ε p0, hε p0, fun t' ht' x hx => ?_⟩
    have hin : ((t', x) : ℝ × ((C → ℝ) × (C → ℝ))) ∈ Icc a b ×ˢ S := ⟨ht', hx⟩
    obtain ⟨p, hpF, hmem⟩ := mem_iUnion₂.mp (hcover hin)
    obtain ⟨ht, hxb⟩ := hmem
    obtain ⟨α, hα0, hα⟩ := hP p (hSΩ (hFK p hpF).2) t' x
      (by rw [← Real.dist_eq]; exact mem_ball.mp ht) (mem_ball.mp hxb).le
    have hle := hmin p hpF
    exact ⟨α, hα0, fun t htt => hα t ⟨by linarith [htt.1], by linarith [htt.2]⟩⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, one_pos, fun t' ht' x hx => ?_⟩
    have hin : ((t', x) : ℝ × ((C → ℝ) × (C → ℝ))) ∈ Icc a b ×ˢ S := ⟨ht', hx⟩
    have := hcover hin
    simp [hne] at this

end uniform

section march

variable (H0 : Matrix C C ℝ) (n : V → C → ℝ)

lemma continuous_det_kJ : Continuous (fun ψ : (C → ℝ) × (C → ℝ) => (kJ H0 n ψ).det) :=
  (contDiff_det_of_entries _ (contDiff_kJ_entry H0 n)).continuous.comp
    (continuous_id.prodMk (continuous_const (y := (0 : V → ℝ))))

/-- States of squared norm `P` at distance `δ` (in determinant) from the boundary of `Ω`. -/
def detSet (P δ : ℝ) : Set ((C → ℝ) × (C → ℝ)) := {ψ | Qf 1 ψ = P ∧ δ ≤ |(kJ H0 n ψ).det|}

lemma detSet_subset {P δ : ℝ} (hδ : 0 < δ) : detSet H0 n P δ ⊆ omega H0 n := by
  intro ψ hψ hdet
  have := hψ.2
  rw [hdet, abs_zero] at this
  linarith

lemma Qf_one_eq (ψ : (C → ℝ) × (C → ℝ)) :
    Qf 1 ψ = ∑ c, ψ.1 c * ψ.1 c + ∑ c, ψ.2 c * ψ.2 c := by
  simp [Qf, one_mulVec, dotProduct]

lemma isCompact_detSet (P δ : ℝ) : IsCompact (detSet H0 n P δ) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq (continuous_Qf 1) continuous_const).inter
      (isClosed_le continuous_const (continuous_abs.comp (continuous_det_kJ H0 n)))
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max 1 P, fun ψ hψ => ?_⟩
    have hP := hψ.1
    rw [Qf_one_eq] at hP
    have h1 : ∀ c, ψ.1 c * ψ.1 c ≤ P := fun c => by
      have := Finset.single_le_sum (f := fun c => ψ.1 c * ψ.1 c)
        (fun c _ => mul_self_nonneg _) (Finset.mem_univ c)
      have := Finset.sum_nonneg (s := Finset.univ) (fun c _ => mul_self_nonneg (ψ.2 c))
      linarith
    have h2 : ∀ c, ψ.2 c * ψ.2 c ≤ P := fun c => by
      have := Finset.single_le_sum (f := fun c => ψ.2 c * ψ.2 c)
        (fun c _ => mul_self_nonneg _) (Finset.mem_univ c)
      have := Finset.sum_nonneg (s := Finset.univ) (fun c _ => mul_self_nonneg (ψ.1 c))
      linarith
    have hb : ∀ r : ℝ, r * r ≤ P → |r| ≤ max 1 P := fun r hr => by
      by_cases h : |r| ≤ 1
      · exact h.trans (le_max_left _ _)
      · push Not at h
        have : |r| * |r| = r * r := abs_mul_abs_self r
        exact (by nlinarith : |r| ≤ P).trans (le_max_right _ _)
    have hR : (0 : ℝ) ≤ max 1 P := le_trans zero_le_one (le_max_left _ _)
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    constructor
    · exact (pi_norm_le_iff_of_nonneg hR).mpr fun c => by
        rw [Real.norm_eq_abs]; exact hb _ (h1 c)
    · exact (pi_norm_le_iff_of_nonneg hR).mpr fun c => by
        rw [Real.norm_eq_abs]; exact hb _ (h2 c)

variable {H0 n}

/-- **Norm conservation** along the NLSE. -/
lemma Qf_one_hasDerivAt (hH0 : H0.IsSymm) {ndd : ℝ → V → ℝ} {α : ℝ → (C → ℝ) × (C → ℝ)} {t : ℝ}
    (h : HasDerivAt α (nlse H0 n ndd t (α t)) t) : HasDerivAt (fun s => Qf 1 (α s)) 0 t := by
  have := Qf_hasDerivAt (v := vfb H0 n (α t) (ndd t)) hH0 h 1
  simpa [Wf] using this

lemma const_on_Icc {f : ℝ → ℝ} {a b : ℝ} (h : ∀ t ∈ Icc a b, HasDerivAt f 0 t) :
    ∀ t ∈ Icc a b, f t = f a :=
  constant_of_has_deriv_right_zero (fun t ht => (h t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

variable (H0 n) in
/-- An NLSE solution from `ψ0` at `t0`, inside `Ω`, on `[t0, s]`. -/
def GoodOn (ndd : ℝ → V → ℝ) (t0 : ℝ) (ψ0 : (C → ℝ) × (C → ℝ)) (α : ℝ → (C → ℝ) × (C → ℝ))
    (s : ℝ) : Prop :=
  α t0 = ψ0 ∧ ∀ t ∈ Icc t0 s, HasDerivAt α (nlse H0 n ndd t (α t)) t ∧ α t ∈ omega H0 n

/-- Gluing a solution on `[t0, s]` with a local solution around `s`. -/
lemma goodOn_glue {ndd : ℝ → V → ℝ} {t0 s s' ε : ℝ} {ψ0 : (C → ℝ) × (C → ℝ)}
    {α β : ℝ → (C → ℝ) × (C → ℝ)} (hts : t0 ≤ s) (hα : GoodOn H0 n ndd t0 ψ0 α s)
    (hβ0 : β s = α s)
    (hβ : ∀ t ∈ Ioo (s - ε) (s + ε), HasDerivAt β (nlse H0 n ndd t (β t)) t ∧ β t ∈ omega H0 n)
    (hs' : s' < s + ε) (hε : 0 < ε) :
    GoodOn H0 n ndd t0 ψ0 (fun t => if t ≤ s then α t else β t) s' := by
  set γ : ℝ → (C → ℝ) × (C → ℝ) := fun t => if t ≤ s then α t else β t with hγ
  refine ⟨by simp [γ, hts, hα.1], fun t ht => ?_⟩
  rcases lt_trichotomy t s with h | h | h
  · have heq : γ =ᶠ[𝓝 t] α := by
      filter_upwards [Iio_mem_nhds h] with u hu
      simp [γ, le_of_lt (mem_Iio.mp hu)]
    have hγt : γ t = α t := heq.eq_of_nhds
    obtain ⟨hd, hm⟩ := hα.2 t ⟨ht.1, h.le⟩
    rw [hγt]
    exact ⟨hd.congr_of_eventuallyEq heq, hm⟩
  · rw [h]
    have hγs : γ s = α s := by simp [γ]
    obtain ⟨hd, hm⟩ := hα.2 s ⟨hts, le_rfl⟩
    have hl : HasDerivWithinAt γ (nlse H0 n ndd s (α s)) (Iic s) s :=
      hd.hasDerivWithinAt.congr (fun u hu => by simp [γ, mem_Iic.mp hu]) hγs
    have hr : HasDerivWithinAt γ (nlse H0 n ndd s (α s)) (Ici s) s := by
      have := (hβ s ⟨by linarith, by linarith⟩).1.hasDerivWithinAt (s := Ici s)
      rw [hβ0] at this
      refine this.congr (fun u hu => ?_) (by rw [hγs, hβ0])
      by_cases hus : u ≤ s
      · have hu' : u = s := le_antisymm hus hu
        rw [hu', hγs, hβ0]
      · simp [γ, hus]
    have hlr := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hlr
    rw [hγs]
    exact ⟨hlr, hm⟩
  · have heq : γ =ᶠ[𝓝 t] β := by
      filter_upwards [Ioi_mem_nhds h] with u hu
      simp [γ, not_le.mpr (mem_Ioi.mp hu)]
    have hγt : γ t = β t := heq.eq_of_nhds
    obtain ⟨hd, hm⟩ := hβ t ⟨by linarith, by linarith [ht.2]⟩
    rw [hγt]
    exact ⟨hd.congr_of_eventuallyEq heq, hm⟩

/-- Marching in uniform steps: either the solution reaches `T`, or it reaches a state with
`|det(K + 𝟙𝟙ᵀ)| < δ` first. -/
theorem nlse_march (hH0 : H0.IsSymm) {ndd : ℝ → V → ℝ} (hcont : Continuous ndd) {t0 T : ℝ}
    (hT : t0 ≤ T) {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omega H0 n) {δ : ℝ} (hδ : 0 < δ) :
    (∃ α, GoodOn H0 n ndd t0 ψ0 α T) ∨
      ∃ s ∈ Icc t0 T, ∃ α, GoodOn H0 n ndd t0 ψ0 α s ∧ |(kJ H0 n (α s)).det| < δ := by
  set P := Qf 1 ψ0
  obtain ⟨ε, hε, hstep⟩ :=
    exists_unif_step H0 n hcont (isCompact_detSet H0 n P δ) (detSet_subset H0 n hδ) t0 T
  have claim : ∀ k : ℕ,
      (∃ α, GoodOn H0 n ndd t0 ψ0 α (min (t0 + k * (ε / 2)) T) ∧
        δ ≤ |(kJ H0 n (α (min (t0 + k * (ε / 2)) T))).det|) ∨
      ∃ s ∈ Icc t0 T, ∃ α, GoodOn H0 n ndd t0 ψ0 α s ∧ |(kJ H0 n (α s)).det| < δ := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero, min_eq_left hT]
      obtain ⟨ε0, hε0, -, -, -, α, hα0, -, hα, -⟩ := exists_local H0 n hcont (t0 := t0) hψ0
      have hg : GoodOn H0 n ndd t0 ψ0 α t0 := by
        refine ⟨hα0, fun t ht => ?_⟩
        have : t = t0 := le_antisymm ht.2 ht.1
        rw [this, hα0]
        exact ⟨hα0 ▸ hα t0 ⟨by linarith, by linarith⟩, hψ0⟩
      by_cases hd : δ ≤ |(kJ H0 n ψ0).det|
      · exact Or.inl ⟨α, hg, by rw [hα0]; exact hd⟩
      · exact Or.inr ⟨t0, ⟨le_rfl, hT⟩, α, hg, by rw [hα0]; exact lt_of_not_ge hd⟩
    | succ k ih =>
      rcases ih with ⟨α, hg, hdet⟩ | hbad
      · set s := min (t0 + k * (ε / 2)) T with hs_def
        have hk0 : (0 : ℝ) ≤ k * (ε / 2) := by positivity
        have hts : t0 ≤ s := le_min (by linarith) hT
        have hsT : s ≤ T := min_le_right _ _
        set s' := min (t0 + ((k + 1 : ℕ) : ℝ) * (ε / 2)) T with hs'_def
        have hcast : ((k + 1 : ℕ) : ℝ) * (ε / 2) = k * (ε / 2) + ε / 2 := by push_cast; ring
        by_cases hsT' : s = T
        · have hs's : s' = s := by
            rw [hs'_def, hsT', min_eq_right]
            have : T ≤ t0 + k * (ε / 2) := by
              rw [← hsT', hs_def]; exact min_le_left _ _
            rw [hcast]; linarith
          exact Or.inl ⟨α, hs's ▸ hg, hs's ▸ hdet⟩
        · have hs_eq : s = t0 + k * (ε / 2) := by
            rcases min_choice (t0 + k * (ε / 2)) T with h | h
            · exact h
            · exact absurd h hsT'
          have hnorm : Qf 1 (α s) = P := by
            rw [const_on_Icc (fun t ht => Qf_one_hasDerivAt hH0 (hg.2 t ht).1) s ⟨hts, le_rfl⟩,
              hg.1]
          obtain ⟨β, hβ0, hβ⟩ := hstep s ⟨hts, hsT⟩ (α s) ⟨hnorm, hdet⟩
          have hs' : s' < s + ε := by
            have : s' ≤ t0 + ((k + 1 : ℕ) : ℝ) * (ε / 2) := min_le_left _ _
            rw [hcast] at this; linarith
          have hgl := goodOn_glue hts hg hβ0 hβ hs' hε
          by_cases hd : δ ≤ |(kJ H0 n ((fun t => if t ≤ s then α t else β t) s')).det|
          · exact Or.inl ⟨_, hgl, hd⟩
          · refine Or.inr ⟨s', ⟨le_min ?_ hT, min_le_right _ _⟩, _, hgl, lt_of_not_ge hd⟩
            rw [hcast]; linarith
      · exact Or.inr hbad
  obtain ⟨k, hk⟩ := exists_nat_ge ((T - t0) / (ε / 2))
  have hmin : min (t0 + k * (ε / 2)) T = T := by
    apply min_eq_right
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε / 2)).mp hk
    linarith
  rcases claim k with ⟨α, hg, -⟩ | hbad
  · rw [hmin] at hg; exact Or.inl ⟨α, hg⟩
  · exact Or.inr hbad

/-- **Blow-up alternative for the NLSE.** The solution from `ψ0 ∈ Ω` either exists (inside `Ω`)
on all of `[t₀, T]`, or it comes arbitrarily close to the boundary of `Ω` before `T`. -/
theorem nlse_global (hH0 : H0.IsSymm) {ndd : ℝ → V → ℝ} (hcont : Continuous ndd) {t0 T : ℝ}
    (hT : t0 ≤ T) {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omega H0 n) :
    (∃ α, GoodOn H0 n ndd t0 ψ0 α T) ∨
      ∀ δ > 0, ∃ s ∈ Icc t0 T, ∃ α, GoodOn H0 n ndd t0 ψ0 α s ∧ |(kJ H0 n (α s)).det| < δ := by
  by_cases h : ∃ α, GoodOn H0 n ndd t0 ψ0 α T
  · exact Or.inl h
  · refine Or.inr fun δ hδ => ?_
    rcases nlse_march hH0 hcont hT hψ0 hδ with h' | h'
    · exact absurd h' h
    · exact h'

/-- **Uniqueness on `[t₀, s]`.** Two NLSE solutions from the same state, inside `Ω`, coincide on the
whole interval (continuity induction from local uniqueness). -/
theorem goodOn_unique {ndd : ℝ → V → ℝ} (hcont : Continuous ndd) {t0 s : ℝ}
    {ψ0 : (C → ℝ) × (C → ℝ)} {α β : ℝ → (C → ℝ) × (C → ℝ)} (hα : GoodOn H0 n ndd t0 ψ0 α s)
    (hβ : GoodOn H0 n ndd t0 ψ0 β s) : ∀ t ∈ Icc t0 s, α t = β t := by
  set A := {t : ℝ | α t = β t}
  have hcl : IsClosed (A ∩ Icc t0 s) := by
    have hc : ContinuousOn (fun t => (α t, β t)) (Icc t0 s) := fun t ht =>
      ((hα.2 t ht).1.continuousAt.prodMk (hβ.2 t ht).1.continuousAt).continuousWithinAt
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
    convert this using 1
    ext t; simp [A, and_comm]
  intro t ht
  refine hcl.Icc_subset_of_forall_mem_nhdsWithin (by simp [A, hα.1, hβ.1]) ?_ ht
  rintro x ⟨hx, hxI⟩
  have hxI' : x ∈ Icc t0 s := Ico_subset_Icc_self hxI
  obtain ⟨ε, hε, a, ha, K, -, -, -, -, hLip⟩ := exists_local H0 n hcont (t0 := x) (hα.2 x hxI').2
  obtain ⟨η1, hη1, hb1⟩ := Metric.continuousAt_iff.mp (hα.2 x hxI').1.continuousAt a ha
  obtain ⟨η2, hη2, hb2⟩ := Metric.continuousAt_iff.mp (hβ.2 x hxI').1.continuousAt a ha
  set r := min ε (min η1 η2) / 2
  have hr : 0 < r := by positivity
  have hr_def : r = min ε (min η1 η2) / 2 := rfl
  have hrε : r < ε := by
    have := min_le_left ε (min η1 η2); have := lt_min hε (lt_min hη1 hη2); rw [hr_def]; linarith
  have hr1 : r < η1 := by
    have := min_le_right ε (min η1 η2); have := min_le_left η1 η2
    have := lt_min hε (lt_min hη1 hη2); rw [hr_def]; linarith
  have hr2 : r < η2 := by
    have := min_le_right ε (min η1 η2); have := min_le_right η1 η2
    have := lt_min hε (lt_min hη1 hη2); rw [hr_def]; linarith
  set b := min (x + r) s
  have hxb : x < b := lt_min (by linarith) hxI.2
  have hbs : b ≤ s := min_le_right _ _
  have hbr : b ≤ x + r := min_le_left _ _
  have hsub : ∀ u ∈ Icc x b, u ∈ Icc t0 s := fun u hu => ⟨hxI.1.trans hu.1, hu.2.trans hbs⟩
  have hdist : ∀ u ∈ Icc x b, dist u x < r ∨ dist u x = r := fun u hu => by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
    rcases lt_or_eq_of_le (show u - x ≤ r by linarith [hu.2]) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hnear : ∀ u ∈ Icc x b, dist u x < η1 ∧ dist u x < η2 ∧ u ∈ Ioo (x - ε) (x + ε) := by
    intro u hu
    have h' : dist u x ≤ r := by rcases hdist u hu with h | h <;> linarith
    refine ⟨by linarith, by linarith, ?_⟩
    rw [Real.dist_eq, abs_le] at h'
    constructor <;> linarith [h'.1, h'.2]
  have hEq := ODE_solution_unique_of_mem_Icc_right (v := nlse H0 n ndd)
    (s := fun _ => closedBall (α x) a) (K := K)
    (fun u hu => hLip u (hnear u (Ico_subset_Icc_self hu)).2.2)
    (fun u hu => (hα.2 u (hsub u hu)).1.continuousAt.continuousWithinAt)
    (fun u hu => (hα.2 u (hsub u (Ico_subset_Icc_self hu))).1.hasDerivWithinAt)
    (fun u hu => mem_closedBall.mpr (hb1 (hnear u (Ico_subset_Icc_self hu)).1).le)
    (fun u hu => (hβ.2 u (hsub u hu)).1.continuousAt.continuousWithinAt)
    (fun u hu => (hβ.2 u (hsub u (Ico_subset_Icc_self hu))).1.hasDerivWithinAt)
    (fun u hu => mem_closedBall.mpr (by
      have := hb2 (hnear u (Ico_subset_Icc_self hu)).2.1
      rw [← hx] at this; exact this.le))
    hx
  exact mem_of_superset (Ioo_mem_nhdsGT hxb) fun u hu => hEq (Ioo_subset_Icc_self hu)

end march

section tddft

variable {H0 : Matrix C C ℝ} {n : V → C → ℝ} {Ntot : ℝ} (hH0 : H0.IsSymm)
  (hN : ∀ c, ∑ i, n i c = Ntot) [Nonempty V]
  {nn nd ndd : ℝ → V → ℝ} (hnd : ∀ t, HasDerivAt nn (nd t) t)
  (hndd : ∀ t, HasDerivAt nd (ndd t) t) (hsum : ∀ t, ∑ i, ndd t i = 0)
include hH0 hN hnd hndd hsum

/-- An NLSE solution inside `Ω`, with the initial density and current of the target, is a TDDFT
solution: gauge-fixed potential `v(ψ, n̈)` and density `n(t)` on the whole interval. -/
theorem tdsol_of_goodOn {t0 s : ℝ} {ψ0 : (C → ℝ) × (C → ℝ)} {α : ℝ → (C → ℝ) × (C → ℝ)}
    (hg : GoodOn H0 n ndd t0 ψ0 α s) (hρ0 : ∀ i, tdens n ψ0 i = nn t0 i)
    (hj0 : ∀ i, tcur H0 n ψ0 i = nd t0 i) :
    ∀ t ∈ Icc t0 s, α t ∈ omega H0 n ∧
      HasDerivAt α (schr H0 n (vfb H0 n (α t) (ndd t)) (α t)) t ∧
      ∑ i, vfb H0 n (α t) (ndd t) i = 0 ∧ ∀ i, tdens n (α t) i = nn t i := by
  have hd : ∀ u ∈ Icc t0 s, HasDerivAt α (schr H0 n (vfb H0 n (α u) (ndd u)) (α u)) u :=
    fun u hu => (hg.2 u hu).1
  have hspec := fun u (hu : u ∈ Icc t0 s) => vfb_spec hH0 hN (hg.2 u hu).2 (hsum u)
  intro t ht
  refine ⟨(hg.2 t ht).2, hd t ht, (hspec t ht).1, fun i => ?_⟩
  have hcur : ∀ u ∈ Icc t0 s, HasDerivAt (fun u => tcur H0 n (α u) i - nd u i) 0 u := by
    intro u hu
    have h1 := (tcur_hasDerivAt hH0 (hd u hu) i).sub (hasDerivAt_pi.1 (hndd u) i)
    convert h1 using 1
    rw [(hspec u hu).2 i]; ring
  have hg0 : ∀ u ∈ Icc t0 s, tcur H0 n (α u) i - nd u i = 0 := by
    intro u hu
    rw [const_on_Icc hcur u hu, hg.1, hj0, sub_self]
  have hf : ∀ u ∈ Icc t0 s, HasDerivAt (fun u => tdens n (α u) i - nn u i) 0 u := by
    intro u hu
    have h1 := (tdens_hasDerivAt hH0 (hd u hu) i).sub (hasDerivAt_pi.1 (hnd u) i)
    convert h1 using 1
    rw [hg0 u hu]
  have := const_on_Icc hf t ht
  rw [hg.1, hρ0 i, sub_self] at this
  linarith

/-- **Lattice TDDFT, blow-up alternative.** Let the target density have continuous `n̈` with
`Σ_i n̈_i = 0`, and let `ψ0 ∈ Ω` reproduce `n(t₀)` and `ṅ(t₀)`. For every `T ≥ t₀`, either there is
a solution on all of `[t₀, T]` — Schrödinger evolution driven by the gauge-fixed potential
`v(ψ, n̈)`, staying in `Ω`, with density `n(t)` — or the solution comes arbitrarily close to the
boundary `det(K + 𝟙𝟙ᵀ) = 0` of `Ω` before `T`. Since the norm is conserved, nothing else can go
wrong. The solution is unique (`goodOn_unique`). -/
theorem td_global (hcont : Continuous ndd) {t0 T : ℝ} (hT : t0 ≤ T)
    {ψ0 : (C → ℝ) × (C → ℝ)} (hψ0 : ψ0 ∈ omega H0 n)
    (hρ0 : ∀ i, tdens n ψ0 i = nn t0 i) (hj0 : ∀ i, tcur H0 n ψ0 i = nd t0 i) :
    (∃ ψ : ℝ → (C → ℝ) × (C → ℝ), ψ t0 = ψ0 ∧ ∀ t ∈ Icc t0 T, ψ t ∈ omega H0 n ∧
      HasDerivAt ψ (schr H0 n (vfb H0 n (ψ t) (ndd t)) (ψ t)) t ∧
      ∑ i, vfb H0 n (ψ t) (ndd t) i = 0 ∧ ∀ i, tdens n (ψ t) i = nn t i) ∨
    ∀ δ > 0, ∃ s ∈ Icc t0 T, ∃ ψ : ℝ → (C → ℝ) × (C → ℝ), ψ t0 = ψ0 ∧
      (∀ t ∈ Icc t0 s, ψ t ∈ omega H0 n ∧
        HasDerivAt ψ (schr H0 n (vfb H0 n (ψ t) (ndd t)) (ψ t)) t ∧
        ∑ i, vfb H0 n (ψ t) (ndd t) i = 0 ∧ ∀ i, tdens n (ψ t) i = nn t i) ∧
      |(kJ H0 n (ψ s)).det| < δ := by
  rcases nlse_global hH0 hcont hT hψ0 with ⟨α, hg⟩ | h
  · exact Or.inl ⟨α, hg.1, tdsol_of_goodOn hH0 hN hnd hndd hsum hg hρ0 hj0⟩
  · refine Or.inr fun δ hδ => ?_
    obtain ⟨s, hs, α, hg, hdet⟩ := h δ hδ
    exact ⟨s, hs, α, hg.1, tdsol_of_goodOn hH0 hN hnd hndd hsum hg hρ0 hj0, hdet⟩

end tddft

end DFT
