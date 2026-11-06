/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.BoxSturm
import DFT.Continuum.BoxExtend
import DFT.Continuum.BoxPicone
import DFT.Continuum.BoxSolve

/-!
# Ground states in the box exist

For every continuous potential `v` on `[0, 1]` the box Hamiltonian has a ground state in the `C²`
form domain, so `hk_box` holds without assuming ground states.

Shooting: for each energy `E`, `sol v E` solves `ψ'' = (v - E) ψ`, `ψ(0) = 0`, `ψ'(0) = 1`
(`BoxSolve`). It stays positive on `(0, 1]` for `E ≤ -‖v‖` and has a zero in `(0, 1)` for
`E ≥ ‖v‖ + 16` (`BoxSturm`). At `E* = sup {E | ψ_E > 0 on (0, 1]}`, by continuous dependence on `E`:

* `star_nonneg`, `star_pos`: `ψ_{E*} ≥ 0` on `[0, 1]` and `> 0` on `(0, 1)` (an interior zero
  would be a double zero, forcing `ψ ≡ 0`);
* `star_one`: `ψ_{E*}(1) = 0` (otherwise slightly larger `E` would still be positive);
* `star_d1`: `ψ'_{E*}(1) < 0`.

The Picone inequality (`BoxPicone`) then shows that no state has lower energy than `E*`, and a
cutoff (`BoxExtend`) makes `ψ_{E*}` a `C²` function on `ℝ`.

* `exists_isGS`: every continuous potential has a ground state.
* `hk_box_complete`: **Hohenberg–Kohn for one particle in a box, unconditional.**
-/
namespace DFT.Continuum.Box

open MeasureTheory Set Filter Topology

/-- The coefficient `v - E`. -/
noncomputable def Wof (v : Pot) (E : ℝ) : ℝ → ℝ := fun x => ext v x - E

lemma continuous_Wof (v : Pot) (E : ℝ) : Continuous (Wof v E) :=
  (continuous_ext v).sub continuous_const

/-- The shooting solution `ψ_E` (with `ψ_E(0) = 0`, `ψ_E'(0) = 1`) as a pair `(ψ_E, ψ_E')`. -/
noncomputable def sol (v : Pot) (E : ℝ) : ℝ → ℝ × ℝ :=
  Classical.choose (exists_sol (continuous_Wof v E))

lemma sol_zero (v : Pot) (E : ℝ) : sol v E 0 = (0, 1) :=
  (Classical.choose_spec (exists_sol (continuous_Wof v E))).1

lemma sol_deriv (v : Pot) (E : ℝ) :
    ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt (sol v E) (field (Wof v E) t (sol v E t)) t :=
  (Classical.choose_spec (exists_sol (continuous_Wof v E))).2

lemma abs_ext_le (v : Pot) (x : ℝ) : |ext v x| ≤ ‖v‖ := by
  have := v.norm_coe_le_norm (projIcc 0 1 zero_le_one x)
  simpa [ext, Real.norm_eq_abs] using this

lemma Icc01_sub : Icc (0 : ℝ) 1 ⊆ Ioo (-1) 2 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma continuousOn_sol (v : Pot) (E : ℝ) : ContinuousOn (sol v E) (Icc 0 1) :=
  fun t ht => (sol_deriv v E t (Icc01_sub ht)).continuousAt.continuousWithinAt

/-- Uniform continuity of the shooting solution in `E`. -/
lemma sol_close (v : Pot) (E : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ E', |E' - E| ≤ 1 →
    ∀ t ∈ Icc (0 : ℝ) 1, ‖sol v E' t - sol v E t‖ ≤ C * |E' - E| := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_sol v E)
  set K := 1 + (‖v‖ + |E| + 1)
  have hK : 0 < K := by positivity
  refine ⟨(max M 0) * ((Real.exp K - 1) / K), by
    have : 0 ≤ Real.exp K - 1 := by linarith [Real.add_one_le_exp K]
    positivity, fun E' hE' t ht => ?_⟩
  have hB : ∀ s ∈ Icc (0 : ℝ) 1, |Wof v E' s| ≤ ‖v‖ + |E| + 1 := by
    intro s _
    have h1 := abs_ext_le v s
    have h2 : |E'| ≤ |E| + 1 := by
      have := abs_sub_abs_le_abs_sub E' E; linarith
    calc |Wof v E' s| = |ext v s - E'| := rfl
      _ ≤ |ext v s| + |E'| := abs_sub _ _
      _ ≤ _ := by linarith
  have hε : ∀ s ∈ Icc (0 : ℝ) 1, |Wof v E' s - Wof v E s| ≤ |E' - E| := by
    intro s _; simp only [Wof]; rw [show ext v s - E' - (ext v s - E) = -(E' - E) by ring, abs_neg]
  have hM' : ∀ s ∈ Icc (0 : ℝ) 1, ‖sol v E s‖ ≤ max M 0 := fun s hs =>
    (hM s hs).trans (le_max_left _ _)
  have h := sol_dist_le (by rw [sol_zero, sol_zero]) (sol_deriv v E') (sol_deriv v E) hB hM' hε t ht
  refine h.trans ?_
  rw [gronwallBound_of_K_ne_0 hK.ne']
  simp only [zero_mul, zero_add]
  have he : Real.exp (K * t) - 1 ≤ Real.exp K - 1 := by
    have : K * t ≤ K := by nlinarith [ht.2]
    linarith [Real.exp_le_exp.mpr this]
  have he0 : 0 ≤ Real.exp (K * t) - 1 := by
    have : 0 ≤ K * t := by nlinarith [ht.1]
    linarith [Real.add_one_le_exp (K * t)]
  have hEp : 0 ≤ |E' - E| * max M 0 := by positivity
  calc |E' - E| * max M 0 / K * (Real.exp (K * t) - 1)
      ≤ |E' - E| * max M 0 / K * (Real.exp K - 1) := by
        apply mul_le_mul_of_nonneg_left he; positivity
    _ = max M 0 * ((Real.exp K - 1) / K) * |E' - E| := by ring

/-- `E` keeps the shooting solution positive on `(0, 1]`. -/
def Pos (v : Pot) (E : ℝ) : Prop := ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (sol v E t).1

lemma pos_low (v : Pot) : Pos v (-‖v‖) := by
  refine pos_of_nonneg (sol_zero v _) (sol_deriv v _) fun t _ => ?_
  have := abs_ext_le v t
  simp only [Wof]; linarith [neg_abs_le (ext v t)]

lemma not_pos_high (v : Pot) {E : ℝ} (hE : ‖v‖ + 16 ≤ E) : ¬ Pos v E := by
  intro hP
  obtain ⟨t, ht, h0⟩ := exists_zero_of_le (sol_zero v E) (sol_deriv v E)
    (fun t _ => by have := abs_ext_le v t; simp only [Wof]; linarith [le_abs_self (ext v t)])
  exact (hP t ⟨ht.1, ht.2.le⟩).ne' h0

lemma bdd (v : Pot) : BddAbove {E | Pos v E} :=
  ⟨‖v‖ + 16, fun E hE => by by_contra h; exact not_pos_high v (le_of_not_ge h) hE⟩

/-- The ground-state energy found by shooting. -/
noncomputable def Estar (v : Pot) : ℝ := sSup {E | Pos v E}

lemma fst_le_norm (a b : ℝ × ℝ) : |a.1 - b.1| ≤ ‖a - b‖ := by
  have := norm_fst_le (a - b); simpa [Real.norm_eq_abs] using this

lemma snd_le_norm (a b : ℝ × ℝ) : |a.2 - b.2| ≤ ‖a - b‖ := by
  have := norm_snd_le (a - b); simpa [Real.norm_eq_abs] using this

lemma star_nonneg (v : Pot) : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (sol v (Estar v) t).1 := by
  intro t ht
  obtain ⟨C, hC0, hC⟩ := sol_close v (Estar v)
  by_contra hneg
  push Not at hneg
  set m := -(sol v (Estar v) t).1
  have hm : 0 < m := by simp only [m]; linarith
  have hne : ({E | Pos v E} : Set ℝ).Nonempty := ⟨_, pos_low v⟩
  obtain ⟨E, hE, hlt⟩ := exists_lt_of_lt_csSup hne
    (show Estar v - min 1 (m / (C + 1)) < Estar v by
      have : 0 < min 1 (m / (C + 1)) := lt_min one_pos (by positivity)
      linarith)
  have hEle : E ≤ Estar v := le_csSup (bdd v) hE
  have hd : |E - Estar v| ≤ min 1 (m / (C + 1)) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  have h1 := (fst_le_norm _ _).trans (hC E (hd.trans (min_le_left _ _)) t ht)
  rcases ht.1.eq_or_lt with h0 | htpos
  · subst h0; simp [sol_zero] at hneg
  have hPE := hE t ⟨htpos, ht.2⟩
  have : C * |E - Estar v| < m := by
    calc C * |E - Estar v| ≤ C * (m / (C + 1)) :=
          mul_le_mul_of_nonneg_left (hd.trans (min_le_right _ _)) hC0
      _ < m := by rw [mul_div_assoc']; rw [div_lt_iff₀ (by linarith)]; nlinarith
  have := (abs_le.mp h1).2
  simp only [m] at *
  linarith

lemma Icc01_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t ∈ Ioo (-1 : ℝ) 2 := Icc01_sub ht

lemma star_pos (v : Pot) : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < (sol v (Estar v) t).1 := by
  intro z hz
  rcases (star_nonneg v z ⟨hz.1.le, hz.2.le⟩).lt_or_eq with h | h
  · exact h
  exfalso
  set α := sol v (Estar v)
  have hmin : IsLocalMin (fun t => (α t).1) z := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with t ht
    rw [← h]; exact star_nonneg v t ⟨ht.1.le, ht.2.le⟩
  have h2 := hmin.hasDerivAt_eq_zero
    (hasDerivAt_fst_of (sol_deriv v _) (Icc01_mem ⟨hz.1.le, hz.2.le⟩))
  have hz0 : α z = 0 := Prod.ext h.symm h2
  have := sol_eq_zero_of_eq_zero (continuous_Wof v _) (sol_deriv v _)
    (Icc01_mem ⟨hz.1.le, hz.2.le⟩) hz0 0 ⟨by norm_num, by norm_num⟩
  rw [sol_zero] at this
  simp at this

lemma star_one (v : Pot) : (sol v (Estar v) 1).1 = 0 := by
  set E := Estar v
  set α := sol v E
  rcases (star_nonneg v 1 ⟨zero_le_one, le_rfl⟩).lt_or_eq with h | h
  swap
  · exact h.symm
  exfalso
  -- `α.2 ≥ 3/4` near `0`
  have hc2 : ContinuousAt (fun t => (α t).2) 0 :=
    (hasDerivAt_snd_of (sol_deriv v E) (Icc01_mem ⟨le_rfl, zero_le_one⟩)).continuousAt
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc2 (1 / 4) (by norm_num)
  set δ' := min (δ / 2) (1 / 2)
  have hδ' : 0 < δ' := lt_min (by linarith) (by norm_num)
  have hδ'1 : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hnear : ∀ s ∈ Icc (0 : ℝ) δ', 3 / 4 ≤ (α s).2 := by
    intro s hs
    have hd : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      linarith [hs.2, min_le_left (δ / 2) (1 / 2)]
    have := hδc hd
    rw [Real.dist_eq] at this
    have h0 : (α 0).2 = 1 := by simp [α, sol_zero]
    rw [h0] at this
    linarith [(abs_lt.mp this).1]
  -- the minimum of  on 
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hδ'1.le)
    ((continuousOn_sol v E).fst.mono (Icc_subset_Icc_left hδ'.le))
  set m := (α t0).1
  have hm : 0 < m := by
    rcases ht0.2.lt_or_eq with hlt | heq
    · exact star_pos v t0 ⟨lt_of_lt_of_le hδ' ht0.1, hlt⟩
    · simp only [m, heq]; exact h
  obtain ⟨C, hC0, hC⟩ := sol_close v E
  set η := min 1 (min (1 / 4) (m / 2)) / (C + 1)
  have hη : 0 < η := div_pos (lt_min one_pos (lt_min (by norm_num) (by linarith))) (by linarith)
  have hCη : C * η ≤ min 1 (min (1 / 4) (m / 2)) := by
    simp only [η]
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ min 1 (min (1 / 4) (m / 2)) :=
      (lt_min one_pos (lt_min (by norm_num) (by linarith))).le
    nlinarith
  have hη1 : η ≤ 1 := by
    simp only [η]
    rw [div_le_one (by linarith)]
    linarith [min_le_left 1 (min (1 / 4) (m / 2))]
  set E' := E + η
  have hE'E : |E' - E| = η := by simp only [E']; rw [add_sub_cancel_left, abs_of_pos hη]
  have hclose : ∀ s ∈ Icc (0 : ℝ) 1, ‖sol v E' s - α s‖ ≤ C * η := fun s hs => by
    have := hC E' (by rw [hE'E]; exact hη1) s hs
    rwa [hE'E] at this
  have hPos : Pos v E' := by
    intro t ht
    rcases le_or_gt t δ' with htδ | htδ
    · -- on , 
      have hder : ∀ s ∈ Icc (0 : ℝ) t, 1 / 2 ≤ (sol v E' s).2 := by
        intro s hs
        have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2, ht.2]⟩
        have h1 := (snd_le_norm _ _).trans (hclose s hs1)
        have h2 := hnear s ⟨hs.1, hs.2.trans htδ⟩
        have h3 : C * η ≤ 1 / 4 := hCη.trans ((min_le_right _ _).trans (min_le_left _ _))
        linarith [(abs_le.mp h1).1]
      have hmvt := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 t)
        (f := fun s => (sol v E' s).1) (C := 1 / 2)
        ((continuousOn_sol v E').fst.mono (Icc_subset_Icc_right ht.2))
        (fun s hs => by
          rw [interior_Icc] at hs
          exact (hasDerivAt_fst_of (sol_deriv v E')
            (Icc01_mem ⟨hs.1.le, by linarith [hs.2, ht.2]⟩)).differentiableAt
            |>.differentiableWithinAt)
        (fun s hs => by
          rw [interior_Icc] at hs
          rw [(hasDerivAt_fst_of (sol_deriv v E')
            (Icc01_mem ⟨hs.1.le, by linarith [hs.2, ht.2]⟩)).deriv]
          exact hder s ⟨hs.1.le, hs.2.le⟩)
        0 ⟨le_rfl, ht.1.le⟩ t ⟨ht.1.le, le_rfl⟩ ht.1.le
      have h00 : (sol v E' 0).1 = 0 := by simp [sol_zero]
      simp only [h00, sub_zero] at hmvt
      linarith [ht.1]
    · have hs1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have h1 := (fst_le_norm _ _).trans (hclose t hs1)
      have h2 : m ≤ (α t).1 := hmin ⟨htδ.le, ht.2⟩
      have h3 : C * η ≤ m / 2 := hCη.trans ((min_le_right _ _).trans (min_le_right _ _))
      linarith [(abs_le.mp h1).1]
  have := le_csSup (bdd v) hPos
  simp only [E'] at this
  change E + η ≤ E at this
  linarith

lemma star_d1 (v : Pot) : (sol v (Estar v) 1).2 < 0 := by
  set α := sol v (Estar v)
  have hder := hasDerivAt_fst_of (sol_deriv v (Estar v)) (Icc01_mem ⟨zero_le_one, le_rfl⟩)
  have hle : (α 1).2 ≤ 0 := by
    have hT := (hasDerivAt_iff_tendsto_slope.mp hder).mono_left
      (nhdsWithin_mono (s := Iio 1) _
        (fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_lt (show x < 1 from hx))))
    refine le_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [slope_def_field, star_one v, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos (star_pos v t ht).le (by linarith [ht.2])
  rcases hle.lt_or_eq with h | h
  · exact h
  exfalso
  have h1 : α 1 = 0 := Prod.ext (star_one v) h
  have := sol_eq_zero_of_eq_zero (continuous_Wof v _) (sol_deriv v _)
    (Icc01_mem ⟨zero_le_one, le_rfl⟩) h1 0 ⟨by norm_num, by norm_num⟩
  rw [sol_zero] at this
  simp at this

/-- The energy above `E`, as an integral. -/
lemma Q_sub_eq (v : Pot) (E : ℝ) {φ : ℝ → ℝ} (hφ : φ ∈ Dom) :
    Q setting v φ - E * ip (μ := μ1) φ φ = ∫ x, (deriv φ x ^ 2 + Wof v E x * φ x ^ 2) ∂μ1 := by
  have i1 := integrable_of_continuous ((cont_deriv_of_mem hφ).mul (cont_deriv_of_mem hφ))
  have i2 := integrable_of_continuous ((continuous_ext v).mul (hφ.1.continuous.mul hφ.1.continuous))
  have i3 := integrable_of_continuous (hφ.1.continuous.mul hφ.1.continuous)
  have hpt : (fun x => deriv φ x ^ 2 + Wof v E x * φ x ^ 2) = fun x =>
      (deriv φ x * deriv φ x + ext v x * (φ x * φ x)) - E * (φ x * φ x) := by
    funext x; simp only [Wof]; ring
  rw [hpt, integral_sub (f := fun x => deriv φ x * deriv φ x + ext v x * (φ x * φ x))
    (g := fun x => E * (φ x * φ x)) (i1.add i2) (i3.const_mul E),
    integral_add (f := fun x => deriv φ x * deriv φ x) (g := fun x => ext v x * (φ x * φ x)) i1 i2,
    integral_const_mul]
  rfl

/-- **Every continuous potential in the box has a ground state** (in the `C²` form domain). -/
theorem exists_isGS (v : Pot) : ∃ ψ, IsGS setting v ψ := by
  set E := Estar v
  set α := sol v E
  obtain ⟨ψe, hψe, hψeq⟩ :=
    exists_contDiff_ext (contDiffOn_sol (continuous_Wof v E) (sol_deriv v E))
  have hIcc : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hev : ∀ t ∈ Icc (0 : ℝ) 1, ψe =ᶠ[𝓝 t] fun s => (α s).1 := fun t ht =>
    Filter.eventually_of_mem (Ioo_mem_nhds (hIcc t ht).1 (hIcc t ht).2) fun s hs => hψeq s hs
  have hdψ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψe ((α t).2) t := fun t ht =>
    (hasDerivAt_fst_of (sol_deriv v E) (Icc01_mem ht)).congr_of_eventuallyEq (hev t ht)
  have hψ0 : ψe 0 = 0 := by
    rw [hψeq 0 (hIcc 0 ⟨le_rfl, zero_le_one⟩)]; simp [sol_zero]
  have hψ1 : ψe 1 = 0 := by rw [hψeq 1 (hIcc 1 ⟨zero_le_one, le_rfl⟩)]; exact star_one v
  have hD : ψe ∈ Dom := ⟨hψe, hψ0, hψ1⟩
  -- no state has energy below `E`
  have hlow : ∀ φ ∈ Dom, E * ip (μ := μ1) φ φ ≤ Q setting v φ := fun φ hφ => by
    have hp := picone (continuous_Wof v E) (ψ := fun t => (α t).1) (ψ' := fun t => (α t).2)
      (fun t ht => hasDerivAt_fst_of (sol_deriv v E) ht)
      (fun t ht => hasDerivAt_snd_of (sol_deriv v E) ht)
      (star_pos v) (by simp [α, sol_zero]) (star_one v) (by simp [α, sol_zero]) (star_d1 v) hφ
    have := Q_sub_eq v E hφ
    linarith
  -- `ψe` has energy exactly `E`
  have hcIcc : ContinuousOn α (Icc 0 1) := continuousOn_sol v E
  have hexact : Q setting v ψe - E * ip (μ := μ1) ψe ψe = 0 := by
    rw [Q_sub_eq v E hD]
    have hcongr : ∫ x, (deriv ψe x ^ 2 + Wof v E x * ψe x ^ 2) ∂μ1 =
        ∫ x in (0 : ℝ)..1, ((α x).2 * (α x).2 + Wof v E x * (α x).1 * (α x).1) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      simp only [(hdψ x hx').deriv, hψeq x (hIcc x hx')]
      ring
    rw [hcongr]
    have hu : ContinuousOn (fun t => (α t).2) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]; exact hcIcc.snd
    have hu' : ContinuousOn (fun t => Wof v E t * (α t).1) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]; exact (continuous_Wof v E).continuousOn.mul hcIcc.fst
    have hv1 : ContinuousOn (fun t => (α t).1) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]; exact hcIcc.fst
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
      (u := fun t => (α t).2) (u' := fun t => Wof v E t * (α t).1)
      (v := fun t => (α t).1) (v' := fun t => (α t).2)
      (fun x hx => hasDerivAt_snd_of (sol_deriv v E)
        (Icc01_mem (by rwa [uIcc_of_le zero_le_one] at hx)))
      (fun x hx => hasDerivAt_fst_of (sol_deriv v E)
        (Icc01_mem (by rwa [uIcc_of_le zero_le_one] at hx)))
      hu'.intervalIntegrable hu.intervalIntegrable
    have h01 : (α 1).1 = 0 := star_one v
    have h00 : (α 0).1 = 0 := by simp [α, sol_zero]
    simp only [h01, h00, mul_zero, sub_zero] at hibp
    rw [intervalIntegral.integral_add (f := fun x => (α x).2 * (α x).2)
      (g := fun x => Wof v E x * (α x).1 * (α x).1) (hu.mul hu).intervalIntegrable
      (hu'.mul hv1).intervalIntegrable, hibp]
    simp only [zero_sub, neg_add_cancel]
  -- `ψe` is not zero
  have hpos : 0 < ip (μ := μ1) ψe ψe := by
    have hint := integrable_of_continuous (hψe.continuous.mul hψe.continuous)
    refine (integral_pos_iff_support_of_nonneg (fun x => mul_self_nonneg (ψe x)) hint).2 ?_
    rw [Measure.restrict_apply' measurableSet_Ioo]
    have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (fun x => ψe x * ψe x) ∩ Ioo 0 1 := by
      intro x hx
      refine ⟨?_, hx⟩
      have : 0 < ψe x := by
        rw [hψeq x (hIcc x ⟨hx.1.le, hx.2.le⟩)]; exact star_pos v x hx
      exact (mul_pos this this).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    simp
  refine ⟨ψe, hD, hpos, fun φ hφ => ?_⟩
  have h1 := hlow φ hφ
  have hQ : Q setting v ψe = E * ip (μ := μ1) ψe ψe := by linarith
  rw [hQ]
  nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]

/-- **Hohenberg–Kohn for one particle in a box, unconditional.** Every continuous potential on
`[0, 1]` has a ground state, and ground states of two continuous potentials with the same density
`ψ²` force the potentials to differ by a constant. -/
theorem hk_box_complete (v v' : Pot) :
    (∃ ψ, IsGS setting v ψ) ∧ ∀ ψ ψ', IsGS setting v ψ → IsGS setting v' ψ' →
      (∀ x ∈ Ioo (0 : ℝ) 1, ψ x ^ 2 = ψ' x ^ 2) → ∃ k : ℝ, v - v' = k • one :=
  ⟨exists_isGS v, fun _ _ h h' hρ => hk_box h h' hρ⟩

end DFT.Continuum.Box
