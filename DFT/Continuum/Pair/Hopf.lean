/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Pair.MaxPrinciple

/-!
# Hopf's lemma: no sign change through critical zeros

A `C²` function on the open square that is a supersolution of `-Δ + c` (`c ≥ 0`) wherever it is
positive, and whose gradient vanishes at each of its zeros, is either positive on the whole square
or nonpositive on the whole square.

* `exists_zero_segment`: the intermediate value theorem along a segment.
* `fderiv_eq_zero_of_d`: vanishing partial derivatives give a vanishing derivative.
* `local_nonpos`: near a zero, `u ≤ 0` (Hopf's lemma on the largest Euclidean ball inside `{u > 0}`,
  with the barrier and the weak comparison of `MaxPrinciple`).
* `pos_or_nonpos`: the global statement, by connectedness of the square.
-/

namespace DFT

namespace Continuum

namespace Pair

open Set Filter Topology Metric

lemma eu_segment (y p : ℝ × ℝ) (s : ℝ) : eu y (y + s • (p - y)) = s ^ 2 * eu y p := by
  simp only [eu, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

/-- The intermediate value theorem along a segment. -/
lemma exists_zero_segment {u : ℝ × ℝ → ℝ} (hu : Continuous u) {y p : ℝ × ℝ} (hy : 0 < u y)
    (hp : u p < 0) : ∃ s ∈ Ioo (0 : ℝ) 1, u (y + s • (p - y)) = 0 := by
  set g : ℝ → ℝ := fun s => u (y + s • (p - y))
  have hg : Continuous g := hu.comp (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : g 0 = u y := by simp [g]
  have h1 : g 1 = u p := by simp [g]
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' zero_le_one hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g 1) (g 0) by rw [h0, h1]; exact ⟨hp.le, hy.le⟩)
  refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, hgs⟩
  · rintro rfl; rw [h0] at hgs; linarith
  · rintro rfl; rw [h1] at hgs; linarith

/-- Vanishing partial derivatives give a vanishing derivative. -/
lemma fderiv_eq_zero_of_d {u : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h1 : d1 u x = 0) (h2 : d2 u x = 0) :
    fderiv ℝ u x = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp only [d1, d2] at h1 h2
  simp [h1, h2]

/-- **Local Hopf lemma.** Near a zero of `u` in the square, `u ≤ 0`. -/
theorem local_nonpos {u c : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hc : Continuous c)
    (hc0 : ∀ p, 0 ≤ c p) (hsup : ∀ p ∈ Sq, 0 < u p → 0 ≤ -lap u p + c p * u p)
    (hgrad : ∀ p ∈ Sq, u p = 0 → d1 u p = 0 ∧ d2 u p = 0) {z : ℝ × ℝ} (hz : z ∈ Sq)
    (h0 : u z = 0) : ∀ᶠ p in 𝓝 z, u p ≤ 0 := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  obtain ⟨r0, hr0, hr0s⟩ := Metric.isOpen_iff.mp (isOpen_Ioo.prod isOpen_Ioo) z hz
  set r := r0 / 2
  have hr : 0 < r := by positivity
  have hB : closedBall z r ⊆ Sq := (closedBall_subset_ball (by simp only [r]; linarith)).trans hr0s
  by_contra hne
  obtain ⟨y, hyu, hyb⟩ := ((Filter.not_eventually.mp hne).and_eventually
    (ball_mem_nhds z (show 0 < r / 4 by positivity))).exists
  have hyz : dist y z < r / 4 := hyb
  have hypos : 0 < u y := lt_of_not_ge hyu
  -- the closest zero of `u` to `y`
  set Z' := closedBall z r ∩ {p | u p = 0}
  have hZc : IsCompact Z' :=
    (isCompact_closedBall z r).inter_right (isClosed_eq hu.continuous continuous_const)
  have hZn : Z'.Nonempty := ⟨z, mem_closedBall_self hr.le, h0⟩
  obtain ⟨x1, hx1Z, hx1min⟩ := hZc.exists_isMinOn hZn (continuous_eu y).continuousOn
  set R2 := eu y x1
  have hx1u : u x1 = 0 := hx1Z.2
  have hR2z : R2 ≤ eu y z := hx1min ⟨mem_closedBall_self hr.le, h0⟩
  have hR2small : R2 < (r / 2) ^ 2 := by
    have := eu_le_dist_sq z y
    rw [dist_comm] at hyz
    nlinarith [dist_nonneg (x := z) (y := y)]
  have hR2pos : 0 < R2 := by
    rcases (show 0 ≤ R2 by simp only [R2, eu]; positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      have : dist x1 y ^ 2 ≤ R2 := dist_sq_le_eu x1 y
      rw [← h] at this
      have hd : dist x1 y = 0 := by nlinarith [dist_nonneg (x := x1) (y := y)]
      rw [dist_eq_zero.mp hd] at hx1u
      linarith
  -- points closer to `y` than `R` lie in the small ball around `z`
  have hnear : ∀ p, eu y p ≤ R2 → dist p z < 3 * r / 4 := by
    intro p hp
    have := dist_lt_of_eu_lt (s := r / 2) (by positivity) (lt_of_le_of_lt hp hR2small)
    linarith [dist_triangle p y z]
  have hinSq : ∀ p, eu y p ≤ R2 → p ∈ Sq := fun p hp =>
    hB (mem_closedBall.mpr (by linarith [hnear p hp]))
  -- no zero strictly inside the Euclidean ball around `y`
  have hnz : ∀ p, eu y p < R2 → u p ≠ 0 := by
    intro p hp h
    have := hx1min ⟨mem_closedBall.mpr (by linarith [hnear p hp.le]), h⟩
    exact absurd this (not_le.mpr hp)
  -- hence `u > 0` inside and `u ≥ 0` on the closed ball (intermediate values on segments)
  have hnn : ∀ p, eu y p ≤ R2 → 0 ≤ u p := by
    intro p hp
    by_contra hneg
    push Not at hneg
    obtain ⟨s, hs, hzero⟩ := exists_zero_segment hu.continuous hypos hneg
    have : eu y (y + s • (p - y)) < R2 := by
      rw [eu_segment]
      have hs2 : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
      have hep : 0 ≤ eu y p := by simp only [eu]; positivity
      rcases hep.lt_or_eq with hep' | hep'
      · nlinarith
      · rw [← hep']; simpa using hR2pos
    exact hnz _ this hzero
  have hposin : ∀ p, eu y p < R2 → 0 < u p := fun p hp =>
    lt_of_le_of_ne (hnn p hp.le) (Ne.symm (hnz p hp))
  -- the gradient vanishes at `x1`
  have hx1Sq : x1 ∈ Sq := hinSq x1 le_rfl
  obtain ⟨hg1, hg2⟩ := hgrad x1 hx1Sq hx1u
  have hgrad0 : fderiv ℝ u x1 = 0 := fderiv_eq_zero_of_d hg1 hg2
  -- the annulus
  set Abar := {p | R2 / 4 ≤ eu y p ∧ eu y p ≤ R2}
  have hAc : IsCompact Abar := by
    refine (isCompact_closedBall y r).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_eu y)).inter
        (isClosed_le (continuous_eu y) continuous_const)) fun p hp => ?_
    have hd := dist_lt_of_eu_lt (s := r / 2) (by positivity) (lt_of_le_of_lt hp.2 hR2small)
    exact mem_closedBall.mpr (by linarith)
  -- the inner circle and the minimum of `u` on it
  set Cin := {p | eu y p = R2 / 4}
  have hCc : IsCompact Cin :=
    hAc.of_isClosed_subset (isClosed_eq (continuous_eu y) continuous_const)
      fun p hp => ⟨hp.ge, by rw [mem_ofPred_eq] at hp; linarith⟩
  have hCn : Cin.Nonempty := by
    refine ⟨(y.1 + Real.sqrt (R2 / 4), y.2), ?_⟩
    simp only [Cin, mem_ofPred_eq, eu, add_sub_cancel_left, sub_self]
    rw [Real.sq_sqrt (by positivity)]; ring
  obtain ⟨pm, hpmC, hpmmin⟩ := hCc.exists_isMinOn hCn hu.continuous.continuousOn
  set m := u pm
  have hm : 0 < m := hposin pm (by rw [hpmC]; linarith)
  set ε := m / 2
  have hε : 0 < ε := by positivity
  -- the bound on `c`
  obtain ⟨C0, hC0⟩ := hAc.exists_bound_of_continuousOn hc.continuousOn
  set C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hcC : ∀ p ∈ Abar, c p ≤ C := fun p hp =>
    ((le_abs_self (c p)).trans (by simpa [Real.norm_eq_abs] using hC0 p hp)).trans
      (le_max_left _ _)
  set α := max 1 ((8 + 2 * C) / R2)
  have hα1 : 1 ≤ α := le_max_left _ _
  have hαR : 8 + 2 * C ≤ α * R2 := by
    have := le_max_right 1 ((8 + 2 * C) / R2)
    rw [div_le_iff₀ hR2pos] at this
    exact this
  set K := Real.exp (-α * R2)
  set h := barrier α y K
  set w : ℝ × ℝ → ℝ := fun p => u p - ε * h p
  have hw : ContDiff ℝ 2 w := hu.sub (contDiff_const.mul (contDiff_barrier α y K))
  have hlapw : ∀ p, lap w p = lap u p - ε * lap h p := fun p =>
    lap_sub_mul hud (differentiable_barrier α y K)
      ((contDiff_d1 hu).differentiable one_ne_zero)
      (by rw [d1_barrier]; exact differentiable_bar1 α y)
      ((contDiff_d2 hu).differentiable one_ne_zero)
      (by rw [d2_barrier]; exact differentiable_bar2 α y) ε p
  have hh1 : ∀ p, h p ≤ 1 := by
    intro p
    have : Real.exp (-α * eu y p) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ eu y p := by simp only [eu]; positivity
      nlinarith
    simp only [h, barrier]; linarith [Real.exp_pos (-α * R2)]
  -- weak comparison on the annulus
  have hcomp : ∀ p ∈ Abar, 0 ≤ w p := by
    obtain ⟨q, hqA, hqmin⟩ := hAc.exists_isMinOn ⟨pm, by rw [mem_ofPred_eq, hpmC]; constructor <;>
      linarith⟩ hw.continuous.continuousOn
    intro p hp
    refine le_trans ?_ (hqmin hp)
    by_contra hneg
    push Not at hneg
    rcases hqA.1.lt_or_eq with hlo | hlo
    · rcases hqA.2.lt_or_eq with hhi | hhi
      · -- interior point: a local minimum of `w`, where `u > 0`
        have hopen : IsOpen {p | R2 / 4 < eu y p ∧ eu y p < R2} :=
          (isOpen_lt continuous_const (continuous_eu y)).inter
            (isOpen_lt (continuous_eu y) continuous_const)
        have hlmin : IsLocalMin w q :=
          Filter.eventually_of_mem (hopen.mem_nhds ⟨hlo, hhi⟩) fun p hp =>
            hqmin ⟨hp.1.le, hp.2.le⟩
        have h11 := d11_nonneg_of_isLocalMin hw hlmin
        have h22 := d22_nonneg_of_isLocalMin hw hlmin
        have hqSq := hinSq q hqA.2
        have hLu := hsup q hqSq (hposin q hhi)
        have hbar := barrier_neg (c := c q) (e := eu y q) hα1 hαR hC hqA.1 (hc0 q) (hcC q hqA)
        rw [← lap_barrier α y K q] at hbar
        have hlap : lap w q = d11 w q + d22 w q := rfl
        rw [hlapw q] at hlap
        have hwq : w q = u q - ε * h q := rfl
        have hhq : h q = Real.exp (-α * eu y q) - Real.exp (-α * R2) := rfl
        rw [← hhq] at hbar
        nlinarith [hc0 q]
      · -- outer circle: `h = 0`
        have : h q = 0 := by simp only [h, barrier, K, hhi, sub_self]
        have := hnn q hqA.2
        simp only [w] at hneg
        rw [‹h q = 0›] at hneg
        linarith
    · -- inner circle: `u ≥ m > ε ≥ ε h`
      have hq' : q ∈ Cin := hlo.symm
      have := hpmmin hq'
      have := hh1 q
      simp only [w] at hneg
      have e2 : m ≤ u q := ‹u pm ≤ u q›
      have e1 : ε * h q ≤ ε := mul_le_of_le_one_right hε.le (hh1 q)
      have e3 : ε = m / 2 := rfl
      linarith
  -- Hopf: `u` grows linearly from `x1` towards `y`, contradicting `∇u(x1) = 0`
  set d := y - x1
  set κ := ε * K * (α * R2)
  have hκ : 0 < κ := by positivity
  have hlin : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), κ * t ≤ u (x1 + t • d) := by
    intro t ht
    have heu : eu y (x1 + t • d) = (1 - t) ^ 2 * R2 := by
      simp only [eu, R2, d, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
      ring
    have hA : x1 + t • d ∈ Abar := by
      rw [mem_ofPred_eq, heu]
      have ha : 1 / 4 ≤ (1 - t) ^ 2 := by nlinarith [ht.1, ht.2]
      have hb : (1 - t) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right ha hR2pos.le]
      · nlinarith [mul_le_mul_of_nonneg_right hb hR2pos.le]
    have hwge := hcomp _ hA
    simp only [w, h, barrier] at hwge
    rw [heu] at hwge
    have hexp : K * (α * R2 * t) ≤ Real.exp (-α * ((1 - t) ^ 2 * R2)) - K := by
      have h1 := Real.add_one_le_exp (-α * ((1 - t) ^ 2 * R2) - -α * R2)
      have h2 : Real.exp (-α * ((1 - t) ^ 2 * R2)) =
          K * Real.exp (-α * ((1 - t) ^ 2 * R2) - -α * R2) := by
        simp only [K]; rw [← Real.exp_add]; ring_nf
      rw [h2]
      have hK : 0 < K := Real.exp_pos _
      have hge : α * R2 * t ≤ -α * ((1 - t) ^ 2 * R2) - -α * R2 := by
        have key : -α * ((1 - t) ^ 2 * R2) - -α * R2 - α * R2 * t =
            α * R2 * (t * (1 - t)) := by ring
        have hnn' : 0 ≤ α * R2 * (t * (1 - t)) :=
          mul_nonneg (mul_nonneg (by linarith) hR2pos.le)
            (mul_nonneg ht.1.le (by linarith [ht.2]))
        linarith
      nlinarith
    nlinarith
  -- little-o at `x1`
  have hfd : HasFDerivAt u (0 : ℝ × ℝ →L[ℝ] ℝ) x1 := by
    rw [← hgrad0]; exact (hud x1).hasFDerivAt
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hfd
  set η := κ / (2 * (‖d‖ + 1))
  have hη : 0 < η := by positivity
  have hev := hlo.def hη
  have htend : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 ((0 : ℝ) • d)) :=
      (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const d
    rwa [zero_smul] at h
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hev)
  set t := min (δ / 2) (1 / 2)
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb := hδb htδ
  simp only [hx1u, zero_apply, sub_zero, Real.norm_eq_abs] at hb
  have hl := hlin t ⟨ht0, min_le_right _ _⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
  have hu_le : u (x1 + t • d) ≤ η * (t * ‖d‖) := (le_abs_self _).trans hb
  have : η * (t * ‖d‖) < κ * t := by
    simp only [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg d, mul_pos hκ ht0, mul_nonneg (mul_pos hκ ht0).le (norm_nonneg d)]
  linarith

/-- **No sign change through critical zeros.** A `C²` function on the open square that is a
supersolution of `-Δ + c` (`c ≥ 0`) where it is positive, and whose gradient vanishes at every zero,
is either positive on the whole square or nonpositive on the whole square. -/
theorem pos_or_nonpos {u c : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hc : Continuous c)
    (hc0 : ∀ p, 0 ≤ c p) (hsup : ∀ p ∈ Sq, 0 < u p → 0 ≤ -lap u p + c p * u p)
    (hgrad : ∀ p ∈ Sq, u p = 0 → d1 u p = 0 ∧ d2 u p = 0) :
    (∀ p ∈ Sq, 0 < u p) ∨ ∀ p ∈ Sq, u p ≤ 0 := by
  set A := {p | ∀ᶠ q in 𝓝 p, u q ≤ 0}
  set B := {p | 0 < u p}
  have hA : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hBo : IsOpen B := isOpen_lt continuous_const hu.continuous
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro p ⟨hpA, hpB⟩
    have := hpA.self_of_nhds
    exact absurd hpB (not_lt.mpr this)
  have hcover : Sq ⊆ A ∪ B := by
    intro p hp
    rcases lt_trichotomy (u p) 0 with hneg | hz | hpos
    · left
      exact (hu.continuous.continuousAt.eventually_lt continuousAt_const hneg).mono
        fun q hq => hq.le
    · exact Or.inl (local_nonpos hu hc hc0 hsup hgrad hp hz)
    · exact Or.inr hpos
  have hconn : IsPreconnected Sq := ((convex_Ioo 0 1).prod (convex_Ioo 0 1)).isPreconnected
  rcases hconn.subset_or_subset hA hBo hdisj hcover with h | h
  · exact Or.inr fun p hp => (h hp).self_of_nhds
  · exact Or.inl fun p hp => h hp

end Pair

end Continuum

end DFT
