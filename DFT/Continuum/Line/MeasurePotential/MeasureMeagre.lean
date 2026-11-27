/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureNBos

/-!
# Measure potentials do not help much: measure-`v`-representable densities are meagre

In the complete metric space `SN n` of `N`-representable densities (`Line/Prim`), the densities
`N g²` with `g²` the ground-state density of one particle in a measure potential form a meagre set
(**`vrepMeas_meagre`**). This covers one particle (`n = 0`) and `N` non-interacting bosons
(`vrepMeasN_bos_iff`). Measure potentials reach the kinked and plateau densities that continuous
potentials miss, but they still reach only a set of first Baire category.

The reason: `g' = c + ∫_{x<t} g d(μ₊ - μ₋)` is bounded (`lipschitz_of_vrepMeas`), so `g²` is
Lipschitz and its second differences are `O(h)`; such densities lie in the closed nowhere dense
sets `BsetL L 0` (`Line/MeagreC1`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

/-- **A measure-`v`-representable one-particle density is the square of a Lipschitz function.** -/
theorem lipschitz_of_vrepMeas {ρ : C01} (h : VRepMeas ρ) :
    ∃ g : ℝ → ℝ, ∃ G B : ℝ, 0 ≤ G ∧ 0 ≤ B ∧ (∀ t : Icc (0 : ℝ) 1, ρ t = g t ^ 2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ G) ∧
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |g b - g a| ≤ B * |b - a| := by
  obtain ⟨g, hg, hgc, -, -, hρ, μp, μm, _, _, c, hd⟩ := (vrepMeas_iff_explicit ρ).1 h
  obtain ⟨Cp, hCp⟩ := Gρ_bdd μp hgc
  obtain ⟨Cm, hCm⟩ := Gρ_bdd μm hgc
  set B := |c| + max Cp 0 + max Cm 0
  have hB : 0 ≤ B := by positivity
  obtain ⟨G, hG⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hgc.continuousOn
  have hdb : ∀ᵐ t ∂vol01, |deriv g t| ≤ B := by
    filter_upwards [hd] with t ht
    rw [ht]
    calc |c + Gρ μp g t - Gρ μm g t| ≤ |c| + |Gρ μp g t| + |Gρ μm g t| := by
          refine (abs_sub _ _).trans ?_
          gcongr; exact abs_add_le _ _
      _ ≤ B := by
          have := (hCp t).trans (le_max_left Cp 0)
          have := (hCm t).trans (le_max_left Cm 0)
          simp only [B]; linarith
  refine ⟨g, max G 0, B, le_max_right _ _, hB, hρ, fun t ht => ?_, fun a ha b hb => ?_⟩
  · exact (by simpa using hG t ht : |g t| ≤ G).trans (le_max_left _ _)
  · -- `g(b) - g(a) = ∫_a^b g'`
    have key : ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a ≤ b →
        |g b - g a| ≤ B * (b - a) := fun {a b} ha hb hab => by
      have hac : AbsolutelyContinuousOnInterval g a b := hg.1.mono (by
        rw [uIcc01, uIcc_of_le hab]; exact Icc_subset_Icc ha.1 hb.2)
      rw [← hac.integral_deriv_eq_sub, ← Real.norm_eq_abs]
      have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b)
        (f := deriv g) (C := B) (by
          have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hdb
          filter_upwards [h1, ae_ne_pt' 1] with t ht ht1 htI
          rw [uIoc_of_le hab] at htI
          rw [Real.norm_eq_abs]
          exact ht ⟨lt_of_le_of_lt ha.1 htI.1,
            lt_of_le_of_ne (htI.2.trans hb.2) ht1⟩)
      rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
    rcases le_total a b with hab | hab
    · rw [abs_of_nonneg (sub_nonneg.2 hab)]; exact key ha hb hab
    · rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.2 hab), neg_sub]; exact key hb ha hab

variable {n : ℕ}

/-- `N` times a measure-`v`-representable one-particle density. -/
def MeasDensN (x : SN n) : Prop :=
  ∃ ρ1 : C01, VRepMeas ρ1 ∧ ∀ t : Icc (0 : ℝ) 1, prim (x : L2I) t ^ 2 = (n + 1) * ρ1 t

lemma mem_BsetL_of_MeasDensN {x : SN n} (h : MeasDensN x) :
    ∃ L : ℕ, (x : L2I) ∈ BsetL L 0 := by
  obtain ⟨ρ1, hρ1, hx⟩ := h
  obtain ⟨g, G, B, hG0, hB0, hρ, hGb, hLip⟩ := lipschitz_of_vrepMeas hρ1
  obtain ⟨L, hL⟩ := exists_nat_ge (4 * (n + 1) * G * B)
  refine ⟨L, fun t h h0 _ h1 h2 => ?_⟩
  have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
  have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
  have hK : ∀ s ∈ Icc (0 : ℝ) 1, prim (x : L2I) s ^ 2 = (n + 1) * g s ^ 2 := fun s hs => by
    rw [hx ⟨s, hs⟩, hρ ⟨s, hs⟩]
  have hN : (0 : ℝ) ≤ n + 1 := by positivity
  -- `|K(s) - K(s')| ≤ 2 N G B |s - s'|`
  have hdiff : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      |(n + 1) * g s ^ 2 - (n + 1) * g s' ^ 2| ≤ 2 * (n + 1) * G * B * |s - s'| :=
    fun s hs s' hs' => by
      rw [← mul_sub, abs_mul, abs_of_nonneg hN, show g s ^ 2 - g s' ^ 2 =
        (g s + g s') * (g s - g s') by ring, abs_mul]
      have h1 : |g s + g s'| ≤ 2 * G := (abs_add_le _ _).trans (by linarith [hGb s hs, hGb s' hs'])
      have h2 := hLip s' hs' s hs
      calc (n + 1) * (|g s + g s'| * |g s - g s'|) ≤ (n + 1) * (2 * G * (B * |s - s'|)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) hN
        _ = 2 * (n + 1) * G * B * |s - s'| := by ring
  simp only [D2]
  rw [hK _ m1, hK _ m2, hK _ m3]
  have a1 := hdiff _ m1 _ m2
  have a2 := hdiff _ m2 _ m3
  rw [show t + h - t = h by ring, abs_of_nonneg h0] at a1
  rw [show t - (t - h) = h by ring, abs_of_nonneg h0] at a2
  calc |(n + 1) * g (t + h) ^ 2 - 2 * ((n + 1) * g t ^ 2) + (n + 1) * g (t - h) ^ 2|
      ≤ |(n + 1) * g (t + h) ^ 2 - (n + 1) * g t ^ 2| +
          |(n + 1) * g t ^ 2 - (n + 1) * g (t - h) ^ 2| := by
        rw [show (n + 1) * g (t + h) ^ 2 - 2 * ((n + 1) * g t ^ 2) + (n + 1) * g (t - h) ^ 2 =
          ((n + 1) * g (t + h) ^ 2 - (n + 1) * g t ^ 2) -
            ((n + 1) * g t ^ 2 - (n + 1) * g (t - h) ^ 2) by ring]
        exact abs_sub _ _
    _ ≤ 4 * (n + 1) * G * B * h := by linarith
    _ ≤ L * h := mul_le_mul_of_nonneg_right hL h0

/-- `BsetL L 0` in `SN n`. -/
def BsetLS (n : ℕ) (L : ℝ) : Set (SN n) := Subtype.val ⁻¹' BsetL L 0

lemma isNowhereDense_BsetLS {L : ℝ} (hL : 0 ≤ L) : IsNowhereDense (BsetLS n L) := by
  have hcl : IsClosed (BsetLS n L) := (isClosed_BsetL L 0).preimage continuous_subtype_val
  rw [IsNowhereDense, hcl.closure_eq]
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨y, hy, hyx, hyB⟩ := exists_not_BsetL hL 0 x.2 (interior_subset hx : x ∈ BsetLS n L) hε
  have hyb : (⟨y, hy⟩ : SN n) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]; exact hyx
  exact hyB (show (⟨y, hy⟩ : SN n) ∈ BsetLS n L from interior_subset (hball hyb))

/-- **Measure-`v`-representable densities are meagre**: in the space of `N`-representable
densities, `N` times the ground-state densities of one particle in measure potentials (one
particle, or `N` non-interacting bosons) form a set of first category. -/
theorem vrepMeas_meagre : IsMeagre {x : SN n | MeasDensN x} :=
  (isMeagre_iUnion fun L : ℕ =>
    (isNowhereDense_BsetLS (n := n) (Nat.cast_nonneg L)).isMeagre).mono
      fun _ hx => mem_iUnion.2 (mem_BsetL_of_MeasDensN hx)

/-- **Most densities are not measure-`v`-representable**: the complement is dense. -/
theorem vrepMeas_nonrep_dense : Dense {x : SN n | ¬ MeasDensN x} := by
  have : CompleteSpace (SN n) := (isClosed_SN n).completeSpace_coe
  exact dense_of_mem_residual (vrepMeas_meagre (n := n))

/-- **Non-interacting bosons**: the `N`-representable densities that are ground-state densities
of `N` non-interacting bosons in some measure potential form a meagre set. -/
theorem vrepMeasN_bos_meagre :
    IsMeagre {x : SN n | ∃ ρ : C01, VRepMeasN .bos n 0 ρ ∧
      ∀ t : Icc (0 : ℝ) 1, prim (x : L2I) t ^ 2 = ρ t} :=
  (vrepMeas_meagre (n := n)).mono fun _ ⟨ρ, hρ, hx⟩ => by
    obtain ⟨ρ1, h1, rfl⟩ := (vrepMeasN_bos_iff ρ).1 hρ
    exact ⟨ρ1, h1, fun t => by rw [hx t]; rfl⟩

end DFT.Continuum.Line
