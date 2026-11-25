/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasureHolder
import DFT.Continuum.Line.MeasureMeagre

/-!
# Interacting `v`-representable densities in measure potentials are meagre

For `N` interacting bosons or fermions (continuous `w`) in measure potentials, the ground-state
densities form a meagre subset of the `N`-representable densities (**`vrepMeasN_meagre`**); the
complement is residual, hence dense (**`vrepMeasN_nonrep_dense`**).

The densities are `5/8`-Hölder (`rhoHat_holder`), so their second differences are at most
`L h^{5/8}`. The sets `BsetH L` of such densities are closed with empty interior in `SN n`
(**`exists_not_BsetH`**): a tent of width `w = r¹⁶` and height `r⁹` costs `O(r)` in `L²` and adds
`≈ 4|g(t₀)| r⁹ ≫ L w^{5/8} = L r¹⁰` to the second difference at its apex. (General `H¹`
densities are only `1/2`-Hölder.)
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

/-- Second differences of `ρ_f` at most `L h^{5/8}` for `h ≤ 1`. -/
def BsetH (L : ℝ) : Set L2I :=
  {f | ∀ t h : ℝ, 0 ≤ h → h ≤ 1 → 0 ≤ t - h → t + h ≤ 1 →
    |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ (5 / 8 : ℝ)}

lemma isClosed_BsetH (L : ℝ) : IsClosed (BsetH L) := by
  have e : BsetH L = ⋂ t : ℝ, ⋂ h : ℝ, {f : L2I | 0 ≤ h → h ≤ 1 → 0 ≤ t - h →
      t + h ≤ 1 → |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ (5 / 8 : ℝ)} := by
    ext f; simp [BsetH]
  rw [e]
  refine isClosed_iInter fun t => isClosed_iInter fun h => ?_
  by_cases hc : 0 ≤ h ∧ h ≤ 1 ∧ 0 ≤ t - h ∧ t + h ≤ 1
  · obtain ⟨h0, hk, h1, h2⟩ := hc
    have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
    have e2 : {f : L2I | 0 ≤ h → h ≤ 1 → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ (5 / 8 : ℝ)} =
        {f : L2I | |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ (5 / 8 : ℝ)} := by
      ext f; exact ⟨fun H => H h0 hk h1 h2, fun H _ _ _ _ => H⟩
    rw [e2]
    refine isClosed_le ?_ continuous_const
    simp only [D2]
    exact continuous_abs.comp ((((continuous_prim_at m1).pow 2).sub
      (((continuous_prim_at m2).pow 2).const_mul 2)).add ((continuous_prim_at m3).pow 2))
  · have e2 : {f : L2I | 0 ≤ h → h ≤ 1 → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ (5 / 8 : ℝ)} = univ := by
      ext f
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h0 hk h1 h2
      exact absurd ⟨h0, hk, h1, h2⟩ hc
    rw [e2]; exact isClosed_univ

variable {n : ℕ}

set_option maxHeartbeats 1000000 in -- many local definitions; the final term is slow to check
/-- **`BsetH L` has empty interior in `SN n`**: a tent of width `r¹⁶` and height `r⁹`. -/
theorem exists_not_BsetH {L : ℝ} (hL : 0 ≤ L) {x : L2I} (hx : x ∈ SN n)
    (hxB : x ∈ BsetH L) {ε : ℝ} (hε : 0 < ε) : ∃ y ∈ SN n, ‖y - x‖ < ε ∧ y ∉ BsetH L := by
  set g := prim x
  have hN : ∫ t, g t ^ 2 ∂μ1 = n + 1 := hx.2
  set N : ℝ := n + 1
  have hNp : 0 < N := by positivity
  obtain ⟨t0, ht0, hg0⟩ : ∃ t0 ∈ Ioo (0 : ℝ) 1, g t0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∫ t, g t ^ 2 ∂μ1 = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => by simp [hcon t ht]
    linarith
  set γ := g t0
  have hγ : 0 < |γ| := abs_pos.2 hg0
  set M := ‖x‖
  have hM : 0 ≤ M := norm_nonneg _
  have hgM : ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ M := fun t ht => abs_prim_le x ht
  -- the parameter `r`
  set c2 := min t0 (1 - t0) / 2
  have hmin : 0 < min t0 (1 - t0) := lt_min ht0.1 (by linarith [ht0.2])
  have hc2 : 0 < c2 := by simp only [c2]; positivity
  have hc2t : c2 ≤ t0 := by simp only [c2]; linarith [min_le_left t0 (1 - t0)]
  have hc2s : c2 ≤ 1 - t0 := by simp only [c2]; linarith [min_le_right t0 (1 - t0)]
  set c3 := 4 * |γ| / (3 * L + (L + 2 * M ^ 2) / |γ| + 1)
  have hc3 : 0 < c3 := by positivity
  set c4 := N / (4 * (2 * M + 1))
  have hc4 : 0 < c4 := by positivity
  set c5 := ε / (4 * (2 * M + 1) * (M + 2) / N + 2)
  have hc5 : 0 < c5 := by positivity
  set r := min (min 1 c2) (min c3 (min c4 c5)) / 2
  have hr0 : 0 < r := by positivity
  have hm0 : 0 < min (min 1 c2) (min c3 (min c4 c5)) := by positivity
  have hrm : r < min (min 1 c2) (min c3 (min c4 c5)) := by simp only [r]; linarith
  have hr1 : r < 1 := lt_of_lt_of_le hrm ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : r < c2 := lt_of_lt_of_le hrm ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : r < c3 := lt_of_lt_of_le hrm ((min_le_right _ _).trans (min_le_left _ _))
  have hr4 : r < c4 :=
    lt_of_lt_of_le hrm ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr5 : r < c5 :=
    lt_of_lt_of_le hrm ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- width and height
  set w := r ^ 16
  have hw : 0 < w := by positivity
  have hwr : w ≤ r := by
    simp only [w]
    calc r ^ 16 ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (by norm_num)
      _ = r := pow_one r
  have hw0 : w ≤ t0 := by linarith
  have hw1 : w ≤ 1 - t0 := by linarith
  obtain ⟨q, hq1, hqp, hqn⟩ := exists_tent_L2' hw hw0 hw1
  set sg : ℝ := if 0 < γ then 1 else -1
  have hsg : |sg| = 1 := by simp only [sg]; split_ifs <;> simp
  have hsgγ : sg * γ = |γ| := by
    simp only [sg]; split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · have : γ < 0 := lt_of_le_of_ne (not_lt.1 h) hg0
      rw [abs_of_neg this]; ring
  set δ := sg * r ^ 9
  have hδabs : |δ| = r ^ 9 := by
    simp only [δ]; rw [abs_mul, hsg, one_mul, abs_of_pos (by positivity)]
  have hδγ : δ * γ = r ^ 9 * |γ| := by simp only [δ]; rw [← hsgγ]; ring
  have hδ1 : |δ| ≤ 1 := by
    rw [hδabs]; exact pow_le_one₀ hr0.le hr1.le
  -- `‖δ q‖ ≤ 2r`
  have hδq : |δ| * ‖q‖ ≤ 2 * r := by
    have hsq : (|δ| * ‖q‖) ^ 2 ≤ (2 * r) ^ 2 := by
      rw [mul_pow, hδabs]
      calc (r ^ 9) ^ 2 * ‖q‖ ^ 2 ≤ (r ^ 9) ^ 2 * (2 / w) :=
            mul_le_mul_of_nonneg_left hqn (by positivity)
        _ = 2 * r ^ 2 := by simp only [w]; field_simp
        _ ≤ (2 * r) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  -- the perturbed state and its norm
  set F : L2I := x + δ • q
  have hFp : ∀ t ∈ Icc (0 : ℝ) 1, prim F t = g t + δ * tentF t0 w t := fun t ht => by
    simp only [F]; rw [prim_add _ _ ht, prim_smul _ _ ht, hqp t ht]
  set J := ∫ t, prim F t ^ 2 ∂μ1
  have hp_c : Continuous (tentF t0 w) := (lipschitz_tent (t0 := t0) hw).continuous
  have hJN : |J - N| ≤ (2 * M + 1) * (2 * r) := by
    have hint1 : Integrable (fun t => prim F t ^ 2 - g t ^ 2) μ1 :=
      (integrable_prim_sq F).sub (integrable_prim_sq x)
    have hint2 : Integrable (fun t => (2 * |δ| * M + δ ^ 2) * tentF t0 w t) μ1 :=
      (hp_c.continuousOn.integrableOn_compact (K := Icc (0 : ℝ) 1) isCompact_Icc
        |>.mono_set Ioo_subset_Icc_self).const_mul _
    have e : J - N = ∫ t, (prim F t ^ 2 - g t ^ 2) ∂μ1 := by
      rw [integral_sub (integrable_prim_sq F) (integrable_prim_sq x), hN]
    rw [e, ← Real.norm_eq_abs]
    calc ‖∫ t, (prim F t ^ 2 - g t ^ 2) ∂μ1‖
        ≤ ∫ t, (2 * |δ| * M + δ ^ 2) * tentF t0 w t ∂μ1 := by
          refine norm_integral_le_of_norm_le hint2 ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          have hti := Ioo_subset_Icc_self ht
          rw [hFp t hti, Real.norm_eq_abs]
          have p0 := tentF_nonneg t0 w t
          have p1 := tentF_le_one (t0 := t0) (t := t) hw
          have hg := hgM t hti
          have e2 : (g t + δ * tentF t0 w t) ^ 2 - g t ^ 2 =
              tentF t0 w t * (2 * δ * g t + δ ^ 2 * tentF t0 w t) := by ring
          rw [e2, abs_mul, abs_of_nonneg p0, mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ p0
          have a1 : |2 * δ * g t| ≤ 2 * |δ| * M := by
            rw [abs_mul, abs_mul, abs_two]; gcongr
          have a2 : |δ ^ 2 * tentF t0 w t| ≤ δ ^ 2 := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg δ), abs_of_nonneg p0]
            exact mul_le_of_le_one_right (sq_nonneg δ) p1
          exact (abs_add_le _ _).trans (by linarith)
      _ = (2 * |δ| * M + δ ^ 2) * ∫ t, tentF t0 w t ∂μ1 := integral_const_mul _ _
      _ ≤ (2 * |δ| * M + δ ^ 2) * (2 * w) :=
          mul_le_mul_of_nonneg_left (integral_tent_le hw) (by positivity)
      _ ≤ (2 * M + 1) * (2 * r) := by
          have hd2 : δ ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hδ1
          have : 2 * |δ| * M + δ ^ 2 ≤ 2 * M + 1 := by nlinarith
          exact mul_le_mul this (by linarith) (by positivity) (by positivity)
  have hJl : N / 2 ≤ J := by
    have : (2 * M + 1) * (2 * r) ≤ N / 2 := by
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (2 * M + 1))).1 hr4
      nlinarith
    linarith [neg_abs_le (J - N)]
  have hJu : J ≤ 2 * N := by
    have : (2 * M + 1) * (2 * r) ≤ N / 2 := by
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (2 * M + 1))).1 hr4
      nlinarith
    linarith [le_abs_self (J - N)]
  have hJpos : 0 < J := by linarith
  set lam := √(N / J)
  have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
  have hlam2 : lam ^ 2 = N / J := Real.sq_sqrt (by positivity)
  have hlam2' : 1 / 2 ≤ lam ^ 2 := by rw [hlam2, le_div_iff₀ hJpos]; linarith
  have hlam1 : |lam - 1| ≤ (2 * M + 1) * (2 * r) / (N / 2) := by
    have h1 : |lam - 1| ≤ |lam ^ 2 - 1| := by
      rw [show lam ^ 2 - 1 = (lam - 1) * (lam + 1) by ring, abs_mul]
      have : 1 ≤ |lam + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
      exact le_mul_of_one_le_right (abs_nonneg _) this
    have h2 : |lam ^ 2 - 1| = |J - N| / J := by
      rw [hlam2, show N / J - 1 = -(J - N) / J by field_simp; ring, abs_div, abs_neg,
        abs_of_pos hJpos]
    rw [h2] at h1
    refine h1.trans ?_
    calc |J - N| / J ≤ (2 * M + 1) * (2 * r) / J := div_le_div_of_nonneg_right hJN hJpos.le
      _ ≤ (2 * M + 1) * (2 * r) / (N / 2) := div_le_div_of_nonneg_left (by positivity)
          (by positivity) hJl
  set y : L2I := lam • F
  have hyp : ∀ t ∈ Icc (0 : ℝ) 1, prim y t = lam * prim F t := fun t ht => prim_smul _ _ ht
  have hySN : y ∈ SN n := by
    refine ⟨?_, ?_⟩
    · have hx1 : g 1 = 0 := hx.1
      rw [hyp 1 ⟨zero_le_one, le_rfl⟩, hFp 1 ⟨zero_le_one, le_rfl⟩, hx1,
        tent_far hw (by rw [abs_of_pos (by linarith [ht0.2])]; exact hw1)]
      ring
    · have : ∫ t, prim y t ^ 2 ∂μ1 = lam ^ 2 * J := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        rw [hyp t (Ioo_subset_Icc_self ht)]; ring
      rw [this, hlam2, div_mul_cancel₀ _ hJpos.ne']
  -- closeness
  have hclose : ‖y - x‖ < ε := by
    have e : y - x = (lam - 1) • F + δ • q := by
      simp only [y, F]; rw [sub_smul, one_smul, smul_add]; abel
    have hF : ‖F‖ ≤ M + 2 * r := by
      simp only [F]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]; linarith
    rw [e]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h5 := (lt_div_iff₀ (by positivity :
      (0 : ℝ) < 4 * (2 * M + 1) * (M + 2) / N + 2)).1 hr5
    have hF' : ‖F‖ ≤ M + 2 := by linarith
    calc |lam - 1| * ‖F‖ + |δ| * ‖q‖
        ≤ (2 * M + 1) * (2 * r) / (N / 2) * (M + 2) + 2 * r :=
          add_le_add (mul_le_mul hlam1 hF' (norm_nonneg _) (by positivity)) hδq
      _ = r * (4 * (2 * M + 1) * (M + 2) / N + 2) := by field_simp; ring
      _ < ε := by linarith
  -- the violation, at `h = w`
  set h := w with hh
  have hh0 : 0 < h := hw
  have hhw : h ≤ w := le_rfl
  have hh1 : h ≤ 1 := by linarith
  have ht1 : 0 ≤ t0 - h := by linarith
  have ht2 : t0 + h ≤ 1 := by linarith
  have hhp : h ^ (5 / 8 : ℝ) = r ^ 10 := by
    rw [hh]
    change (r ^ 16) ^ (5 / 8 : ℝ) = r ^ 10
    rw [← Real.rpow_natCast r 16, ← Real.rpow_mul hr0.le, ← Real.rpow_natCast r 10]
    norm_num
  have hD := hxB t0 h hh0.le hh1 ht1 ht2
  rw [hhp] at hD
  have key := D2_perturb (lam := lam) (δ := δ) hw hh0 hhw ht1 ht2 hqp hg0 hlam2' hD
  refine ⟨y, hySN, hclose, fun hyB => ?_⟩
  have hyD := hyB t0 h hh0.le hh1 ht1 ht2
  rw [hhp] at hyD
  change |D2 (fun s => prim (lam • (x + δ • q)) s ^ 2) t0 h| ≤ L * r ^ 10 at hyD
  set S := ∫ s in (t0 - h)..(t0 + h), (x : ℝ → ℝ) s ^ 2
  have hS : S ≤ M ^ 2 := integral_sq_le_mu1 x ht1 (by linarith) ht2
  have hS0 : 0 ≤ S := intervalIntegral.integral_nonneg (by linarith) fun s _ => sq_nonneg _
  have hA : 4 * (δ * prim x t0) / w * h = 4 * |γ| * r ^ 9 := by
    change 4 * (δ * γ) / w * w = _
    rw [hδγ, div_mul_cancel₀ _ hw.ne']; ring
  rw [hA] at key
  have hbig : 3 * L + (L + 2 * M ^ 2) / |γ| < 4 * |γ| / r := by
    have := hr3
    simp only [c3] at this
    rw [lt_div_iff₀ (by positivity)] at this
    rw [lt_div_iff₀ hr0]
    have : 0 ≤ (L + 2 * M ^ 2) / |γ| := by positivity
    nlinarith
  have p10 : r ^ 10 ≤ r := by
    calc r ^ 10 ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (by norm_num)
      _ = r := pow_one r
  have herr : |δ| * (L * r ^ 10 + 2 * (h * S)) / |prim x t0| ≤
      r ^ 9 * (r * ((L + 2 * M ^ 2) / |γ|)) := by
    change |δ| * (L * r ^ 10 + 2 * (h * S)) / |γ| ≤ _
    rw [div_le_iff₀ hγ, hδabs]
    have h1 : L * r ^ 10 ≤ L * r := mul_le_mul_of_nonneg_left p10 hL
    have h2 : h * S ≤ r * M ^ 2 := mul_le_mul hwr hS hS0 hr0.le
    calc r ^ 9 * (L * r ^ 10 + 2 * (h * S)) ≤ r ^ 9 * (r * (L + 2 * M ^ 2)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = r ^ 9 * (r * ((L + 2 * M ^ 2) / |γ|)) * |γ| := by field_simp
  have : L * r ^ 10 <
      (4 * |γ| * r ^ 9 - L * r ^ 10 - |δ| * (L * r ^ 10 + 2 * (h * S)) / |prim x t0|) / 2 := by
    have hr9 : 0 < r ^ 9 := by positivity
    have h3 : r * (3 * L + (L + 2 * M ^ 2) / |γ|) < 4 * |γ| := by
      have := mul_lt_mul_of_pos_left hbig hr0
      rwa [mul_div_cancel₀ _ hr0.ne'] at this
    have h4 := mul_lt_mul_of_pos_left h3 hr9
    have e10 : r ^ 10 = r ^ 9 * r := by ring
    rw [e10] at herr ⊢
    nlinarith
  linarith only [this, key, hyD]

/-! ### Meagreness -/

/-- `BsetH L` in `SN n`. -/
def BsetHS (n : ℕ) (L : ℝ) : Set (SN n) := Subtype.val ⁻¹' BsetH L

lemma isNowhereDense_BsetHS {L : ℝ} (hL : 0 ≤ L) : IsNowhereDense (BsetHS n L) := by
  have hcl : IsClosed (BsetHS n L) := (isClosed_BsetH L).preimage continuous_subtype_val
  rw [IsNowhereDense, hcl.closure_eq]
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨y, hy, hyx, hyB⟩ := exists_not_BsetH hL x.2 (interior_subset hx : x ∈ BsetHS n L) hε
  have hyb : (⟨y, hy⟩ : SN n) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]; exact hyx
  exact hyB (show (⟨y, hy⟩ : SN n) ∈ BsetHS n L from interior_subset (hball hyb))

/-- A `5/8`-Hölder density has second differences `O(h^{5/8})`. -/
lemma mem_BsetH_of_holder {x : L2I} {ρ : Pot} (hx : ∀ t : Icc (0 : ℝ) 1, prim x t ^ 2 = ρ t)
    {C : ℝ} (hC : ∀ t t' : Icc (0 : ℝ) 1, |ρ t' - ρ t| ≤ C * |(t' : ℝ) - t| ^ (5 / 8 : ℝ)) :
    x ∈ BsetH (2 * C) := by
  intro t h h0 _ h1 h2
  have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
  have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
  have a1 := hC ⟨t, m2⟩ ⟨t + h, m1⟩
  have a2 := hC ⟨t - h, m3⟩ ⟨t, m2⟩
  simp only [show t + h - t = h by ring, show t - (t - h) = h by ring, abs_of_nonneg h0] at a1 a2
  simp only [D2]
  rw [hx ⟨t + h, m1⟩, hx ⟨t, m2⟩, hx ⟨t - h, m3⟩]
  calc |ρ ⟨t + h, m1⟩ - 2 * ρ ⟨t, m2⟩ + ρ ⟨t - h, m3⟩|
      = |(ρ ⟨t + h, m1⟩ - ρ ⟨t, m2⟩) - (ρ ⟨t, m2⟩ - ρ ⟨t - h, m3⟩)| := by ring_nf
    _ ≤ |ρ ⟨t + h, m1⟩ - ρ ⟨t, m2⟩| + |ρ ⟨t, m2⟩ - ρ ⟨t - h, m3⟩| := abs_sub _ _
    _ ≤ 2 * C * h ^ (5 / 8 : ℝ) := by linarith

variable {τ : Stat} {w : Cfg n → ℝ}

/-- **Interacting measure-`v`-representable densities are meagre**: for `N` interacting bosons or
fermions (continuous `w`), the ground-state densities of measure potentials form a meagre subset of
the `N`-representable densities. -/
theorem vrepMeasN_meagre (hw : Continuous w) :
    IsMeagre {x : SN n | ∃ ρ : Pot, VRepMeasN τ n w ρ ∧
      ∀ t : Icc (0 : ℝ) 1, prim (x : L2I) t ^ 2 = ρ t} :=
  (isMeagre_iUnion fun L : ℕ =>
    (isNowhereDense_BsetHS (n := n) (Nat.cast_nonneg L)).isMeagre).mono fun x hx => by
    obtain ⟨ρ, ⟨μp, μm, _, _, Φ, hΦ, rfl⟩, hx⟩ := hx
    obtain ⟨C, -, hC⟩ := rhoHat_holder hw hΦ
    obtain ⟨L, hL⟩ := exists_nat_ge (2 * C)
    refine mem_iUnion.2 ⟨L, fun t h h0 h1 h2 h3 => ?_⟩
    refine (mem_BsetH_of_holder hx hC t h h0 h1 h2 h3).trans ?_
    exact mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg h0 _)

/-- **Most densities are not ground-state densities of any measure potential**, for interacting
bosons or fermions: the complement is residual, hence dense. -/
theorem vrepMeasN_nonrep_dense (hw : Continuous w) :
    Dense {x : SN n | ¬ ∃ ρ : Pot, VRepMeasN τ n w ρ ∧
      ∀ t : Icc (0 : ℝ) 1, prim (x : L2I) t ^ 2 = ρ t} := by
  have : CompleteSpace (SN n) := (isClosed_SN n).completeSpace_coe
  exact dense_of_mem_residual (vrepMeasN_meagre (τ := τ) hw)

end DFT.Continuum.Line
