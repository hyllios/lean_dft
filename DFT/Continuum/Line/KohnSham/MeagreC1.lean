/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.KohnSham.Meagre

/-!
# Densities with a `C¹` profile are meagre

A sharpening of `Line/Meagre`: in the space `SN n` of `N`-representable densities, the densities
whose profile is `C¹` on `[0, 1]` (vanishing at the walls) already form a meagre set. A `C¹` profile
has `|K(t + h) - 2K(t) + K(t - h)| ≤ h` for all small `h` (uniform continuity of `K'`), a closed
condition `Bset k` for `h ≤ 1/(k+1)`. Its interior is empty: a tent of width `w = r⁴` and height
`δ = r³` costs `O(r)` in `L²` but adds `≈ -4δγh/w = -4γh/r` to the second difference at its apex.

* `D2_perturb`: the second difference of the perturbed, rescaled density, bounded below.
* `exists_tent_L2'`: the tent with `‖q‖² ≤ 2/w`; `integral_tent_le`: `∫ tent ≤ 2w`.
* `Bset`, `isClosed_Bset`, `exists_not_Bset`, `isNowhereDense_BsetS`.
* `C1Dens`; **`meagre_C1Dens`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

/-! ### The perturbation estimate -/

/-- **The second difference at the apex of a tent.** For `y = λ (x + δ q)`, `q` the derivative of a
tent of width `w` at `t₀`, `λ² ≥ 1/2`, and `|Δ²_h ρ_x(t₀)| ≤ E₀`:
`|Δ²_h ρ_y(t₀)| ≥ (4δ g(t₀) h / w - E₀ - |δ| (E₀ + 2h ∫_{t₀-h}^{t₀+h} g'²) / |g(t₀)|) / 2`. -/
theorem D2_perturb {x q : L2I} {t0 w δ lam h E0 : ℝ} (hw : 0 < w) (hh0 : 0 < h) (hhw : h ≤ w)
    (ht1 : 0 ≤ t0 - h) (ht2 : t0 + h ≤ 1)
    (hqp : ∀ t ∈ Icc (0 : ℝ) 1, prim q t = tentF t0 w t) (hg0 : prim x t0 ≠ 0)
    (hlam : 1 / 2 ≤ lam ^ 2)
    (hD : |D2 (fun s => prim x s ^ 2) t0 h| ≤ E0) :
    (4 * (δ * prim x t0) / w * h - E0 -
        |δ| * (E0 + 2 * (h * ∫ s in (t0 - h)..(t0 + h), (x : ℝ → ℝ) s ^ 2)) / |prim x t0|) / 2
      ≤ |D2 (fun s => prim (lam • (x + δ • q)) s ^ 2) t0 h| := by
  set g := prim x
  set γ := g t0
  have hγabs : 0 < |γ| := abs_pos.2 hg0
  have m1 : t0 + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht2⟩
  have m2 : t0 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have m3 : t0 - h ∈ Icc (0 : ℝ) 1 := ⟨ht1, by linarith⟩
  have hyp : ∀ t ∈ Icc (0 : ℝ) 1, prim (lam • (x + δ • q)) t = lam * (g t + δ * tentF t0 w t) :=
    fun t ht => by rw [prim_smul _ _ ht, prim_add _ _ ht, prim_smul _ _ ht, hqp t ht]
  obtain ⟨tp, tm⟩ := tent_side (t0 := t0) hw hh0.le hhw
  simp only [D2]
  rw [hyp _ m1, hyp _ m2, hyp _ m3, tp, tm, tent_center t0 w]
  simp only [D2] at hD
  set P := g (t0 + h)
  set R := g (t0 - h)
  set a := 1 - h / w
  have ha0 : 0 ≤ a := by simp only [a]; rw [sub_nonneg, div_le_one hw]; exact hhw
  have ha1 : a ≤ 1 := by
    simp only [a]; have : 0 ≤ h / w := by positivity
    linarith
  have h1a : 1 - a = h / w := by simp only [a]; ring
  set S := ∫ s in (t0 - h)..(t0 + h), (x : ℝ → ℝ) s ^ 2
  have hii : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 →
      IntervalIntegrable (fun s => (x : ℝ → ℝ) s ^ 2) volume u v := fun hu huv hv =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le huv).2
      ((show IntegrableOn _ (Ioo (0 : ℝ) 1) volume from integrable_sq_L2I x).mono_set
        (Ioo_subset_Ioo hu hv))
  have hsplit : S = (∫ s in (t0 - h)..t0, (x : ℝ → ℝ) s ^ 2) +
      ∫ s in t0..(t0 + h), (x : ℝ → ℝ) s ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hii ht1 (by linarith) m2.2)
      (hii m2.1 (by linarith) ht2)).symm
  have hnn1 : 0 ≤ ∫ s in (t0 - h)..t0, (x : ℝ → ℝ) s ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ => sq_nonneg _
  have hnn2 : 0 ≤ ∫ s in t0..(t0 + h), (x : ℝ → ℝ) s ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ => sq_nonneg _
  have hdP : (P - γ) ^ 2 ≤ h * S := by
    have := sq_prim_sub_le x m2.1 (by linarith : t0 ≤ t0 + h) ht2
    rw [show t0 + h - t0 = h by ring] at this
    exact this.trans (by gcongr; linarith)
  have hdR : (R - γ) ^ 2 ≤ h * S := by
    have := sq_prim_sub_le x ht1 (by linarith : t0 - h ≤ t0) m2.2
    rw [show t0 - (t0 - h) = h by ring] at this
    calc (R - γ) ^ 2 = (γ - R) ^ 2 := by ring
      _ ≤ _ := this
      _ ≤ h * S := by gcongr; linarith
  set T := (P + δ * a) ^ 2 - 2 * (γ + δ * 1) ^ 2 + (R + δ * a) ^ 2
  have hid : 2 * γ * ((P - γ) + (R - γ)) =
      (P ^ 2 - 2 * γ ^ 2 + R ^ 2) - (P - γ) ^ 2 - (R - γ) ^ 2 := by ring
  have hcross : |2 * δ * a * ((P - γ) + (R - γ))| ≤ |δ| * (E0 + 2 * (h * S)) / |γ| := by
    rw [le_div_iff₀ hγabs]
    have e3 : |2 * δ * a * ((P - γ) + (R - γ))| * |γ| =
        |δ| * a * |2 * γ * ((P - γ) + (R - γ))| := by
      simp only [abs_mul, abs_of_nonneg ha0]; ring
    rw [e3, hid]
    have hb : |(P ^ 2 - 2 * γ ^ 2 + R ^ 2) - (P - γ) ^ 2 - (R - γ) ^ 2| ≤ E0 + 2 * (h * S) := by
      have := abs_sub (P ^ 2 - 2 * γ ^ 2 + R ^ 2 - (P - γ) ^ 2) ((R - γ) ^ 2)
      have := abs_sub (P ^ 2 - 2 * γ ^ 2 + R ^ 2) ((P - γ) ^ 2)
      rw [abs_of_nonneg (sq_nonneg (P - γ))] at this
      have := abs_of_nonneg (sq_nonneg (R - γ))
      linarith
    calc |δ| * a * |P ^ 2 - 2 * γ ^ 2 + R ^ 2 - (P - γ) ^ 2 - (R - γ) ^ 2|
        ≤ |δ| * 1 * (E0 + 2 * (h * S)) := by gcongr
      _ = _ := by ring
  have hT : -T ≥ 4 * (δ * γ) / w * h - E0 - |δ| * (E0 + 2 * (h * S)) / |γ| := by
    have e4 : -T = -(P ^ 2 - 2 * γ ^ 2 + R ^ 2) + 4 * (δ * γ) * (1 - a)
        - 2 * δ * a * ((P - γ) + (R - γ)) + 2 * δ ^ 2 * (1 - a ^ 2) := by
      simp only [T]; ring
    have hA' : 4 * (δ * γ) * (1 - a) = 4 * (δ * γ) / w * h := by
      rw [h1a]; field_simp
    have h5 : 0 ≤ 2 * δ ^ 2 * (1 - a ^ 2) := by
      have : 0 ≤ 1 - a ^ 2 := by
        rw [show 1 - a ^ 2 = (1 - a) * (1 + a) by ring]
        exact mul_nonneg (sub_nonneg.2 ha1) (by linarith)
      positivity
    have h6 := le_abs_self (2 * δ * a * ((P - γ) + (R - γ)))
    have h7 := le_abs_self (P ^ 2 - 2 * γ ^ 2 + R ^ 2)
    rw [e4, hA']
    linarith only [h5, h6, h7, hD, hcross]
  have hkey : (lam * (P + δ * a)) ^ 2 - 2 * (lam * (γ + δ * 1)) ^ 2 +
      (lam * (R + δ * a)) ^ 2 = lam ^ 2 * T := by simp only [T]; ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg lam)]
  rcases le_or_gt 0 (-T) with hT0 | hT0
  · have h9 : 1 / 2 * -T ≤ lam ^ 2 * -T := mul_le_mul_of_nonneg_right hlam hT0
    have : -T ≤ |T| := neg_le_abs T
    have : lam ^ 2 * -T ≤ lam ^ 2 * |T| := mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  · have : 0 ≤ lam ^ 2 * |T| := by positivity
    linarith

/-! ### Quantitative facts about the tent -/

lemma tentF_nonneg (t0 w t : ℝ) : 0 ≤ tentF t0 w t := le_max_left _ _

lemma tentF_le_one {t0 w t : ℝ} (hw : 0 < w) : tentF t0 w t ≤ 1 :=
  max_le zero_le_one (by have : 0 ≤ |t - t0| / w := by positivity
                         linarith)

lemma tent_le_indicator {t0 w : ℝ} (hw : 0 < w) (t : ℝ) :
    tentF t0 w t ≤ (Icc (t0 - w) (t0 + w)).indicator 1 t := by
  by_cases ht : t ∈ Icc (t0 - w) (t0 + w)
  · rw [indicator_of_mem ht]; exact tentF_le_one hw
  · rw [indicator_of_notMem ht, tent_far hw]
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

lemma integral_indicator_Icc_le {a b : ℝ} (hab : a ≤ b) :
    ∫ t, (Icc a b).indicator (1 : ℝ → ℝ) t ∂μ1 ≤ b - a := by
  rw [integral_indicator_one measurableSet_Icc]
  have h1 : μ1 (Icc a b) ≤ volume (Icc a b) := Measure.restrict_le_self _
  rw [Real.volume_Icc] at h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rwa [ENNReal.toReal_ofReal (by linarith)] at this

lemma integral_tent_le {t0 w : ℝ} (hw : 0 < w) : ∫ t, tentF t0 w t ∂μ1 ≤ 2 * w := by
  have hc : Continuous (tentF t0 w) := (lipschitz_tent (t0 := t0) hw).continuous
  have hi : Integrable ((Icc (t0 - w) (t0 + w)).indicator (1 : ℝ → ℝ)) μ1 :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  calc ∫ t, tentF t0 w t ∂μ1 ≤ ∫ t, (Icc (t0 - w) (t0 + w)).indicator 1 t ∂μ1 :=
        integral_mono_of_nonneg (ae_of_all _ fun t => tentF_nonneg _ _ _) hi
          (ae_of_all _ fun t => tent_le_indicator hw t)
    _ ≤ t0 + w - (t0 - w) := integral_indicator_Icc_le (by linarith)
    _ = 2 * w := by ring

lemma deriv_tent_eq_zero {t0 w t : ℝ} (hw : 0 < w) (ht : w < |t - t0|) :
    deriv (tentF t0 w) t = 0 := by
  have hev : tentF t0 w =ᶠ[𝓝 t] fun _ => 0 := by
    have hU : IsOpen {s : ℝ | w < |s - t0|} :=
      isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
    filter_upwards [hU.mem_nhds ht] with s hs
    exact tent_far hw hs.le
  rw [hev.deriv_eq, deriv_const]

/-- The tent as the primitive of an `L²` function of norm `‖q‖² ≤ 2/w`. -/
lemma exists_tent_L2' {t0 w : ℝ} (hw : 0 < w) (hw0 : w ≤ t0) (hw1 : w ≤ 1 - t0) :
    ∃ q : L2I, prim q 1 = 0 ∧ (∀ t ∈ Icc (0 : ℝ) 1, prim q t = tentF t0 w t) ∧
      ‖q‖ ^ 2 ≤ 2 / w := by
  have hl := lipschitz_tent (t0 := t0) hw
  have hb : ∀ t, ‖deriv (tentF t0 w) t‖ ≤ 1 / w := fun t => norm_deriv_le_of_lipschitz hl
  have hm : MemLp (deriv (tentF t0 w)) 2 μ1 :=
    MemLp.of_bound (measurable_deriv _).aestronglyMeasurable (1 / w) (ae_of_all _ hb)
  set q : L2I := hm.toLp _
  have h0 : tentF t0 w 0 = 0 := by
    refine tent_far hw ?_
    rw [zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < t0)]
    exact hw0
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, prim q t = tentF t0 w t := fun t ht => by
    rw [prim, integral_congr_mu1 (MemLp.coeFn_toLp hm) ht,
      (hl.lipschitzOnWith (s := uIcc 0 t)).absolutelyContinuousOnInterval.integral_deriv_eq_sub,
      h0, sub_zero]
  refine ⟨q, ?_, hp, ?_⟩
  · rw [hp 1 ⟨zero_le_one, le_rfl⟩]
    exact tent_far hw (by rw [abs_of_pos (by linarith)]; exact hw1)
  · have hbd : ∀ t, deriv (tentF t0 w) t ^ 2 ≤
        (1 / w) ^ 2 * (Icc (t0 - w) (t0 + w)).indicator 1 t :=
      fun t => by
        by_cases ht : t ∈ Icc (t0 - w) (t0 + w)
        · rw [indicator_of_mem ht, Pi.one_apply, mul_one, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using hb t) 2
        · rw [indicator_of_notMem ht, mul_zero, deriv_tent_eq_zero hw]
          · simp
          · simp only [mem_Icc, not_and_or, not_le] at ht
            rcases ht with ht | ht
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
    have hi : Integrable ((Icc (t0 - w) (t0 + w)).indicator (1 : ℝ → ℝ)) μ1 :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Icc
    rw [norm_sq_L2I]
    calc ∫ t, (q : ℝ → ℝ) t ^ 2 ∂μ1 = ∫ t, deriv (tentF t0 w) t ^ 2 ∂μ1 :=
          integral_congr_ae (by filter_upwards [MemLp.coeFn_toLp hm] with t ht; rw [ht])
      _ ≤ ∫ t, (1 / w) ^ 2 * (Icc (t0 - w) (t0 + w)).indicator 1 t ∂μ1 :=
          integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) (hi.const_mul _)
            (ae_of_all _ hbd)
      _ ≤ (1 / w) ^ 2 * (t0 + w - (t0 - w)) := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_indicator_Icc_le (by linarith))
            (by positivity)
      _ = 2 / w := by field_simp; ring

lemma integral_sq_le_mu1 (x : L2I) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ s in a..b, (x : ℝ → ℝ) s ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_sq_L2I, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_set (show IntegrableOn _ (Ioo (0 : ℝ) 1) volume from integrable_sq_L2I x)
    (ae_of_all _ fun s => sq_nonneg _) (LE.le.eventuallySubset (Ioo_subset_Ioo ha hb))

/-! ### The closed sets `Bset k` -/

/-- Second differences of `ρ_f` at most `h` for `h ≤ 1/(k+1)`. -/
def Bset (k : ℕ) : Set L2I :=
  {f | ∀ t h : ℝ, 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h → t + h ≤ 1 →
    |D2 (fun s => prim f s ^ 2) t h| ≤ h}

lemma isClosed_Bset (k : ℕ) : IsClosed (Bset k) := by
  have e : Bset k = ⋂ t : ℝ, ⋂ h : ℝ, {f : L2I | 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h →
      t + h ≤ 1 → |D2 (fun s => prim f s ^ 2) t h| ≤ h} := by
    ext f; simp [Bset]
  rw [e]
  refine isClosed_iInter fun t => isClosed_iInter fun h => ?_
  by_cases hc : 0 ≤ h ∧ h ≤ 1 / ((k : ℝ) + 1) ∧ 0 ≤ t - h ∧ t + h ≤ 1
  · obtain ⟨h0, hk, h1, h2⟩ := hc
    have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
    have e2 : {f : L2I | 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ h} =
        {f : L2I | |D2 (fun s => prim f s ^ 2) t h| ≤ h} := by
      ext f; exact ⟨fun H => H h0 hk h1 h2, fun H _ _ _ _ => H⟩
    rw [e2]
    refine isClosed_le ?_ continuous_const
    simp only [D2]
    exact continuous_abs.comp ((((continuous_prim_at m1).pow 2).sub
      (((continuous_prim_at m2).pow 2).const_mul 2)).add ((continuous_prim_at m3).pow 2))
  · have e2 : {f : L2I | 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ h} = univ := by
      ext f
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h0 hk h1 h2
      exact absurd ⟨h0, hk, h1, h2⟩ hc
    rw [e2]; exact isClosed_univ

/-- Second differences of `ρ_f` at most `L h` for `h ≤ 1/(k+1)`. -/
def BsetL (L : ℝ) (k : ℕ) : Set L2I :=
  {f | ∀ t h : ℝ, 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h → t + h ≤ 1 →
    |D2 (fun s => prim f s ^ 2) t h| ≤ L * h}

lemma Bset_eq (k : ℕ) : Bset k = BsetL 1 k := by
  ext f; simp [Bset, BsetL]

lemma isClosed_BsetL (L : ℝ) (k : ℕ) : IsClosed (BsetL L k) := by
  have e : BsetL L k = ⋂ t : ℝ, ⋂ h : ℝ, {f : L2I | 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h →
      t + h ≤ 1 → |D2 (fun s => prim f s ^ 2) t h| ≤ L * h} := by
    ext f; simp [BsetL]
  rw [e]
  refine isClosed_iInter fun t => isClosed_iInter fun h => ?_
  by_cases hc : 0 ≤ h ∧ h ≤ 1 / ((k : ℝ) + 1) ∧ 0 ≤ t - h ∧ t + h ≤ 1
  · obtain ⟨h0, hk, h1, h2⟩ := hc
    have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
    have e2 : {f : L2I | 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ L * h} =
        {f : L2I | |D2 (fun s => prim f s ^ 2) t h| ≤ L * h} := by
      ext f; exact ⟨fun H => H h0 hk h1 h2, fun H _ _ _ _ => H⟩
    rw [e2]
    refine isClosed_le ?_ continuous_const
    simp only [D2]
    exact continuous_abs.comp ((((continuous_prim_at m1).pow 2).sub
      (((continuous_prim_at m2).pow 2).const_mul 2)).add ((continuous_prim_at m3).pow 2))
  · have e2 : {f : L2I | 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ L * h} = univ := by
      ext f
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h0 hk h1 h2
      exact absurd ⟨h0, hk, h1, h2⟩ hc
    rw [e2]; exact isClosed_univ

/-! ### Empty interior -/

variable {n : ℕ}

set_option maxHeartbeats 1000000 in -- many local definitions; the final term is slow to check
/-- **`BsetL L k` has empty interior in `SN n`.** -/
theorem exists_not_BsetL {L : ℝ} (hL : 0 ≤ L) (k : ℕ) {x : L2I} (hx : x ∈ SN n)
    (hxB : x ∈ BsetL L k) {ε : ℝ} (hε : 0 < ε) : ∃ y ∈ SN n, ‖y - x‖ < ε ∧ y ∉ BsetL L k := by
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
  set w := r ^ 4
  have hw : 0 < w := by positivity
  have hwr : w ≤ r := by
    simp only [w]
    calc r ^ 4 ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (by norm_num)
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
  set δ := sg * r ^ 3
  have hδabs : |δ| = r ^ 3 := by
    simp only [δ]; rw [abs_mul, hsg, one_mul, abs_of_pos (by positivity)]
  have hδγ : δ * γ = r ^ 3 * |γ| := by simp only [δ]; rw [← hsgγ]; ring
  have hδ1 : |δ| ≤ 1 := by
    rw [hδabs]; exact pow_le_one₀ hr0.le hr1.le
  -- `‖δ q‖ ≤ 2r`
  have hδq : |δ| * ‖q‖ ≤ 2 * r := by
    have hsq : (|δ| * ‖q‖) ^ 2 ≤ (2 * r) ^ 2 := by
      rw [mul_pow, hδabs]
      calc (r ^ 3) ^ 2 * ‖q‖ ^ 2 ≤ (r ^ 3) ^ 2 * (2 / w) :=
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
  -- the violation
  set h := min w (1 / ((k : ℝ) + 1))
  have hh0 : 0 < h := lt_min hw (by positivity)
  have hhw : h ≤ w := min_le_left _ _
  have hhk : h ≤ 1 / ((k : ℝ) + 1) := min_le_right _ _
  have ht1 : 0 ≤ t0 - h := by linarith
  have ht2 : t0 + h ≤ 1 := by linarith
  have hD := hxB t0 h hh0.le hhk ht1 ht2
  have key := D2_perturb (lam := lam) (δ := δ) hw hh0 hhw ht1 ht2 hqp hg0 hlam2' hD
  refine ⟨y, hySN, hclose, fun hyB => ?_⟩
  have hyD := hyB t0 h hh0.le hhk ht1 ht2
  change |D2 (fun s => prim (lam • (x + δ • q)) s ^ 2) t0 h| ≤ L * h at hyD
  set S := ∫ s in (t0 - h)..(t0 + h), (x : ℝ → ℝ) s ^ 2
  have hS : S ≤ M ^ 2 := integral_sq_le_mu1 x ht1 (by linarith) ht2
  have hS0 : 0 ≤ S := intervalIntegral.integral_nonneg (by linarith) fun s _ => sq_nonneg _
  have hA : 4 * (δ * prim x t0) / w = 4 * |γ| / r := by
    change 4 * (δ * γ) / w = _
    rw [hδγ]; simp only [w]; field_simp
  rw [hA] at key
  -- `4|γ|/r > 3L + (L + 2M²)/|γ|`
  have hbig : 3 * L + (L + 2 * M ^ 2) / |γ| < 4 * |γ| / r := by
    have := hr3
    simp only [c3] at this
    rw [lt_div_iff₀ (by positivity)] at this
    rw [lt_div_iff₀ hr0]
    have : 0 ≤ (L + 2 * M ^ 2) / |γ| := by positivity
    nlinarith
  have herr : |δ| * (L * h + 2 * (h * S)) / |prim x t0| ≤ h * ((L + 2 * M ^ 2) / |γ|) := by
    change |δ| * (L * h + 2 * (h * S)) / |γ| ≤ _
    rw [div_le_iff₀ hγ]
    have h1 : L * h + 2 * (h * S) ≤ L * h + 2 * (h * M ^ 2) := by
      have := mul_le_mul_of_nonneg_left hS hh0.le; linarith
    have : |δ| * (L * h + 2 * (h * S)) ≤ 1 * (L * h + 2 * (h * M ^ 2)) :=
      mul_le_mul hδ1 h1 (by positivity) zero_le_one
    calc |δ| * (L * h + 2 * (h * S)) ≤ h * (L + 2 * M ^ 2) := by linarith
      _ = h * ((L + 2 * M ^ 2) / |γ|) * |γ| := by field_simp
  have : L * h < (4 * |γ| / r * h - L * h - |δ| * (L * h + 2 * (h * S)) / |prim x t0|) / 2 := by
    have h3 := mul_lt_mul_of_pos_left hbig hh0
    have e1 : h * (3 * L + (L + 2 * M ^ 2) / |γ|) =
        3 * (L * h) + h * ((L + 2 * M ^ 2) / |γ|) := by ring
    have e2 : h * (4 * |γ| / r) = 4 * |γ| / r * h := by ring
    rw [e1, e2] at h3
    linarith only [h3, herr]
  linarith only [this, key, hyD]

/-- **`Bset k` has empty interior in `SN n`.** -/
theorem exists_not_Bset (k : ℕ) {x : L2I} (hx : x ∈ SN n) (hxB : x ∈ Bset k) {ε : ℝ}
    (hε : 0 < ε) : ∃ y ∈ SN n, ‖y - x‖ < ε ∧ y ∉ Bset k := by
  rw [Bset_eq] at hxB ⊢
  exact exists_not_BsetL zero_le_one k hx hxB hε

/-! ### Meagreness -/

/-- `Bset k` in `SN n`. -/
def BsetS (n : ℕ) (k : ℕ) : Set (SN n) := Subtype.val ⁻¹' Bset k

lemma isNowhereDense_BsetS (k : ℕ) : IsNowhereDense (BsetS n k) := by
  have hcl : IsClosed (BsetS n k) := (isClosed_Bset k).preimage continuous_subtype_val
  rw [IsNowhereDense, hcl.closure_eq]
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨y, hy, hyx, hyB⟩ := exists_not_Bset k x.2 (interior_subset hx : x ∈ BsetS n k) hε
  have hyb : (⟨y, hy⟩ : SN n) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]; exact hyx
  exact hyB (show (⟨y, hy⟩ : SN n) ∈ BsetS n k from interior_subset (hball hyb))

/-- `ρ` has a profile `K` that is `C¹` on `[0, 1]` and vanishes at the walls. -/
def C1Dens (ρ : Pot → ℝ) : Prop :=
  ∃ K K' : ℝ → ℝ, ContinuousOn K' (Icc 0 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt K (K' t) (Icc 0 1) t) ∧ K 0 = 0 ∧ K 1 = 0 ∧
    ρ = fun u => ∫ t, ext u t * K t ∂μ1

/-- A `C¹` profile has second differences at most `h` for small `h`. -/
lemma D2_le_of_C1 {K K' : ℝ → ℝ} (hK' : ContinuousOn K' (Icc 0 1))
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt K (K' t) (Icc 0 1) t) :
    ∃ k : ℕ, ∀ t h : ℝ, 0 ≤ h → h ≤ 1 / ((k : ℝ) + 1) → 0 ≤ t - h → t + h ≤ 1 →
      |D2 K t h| ≤ h := by
  obtain ⟨d, hd, hu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hK') (1 / 2) (by norm_num)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd
  refine ⟨k, fun t h h0 hk' h1 h2 => ?_⟩
  have hhd : h < d := lt_of_le_of_lt hk' hk
  have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- `|K(t+h) - K(t) - h K'(t)| ≤ h/2` and `|K(t) - K(t-h) - h K'(t)| ≤ h/2`
  have side : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → t ∈ Icc a b → b - a ≤ h →
      ‖(K b - b * K' t) - (K a - a * K' t)‖ ≤ 1 / 2 * (b - a) := by
    intro a b ha hab hb hta hba
    have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha hb
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => K s - s * K' t)
      (f' := fun s => K' s - K' t) (fun s hs => ?_) (fun s hs => ?_) b ⟨hab, le_rfl⟩
    · exact (((hK s (hsub hs)).mono hsub).sub
        ((hasDerivWithinAt_id s _).mul_const (K' t))).congr_deriv (by simp)
    · have hs' : s ∈ Icc (0 : ℝ) 1 := hsub (Ico_subset_Icc_self hs)
      have hdist : dist s t < d := by
        rw [Real.dist_eq]
        rw [abs_lt]
        constructor <;> linarith [hs.1, hs.2, hta.1, hta.2]
      have := hu s hs' t m2 hdist
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]; linarith
  have s1 := side t (t + h) m2.1 (by linarith) h2 ⟨le_rfl, by linarith⟩ (by linarith)
  have s2 := side (t - h) t h1 (by linarith) m2.2 ⟨by linarith, le_rfl⟩ (by linarith)
  rw [Real.norm_eq_abs] at s1 s2
  rw [D2]
  have e : K (t + h) - 2 * K t + K (t - h) =
      ((K (t + h) - (t + h) * K' t) - (K t - t * K' t)) -
        ((K t - t * K' t) - (K (t - h) - (t - h) * K' t)) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have : t + h - t = h := by ring
  have : t - (t - h) = h := by ring
  nlinarith [abs_nonneg ((K (t + h) - (t + h) * K' t) - (K t - t * K' t))]

lemma mem_BsetS_of_C1Dens (x : SN n) (h : C1Dens (rhoF x)) : ∃ k : ℕ, x ∈ BsetS n k := by
  obtain ⟨K, K', hK', hK, hK0, hK1, hρ⟩ := h
  obtain ⟨k, hk⟩ := D2_le_of_C1 hK' hK
  have hKc : ContinuousOn K (Icc 0 1) := fun t ht => (hK t ht).continuousWithinAt
  set Kc : ℝ → ℝ := fun t => K (projIcc (0 : ℝ) 1 zero_le_one t)
  have hKcc : Continuous Kc :=
    hKc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun t => (projIcc _ _ _ t).2
  have hc := H10.continuous_clamp (h10_prim x.2.1)
  have he := eqOn_of_integral_pot (f := fun t => H10.clamp (prim (x : L2I)) t ^ 2) (g := Kc)
    (hc.pow 2) hKcc fun u => by
      have h1 := congrFun hρ u
      change ∫ t, ext u t * prim (x : L2I) t ^ 2 ∂μ1 = ∫ t, ext u t * K t ∂μ1 at h1
      have h2 : ∫ t in Ioo (0 : ℝ) 1, ext u t * H10.clamp (prim (x : L2I)) t ^ 2 =
          ∫ t, ext u t * prim (x : L2I) t ^ 2 ∂μ1 :=
        setIntegral_congr_fun measurableSet_Ioo fun t ht => by
          simp only [H10.clamp_eq (Ioo_subset_Icc_self ht)]
      have h3 : ∫ t in Ioo (0 : ℝ) 1, ext u t * Kc t = ∫ t, ext u t * K t ∂μ1 :=
        setIntegral_congr_fun measurableSet_Ioo fun t ht => by
          simp only [Kc, projIcc_of_mem _ (Ioo_subset_Icc_self ht)]
      rw [h2, h3, h1]
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, prim (x : L2I) t ^ 2 = K t := by
    intro t ⟨h0, h1⟩
    rcases eq_or_lt_of_le h0 with rfl | h0
    · rw [prim_zero, hK0]; ring
    rcases eq_or_lt_of_le h1 with rfl | h1
    · rw [x.2.1, hK1]; ring
    have := he ⟨h0, h1⟩
    simp only [H10.clamp_eq (⟨h0.le, h1.le⟩ : t ∈ Icc (0 : ℝ) 1), Kc,
      projIcc_of_mem _ (⟨h0.le, h1.le⟩ : t ∈ Icc (0 : ℝ) 1)] at this
    exact this
  refine ⟨k, fun t h h0 hk' h1 h2 => ?_⟩
  have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
  have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
  have e : D2 (fun s => prim (x : L2I) s ^ 2) t h = D2 K t h := by
    simp only [D2]; rw [heq _ m1, heq _ m2, heq _ m3]
  rw [e]
  exact hk t h h0 hk' h1 h2

/-- **Densities with a `C¹` profile are meagre** in the space of `N`-representable densities. -/
theorem meagre_C1Dens : IsMeagre {x : SN n | C1Dens (rhoF x)} :=
  (isMeagre_iUnion fun k : ℕ => (isNowhereDense_BsetS (n := n) k).isMeagre).mono
    fun x hx => mem_iUnion.2 (mem_BsetS_of_C1Dens x hx)

end DFT.Continuum.Line
