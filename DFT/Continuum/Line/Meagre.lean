/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Prim

/-!
# Kohn–Sham `v`-representable densities are meagre

In the complete metric space `SN n` of `N`-representable densities (`ρ_f = (∫₀ᵗ f)²`, `f ∈ L²`,
see `Line/Prim`), the densities with a `C²` profile form a set of first Baire category. Kohn–Sham
densities `Σ_j φ_j²` (fermions) and `N φ₀²` (bosons) are `C²`, and so are the ground-state densities
of one particle, so all of these are **meagre**: dense (`Line/Dense`) but of first category. Their
complement, the non-`v`-representable densities, is residual, in particular dense.

On a lattice the picture is the opposite: there the `v`-representable densities fill the interior
of the density polytope. The difference is the potential class: with continuous potentials the
ground-state densities are too regular. With distributional potentials (`H⁻¹`) every positive
`H¹` density on an interval is `v`-representable (Corso, Lett. Math. Phys. 2026).

The proof:
* `D2_bound_of_C2`: a `C²` function has second differences `|K(t+h) - 2K(t) + K(t-h)| ≤ L h²`;
* `Cond L`: densities with that bound, closed in `L²` (`isClosed_Cond`);
* `exists_not_Cond`: **empty interior.** Add a small tentF of width `w` to `g = √ρ` at a point
  where `g ≠ 0` and renormalise. The second difference at the apex picks up a term of order `h/w`,
  while the cross terms are `O(h²) + O(h ∫_{t-h}^{t+h} g'²) = o(h)` by Cauchy–Schwarz.
* `meagre_C2Dens`, **`ks_meagre`**, **`ks_nonrep_dense`**, **`one_vrep_meagre`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

/-- The second difference `F(t + h) - 2 F(t) + F(t - h)`. -/
def D2 (F : ℝ → ℝ) (t h : ℝ) : ℝ := F (t + h) - 2 * F t + F (t - h)

/-! ### `C²` functions have bounded second differences -/

theorem D2_bound_of_C2 {K : ℝ → ℝ} (hK : ContDiff ℝ 2 K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t h, 0 ≤ h → 0 ≤ t - h → t + h ≤ 1 → |D2 K t h| ≤ L * h ^ 2 := by
  have h1 : ContDiff ℝ 1 (deriv K) := (contDiff_succ_iff_deriv.mp hK).2.2
  have hdd : Continuous (deriv (deriv K)) := h1.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hdd.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨2 * M, by positivity, fun t h h0 ht0 ht1 => ?_⟩
  have hK1 : ∀ r, HasDerivAt K (deriv K r) r := fun r =>
    ((hK.differentiable (by norm_num)) r).hasDerivAt
  have hK2 : ∀ r, HasDerivAt (deriv K) (deriv (deriv K) r) r := fun r =>
    (h1.differentiable one_ne_zero r).hasDerivAt
  have hd : ∀ s ∈ Icc (0 : ℝ) h, ‖deriv K (t + s) - deriv K (t - s)‖ ≤ M * (2 * s) := by
    intro s hs
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := deriv K) (f' := deriv (deriv K))
      (a := t - s) (b := t + s) (C := M) (fun r _ => (hK2 r).hasDerivWithinAt)
      (fun r hr => hM r ⟨by linarith [hr.1, hs.2], by linarith [hr.2, hs.2]⟩) (t + s)
      ⟨by linarith [hs.1], le_rfl⟩
    calc _ ≤ M * (t + s - (t - s)) := this
      _ = M * (2 * s) := by ring
  set F : ℝ → ℝ := fun s => K (t + s) + K (t - s)
  have hF : ∀ s, HasDerivAt F (deriv K (t + s) - deriv K (t - s)) s := fun s => by
    have a := (hK1 (t + s)).comp s ((hasDerivAt_id s).const_add t)
    have b := (hK1 (t - s)).comp s ((hasDerivAt_id s).const_sub t)
    exact (a.add b).congr_deriv (by simp; ring)
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := F) (a := 0) (b := h)
    (C := 2 * M * h) (fun s _ => (hF s).hasDerivWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).trans (by nlinarith [hs.1, hs.2])) h ⟨h0, le_rfl⟩
  simp only [F, add_zero, sub_zero, Real.norm_eq_abs] at this
  rw [D2]
  calc |K (t + h) - 2 * K t + K (t - h)| = |K (t + h) + K (t - h) - (K t + K t)| := by
        congr 1; ring
    _ ≤ 2 * M * h * h := this
    _ = 2 * M * h ^ 2 := by ring

/-! ### The closed sets `Cond L` -/

/-- `ρ_f` has second differences at most `L h²` on `[0, 1]`. -/
def Cond (L : ℝ) : Set L2I :=
  {f | ∀ t h : ℝ, 0 ≤ h → 0 ≤ t - h → t + h ≤ 1 → |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ 2}

lemma continuous_prim_at {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Continuous fun f : L2I => prim f s :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun f f' => by
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact abs_prim_sub_le f f' hs).continuous

lemma isClosed_Cond (L : ℝ) : IsClosed (Cond L) := by
  have e : Cond L = ⋂ t : ℝ, ⋂ h : ℝ, {f : L2I | 0 ≤ h → 0 ≤ t - h → t + h ≤ 1 →
      |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ 2} := by
    ext f; simp [Cond]
  rw [e]
  refine isClosed_iInter fun t => isClosed_iInter fun h => ?_
  by_cases hc : 0 ≤ h ∧ 0 ≤ t - h ∧ t + h ≤ 1
  · obtain ⟨h0, h1, h2⟩ := hc
    have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
    have e2 : {f : L2I | 0 ≤ h → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ 2} =
        {f : L2I | |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ 2} := by
      ext f; simp [h0, h1, h2]
    rw [e2]
    refine isClosed_le ?_ continuous_const
    simp only [D2]
    exact continuous_abs.comp ((((continuous_prim_at m1).pow 2).sub
      (((continuous_prim_at m2).pow 2).const_mul 2)).add ((continuous_prim_at m3).pow 2))
  · have e2 : {f : L2I | 0 ≤ h → 0 ≤ t - h → t + h ≤ 1 →
        |D2 (fun s => prim f s ^ 2) t h| ≤ L * h ^ 2} = univ := by
      ext f
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h0 h1 h2
      exact absurd ⟨h0, h1, h2⟩ hc
    rw [e2]; exact isClosed_univ

/-! ### Cauchy–Schwarz for the primitive -/

lemma sq_prim_sub_le (f : L2I) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (prim f b - prim f a) ^ 2 ≤ (b - a) * ∫ s in a..b, (f : ℝ → ℝ) s ^ 2 := by
  have hii : ∀ {k : ℝ → ℝ}, Integrable k μ1 → IntervalIntegrable k volume a b := fun hk =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
      ((show IntegrableOn _ (Ioo (0 : ℝ) 1) volume from hk).mono_set (Ioo_subset_Ioo ha hb))
  have e : prim f b - prim f a = ∫ s in a..b, (f : ℝ → ℝ) s :=
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_of_mu1 (integrable_L2I f) ⟨le_trans ha hab, hb⟩)
      (intervalIntegrable_of_mu1 (integrable_L2I f) ⟨ha, hab.trans hb⟩)
  rw [e]
  set I := ∫ s in a..b, (f : ℝ → ℝ) s
  set J := ∫ s in a..b, (f : ℝ → ℝ) s ^ 2
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp [I]
  · have hpos : 0 < b - a := sub_pos.2 h
    set m := I / (b - a)
    have h0 : 0 ≤ ∫ s in a..b, ((f : ℝ → ℝ) s - m) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg _)
    have i1 : IntervalIntegrable (fun s => (f : ℝ → ℝ) s ^ 2 - 2 * m * (f : ℝ → ℝ) s) volume a b :=
      (hii (integrable_sq_L2I f)).sub ((hii (integrable_L2I f)).const_mul _)
    have hexp : ∫ s in a..b, ((f : ℝ → ℝ) s - m) ^ 2 = J - 2 * m * I + m ^ 2 * (b - a) := by
      have : (fun s => ((f : ℝ → ℝ) s - m) ^ 2) =
          fun s => ((f : ℝ → ℝ) s ^ 2 - 2 * m * (f : ℝ → ℝ) s) + m ^ 2 := by
        funext s; ring
      rw [this, intervalIntegral.integral_add i1 intervalIntegrable_const,
        intervalIntegral.integral_sub (hii (integrable_sq_L2I f))
          ((hii (integrable_L2I f)).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      ring
    have e2 : J - 2 * m * I + m ^ 2 * (b - a) = J - I ^ 2 / (b - a) := by
      simp only [m]; field_simp; ring
    rw [hexp, e2] at h0
    have h3 : I ^ 2 / (b - a) ≤ J := by linarith
    rw [div_le_iff₀ hpos] at h3
    linarith

/-! ### A tentF -/

/-- The tentF of height `1` and half-width `w` centred at `t₀`. -/
noncomputable def tentF (t0 w t : ℝ) : ℝ := max 0 (1 - |t - t0| / w)

lemma lipschitz_tent {t0 w : ℝ} (hw : 0 < w) :
    LipschitzWith ⟨1 / w, by positivity⟩ (tentF t0 w) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp only [tentF, Real.dist_eq]
    calc |max 0 (1 - |x - t0| / w) - max 0 (1 - |y - t0| / w)|
        ≤ |(1 - |x - t0| / w) - (1 - |y - t0| / w)| := by
          rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
      _ = |(|y - t0| - |x - t0|)| / w := by
          rw [show (1 - |x - t0| / w) - (1 - |y - t0| / w) = (|y - t0| - |x - t0|) / w by ring,
            abs_div, abs_of_pos hw]
      _ ≤ |x - y| / w := by
          refine div_le_div_of_nonneg_right ?_ hw.le
          have := abs_abs_sub_abs_le_abs_sub (y - t0) (x - t0)
          rw [show y - t0 - (x - t0) = y - x by ring] at this
          rw [abs_sub_comm x y]; exact this
      _ = 1 / w * |x - y| := by ring

lemma tent_center (t0 w : ℝ) : tentF t0 w t0 = 1 := by
  simp [tentF]

lemma tent_side {t0 w h : ℝ} (hw : 0 < w) (h0 : 0 ≤ h) (hhw : h ≤ w) :
    tentF t0 w (t0 + h) = 1 - h / w ∧ tentF t0 w (t0 - h) = 1 - h / w := by
  have hle : h / w ≤ 1 := by rw [div_le_one hw]; exact hhw
  constructor
  · simp only [tentF, add_sub_cancel_left, abs_of_nonneg h0]
    exact max_eq_right (by linarith)
  · simp only [tentF, sub_sub_cancel_left, abs_neg, abs_of_nonneg h0]
    exact max_eq_right (by linarith)

lemma tent_far {t0 w t : ℝ} (hw : 0 < w) (ht : w ≤ |t - t0|) : tentF t0 w t = 0 := by
  simp only [tentF]
  refine max_eq_left ?_
  have : 1 ≤ |t - t0| / w := by rw [le_div_iff₀ hw, one_mul]; exact ht
  linarith

/-- The tentF as the primitive of an `L²` function. -/
lemma exists_tent_L2 {t0 w : ℝ} (hw : 0 < w) (hw0 : w ≤ t0) (hw1 : w ≤ 1 - t0) :
    ∃ q : L2I, prim q 1 = 0 ∧ ∀ t ∈ Icc (0 : ℝ) 1, prim q t = tentF t0 w t := by
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
  refine ⟨q, ?_, hp⟩
  rw [hp 1 ⟨zero_le_one, le_rfl⟩]
  exact tent_far hw (by rw [abs_of_pos (by linarith)]; exact hw1)

/-! ### Empty interior -/

variable {n : ℕ}

/-- **The sets `Cond L` have empty interior in `SN n`**: every `x ∈ SN n` with `ρ_x ∈ Cond L` is a
limit of `y ∈ SN n` with `ρ_y ∉ Cond L`. -/
theorem exists_not_Cond {L : ℝ} (hL : 0 ≤ L) {x : L2I} (hx : x ∈ SN n) (hxL : x ∈ Cond L)
    {ε : ℝ} (hε : 0 < ε) : ∃ y ∈ SN n, ‖y - x‖ < ε ∧ y ∉ Cond L := by
  set g := prim x with hgdef
  have hN : ∫ t, g t ^ 2 ∂μ1 = n + 1 := hx.2
  have hNp : (0 : ℝ) < n + 1 := by positivity
  -- a point where `g ≠ 0`
  obtain ⟨t0, ht0, hg0⟩ : ∃ t0 ∈ Ioo (0 : ℝ) 1, g t0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∫ t, g t ^ 2 ∂μ1 = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht => by simp [hcon t ht]
    linarith
  set γ := g t0
  set w := min t0 (1 - t0) / 2
  have hmin : 0 < min t0 (1 - t0) := lt_min ht0.1 (by linarith [ht0.2])
  have hw : 0 < w := by positivity
  have hw0 : w ≤ t0 := by have := min_le_left t0 (1 - t0); simp only [w]; linarith
  have hw1 : w ≤ 1 - t0 := by have := min_le_right t0 (1 - t0); simp only [w]; linarith
  obtain ⟨q, hq1, hqp⟩ := exists_tent_L2 hw hw0 hw1
  -- the perturbed family
  set F : ℝ → L2I := fun δ => x + δ • q
  have hFc : Continuous F := continuous_const.add (continuous_id.smul continuous_const)
  have hFp : ∀ δ : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, prim (F δ) t = g t + δ * tentF t0 w t :=
    fun δ t ht => by simp only [F]; rw [prim_add _ _ ht, prim_smul _ _ ht, hqp t ht]
  set J : ℝ → ℝ := fun δ => ∫ t, prim (F δ) t ^ 2 ∂μ1
  have hJc : Continuous J := continuous_int_prim_sq.comp hFc
  have hJ0 : J 0 = n + 1 := by simp only [J, F, zero_smul, add_zero]; exact hN
  set lam : ℝ → ℝ := fun δ => √((n + 1) / J δ)
  set y : ℝ → L2I := fun δ => lam δ • F δ
  have hyc : ContinuousAt y 0 := by
    have hl : ContinuousAt lam 0 :=
      (continuous_const.continuousAt.div hJc.continuousAt (by rw [hJ0]; exact hNp.ne')).sqrt
    exact hl.smul hFc.continuousAt
  have hy0 : y 0 = x := by
    simp only [y, lam, F, hJ0, div_self hNp.ne', Real.sqrt_one, zero_smul, add_zero, one_smul]
  have hev1 : ∀ᶠ δ in 𝓝 (0 : ℝ), (n + 1 : ℝ) / 2 < J δ ∧ J δ < 2 * (n + 1) := by
    have := hJc.continuousAt (x := 0)
    rw [ContinuousAt, hJ0] at this
    exact this.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have hev2 : ∀ᶠ δ in 𝓝 (0 : ℝ), ‖y δ - x‖ < ε := by
    have := hyc.tendsto
    rw [hy0] at this
    filter_upwards [this.eventually (Metric.ball_mem_nhds x hε)] with δ hδ
    rwa [dist_eq_norm] at hδ
  obtain ⟨δ0, hδ0, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
  set sg : ℝ := if 0 < γ then 1 else -1
  have hsg : |sg| = 1 := by simp only [sg]; split_ifs <;> simp
  have hsgγ : 0 < sg * γ := by
    simp only [sg]; split_ifs with h
    · simpa using h
    · have : γ < 0 := lt_of_le_of_ne (not_lt.1 h) hg0
      linarith
  set δ := sg * (δ0 / 2)
  have hδabs : |δ| = δ0 / 2 := by
    simp only [δ]; rw [abs_mul, hsg, one_mul, abs_of_pos (by positivity)]
  have hδγ : 0 < δ * γ := by
    have : δ * γ = (sg * γ) * (δ0 / 2) := by simp only [δ]; ring
    rw [this]; positivity
  have hδin : dist δ 0 < δ0 := by rw [Real.dist_eq, sub_zero, hδabs]; linarith
  obtain ⟨⟨hJl, hJu⟩, hclose⟩ := hball hδin
  have hJpos : 0 < J δ := by linarith
  have hlam2 : lam δ ^ 2 = (n + 1) / J δ := Real.sq_sqrt (by positivity)
  have hlam2' : 1 / 2 ≤ lam δ ^ 2 := by
    rw [hlam2, le_div_iff₀ hJpos]; linarith
  have hyp : ∀ t ∈ Icc (0 : ℝ) 1, prim (y δ) t = lam δ * (g t + δ * tentF t0 w t) :=
    fun t ht => by simp only [y]; rw [prim_smul _ _ ht, hFp δ t ht]
  have hySN : y δ ∈ SN n := by
    refine ⟨?_, ?_⟩
    · simp only [y]
      rw [prim_smul _ _ ⟨zero_le_one, le_rfl⟩]
      simp only [F]
      rw [prim_add _ _ ⟨zero_le_one, le_rfl⟩, prim_smul _ _ ⟨zero_le_one, le_rfl⟩, hx.1, hq1]
      ring
    · have : ∫ t, prim (y δ) t ^ 2 ∂μ1 = lam δ ^ 2 * J δ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        simp only [y]
        rw [prim_smul _ _ (Ioo_subset_Icc_self ht)]
        ring
      rw [this, hlam2, div_mul_cancel₀ _ hJpos.ne']
  -- the oscillation of `g` near `t₀`
  set Φ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, (x : ℝ → ℝ) s ^ 2
  have hΦc : ContinuousOn Φ (Icc 0 1) := by
    simpa [uIcc01] using ((intervalIntegrable_of_mu1 (integrable_sq_L2I x)
      ⟨zero_le_one, le_rfl⟩).absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by simp)).continuousOn
  have hσ : Tendsto (fun h => Φ (t0 + h) - Φ (t0 - h)) (𝓝 0) (𝓝 0) := by
    have hΦt : ContinuousAt Φ t0 := hΦc.continuousAt (Icc_mem_nhds ht0.1 ht0.2)
    have h1 : Tendsto (fun h : ℝ => t0 + h) (𝓝 0) (𝓝 t0) := by
      exact (by fun_prop : Continuous fun h : ℝ => t0 + h).tendsto' 0 t0 (by simp)
    have h2 : Tendsto (fun h : ℝ => t0 - h) (𝓝 0) (𝓝 t0) := by
      exact (by fun_prop : Continuous fun h : ℝ => t0 - h).tendsto' 0 t0 (by simp)
    simpa using (hΦt.tendsto.comp h1).sub (hΦt.tendsto.comp h2)
  set A := 4 * (δ * γ) / w
  have hA : 0 < A := by positivity
  have hγabs : 0 < |γ| := abs_pos.2 hg0
  have hR : Tendsto (fun h => 3 * L * h + |δ| * (L * h + 2 * (Φ (t0 + h) - Φ (t0 - h))) / |γ|)
      (𝓝 0) (𝓝 0) := by
    have := (tendsto_id.const_mul (3 * L)).add
      ((((tendsto_id.const_mul L).add (hσ.const_mul 2)).const_mul |δ|).div_const |γ|)
    simpa using this
  have hev3 : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (3 * L * h + |δ| * (L * h + 2 * (Φ (t0 + h) - Φ (t0 - h))) / |γ| < A ∧ h < w) :=
    ((hR.eventually (gt_mem_nhds hA)).and (Iio_mem_nhds hw)).filter_mono nhdsWithin_le_nhds
  obtain ⟨h, ⟨hRh, hhw⟩, hh0⟩ := (hev3.and self_mem_nhdsWithin).exists
  have hh0' : 0 < h := hh0
  refine ⟨y δ, hySN, hclose, fun hyC => ?_⟩
  have ht1 : 0 ≤ t0 - h := by linarith
  have ht2 : t0 + h ≤ 1 := by linarith
  have m1 : t0 + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht2⟩
  have m2 : t0 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht0
  have m3 : t0 - h ∈ Icc (0 : ℝ) 1 := ⟨ht1, by linarith⟩
  have key := hyC t0 h hh0'.le ht1 ht2
  obtain ⟨tp, tm⟩ := tent_side (t0 := t0) hw hh0'.le hhw.le
  simp only [D2] at key
  rw [hyp _ m1, hyp _ m2, hyp _ m3, tp, tm, tent_center t0 w] at key
  have hD := hxL t0 h hh0'.le ht1 ht2
  simp only [D2] at hD
  -- notation
  set P := g (t0 + h)
  set R := g (t0 - h)
  set a := 1 - h / w
  have ha0 : 0 ≤ a := by simp only [a]; rw [sub_nonneg, div_le_one hw]; linarith
  have ha1 : a ≤ 1 := by simp only [a]; have : 0 ≤ h / w := by positivity
                         linarith
  have h1a : 1 - a = h / w := by simp only [a]; ring
  set σ := Φ (t0 + h) - Φ (t0 - h)
  -- Cauchy–Schwarz on both sides
  have hΦsub : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 →
      Φ v - Φ u = ∫ s in u..v, (x : ℝ → ℝ) s ^ 2 := fun hu huv hv =>
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_of_mu1 (integrable_sq_L2I x) ⟨le_trans hu huv, hv⟩)
      (intervalIntegrable_of_mu1 (integrable_sq_L2I x) ⟨hu, huv.trans hv⟩)
  have hmono : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 → 0 ≤ Φ v - Φ u := fun hu huv hv => by
    rw [hΦsub hu huv hv]; exact intervalIntegral.integral_nonneg huv fun s _ => sq_nonneg _
  have hdP : (P - γ) ^ 2 ≤ h * σ := by
    have := sq_prim_sub_le x m2.1 (by linarith : t0 ≤ t0 + h) ht2
    rw [← hΦsub m2.1 (by linarith) ht2, show t0 + h - t0 = h by ring] at this
    have hm := hmono ht1 (by linarith : t0 - h ≤ t0) m2.2
    calc (P - γ) ^ 2 ≤ h * (Φ (t0 + h) - Φ t0) := this
      _ ≤ h * σ := by gcongr; simp only [σ]; linarith
  have hdR : (R - γ) ^ 2 ≤ h * σ := by
    have := sq_prim_sub_le x ht1 (by linarith : t0 - h ≤ t0) m2.2
    rw [← hΦsub ht1 (by linarith) m2.2, show t0 - (t0 - h) = h by ring] at this
    have hm := hmono m2.1 (by linarith : t0 ≤ t0 + h) ht2
    calc (R - γ) ^ 2 = (γ - R) ^ 2 := by ring
      _ ≤ h * (Φ t0 - Φ (t0 - h)) := this
      _ ≤ h * σ := by gcongr; simp only [σ]; linarith
  -- the cross term
  set T := (P + δ * a) ^ 2 - 2 * (γ + δ * 1) ^ 2 + (R + δ * a) ^ 2
  have hid : 2 * γ * ((P - γ) + (R - γ)) =
      (P ^ 2 - 2 * γ ^ 2 + R ^ 2) - (P - γ) ^ 2 - (R - γ) ^ 2 := by ring
  have hcross : |2 * δ * a * ((P - γ) + (R - γ))| ≤ |δ| * (L * h ^ 2 + 2 * (h * σ)) / |γ| := by
    rw [le_div_iff₀ hγabs]
    have e3 : |2 * δ * a * ((P - γ) + (R - γ))| * |γ| =
        |δ| * a * |2 * γ * ((P - γ) + (R - γ))| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_mul, abs_mul]; ring
    rw [e3, hid]
    have hb : |(P ^ 2 - 2 * γ ^ 2 + R ^ 2) - (P - γ) ^ 2 - (R - γ) ^ 2| ≤
        L * h ^ 2 + 2 * (h * σ) := by
      have := abs_sub (P ^ 2 - 2 * γ ^ 2 + R ^ 2 - (P - γ) ^ 2) ((R - γ) ^ 2)
      have := abs_sub (P ^ 2 - 2 * γ ^ 2 + R ^ 2) ((P - γ) ^ 2)
      rw [abs_of_nonneg (sq_nonneg (P - γ))] at this
      have := abs_of_nonneg (sq_nonneg (R - γ))
      linarith
    calc |δ| * a * |P ^ 2 - 2 * γ ^ 2 + R ^ 2 - (P - γ) ^ 2 - (R - γ) ^ 2|
        ≤ |δ| * 1 * (L * h ^ 2 + 2 * (h * σ)) := by
          gcongr
      _ = _ := by ring
  -- `-T` is large
  have hT : -T ≥ A * h - L * h ^ 2 - |δ| * (L * h ^ 2 + 2 * (h * σ)) / |γ| := by
    have e4 : -T = -(P ^ 2 - 2 * γ ^ 2 + R ^ 2) + 4 * (δ * γ) * (1 - a)
        - 2 * δ * a * ((P - γ) + (R - γ)) + 2 * δ ^ 2 * (1 - a ^ 2) := by
      simp only [T]; ring
    have hA' : 4 * (δ * γ) * (1 - a) = A * h := by
      rw [h1a]; simp only [A]; field_simp
    have h5 : 0 ≤ 2 * δ ^ 2 * (1 - a ^ 2) := by
      have : 0 ≤ 1 - a ^ 2 := by
        rw [show 1 - a ^ 2 = (1 - a) * (1 + a) by ring]
        exact mul_nonneg (sub_nonneg.2 ha1) (by linarith)
      positivity
    have h6 := le_abs_self (2 * δ * a * ((P - γ) + (R - γ)))
    have h7 := le_abs_self (P ^ 2 - 2 * γ ^ 2 + R ^ 2)
    rw [e4, hA']
    linarith only [h5, h6, h7, hD, hcross]
  have hgoal : 2 * L * h ^ 2 < -T := by
    set Q := |δ| * (L * h + 2 * σ) / |γ|
    have e5 : |δ| * (L * h ^ 2 + 2 * (h * σ)) / |γ| = h * Q := by simp only [Q]; ring
    have h8 : 3 * L * h ^ 2 + h * Q < A * h := by
      calc 3 * L * h ^ 2 + h * Q = (3 * L * h + Q) * h := by ring
        _ < A * h := mul_lt_mul_of_pos_right hRh hh0'
    rw [e5] at hT
    linarith only [hT, h8]
  have hkey : (lam δ * (P + δ * a)) ^ 2 - 2 * (lam δ * (γ + δ * 1)) ^ 2 +
      (lam δ * (R + δ * a)) ^ 2 = lam δ ^ 2 * T := by simp only [T]; ring
  rw [hkey] at key
  have hLh : 0 ≤ 2 * L * h ^ 2 := by positivity
  have hTneg : T < 0 := by linarith
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_neg hTneg] at key
  have h9 : 1 / 2 * -T ≤ lam δ ^ 2 * -T := mul_le_mul_of_nonneg_right hlam2' (by linarith)
  linarith

/-! ### Meagreness -/

/-- `Cond L` as a subset of `SN n`. -/
def CondS (n : ℕ) (L : ℝ) : Set (SN n) := Subtype.val ⁻¹' Cond L

lemma isClosed_CondS (L : ℝ) : IsClosed (CondS n L) :=
  (isClosed_Cond L).preimage continuous_subtype_val

lemma interior_CondS {L : ℝ} (hL : 0 ≤ L) : interior (CondS n L) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨y, hy, hyx, hyC⟩ := exists_not_Cond hL x.2 (interior_subset hx : x ∈ CondS n L) hε
  have hyb : (⟨y, hy⟩ : SN n) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]; exact hyx
  exact hyC (show (⟨y, hy⟩ : SN n) ∈ CondS n L from interior_subset (hball hyb))

lemma isNowhereDense_CondS {L : ℝ} (hL : 0 ≤ L) : IsNowhereDense (CondS n L) := by
  rw [IsNowhereDense, (isClosed_CondS L).closure_eq, interior_CondS hL]

/-- `ρ` has a `C²` profile vanishing at the walls. -/
def C2Dens (ρ : Pot → ℝ) : Prop :=
  ∃ K : ℝ → ℝ, ContDiff ℝ 2 K ∧ K 0 = 0 ∧ K 1 = 0 ∧ ρ = fun u => ∫ t, ext u t * K t ∂μ1

lemma mem_CondS_of_C2Dens (x : SN n) (h : C2Dens (rhoF x)) : ∃ L : ℕ, x ∈ CondS n L := by
  obtain ⟨K, hK, hK0, hK1, hρ⟩ := h
  obtain ⟨L, -, hL⟩ := D2_bound_of_C2 hK
  have hc := H10.continuous_clamp (h10_prim x.2.1)
  have he := eqOn_of_integral_pot (f := fun t => H10.clamp (prim (x : L2I)) t ^ 2) (g := K)
    (hc.pow 2) hK.continuous fun u => by
      rw [← show ∫ t, ext u t * prim (x : L2I) t ^ 2 ∂μ1 = ∫ t, ext u t * K t ∂μ1 from
        congrFun hρ u]
      exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
        simp only [H10.clamp_eq (Ioo_subset_Icc_self ht)]
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, prim (x : L2I) t ^ 2 = K t := by
    intro t ⟨h0, h1⟩
    rcases eq_or_lt_of_le h0 with rfl | h0
    · rw [prim_zero, hK0]; ring
    rcases eq_or_lt_of_le h1 with rfl | h1
    · rw [x.2.1, hK1]; ring
    have := he ⟨h0, h1⟩
    simp only [H10.clamp_eq (⟨h0.le, h1.le⟩ : t ∈ Icc (0 : ℝ) 1)] at this
    exact this
  refine ⟨⌈L⌉₊, fun t h h0 h1 h2 => ?_⟩
  have m1 : t + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
  have m2 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have m3 : t - h ∈ Icc (0 : ℝ) 1 := ⟨h1, by linarith⟩
  have e : D2 (fun s => prim (x : L2I) s ^ 2) t h = D2 K t h := by
    simp only [D2]; rw [heq _ m1, heq _ m2, heq _ m3]
  rw [e]
  exact (hL t h h0 h1 h2).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil L) (sq_nonneg h))

/-- **Densities with a `C²` profile are meagre** in the space of `N`-representable densities. -/
theorem meagre_C2Dens : IsMeagre {x : SN n | C2Dens (rhoF x)} :=
  (isMeagre_iUnion fun L : ℕ => (isNowhereDense_CondS (n := n) (Nat.cast_nonneg L)).isMeagre).mono
    fun x hx => mem_iUnion.2 (mem_CondS_of_C2Dens x hx)

/-! ### Kohn–Sham and one particle -/

variable {τ : Stat}

lemma C2Dens_of_ksRep {ρ : Pot → ℝ} (h : KSRep τ n ρ) : C2Dens ρ := by
  obtain ⟨vs, hvs⟩ := h
  cases τ
  · obtain ⟨φ, hφ, h1, hiff⟩ := ksDens_bos (n := n) vs
    refine ⟨fun t => (n + 1) * φ t ^ 2, contDiff_const.mul (hφ.1.1.pow 2), by simp [hφ.1.2.1],
      by simp [hφ.1.2.2], (hiff ρ).1 hvs⟩
  · obtain ⟨φ, lam, hφ, -, -, hiff⟩ := ksDens_fer (n := n) vs
    refine ⟨fun t => ∑ j, φ j t ^ 2, ContDiff.sum fun j _ => (hφ j).1.pow 2,
      by simp [fun j => (hφ j).2.1], by simp [fun j => (hφ j).2.2], (hiff ρ).1 hvs⟩

/-- **Kohn–Sham `v`-representable densities are meagre** in the complete metric space of
`N`-representable densities (bosons or fermions). -/
theorem ks_meagre : IsMeagre {x : SN n | KSRep τ n (rhoF x)} :=
  meagre_C2Dens.mono fun _ hx => C2Dens_of_ksRep hx

/-- **The non-Kohn–Sham-`v`-representable densities are residual, hence dense.** -/
theorem ks_nonrep_dense : Dense {x : SN n | ¬ KSRep τ n (rhoF x)} := by
  have : CompleteSpace (SN n) := (isClosed_SN n).completeSpace_coe
  exact dense_of_mem_residual (ks_meagre (τ := τ) (n := n))

/-- **One particle**: interacting `v`-representable densities are meagre. -/
theorem one_vrep_meagre {w : Cfg 0 → ℝ} {hw : Continuous w} :
    IsMeagre {x : SN 0 | PureVRep (settingW τ 0 w hw) (rhoF x)} :=
  meagre_C2Dens.mono fun x hx => by
    obtain ⟨g, q, hg, hρ⟩ := (pureVRep_one_iff_boxRep _).1 hx
    exact ⟨fun t => g t ^ 2, hg.1.1.pow 2, by simp [hg.1.2.1], by simp [hg.1.2.2], hρ⟩

end DFT.Continuum.Line
