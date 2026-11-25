/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import DFT.Continuum.Line.MeasurePotential.MeasureUCP

/-!
# Hohenberg–Kohn for measure potentials (one particle)

A ground state `g` determines its potential up to the obvious freedom: a constant, and atoms at the
walls (which `g` cannot see, since `g(0) = g(1) = 0`).

* `h10_of_lipschitz`, `cutF`: a Lipschitz cutoff, `0` outside `(a, 1 - a)` and `1` on
  `[2a, 1 - 2a]`.
* **`dense_mulP`**: if `g ∈ H¹₀` is positive on `(0, 1)`, the products `g φ`, `φ ∈ H¹₀`, are
  uniformly dense in `{h ∈ C([0, 1]) | h(0) = h(1) = 0}` (`φ = cutoff × Weierstrass polynomial
  for h/g`).
* **`hk_of_pos`**: if `g > 0` on `(0, 1)` solves `-g'' + ν g = E g` and `-g'' + ν' g = E' g`
  weakly, then `ν - ν' = (E - E') dx + a δ₀ + b δ₁`. This holds for any `ν, ν' ∈ C([0, 1])*`.
* `isGSM_gauge`: conversely, adding `C dx + a δ₀ + b δ₁` does not change the ground states.
* **`hk_meas`**: two measure potentials with a common ground state differ by `C dx + a δ₀ + b δ₁`;
  **`isGSM_iff_gauge`**: for a ground state `g` of `ν`, `g` is a ground state of `ν'` iff
  `ν' - ν` is such a gauge term.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

/-! ### A Lipschitz cutoff -/

lemma h10_of_lipschitz {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) (h0 : f 0 = 0)
    (h1 : f 1 = 0) : H10 f := by
  refine ⟨(hf.lipschitzOnWith).absolutelyContinuousOnInterval, h0, h1, ?_⟩
  refine Integrable.of_bound ((measurable_deriv f).pow_const 2).aestronglyMeasurable
    ((K : ℝ) ^ 2) (ae_of_all _ fun t => ?_)
  have hd : ‖deriv f t‖ ≤ K := norm_deriv_le_of_lipschitz hf
  rw [Real.norm_eq_abs] at hd
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hd 2

/-- The cutoff `max 0 (min 1 (min ((t - a)/a) ((1 - a - t)/a)))`. -/
noncomputable def cutF (a t : ℝ) : ℝ := max 0 (min 1 (min ((t - a) / a) ((1 - a - t) / a)))

lemma lipschitz_cutF {a : ℝ} (ha : 0 < a) : LipschitzWith ⟨1 / a, by positivity⟩ (cutF a) := by
  have hl1 : LipschitzWith ⟨1 / a, by positivity⟩ fun t : ℝ => (t - a) / a :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, ← sub_div, show x - a - (y - a) = x - y by ring, abs_div,
        abs_of_pos ha]
      rw [div_eq_inv_mul]; change a⁻¹ * |x - y| ≤ (1 / a) * |x - y|; rw [one_div]
  have hl2 : LipschitzWith ⟨1 / a, by positivity⟩ fun t : ℝ => (1 - a - t) / a :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, ← sub_div, show 1 - a - x - (1 - a - y) = -(x - y) by ring,
        abs_div, abs_neg, abs_of_pos ha]
      rw [div_eq_inv_mul]; change a⁻¹ * |x - y| ≤ (1 / a) * |x - y|; rw [one_div]
  have h := ((hl1.min hl2).const_min 1).const_max 0
  exact h.weaken (max_le le_rfl le_rfl)

lemma cutF_nonneg (a t : ℝ) : 0 ≤ cutF a t := le_max_left _ _

lemma cutF_le_one (a t : ℝ) : cutF a t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma cutF_out {a t : ℝ} (ha : 0 < a) (ht : t ≤ a ∨ 1 - a ≤ t) : cutF a t = 0 := by
  refine max_eq_left (min_le_of_right_le ?_)
  rcases ht with h | h
  · exact min_le_of_left_le (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
  · exact min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)

lemma cutF_mid {a t : ℝ} (ha : 0 < a) (h1 : 2 * a ≤ t) (h2 : t ≤ 1 - 2 * a) : cutF a t = 1 := by
  have e1 : 1 ≤ (t - a) / a := by rw [le_div_iff₀ ha]; linarith
  have e2 : 1 ≤ (1 - a - t) / a := by rw [le_div_iff₀ ha]; linarith
  rw [cutF, min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

lemma h10_cutF {a : ℝ} (ha : 0 < a) : H10 (cutF a) :=
  h10_of_lipschitz (lipschitz_cutF ha) (cutF_out ha (Or.inl ha.le))
    (cutF_out ha (Or.inr (by linarith)))

/-! ### Density of `g · H¹₀` -/

/-- **The products `g φ`, `φ ∈ H¹₀`, are dense** in the continuous functions vanishing at the
walls, when `g ∈ H¹₀` is positive on `(0, 1)`. -/
theorem dense_mulP {g : ℝ → ℝ} (hg : H10 g) (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) (h : Pot)
    (h0 : h ⟨0, le_rfl, zero_le_one⟩ = 0) (h1 : h ⟨1, zero_le_one, le_rfl⟩ = 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ φ : ℝ → ℝ, ∃ hφ : H10 φ, ‖mulP hg hφ - h‖ ≤ 2 * ε := by
  set H := Box.ext h
  have hHc : Continuous H := continuous_ext h
  have hH0 : H 0 = 0 := by
    simp only [H, Box.ext]; rw [projIcc_left]; exact h0
  have hH1 : H 1 = 0 := by
    simp only [H, Box.ext]; rw [projIcc_right]; exact h1
  -- `|h| < ε` near the walls
  obtain ⟨δ0, hδ0, hb0⟩ := Metric.continuousAt_iff.1 hHc.continuousAt ε hε
  obtain ⟨δ1, hδ1, hb1⟩ := Metric.continuousAt_iff.1 (hHc.continuousAt (x := 1)) ε hε
  set a := min (1 / 4) (min δ0 δ1) / 3
  have ha : 0 < a := by positivity
  have ha4 : a ≤ 1 / 12 := by
    have := min_le_left (1 / 4 : ℝ) (min δ0 δ1); simp only [a]; linarith
  have ha0 : 2 * a < δ0 := by
    have := (min_le_right (1 / 4 : ℝ) (min δ0 δ1)).trans (min_le_left δ0 δ1)
    have : 0 < min (1 / 4 : ℝ) (min δ0 δ1) := by positivity
    simp only [a]; linarith
  have ha1 : 2 * a < δ1 := by
    have := (min_le_right (1 / 4 : ℝ) (min δ0 δ1)).trans (min_le_right δ0 δ1)
    have : 0 < min (1 / 4 : ℝ) (min δ0 δ1) := by positivity
    simp only [a]; linarith
  have hsmall : ∀ t ∈ Icc (0 : ℝ) 1, (t ≤ 2 * a ∨ 1 - 2 * a ≤ t) → |H t| < ε := fun t ht hor => by
    rcases hor with h' | h'
    · have := hb0 (x := t) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith)
      rwa [Real.dist_eq, hH0, sub_zero] at this
    · have := hb1 (x := t) (by
        rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.2])]; linarith)
      rwa [Real.dist_eq, hH1, sub_zero] at this
  -- `g` on `[a, 1 - a]`
  have hIcc : Icc a (1 - a) ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgc : ContinuousOn g (Icc a (1 - a)) := hg.continuousOn.mono (hIcc.trans Ioo_subset_Icc_self)
  have hk : ContinuousOn (fun t => H t / g t) (Icc a (1 - a)) :=
    hHc.continuousOn.div hgc fun t ht => (hpos t (hIcc ht)).ne'
  obtain ⟨G, hG⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hg.continuousOn
  set G' := max G 0
  set η := ε / (G' + 1)
  have hη : 0 < η := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a (1 - a) _ hk η hη
  -- the approximant
  have hφ : H10 fun t => cutF a t * p.eval t := (h10_cutF ha).mul_C1
    (lipschitz_cutF ha).continuous (by simpa using p.contDiff_aeval (𝕜 := ℝ) 1)
  refine ⟨_, hφ, (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_⟩
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.2
  have hHt : h t = H t := by simp [H, Box.ext, projIcc_of_mem _ htI]
  simp only [ContinuousMap.sub_apply, mulP_apply, Real.norm_eq_abs, hHt]
  have hgt : |g t| ≤ G' := (by simpa using hG t htI : |g t| ≤ G).trans (le_max_left _ _)
  by_cases hout : (t : ℝ) ≤ a ∨ 1 - a ≤ t
  · rw [cutF_out ha hout, zero_mul, mul_zero, zero_sub, abs_neg]
    refine (hsmall t htI ?_).le.trans (by linarith)
    rcases hout with h' | h'
    · left; linarith
    · right; linarith
  · push Not at hout
    have htk : (t : ℝ) ∈ Icc a (1 - a) := ⟨hout.1.le, hout.2.le⟩
    have hg0 : g t ≠ 0 := (hpos t (hIcc htk)).ne'
    set χ := cutF a t
    have e : g t * (χ * p.eval (t : ℝ)) - H t =
        g t * χ * (p.eval (t : ℝ) - H t / g t) + (χ - 1) * H t := by
      field_simp; ring
    rw [e]
    have b1 : |g t * χ * (p.eval (t : ℝ) - H t / g t)| ≤ ε := by
      rw [abs_mul, abs_mul, abs_of_nonneg (cutF_nonneg a t)]
      have hp' := (hp t htk).le
      calc |g t| * χ * |p.eval (t : ℝ) - H t / g t| ≤ G' * 1 * η := by
            gcongr
            · exact cutF_nonneg a t
            · exact cutF_le_one a t
      _ ≤ ε := by
            simp only [η, mul_one]
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith [le_max_right G 0]
    have b2 : |(χ - 1) * H t| ≤ ε := by
      by_cases hmid : 2 * a ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 - 2 * a
      · rw [show χ = 1 from cutF_mid ha hmid.1 hmid.2]; simp [hε.le]
      · rw [not_and_or, not_le, not_le] at hmid
        rw [abs_mul]
        have hχ : |χ - 1| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [cutF_nonneg a t, cutF_le_one a t]
        have := hsmall t htI (hmid.elim (fun h' => Or.inl h'.le) fun h' => Or.inr h'.le)
        nlinarith [abs_nonneg (χ - 1), abs_nonneg (H t)]
    calc _ ≤ |g t * χ * (p.eval (t : ℝ) - H t / g t)| + |(χ - 1) * H t| := abs_add_le _ _
      _ ≤ 2 * ε := by linarith

/-! ### Hohenberg–Kohn -/

/-- The linear function `t`, and `1 - t`, on `[0, 1]`. -/
noncomputable def linP (b : ℝ) : Pot := ⟨fun t => b + (1 - 2 * b) * (t : ℝ), by fun_prop⟩

lemma eq_zero_of_dense {D : PotM} {g : ℝ → ℝ} (hg : H10 g)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t) (hD : ∀ φ (hφ : H10 φ), D (mulP hg hφ) = 0) (h : Pot)
    (h0 : h ⟨0, le_rfl, zero_le_one⟩ = 0) (h1 : h ⟨1, zero_le_one, le_rfl⟩ = 0) : D h = 0 := by
  by_contra hne
  set r := |D h|
  have hr : 0 < r := abs_pos.2 hne
  set ε := r / (4 * (‖D‖ + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨φ, hφ, hle⟩ := dense_mulP hg hpos h h0 h1 hε
  have := D.le_opNorm (mulP hg hφ - h)
  rw [map_sub, hD φ hφ, zero_sub, norm_neg, Real.norm_eq_abs] at this
  have h2 : ‖D‖ * ‖mulP hg hφ - h‖ ≤ ‖D‖ * (2 * ε) := mul_le_mul_of_nonneg_left hle (norm_nonneg D)
  have h3 : ‖D‖ * (2 * ε) < r := by
    simp only [ε]
    rw [show ‖D‖ * (2 * (r / (4 * (‖D‖ + 1)))) = r * (‖D‖ / (2 * (‖D‖ + 1))) by
      field_simp; ring]
    have : ‖D‖ / (2 * (‖D‖ + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [norm_nonneg D]
    nlinarith
  linarith

/-- **Hohenberg–Kohn**: if `g ∈ H¹₀`, positive on `(0, 1)`, solves `-g'' + ν g = E g` and
`-g'' + ν' g = E' g` weakly, then `ν - ν' = (E - E') dx + a δ₀ + b δ₁`. -/
theorem hk_of_pos {ν ν' : PotM} {g : ℝ → ℝ} (hg : H10 g) (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t)
    {E E' : ℝ}
    (hE : ∀ φ (hφ : H10 φ), ∫ t, deriv g t * deriv φ t ∂μ1 + ν (mulP hg hφ) =
      E * ∫ t, g t * φ t ∂μ1)
    (hE' : ∀ φ (hφ : H10 φ), ∫ t, deriv g t * deriv φ t ∂μ1 + ν' (mulP hg hφ) =
      E' * ∫ t, g t * φ t ∂μ1) :
    ∃ a b : ℝ, ν - ν' = (E - E') • intCLM μ1 + a • deltaM ⟨0, le_rfl, zero_le_one⟩ +
      b • deltaM ⟨1, zero_le_one, le_rfl⟩ := by
  set D := ν - ν' - (E - E') • intCLM μ1
  have hD : ∀ φ (hφ : H10 φ), D (mulP hg hφ) = 0 := fun φ hφ => by
    have := hE φ hφ
    have := hE' φ hφ
    simp only [D, sub_apply, smul_apply, smul_eq_mul, intCLM_mulP μ1]
    linarith
  set z : Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  set o : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  refine ⟨D (linP 1), D (linP 0), ?_⟩
  have key : ∀ h : Pot, D h = h z * D (linP 1) + h o * D (linP 0) := fun h => by
    set h' := h - h z • linP 1 - h o • linP 0
    have hz : h' z = 0 := by simp [h', linP, z]
    have ho : h' o = 0 := by simp [h', linP, o]; norm_num
    have := eq_zero_of_dense hg hpos hD h' hz ho
    simp only [h', map_sub, map_smul, smul_eq_mul] at this
    linarith
  ext h
  have hDh : D h = ν h - ν' h - (E - E') * intCLM μ1 h := by simp [D]
  rw [key h] at hDh
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, deltaM,
    ContinuousMap.evalCLM_apply]
  linarith

/-- **Gauge invariance**: adding `C dx + a δ₀ + b δ₁` does not change the ground states. -/
theorem isGSM_gauge {ν : PotM} {ψ : ℝ → ℝ} (C a b : ℝ) :
    IsGSM (ν + C • intCLM μ1 + a • deltaM ⟨0, le_rfl, zero_le_one⟩ +
      b • deltaM ⟨1, zero_le_one, le_rfl⟩) ψ ↔ IsGSM ν ψ := by
  have hQ : ∀ {φ : ℝ → ℝ} (hφ : H10 φ), QM (ν + C • intCLM μ1 +
      a • deltaM ⟨0, le_rfl, zero_le_one⟩ + b • deltaM ⟨1, zero_le_one, le_rfl⟩) hφ =
      QM ν hφ + C * ∫ t, φ t ^ 2 ∂μ1 := fun {φ} hφ => by
    have hs : intCLM μ1 (sqP hφ) = ∫ t, φ t ^ 2 ∂μ1 := by
      rw [← mulP_self, intCLM_mulP]; simp_rw [sq]
    simp only [QM, add_apply, smul_apply, smul_eq_mul, deltaM, ContinuousMap.evalCLM_apply,
      sqP_apply, hs, hφ.2.1, hφ.2.2.1]
    ring
  constructor
  · rintro ⟨hψ, hn, hmin⟩
    refine ⟨hψ, hn, fun φ hφ => ?_⟩
    have := hmin φ hφ
    rw [hQ, hQ] at this
    nlinarith
  · rintro ⟨hψ, hn, hmin⟩
    refine ⟨hψ, hn, fun φ hφ => ?_⟩
    rw [hQ, hQ]
    nlinarith [hmin φ hφ]

/-- A ground state of a measure potential, normalised and made positive. -/
lemma exists_pos_gs {μp μm : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] {ν' : PotM} {ψ : ℝ → ℝ}
    (h : IsGSM (nuOf μp μm) ψ) (h' : IsGSM ν' ψ) :
    ∃ g : ℝ → ℝ, ∃ _ : H10 g, IsGSM (nuOf μp μm) g ∧ IsGSM ν' g ∧
      ∫ t, g t ^ 2 ∂μ1 = 1 ∧ ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t := by
  have hψ := h.1
  have hpos := h.2.1
  set m := ∫ t, ψ t ^ 2 ∂μ1
  set c := 1 / √m
  have hc2 : c ^ 2 = 1 / m := by rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
  have hc : c ≠ 0 := by
    intro h0; rw [h0] at hc2; have : (0 : ℝ) < 1 / m := by positivity
    simp at hc2; linarith
  have hn1 : ∫ t, (c * ψ t) ^ 2 ∂μ1 = 1 := by rw [norm2_smul, hc2, one_div_mul_cancel hpos.ne']
  rcases gs_pos_or_neg (h.const_mul hc) with hp | hn
  · exact ⟨_, hψ.const_mul c, h.const_mul hc, h'.const_mul hc, hn1, hp⟩
  · refine ⟨_, hψ.const_mul (-c), h.const_mul (neg_ne_zero.2 hc), h'.const_mul (neg_ne_zero.2 hc),
      by rw [norm2_smul, neg_sq, ← norm2_smul, hn1], fun t ht => ?_⟩
    have := hn t ht
    simp only [neg_mul] at this ⊢
    linarith

/-- **Hohenberg–Kohn for measure potentials**: two measure potentials with a common ground state
differ by `C dx + a δ₀ + b δ₁`. -/
theorem hk_meas {μp μm μp' μm' : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] [IsMeas01 μp']
    [IsMeas01 μm'] {ψ : ℝ → ℝ} (h : IsGSM (nuOf μp μm) ψ) (h' : IsGSM (nuOf μp' μm') ψ) :
    ∃ C a b : ℝ, nuOf μp μm - nuOf μp' μm' = C • intCLM μ1 +
      a • deltaM ⟨0, le_rfl, zero_le_one⟩ + b • deltaM ⟨1, zero_le_one, le_rfl⟩ := by
  obtain ⟨g, hg, hgs, hgs', hn, hpos⟩ := exists_pos_gs h h'
  obtain ⟨a, b, hab⟩ := hk_of_pos hg hpos
    (fun φ hφ => euler_lagrange hg hn (QM_eq_EM_of_isGSM hgs hn hg) hφ)
    (fun φ hφ => euler_lagrange hg hn (QM_eq_EM_of_isGSM hgs' hn hg) hφ)
  exact ⟨_, a, b, hab⟩

/-- **The potential is determined by the ground state up to gauge**: for a ground state `ψ` of a
measure potential `ν`, `ψ` is a ground state of another measure potential `ν'` iff
`ν' = ν + C dx + a δ₀ + b δ₁`. -/
theorem isGSM_iff_gauge {μp μm μp' μm' : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] [IsMeas01 μp']
    [IsMeas01 μm'] {ψ : ℝ → ℝ} (h : IsGSM (nuOf μp μm) ψ) :
    IsGSM (nuOf μp' μm') ψ ↔ ∃ C a b : ℝ, nuOf μp' μm' = nuOf μp μm + C • intCLM μ1 +
      a • deltaM ⟨0, le_rfl, zero_le_one⟩ + b • deltaM ⟨1, zero_le_one, le_rfl⟩ := by
  constructor
  · intro h'
    obtain ⟨C, a, b, hab⟩ := hk_meas h h'
    refine ⟨-C, -a, -b, ?_⟩
    have : nuOf μp' μm' = nuOf μp μm - (C • intCLM μ1 + a • deltaM ⟨0, le_rfl, zero_le_one⟩ +
        b • deltaM ⟨1, zero_le_one, le_rfl⟩) := by rw [← hab]; abel
    rw [this]; module
  · rintro ⟨C, a, b, hν⟩
    rw [hν]; exact (isGSM_gauge C a b).2 h

end DFT.Continuum.Line
