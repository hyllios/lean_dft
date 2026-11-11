/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Strong

/-!
# The Pauli principle for one orbital

Let `Φ` be an antisymmetric state of `n + 1` particles on `[0, 1]` and `f` a normalised orbital,
`∫₀¹ f² = 1`. Projecting particle `k` on `f` gives `Pₖ Φ (x) = f(xₖ) Gₖ(x)`, with
`Gₖ(x) = ∫ f(t) Φ(x with xₖ = t) dt`. The occupation of `f` is at most one:

`Σₖ ⟨Φ, Pₖ Φ⟩ ≤ ⟨Φ, Φ⟩`.

Each `Pₖ` is a projection and `⟨Pₖ Φ, Pₗ Φ⟩ = 0` for `k ≠ l`, because the double projection
`∫∫ f(t) f(s) Φ(x with xₖ = t, xₗ = s)` changes sign when `s` and `t` are exchanged. Hence
`‖Σₖ Pₖ Φ‖² = Σₖ ⟨Φ, Pₖ Φ⟩` and `0 ≤ ‖Φ - Σₖ Pₖ Φ‖²` is the claim.

* `avgK`: the average of a function over coordinate `k`; `integral_avgK`: averaging over one
  coordinate does not change the integral over the cube.
* `pauli`: the bound.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ}

/-! ### Averaging over one coordinate -/

/-- The average of `H` over coordinate `k`: `∫₀¹ H(x with xₖ = t) dt`. -/
noncomputable def avgK (k : Fin (n + 1)) (H : Cfg n → ℝ) (x : Cfg n) : ℝ :=
  ∫ t, H (Function.update x k t) ∂μ1

lemma continuous_avgK (k : Fin (n + 1)) {H : Cfg n → ℝ} (hH : Continuous H) :
    Continuous (avgK k H) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (x : Cfg n) (t : ℝ) => H (Function.update x k t))
    (hH.comp (continuous_fst.update k continuous_snd)) 0 1
  refine h.congr fun x => ?_
  rw [integral_unit']; rfl

lemma avgK_update (k : Fin (n + 1)) (H : Cfg n → ℝ) (x : Cfg n) (s : ℝ) :
    avgK k H (Function.update x k s) = avgK k H x := by
  simp only [avgK, Function.update_idem]

lemma mu1_real_univ : μ1.real univ = 1 := by
  simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ]

/-- **Averaging over a coordinate does not change the integral.** -/
lemma integral_avgK (k : Fin (n + 1)) {H : Cfg n → ℝ} (hH : Continuous H) :
    ∫ x, avgK k H x ∂μN n = ∫ x, H x ∂μN n := by
  rw [integral_cube_insertNth (continuous_avgK k hH) k, integral_cube_insertNth hH k]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) fun y _ => ?_
  have e : ∀ s, avgK k H (Fin.insertNth k s y) = ∫ t, H (Fin.insertNth k t y) ∂μ1 := fun s => by
    simp only [avgK, Fin.update_insertNth]
  simp only [e]
  change ∫ _ , (∫ t, H (Fin.insertNth k t y) ∂μ1) ∂μ1 = _
  rw [integral_const, mu1_real_univ, one_smul]

/-! ### Integrability -/

lemma integrable_prod_mu1 {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) :
    Integrable (Function.uncurry F) (μ1.prod μ1) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact ((hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))

/-! ### The Pauli bound -/

section pauli

variable {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomF n) {f : ℝ → ℝ} (hf : Continuous f)

/-- `Gₖ(x) = ∫ f(t) Φ(x with xₖ = t) dt`. -/
noncomputable def gK (Φ : Cfg n → ℝ) (f : ℝ → ℝ) (k : Fin (n + 1)) : Cfg n → ℝ :=
  avgK k fun z => f (z k) * Φ z

lemma gK_apply (k : Fin (n + 1)) (x : Cfg n) :
    gK Φ f k x = ∫ t, f t * Φ (Function.update x k t) ∂μ1 := by
  simp only [gK, avgK, Function.update_self]

include hΦ hf

lemma continuous_gK (k : Fin (n + 1)) : Continuous (gK Φ f k) :=
  continuous_avgK k ((hf.comp (continuous_apply k)).mul hΦ.1.continuous)

omit hΦ hf in
lemma gK_update (k : Fin (n + 1)) (x : Cfg n) (s : ℝ) :
    gK Φ f k (Function.update x k s) = gK Φ f k x := avgK_update k _ x s

/-- The projection `Pₖ Φ (x) = f(xₖ) Gₖ(x)`. -/
noncomputable def pK (Φ : Cfg n → ℝ) (f : ℝ → ℝ) (k : Fin (n + 1)) (x : Cfg n) : ℝ :=
  f (x k) * gK Φ f k x

lemma continuous_pK (k : Fin (n + 1)) : Continuous (pK Φ f k) :=
  (hf.comp (continuous_apply k)).mul (continuous_gK hΦ hf k)

/-- `⟨Φ, Pₖ Φ⟩ = ∫ Gₖ²`. -/
lemma inner_pK (k : Fin (n + 1)) :
    ∫ x, Φ x * pK Φ f k x ∂μN n = ∫ x, gK Φ f k x * gK Φ f k x ∂μN n := by
  rw [← integral_avgK k (H := fun x => Φ x * pK Φ f k x)
    (hΦ.1.continuous.mul (continuous_pK hΦ hf k))]
  congr 1; funext x
  simp only [avgK, pK, Function.update_self, gK_update]
  rw [gK_apply k x, ← integral_mul_const]
  congr 1; funext t; ring

lemma pK_pK_self (hf1 : ∫ t, f t * f t ∂μ1 = 1) (k : Fin (n + 1)) :
    ∫ x, pK Φ f k x * pK Φ f k x ∂μN n = ∫ x, gK Φ f k x * gK Φ f k x ∂μN n := by
  rw [← integral_avgK k (H := fun x => pK Φ f k x * pK Φ f k x)
    ((continuous_pK hΦ hf k).mul (continuous_pK hΦ hf k))]
  congr 1; funext x
  simp only [avgK, pK, Function.update_self, gK_update]
  have : (fun t => f t * gK Φ f k x * (f t * gK Φ f k x)) =
      fun t => (gK Φ f k x * gK Φ f k x) * (f t * f t) := by funext t; ring
  rw [this, integral_const_mul, hf1, mul_one]

/-- The double projection on particles `k ≠ l` vanishes (antisymmetry). -/
lemma double_zero {k l : Fin (n + 1)} (hkl : k ≠ l) (x : Cfg n) :
    ∫ t, f t * gK Φ f l (Function.update x k t) ∂μ1 = 0 := by
  set u : ℝ → ℝ → Cfg n := fun t s => Function.update (Function.update x k t) l s
  set F : ℝ → ℝ → ℝ := fun t s => f t * f s * Φ (u t s)
  have hu : Continuous (Function.uncurry u) := by
    change Continuous fun p : ℝ × ℝ => Function.update (Function.update x k p.1) l p.2
    exact ((continuous_const : Continuous fun _ : ℝ × ℝ => x).update k continuous_fst).update l
      continuous_snd
  have hFc : Continuous (Function.uncurry F) :=
    ((hf.comp continuous_fst).mul (hf.comp continuous_snd)).mul (hΦ.1.continuous.comp hu)
  -- exchanging `s` and `t` flips the sign
  have hswap : ∀ t s, F s t = -F t s := by
    intro t s
    have hpm : pm (Equiv.swap k l) (u s t) = u t s := by
      funext i
      simp only [pm_apply, u]
      by_cases hik : i = k
      · subst hik
        simp [Function.update_of_ne hkl]
      · by_cases hil : i = l
        · subst hil
          simp [Function.update_of_ne hkl]
        · rw [Equiv.swap_apply_of_ne_of_ne hik hil]
          simp [Function.update_of_ne hik, Function.update_of_ne hil]
    have h := anti hΦ (Equiv.swap k l) (u s t)
    rw [hpm, sgn_swap hkl] at h
    simp only [F, h]; ring
  have hJ : ∫ t, f t * gK Φ f l (Function.update x k t) ∂μ1 = ∫ t, ∫ s, F t s ∂μ1 ∂μ1 := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [gK_apply, ← integral_const_mul, F, u]
    congr 1; funext s; ring
  have hsw := integral_integral_swap (integrable_prod_mu1 hFc)
  have hneg : ∫ s, ∫ t, F t s ∂μ1 ∂μ1 = -∫ t, ∫ s, F t s ∂μ1 ∂μ1 := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only
    rw [← integral_neg]
    congr 1; funext t
    rw [hswap s t]
  rw [hJ]
  linarith [hsw.trans hneg]

/-- `⟨Pₖ Φ, Pₗ Φ⟩ = 0` for `k ≠ l`. -/
lemma pK_pK_ne {k l : Fin (n + 1)} (hkl : k ≠ l) :
    ∫ x, pK Φ f k x * pK Φ f l x ∂μN n = 0 := by
  rw [← integral_avgK k (H := fun x => pK Φ f k x * pK Φ f l x)
    ((continuous_pK hΦ hf k).mul (continuous_pK hΦ hf l))]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
  simp only [avgK, pK, Function.update_self, gK_update, Function.update_of_ne hkl.symm,
    Pi.zero_apply]
  have : (fun t => f t * gK Φ f k x * (f (x l) * gK Φ f l (Function.update x k t))) =
      fun t => (gK Φ f k x * f (x l)) * (f t * gK Φ f l (Function.update x k t)) := by
    funext t; ring
  rw [this, integral_const_mul, double_zero hΦ hf hkl x, mul_zero]

/-- **The Pauli principle**: an orbital is occupied at most once,
`Σₖ ⟨Φ, Pₖ Φ⟩ ≤ ⟨Φ, Φ⟩`. -/
theorem pauli (hf1 : ∫ t, f t * f t ∂μ1 = 1) :
    ∑ k, ∫ x, Φ x * pK Φ f k x ∂μN n ≤ ∫ x, Φ x * Φ x ∂μN n := by
  have hc := hΦ.1.continuous
  have hP := continuous_pK hΦ hf
  have hA : Continuous fun x => ∑ k, pK Φ f k x := continuous_finsetSum _ fun k _ => hP k
  have h0 : 0 ≤ ∫ x, (Φ x - ∑ k, pK Φ f k x) ^ 2 ∂μN n :=
    integral_nonneg fun x => sq_nonneg _
  have hexp : (fun x => (Φ x - ∑ k, pK Φ f k x) ^ 2) = fun x =>
      (Φ x * Φ x - 2 * ∑ k, Φ x * pK Φ f k x) + ∑ k, ∑ l, pK Φ f k x * pK Φ f l x := by
    funext x
    rw [← Finset.mul_sum, ← Finset.sum_mul_sum]
    ring
  have i1 : Integrable (fun x => Φ x * Φ x) (μN n) := integrableN (hc.mul hc)
  have i2 : Integrable (fun x => ∑ k, Φ x * pK Φ f k x) (μN n) :=
    integrableN (continuous_finsetSum _ fun k _ => hc.mul (hP k))
  have i3 : Integrable (fun x => ∑ k, ∑ l, pK Φ f k x * pK Φ f l x) (μN n) :=
    integrableN (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
      (hP k).mul (hP l))
  have e1 : ∫ x, (Φ x * Φ x - 2 * ∑ k, Φ x * pK Φ f k x) +
      ∑ k, ∑ l, pK Φ f k x * pK Φ f l x ∂μN n =
      ∫ x, Φ x * Φ x ∂μN n - 2 * ∑ k, ∫ x, Φ x * pK Φ f k x ∂μN n +
        ∑ k, ∫ x, ∑ l, pK Φ f k x * pK Φ f l x ∂μN n := by
    rw [integral_add (f := fun x => Φ x * Φ x - 2 * ∑ k, Φ x * pK Φ f k x)
        (g := fun x => ∑ k, ∑ l, pK Φ f k x * pK Φ f l x) (i1.sub (i2.const_mul 2)) i3,
      integral_sub (f := fun x => Φ x * Φ x) (g := fun x => 2 * ∑ k, Φ x * pK Φ f k x)
        i1 (i2.const_mul 2), integral_const_mul,
      integral_finsetSum (f := fun k x => Φ x * pK Φ f k x) _
        fun k _ => integrableN (hc.mul (hP k)),
      integral_finsetSum (f := fun k x => ∑ l, pK Φ f k x * pK Φ f l x) _
        fun k _ => integrableN (continuous_finsetSum _ fun l _ => (hP k).mul (hP l))]
  rw [hexp, e1] at h0
  have hdiag : ∀ k, ∫ x, ∑ l, pK Φ f k x * pK Φ f l x ∂μN n = ∫ x, Φ x * pK Φ f k x ∂μN n := by
    intro k
    rw [integral_finsetSum (f := fun l x => pK Φ f k x * pK Φ f l x) _
        fun l _ => integrableN ((hP k).mul (hP l)),
      Finset.sum_eq_single k (fun l _ hlk => pK_pK_ne hΦ hf (Ne.symm hlk))
        (fun h => absurd (Finset.mem_univ k) h),
      pK_pK_self hΦ hf hf1, inner_pK hΦ hf]
  simp only [hdiag] at h0
  linarith

end pauli

end DFT.Continuum.Line
