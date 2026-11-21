/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Mixed

/-!
# Cosine coefficients of smooth functions on the cube

For a smooth function `F` on `ℝ^d`, the cosine coefficients on the cube decay like a product:

  `|∫_{[0,1]^d} F(y) Π_j cos(π l_j y_j) dy| ≤ C Π_j (1 + l_j)^{-2}`.

In one variable this is two integrations by parts (the boundary terms of the second one do not
vanish, which is why the decay is only `l^{-2}`). In `d` variables it is an induction: split off
the first coordinate, integrate by parts in it under the integral over the others, and bound the
three resulting coefficient functions by the induction hypothesis, uniformly in a compact family
of parameters.

* `integral_mul_cos_ibp`: the one-dimensional identity.
* `cosP`, `rho`: the cosine products and the weight `ρ(k) = (k + 1)^{-2}`.
* `coef_decay`: **the decay bound**, uniform over a compact set of parameters.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real
open scoped ENNReal ContDiff

/-! ### Integration by parts in one variable -/

/-- `∫₀¹ g cos(πlt) = ((-1)^l g'(1) - g'(0) - ∫₀¹ g'' cos(πlt)) / (πl)²` for `l ≥ 1`. -/
lemma integral_mul_cos_ibp {g g1 g2 : ℝ → ℝ} (h1 : ∀ t, HasDerivAt g (g1 t) t)
    (h2 : ∀ t, HasDerivAt g1 (g2 t) t) (hg2 : Continuous g2) {l : ℕ} (hl : 0 < l) :
    ∫ t, g t * Real.cos (π * l * t) ∂μ1 =
      ((-1) ^ l * g1 1 - g1 0 - ∫ t, g2 t * Real.cos (π * l * t) ∂μ1) / (π * l) ^ 2 := by
  have hc : (π * l : ℝ) ≠ 0 := by positivity
  set c : ℝ := π * l with hcdef
  have hg1c : Continuous g1 := continuous_iff_continuousAt.2 fun t => (h2 t).continuousAt
  have hsin : ∀ t, HasDerivAt (fun s => Real.sin (c * s) / c) (Real.cos (c * t)) t := fun t => by
    have h := ((Real.hasDerivAt_sin (c * t)).comp t ((hasDerivAt_id t).const_mul c)).div_const c
    have e : Real.cos (c * t) * (c * 1) / c = Real.cos (c * t) := by field_simp
    exact h.congr_deriv e
  have hcos : ∀ t, HasDerivAt (fun s => -(Real.cos (c * s) / c)) (Real.sin (c * t)) t := fun t => by
    have h := (((Real.hasDerivAt_cos (c * t)).comp t ((hasDerivAt_id t).const_mul c)).div_const
      c).neg
    have e : -(-Real.sin (c * t) * (c * 1) / c) = Real.sin (c * t) := by field_simp
    exact h.congr_deriv e
  have e1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := g)
    (u' := g1) (v := fun s => Real.sin (c * s) / c) (v' := fun s => Real.cos (c * s))
    (fun t _ => h1 t) (fun t _ => hsin t) (hg1c.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s => Real.cos (c * s)).intervalIntegrable _ _)
  have e2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := g1)
    (u' := g2) (v := fun s => -(Real.cos (c * s) / c)) (v' := fun s => Real.sin (c * s))
    (fun t _ => h2 t) (fun t _ => hcos t) (hg2.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s => Real.sin (c * s)).intervalIntegrable _ _)
  have i1 : ∫ x in (0 : ℝ)..1, g1 x * (Real.sin (c * x) / c) =
      (∫ x in (0 : ℝ)..1, g1 x * Real.sin (c * x)) / c := by
    rw [← intervalIntegral.integral_div]; congr 1; funext x; ring
  have i2 : ∫ x in (0 : ℝ)..1, g2 x * -(Real.cos (c * x) / c) =
      -(∫ x in (0 : ℝ)..1, g2 x * Real.cos (c * x)) / c := by
    rw [show (fun x => g2 x * -(Real.cos (c * x) / c)) =
      fun x => -(g2 x * Real.cos (c * x)) / c from funext fun x => by ring,
      intervalIntegral.integral_div, intervalIntegral.integral_neg]
  rw [i1] at e1
  rw [i2] at e2
  have hs1 : Real.sin (c * 1) = 0 := by rw [mul_one, hcdef, mul_comm]; exact Real.sin_nat_mul_pi l
  have hc1 : Real.cos (c * 1) = (-1) ^ l := by
    rw [mul_one, hcdef, mul_comm]; exact Real.cos_nat_mul_pi l
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, hs1, hc1] at e1 e2
  rw [integral_mu1_eq, integral_mu1_eq, e1, e2]
  field_simp
  ring

/-! ### Fubini on the cube -/

/-- Integrals over the cube as iterated integrals, first coordinate outside. -/
lemma integral_cons {d : ℕ} {G : (Fin (d + 1) → ℝ) → ℝ} (hG : Continuous G) :
    ∫ x, G x ∂piM (d + 1) = ∫ t, ∫ y, G (Fin.cons t y) ∂piM d ∂μ1 ∧
      Integrable (fun p : ℝ × (Fin d → ℝ) => G (Fin.cons p.1 p.2)) (μ1.prod (piM d)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have hmp : MeasurePreserving e (piM (d + 1)) (μ1.prod (piM d)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ1) 0
  have hsymm : ∀ p : ℝ × (Fin d → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hi : Integrable (fun p : ℝ × (Fin d → ℝ) => G (e.symm p)) (μ1.prod (piM d)) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 (integrable_piM hG)
  simp only [hsymm] at hi
  refine ⟨?_, hi⟩
  rw [← hmp.symm.integral_comp' (f := e.symm) (g := G)]
  simp only [hsymm]
  exact integral_prod _ hi

/-- Exchanging the two integrals over the cube. -/
lemma integral_swap_cons {d : ℕ} {Φ : ℝ → (Fin d → ℝ) → ℝ}
    (hΦ : Continuous fun p : ℝ × (Fin d → ℝ) => Φ p.1 p.2) :
    ∫ t, ∫ y, Φ t y ∂piM d ∂μ1 = ∫ y, ∫ t, Φ t y ∂μ1 ∂piM d := by
  have hp : Continuous fun x : Fin (d + 1) → ℝ => (x 0, Fin.tail x) :=
    (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  have hG : Continuous fun x : Fin (d + 1) → ℝ => Φ (x 0) (Fin.tail x) := hΦ.comp hp
  have hi := (integral_cons hG).2
  simp only [Fin.cons_zero, Fin.tail_cons] at hi
  exact integral_integral_swap hi

/-- A parametric integral over `(0, 1)` is continuous. -/
lemma continuous_param1 {d : ℕ} {G : (Fin d → ℝ) → ℝ → ℝ}
    (hG : Continuous fun p : (Fin d → ℝ) × ℝ => G p.1 p.2) :
    Continuous fun y => ∫ t, G y t ∂μ1 := by
  rw [mu1_eq_Icc]
  exact continuous_parametric_integral_of_continuous hG isCompact_Icc

lemma abs_integral_mu1_le {f : ℝ → ℝ} {C : ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ C) :
    |∫ t, f t ∂μ1| ≤ C := by
  have hle := norm_integral_le_of_norm_le_const (μ := μ1) (f := f) (C := C)
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => h t (Ioo_subset_Icc_self ht))
  simpa [Real.volume_Ioo] using hle

/-! ### Smooth families -/

lemma contDiff_cons {d : ℕ} :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_fst : ContDiff ℝ ∞ fun p : ℝ × (Fin d → ℝ) => p.1)
  · simpa using contDiff_pi.1 (contDiff_snd : ContDiff ℝ ∞
      fun p : ℝ × (Fin d → ℝ) => p.2) j

/-- The partial derivative in a scalar variable of a smooth family is a smooth family. -/
lemma contDiff_deriv_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ fun p : E × ℝ => f p.1 p.2) :
    ContDiff ℝ ∞ fun p : E × ℝ => deriv (f p.1) p.2 := by
  have hf' : ContDiff ℝ ∞ fun q : (E × ℝ) × ℝ => f q.1.1 q.2 :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have h := ContDiff.fderiv (n := ∞) (m := ∞) (f := fun (p : E × ℝ) (s : ℝ) => f p.1 s)
    (g := fun p => p.2) hf' contDiff_snd (by simp)
  exact h.clm_apply contDiff_const

lemma hasDerivAt_of_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ fun p : E × ℝ => f p.1 p.2) (q : E) (t : ℝ) :
    HasDerivAt (f q) (deriv (f q) t) t := by
  have h : ContDiff ℝ ∞ (f q) := hf.comp (contDiff_const.prodMk contDiff_id)
  exact ((h.differentiable (by simp)) t).hasDerivAt

/-! ### The decay of cosine coefficients -/

/-- The cosine product `Π_j cos(π l_j y_j)`. -/
noncomputable def cosP {d : ℕ} (l : Fin d → ℕ) (y : Fin d → ℝ) : ℝ :=
  ∏ j, Real.cos (π * l j * y j)

lemma cosP_cons {d : ℕ} (k : ℕ) (l : Fin d → ℕ) (t : ℝ) (y : Fin d → ℝ) :
    cosP (Fin.cons k l : Fin (d + 1) → ℕ) (Fin.cons t y) = Real.cos (π * k * t) * cosP l y := by
  simp only [cosP, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma continuous_cosP {d : ℕ} (l : Fin d → ℕ) : Continuous (cosP l) :=
  continuous_finsetProd _ fun j _ => by fun_prop

/-- The weight `ρ(k) = (k + 1)^{-2}`. -/
noncomputable def rho (k : ℕ) : ℝ := (((k : ℝ) + 1) ^ 2)⁻¹

lemma rho_pos (k : ℕ) : 0 < rho k := by unfold rho; positivity

lemma inv_pi_sq_le_rho {k : ℕ} (hk : 0 < k) : ((π * k) ^ 2)⁻¹ ≤ rho k := by
  unfold rho
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 2)
  nlinarith [Real.pi_gt_three]

/-- **Decay of cosine coefficients**: for a smooth family `F(z, ·)` and `z` in a compact set,
`|∫ F(z, y) Π_j cos(π l_j y_j) dy| ≤ C Π_j (1 + l_j)^{-2}`. -/
theorem coef_decay : ∀ (d : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E},
    IsCompact S → ∀ {F : E → (Fin d → ℝ) → ℝ},
    ContDiff ℝ ∞ (fun p : E × (Fin d → ℝ) => F p.1 p.2) →
    ∃ C, 0 ≤ C ∧ ∀ z ∈ S, ∀ l : Fin d → ℕ,
      |∫ y, F z y * cosP l y ∂piM d| ≤ C * ∏ j, rho (l j) := by
  intro d
  induction d with
  | zero =>
    intro E _ _ S hS F hF
    have hc : ContinuousOn (fun z => F z isEmptyElim) S :=
      (hF.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc
    refine ⟨max C 0, le_max_right _ _, fun z hz l => ?_⟩
    have hpi : piM 0 = Measure.dirac (isEmptyElim : Fin 0 → ℝ) := Measure.pi_of_empty _ _
    rw [hpi, integral_dirac]
    simp only [cosP, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact (Real.norm_eq_abs _ ▸ hC z hz).trans (le_max_left _ _)
  | succ d ih =>
    intro E _ _ S hS F hF
    -- the slices and their derivatives in the first coordinate
    set f : E × (Fin d → ℝ) → ℝ → ℝ := fun q t => F q.1 (Fin.cons t q.2) with hfdef
    have hf : ContDiff ℝ ∞ fun p : (E × (Fin d → ℝ)) × ℝ => f p.1 p.2 :=
      hF.comp ((contDiff_fst.comp contDiff_fst).prodMk (contDiff_cons.comp
        (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))))
    have hf1 := contDiff_deriv_snd hf
    set f1 : E × (Fin d → ℝ) → ℝ → ℝ := fun q t => deriv (f q) t with hf1def
    have hf2 := contDiff_deriv_snd (f := f1) hf1
    set f2 : E × (Fin d → ℝ) → ℝ → ℝ := fun q t => deriv (f1 q) t with hf2def
    -- as families over the parameters `(z, t)`
    have hfam : ∀ {g : E × (Fin d → ℝ) → ℝ → ℝ},
        ContDiff ℝ ∞ (fun p : (E × (Fin d → ℝ)) × ℝ => g p.1 p.2) →
        ContDiff ℝ ∞ (fun p : (E × ℝ) × (Fin d → ℝ) => g (p.1.1, p.2) p.1.2) := fun hg =>
      hg.comp (((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).prodMk
        (contDiff_snd.comp contDiff_fst))
    have hS' : IsCompact (S ×ˢ Icc (0 : ℝ) 1) := hS.prod isCompact_Icc
    obtain ⟨C0, hC0, h0⟩ := ih (F := fun q y => f (q.1, y) q.2) hS' (hfam hf)
    obtain ⟨C1, hC1, h1⟩ := ih (F := fun q y => f1 (q.1, y) q.2) hS' (hfam hf1)
    obtain ⟨C2, hC2, h2⟩ := ih (F := fun q y => f2 (q.1, y) q.2) hS' (hfam hf2)
    refine ⟨max C0 (2 * C1 + C2), by positivity, fun z hz l => ?_⟩
    obtain ⟨k, l', rfl⟩ : ∃ k l', l = (Fin.cons k l' : Fin (d + 1) → ℕ) :=
      ⟨l 0, Fin.tail l, (Fin.cons_self_tail l).symm⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    set P := ∏ j, rho (l' j)
    have hP : 0 ≤ P := Finset.prod_nonneg fun j _ => (rho_pos _).le
    have hcont : ∀ {g : E × (Fin d → ℝ) → ℝ → ℝ},
        ContDiff ℝ ∞ (fun p : (E × (Fin d → ℝ)) × ℝ => g p.1 p.2) →
        Continuous fun p : ℝ × (Fin d → ℝ) => g (z, p.2) p.1 := fun hg =>
      hg.continuous.comp ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)
    -- the coefficient as an iterated integral
    have hG : Continuous fun x : Fin (d + 1) → ℝ => F z x * cosP (Fin.cons k l') x :=
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).mul (continuous_cosP _)
    rw [(integral_cons hG).1]
    simp only [cosP_cons]
    have hin : ∀ t, ∫ y, F z (Fin.cons t y) * (Real.cos (π * k * t) * cosP l' y) ∂piM d =
        Real.cos (π * k * t) * ∫ y, f (z, y) t * cosP l' y ∂piM d := fun t => by
      rw [← integral_const_mul]; congr 1; funext y; simp only [hfdef]; ring
    simp only [hin]
    -- a bound for `∫ t, cos(πkt) ∫ y, g(z,y,t) cosP l' y`
    have hbd : ∀ {g : E × (Fin d → ℝ) → ℝ → ℝ} {C : ℝ},
        (∀ q ∈ S ×ˢ Icc (0 : ℝ) 1, ∀ l : Fin d → ℕ,
          |∫ y, g (q.1, y) q.2 * cosP l y ∂piM d| ≤ C * ∏ j, rho (l j)) →
        |∫ t, Real.cos (π * k * t) * ∫ y, g (z, y) t * cosP l' y ∂piM d ∂μ1| ≤ C * P := by
      intro g C hg
      refine abs_integral_mu1_le fun t ht => ?_
      rw [abs_mul]
      calc |Real.cos (π * k * t)| * |∫ y, g (z, y) t * cosP l' y ∂piM d| ≤ 1 * (C * P) :=
            mul_le_mul (Real.abs_cos_le_one _) (hg (z, t) ⟨hz, ht⟩ l') (abs_nonneg _) zero_le_one
        _ = C * P := one_mul _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have h := hbd (g := f) (C := C0) h0
      have hr : rho 0 = 1 := by simp [rho]
      rw [hr, one_mul]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hP)
    · -- integrate by parts in the first coordinate
      have hsw : ∀ {g : E × (Fin d → ℝ) → ℝ → ℝ},
          ContDiff ℝ ∞ (fun p : (E × (Fin d → ℝ)) × ℝ => g p.1 p.2) →
          ∫ t, Real.cos (π * k * t) * ∫ y, g (z, y) t * cosP l' y ∂piM d ∂μ1 =
            ∫ y, cosP l' y * ∫ t, g (z, y) t * Real.cos (π * k * t) ∂μ1 ∂piM d := by
        intro g hg
        have e1 : ∀ t, Real.cos (π * k * t) * ∫ y, g (z, y) t * cosP l' y ∂piM d =
            ∫ y, g (z, y) t * Real.cos (π * k * t) * cosP l' y ∂piM d := fun t => by
          rw [← integral_const_mul]; congr 1; funext y; ring
        have e2 : ∀ y, cosP l' y * ∫ t, g (z, y) t * Real.cos (π * k * t) ∂μ1 =
            ∫ t, g (z, y) t * Real.cos (π * k * t) * cosP l' y ∂μ1 := fun y => by
          rw [← integral_const_mul]; congr 1; funext t; ring
        simp only [e1, e2]
        exact integral_swap_cons (Φ := fun t y => g (z, y) t * Real.cos (π * k * t) * cosP l' y)
          (((hcont hg).mul (by fun_prop)).mul ((continuous_cosP l').comp continuous_snd))
      have hibp : ∀ y, ∫ t, f (z, y) t * Real.cos (π * k * t) ∂μ1 =
          ((-1) ^ k * f1 (z, y) 1 - f1 (z, y) 0 -
            ∫ t, f2 (z, y) t * Real.cos (π * k * t) ∂μ1) / (π * k) ^ 2 := fun y =>
        integral_mul_cos_ibp (g := f (z, y)) (g1 := f1 (z, y)) (g2 := f2 (z, y))
          (fun t => hasDerivAt_of_family (f := f) hf (z, y) t)
          (fun t => hasDerivAt_of_family (f := f1) hf1 (z, y) t)
          (hf2.continuous.comp (continuous_const.prodMk continuous_id)) hk
      rw [hsw hf]
      simp only [hibp]
      -- split the integral over `y`
      set A : (Fin d → ℝ) → ℝ := fun y => f1 (z, y) 1
      set B : (Fin d → ℝ) → ℝ := fun y => f1 (z, y) 0
      set D : (Fin d → ℝ) → ℝ := fun y => ∫ t, f2 (z, y) t * Real.cos (π * k * t) ∂μ1
      have hA : Continuous A := (hf1.continuous).comp
        ((continuous_const.prodMk continuous_id).prodMk continuous_const)
      have hB : Continuous B := (hf1.continuous).comp
        ((continuous_const.prodMk continuous_id).prodMk continuous_const)
      have hD : Continuous D :=
        continuous_param1 (G := fun y t => f2 (z, y) t * Real.cos (π * k * t))
        (((hf2.continuous).comp ((continuous_const.prodMk continuous_fst).prodMk
          continuous_snd)).mul (by fun_prop))
      have hc := continuous_cosP l'
      have esplit : ∫ y, cosP l' y * (((-1) ^ k * A y - B y - D y) / (π * k) ^ 2) ∂piM d =
          ((-1) ^ k * ∫ y, A y * cosP l' y ∂piM d - ∫ y, B y * cosP l' y ∂piM d -
            ∫ y, D y * cosP l' y ∂piM d) / (π * k) ^ 2 := by
        have e : (fun y => cosP l' y * (((-1) ^ k * A y - B y - D y) / (π * k) ^ 2)) =
            fun y => (((-1) ^ k * (A y * cosP l' y) - B y * cosP l' y) - D y * cosP l' y) /
              (π * k) ^ 2 := by
          funext y; ring
        rw [e, integral_div, integral_sub, integral_sub, integral_const_mul]
        · exact (integrable_piM ((hA.mul hc).const_smul ((-1 : ℝ) ^ k))).congr
            (ae_of_all _ fun y => by simp [smul_eq_mul])
        · exact integrable_piM (hB.mul hc)
        · exact integrable_piM ((continuous_const.mul (hA.mul hc)).sub (hB.mul hc))
        · exact integrable_piM (hD.mul hc)
      rw [esplit]
      -- the three coefficient functions
      have bA : |∫ y, A y * cosP l' y ∂piM d| ≤ C1 * P :=
        h1 (z, 1) ⟨hz, by simp⟩ l'
      have bB : |∫ y, B y * cosP l' y ∂piM d| ≤ C1 * P :=
        h1 (z, 0) ⟨hz, by simp⟩ l'
      have bD : |∫ y, D y * cosP l' y ∂piM d| ≤ C2 * P := by
        have e : ∫ y, D y * cosP l' y ∂piM d =
            ∫ t, Real.cos (π * k * t) * ∫ y, f2 (z, y) t * cosP l' y ∂piM d ∂μ1 := by
          rw [hsw hf2]; congr 1; funext y; ring
        rw [e]; exact hbd (g := f2) h2
      have hpk := inv_pi_sq_le_rho hk
      have hsgn : |((-1 : ℝ) ^ k)| = 1 := by simp
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (π * k) ^ 2), div_eq_mul_inv]
      have htri : |(-1) ^ k * ∫ y, A y * cosP l' y ∂piM d - ∫ y, B y * cosP l' y ∂piM d -
          ∫ y, D y * cosP l' y ∂piM d| ≤ (2 * C1 + C2) * P := by
        set a := ∫ y, A y * cosP l' y ∂piM d
        set b' := ∫ y, B y * cosP l' y ∂piM d
        set e := ∫ y, D y * cosP l' y ∂piM d
        have t1 := abs_sub ((-1 : ℝ) ^ k * a - b') e
        have t2 := abs_sub ((-1 : ℝ) ^ k * a) b'
        rw [abs_mul, hsgn, one_mul] at t2
        linarith
      calc |(-1) ^ k * ∫ y, A y * cosP l' y ∂piM d - ∫ y, B y * cosP l' y ∂piM d -
            ∫ y, D y * cosP l' y ∂piM d| * ((π * k) ^ 2)⁻¹
          ≤ ((2 * C1 + C2) * P) * rho k :=
            mul_le_mul htri hpk (by positivity) (by positivity)
        _ ≤ (max C0 (2 * C1 + C2) * P) * rho k :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hP)
              (rho_pos k).le
        _ = max C0 (2 * C1 + C2) * (rho k * P) := by ring

end DFT.Continuum.Sine
