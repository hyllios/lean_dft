/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Represent

/-!
# Densities of states on a line have `√ρ ∈ H¹`

For a state `Φ` of `N = n + 1` particles on `[0, 1]` (any `Φ` in the form domain `Dom τ n`), the
one-body density `ρ(t) = N ∫ Φ(t, y)² dy` is `C¹`, nonnegative, vanishes at `0` and `1`, and
satisfies the **Lieb (Hoffmann-Ostenhof) bound**
`∫₀¹ ρ'² / (4ρ) ≤ Σ_k ∫ |∂_k Φ|²`. Where `ρ > 0`, `ρ'² / (4ρ) = ((√ρ)')²`, so `√ρ` has finite
`H¹` energy, bounded by the kinetic energy. This is the necessity half of Lieb's
characterisation of `N`-representable densities (`√ρ ∈ H¹`).

The proof: `ρ' = 2N ∫ Φ ∂₀Φ dy` (differentiation under the integral), the Cauchy–Schwarz
inequality in `y` (`ρ'² ≤ 4 ρ · N ∫ |∂₀Φ|² dy`, via a discriminant), and the exchange symmetry of
`|∂_k Φ|²`.

* `marg`, `margD`, `margK`: `∫ Φ²`, `∫ 2Φ ∂₀Φ` and `∫ |∂₀Φ|²` over the other `n` particles.
* `hasDerivAt_marg`: `marg' = margD`; `margD_sq_le`: `margD² ≤ 4 marg margK`.
* `rhoN`, `rhoD`: the density and its derivative; `dens_eq_rhoN`: `rhoN` is the density.
* `sqrt_dens_H1`: **`√ρ ∈ H¹` with `∫ ((√ρ)')² ≤ T`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat} {Φ : Cfg n → ℝ}

lemma continuous_cons_pair : Continuous fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Cfg n) := by
  fun_prop

lemma continuous_cons_right (t : ℝ) : Continuous fun y : Fin n → ℝ => (Fin.cons t y : Cfg n) := by
  fun_prop

lemma measurableSet_cube' : MeasurableSet (Cube' n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma integrableOn_cube' {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) : IntegrableOn g (Cube' n) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (pi_mono fun _ _ => Ioo_subset_Icc_self)

/-- Integrals over the other particles of a jointly continuous function are continuous. -/
lemma continuous_integral_cube' {G : ℝ → (Fin n → ℝ) → ℝ}
    (hG : Continuous fun p : ℝ × (Fin n → ℝ) => G p.1 p.2) :
    Continuous fun t => ∫ y in Cube' n, G t y := by
  have hae : Cube' n =ᵐ[volume] Icc (0 : Fin n → ℝ) 1 :=
    Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ)) (f := 0) (g := 1)
  have e : ∀ t, ∫ y in Cube' n, G t y = ∫ y in Icc (0 : Fin n → ℝ) 1, G t y :=
    fun t => setIntegral_congr_set hae
  simp only [e]
  exact continuous_parametric_integral_of_continuous (f := G) hG isCompact_Icc

lemma hasDerivAt_cons_slice {f : Cfg n → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (y : Fin n → ℝ) :
    HasDerivAt (fun s => f (Fin.cons s y)) (dk 0 f (Fin.cons t y)) t := by
  simpa [Fin.update_cons_zero] using hasDerivAt_slice hf (Fin.cons t y) 0 t

lemma bound_cons {h : Cfg n → ℝ} (hh : Continuous h) (t0 : ℝ) :
    ∃ C, ∀ s ∈ Metric.ball t0 1, ∀ y ∈ Cube' n, |h (Fin.cons s y)| ≤ C := by
  have hK : IsCompact (Icc (t0 - 1) (t0 + 1) ×ˢ Set.pi univ fun _ : Fin n => Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hh.comp continuous_cons_pair).continuousOn
  refine ⟨C, fun s hs y hy => ?_⟩
  have hs' : s ∈ Icc (t0 - 1) (t0 + 1) := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith [hs.1, hs.2]
  have := hC (s, y) ⟨hs', fun i _ => Ioo_subset_Icc_self (hy i (mem_univ i))⟩
  simpa [Real.norm_eq_abs] using this

/-! ### The marginals -/

/-- `∫ Φ(t, y)² dy`. -/
noncomputable def marg (Φ : Cfg n → ℝ) (t : ℝ) : ℝ := ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2

/-- `∫ 2 Φ(t, y) ∂₀Φ(t, y) dy`. -/
noncomputable def margD (Φ : Cfg n → ℝ) (t : ℝ) : ℝ :=
  ∫ y in Cube' n, 2 * (Φ (Fin.cons t y) * dk 0 Φ (Fin.cons t y))

/-- `∫ |∂₀Φ(t, y)|² dy`. -/
noncomputable def margK (Φ : Cfg n → ℝ) (t : ℝ) : ℝ := ∫ y in Cube' n, dk 0 Φ (Fin.cons t y) ^ 2

lemma marg_nonneg (t : ℝ) : 0 ≤ marg Φ t :=
  setIntegral_nonneg measurableSet_cube' fun _ _ => sq_nonneg _

lemma margK_nonneg (t : ℝ) : 0 ≤ margK Φ t :=
  setIntegral_nonneg measurableSet_cube' fun _ _ => sq_nonneg _

/-- `C²` functions of exchange symmetry `τ`, with no boundary condition. -/
def DomC (τ : Stat) (n : ℕ) : Set (Cfg n → ℝ) :=
  {ψ | ContDiff ℝ 2 ψ ∧ ∀ σ x, ψ (pm σ x) = ch τ σ * ψ x}

lemma domC_of_dom {ψ : Cfg n → ℝ} (h : ψ ∈ Dom τ n) : ψ ∈ DomC τ n := ⟨h.1, h.2.1⟩

lemma diffC {ψ : Cfg n → ℝ} (h : ψ ∈ DomC τ n) : Differentiable ℝ ψ :=
  h.1.differentiable (by norm_num)

lemma cont_dkC {ψ : Cfg n → ℝ} (h : ψ ∈ DomC τ n) (k : Fin (n + 1)) : Continuous (dk k ψ) :=
  (h.1.continuous_fderiv (by norm_num)).clm_apply continuous_const

section dom

variable (hΦ : Φ ∈ DomC τ n)
include hΦ

lemma continuous_marg : Continuous (marg Φ) :=
  continuous_integral_cube' (G := fun t y => Φ (Fin.cons t y) ^ 2)
    ((hΦ.1.continuous.comp continuous_cons_pair).pow 2)

lemma continuous_margD : Continuous (margD Φ) :=
  continuous_integral_cube' (G := fun t y => 2 * (Φ (Fin.cons t y) * dk 0 Φ (Fin.cons t y)))
    (continuous_const.mul ((hΦ.1.continuous.comp continuous_cons_pair).mul
      ((cont_dkC hΦ 0).comp continuous_cons_pair)))

lemma continuous_margK : Continuous (margK Φ) :=
  continuous_integral_cube' (G := fun t y => dk 0 Φ (Fin.cons t y) ^ 2)
    (((cont_dkC hΦ 0).comp continuous_cons_pair).pow 2)

/-- Differentiation under the integral: `marg' = margD`. -/
lemma hasDerivAt_marg (t0 : ℝ) : HasDerivAt (marg Φ) (margD Φ t0) t0 := by
  have hc := hΦ.1.continuous
  have hd := cont_dkC hΦ 0
  obtain ⟨C, hC⟩ := bound_cons (hc.mul hd) t0
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Cube' n))
    (F := fun s y => Φ (Fin.cons s y) ^ 2)
    (F' := fun s y => 2 * (Φ (Fin.cons s y) * dk 0 Φ (Fin.cons s y)))
    (bound := fun _ => 2 * C) (Metric.ball_mem_nhds t0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s =>
      ((hc.comp (continuous_cons_right s)).pow 2).aestronglyMeasurable
  · exact integrableOn_cube' ((hc.comp (continuous_cons_right t0)).pow 2)
  · exact (continuous_const.mul ((hc.comp (continuous_cons_right t0)).mul
      (hd.comp (continuous_cons_right t0)))).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_cube').mono fun y hy s hs => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (hC s hs y hy) two_pos.le
  · exact integrableOn_cube' continuous_const
  · refine ae_of_all _ fun y s _ => ?_
    exact ((hasDerivAt_cons_slice (diffC hΦ) s y).pow 2).congr_deriv (by ring)

/-- **Cauchy–Schwarz in the other particles**: `margD² ≤ 4 marg margK`. -/
lemma margD_sq_le (t : ℝ) : margD Φ t ^ 2 ≤ 4 * marg Φ t * margK Φ t := by
  have ha : Continuous fun y : Fin n → ℝ => Φ (Fin.cons t y) :=
    hΦ.1.continuous.comp (continuous_cons_right t)
  have hb : Continuous fun y : Fin n → ℝ => dk 0 Φ (Fin.cons t y) :=
    (cont_dkC hΦ 0).comp (continuous_cons_right t)
  have hq : ∀ r : ℝ, 0 ≤ marg Φ t * (r * r) + margD Φ t * r + margK Φ t := by
    intro r
    have i1 := integrableOn_cube' (g := fun y => Φ (Fin.cons t y) ^ 2 * (r * r))
      ((ha.pow 2).mul continuous_const)
    have i2 := integrableOn_cube'
      (g := fun y => 2 * (Φ (Fin.cons t y) * dk 0 Φ (Fin.cons t y)) * r)
      ((continuous_const.mul (ha.mul hb)).mul continuous_const)
    have i3 := integrableOn_cube' (g := fun y => dk 0 Φ (Fin.cons t y) ^ 2) (hb.pow 2)
    have e : ∫ y in Cube' n, (r * Φ (Fin.cons t y) + dk 0 Φ (Fin.cons t y)) ^ 2 =
        marg Φ t * (r * r) + margD Φ t * r + margK Φ t := by
      calc ∫ y in Cube' n, (r * Φ (Fin.cons t y) + dk 0 Φ (Fin.cons t y)) ^ 2
          = ∫ y in Cube' n, ((Φ (Fin.cons t y) ^ 2 * (r * r) +
              2 * (Φ (Fin.cons t y) * dk 0 Φ (Fin.cons t y)) * r) +
              dk 0 Φ (Fin.cons t y) ^ 2) := by congr 1; funext y; ring
        _ = (∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 * (r * r)) +
              (∫ y in Cube' n, 2 * (Φ (Fin.cons t y) * dk 0 Φ (Fin.cons t y)) * r) +
              ∫ y in Cube' n, dk 0 Φ (Fin.cons t y) ^ 2 := by
            rw [integral_add (f := fun y => Φ (Fin.cons t y) ^ 2 * (r * r) +
              2 * (Φ (Fin.cons t y) * dk 0 Φ (Fin.cons t y)) * r) (by exact i1.add i2) i3,
              integral_add i1 i2]
        _ = _ := by rw [integral_mul_const, integral_mul_const]; rfl
    rw [← e]
    exact setIntegral_nonneg measurableSet_cube' fun _ _ => sq_nonneg _
  have := discrim_le_zero hq
  rw [discrim] at this
  linarith

/-- `∫ |∂_k Φ|² = ∫ |∂₀Φ|²` by exchange symmetry. -/
lemma integral_dk_sq (k : Fin (n + 1)) :
    ∫ x, dk k Φ x ^ 2 ∂μN n = ∫ x, dk 0 Φ x ^ 2 ∂μN n := by
  set σ := Equiv.swap (0 : Fin (n + 1)) k
  have h : ∀ x, dk k Φ x ^ 2 = dk 0 Φ (pm σ x) ^ 2 := by
    intro x
    have e1 := dk_comp_pm (diffC hΦ) σ k x
    have e2 : (fun y => Φ (pm σ y)) = ch τ σ • Φ := by funext y; simp [hΦ.2 σ y]
    have hs : σ⁻¹ k = 0 := by simp [σ, Equiv.swap_inv]
    rw [e2, dk_smul (diffC hΦ), hs] at e1
    rw [← e1, Pi.smul_apply, smul_eq_mul, mul_pow, sq (ch τ σ), ch_mul_self, one_mul]
  simp only [h]
  exact integral_pm σ (fun x => dk 0 Φ x ^ 2)

/-- The kinetic energy is `N ∫ |∂₀Φ|²`. -/
lemma kin_eq : ∫ x, ∑ k, dk k Φ x * dk k Φ x ∂μN n = (n + 1) * ∫ x, dk 0 Φ x ^ 2 ∂μN n := by
  rw [integral_finsetSum (f := fun k x => dk k Φ x * dk k Φ x) _
    fun k _ => integrableN ((cont_dkC hΦ k).mul (cont_dkC hΦ k))]
  simp only [← sq, integral_dk_sq hΦ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast; ring

/-- The density is nonnegative and `C¹`, with derivative `rhoD`. -/
lemma rho_propsC : (∀ t, 0 ≤ (n + 1 : ℝ) * marg Φ t) ∧
    (∀ t, HasDerivAt (fun s => (n + 1 : ℝ) * marg Φ s) ((n + 1 : ℝ) * margD Φ t) t) ∧
    Continuous fun t => (n + 1 : ℝ) * margD Φ t :=
  ⟨fun t => mul_nonneg (by positivity) (marg_nonneg t),
    fun t => (hasDerivAt_marg hΦ t).const_mul _, continuous_const.mul (continuous_margD hΦ)⟩

end dom

/-! ### The density -/

/-- The one-body density `ρ(t) = N ∫ Φ(t, y)² dy`. -/
noncomputable def rhoN (Φ : Cfg n → ℝ) (t : ℝ) : ℝ := (n + 1) * marg Φ t

/-- Its derivative `ρ'(t) = 2N ∫ Φ(t, y) ∂₀Φ(t, y) dy`. -/
noncomputable def rhoD (Φ : Cfg n → ℝ) (t : ℝ) : ℝ := (n + 1) * margD Φ t

/-- `rhoN` is the density: `⟨Φ, (Σ_k v(x_k)) Φ⟩ = ∫₀¹ v ρ`. -/
theorem dens_eq_rhoN {w : Cfg n → ℝ} {hw : Continuous w} (hΦ : Φ ∈ Dom τ n) (v : Pot) :
    dens (setting τ n w hw) Φ v = ∫ t in Ioo (0 : ℝ) 1, ext v t * rhoN Φ t := by
  have hv := continuous_ext v
  have swapsq : ∀ k : Fin (n + 1), ∫ x, ext v (x k) * (Φ x * Φ x) ∂μN n =
      ∫ x, ext v (x 0) * (Φ x * Φ x) ∂μN n := by
    intro k
    rw [← integral_pm (Equiv.swap 0 k)]
    congr 1; funext x
    rw [sq_pm hΦ]
    simp
  simp only [dens, pf]
  change ∫ x, (∑ k, ext v (x k)) * (Φ x * Φ x) ∂μN n = _
  have hpt : (fun x : Cfg n => (∑ k, ext v (x k)) * (Φ x * Φ x)) =
      fun x => ∑ k, ext v (x k) * (Φ x * Φ x) := by
    funext x; rw [Finset.sum_mul]
  rw [hpt, integral_finsetSum (f := fun k x => ext v (x k) * (Φ x * Φ x)) _
    fun k _ => integrableN ((hv.comp (continuous_apply k)).mul
    (hΦ.1.continuous.mul hΦ.1.continuous))]
  simp only [swapsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_cube_cons (F := fun x => ext v (x 0) * (Φ x * Φ x))
    ((hv.comp (continuous_apply 0)).mul (hΦ.1.continuous.mul hΦ.1.continuous))]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  simp only [Fin.cons_zero, rhoN, marg, ← integral_const_mul]
  push_cast
  congr 1; funext y; ring

/-- **`√ρ ∈ H¹` for every state on a line** (the necessity half of Lieb's characterisation of
`N`-representable densities). For `Φ` in the form domain, the density `ρ = rhoN Φ`:
* is nonnegative, vanishes at the walls, and integrates to `N ‖Φ‖²`;
* is differentiable with continuous derivative `ρ' = rhoD Φ`;
* has `√ρ` differentiable wherever `ρ > 0`, with `(√ρ)' = ρ' / (2√ρ)`;
* satisfies the **Lieb bound** `∫₀¹ ρ'² / (4ρ) ≤ Σ_k ∫ |∂_k Φ|²` (the integrand is
  `((√ρ)')²` where `ρ > 0`, and is integrable). -/
theorem sqrt_dens_H1 (hΦ : Φ ∈ Dom τ n) :
    (∀ t, 0 ≤ rhoN Φ t) ∧ rhoN Φ 0 = 0 ∧ rhoN Φ 1 = 0 ∧
      ∫ t in Ioo (0 : ℝ) 1, rhoN Φ t = (n + 1) * ∫ x, Φ x ^ 2 ∂μN n ∧
      (∀ t, HasDerivAt (rhoN Φ) (rhoD Φ t) t) ∧ Continuous (rhoD Φ) ∧
      (∀ t, 0 < rhoN Φ t →
        HasDerivAt (fun s => √(rhoN Φ s)) (rhoD Φ t / (2 * √(rhoN Φ t))) t) ∧
      IntegrableOn (fun t => rhoD Φ t ^ 2 / (4 * rhoN Φ t)) (Ioo 0 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, rhoD Φ t ^ 2 / (4 * rhoN Φ t) ≤
        ∫ x, ∑ k, dk k Φ x * dk k Φ x ∂μN n := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hρ0 : ∀ t, 0 ≤ rhoN Φ t := fun t => mul_nonneg hN.le (marg_nonneg t)
  have hwall : ∀ a : ℝ, (a = 0 ∨ a = 1) → rhoN Φ a = 0 := by
    intro a ha
    have h0 : ∀ y : Fin n → ℝ, Φ (Fin.cons a y) ^ 2 = 0 := fun y => by
      rw [hΦ.2.2 (Fin.cons a y) 0 (by simpa using ha)]; ring
    simp [rhoN, marg, h0]
  have hder : ∀ t, HasDerivAt (rhoN Φ) (rhoD Φ t) t := fun t =>
    (hasDerivAt_marg (domC_of_dom hΦ) t).const_mul ((n : ℝ) + 1)
  have hcρ : Continuous (rhoN Φ) := continuous_const.mul (continuous_marg (domC_of_dom hΦ))
  have hcD : Continuous (rhoD Φ) := continuous_const.mul (continuous_margD (domC_of_dom hΦ))
  have hKint : IntegrableOn (margK Φ) (Ioo (0 : ℝ) 1) :=
    ((continuous_margK (domC_of_dom hΦ)).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  have hq0 : ∀ t, 0 ≤ rhoD Φ t ^ 2 / (4 * rhoN Φ t) := fun t =>
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (hρ0 t))
  have hpt : ∀ t, rhoD Φ t ^ 2 / (4 * rhoN Φ t) ≤ (n + 1) * margK Φ t := by
    intro t
    rcases (marg_nonneg (Φ := Φ) t).eq_or_lt with h0 | hpos
    · rw [rhoN, ← h0, mul_zero, mul_zero, div_zero]
      exact mul_nonneg hN.le (margK_nonneg t)
    · rw [div_le_iff₀ (by rw [rhoN]; positivity)]
      have h := margD_sq_le (domC_of_dom hΦ) t
      have hN2 : 0 ≤ ((n : ℝ) + 1) ^ 2 := by positivity
      calc rhoD Φ t ^ 2 = ((n : ℝ) + 1) ^ 2 * margD Φ t ^ 2 := by rw [rhoD]; ring
        _ ≤ ((n : ℝ) + 1) ^ 2 * (4 * marg Φ t * margK Φ t) := mul_le_mul_of_nonneg_left h hN2
        _ = (n + 1) * margK Φ t * (4 * rhoN Φ t) := by rw [rhoN]; ring
  have hqm : Measurable fun t => rhoD Φ t ^ 2 / (4 * rhoN Φ t) :=
    (hcD.pow 2).measurable.div (hcρ.measurable.const_mul 4)
  have hqint : IntegrableOn (fun t => rhoD Φ t ^ 2 / (4 * rhoN Φ t)) (Ioo 0 1) :=
    (hKint.const_mul ((n : ℝ) + 1)).mono' hqm.aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hq0 t)]; exact hpt t)
  refine ⟨hρ0, hwall 0 (Or.inl rfl), hwall 1 (Or.inr rfl), ?_, hder, hcD,
    fun t ht => (hder t).sqrt ht.ne', hqint, ?_⟩
  · rw [integral_cube_cons (F := fun x => Φ x ^ 2) (hΦ.1.continuous.pow 2), ← integral_const_mul]
    rfl
  · calc ∫ t in Ioo (0 : ℝ) 1, rhoD Φ t ^ 2 / (4 * rhoN Φ t)
        ≤ ∫ t in Ioo (0 : ℝ) 1, (n + 1) * margK Φ t :=
          integral_mono hqint (hKint.const_mul _) hpt
      _ = ∫ x, ∑ k, dk k Φ x * dk k Φ x ∂μN n := by
          rw [kin_eq (domC_of_dom hΦ), integral_cube_cons (F := fun x => dk 0 Φ x ^ 2)
            ((cont_dk hΦ 0).pow 2), integral_const_mul]
          rfl

end DFT.Continuum.Line
