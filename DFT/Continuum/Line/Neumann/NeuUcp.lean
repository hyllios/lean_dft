/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.NeuDensD
import DFT.Continuum.Line.Neumann.NeuEL

/-!
# Unique continuation for bosonic Neumann ground states of `H⁻¹` potentials

For `N` bosons on `[0, 1]` with Neumann walls, an `H⁻¹` potential `v` and a continuous interaction
`w`, every ground state is nonzero almost everywhere (**`gsNH_ne_zero_bos`**).

The proof is that of `Line/MeasureNUcp`, with two changes.

* The potential term of Moser's estimate is first order. With `φ = η²/(u + ε)` the mixed density
  is the density of `p = u φ = η² u/(u + ε)`, and `|∂₀p| ≤ |η ∂₀u/(u + ε)| + 2|∂₀η|`. The marginal
  bound `‖ρ(u, φ)‖² ≤ 2N² (∫ p² + ∫ (∂₀p)²)` (`Line/NeuDensD`) and Young's inequality bound
  `|v(ρ(u, φ))|` by a quarter of the logarithmic gradient plus a constant, which is absorbed
  (`log_estimate_H`).
* The zero-set machinery (`LogData`) is stated in `H¹₀`. A cutoff `ζ` equal to `1` near the
  support of `η` and vanishing on the walls moves `u` into `H¹₀` without changing it on
  `[a, 1 - a]ᴺ` or near the support of `η` (`logData_H`).

* `prodB`, `bmp`, `etaA`, `zetaA`: product cutoffs.
* `log_estimate_coreN`, `logTest_memN`, `memLp_logA`, **`log_estimate_H`**, **`logData_H`**,
  **`gsNH_ne_zero_bos`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

/-! ### Product cutoffs -/

/-- `x ↦ Π_j f(x_j)`. -/
noncomputable def prodB (f : ℝ → ℝ) (x : Cfg n) : ℝ := ∏ j, f (x j)

lemma contDiff_prodB {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (prodB (n := n) f) :=
  contDiff_prod fun j _ => hf.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).contDiff

lemma prodB_pm (f : ℝ → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    prodB f (pm σ x) = prodB f x := by
  simp only [prodB, pm_apply]
  exact Equiv.prod_comp σ (fun j => f (x j))

lemma prodB_nonneg {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (x : Cfg n) : 0 ≤ prodB f x :=
  Finset.prod_nonneg fun _ _ => h0 _

lemma prodB_le_one {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1) (x : Cfg n) :
    prodB f x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => h0 _) fun _ _ => h1 _

/-- A bump centred at `1/2`. -/
noncomputable def bmp (r₁ r₂ : ℝ) (h1 : 0 < r₁) (h2 : r₁ < r₂) : ContDiffBump (1 / 2 : ℝ) :=
  ⟨r₁, r₂, h1, h2⟩

section cutoffs

variable {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)

/-- `η_a = Π_j b(x_j)`, `b = 1` on `[a/2, 1 - a/2]`, supported in `(a/4, 1 - a/4)`. -/
noncomputable def etaA : Cfg n → ℝ :=
  prodB (bmp (1 / 2 - a / 2) (1 / 2 - a / 4) (by linarith) (by linarith))

/-- `ζ_a = Π_j z(x_j)`, `z = 1` on `[a/8, 1 - a/8]`, supported in `(a/16, 1 - a/16)`. -/
noncomputable def zetaA : Cfg n → ℝ :=
  prodB (bmp (1 / 2 - a / 8) (1 / 2 - a / 16) (by linarith) (by linarith))

include ha ha2

lemma contDiff_etaA : ContDiff ℝ 1 (etaA (n := n) ha ha2) := contDiff_prodB (ContDiffBump.contDiff _)

lemma contDiff_zetaA : ContDiff ℝ 1 (zetaA (n := n) ha ha2) :=
  contDiff_prodB (ContDiffBump.contDiff _)

lemma etaA_pm (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    etaA ha ha2 (pm σ x) = etaA ha ha2 x := prodB_pm _ σ x

lemma abs_etaA_le (x : Cfg n) : |etaA ha ha2 x| ≤ 1 := by
  unfold etaA
  rw [abs_of_nonneg (prodB_nonneg (fun t => ContDiffBump.nonneg _) x)]
  exact prodB_le_one (fun t => ContDiffBump.nonneg _) (fun _ => ContDiffBump.le_one _) x

lemma zetaA_nonneg (x : Cfg n) : 0 ≤ zetaA ha ha2 x := prodB_nonneg (fun _ => ContDiffBump.nonneg _) x

lemma etaA_eq_one {x : Cfg n} (hx : x ∈ Qa n a) : etaA ha ha2 x = 1 := by
  unfold etaA prodB
  refine Finset.prod_eq_one fun j _ => ContDiffBump.one_of_mem_closedBall _ ?_
  have := Set.mem_univ_pi.1 hx j
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(1 / 2 - a / 2) ≤ x j - 1 / 2 ∧ x j - 1 / 2 ≤ 1 / 2 - a / 2
  constructor <;> linarith [this.1, this.2]

lemma zetaA_wall (x : Cfg n) (j : Fin (n + 1)) (h : x j = 0 ∨ x j = 1) : zetaA ha ha2 x = 0 := by
  unfold zetaA prodB
  refine Finset.prod_eq_zero (Finset.mem_univ j) (ContDiffBump.zero_of_le_dist _ ?_)
  change 1 / 2 - a / 16 ≤ dist (x j) (1 / 2)
  rcases h with h | h <;> rw [h, Real.dist_eq] <;> norm_num <;> linarith

/-- The open set where `ζ_a = 1`. -/
def Va (n : ℕ) (a : ℝ) : Set (Cfg n) := {x | ∀ j, dist (x j) (1 / 2) < 1 / 2 - a / 8}

omit ha ha2 in
lemma isOpen_Va : IsOpen (Va n a) := by
  simp only [Va, ofPred_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt ((continuous_apply j).dist continuous_const) continuous_const

lemma zetaA_eq_one {x : Cfg n} (hx : x ∈ Va n a) : zetaA ha ha2 x = 1 := by
  unfold zetaA prodB
  exact Finset.prod_eq_one fun j _ => ContDiffBump.one_of_mem_closedBall _
    (Metric.mem_closedBall.2 (hx j).le)

lemma dk_zetaA {x : Cfg n} (hx : x ∈ Va n a) (k : Fin (n + 1)) : dk k (zetaA ha ha2) x = 0 := by
  have he : zetaA ha ha2 =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (isOpen_Va.mem_nhds hx) fun y hy => zetaA_eq_one ha ha2 hy
  simp [dk, he.fderiv_eq]

lemma mem_Va_of_etaA {x : Cfg n} (hx : etaA ha ha2 x ≠ 0) : x ∈ Va n a := fun j => by
  unfold etaA prodB at hx
  have hj : bmp (1 / 2 - a / 2) (1 / 2 - a / 4) (by linarith) (by linarith) (x j) ≠ 0 :=
    (Finset.prod_ne_zero_iff.1 hx) j (Finset.mem_univ j)
  have := (ContDiffBump.support_eq _).le (Function.mem_support.2 hj)
  rw [Metric.mem_ball] at this
  change dist (x j) (1 / 2) < 1 / 2 - a / 4 at this
  linarith

omit ha2 in
lemma Qa_sub_Va : Qa n a ⊆ Va n a := fun x hx j => by
  have := Set.mem_univ_pi.1 hx j
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [this.1, this.2]

end cutoffs

/-! ### Moser's estimate with Neumann walls -/

/-- The logarithmic gradients are in `L²`. -/
lemma memLp_logA {u : Cfg n → ℝ} (hD : u ∈ DomN .bos n) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η) {ε : ℝ} (hε : 0 < ε) (k : Fin (n + 1)) :
    MemLp (fun x => η x * (dWN k u x / (u x + ε))) 2 (μN n) := by
  have hum := hD.1
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  refine (dWN_spec (hD.2.1 k)).1.of_le_mul (c := Bη / ε) (hη.continuous.aemeasurable.mul
    ((dWN_spec (hD.2.1 k)).1.aestronglyMeasurable.aemeasurable.div
      (hum.aestronglyMeasurable.aemeasurable.add_const ε))).aestronglyMeasurable ?_
  filter_upwards [hBη, hu0] with x hx h0
  have hp : 0 < u x + ε := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at *
  simp only [abs_mul, abs_div, abs_of_pos hp]
  rw [mul_div_assoc', div_le_iff₀ hp]
  have h1 : |η x| * |dWN k u x| ≤ Bη * |dWN k u x| :=
    mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have h2 : Bη / ε * |dWN k u x| * ε ≤ Bη / ε * |dWN k u x| * (u x + ε) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (div_nonneg ((abs_nonneg _).trans hx)
      hε.le) (abs_nonneg _))
  have h3 : Bη / ε * |dWN k u x| * ε = Bη * |dWN k u x| := by field_simp
  linarith

/-- **The logarithmic estimate from a lower bound** `-K ≤ Σ_k ∫ ∂ₖu ∂ₖφ`, `φ = logTest η u ε`. -/
theorem log_estimate_coreN {u : Cfg n → ℝ} (hD : u ∈ DomN .bos n) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x)
    {η : Cfg n → ℝ} (hη : ContDiff ℝ 1 η)
    {ε : ℝ} (hε : 0 < ε) {K : ℝ}
    (hlow : -K ≤ ∑ k, ∫ x, dWN k u x * dWN k (logTest η u ε) x ∂μN n) :
    ∑ k, ∫ x, (η x * (dWN k u x / (u x + ε))) ^ 2 ∂μN n ≤
      4 * ∑ k, ∫ x, dk k η x ^ 2 ∂μN n + 2 * K := by
  have hum := hD.1
  set ζ : Cfg n → ℝ := fun x => η x * η x with hζdef
  have hζ : ContDiff ℝ 1 ζ := hη.mul hη
  have hdζ : ∀ k x, dk k ζ x = 2 * η x * dk k η x := fun k x => by
    rw [dk_mul (hη.differentiable one_ne_zero) (hη.differentiable one_ne_zero)]; ring
  have hGc : Continuous (Gr ε) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_Gr hε t).continuousAt
  set g : Cfg n → ℝ := fun x => Gr ε (u x)
  have hgL : MemLp g 2 (μN n) := MemLp.of_bound (hGc.comp_aestronglyMeasurable
    hum.aestronglyMeasurable) (1 / ε) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact abs_Gr_le hε _)
  have hg : ∀ k, IsWDN k g (fun x => 1 / (|u x| + ε) ^ 2 * dWN k u x) := fun k =>
    isWDN_comp hD (hasDerivAt_Gr hε) (continuous_Gr' hε) (Gr'_le hε) Gr_zero k
  set φ : Cfg n → ℝ := fun x => ε⁻¹ * ζ x + (-1) * (ζ x * g x)
  have hφe : logTest η u ε = φ := rfl
  rw [hφe] at hlow
  have hL1 : MemLp (fun x => ε⁻¹ * ζ x) 2 (μN n) := memLp_cont (continuous_const.mul hζ.continuous)
  have hL2 : MemLp (fun x => -1 * (ζ x * g x)) 2 (μN n) :=
    (memLp_mul_cont hζ.continuous hgL).const_mul (-1)
  have hφWD : ∀ k, IsWDN k φ (fun x => ε⁻¹ * dk k ζ x +
      (-1) * (ζ x * (1 / (|u x| + ε) ^ 2 * dWN k u x) + dk k ζ x * g x)) := fun k =>
    IsWDN.add hL1 hL2 ((isWDN_of_C1 hζ k).const_mul ε⁻¹)
      (((hg k).mul_C1 hgL hζ).const_mul (-1))
  obtain ⟨Bη, hBη⟩ := ae_bound_cont hη.continuous
  set A : Fin (n + 1) → Cfg n → ℝ := fun k x => η x * (dWN k u x / (u x + ε))
  have hAL : ∀ k, MemLp (A k) 2 (μN n) := fun k => by
    refine (dWN_spec (hD.2.1 k)).1.of_le_mul (c := Bη / ε) (hη.continuous.aemeasurable.mul
      ((dWN_spec (hD.2.1 k)).1.aestronglyMeasurable.aemeasurable.div
        (hum.aestronglyMeasurable.aemeasurable.add_const ε))).aestronglyMeasurable ?_
    filter_upwards [hBη, hu0] with x hx h0
    have hp : 0 < u x + ε := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at *
    simp only [A, abs_mul, abs_div, abs_of_pos hp]
    rw [mul_div_assoc', div_le_iff₀ hp]
    have h1 : |η x| * |dWN k u x| ≤ Bη * |dWN k u x| :=
      mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have h2 : Bη / ε * |dWN k u x| * ε ≤ Bη / ε * |dWN k u x| * (u x + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (div_nonneg ((abs_nonneg _).trans hx)
        hε.le) (abs_nonneg _))
    have h3 : Bη / ε * |dWN k u x| * ε = Bη * |dWN k u x| := by field_simp
    linarith
  have hdη : ∀ k, Continuous (dk k η) := fun k => continuous_dk_of_C1 hη k
  have hpt : ∀ k, ∀ᵐ x ∂μN n, dWN k u x * dWN k φ x = 2 * (A k x * dk k η x) - A k x ^ 2 := by
    intro k
    filter_upwards [dWN_ae_eq (hφWD k), hu0] with x hx h0
    have hp : 0 < u x + ε := by linarith
    rw [hx]
    simp only [A, hdζ, g, ζ, Gr_of_nonneg h0, abs_of_nonneg h0]
    field_simp
    ring
  have hk : ∀ k, ∫ x, dWN k u x * dWN k φ x ∂μN n =
      2 * ∫ x, A k x * dk k η x ∂μN n - ∫ x, A k x ^ 2 ∂μN n := fun k => by
    rw [integral_congr_ae (hpt k), integral_sub ((int_mul_cont (hAL k) (hdη k)).const_mul 2)
      (hAL k).integrable_sq, integral_const_mul]
  have hAB : ∀ k, ∫ x, A k x * dk k η x ∂μN n ≤
      (1 / 4) * ∫ x, A k x ^ 2 ∂μN n + ∫ x, dk k η x ^ 2 ∂μN n := fun k => by
    rw [← integral_const_mul, ← integral_add (f := fun x => 1 / 4 * A k x ^ 2)
      (g := fun x => dk k η x ^ 2) ((hAL k).integrable_sq.const_mul _)
      (integrableN ((hdη k).pow 2))]
    refine integral_mono (int_mul_cont (hAL k) (hdη k))
      (((hAL k).integrable_sq.const_mul _).add (integrableN ((hdη k).pow 2))) fun x => ?_
    nlinarith [sq_nonneg (A k x - 2 * dk k η x)]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hAB k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hid : ∑ k, ∫ x, dWN k u x * dWN k φ x ∂μN n =
      2 * ∑ k, ∫ x, A k x * dk k η x ∂μN n - ∑ k, ∫ x, A k x ^ 2 ∂μN n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hk k
  change ∑ k, ∫ x, A k x ^ 2 ∂μN n ≤ _
  linarith

/-- The test function `logTest η u ε` is a bosonic Neumann state. -/
lemma logTest_memN {u : Cfg n → ℝ} (hu : u ∈ DomN .bos n) {η : Cfg n → ℝ}
    (hη : ContDiff ℝ 1 η) (hηs : ∀ σ x, η (pm σ x) = η x) {ε : ℝ} (hε : 0 < ε) :
    logTest η u ε ∈ DomN .bos n := by
  have hζ : ContDiff ℝ 1 fun x => η x * η x := hη.mul hη
  have hGc : Continuous (Gr ε) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_Gr hε t).continuousAt
  have hgL : MemLp (fun x => Gr ε (u x)) 2 (μN n) := MemLp.of_bound
    (hGc.comp_aestronglyMeasurable hu.1.aestronglyMeasurable) (1 / ε)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_Gr_le hε _)
  have hL1 : MemLp (fun x => ε⁻¹ * (η x * η x)) 2 (μN n) :=
    memLp_cont (continuous_const.mul hζ.continuous)
  have hL2 : MemLp (fun x => -1 * (η x * η x * Gr ε (u x))) 2 (μN n) :=
    (memLp_mul_cont hζ.continuous hgL).const_mul (-1)
  refine ⟨hL1.add hL2, fun k => ⟨_, IsWDN.add hL1 hL2 ((isWDN_of_C1 hζ k).const_mul ε⁻¹)
    (((isWDN_comp hu (hasDerivAt_Gr hε) (continuous_Gr' hε) (Gr'_le hε) Gr_zero
      k).mul_C1 hgL hζ).const_mul (-1))⟩, fun σ _ => ?_⟩
  filter_upwards [hu.2.2 σ trivial] with x hx
  simp only [ch_bos, one_mul] at hx ⊢
  simp only [logTest, hηs, hx]

/-! ### Pointwise algebra for the derivative of `η² u/(u + ε)` -/

lemma eG_identity {η dη D u ε : ℝ} (hp : 0 < u + ε) :
    η * η * (ε * (1 / (u + ε) ^ 2 * D)) + 2 * η * dη * (u / (u + ε)) =
      (η * (ε / (u + ε))) * (η * (D / (u + ε))) + (2 * η * (u / (u + ε))) * dη := by
  field_simp

lemma G_sq_le {η A d q r : ℝ} (hη : |η| ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) : ((η * q) * A + (2 * η * r) * d) ^ 2 ≤ 2 * A ^ 2 + 8 * d ^ 2 := by
  have hη2 : η ^ 2 ≤ 1 := by nlinarith [abs_nonneg η, sq_abs η]
  have hηq : (η * q) ^ 2 ≤ 1 := by
    rw [mul_pow]; nlinarith [sq_nonneg η, sq_nonneg q]
  have hηr : (2 * η * r) ^ 2 ≤ 4 := by
    have : (η * r) ^ 2 ≤ 1 := by rw [mul_pow]; nlinarith [sq_nonneg η, sq_nonneg r]
    nlinarith
  nlinarith [sq_nonneg ((η * q) * A - (2 * η * r) * d),
    mul_le_mul_of_nonneg_right hηq (sq_nonneg A), mul_le_mul_of_nonneg_right hηr (sq_nonneg d)]

/-- **The logarithmic estimate for `H⁻¹` potentials, from the weak equation.** Let `u ≥ 0` be a
symmetric Neumann `H¹` function satisfying the weak equation with energy `E` against Moser's test
function `φ = logTest η u ε`, with a potential term `v(e)` for some `e ∈ H1E` having the integrals
of `u φ`. For a symmetric `C¹` cutoff `|η| ≤ 1`, `Σ_k ∫ η² (∂ₖu/(u+ε))²` is bounded uniformly in
`ε > 0`. -/
theorem log_estimate_gen {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {u : Cfg n → ℝ}
    (hu : u ∈ DomN .bos n) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x) {η : Cfg n → ℝ}
    (hη : ContDiff ℝ 1 η) (hηs : ∀ σ x, η (pm σ x) = η x) (hη1 : ∀ᵐ x ∂μN n, |η x| ≤ 1)
    (E : ℝ) (hEL : ∀ ε > 0, ∃ e : H1E, (∀ u' : C01, ∫ t, iccExt u' t * iccExt (evE e) t ∂vol01 =
      ∫ x, (∑ k, iccExt u' (x k)) * (u x * logTest η u ε x) ∂μN n) ∧
      kinN2 u (logTest η u ε) + ∫ x, w x * (u x * logTest η u ε x) ∂μN n + v e =
        E * ∫ x, u x * logTest η u ε x ∂μN n) :
    ∃ K, 0 ≤ K ∧ ∀ ε > 0, ∑ k, ∫ x, (η x * (dWN k u x / (u x + ε))) ^ 2 ∂μN n ≤ K := by
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  set D := ∑ k, ∫ x, dk k η x ^ 2 ∂μN n
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  set K0 := |E| + max B 0 + (1 + 8 * D) / 8 + 4 * (n + 1) ^ 2 * ‖v‖ ^ 2
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨8 * D + 4 * K0, by positivity, fun ε hε => ?_⟩
  set S := ∑ k, ∫ x, (η x * (dWN k u x / (u x + ε))) ^ 2 ∂μN n
  set A : Fin (n + 1) → Cfg n → ℝ := fun k x => η x * (dWN k u x / (u x + ε))
  have hAL : ∀ k, MemLp (A k) 2 (μN n) := fun k => memLp_logA hu hu0 hη hε k
  have hA0 : ∫ x, A 0 x ^ 2 ∂μN n ≤ S :=
    Finset.single_le_sum (f := fun k => ∫ x, A k x ^ 2 ∂μN n)
      (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ 0)
  have hη0 : ∫ x, dk 0 η x ^ 2 ∂μN n ≤ D :=
    Finset.single_le_sum (f := fun k => ∫ x, dk k η x ^ 2 ∂μN n)
      (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ 0)
  -- the test function and the Euler–Lagrange equation
  set φ := logTest η u ε
  have hφD : φ ∈ DomN .bos n := logTest_memN hu hη hηs hε
  obtain ⟨e, hint, hel⟩ := hEL ε hε
  -- `u φ = p = η² ε Gr(u)` with its derivative
  set ζ : Cfg n → ℝ := fun x => η x * η x
  have hζ : ContDiff ℝ 1 ζ := hη.mul hη
  have hdζ : ∀ x, dk 0 ζ x = 2 * η x * dk 0 η x := fun x => by
    rw [dk_mul (hη.differentiable one_ne_zero) (hη.differentiable one_ne_zero)]; ring
  have hGc : Continuous (Gr ε) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_Gr hε t).continuousAt
  have hgL : MemLp (fun x => ε * Gr ε (u x)) 2 (μN n) := (MemLp.of_bound
    (hGc.comp_aestronglyMeasurable hu.1.aestronglyMeasurable) (1 / ε)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_Gr_le hε _)).const_mul ε
  set p : Cfg n → ℝ := fun x => ζ x * (ε * Gr ε (u x))
  set G : Cfg n → ℝ := fun x => ζ x * (ε * (1 / (|u x| + ε) ^ 2 * dWN 0 u x)) +
    dk 0 ζ x * (ε * Gr ε (u x))
  have hpG : IsWDN 0 p G :=
    ((isWDN_comp hu (hasDerivAt_Gr hε) (continuous_Gr' hε) (Gr'_le hε) Gr_zero
      0).const_mul ε).mul_C1 hgL hζ
  have hpL : MemLp p 2 (μN n) := memLp_mul_cont hζ.continuous hgL
  have hGr : ∀ t, 0 ≤ t → ε * Gr ε t = t / (t + ε) := fun t ht => by
    rw [Gr_of_nonneg ht]; field_simp; ring
  have hη2 : ∀ᵐ x ∂μN n, ζ x ≤ 1 := by
    filter_upwards [hη1] with x hx
    simp only [ζ]; nlinarith [abs_nonneg (η x), abs_mul_abs_self (η x)]
  have huφ : ∀ᵐ x ∂μN n, u x * φ x = p x := by
    filter_upwards [hu0] with x h0
    have hp : 0 < u x + ε := by linarith
    simp only [φ, p, ζ, logTest, Gr_of_nonneg h0]
    field_simp; ring
  have hp01 : ∀ᵐ x ∂μN n, 0 ≤ p x ∧ p x ≤ 1 := by
    filter_upwards [hu0, hη2] with x h0 hη2x
    have hp : 0 < u x + ε := by linarith
    have hr0 : 0 ≤ u x / (u x + ε) := div_nonneg h0 hp.le
    have hr1 : u x / (u x + ε) ≤ 1 := (div_le_one hp).2 (by linarith)
    simp only [p, hGr _ h0]
    exact ⟨mul_nonneg (mul_self_nonneg _) hr0,
      (mul_le_mul hη2x hr1 hr0 zero_le_one).trans (by norm_num)⟩
  have hpsym : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ᵐ x ∂μN n, p (pm σ x) = p x := fun σ => by
    filter_upwards [hu.2.2 σ trivial] with x hx
    simp only [ch_bos, one_mul] at hx
    simp only [p, ζ, hηs, hx]
  -- the mixed density is the density of `p`
  have he : ∀ u' : C01, ∫ t, iccExt u' t * iccExt (evE e) t ∂vol01 =
      ∫ t, iccExt u' t * ((n + 1) * mF p t) ∂vol01 := fun u' => by
    rw [hint u', int_mF (hpL.integrable one_le_two) hpsym]
    refine integral_congr_ae ?_
    filter_upwards [huφ] with x hx
    rw [hx]
  have hnorm := norm_sq_le_marg hpL hpG he
  -- `∫ p² ≤ 1`, `∫ G² ≤ 2 ∫ A₀² + 8 ∫ (∂₀η)²`
  have hvol : ∫ _x, (1 : ℝ) ∂μN n = 1 := by
    simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ, volume_cube]
  have hp2 : ∫ x, p x ^ 2 ∂μN n ≤ 1 := by
    calc ∫ x, p x ^ 2 ∂μN n ≤ ∫ _x, (1 : ℝ) ∂μN n :=
          integral_mono_ae (int_sq hpL) (integrable_const _) (by
            filter_upwards [hp01] with x hx
            nlinarith [hx.1, hx.2])
      _ = 1 := hvol
  have hdη := continuous_dk_of_C1 hη 0
  have hG2 : ∫ x, G x ^ 2 ∂μN n ≤ 2 * ∫ x, A 0 x ^ 2 ∂μN n + 8 * ∫ x, dk 0 η x ^ 2 ∂μN n := by
    have i1 : Integrable (fun x => 2 * A 0 x ^ 2 + 8 * dk 0 η x ^ 2) (μN n) :=
      ((hAL 0).integrable_sq.const_mul 2).add ((integrableN (hdη.pow 2)).const_mul 8)
    calc ∫ x, G x ^ 2 ∂μN n ≤ ∫ x, (2 * A 0 x ^ 2 + 8 * dk 0 η x ^ 2) ∂μN n := by
          refine integral_mono_ae (int_sq hpG.1) i1 ?_
          filter_upwards [hu0, hη1] with x h0 hη1x
          have hp : 0 < u x + ε := by linarith
          have eG : G x = (η x * (ε / (u x + ε))) * A 0 x +
              (2 * η x * (u x / (u x + ε))) * dk 0 η x := by
            simp only [G, A, ζ, hdζ, abs_of_nonneg h0, hGr _ h0]
            exact eG_identity hp
          rw [eG]
          exact G_sq_le hη1x (div_nonneg hε.le hp.le) ((div_le_one hp).2 (by linarith))
            (div_nonneg h0 hp.le) ((div_le_one hp).2 (by linarith))
      _ = 2 * ∫ x, A 0 x ^ 2 ∂μN n + 8 * ∫ x, dk 0 η x ^ 2 ∂μN n := by
          rw [integral_add (f := fun x => 2 * A 0 x ^ 2) (g := fun x => 8 * dk 0 η x ^ 2)
            ((hAL 0).integrable_sq.const_mul 2) ((integrableN (hdη.pow 2)).const_mul 8),
            integral_const_mul, integral_const_mul]
  -- `|v(ρ(u, φ))| ≤ ‖ρ‖² / (16 N²) + 4 N² ‖v‖²`
  have hN : (0 : ℝ) < (n + 1) ^ 2 := by positivity
  have hve : |v e| ≤ ‖e‖ ^ 2 / (16 * (n + 1) ^ 2) + 4 * (n + 1) ^ 2 * ‖v‖ ^ 2 := by
    have h1 : |v e| ≤ ‖v‖ * ‖e‖ := by rw [← Real.norm_eq_abs]; exact v.le_opNorm e
    have h2 : ‖v‖ * ‖e‖ ≤ ‖e‖ ^ 2 / (16 * (n + 1) ^ 2) + 4 * (n + 1) ^ 2 * ‖v‖ ^ 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖e‖ - 8 * (n + 1) ^ 2 * ‖v‖)]
    linarith
  have h4 : ∫ x, p x ^ 2 ∂μN n + ∫ x, G x ^ 2 ∂μN n ≤ 1 + 2 * S + 8 * D := by
    linarith [hp2, hG2, hA0, hη0]
  have h5 : ‖e‖ ^ 2 ≤ 2 * (n + 1) ^ 2 * (1 + 2 * S + 8 * D) :=
    hnorm.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
  have h3 : ‖e‖ ^ 2 / (16 * (n + 1) ^ 2) ≤ (1 + 8 * D) / 8 + S / 4 := by
    calc ‖e‖ ^ 2 / (16 * (n + 1) ^ 2) ≤ 2 * (n + 1) ^ 2 * (1 + 2 * S + 8 * D) /
          (16 * (n + 1) ^ 2) := div_le_div_of_nonneg_right h5 (by positivity)
      _ = (1 + 8 * D) / 8 + S / 4 := by field_simp; ring
  have hve' : |v e| ≤ (1 + 8 * D) / 8 + S / 4 + 4 * (n + 1) ^ 2 * ‖v‖ ^ 2 := by linarith
  -- `0 ≤ u φ ≤ 1`: the energy and interaction terms
  have iuφ := int_mul_L2 hu.1 hφD.1
  have hb1 : ∀ᵐ x ∂μN n, 0 ≤ u x * φ x ∧ u x * φ x ≤ 1 := by
    filter_upwards [huφ, hp01] with x h1 h2
    rw [h1]; exact h2
  have hI : 0 ≤ ∫ x, u x * φ x ∂μN n ∧ ∫ x, u x * φ x ∂μN n ≤ 1 := by
    refine ⟨integral_nonneg_of_ae (hb1.mono fun x hx => hx.1), ?_⟩
    calc ∫ x, u x * φ x ∂μN n ≤ ∫ _x, (1 : ℝ) ∂μN n :=
          integral_mono_ae iuφ (integrable_const _) (hb1.mono fun x hx => hx.2)
      _ = 1 := hvol
  have hW : |∫ x, w x * (u x * φ x) ∂μN n| ≤ max B 0 := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, w x * (u x * φ x) ∂μN n‖ ≤ ∫ x, max B 0 * (u x * φ x) ∂μN n := by
          refine norm_integral_le_of_norm_le (iuφ.const_mul _) ?_
          filter_upwards [hB, hb1] with x hx hx'
          rw [norm_mul, Real.norm_eq_abs (u x * φ x), abs_of_nonneg hx'.1]
          exact mul_le_mul_of_nonneg_right (hx.trans (le_max_left _ _)) hx'.1
      _ = max B 0 * ∫ x, u x * φ x ∂μN n := integral_const_mul _ _
      _ ≤ max B 0 * 1 := mul_le_mul_of_nonneg_left hI.2 (le_max_right _ _)
      _ = max B 0 := mul_one _
  have hE : |E * ∫ x, u x * φ x ∂μN n| ≤ |E| := by
    rw [abs_mul, abs_of_nonneg hI.1]
    calc |E| * ∫ x, u x * φ x ∂μN n ≤ |E| * 1 := mul_le_mul_of_nonneg_left hI.2 (abs_nonneg _)
      _ = |E| := mul_one _
  -- Moser
  have hK0def : K0 = |E| + max B 0 + (1 + 8 * D) / 8 + 4 * (n + 1) ^ 2 * ‖v‖ ^ 2 := rfl
  have hk2 : kinN2 u φ = ∑ k, ∫ x, dWN k u x * dWN k (logTest η u ε) x ∂μN n := rfl
  have hel' : kinN2 u φ = E * ∫ x, u x * φ x ∂μN n - ∫ x, w x * (u x * φ x) ∂μN n - v e := by
    linarith
  have hlow : -(K0 + S / 4) ≤ ∑ k, ∫ x, dWN k u x * dWN k (logTest η u ε) x ∂μN n := by
    rw [← hk2, hel', hK0def]
    linarith [neg_abs_le (E * ∫ x, u x * φ x ∂μN n), le_abs_self (∫ x, w x * (u x * φ x) ∂μN n),
      le_abs_self (v e)]
  have hcore := log_estimate_coreN hu hu0 hη hε hlow
  have hS : S = ∑ k, ∫ x, (η x * (dWN k u x / (u x + ε))) ^ 2 ∂μN n := rfl
  rw [← hS] at hcore
  linarith

/-- **The logarithmic estimate for `H⁻¹` potentials**: for a nonnegative bosonic Neumann ground
state `u` and a symmetric `C¹` cutoff `|η| ≤ 1`, `Σ_k ∫ η² (∂ₖu/(u+ε))²` is bounded uniformly in
`ε > 0`. -/
theorem log_estimate_H {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {u : Cfg n → ℝ}
    (hu : IsGSNH .bos w v u) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x) {η : Cfg n → ℝ}
    (hη : ContDiff ℝ 1 η) (hηs : ∀ σ x, η (pm σ x) = η x) (hη1 : ∀ x, |η x| ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ ε > 0, ∑ k, ∫ x, (η x * (dWN k u x / (u x + ε))) ^ 2 ∂μN n ≤ K :=
  log_estimate_gen hw hu.1 hu0 hη hηs (ae_of_all _ hη1) (QNH .bos w v u) fun ε hε =>
    ⟨rhoE2 .bos u (logTest η u ε), fun u' => int_rhoE2 hu.1 (logTest_memN hu.1 hη hηs hε) u',
      euler_lagrangeNH hw hu (logTest_memN hu.1 hη hηs hε)⟩

/-! ### The logarithmic data -/

/-- A nonnegative bosonic Neumann ground state, cut off by `ζ_a`, gives the logarithmic data on
`[a, 1 - a]ᴺ`. -/
theorem logData_H {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {u : Cfg n → ℝ}
    (hu : IsGSNH .bos w v u) (hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x) {a : ℝ} (ha : 0 < a)
    (ha2 : a ≤ 1 / 2) : LogData (fun x => zetaA ha ha2 x * u x) (Qa n a) := by
  have hζ := contDiff_zetaA (n := n) ha ha2
  have hζw : ∀ (x : Cfg n) (j : Fin (n + 1)), (x j = 0 ∨ x j = 1) → zetaA ha ha2 x = 0 :=
    fun x j h => zetaA_wall ha ha2 x j h
  have hWD : ∀ k, IsWD k (fun x => zetaA ha ha2 x * u x)
      (fun x => zetaA ha ha2 x * dWN k u x + dk k (zetaA ha ha2) x * u x) := fun k =>
    (dWN_spec (hu.1.2.1 k)).mul_cutoff hu.1.1 hζ hζw
  obtain ⟨K, hK0, hK⟩ := log_estimate_H hw hu hu0 (contDiff_etaA ha ha2) (etaA_pm ha ha2)
    (abs_etaA_le ha ha2)
  refine ⟨⟨memLp_mul_cont hζ.continuous hu.1.1, fun k => ⟨_, hWD k⟩⟩, ?_, measurableSet_Qa a,
    Qa_sub_cube ha, convex_Qa a, etaA ha ha2, (contDiff_etaA ha ha2).continuous, 1, one_pos,
    fun x hx => by rw [etaA_eq_one ha ha2 hx, abs_one], K, hK0, fun ε hε => ?_⟩
  · filter_upwards [hu0] with x h0
    exact mul_nonneg (zetaA_nonneg ha ha2 x) h0
  refine le_trans (le_of_eq ?_) (hK ε hε)
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [dW_ae_eq (hWD k)] with x hx
  rw [hx]
  by_cases h0 : etaA ha ha2 x = 0
  · simp [h0]
  · have hV := mem_Va_of_etaA ha ha2 h0
    rw [zetaA_eq_one ha ha2 hV, dk_zetaA ha ha2 hV, one_mul, one_mul, zero_mul, add_zero]

/-- **Bosonic Neumann ground states of `H⁻¹` potentials are nonzero almost everywhere.** -/
theorem gsNH_ne_zero_bos {w : Cfg n → ℝ} (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ}
    (hΨ : IsGSNH .bos w v Ψ) : ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  set u : Cfg n → ℝ := fun x => |Ψ x|
  have hu : IsGSNH .bos w v u := isGSNH_abs hΨ
  have hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x := ae_of_all _ fun x => abs_nonneg _
  have hum := hu.1.1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  set Z : Set (Cfg n) := {x | u' x = 0}
  have hZ : MeasurableSet Z := hu'm (measurableSet_singleton 0)
  have hv : ∀ᵐ x ∂volume, x ∈ Cube n → u x = u' x := (ae_restrict_iff' measurableSet_cube).1 hue
  have hinv : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ k (h : ℝ), 0 ≤ h →
      ∀ᵐ x ∂volume, x ∈ Sa n a h k → (x ∈ Z ↔ x + h • ek k ∈ Z) := by
    intro a ha ha2 k h hh
    have hQc := Qa_sub_cube (n := n) ha
    have hv' := (measurePreserving_add_right volume (h • ek k)).quasiMeasurePreserving.ae hv
    filter_upwards [(logData_H hw hu hu0 ha ha2).zero_set_translate k hh, hv, hv']
      with x hx h1 h2 hxS
    simp only [Z, mem_ofPred_eq]
    rw [← h1 (hQc hxS.1), ← h2 (hQc hxS.2)]
    have hx' := hx hxS
    rwa [zetaA_eq_one ha ha2 (Qa_sub_Va ha hxS.1),
      zetaA_eq_one ha ha2 (Qa_sub_Va ha hxS.2), one_mul, one_mul] at hx'
  rcases null_or_conull hZ hinv with h | h
  · exfalso
    have hz : ∀ᵐ x ∂μN n, u x ^ 2 = 0 := by
      filter_upwards [h, hue] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rw [he, hx]; ring
    have : ∫ x, u x ^ 2 ∂μN n = 0 := integral_eq_zero_of_ae hz
    rw [hu.2.1] at this; exact one_ne_zero this
  · filter_upwards [h, hue] with x hx he
    simp only [Z, mem_ofPred_eq] at hx
    rw [← he] at hx
    exact abs_ne_zero.1 hx

end DFT.Continuum.Line
