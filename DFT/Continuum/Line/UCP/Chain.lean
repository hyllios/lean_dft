/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.UCP.H1Approx

/-!
# The chain rule in `H¹₀`

For `Φ ∈ H¹₀` and `G ∈ C¹(ℝ)` with `|G'| ≤ L` and `G(0) = 0`,
`∂ₖ (G ∘ Φ) = G'(Φ) ∂ₖ Φ` weakly (`isWD_comp`).

Proof: for the `C²` truncations `P_M` the identity is classical (`isWD_of_C1`; `G ∘ P_M` vanishes on
the walls because `G(0) = 0`). Along a subsequence `P_M → Φ` a.e. (`exists_ae_subseq`). Then
* `G(P_M) → G(Φ)` in `L²` (`G` is `L`-Lipschitz);
* `G'(P_M) ∂ₖ P_M φ = (G'(P_M) - G'(Φ)) φ · ∂ₖ P_M + G'(Φ) φ · ∂ₖ P_M`: the first term is at most
  `‖(G'(P_M) - G'(Φ)) φ‖₂ · T(Φ)^{1/2} → 0` (dominated convergence), the second converges by the
  weak convergence `∂ₖ P_M ⇀ ∂ₖ Φ` (`tendsto_trunc_dk`).

* `abs_integral_mul_le`: Cauchy–Schwarz on the cube.
* `exists_ae_subseq`: `L²` convergence has an a.e. convergent subsequence.
* **`isWD_comp`**: the chain rule.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-- Cauchy–Schwarz on the cube. -/
lemma abs_integral_mul_le {f g : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (hg : MemLp g 2 (μN n)) :
    |∫ x, f x * g x ∂μN n| ≤ √(∫ x, f x ^ 2 ∂μN n) * √(∫ x, g x ^ 2 ∂μN n) := by
  have e1 : ‖hf.toLp f‖ = √(∫ x, f x ^ 2 ∂μN n) := by
    rw [← norm_sq_toLp hf, Real.sqrt_sq (norm_nonneg _)]
  have e2 : ‖hg.toLp g‖ = √(∫ x, g x ^ 2 ∂μN n) := by
    rw [← norm_sq_toLp hg, Real.sqrt_sq (norm_nonneg _)]
  rw [← inner_toLp_toLp hf hg, ← e1, ← e2]
  exact abs_real_inner_le_norm _ _

/-- `L²` convergence has an a.e. convergent subsequence. -/
lemma exists_ae_subseq {f : ℕ → Cfg n → ℝ} {f0 : Cfg n → ℝ} (hf : ∀ M, MemLp (f M) 2 (μN n))
    (hf0 : MemLp f0 2 (μN n)) (h : Tendsto (fun M => ∫ x, (f0 x - f M x) ^ 2 ∂μN n) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μN n, Tendsto (fun j => f (ns j) x) atTop (𝓝 (f0 x)) := by
  refine TendstoInMeasure.exists_seq_tendsto_ae
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ?_)
  have e : ∀ M, eLpNorm (f M - f0) 2 (μN n) =
      ENNReal.ofReal √(∫ x, (f0 x - f M x) ^ 2 ∂μN n) := fun M => by
    have hd : MemLp (f M - f0) 2 (μN n) := (hf M).sub hf0
    rw [← ENNReal.ofReal_toReal hd.eLpNorm_ne_top, ← Lp.norm_toLp _ hd]
    congr 1
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_toLp hd]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
  simp only [e]
  simpa using ENNReal.tendsto_ofReal h.sqrt

/-- **The chain rule in `H¹₀`**: `∂ₖ (G ∘ Φ) = G'(Φ) ∂ₖ Φ` for `G ∈ C¹`, `|G'| ≤ L`, `G(0) = 0`. -/
theorem isWD_comp {Φ : Cfg n → ℝ} (hΦ : H1W Φ) {G G' : ℝ → ℝ}
    (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G') {L : ℝ} (hL : ∀ t, |G' t| ≤ L)
    (hG0 : G 0 = 0) (k : Fin (n + 1)) :
    IsWD k (fun x => G (Φ x)) (fun x => G' (Φ x) * dW k Φ x) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hGd : Differentiable ℝ G := fun t => (hG t).differentiableAt
  have hderiv : deriv G = G' := funext fun t => (hG t).deriv
  have hGC1 : ContDiff ℝ 1 G := contDiff_one_iff_deriv.2 ⟨hGd, hderiv ▸ hG'c⟩
  have hLip : ∀ a b, |G a - G b| ≤ L * |a - b| := by
    have hl := lipschitzWith_of_nnnorm_deriv_le (C := L.toNNReal) hGd (fun x => by
      rw [hderiv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hL0]
      exact hL x)
    intro a b
    have h := hl.dist_le_mul a b
    rwa [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0] at h
  have hGb : ∀ t, |G t| ≤ L * |t| := fun t => by simpa [hG0] using hLip t 0
  have hW := dW_spec (hΦ.2 k)
  have hΦm := hΦ.1.aestronglyMeasurable
  have hGΦ : MemLp (fun x => G (Φ x)) 2 (μN n) :=
    hΦ.1.of_le_mul (c := L) (hGC1.continuous.comp_aestronglyMeasurable hΦm)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hGb _)
  have hG'Φm : AEStronglyMeasurable (fun x => G' (Φ x)) (μN n) :=
    hG'c.comp_aestronglyMeasurable hΦm
  have hG'Φ : MemLp (fun x => G' (Φ x)) 2 (μN n) :=
    MemLp.of_bound hG'Φm L (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hL _)
  refine ⟨hW.1.of_le_mul (c := L) (hG'Φm.mul hW.1.aestronglyMeasurable) (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)), fun φ hφ => ?_⟩
  set P : ℕ → Cfg n → ℝ := fun M => trunc M Φ with hPdef
  have hP2 : ∀ M, ContDiff ℝ 2 (P M) := fun M => contDiff_trunc M Φ
  have hPw : ∀ M, ∀ x j, (x j = 0 ∨ x j = 1) → P M x = 0 := fun M => trunc_wall M Φ
  have hPc : ∀ M, Continuous (P M) := fun M => continuous_trunc M Φ
  -- the classical identity for the truncations
  have hM : ∀ M, ∫ x, G (P M x) * dk k φ x ∂μN n =
      -∫ x, G' (P M x) * dk k (P M) x * φ x ∂μN n := fun M => by
    have hC1 : ContDiff ℝ 1 (fun x => G (P M x)) := hGC1.comp ((hP2 M).of_le (by norm_num))
    have hface : ∀ x j, (x j = 0 ∨ x j = 1) → G (P M x) = 0 := fun x j hj => by
      rw [hPw M x j hj, hG0]
    have h := (isWD_of_C1 hC1 hface k).2 φ hφ
    have hdk : ∀ x, dk k (fun x => G (P M x)) x = G' (P M x) * dk k (P M) x := fun x => by
      have hf := (((hP2 M).differentiable (by norm_num)) x).hasFDerivAt
      have h2 := ((hG (P M x)).comp_hasFDerivAt x hf).fderiv
      simp only [dk]
      rw [show (fun x => G (P M x)) = G ∘ P M from rfl, h2]
      simp
    simp only [hdk] at h
    exact h
  -- a subsequence converging a.e.
  have hL2 := tendsto_trunc hΦ.1
  obtain ⟨ns, hns, hae⟩ := exists_ae_subseq (fun M => memLp_cont (hPc M)) hΦ.1 hL2
  have hL2s : Tendsto (fun j => ∫ x, (Φ x - P (ns j) x) ^ 2 ∂μN n) atTop (𝓝 0) :=
    hL2.comp hns.tendsto_atTop
  have hdφ := continuous_dk_of_C1 hφ k
  -- the left side
  have hlhs : Tendsto (fun j => ∫ x, G (P (ns j) x) * dk k φ x ∂μN n) atTop
      (𝓝 (∫ x, G (Φ x) * dk k φ x ∂μN n)) := by
    refine tendsto_integral_mul_of_L2 (f := fun j x => G (P (ns j) x))
      (fun j => memLp_cont (hGC1.continuous.comp (hPc _))) hGΦ (memLp_cont hdφ) ?_
    refine squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _) (fun j => ?_)
      (by simpa using hL2s.const_mul (L ^ 2))
    rw [← integral_const_mul]
    have hint : Integrable (fun x => L ^ 2 * (Φ x - P (ns j) x) ^ 2) (μN n) := by
      have := ((hΦ.1.sub (memLp_cont (hPc (ns j)))).integrable_sq).const_mul (L ^ 2)
      simpa only [Pi.sub_apply] using this
    refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hint
      (ae_of_all _ fun x => ?_)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hLip (Φ x) (P (ns j) x)) 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    exact h2
  -- the right side, split in two
  obtain ⟨B, hB⟩ := ae_bound_cont hφ.continuous
  set g2 : Cfg n → ℝ := fun x => G' (Φ x) * φ x
  have hg2 : MemLp g2 2 (μN n) := by
    have := memLp_mul_cont hφ.continuous hG'Φ
    simpa only [g2, mul_comm] using this
  set D : ℕ → Cfg n → ℝ := fun j x => (G' (P (ns j) x) - G' (Φ x)) * φ x
  have hDm : ∀ j, MemLp (D j) 2 (μN n) := fun j => by
    have h1 : MemLp (fun x => G' (P (ns j) x) - G' (Φ x)) 2 (μN n) :=
      (memLp_cont (hG'c.comp (hPc _))).sub hG'Φ
    simpa only [D, mul_comm] using memLp_mul_cont hφ.continuous h1
  have hdP : ∀ j, MemLp (dk k (P (ns j))) 2 (μN n) := fun j =>
    memLp_cont (continuous_dk_of_C1 ((hP2 _).of_le (by norm_num)) k)
  have hsplit : ∀ j, ∫ x, G' (P (ns j) x) * dk k (P (ns j)) x * φ x ∂μN n =
      ∫ x, D j x * dk k (P (ns j)) x ∂μN n + ∫ x, g2 x * dk k (P (ns j)) x ∂μN n := fun j => by
    rw [← integral_add (int_mul_L2 (hDm j) (hdP j)) (int_mul_L2 hg2 (hdP j))]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [D, g2]; ring)
  have hDlim : Tendsto (fun j => ∫ x, D j x ^ 2 ∂μN n) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂μN n := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * L * B) ^ 2)
      (fun j => ((hDm j).aestronglyMeasurable.pow 2)) (integrable_const _) (fun j => ?_) ?_
    · filter_upwards [hB] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : |G' (P (ns j) x) - G' (Φ x)| ≤ 2 * L := by
        have := abs_sub (G' (P (ns j) x)) (G' (Φ x)); linarith [hL (P (ns j) x), hL (Φ x)]
      have h2 : |D j x| ≤ 2 * L * B := by
        simp only [D, abs_mul]
        rw [Real.norm_eq_abs] at hx
        exact mul_le_mul h1 hx (abs_nonneg _) (by positivity)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    · filter_upwards [hae] with x hx
      have h1 := ((hG'c.tendsto (Φ x)).comp hx).sub_const (G' (Φ x))
      have h2 := (h1.mul_const (φ x)).pow 2
      simpa [D] using h2
  have hT1 : Tendsto (fun j => ∫ x, D j x * dk k (P (ns j)) x ∂μN n) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => ?_)
      (by simpa using (hDlim.sqrt).mul_const √(kinW Φ))
    refine (abs_integral_mul_le (hDm j) (hdP j)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    exact norm_dk_trunc_sq_le hΦ k (ns j)
  have hT2 : Tendsto (fun j => ∫ x, g2 x * dk k (P (ns j)) x ∂μN n) atTop
      (𝓝 (∫ x, g2 x * dW k Φ x ∂μN n)) :=
    (tendsto_trunc_dk hΦ k hg2).comp hns.tendsto_atTop
  have hrhs := hT1.add hT2
  rw [zero_add] at hrhs
  have heq : (fun j => ∫ x, G (P (ns j) x) * dk k φ x ∂μN n) =
      fun j => -(∫ x, D j x * dk k (P (ns j)) x ∂μN n +
        ∫ x, g2 x * dk k (P (ns j)) x ∂μN n) := funext fun j => by rw [hM, hsplit]
  rw [heq] at hlhs
  have := tendsto_nhds_unique hlhs hrhs.neg
  rw [this]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [g2]; ring)

end DFT.Continuum.Line
