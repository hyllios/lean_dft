/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.GroundState.Realize

/-!
# Approximation of `H¹₀` states by `C²` states

For `Φ ∈ H¹₀` the sine truncations `P_M` (`C²` states, `Line/Complete`) satisfy

* `P_M → Φ` in `L²` (`tendsto_trunc`), and
* `∂ₖ P_M ⇀ ∂ₖ Φ` **weakly** in `L²`, with `‖∂ₖ P_M‖² ≤ T(Φ)` (`tendsto_trunc_dk`).

The weak convergence needs no completeness of the cosines: on the sine basis,
`⟨s_m, ∂ₖ P_M⟩ = -π(m_k+1) ⟨c^k_m, P_M⟩ → -π(m_k+1) ⟨c^k_m, Φ⟩ = ⟨s_m, ∂ₖ Φ⟩` (integration by parts
on both sides), and a bounded sequence converging on a Hilbert basis converges weakly
(`tendsto_inner_of_basis`). This is the approximation used for chain rules in `H¹₀`.

* `tendsto_inner_of_basis`: weak convergence from convergence on a Hilbert basis.
* `tendsto_integral_mul_of_L2`: `L²` convergence passes to integrals against `L²` functions.
* `norm_dk_trunc_sq_le`: `∫ (∂ₖ P_M)² ≤ T(Φ)`.
* **`tendsto_trunc_dk`**: `∫ g ∂ₖ P_M → ∫ g ∂ₖ Φ` for every `g ∈ L²`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

/-- **Weak convergence from convergence on a Hilbert basis**, for a bounded sequence. -/
theorem tendsto_inner_of_basis {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : HilbertBasis ι ℝ E) {x : ℕ → E} {x0 : E} {C : ℝ} (hC : ∀ M, ‖x M‖ ≤ C)
    (hb : ∀ i, Tendsto (fun M => inner ℝ (b i) (x M)) atTop (𝓝 (inner ℝ (b i) x0))) (y : E) :
    Tendsto (fun M => inner ℝ y (x M)) atTop (𝓝 (inner ℝ y x0)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K := C + ‖x0‖ + 1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hK : 0 < K := by positivity
  obtain ⟨s, hs⟩ := Metric.tendsto_atTop.1 (b.hasSum_repr y) (ε / (2 * K)) (by positivity)
  set ys := ∑ i ∈ s, b.repr y i • b i
  have hys : ‖y - ys‖ < ε / (2 * K) := by
    have := hs s le_rfl
    rwa [dist_eq_norm, norm_sub_rev] at this
  have hfin : Tendsto (fun M => inner ℝ ys (x M)) atTop (𝓝 (inner ℝ ys x0)) := by
    simp only [ys, sum_inner, real_inner_smul_left]
    exact tendsto_finsetSum s fun i _ => (hb i).const_mul _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hfin (ε / 2) (half_pos hε)
  refine ⟨N, fun M hM => ?_⟩
  have h1 := hN M hM
  rw [Real.dist_eq] at h1 ⊢
  have key : inner ℝ y (x M) - inner ℝ y x0 =
      inner ℝ (y - ys) (x M - x0) + (inner ℝ ys (x M) - inner ℝ ys x0) := by
    simp only [inner_sub_left, inner_sub_right]; ring
  have h2 : |inner ℝ (y - ys) (x M - x0)| ≤ ‖y - ys‖ * K := by
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    linarith [norm_sub_le (x M) x0, hC M]
  have h3 : ‖y - ys‖ * K ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_right hys.le hK.le
    rwa [div_mul_eq_mul_div, mul_comm 2 K, ← div_div, mul_div_cancel_right₀ _ hK.ne'] at this
  rw [key]
  calc |inner ℝ (y - ys) (x M - x0) + (inner ℝ ys (x M) - inner ℝ ys x0)|
      ≤ |inner ℝ (y - ys) (x M - x0)| + |inner ℝ ys (x M) - inner ℝ ys x0| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := add_halves ε

/-- `L²` convergence passes to integrals against `L²` functions. -/
lemma tendsto_integral_mul_of_L2 {f : ℕ → Cfg n → ℝ} {f0 g : Cfg n → ℝ}
    (hf : ∀ M, MemLp (f M) 2 (μN n)) (hf0 : MemLp f0 2 (μN n)) (hg : MemLp g 2 (μN n))
    (h : Tendsto (fun M => ∫ x, (f0 x - f M x) ^ 2 ∂μN n) atTop (𝓝 0)) :
    Tendsto (fun M => ∫ x, f M x * g x ∂μN n) atTop (𝓝 (∫ x, f0 x * g x ∂μN n)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun M => √(∫ x, (f0 x - f M x) ^ 2 ∂μN n) * ‖hg.toLp g‖) atTop (𝓝 0) := by
    simpa using (h.sqrt).mul_const ‖hg.toLp g‖
  refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) hb
  have hd : MemLp (fun x => f0 x - f M x) 2 (μN n) := hf0.sub (hf M)
  have e : ∫ x, f M x * g x ∂μN n - ∫ x, f0 x * g x ∂μN n =
      -inner ℝ (hd.toLp _) (hg.toLp g) := by
    rw [inner_toLp_toLp, ← integral_sub (int_mul_L2 (hf M) hg) (int_mul_L2 hf0 hg), ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e, norm_neg, Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans (le_of_eq ?_)
  congr 1
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_toLp]

/-- `⟨s_m, ∂ₖ P_M⟩ = -π(m_k+1) ⟨c^k_m, P_M⟩`, and the same for `Φ`. -/
lemma integral_smd_dk (k : Fin (n + 1)) (m : Fin (n + 1) → ℕ) {Ψ G : Cfg n → ℝ}
    (hG : IsWD k Ψ G) :
    ∫ x, smd m x * G x ∂μN n = -(π * (m k + 1)) * ∫ x, Ψ x * cmd k m x ∂μN n := by
  have h := hG.2 (smd m) ((contDiff_smd m).of_le (by norm_num))
  have e1 : ∫ x, Ψ x * dk k (smd m) x ∂μN n = π * (m k + 1) * ∫ x, Ψ x * cmd k m x ∂μN n := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [dk_smd]; ring)
  have e2 : ∫ x, smd m x * G x ∂μN n = ∫ x, G x * smd m x ∂μN n :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [e2]
  linarith

section trunc

variable {Φ : Cfg n → ℝ} (hΦ : H1W Φ)
include hΦ

/-- The truncations have kinetic energy at most that of `Φ`, in each direction. -/
lemma norm_dk_trunc_sq_le (k : Fin (n + 1)) (M : ℕ) :
    ∫ x, dk k (trunc M Φ) x ^ 2 ∂μN n ≤ kinW Φ := by
  have hc : ∀ k, Continuous (dk k (trunc M Φ)) := fun k =>
    continuous_dk_of_C1 ((contDiff_trunc M Φ).of_le (by norm_num)) k
  have h := kin_trunc_le hΦ M
  rw [integral_finsetSum (f := fun k x => dk k (trunc M Φ) x * dk k (trunc M Φ) x) _
    fun k _ => integrableN ((hc k).mul (hc k))] at h
  refine le_trans ?_ h
  have := Finset.single_le_sum (f := fun k => ∫ x, dk k (trunc M Φ) x * dk k (trunc M Φ) x ∂μN n)
    (fun k _ => integral_nonneg fun x => mul_self_nonneg _) (Finset.mem_univ k)
  refine le_trans (le_of_eq ?_) this
  exact integral_congr_ae (ae_of_all _ fun x => sq _)

/-- **Weak convergence of the derivatives of the truncations.** -/
theorem tendsto_trunc_dk (k : Fin (n + 1)) {g : Cfg n → ℝ} (hg : MemLp g 2 (μN n)) :
    Tendsto (fun M => ∫ x, g x * dk k (trunc M Φ) x ∂μN n) atTop
      (𝓝 (∫ x, g x * dW k Φ x ∂μN n)) := by
  have hPm : ∀ M, MemLp (dk k (trunc M Φ)) 2 (μN n) := fun M =>
    memLp_cont (continuous_dk_of_C1 ((contDiff_trunc M Φ).of_le (by norm_num)) k)
  have hW := dW_spec (hΦ.2 k)
  set x : ℕ → HN n := fun M => (hPm M).toLp _
  set x0 : HN n := hW.1.toLp _
  have hC : ∀ M, ‖x M‖ ≤ √(kinW Φ) := fun M => by
    refine Real.le_sqrt_of_sq_le ?_
    rw [norm_sq_toLp]
    exact norm_dk_trunc_sq_le hΦ k M
  have hb : ∀ m, Tendsto (fun M => inner ℝ (bN m) (x M)) atTop (𝓝 (inner ℝ (bN m) x0)) := by
    intro m
    simp only [bN_apply, x, x0, eN, inner_toLp_toLp]
    rw [integral_smd_dk k m hW]
    simp only [fun M => integral_smd_dk k m (isWD_of_C2 (contDiff_trunc M Φ) (trunc_wall M Φ) k)]
    refine Tendsto.const_mul _ ?_
    exact tendsto_integral_mul_of_L2 (fun M => memLp_cont (continuous_trunc M Φ)) hΦ.1
      (memLp_cont (contDiff_cmd k m).continuous) (tendsto_trunc hΦ.1)
  have h := tendsto_inner_of_basis bN hC hb (hg.toLp g)
  simp only [x, x0, inner_toLp_toLp] at h
  exact h

end trunc

end DFT.Continuum.Line
