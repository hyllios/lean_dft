/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.UCP.Chain

/-!
# `|Φ|` in `H¹₀` and the first Perron–Frobenius step

For `Φ ∈ H¹₀`, `|Φ| ∈ H¹₀` with weak derivatives `rsgn(Φ) ∂ₖΦ` (`isWD_abs`): apply the chain rule
(`isWD_comp`) to `G_ε(t) = √(t² + ε²) - ε` and let `ε → 0` by dominated convergence. Hence the
kinetic energy of `|Φ|` is at most that of `Φ` (`kinW_abs_le`), and for bosons `|Ψ|` is a ground
state whenever `Ψ` is (`isGS_abs`).

* `rsgn`, `Geps`, `Geps'`: the sign function and the smoothings of `|t|`.
* **`isWD_abs`**, `abs_mem_DomW` (`|Φ|` is a bosonic `H¹₀` state for either statistics),
  `kinW_abs_le`, **`isGS_abs`**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat}

/-- The sign function. -/
noncomputable def rsgn (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then -1 else 0

lemma abs_rsgn_le (t : ℝ) : |rsgn t| ≤ 1 := by
  unfold rsgn; split_ifs <;> norm_num

lemma rsgn_mul_self (t : ℝ) : rsgn t * t = |t| := by
  unfold rsgn; split_ifs with h1 h2
  · rw [abs_of_pos h1, one_mul]
  · rw [abs_of_neg h2]; ring
  · have : t = 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    simp [this]

/-- `G_ε(t) = √(t² + ε²) - ε`. -/
noncomputable def Geps (ε t : ℝ) : ℝ := √(t ^ 2 + ε ^ 2) - ε

/-- `G_ε'(t) = t / √(t² + ε²)`. -/
noncomputable def Geps' (ε t : ℝ) : ℝ := t / √(t ^ 2 + ε ^ 2)

section eps

variable {ε : ℝ} (hε : 0 < ε)
include hε

lemma sqrt_pos_geps (t : ℝ) : 0 < √(t ^ 2 + ε ^ 2) := Real.sqrt_pos.2 (by positivity)

lemma hasDerivAt_Geps (t : ℝ) : HasDerivAt (Geps ε) (Geps' ε t) t := by
  have h := (((hasDerivAt_pow 2 t).add_const (ε ^ 2)).sqrt (by positivity)).sub_const ε
  refine h.congr_deriv ?_
  have := (sqrt_pos_geps hε t).ne'
  simp only [Geps']
  field_simp
  push_cast; ring

lemma continuous_Geps' : Continuous (Geps' ε) :=
  continuous_id.div (by fun_prop) fun t => (sqrt_pos_geps hε t).ne'

lemma abs_Geps'_le (t : ℝ) : |Geps' ε t| ≤ 1 := by
  have hp := sqrt_pos_geps hε t
  rw [Geps', abs_div, abs_of_pos hp, div_le_one hp]
  calc |t| = √(t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ √(t ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

lemma Geps_zero : Geps ε 0 = 0 := by
  simp [Geps, Real.sqrt_sq hε.le]

lemma abs_Geps_le (t : ℝ) : |Geps ε t| ≤ |t| := by
  have h1 : ε ≤ √(t ^ 2 + ε ^ 2) := by
    calc ε = √(ε ^ 2) := (Real.sqrt_sq hε.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have h2 : √(t ^ 2 + ε ^ 2) ≤ |t| + ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs t, abs_nonneg t]
  rw [Geps, abs_of_nonneg (by linarith)]
  linarith

end eps

lemma tendsto_Geps (t : ℝ) :
    Tendsto (fun j : ℕ => Geps (1 / ((j : ℝ) + 1)) t) atTop (𝓝 |t|) := by
  have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := ((((h0.pow 2).const_add (t ^ 2)).sqrt).sub h0)
  have e : √(t ^ 2 + (0 : ℝ) ^ 2) - 0 = |t| := by simp [Real.sqrt_sq_eq_abs]
  rw [e] at h
  exact h

lemma tendsto_Geps' (t : ℝ) :
    Tendsto (fun j : ℕ => Geps' (1 / ((j : ℝ) + 1)) t) atTop (𝓝 (rsgn t)) := by
  have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; simp [Geps', rsgn]
  have hs : Tendsto (fun j : ℕ => √(t ^ 2 + (1 / ((j : ℝ) + 1)) ^ 2)) atTop (𝓝 |t|) := by
    have h := ((h0.pow 2).const_add (t ^ 2)).sqrt
    have e : √(t ^ 2 + (0 : ℝ) ^ 2) = |t| := by simp [Real.sqrt_sq_eq_abs]
    rw [e] at h
    exact h
  have h := (tendsto_const_nhds (x := t)).div hs (abs_ne_zero.2 ht)
  have e : t / |t| = rsgn t := by
    rcases lt_or_gt_of_ne ht with h1 | h1
    · rw [abs_of_neg h1, div_neg, div_self ht]; simp [rsgn, h1, not_lt.2 h1.le]
    · rw [abs_of_pos h1, div_self ht]; simp [rsgn, h1]
  rw [e] at h
  exact h

/-- **`|Φ|` has weak derivatives `rsgn(Φ) ∂ₖΦ`.** -/
theorem isWD_abs {Φ : Cfg n → ℝ} (hΦ : H1W Φ) (k : Fin (n + 1)) :
    IsWD k (fun x => |Φ x|) (fun x => rsgn (Φ x) * dW k Φ x) := by
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε : ∀ j, 0 < ε j := fun j => by positivity
  have hW := dW_spec (hΦ.2 k)
  have hcomp : ∀ j, IsWD k (fun x => Geps (ε j) (Φ x)) (fun x => Geps' (ε j) (Φ x) * dW k Φ x) :=
    fun j => isWD_comp hΦ (hasDerivAt_Geps (hε j)) (continuous_Geps' (hε j))
      (abs_Geps'_le (hε j)) (Geps_zero (hε j)) k
  have hlimD : ∀ x, Tendsto (fun j => Geps' (ε j) (Φ x) * dW k Φ x) atTop
      (𝓝 (rsgn (Φ x) * dW k Φ x)) := fun x => (tendsto_Geps' (Φ x)).mul_const _
  have hmeas : AEStronglyMeasurable (fun x => rsgn (Φ x) * dW k Φ x) (μN n) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hcomp j).1.aestronglyMeasurable)
      (ae_of_all _ hlimD)
  refine ⟨hW.1.of_le_mul (c := 1) hmeas (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_rsgn_le _) (abs_nonneg _)), fun φ hφ => ?_⟩
  have hdφ := continuous_dk_of_C1 hφ k
  have hlhs : Tendsto (fun j => ∫ x, Geps (ε j) (Φ x) * dk k φ x ∂μN n) atTop
      (𝓝 (∫ x, |Φ x| * dk k φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |Φ x| * |dk k φ x|)
      (fun j => (((continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_Geps (hε j) t).continuousAt).comp_aestronglyMeasurable
        hΦ.1.aestronglyMeasurable).mul hdφ.aestronglyMeasurable)) ?_
      (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => (tendsto_Geps (Φ x)).mul_const _)
    · have := (int_mul_cont hΦ.1 hdφ).norm
      simpa [Real.norm_eq_abs, abs_mul] using this
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_Geps_le (hε j) _) (abs_nonneg _)
  have hrhs : Tendsto (fun j => ∫ x, Geps' (ε j) (Φ x) * dW k Φ x * φ x ∂μN n) atTop
      (𝓝 (∫ x, rsgn (Φ x) * dW k Φ x * φ x ∂μN n)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |dW k Φ x| * |φ x|)
      (fun j => ((hcomp j).1.aestronglyMeasurable.mul hφ.continuous.aestronglyMeasurable)) ?_
      (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => (hlimD x).mul_const _)
    · have := (int_mul_cont hW.1 hφ.continuous).norm
      simpa [Real.norm_eq_abs, abs_mul] using this
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (abs_nonneg _) (abs_Geps'_le (hε j) _)) (abs_nonneg _)
  have heq : (fun j => ∫ x, Geps (ε j) (Φ x) * dk k φ x ∂μN n) =
      fun j => -∫ x, Geps' (ε j) (Φ x) * dW k Φ x * φ x ∂μN n :=
    funext fun j => (hcomp j).2 φ hφ
  rw [heq] at hlhs
  exact tendsto_nhds_unique hlhs hrhs.neg

lemma abs_ch (τ : Stat) (σ : Equiv.Perm (Fin (n + 1))) : |ch τ σ| = 1 := by
  have h := ch_mul_self τ σ
  have h2 : |ch τ σ| * |ch τ σ| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg (ch τ σ)]

/-- `|Φ|` is a bosonic `H¹₀` state, for either statistics of `Φ`. -/
theorem abs_mem_DomW {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) :
    (fun x => |Φ x|) ∈ DomW .bos n :=
  ⟨hΦ.1.abs, fun k => ⟨_, isWD_abs (h1W_of_mem hΦ) k⟩, fun σ _ => by
    filter_upwards [hΦ.2.2 σ trivial] with x hx
    rw [hx, abs_mul, abs_ch, ch_bos]⟩

/-- **Kato's inequality in `H¹₀`**: `T(|Φ|) ≤ T(Φ)`. -/
theorem kinW_abs_le {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) : kinW (fun x => |Φ x|) ≤ kinW Φ := by
  refine Finset.sum_le_sum fun k _ => ?_
  have hd := dW_ae_eq (isWD_abs (h1W_of_mem hΦ) k)
  have hm := memLp_dW hΦ k
  have e : ∫ x, dW k (fun x => |Φ x|) x * dW k (fun x => |Φ x|) x ∂μN n =
      ∫ x, (rsgn (Φ x) * dW k Φ x) * (rsgn (Φ x) * dW k Φ x) ∂μN n :=
    integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx])
  rw [e]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_self_nonneg _) (int_mul_L2 hm hm)
    (ae_of_all _ fun x => ?_)
  have h1 : rsgn (Φ x) * rsgn (Φ x) ≤ 1 := by
    have := abs_rsgn_le (Φ x)
    nlinarith [abs_mul_abs_self (rsgn (Φ x)), abs_nonneg (rsgn (Φ x))]
  have h2 := mul_self_nonneg (dW k Φ x)
  calc rsgn (Φ x) * dW k Φ x * (rsgn (Φ x) * dW k Φ x) =
      (rsgn (Φ x) * rsgn (Φ x)) * (dW k Φ x * dW k Φ x) := by ring
    _ ≤ 1 * (dW k Φ x * dW k Φ x) := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

/-- **Perron–Frobenius, first step**: for bosons, `|Ψ|` is a ground state whenever `Ψ` is. -/
theorem isGS_abs {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {Ψ : Cfg n → ℝ}
    (hΨ : IsGS (settingW .bos n w hw) v Ψ) : IsGS (settingW .bos n w hw) v (fun x => |Ψ x|) := by
  have hD := abs_mem_DomW hΨ.1
  have hip : ip (μ := μN n) (fun x => |Ψ x|) (fun x => |Ψ x|) = ip (μ := μN n) Ψ Ψ := by
    simp only [ip, abs_mul_abs_self]
  have hQ : Q (settingW .bos n w hw) v (fun x => |Ψ x|) ≤ Q (settingW .bos n w hw) v Ψ := by
    rw [QW_eq v hD, QW_eq v hΨ.1]
    simp only [abs_mul_abs_self]
    linarith [kinW_abs_le hΨ.1]
  refine ⟨hD, hip ▸ hΨ.2.1, fun φ hφ => ?_⟩
  rw [hip]
  have h0 : 0 ≤ ip (μ := μN n) φ φ := integral_nonneg fun x => mul_self_nonneg (φ x)
  exact (mul_le_mul_of_nonneg_right hQ h0).trans (hΨ.2.2 φ hφ)

end DFT.Continuum.Line
