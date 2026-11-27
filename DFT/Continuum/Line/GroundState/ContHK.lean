/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.GroundState.Realize

/-!
# Hohenberg–Kohn on `H¹₀` for continuous potentials, modulo unique continuation

For continuous potentials the ground state exists in `H¹₀` (`exists_isNGS_W_cont`) but need not
be `C²`. Everything in the
Hohenberg–Kohn argument (`weak_hk`, `sep_lineW`, `rigidL_lineW`) already holds on `H¹₀` for
continuous potentials, so HK reduces to one analytic statement:

* `UcpW τ n w hw`: **every `H¹₀` ground state of every continuous `v` is nonzero a.e.**

Results:
* `isGS_W_of_isNGS_W`: normalised minimisers on `H¹₀` are ground states.
* `exists_isGS_W_cont`: ground states exist on `H¹₀` for continuous `v`, `w`.
* `hk_line_W_cont`: **Hohenberg–Kohn on `H¹₀` for continuous potentials, given `UcpW`.**
  `UcpW` is proved for both statistics in `Line/UcpBos` and `Line/UcpY`
  (`hk_line_W_cont_stat` in `Line/LiebCont`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville

variable {n : ℕ} {τ : Stat}

/-- **Unique continuation for `H¹₀` ground states** (the remaining analytic input). -/
def UcpW (τ : Stat) (n : ℕ) (w : Cfg n → ℝ) (hw : Continuous w) : Prop :=
  ∀ (v : Pot) (Ψ : Cfg n → ℝ), IsGS (settingW τ n w hw) v Ψ → ∀ᵐ x ∂μN n, Ψ x ≠ 0

/-- On `H¹₀`, the energy form is nonnegative on null states. -/
lemma h0W_null {s : Sine.SymT n} {w : Cfg n → ℝ} (hw : Continuous w) {φ : Cfg n → ℝ}
    (hφ : φ ∈ DomWS s) (h0 : ip (μ := μN n) φ φ = 0) : 0 ≤ (settingWS s w hw).h0 φ φ := by
  have hz : (fun x => φ x * φ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (φ x)) (int_mul_L2 hφ.1 hφ.1)).1 h0
  have hw0 : ∫ x, w x * (φ x * φ x) ∂μN n = 0 := by
    rw [integral_eq_zero_of_ae]
    filter_upwards [hz] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, mul_zero]
  change 0 ≤ h0W n w φ φ
  simp only [h0W, hw0, add_zero]
  exact Finset.sum_nonneg fun k _ => integral_nonneg fun x => mul_self_nonneg _

lemma isGS_W_of_isNGS_W {s : Sine.SymT n} {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}
    {Φ : Cfg n → ℝ} (h : IsNGS (settingWS s w hw) v Φ) : IsGS (settingWS s w hw) v Φ :=
  isGS_of_isNGS (fun _ hφ h0 => h0W_null hw hφ h0) h

/-- **Ground states exist on `H¹₀`** for every continuous `v` and continuous `w`. -/
theorem exists_isGS_W_cont {w : Cfg n → ℝ} (hw : Continuous w) (v : Pot) :
    ∃ Φ, IsGS (settingW τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_isNGS_W_cont (τ := τ) hw v
  exact ⟨Φ, isGS_W_of_isNGS_W hΦ, hΦ.1.2⟩

/-- **Hohenberg–Kohn on `H¹₀` for continuous potentials, given unique continuation.** The ground
state of every continuous `v` exists, and ground states of `v` and `v'` with the same norm and
density force `v - v'` to be constant. -/
theorem hk_line_W_cont {w : Cfg n → ℝ} {hw : Continuous w} (hU : UcpW τ n w hw) (v v' : Pot) :
    (∃ Φ, IsGS (settingW τ n w hw) v Φ) ∧ ∀ Ψ Ψ', IsGS (settingW τ n w hw) v Ψ →
      IsGS (settingW τ n w hw) v' Ψ' → ip (μ := μN n) Ψ Ψ = ip (μ := μN n) Ψ' Ψ' →
      dens (settingW τ n w hw) Ψ = dens (settingW τ n w hw) Ψ' → ∃ k : ℝ, v - v' = k • one :=
  ⟨(exists_isGS_W_cont hw v).imp fun _ h => h.1, fun _ _ hΨ hΨ' hn hd =>
    hk_of_ucp (sep_lineW w hw) (rigidL_lineW w hw) hΨ hΨ' hn hd (hU v _ hΨ)⟩

end DFT.Continuum.Line
