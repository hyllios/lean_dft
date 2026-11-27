/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.HK.UcpBos
import DFT.Continuum.Line.HK.UcpY

/-!
# Hohenberg–Kohn and the Lieb functional on `H¹₀` for continuous potentials

For `N` bosons or fermions on the line, with any continuous one-body potential `v` and any
continuous interaction `w` (no smoothness, no relabelling symmetry of `w`):

* `ucpW_cont`: every `H¹₀` ground state is nonzero almost everywhere (`ucpW_bos`, `ucpW_fer`);
* `hk_line_W_cont_stat`: Hohenberg–Kohn for either statistics;
* **`lieb_line_W_cont_of`**: at the density of any normalised ground state `ψ` of `v`, the Lieb
  functional equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every other subgradient `-v'` has
  `v - v'` constant;
* **`lieb_line_W_cont`**: such a ground state exists for every continuous `v`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Box SturmLiouville

variable {n : ℕ} {τ : Stat}

/-- **Unique continuation for `H¹₀` ground states**, bosons or fermions. -/
theorem ucpW_cont (w : Cfg n → ℝ) (hw : Continuous w) : UcpW τ n w hw := by
  cases τ
  · exact ucpW_bos w hw
  · exact ucpW_fer w hw

/-- **Hohenberg–Kohn on `H¹₀` with continuous potentials**, bosons or fermions. -/
theorem hk_line_W_cont_stat {w : Cfg n → ℝ} {hw : Continuous w} (v v' : Pot) :
    (∃ Φ, IsGS (settingW τ n w hw) v Φ) ∧ ∀ Ψ Ψ', IsGS (settingW τ n w hw) v Ψ →
      IsGS (settingW τ n w hw) v' Ψ' → ip (μ := μN n) Ψ Ψ = ip (μ := μN n) Ψ' Ψ' →
      dens (settingW τ n w hw) Ψ = dens (settingW τ n w hw) Ψ' →
        ∃ k : ℝ, v - v' = k • one :=
  hk_line_W_cont (ucpW_cont w hw) v v'

/-- **The Lieb functional on `H¹₀` at a v-representable density.** For continuous `v` and `w`
and any normalised ground state `ψ` of `v`: `F(ρ_ψ) = ⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient of
`F` at `ρ_ψ`, and every other subgradient `-v'` has `v - v'` constant. -/
theorem lieb_line_W_cont_of {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} {ψ : Cfg n → ℝ}
    (hψ : IsNGS (settingW τ n w hw) v ψ) :
    liebF (settingW τ n w hw) (dens (settingW τ n w hw) ψ) =
        (((settingW τ n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (settingW τ n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingW τ n w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  have hnull : ∀ φ ∈ (settingW τ n w hw).D, ip (μ := μN n) φ φ = 0 →
      0 ≤ (settingW τ n w hw).h0 φ φ := fun _ hφ h => h0W_null hw hφ h
  refine ⟨liebF_of_isNGS hψ, subgrad_of_isNGS hψ, fun v' hsub => ?_⟩
  exact subgrad_unique (sep_lineW w hw) (rigidL_lineW w hw) hnull hψ
    (ucpW_cont w hw v ψ (isGS_of_isNGS hnull hψ)) (fun φ _ => hsub (dens (settingW τ n w hw) φ))

/-- **The Lieb functional for `N` bosons or fermions on a line with continuous potentials.** For
every continuous `v` and continuous `w` a normalised `H¹₀` ground state `ψ` exists; at its density
the Lieb functional equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and every other subgradient
`-v'` has `v - v'` constant. -/
theorem lieb_line_W_cont {w : Cfg n → ℝ} (hw : Continuous w) (v : Pot) :
    ∃ ψ, IsNGS (settingW τ n w hw) v ψ ∧
      liebF (settingW τ n w hw) (dens (settingW τ n w hw) ψ) =
        (((settingW τ n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (settingW τ n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((settingW τ n w hw).h0 ψ ψ + dens (settingW τ n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingW τ n w hw) ρ) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψ⟩ := exists_isNGS_W_cont (τ := τ) hw v
  exact ⟨ψ, hψ, lieb_line_W_cont_of hψ⟩

end DFT.Continuum.Line
