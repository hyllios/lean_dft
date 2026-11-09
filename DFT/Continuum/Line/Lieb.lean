/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.General.Lieb
import DFT.Continuum.Line.Fermions

/-!
# The Lieb functional for `N` fermions on a line

For `n + 1` interacting fermions on `[0, 1]`, separation, rigidity and unique continuation all hold
(`sep_line`, `rigidL_line`, `ucp_line`), so Lieb's formulation of Hohenberg–Kohn holds with no
further assumption at every ground-state density:

* `h0N_nonneg_of_ip_zero`: a state of zero norm has nonnegative energy (it vanishes on the cube, so
  only the kinetic energy is left).
* `lieb_line`: at the density `ρ` of a normalised ground state `ψ` of `v`, the Lieb functional
  equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient, and it is the only one up to constants.

Unlike `lieb_box`, the ground state is a hypothesis: existence of ground states for interacting
particles is not formalized.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box

variable {n : ℕ} {w : Cfg n → ℝ} {hw : Continuous w}

/-- A state of zero norm has nonnegative energy: it vanishes on the cube, so the interaction
term vanishes and only the kinetic energy is left. -/
lemma h0N_nonneg_of_ip_zero {φ : Cfg n → ℝ} (hφ : φ ∈ DomF n)
    (h : ip (μ := μN n) φ φ = 0) : 0 ≤ (settingF n w hw).h0 φ φ := by
  have hc := hφ.1.continuous
  -- `φ² = 0` almost everywhere on the cube, hence `φ = 0` on the (open) cube
  have hae : (fun x => φ x * φ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (φ x))
      (integrableN (hc.mul hc))).1 h
  have hz : EqOn (fun x => φ x * φ x) (fun _ => 0) (Cube n) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_cube (hc.mul hc).continuousOn continuousOn_const
  have hW : ∫ x, w x * (φ x * φ x) ∂μN n = 0 := by
    refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_cube).2
      (ae_of_all _ fun x hx => ?_))
    have := hz hx
    simp only at this
    simp [this]
  change 0 ≤ ∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n + ∫ x, w x * (φ x * φ x) ∂μN n
  rw [hW, add_zero]
  exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _

/-- **The Lieb functional for `N` fermions on a line.** For any continuous interaction invariant
under relabelling and any continuous potential `v` with a normalised ground state `ψ`: at the
density of `ψ`, the Lieb functional equals `⟨ψ, (T + W) ψ⟩`, `-v` is a subgradient of it, and every
other subgradient `-v'` has `v - v'` constant. -/
theorem lieb_line (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {ψ : Cfg n → ℝ}
    (hψ : IsNGS (settingF n w hw) v ψ) :
    liebF (settingF n w hw) (dens (settingF n w hw) ψ) =
        (((settingF n w hw).h0 ψ ψ : ℝ) : EReal) ∧
      (∀ ρ : Pot → ℝ, (((settingF n w hw).h0 ψ ψ + dens (settingF n w hw) ψ v - ρ v : ℝ) :
        EReal) ≤ liebF (settingF n w hw) ρ) ∧
      ∀ v' : Pot, (∀ ρ : Pot → ℝ,
        (((settingF n w hw).h0 ψ ψ + dens (settingF n w hw) ψ v' - ρ v' : ℝ) : EReal) ≤
          liebF (settingF n w hw) ρ) →
        ∃ k : ℝ, v - v' = k • one := by
  have hnull : ∀ φ ∈ (settingF n w hw).D, ip (μ := μN n) φ φ = 0 →
      0 ≤ (settingF n w hw).h0 φ φ := fun φ hφ h => h0N_nonneg_of_ip_zero hφ h
  refine ⟨liebF_of_isNGS hψ, subgrad_of_isNGS hψ, fun v' hsub => ?_⟩
  exact subgrad_unique (sep_line w hw) (rigidL_line w hw) hnull hψ
    (ucp_line hws (isGS_of_isNGS hnull hψ)) (fun φ _ => hsub (dens (settingF n w hw) φ))

end DFT.Continuum.Line
