/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Lieb
import DFT.Continuum.BoxGround

/-!
# The Lieb functional for one particle in a box

For one particle on `[0, 1]` with hard walls and continuous potentials, everything in `Lieb` holds
unconditionally:

* `exists_isNGS`: every continuous potential has a normalised ground state;
* `lieb_box`: at its density `ρ`, the Lieb functional equals the kinetic energy of the ground state,
  `-v` is a subgradient, and it is the only one up to constants: the Lieb functional has a unique
  subgradient (modulo constants) at every ground-state density.
-/

namespace DFT

namespace Continuum

namespace Box

open MeasureTheory Set

lemma kin_nonneg (φ : ℝ → ℝ) : 0 ≤ setting.h0 φ φ :=
  integral_nonneg fun x => mul_self_nonneg (deriv φ x)

/-- **Normalised ground states exist** for every continuous potential. -/
theorem exists_isNGS (v : Pot) : ∃ ψ, IsNGS setting v ψ := by
  obtain ⟨ψ, hD, -, hQ, hpos, hlow⟩ := gs_data v
  set c := (Real.sqrt (ip (μ := μ1) ψ ψ))⁻¹
  have hs : 0 < Real.sqrt (ip (μ := μ1) ψ ψ) := Real.sqrt_pos.mpr hpos
  have hc2 : c * c * ip (μ := μ1) ψ ψ = 1 := by
    simp only [c]; field_simp; rw [Real.sq_sqrt hpos.le]
  have hcD : c • ψ ∈ Dom := Dom.smul_mem c hD
  refine ⟨c • ψ, ⟨hcD, by rw [ip_smul_self, hc2]⟩, fun φ hφ => ?_⟩
  rw [Q_smul_self (S := setting) v c hD, hQ]
  have := hlow φ hφ.1
  rw [hφ.2, mul_one] at this
  calc c * c * (Estar v * ip (μ := μ1) ψ ψ) = Estar v * (c * c * ip (μ := μ1) ψ ψ) := by ring
    _ = Estar v := by rw [hc2, mul_one]
    _ ≤ Q setting v φ := this

/-- **The Lieb functional in the box.** For every continuous potential `v` there is a normalised
ground state `ψ`; at its density, `F` equals the kinetic energy `∫ ψ'²`, `-v` is a subgradient of
`F`, and every other subgradient `-v'` has `v - v'` constant. -/
theorem lieb_box (v : Pot) : ∃ ψ, IsNGS setting v ψ ∧
    liebF setting (dens setting ψ) = ((setting.h0 ψ ψ : ℝ) : EReal) ∧
    (∀ ρ : Pot → ℝ, ((setting.h0 ψ ψ + dens setting ψ v - ρ v : ℝ) : EReal) ≤ liebF setting ρ) ∧
    ∀ v' : Pot, (∀ ρ : Pot → ℝ,
      ((setting.h0 ψ ψ + dens setting ψ v' - ρ v' : ℝ) : EReal) ≤ liebF setting ρ) →
      ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψ⟩ := exists_isNGS v
  have hnull : ∀ φ ∈ setting.D, ip (μ := μ1) φ φ = 0 → 0 ≤ setting.h0 φ φ :=
    fun φ _ _ => kin_nonneg φ
  refine ⟨ψ, hψ, liebF_of_isNGS hψ, subgrad_of_isNGS hψ, fun v' hsub => ?_⟩
  exact subgrad_unique sep_box rigidL_box hnull hψ (ucp_of_isGS (isGS_of_isNGS hnull hψ))
    (fun φ _ => hsub (dens setting φ))

end Box

end Continuum

end DFT
