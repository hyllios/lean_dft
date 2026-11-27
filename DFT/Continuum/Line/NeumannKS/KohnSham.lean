/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeumannKS.Diff

/-!
# The exact Kohn–Sham potential with Neumann walls

The Hartree-exchange-correlation functional `E_Hxc(ρ) = F_w(ρ) - F_0(ρ)` compares the Lieb
functionals with and without the interaction (same statistics). On the `v`-representable
densities it is Gateaux differentiable, and its differential is `v_Hxc(ρ) = v⁽⁰⁾_ρ - v⁽ʷ⁾_ρ`
modulo constants (**`hasDerivAt_hxcNH`**).

**`ks_exact`**: if `ρ` is the ground-state density of `T + w + v`, it is the ground-state density
of a non-interacting `T + v_KS`, unique up to a constant, and along every `δ` of mass zero
`v_KS(δ) = v(δ) + dE_Hxc(ρ)(δ)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-- **The Hartree-exchange-correlation functional** `E_Hxc(ρ) = F_w(ρ) - F_0(ρ)` (Neumann walls). -/
noncomputable def hxcNH (τ : Stat) (w : Cfg n → ℝ) (ρ : H1E) : ℝ :=
  (liebNH τ w ρ).toReal - (liebNH τ (0 : Cfg n → ℝ) ρ).toReal

/-- **Differentiability of `E_Hxc`**: at a density `ρ` that is the ground-state density of `v`
for the interaction `w` and of `v_s` without interaction, `E_Hxc` has derivative
`v_s(δ) - v(δ)` along every `δ` of mass zero. -/
theorem hasDerivAt_hxcNH (hw : Continuous w) {v vs : PotH} {Ψ Ψs : Cfg n → ℝ}
    (hΨ : IsGSNH τ w v Ψ) (hΨs : IsGSNH τ 0 vs Ψs) (hρ : rhoE τ Ψs = rhoE τ Ψ) {δ : H1E}
    (hδ : ellE δ = 0) :
    HasDerivAt (fun ε : ℝ => hxcNH τ w (rhoE τ Ψ + ε • δ)) (vs δ - v δ) 0 := by
  have h1 := (hasDerivAt_liebNH hw hΨ hδ).2
  have h0 := (hasDerivAt_liebNH (w := (0 : Cfg n → ℝ)) continuous_const hΨs hδ).2
  rw [hρ] at h0
  rw [show vs δ - v δ = -v δ - -vs δ by ring]
  exact h1.sub h0

/-- **The exact Kohn–Sham scheme** (Neumann walls, `H⁻¹` potentials, continuous interaction,
bosons or fermions). If `Ψ` is a ground state of `T + w + v`, there is a non-interacting
`T + v_s` whose ground-state density is `ρ_Ψ`; `v_s` is unique up to a constant, and
`v_s(δ) = v(δ) + dE_Hxc(ρ_Ψ)(δ)` along every `δ` of mass zero. -/
theorem ks_exact (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ} (hΨ : IsGSNH τ w v Ψ) :
    ∃ (vs : PotH) (Ψs : Cfg n → ℝ), IsGSNH τ 0 vs Ψs ∧ rhoE τ Ψs = rhoE τ Ψ ∧
      (∀ δ : H1E, ellE δ = 0 →
        HasDerivAt (fun ε : ℝ => hxcNH τ w (rhoE τ Ψ + ε • δ)) (vs δ - v δ) 0) ∧
      ∀ (vs' : PotH) (Ψs' : Cfg n → ℝ), IsGSNH τ 0 vs' Ψs' → rhoE τ Ψs' = rhoE τ Ψ →
        ∃ c : ℝ, vs' - vs = c • ellE := by
  obtain ⟨hpos, hN⟩ := vrepNH_nec hw ⟨v, Ψ, hΨ, rfl⟩
  obtain ⟨vs, Ψs, hΨs, hρs⟩ := vrepNH_suff (τ := τ) (w := (0 : Cfg n → ℝ)) continuous_const
    hpos hN
  refine ⟨vs, Ψs, hΨs, hρs, fun δ hδ => hasDerivAt_hxcNH hw hΨ hΨs hρs hδ,
    fun vs' Ψs' hΨs' hρ' => hkNH continuous_const hΨs' hΨs (hρ'.trans hρs.symm)⟩

end DFT.Continuum.Line
