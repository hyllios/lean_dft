/-
Copyright (c) 2026 lean_dft contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Pittalis
-/
import DFT.Continuum.Line.NeumannKS.Diff

/-!
# The constrained-search derivative on the fixed-mass space

For positive densities the constrained-search and Lieb functionals agree locally
on each mass-zero line (Corso, Lemma 6.1).
-/

namespace DFT.Continuum.Line

open Set MeasureTheory SturmLiouville Filter Topology

theorem levyDerivativeAtDensity {n : ℕ} (τ : Stat) {w : Cfg n → ℝ} (hw : Continuous w)
    (ρ : H1E) (hp : ∀ t ∈ Icc (0 : ℝ) 1, 0 < fnE ρ t)
    (hm : ∫ t, fnE ρ t ∂vol01 = n + 1) :
    ∃ (v : PotH) (Ψ : Cfg n → ℝ), IsGSNH τ w v Ψ ∧ rhoE τ Ψ = ρ ∧
      ∀ δ : H1E, ellE δ = 0 →
        (∀ᶠ ε : ℝ in 𝓝 0, ∃ e : ℝ, levyNH τ w (ρ + ε • δ) = (e : EReal) ∧
          liebNH τ w (ρ + ε • δ) = (e : EReal)) ∧
        HasDerivAt (fun ε : ℝ => (levyNH τ w (ρ + ε • δ)).toReal) (-v δ) 0 := by
  obtain ⟨v, Ψ, hΨ, rfl⟩ := vrepNH_suff (τ := τ) hw hp hm
  refine ⟨v, Ψ, hΨ, rfl, fun δ hδ => ?_⟩
  have hfinite : ∀ᶠ ε : ℝ in 𝓝 0, ∃ e : ℝ,
      levyNH τ w (rhoE τ Ψ + ε • δ) = (e : EReal) ∧
      liebNH τ w (rhoE τ Ψ + ε • δ) = (e : EReal) := by
    filter_upwards [eventually_vrepNH hw hΨ hδ] with ε hε
    obtain ⟨vε, Φ, hΦ, hρ⟩ := hε
    rw [← hρ]
    exact ⟨intEN w Φ, levyNH_eq_of_isGSNH hw hΦ, liebNH_eq_of_isGSNH hw hΦ⟩
  refine ⟨hfinite, (hasDerivAt_liebNH hw hΨ hδ).2.congr_of_eventuallyEq ?_⟩
  filter_upwards [hfinite] with ε hε
  obtain ⟨e, hL, hF⟩ := hε
  exact congrArg EReal.toReal (hL.trans hF.symm)

end DFT.Continuum.Line
