/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.WeakHK
import DFT.Continuum.General.VRep

/-!
# `v`-representability on a line, `C²` states

On a lattice, an interior density is always ensemble-`v`-representable, but it can fail to be
pure-state-`v`-representable through degeneracy. On a line the picture is reversed:

* **Ensembles give nothing new** (`ensDens_iff_line`, `ensVRep_iff_line`): the `C²` ground state of
  every potential is nondegenerate (`gs_unique_line`), so every ground-state ensemble has the
  density of the ground state. The `H¹₀` version for continuous potentials is `ensVRep_iff_W_cont`
  (`Line/Nondeg`).
-/

namespace DFT.Continuum

open MeasureTheory

namespace Line

open Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-! ### Ensembles: nondegeneracy makes them pure -/

/-- On a line, all normalised ground states of `v` have the same density. -/
theorem gs_dens_unique (hws : ∀ σ x, w (pm σ x) = w x) {v : Pot} {Φ Ψ : Cfg n → ℝ}
    (hΦ : IsGS (setting τ n w hw) v Φ) (h1 : ip (μ := μN n) Φ Φ = 1)
    (hΨ : IsGS (setting τ n w hw) v Ψ) (h2 : ip (μ := μN n) Ψ Ψ = 1) :
    dens (setting τ n w hw) Φ = dens (setting τ n w hw) Ψ := by
  obtain ⟨c, hc⟩ := gs_unique_line hws hΦ hΨ
  refine dens_eq_of_ae_smul (c := c) ?_ h1 h2
  filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
  rw [hc x (cube_subset hx)]; rfl

/-- **Ensembles give nothing new on a line**: for every potential, the ensemble densities are
exactly the pure ground-state densities. -/
theorem ensDens_iff_line (hws : ∀ σ x, w (pm σ x) = w x) (v : Pot) (ρ : Pot → ℝ) :
    EnsDens (setting τ n w hw) v ρ ↔ PureDens (setting τ n w hw) v ρ :=
  ⟨pureDens_of_ensDens fun _ _ h1 h1' h2 h2' => gs_dens_unique hws h1 h1' h2 h2',
    ensDens_of_pureDens⟩

/-- **Ensemble `v`-representability equals pure-state `v`-representability on a line.** -/
theorem ensVRep_iff_line (hws : ∀ σ x, w (pm σ x) = w x) (ρ : Pot → ℝ) :
    EnsVRep (setting τ n w hw) ρ ↔ PureVRep (setting τ n w hw) ρ :=
  exists_congr fun v => ensDens_iff_line hws v ρ

end Line

end DFT.Continuum
