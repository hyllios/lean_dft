import LatticeDFT.Basic.GroundState

/-!
# Spinless lattice fermions: configurations and occupations

`Conf M N`: `N`-element subsets of the sites `Fin M`; `occF i s`: occupation of site `i`.
-/

namespace LatticeDFT

section

open Matrix

variable {M N : ℕ}

/-- Configurations of `N` spinless fermions on `M` sites. -/
abbrev Conf (M N : ℕ) := {s : Finset (Fin M) // s.card = N}

/-- Occupation numbers. -/
def occF (i : Fin M) (s : Conf M N) : ℝ := if i ∈ s.1 then 1 else 0

end

end LatticeDFT
