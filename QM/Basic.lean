/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Physlib.QuantumMechanics.Operators.StateObservables.Variance
import Physlib.QuantumMechanics.Operators.Uncertainty

/-!
# Basic quantum mechanics (from Physlib)

lean_qm does not redefine basic quantum mechanics. Expectation values, variances and the
Robertson uncertainty relation are taken from Physlib, where they are stated for (possibly
unbounded) operators `T : H →ₗ.[ℂ] H`:

* `LinearPMap.expectedValue`, `LinearPMap.variance`, `LinearPMap.variance_nonneg`
* `LinearPMap.state_uncertainty_of_raw_commutator` (Robertson)

Finite-dimensional / bounded operators enter through `LinearMap.toPMap` with domain `⊤`.
lean_qm starts where Physlib stops: Fock space, many-body theory, Green's functions.
-/
