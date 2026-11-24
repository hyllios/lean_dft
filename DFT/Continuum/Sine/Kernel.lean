/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Sine.Coeff
import DFT.Continuum.Line.Free

/-!
# The potential in the sine basis

* `Ker V m' m = ⟨s_{m'}, V s_m⟩`, the matrix of the potential in the sine basis; `Ker_symm`.
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box Line Real

variable {n : ℕ}

/-- The matrix of the potential `V` in the sine basis, `⟨s_{m'}, V s_m⟩`. -/
noncomputable def Ker (V : Cfg n → ℝ) (m' m : Fin (n + 1) → ℕ) : ℝ :=
  ∫ x, smd m' x * (V x * smd m x) ∂μN n

lemma Ker_symm (V : Cfg n → ℝ) (m' m : Fin (n + 1) → ℕ) : Ker V m' m = Ker V m m' := by
  simp only [Ker]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

instance : IsFiniteMeasure (μN n) :=
  isFiniteMeasure_restrict.2 (by rw [volume_cube]; exact ENNReal.one_ne_top)

lemma muN_real_univ : (μN n).real univ = 1 := by
  simp [measureReal_def, Measure.restrict_apply MeasurableSet.univ, volume_cube]


end DFT.Continuum.Sine
