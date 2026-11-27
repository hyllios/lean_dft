/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.GroundState.ContHK
import DFT.Continuum.Line.UCP.AbsW
import DFT.Continuum.Line.UCP.Invariant

/-!
# Unique continuation for bosonic `H¹₀` ground states

For bosons on the line with any continuous one-body potential `v` and continuous interaction
`w`, every `H¹₀` ground state is nonzero almost everywhere (`gs_ne_zero_W_bos`):

* `|Ψ|` is again a ground state (`isGS_abs`), nonnegative and nonzero;
* its zero set is invariant under small translations inside the cube (`zero_set_translate`,
  through Moser's logarithmic estimate);
* an invariant set is null or conull (`null_or_conull`); conull would make `|Ψ| = 0`.

Hence `UcpW .bos` holds (`ucpW_bos`), with no smoothness assumption; Hohenberg–Kohn follows in
`Line/LiebCont` (`hk_line_W_cont_stat`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {w : Cfg n → ℝ} {hw : Continuous w}

/-- **Bosonic `H¹₀` ground states of continuous potentials are nonzero almost everywhere.** -/
theorem gs_ne_zero_W_bos {v : C01} {Ψ : Cfg n → ℝ} (hΨ : IsGS (settingW .bos n w hw) v Ψ) :
    ∀ᵐ x ∂μN n, Ψ x ≠ 0 := by
  set u : Cfg n → ℝ := fun x => |Ψ x|
  have hu : IsGS (settingW .bos n w hw) v u := isGS_abs hΨ
  have hu0 : ∀ᵐ x ∂μN n, 0 ≤ u x := ae_of_all _ fun x => abs_nonneg _
  have hum := hu.1.1.aestronglyMeasurable
  set u' := hum.mk u
  have hue : u =ᵐ[μN n] u' := hum.ae_eq_mk
  have hu'm : Measurable u' := hum.stronglyMeasurable_mk.measurable
  set Z : Set (Cfg n) := {x | u' x = 0}
  have hZ : MeasurableSet Z := hu'm (measurableSet_singleton 0)
  have hv : ∀ᵐ x ∂volume, x ∈ Cube n → u x = u' x := (ae_restrict_iff' measurableSet_cube).1 hue
  have hinv : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ k (h : ℝ), 0 ≤ h →
      ∀ᵐ x ∂volume, x ∈ Sa n a h k → (x ∈ Z ↔ x + h • ek k ∈ Z) := by
    intro a ha ha2 k h hh
    have hQc := Qa_sub_cube (n := n) ha
    have hv' := (measurePreserving_add_right volume (h • ek k)).quasiMeasurePreserving.ae hv
    filter_upwards [zero_set_translate hu hu0 ha ha2 k hh, hv, hv'] with x hx h1 h2 hxS
    simp only [Z, mem_ofPred_eq]
    rw [← h1 (hQc hxS.1), ← h2 (hQc hxS.2)]
    exact hx hxS
  rcases null_or_conull hZ hinv with h | h
  · exfalso
    have hz : ∀ᵐ x ∂μN n, u x * u x = 0 := by
      filter_upwards [h, hue] with x hx he
      simp only [Z, mem_ofPred_eq] at hx
      rw [he, hx, mul_zero]
    have hip : ip (μ := μN n) u u = 0 := integral_eq_zero_of_ae hz
    exact hu.2.1.ne' hip
  · filter_upwards [h, hue] with x hx he
    simp only [Z, mem_ofPred_eq] at hx
    rw [← he] at hx
    exact abs_ne_zero.1 hx

/-- **Unique continuation for bosonic `H¹₀` ground states.** -/
theorem ucpW_bos (w : Cfg n → ℝ) (hw : Continuous w) : UcpW .bos n w hw :=
  fun _ _ hΨ => gs_ne_zero_W_bos hΨ

end DFT.Continuum.Line
