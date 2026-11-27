/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureHK
import DFT.Continuum.Line.MeasurePotential.MeasureNBos

/-!
# Hohenberg–Kohn for `N` particles in measure potentials: what holds in general

* **`isGSN_of_same_dens`** (the first half of Hohenberg–Kohn, any statistics, any continuous `w`):
  if `Φ` is a ground state of `ν` and `Φ'` one of `ν'` with the same density, then `Φ` is also a
  ground state of `ν'` (and `Φ'` of `ν`).
* **`hk_bos0`** (non-interacting bosons): two measure potentials with ground states of the same
  density differ by `C dx + a δ₀ + b δ₁`.

The second half for interacting particles needs unique continuation and positivity of the density
for ground states of measure potentials; see the log.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

lemma QMN_sub (τ : Stat) (w : Cfg n → ℝ) (ν ν' : PotM) (Φ : Cfg n → ℝ) :
    QMN τ w ν Φ = QMN τ w ν' Φ + (ν - ν') (rhoHat τ Φ) := by
  simp only [QMN, sub_apply]; ring

/-- **First half of Hohenberg–Kohn**: ground states of `ν` and `ν'` with the same density are
ground states of both. -/
theorem isGSN_of_same_dens {τ : Stat} {w : Cfg n → ℝ} {ν ν' : PotM} {Φ Φ' : Cfg n → ℝ}
    (h : IsGSN τ w ν Φ) (h' : IsGSN τ w ν' Φ') (hρ : rhoHat τ Φ = rhoHat τ Φ') :
    IsGSN τ w ν' Φ ∧ IsGSN τ w ν Φ' := by
  have h1 := h.2.2 Φ' h'.1 h'.2.1
  have h2 := h'.2.2 Φ h.1 h.2.1
  rw [QMN_sub τ w ν ν' Φ, QMN_sub τ w ν ν' Φ', hρ] at h1
  refine ⟨⟨h.1, h.2.1, fun Ψ hΨ hΨn => ?_⟩, ⟨h'.1, h'.2.1, fun Ψ hΨ hΨn => ?_⟩⟩
  · have := h'.2.2 Ψ hΨ hΨn; linarith
  · have := h.2.2 Ψ hΨ hΨn
    rw [QMN_sub τ w ν ν' Φ', QMN_sub τ w ν ν' Φ, hρ] at *
    linarith

/-- The normalised square root of the density of an `N`-boson ground state (`w = 0`) is a
one-particle ground state; the function depends only on `Φ`. -/
lemma gs1_of_isGSN' {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN .bos 0 ν Φ) :
    ∃ hg : H10 (fun t => 1 / √((n : ℝ) + 1) * gN .bos Φ t),
      ∫ t, (1 / √((n : ℝ) + 1) * gN .bos Φ t) ^ 2 ∂μ1 = 1 ∧ QM ν hg = EM ν := by
  have hG := h10_gN (τ := .bos) Φ
  have hN : (0 : ℝ) < n + 1 := by positivity
  set c := 1 / √((n : ℝ) + 1)
  have hc2 : c ^ 2 = 1 / ((n : ℝ) + 1) := by rw [div_pow, Real.sq_sqrt hN.le, one_pow]
  have hgn : ∫ t, gN .bos Φ t ^ 2 ∂μ1 = n + 1 := by rw [integral_gN_sq h.1, h.2.1, mul_one]
  have hn : ∫ t, (c * gN .bos Φ t) ^ 2 ∂μ1 = 1 := by
    rw [norm2_smul, hc2, hgn, one_div_mul_cancel hN.ne']
  have hQ : QM ν hG ≤ (n + 1) * EM ν := by
    rw [← QMN_isGSN h, QMN_zero, QM]
    have := kinM_gN_le h.1; rw [rhoHat]; linarith
  refine ⟨hG.const_mul c, hn, le_antisymm ?_ (EM_le ν _ hn)⟩
  rw [QM_smul ν hG c, hc2]
  calc 1 / ((n : ℝ) + 1) * QM ν hG ≤ 1 / ((n : ℝ) + 1) * ((n + 1) * EM ν) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = EM ν := by field_simp

/-- **Hohenberg–Kohn for non-interacting bosons in measure potentials**: if `ν` and `ν'` have
`N`-boson ground states with the same density, then `ν - ν' = C dx + a δ₀ + b δ₁`. -/
theorem hk_bos0 {μp μm μp' μm' : Measure ℝ} [IsMeas01 μp] [IsMeas01 μm] [IsMeas01 μp']
    [IsMeas01 μm'] {Φ Φ' : Cfg n → ℝ} (h : IsGSN .bos 0 (nuOf μp μm) Φ)
    (h' : IsGSN .bos 0 (nuOf μp' μm') Φ') (hρ : rhoHat .bos Φ = rhoHat .bos Φ') :
    ∃ C a b : ℝ, nuOf μp μm - nuOf μp' μm' = C • intCLM μ1 +
      a • deltaM ⟨0, le_rfl, zero_le_one⟩ + b • deltaM ⟨1, zero_le_one, le_rfl⟩ := by
  have h2 := (isGSN_of_same_dens h h' hρ).1
  obtain ⟨hg, hn, hmin⟩ := gs1_of_isGSN' h
  obtain ⟨hg', hn', hmin'⟩ := gs1_of_isGSN' h2
  exact hk_meas (isGSM_of_min hg hn hmin) (isGSM_of_min hg' hn' hmin')

end DFT.Continuum.Line
