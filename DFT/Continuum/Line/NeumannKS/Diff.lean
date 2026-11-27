/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.Analysis.Calculus.Deriv.Sandwich
import DFT.Continuum.Line.NeumannKS.Inverse

/-!
# Differentiability of the Lieb functional with Neumann walls (Corso's Lemma 6.1)

Let `ρ` be the ground-state density of `v` and `δ ∈ H¹(0, 1)` with `∫ δ = 0`. Then
`ε ↦ F(ρ + ε δ)` is finite near `0` and has derivative `-v(δ)` at `0`
(**`hasDerivAt_liebNH`**): the Lieb functional is Gateaux differentiable on the `v`-representable
densities, with differential `-v_ρ` modulo constants.

The densities `ρ_ε = ρ + ε δ` stay positive with mass `N` for small `ε`, so they are ground-state
densities of potentials `v_ε` (`eventually_vrepNH`). The supremum defining `F` at `ρ_ε` and at `ρ`
gives `-ε v(δ) ≤ F(ρ_ε) - F(ρ) ≤ -ε v_ε(δ)`, and `v_ε(δ) → v(δ)` (`tendsto_vrepNH`), so
`hasDerivAt_of_sandwich` applies.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-- **Small mass-zero perturbations of a `v`-representable density are `v`-representable.** -/
lemma eventually_vrepNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ} (hΨ : IsGSNH τ w v Ψ)
    {δ : H1E} (hδ : ellE δ = 0) : ∀ᶠ ε : ℝ in 𝓝 0, VRepNH τ n w (rhoE τ Ψ + ε • δ) := by
  set ρ := rhoE τ Ψ
  obtain ⟨hpos, hN⟩ := vrepNH_nec hw ⟨v, Ψ, hΨ, rfl⟩
  obtain ⟨tm, htm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (continuousOn_fnE ρ)
  have hc0 : 0 < fnE ρ tm := hpos tm htm
  set B := ‖evE‖ * ‖δ‖
  have hB : 0 ≤ B := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < fnE ρ tm / (B + 1))]
    with ε hε
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, lt_div_iff₀ (by positivity)] at hε
  refine vrepNH_suff hw (fun t ht => ?_) ?_
  · rw [fnE_add_smul ρ δ ε ht]
    have h1 : |ε * fnE δ t| ≤ |ε| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_fnE_le δ ht) (abs_nonneg ε)
    have h2 : fnE ρ tm ≤ fnE ρ t := hmin ht
    nlinarith [neg_abs_le (ε * fnE δ t), abs_nonneg ε]
  · rw [← ellE_apply, map_add, map_smul, hδ, smul_zero, add_zero, ellE_apply, hN]

/-- **Differentiability of the Lieb functional** (Neumann walls, `H⁻¹` potentials; Corso,
Lemma 6.1): at the ground-state density `ρ` of `v`, along every `δ` of mass zero, `F(ρ + ε δ)` is
finite for small `ε` and has derivative `-v(δ)` at `ε = 0`. -/
theorem hasDerivAt_liebNH (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ} (hΨ : IsGSNH τ w v Ψ)
    {δ : H1E} (hδ : ellE δ = 0) :
    (∀ᶠ ε : ℝ in 𝓝 0, liebNH τ w (rhoE τ Ψ + ε • δ) ≠ ⊤) ∧
      HasDerivAt (fun ε : ℝ => (liebNH τ w (rhoE τ Ψ + ε • δ)).toReal) (-v δ) 0 := by
  classical
  set ρ := rhoE τ Ψ
  have hev := eventually_vrepNH hw hΨ hδ
  -- a ground state for every `ε`: the chosen one where `ρ_ε` is representable, `Ψ` elsewhere
  set P : ℝ → PotH × (Cfg n → ℝ) := fun ε =>
    if h : VRepNH τ n w (ρ + ε • δ) then (h.choose, h.choose_spec.choose) else (v, Ψ)
  have hP : ∀ ε, IsGSNH τ w (P ε).1 (P ε).2 := fun ε => by
    by_cases h : VRepNH τ n w (ρ + ε • δ)
    · simp only [P, h, ↓reduceDIte]; exact h.choose_spec.choose_spec.1
    · simp only [P, h, ↓reduceDIte]; exact hΨ
  have hPρ : ∀ ε, VRepNH τ n w (ρ + ε • δ) → rhoE τ (P ε).2 = ρ + ε • δ := fun ε h => by
    simp only [P, h, ↓reduceDIte]; exact h.choose_spec.choose_spec.2
  -- `F(ρ_ε)` through the chosen ground state
  have hF : ∀ ε, VRepNH τ n w (ρ + ε • δ) → liebNH τ w (ρ + ε • δ) =
      ((gsEH τ w (P ε).1 - (P ε).1 (ρ + ε • δ) : ℝ) : EReal) := fun ε h => by
    rw [← hPρ ε h, liebNH_eq_of_isGSNH hw (hP ε), gsEH_sub_rhoE_eq hw (hP ε)]
  have hF0 : liebNH τ w ρ = ((gsEH τ w v - v ρ : ℝ) : EReal) := by
    rw [liebNH_eq_of_isGSNH hw hΨ, gsEH_sub_rhoE_eq hw hΨ]
  refine ⟨hev.mono fun ε h => by rw [hF ε h]; exact EReal.coe_ne_top _, ?_⟩
  -- the potentials converge
  have hρP : Tendsto (fun ε => rhoE τ (P ε).2) (𝓝 0) (𝓝 ρ) := by
    have hc : Tendsto (fun ε : ℝ => ρ + ε • δ) (𝓝 0) (𝓝 ρ) := by
      have hcont : Continuous fun ε : ℝ => ρ + ε • δ := by fun_prop
      simpa using hcont.tendsto 0
    exact hc.congr' (hev.mono fun ε h => (hPρ ε h).symm)
  have hV : Tendsto (fun ε => (P ε).1 δ) (𝓝 0) (𝓝 (v δ)) := by
    refine tendsto_nhds_iff_seq_tendsto.2 fun εs hεs => ?_
    exact tendsto_vrepNH hw hΨ (fun k => hP (εs k)) (hρP.comp hεs) hδ
  refine hasDerivAt_of_sandwich (b := fun ε => -(P ε).1 δ)
    (hV.neg.mono_left nhdsWithin_le_nhds) (hev.mono fun ε h => ?_)
  simp only [zero_smul, add_zero]
  rw [hF ε h, hF0, EReal.toReal_coe, EReal.toReal_coe]
  have e1 := gsEH_sub_le_of_isGSNH hw (hP ε) v
  have e2 := gsEH_sub_le_of_isGSNH hw hΨ (P ε).1
  rw [hPρ ε h] at e1
  simp only [map_add, map_smul, smul_eq_mul] at e1 e2 ⊢
  constructor <;> nlinarith
