/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.LiebMattis

/-!
# The Lieb–Mattis theorem in terms of the total spin

A spatial wave function of type `(a, b)` (antisymmetric within the `a` spin-up and within the `b`
spin-down particles) describes the spin state with `S_z = (a - b) / 2`. It has total spin exactly
`S = (a - b) / 2` iff it is a highest-weight state, `S₊ ψ = 0`. Spatially `S₊` moves one
spin-down particle into the spin-up group; up to a nonzero factor it is the Young
antisymmetrisation into type `(a + 1, b - 1)`, `ψ ↦ altY (a + 1) ψ` (Fock's condition). So we
take

* `HW a ψ`: `ψ` has type `(a, N - a)` and `altY (a + 1) ψ = 0` on the cube (no condition when
  `a = N`, the fully polarised case),
* `Espin a = inf { ⟨ψ, Hψ⟩ / ⟨ψ, ψ⟩ : HW a ψ }`, the lowest energy with total spin
  `S = a - N/2`.

Results:

* `gs_highest_weight`: **the ground state of the sector `S_z = (a - b)/2` has total spin exactly
  `(a - b)/2`** (for `a ≥ b ≥ 1`); otherwise `S₊` would carry it to the sector `(a + 1, b - 1)`
  with the same energy, against `lieb_mattis`.
* `lieb_mattis_spin`: **`E(S) < E(S + 1)`** for `S ≥ 0`: `Espin a < Espin (a + 1)` whenever
  `a ≥ N - a ≥ 1`.

This is the elementary, purely spatial formulation. `Line/LiebMattisTotal` (`C²` states) and
`Line/SpinWeak` (`H¹₀` states) derive the same statement from spin-orbital wave functions and the
total-spin operator `S²`, without taking Fock's condition as a definition.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology Sine

variable {n : ℕ} {a : ℕ}

/-- Highest-weight states of type `(a, N - a)`: total spin `S = S_z = a - N/2`. -/
def HW (a n : ℕ) (ψ : Cfg n → ℝ) : Prop :=
  ψ ∈ DomY a n ∧ (a ≤ n → ∀ x ∈ Cube n, altY (a + 1) ψ x = 0)

/-- `E(S)`: the lowest energy of a state of total spin `S = a - N/2`. -/
noncomputable def Espin (w : Cfg n → ℝ) (hw : Continuous w) (v : Pot) (a : ℕ) : ℝ :=
  sInf ((fun ψ => Q (settingS (ymix a) w hw) v ψ / ip (μ := μN n) ψ ψ) ''
    {ψ | HW a n ψ ∧ 0 < ip (μ := μN n) ψ ψ})

section main

variable {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot} (hws : ∀ σ x, w (pm σ x) = w x)
  {F : Cfg n → ℝ} (hF : ContDiff ℝ (2 * (n + 1) : ℕ) F)
  (hVF : ∀ x ∈ CubeC n, LN n v x + w x = F x)
include hws hF hVF

/-- **The ground state of the sector `S_z = (a - b)/2` has total spin exactly `(a - b)/2`.** -/
theorem gs_highest_weight {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a)
    {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) :
    ∀ x ∈ Cube n, altY (a + 1) Φ x = 0 := by
  set g := altY (a + 1) Φ
  have hgD : g ∈ DomY (a + 1) n := altY_memY hΦ.1.1 hΦ.1.2.2
  have hQg : Q (settingS (ymix (a + 1)) w hw) v g =
      Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ * ip (μ := μN n) g g :=
    Q_altY hws hΦ
  rcases (integral_nonneg fun x => mul_self_nonneg (g x) :
    (0 : ℝ) ≤ ip (μ := μN n) g g).eq_or_lt with h0 | hpos
  · exact eq_zero_of_ip_zero' hgD.1 h0.symm
  · exfalso
    obtain ⟨Ψ, hΨ, -⟩ := exists_isGS_smoothS (a + 1) hws hF hVF (hw := hw)
    have hlm := lieb_mattis hws hF hVF hab hb1 hba hΦ hΨ
    have hle := le_Q_of_isGS hΨ hgD
    rw [hQg] at hle
    have := (mul_le_mul_iff_of_pos_right hpos).1 hle
    linarith

omit hws hF hVF in
/-- The energy of a state of type `(a, N - a)` is at least the ground-state energy. -/
lemma Espin_ge {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) {ψ : Cfg n → ℝ}
    (hψ : ψ ∈ DomY a n) (hpos : 0 < ip (μ := μN n) ψ ψ) :
    Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ ≤
      Q (settingS (ymix a) w hw) v ψ / ip (μ := μN n) ψ ψ := by
  rw [le_div_iff₀ hpos]
  exact le_Q_of_isGS hΦ hψ

omit hws hF hVF in
lemma bddBelow_Espin {Φ : Cfg n → ℝ} (hΦ : IsGS (settingS (ymix a) w hw) v Φ) :
    BddBelow ((fun ψ => Q (settingS (ymix a) w hw) v ψ / ip (μ := μN n) ψ ψ) ''
      {ψ | HW a n ψ ∧ 0 < ip (μ := μN n) ψ ψ}) := by
  refine ⟨Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ, ?_⟩
  rintro _ ⟨ψ, ⟨hψ, hpos⟩, rfl⟩
  rw [le_div_iff₀ hpos]
  exact le_Q_of_isGS hΦ hψ.1

/-- **The Lieb–Mattis theorem**: `E(S) < E(S + 1)` for `S ≥ 0`. With `a` spin-up particles
(`S = a - N/2`) and `a ≥ N - a ≥ 1`, the lowest energy with total spin `S` is strictly below the
lowest energy with total spin `S + 1`. Moreover `E(S)` is attained by the ground state of the
sector `S_z = S`. -/
theorem lieb_mattis_spin {b : ℕ} (hab : a + b = n + 1) (hb1 : 1 ≤ b) (hba : b ≤ a) :
    Espin w hw v a < Espin w hw v (a + 1) := by
  obtain ⟨Φ, hΦ, hΦ1⟩ := exists_isGS_smoothS a hws hF hVF (hw := hw)
  obtain ⟨Ψ, hΨ, hΨ1⟩ := exists_isGS_smoothS (a + 1) hws hF hVF (hw := hw)
  have hlm := lieb_mattis hws hF hVF hab hb1 hba hΦ hΨ
  -- the ground state of type `(a, b)` is a highest-weight state
  have hΦHW : HW a n Φ := ⟨hΦ.1, fun _ => gs_highest_weight hws hF hVF hab hb1 hba hΦ⟩
  have h1 : Espin w hw v a ≤ Q (settingS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ :=
    csInf_le (bddBelow_Espin hΦ) ⟨Φ, ⟨hΦHW, hΦ.2.1⟩, rfl⟩
  -- so is the ground state of type `(a + 1, b - 1)`
  have hΨHW : HW (a + 1) n Ψ := by
    refine ⟨hΨ.1, fun ha1 => ?_⟩
    exact gs_highest_weight (b := b - 1) hws hF hVF (by omega) (by omega) (by omega) hΨ
  have h2 : Q (settingS (ymix (a + 1)) w hw) v Ψ / ip (μ := μN n) Ψ Ψ ≤
      Espin w hw v (a + 1) := by
    refine le_csInf ⟨_, ⟨Ψ, ⟨hΨHW, hΨ.2.1⟩, rfl⟩⟩ ?_
    rintro _ ⟨ψ, ⟨hψ, hpos⟩, rfl⟩
    exact Espin_ge hΨ hψ.1 hpos
  linarith

end main

end DFT.Continuum.Line
