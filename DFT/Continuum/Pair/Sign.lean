/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Pair.Bosons
import DFT.Continuum.Pair.Nodal
import DFT.Continuum.Pair.Hopf

/-!
# Interacting bosons: the ground state does not change sign

The Perron–Frobenius property for two interacting bosons in a box, proved inside the `C²` form
domain, without Sobolev spaces or regularity theory:

* `grad_zero_at_zero` (`Nodal`): a ground state has zero gradient wherever it vanishes. Testing the
  ground-state property against `√(Φ²+ε²) − ε + tφ` forces `∫ h_ε''(Φ)|∇Φ|² φ → 0`, which a
  crossing zero with nonzero gradient would keep away from `0`.
* `pos_or_nonpos` (`Hopf`): a supersolution that is positive somewhere and has zero gradient at its
  zeros is positive everywhere (Hopf's boundary lemma with an exponential barrier).
* `gs_sign`: interacting bosonic ground states do not change sign.
* `hk_interacting_bosons`: **Hohenberg–Kohn for two interacting bosons in a box**, for every
  continuous symmetric interaction, with no further assumption.
-/
namespace DFT.Continuum.Pair

open MeasureTheory Set Box

/-- A ground state is positive on the square if it is positive somewhere, and in general is
nonnegative or nonpositive there. -/
lemma gs_pos_or_nonpos {w : ℝ × ℝ → ℝ} {hw : Continuous w} (hws : ∀ p, w p.swap = w p)
    {v : Pot} {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ) :
    (∀ p ∈ Sq, 0 < Φ p) ∨ ∀ p ∈ Sq, Φ p ≤ 0 := by
  set E := Q (setting2 1 w hw) v Φ / ip (μ := μ2) Φ Φ
  set V : ℝ × ℝ → ℝ := fun p => w p + L2 v p - E
  have hV : Continuous V := (hw.add (continuous_L2 v)).sub continuous_const
  have heq := strong_eq hws hΦ
  refine pos_or_nonpos (c := fun p => max (V p) 0) hΦ.1.1 (hV.max continuous_const)
    (fun p => le_max_right _ _) (fun p hp hpos => ?_) (grad_zero_at_zero hws hΦ)
  have e := heq p hp
  have h1 : 0 ≤ (max (V p) 0 - V p) * Φ p :=
    mul_nonneg (by linarith [le_max_left (V p) 0]) hpos.le
  simp only [V] at e h1 ⊢
  nlinarith

/-- **Interacting bosonic ground states do not change sign.** -/
theorem gs_sign {w : ℝ × ℝ → ℝ} {hw : Continuous w} (hws : ∀ p, w p.swap = w p)
    {v : Pot} {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ) :
    (∀ p ∈ Sq, 0 ≤ Φ p) ∨ ∀ p ∈ Sq, Φ p ≤ 0 := by
  rcases gs_pos_or_nonpos hws hΦ with h | h
  · exact Or.inl fun p hp => (h p hp).le
  · exact Or.inr h

/-- **Hohenberg–Kohn for two interacting bosons in a box.** For any continuous symmetric
interaction, if ground states of continuous potentials `v` and `v'` have the same one-body density,
then `v - v'` is constant. -/
theorem hk_interacting_bosons {w : ℝ × ℝ → ℝ} {hw : Continuous w} (hws : ∀ p, w p.swap = w p)
    {v v' : Pot} {Φ Φ' : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ)
    (hΦ' : IsGS (setting2 1 w hw) v' Φ')
    (hρ : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, Φ (x, y) ^ 2 =
      ∫ y in Ioo (0 : ℝ) 1, Φ' (x, y) ^ 2) : ∃ k : ℝ, v - v' = k • one :=
  hk_bosons hws hΦ hΦ' hρ (gs_sign hws hΦ)

end DFT.Continuum.Pair
