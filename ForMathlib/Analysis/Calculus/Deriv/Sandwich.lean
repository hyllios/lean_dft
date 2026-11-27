/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Derivatives from two-sided linear bounds

If `ε a ≤ f(ε) - f(0) ≤ ε b(ε)` near `0` and `b(ε) → a`, then `f'(0) = a`. This is the shape of
the derivative of a convex (or concave) function at a point where its subgradient is unique and
depends continuously on the point: `a` is the subgradient at `0`, `b(ε)` the one at `ε`.

* **`hasDerivAt_of_sandwich`**.
-/

open Filter Topology

/-- **A derivative from two-sided linear bounds.** If `ε a ≤ f ε - f 0 ≤ ε b(ε)` for `ε` near `0`
and `b(ε) → a` as `ε → 0`, `ε ≠ 0`, then `f` has derivative `a` at `0`. -/
theorem hasDerivAt_of_sandwich {f b : ℝ → ℝ} {a : ℝ} (hb : Tendsto b (𝓝[≠] 0) (𝓝 a))
    (h : ∀ᶠ ε in 𝓝 0, ε * a ≤ f ε - f 0 ∧ f ε - f 0 ≤ ε * b ε) : HasDerivAt f a 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hb' : Tendsto (fun ε => b ε - a) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hb.sub_const a
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_ hb'.norm)
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with ε ⟨h1, h2⟩ hε
  have hε : ε ≠ 0 := hε
  suffices key : |(f ε - f 0) / ε - a| ≤ |b ε - a| by
    simpa [slope_def_field, Real.norm_eq_abs] using key
  rcases hε.lt_or_gt with hn | hp
  · -- `ε < 0`: dividing reverses both bounds
    have l1 : (f ε - f 0) / ε ≤ a := by rw [div_le_iff_of_neg hn]; linarith
    have l2 : b ε ≤ (f ε - f 0) / ε := by rw [le_div_iff_of_neg hn]; linarith
    rw [abs_of_nonpos (show (f ε - f 0) / ε - a ≤ 0 by linarith),
      abs_of_nonpos (show b ε - a ≤ 0 by linarith)]
    linarith
  · have l1 : a ≤ (f ε - f 0) / ε := by rw [le_div_iff₀ hp]; linarith
    have l2 : (f ε - f 0) / ε ≤ b ε := by rw [div_le_iff₀ hp]; linarith
    rw [abs_of_nonneg (show 0 ≤ (f ε - f 0) / ε - a by linarith),
      abs_of_nonneg (show 0 ≤ b ε - a by linarith)]
    linarith
