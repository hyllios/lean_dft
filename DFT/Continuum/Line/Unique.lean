/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Lieb

/-!
# The ground state on a line is nondegenerate

For `n + 1` bosons or fermions on `[0, 1]` with a continuous interaction invariant under
relabelling, any two ground states of the same potential are proportional on the closed cube.

The ground states of `v`, together with the states of zero norm, form a linear space
(`isGS_add_smul`). A bosonic ground state has no zeros in the open cube, a fermionic one none away
from collisions; so if `Φ` and `Ψ` are ground states and `x₀` is a point of the ordered chamber,
`Φ - (Φ(x₀)/Ψ(x₀)) Ψ` vanishes at `x₀`, hence is not a ground state, hence has zero norm and
vanishes on the cube.

* `isGS_add_smul` (in `General/HK`): `ψ + s φ` is a ground state if it has positive norm.
* `gs_ne_zero_stat`: no zeros on the cube away from collisions, for both statistics.
* `gs_unique_line`: **nondegeneracy**, `Φ = c Ψ` on the closed cube.
-/

namespace DFT.Continuum

open MeasureTheory

namespace Line

open Set Box

variable {n : ℕ} {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

/-- **No zeros away from collisions**, for bosons and fermions. -/
theorem gs_ne_zero_stat {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) {Φ : Cfg n → ℝ}
    (hΦ : IsGS (setting τ n w hw) v Φ) : ∀ x ∈ Cube n, Function.Injective x → Φ x ≠ 0 := by
  cases τ
  · exact fun x hx _ => gs_ne_zero_bos hws hΦ x hx
  · exact gs_ne_zero_line hws hΦ

/-- A point of the ordered chamber: `x_i = (i + 1) / (n + 2)`. -/
lemma exists_inj_cube : ∃ x ∈ Cube n, Function.Injective x := by
  refine ⟨fun i => ((i : ℕ) + 1 : ℝ) / (n + 2), fun i _ => ?_, fun i j h => ?_⟩
  · have hi : (i : ℕ) < n + 1 := i.2
    have hi' : ((i : ℕ) : ℝ) + 1 < n + 2 := by
      have : ((i : ℕ) : ℝ) < n + 1 := by exact_mod_cast hi
      linarith
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; exact hi'
  · have hn : (0 : ℝ) < n + 2 := by positivity
    simp only at h
    rw [div_left_inj' hn.ne'] at h
    exact Fin.ext (by exact_mod_cast (by linarith : ((i : ℕ) : ℝ) = (j : ℕ)))

/-- A state of zero norm vanishes on the open cube. -/
lemma eq_zero_of_ip_zero {τ : Stat} {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n)
    (h : ip (μ := μN n) φ φ = 0) : ∀ x ∈ Cube n, φ x = 0 := by
  have hc := hφ.1.continuous
  have hae : (fun x => φ x * φ x) =ᵐ[μN n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (φ x))
      (integrableN (hc.mul hc))).1 h
  have hz : EqOn (fun x => φ x * φ x) (fun _ => 0) (Cube n) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_cube (hc.mul hc).continuousOn continuousOn_const
  exact fun x hx => mul_self_eq_zero.1 (hz hx)

/-- **The ground state on a line is nondegenerate**: two ground states of the same potential are
proportional on the closed cube. -/
theorem gs_unique_line {τ : Stat} (hws : ∀ σ x, w (pm σ x) = w x) {Φ Ψ : Cfg n → ℝ}
    (hΦ : IsGS (setting τ n w hw) v Φ) (hΨ : IsGS (setting τ n w hw) v Ψ) :
    ∃ c : ℝ, ∀ x ∈ CubeC n, Φ x = c * Ψ x := by
  obtain ⟨x0, hx0, hinj⟩ := exists_inj_cube (n := n)
  have hΨ0 := gs_ne_zero_stat hws hΨ x0 hx0 hinj
  set s := -(Φ x0 / Ψ x0)
  have hχ0 : (Φ + s • Ψ) x0 = 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s]; field_simp; ring
  have hD : Φ + s • Ψ ∈ Dom τ n := (Dom τ n).add_mem hΦ.1 ((Dom τ n).smul_mem s hΨ.1)
  have hip : ip (μ := μN n) (Φ + s • Ψ) (Φ + s • Ψ) = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) (integral_nonneg fun x => mul_self_nonneg _)
    exact gs_ne_zero_stat hws (isGS_add_smul hΦ hΨ s hpos) x0 hx0 hinj hχ0
  have hz := eq_zero_of_ip_zero hD hip
  refine ⟨-s, fun x hx => ?_⟩
  by_cases hxo : x ∈ Cube n
  · have := hz x hxo
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  · -- on the boundary both vanish
    have : ∃ k, x k = 0 ∨ x k = 1 := by
      by_contra hne
      push Not at hne
      exact hxo fun k _ => ⟨lt_of_le_of_ne (hx k (mem_univ k)).1 (hne k).1.symm,
        lt_of_le_of_ne (hx k (mem_univ k)).2 (hne k).2⟩
    obtain ⟨k, hk⟩ := this
    rw [hΦ.1.2.2 x k hk, hΨ.1.2.2 x k hk, mul_zero]

end Line

end DFT.Continuum
