/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.HK.SquareWall
import DFT.Lattice.Generic.Krylov

/-!
# The plane of the two-fermion square, without a gap

On the plane `v₀ + v₂ = v₁ + v₃` write `δ = v₀ − v₁` and `σ = v₀ − v₃`. A ground state is explicit
in each sector of the hidden involution `Qsq`, with no gap hypothesis: `(0, 2, r − δ, r + δ, 2, 0)`
with `r = √(δ² + 4)` when `σ² ≤ δ²`, and `(r − σ, 2, 0, 0, −2, −(r + σ))` with `r = √(σ² + 4)` when
`δ² ≤ σ²`. These are the states `Ψ_A`, `Ψ_B` of Penz and van Leeuwen (J. Chem. Phys. 155, 244111
(2021), Secs. III C and IV B, Eqs. (45)–(49), Fig. 4; `δ = 2s`, `σ = 2t`), who also show that the
points with `|s| ≥ |t|`, `s ≠ 0` (and symmetrically) are not uniquely v-representable. New here: the
formal proof, the constant potentials not exceptional, the exceptional set and the set of shared
densities not closed, and the direction of `square_wall` fixed. Consequences:

* every non-constant potential of the plane is exceptional (`square_plane_exceptional`), while a
  constant potential is not (`square_const_not_exceptional`): the exceptional set contains the plane
  minus its line of constant potentials;
* the exceptional set of the square is not closed (`square_exceptional_not_closed`), although it
  lies in a closed, nowhere dense, null set (`square_generic_hk_ae`);
* `square_wall_unit`: `square_wall` with the direction fixed to `(1, 1, −1, −1)` or `(1, −1, −1, 1)`
  (for an existential direction the value of the bound `|ε| ≤ g/2` has no content);
  `square_wall_plus`, `square_wall_minus`: which of the two, `(1, 1, −1, −1)` when
  `(v₀ − v₃)² ≤ (v₀ − v₁)²` and `(1, −1, −1, 1)` when `(v₀ − v₁)² ≤ (v₀ − v₃)²`;
* the densities produced by more than one potential do not form a closed set, for pure states
  (`SharedDens`, `square_sharedDens_not_closed`) and for ensembles (`SharedEnsDens`,
  `square_sharedEnsDens_not_closed`, the non-uv densities of Penz and van Leeuwen for real states):
  the densities of the `Q = +1` state at `(t, 0, 0, t)`, shared with
  `(t, 0, 0, t) + (t/2)(1, 1, −1, −1)`, tend to the uniform density as `t → 0`, and only constant
  potentials produce that one (weak Hohenberg–Kohn, also for ensembles `weak_hk_ens`, and
  `square_const_shared`). By the same example the uniquely v-representable densities are not
  open relative to the ensemble-v-representable ones (`square_uvDens_not_relOpen`);
* complex states give no new ensemble densities for a real Hamiltonian (`ensDensC_eq_ensDens`:
  with `ψ = a + i b`, the parts `a`, `b` are real ground states and `|ψ|² = a² + b²`), so both
  results hold in the setting of Penz and van Leeuwen, complex states and ensembles
  (`square_sharedEnsDensC_not_closed`, `square_uvDensC_not_relOpen`);
* the exact segment: along `(1, 1, −1, −1)` the `Q = +1` state stays a ground state exactly while
  `(v₀ − v₃ + 2ε)² ≤ (v₀ − v₁)²` (`square_segment_plus`; mirror `square_segment_minus`), and
  beyond it stays an eigenvector (`eigen_sq_plus`); for the counterexample
  `(3/4, −3/4, −3/4, 3/4)` this is `|ε| ≤ 3/4`, three times the bound `g/2` of `square_wall_plus`
  (`square_example_segment`).

Also `sq_plane_sos`, `ground_sq_plus`, `ground_sq_minus`, `support_const_of_shared`,
`square_plane_shared`, `square_const_shared`, `isGroundState_smul`, `psiSq` and its lemmas,
`EnsDens`, `dens_mem_ensDens`, `sharedDens_subset_sharedEnsDens`; for complex states `qfC`,
`normSqC`, `IsGroundStateC`, `densC`, `EnsDensC`, `SharedEnsDensC` and the lemmas behind
`ensDensC_eq_ensDens`.
-/

namespace DFT

open Matrix

/-- The sum of squares behind `ground_sq_plus`, on plain reals: with `r² = δ² + 4`, `r > 0` and
`σ² ≤ δ²`, the sum of the two weighted squares and the bracket is nonnegative (the sum is the
energy excess of `φ` over the `Q = +1` state, modulo `r² = δ² + 4`). -/
lemma sq_plane_sos {δ σ r f0 f1 f2 f3 f4 f5 : ℝ} (hr0 : 0 < r) (hr : r ^ 2 = δ ^ 2 + 4)
    (hs : σ ^ 2 ≤ δ ^ 2) :
    0 ≤ (r + δ) * (f2 - (r - δ) * (f1 + f4) / 4) ^ 2 +
      (r - δ) * (f3 - (r + δ) * (f1 + f4) / 4) ^ 2 +
      ((r + σ) * f0 ^ 2 + (r - σ) * f5 ^ 2 + r * (f1 - f4) ^ 2 / 2 - 2 * f0 * (f1 - f4) +
        2 * f5 * (f1 - f4)) := by
  have hδlt : δ ^ 2 < r ^ 2 := by linarith
  have hσlt : σ ^ 2 < r ^ 2 := by linarith
  obtain ⟨hδa, hδb⟩ := abs_lt_of_sq_lt_sq' hδlt hr0.le
  obtain ⟨hσa, hσb⟩ := abs_lt_of_sq_lt_sq' hσlt hr0.le
  have hrd1 : 0 < r + δ := by linarith
  have hrd2 : 0 < r - δ := by linarith
  have hrs1 : 0 < r + σ := by linarith
  have hrs2 : 0 < r - σ := by linarith
  have hP0 : 0 ≤ (r + δ) * (f2 - (r - δ) * (f1 + f4) / 4) ^ 2 +
      (r - δ) * (f3 - (r + δ) * (f1 + f4) / 4) ^ 2 := by positivity
  have hAB4 : 0 ≤ (r + σ) * (r - σ) - 4 := by
    have e : (r + σ) * (r - σ) - 4 = δ ^ 2 - σ ^ 2 := by linear_combination hr
    rw [e]; linarith
  have hABM0 : 0 ≤ (r + σ) * (r - σ) *
      ((r + σ) * f0 ^ 2 + (r - σ) * f5 ^ 2 + r * (f1 - f4) ^ 2 / 2 -
      2 * f0 * (f1 - f4) + 2 * f5 * (f1 - f4)) := by
    have e : (r + σ) * (r - σ) * ((r + σ) * f0 ^ 2 + (r - σ) * f5 ^ 2 + r * (f1 - f4) ^ 2 / 2 -
        2 * f0 * (f1 - f4) + 2 * f5 * (f1 - f4)) =
        (r - σ) * ((r + σ) * f0 - (f1 - f4)) ^ 2 + (r + σ) * ((r - σ) * f5 + (f1 - f4)) ^ 2 +
          r * (f1 - f4) ^ 2 * ((r + σ) * (r - σ) - 4) / 2 := by ring
    rw [e]; positivity
  have hM0 : 0 ≤ (r + σ) * f0 ^ 2 + (r - σ) * f5 ^ 2 + r * (f1 - f4) ^ 2 / 2 -
      2 * f0 * (f1 - f4) + 2 * f5 * (f1 - f4) :=
    le_of_mul_le_mul_left (by rw [mul_zero]; exact hABM0) (mul_pos hrs1 hrs2)
  linarith

/-- The `Q = +1` ground state on the plane `v₀ + v₂ = v₁ + v₃`, when `(v₀ − v₃)² ≤ (v₀ − v₁)²`:
`(0, 2, r − δ, r + δ, 2, 0)` with `δ = v₀ − v₁` and `r = √(δ² + 4)` (Penz–van Leeuwen's `Ψ_A`). -/
lemma ground_sq_plus {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {δ r : ℝ} (hδ : v 0 - v 1 = δ)
    (hr0 : 0 < r) (hr : r ^ 2 = δ ^ 2 + 4) (hs : (v 0 - v 3) ^ 2 ≤ δ ^ 2) :
    IsGroundState (hamN H0sq occ4 v) ![0, 2, r - δ, r + δ, 2, 0] := by
  subst hδ
  refine ⟨fun h => by simpa using congrFun h 1, fun φ => ?_⟩
  have h2 : v 2 = v 1 + v 3 - v 0 := by linarith
  have hsos := sq_plane_sos (f0 := φ 0) (f1 := φ 1) (f2 := φ 2) (f3 := φ 3) (f4 := φ 4) (f5 := φ 5)
    hr0 hr hs
  have hN0 : 0 ≤ (2 : ℝ) ^ 2 + (r - (v 0 - v 1)) ^ 2 + (r + (v 0 - v 1)) ^ 2 + 2 ^ 2 := by
    positivity
  have hfin := mul_nonneg hN0 hsos
  rw [qf_sq, qf_sq]
  simp only [Fin.isValue, cons_val_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul, add_zero, mul_zero, cons_val_one, sub_self, cons_val, zero_add, sub_zero,
      dotProduct, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, cons_val_succ,
      cons_val_fin_one, Finset.sum_const_zero, ge_iff_le]
  rw [h2]
  linear_combination hfin -
    (((2 : ℝ) ^ 2 + (r - (v 0 - v 1)) ^ 2 + (r + (v 0 - v 1)) ^ 2 + 2 ^ 2) *
        (-(φ 1 + φ 4) * (r * φ 1 - 4 * φ 2 - 4 * φ 3 + r * φ 4) / 8) -
      2 * r * (φ 0 * φ 0 + φ 1 * φ 1 + φ 2 * φ 2 + φ 3 * φ 3 + φ 4 * φ 4 + φ 5 * φ 5)) * hr

/-- The `Q = −1` ground state on the plane `v₀ + v₂ = v₁ + v₃`, when `(v₀ − v₁)² ≤ (v₀ − v₃)²`:
`(r − σ, 2, 0, 0, −2, −(r + σ))` with `σ = v₀ − v₃` and `r = √(σ² + 4)` (Penz–van Leeuwen's
`Ψ_B`). -/
lemma ground_sq_minus {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {σ r : ℝ} (hσ : v 0 - v 3 = σ)
    (hr0 : 0 < r) (hr : r ^ 2 = σ ^ 2 + 4) (hs : (v 0 - v 1) ^ 2 ≤ σ ^ 2) :
    IsGroundState (hamN H0sq occ4 v) ![r - σ, 2, 0, 0, -2, -(r + σ)] := by
  subst hσ
  refine ⟨fun h => by simpa using congrFun h 1, fun φ => ?_⟩
  have h2 : v 2 = v 1 + v 3 - v 0 := by linarith
  have hsos := sq_plane_sos (f0 := φ 2) (f1 := φ 1) (f2 := φ 0) (f3 := -φ 5) (f4 := -φ 4)
    (f5 := -φ 3) hr0 hr hs
  have hN0 : 0 ≤ (r - (v 0 - v 3)) ^ 2 + 2 ^ 2 + 2 ^ 2 + (r + (v 0 - v 3)) ^ 2 := by positivity
  have hfin := mul_nonneg hN0 hsos
  rw [qf_sq, qf_sq]
  simp only [Fin.isValue, neg_add_rev, neg_sub, cons_val_zero, cons_val_one, cons_val, mul_neg,
      mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      add_zero, neg_zero, even_two, Even.neg_pow, neg_mul, sub_neg_eq_add, dotProduct,
      Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, cons_val_succ, neg_neg,
      cons_val_fin_one, Finset.sum_const, Finset.card_singleton, one_smul, zero_add, ge_iff_le]
  rw [h2]
  linear_combination hfin -
    (((r - (v 0 - v 3)) ^ 2 + 2 ^ 2 + 2 ^ 2 + (r + (v 0 - v 3)) ^ 2) *
        (-(φ 1 - φ 4) * (-4 * φ 0 + r * φ 1 - r * φ 4 + 4 * φ 5) / 8) -
      2 * r * (φ 0 * φ 0 + φ 1 * φ 1 + φ 2 * φ 2 + φ 3 * φ 3 + φ 4 * φ 4 + φ 5 * φ 5)) * hr

/-- On the plane `v₀ + v₂ = v₁ + v₃`, at a non-constant potential, some ground state is also a
ground state of a potential that differs by more than a constant; no gap is assumed (compare
`square_wall`). The witness is the explicit ground state of `ground_sq_plus` or `ground_sq_minus`,
moved along `(1, 1, −1, −1)` or `(1, −1, −1, 1)`. -/
theorem square_plane_shared {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3)
    (hnc : ¬ ∃ k : ℝ, ∀ i, v i = k) :
    ∃ ψ : Fin 6 → ℝ, ∃ v' : Fin 4 → ℝ, IsGroundState (hamN H0sq occ4 v) ψ ∧
      IsGroundState (hamN H0sq occ4 v') ψ ∧ ¬ ∃ k : ℝ, ∀ i, v i - v' i = k := by
  have hconst : ∀ k : ℝ, v 0 = k → v 1 = k → v 3 = k → False := by
    intro k h0 h1 h3
    apply hnc
    refine ⟨k, fun i => ?_⟩
    fin_cases i <;> simp <;> linarith
  rcases le_total ((v 0 - v 3) ^ 2) ((v 0 - v 1) ^ 2) with hs | hs
  · -- the `Q = +1` sector: move along `w = (1, 1, −1, −1)`, which keeps `δ` and shifts `σ` by `2ε`
    have hr0 : 0 < Real.sqrt ((v 0 - v 1) ^ 2 + 4) := Real.sqrt_pos.mpr (by positivity)
    have hr : Real.sqrt ((v 0 - v 1) ^ 2 + 4) ^ 2 = (v 0 - v 1) ^ 2 + 4 :=
      Real.sq_sqrt (by positivity)
    obtain ⟨ε, hε0, hεs⟩ : ∃ ε : ℝ, ε ≠ 0 ∧ (v 0 - v 3 + 2 * ε) ^ 2 ≤ (v 0 - v 1) ^ 2 := by
      by_cases hσ : v 0 - v 3 = 0
      · refine ⟨(v 0 - v 1) / 2, fun h => hconst (v 0) rfl (by linarith) (by linarith), ?_⟩
        rw [hσ]; nlinarith
      · exact ⟨-(v 0 - v 3), neg_ne_zero.mpr hσ, by nlinarith⟩
    refine ⟨_, v + ε • ![1, 1, -1, -1], ground_sq_plus hv rfl hr0 hr hs, ?_, ?_⟩
    · refine ground_sq_plus ?_ ?_ hr0 hr ?_
      · simp; linarith
      · simp
      · simp; nlinarith
    · rintro ⟨k, hk⟩
      have h0 := hk 0
      have h2 := hk 2
      simp at h0 h2
      exact hε0 (by linarith)
  · -- the `Q = −1` sector: move along `w = (1, −1, −1, 1)`, which keeps `σ` and shifts `δ` by `2ε`
    have hr0 : 0 < Real.sqrt ((v 0 - v 3) ^ 2 + 4) := Real.sqrt_pos.mpr (by positivity)
    have hr : Real.sqrt ((v 0 - v 3) ^ 2 + 4) ^ 2 = (v 0 - v 3) ^ 2 + 4 :=
      Real.sq_sqrt (by positivity)
    obtain ⟨ε, hε0, hεs⟩ : ∃ ε : ℝ, ε ≠ 0 ∧ (v 0 - v 1 + 2 * ε) ^ 2 ≤ (v 0 - v 3) ^ 2 := by
      by_cases hδ : v 0 - v 1 = 0
      · refine ⟨(v 0 - v 3) / 2, fun h => hconst (v 0) rfl (by linarith) (by linarith), ?_⟩
        rw [hδ]; nlinarith
      · exact ⟨-(v 0 - v 1), neg_ne_zero.mpr hδ, by nlinarith⟩
    refine ⟨_, v + ε • ![1, -1, -1, 1], ground_sq_minus hv rfl hr0 hr hs, ?_, ?_⟩
    · refine ground_sq_minus ?_ ?_ hr0 hr ?_
      · simp; linarith
      · simp
      · simp; nlinarith
    · rintro ⟨k, hk⟩
      have h0 := hk 0
      have h2 := hk 2
      simp at h0 h2
      exact hε0 (by linarith)

/-! ### The exact segment along a fixed direction -/

/-- On the plane `v₀ + v₂ = v₁ + v₃` the `Q = +1` state `(0, 2, r − δ, r + δ, 2, 0)`, `δ = v₀ − v₁`,
`r² = δ² + 4`, is an eigenvector with eigenvalue `v₁ + v₃ + 4 − r`, whatever `σ = v₀ − v₃`; it is a
ground state only when `σ² ≤ δ²` (`ground_sq_plus`, `square_segment_plus`). -/
lemma eigen_sq_plus {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {δ r : ℝ} (hδ : v 0 - v 1 = δ)
    (hr : r ^ 2 = δ ^ 2 + 4) :
    hamN H0sq occ4 v *ᵥ ![0, 2, r - δ, r + δ, 2, 0] =
      (v 1 + v 3 + 4 - r) • ![0, 2, r - δ, r + δ, 2, 0] := by
  subst hδ
  have h2 : v 2 = v 1 + v 3 - v 0 := by linarith
  ext i
  rw [hamN_mulVec_apply]
  fin_cases i <;>
    simp [H0sq, occ4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h2] <;>
    linarith [hr]

/-- The exact segment along `(1, 1, −1, −1)`: on the plane `v₀ + v₂ = v₁ + v₃`, the `Q = +1` state
`(0, 2, r − δ, r + δ, 2, 0)` of `v` (`δ = v₀ − v₁`, `r² = δ² + 4`) is a ground state of
`v + ε (1, 1, −1, −1)` if and only if `(v₀ − v₃ + 2ε)² ≤ δ²`. The direction keeps `δ` and the plane
and shifts `σ = v₀ − v₃` by `2ε`; beyond the segment the `Q = −1` state of the moved potential
`v + ε (1, 1, −1, −1)` is a test vector with a strictly lower Rayleigh quotient. -/
theorem square_segment_plus {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {δ r : ℝ}
    (hδ : v 0 - v 1 = δ) (hr0 : 0 < r) (hr : r ^ 2 = δ ^ 2 + 4) (ε : ℝ) :
    IsGroundState (hamN H0sq occ4 (v + ε • ![1, 1, -1, -1])) ![0, 2, r - δ, r + δ, 2, 0] ↔
      (v 0 - v 3 + 2 * ε) ^ 2 ≤ δ ^ 2 := by
  constructor
  · intro hψ
    by_contra hlt
    rw [not_le] at hlt
    subst hδ
    have hs0 : 0 < Real.sqrt ((v 0 - v 3 + 2 * ε) ^ 2 + 4) := Real.sqrt_pos.mpr (by positivity)
    have hs : Real.sqrt ((v 0 - v 3 + 2 * ε) ^ 2 + 4) ^ 2 = (v 0 - v 3 + 2 * ε) ^ 2 + 4 :=
      Real.sq_sqrt (by positivity)
    set s := Real.sqrt ((v 0 - v 3 + 2 * ε) ^ 2 + 4)
    have hrs : r < s := by nlinarith
    have h2 : v 2 = v 1 + v 3 - v 0 := by linarith
    have hid : qf (hamN H0sq occ4 (v + ε • ![1, 1, -1, -1]))
          ![s - (v 0 - v 3 + 2 * ε), 2, 0, 0, -2, -(s + (v 0 - v 3 + 2 * ε))] *
          (![0, 2, r - (v 0 - v 1), r + (v 0 - v 1), 2, 0] ⬝ᵥ
            ![0, 2, r - (v 0 - v 1), r + (v 0 - v 1), 2, 0]) -
        qf (hamN H0sq occ4 (v + ε • ![1, 1, -1, -1]))
            ![0, 2, r - (v 0 - v 1), r + (v 0 - v 1), 2, 0] *
          (![s - (v 0 - v 3 + 2 * ε), 2, 0, 0, -2, -(s + (v 0 - v 3 + 2 * ε))] ⬝ᵥ
            ![s - (v 0 - v 3 + 2 * ε), 2, 0, 0, -2, -(s + (v 0 - v 3 + 2 * ε))]) =
        16 * r ^ 2 * s ^ 2 * (r - s) := by
      rw [qf_sq, qf_sq]
      simp [dotProduct, Fin.sum_univ_succ]
      linear_combination
        (-32*ε^2*s - 24*ε*s*v 0 - 8*ε*s*v 1 + 8*ε*s*v 2 + 24*ε*s*v 3 - 16*r*s^2 + 16*s^3 -
          4*s*v 0^2 - 4*s*v 0*v 1 + 4*s*v 0*v 2 + 8*s*v 0*v 3 + 4*s*v 1*v 3 - 4*s*v 2*v 3 -
          4*s*v 3^2 - 32*s) * hr +
        (-12*r*v 0^2 + 24*r*v 0*v 1 - 4*r*v 0*v 2 + 4*r*v 0*v 3 - 12*r*v 1^2 + 4*r*v 1*v 2 -
          4*r*v 1*v 3 - 32*r + 16*s*v 0^2 - 32*s*v 0*v 1 + 16*s*v 1^2 + 64*s) * hs +
        (-32*ε^2*r*v 0 + 32*ε^2*r*v 1 - 32*ε*r*v 0^2 + 32*ε*r*v 0*v 1 + 32*ε*r*v 0*v 3 -
          32*ε*r*v 1*v 3 + 16*ε*s*v 0^2 - 32*ε*s*v 0*v 1 + 16*ε*s*v 1^2 + 64*ε*s - 8*r*v 0^3 +
          8*r*v 0^2*v 1 + 16*r*v 0^2*v 3 - 16*r*v 0*v 1*v 3 - 8*r*v 0*v 3^2 - 32*r*v 0 +
          8*r*v 1*v 3^2 + 32*r*v 1 + 8*s*v 0^3 - 16*s*v 0^2*v 1 - 8*s*v 0^2*v 3 +
          8*s*v 0*v 1^2 + 16*s*v 0*v 1*v 3 + 32*s*v 0 - 8*s*v 1^2*v 3 - 32*s*v 3) * h2
    have key := hψ.2 ![s - (v 0 - v 3 + 2 * ε), 2, 0, 0, -2, -(s + (v 0 - v 3 + 2 * ε))]
    have hpos : 0 < 16 * r ^ 2 * s ^ 2 * (s - r) := by
      have := sub_pos.mpr hrs
      positivity
    linarith
  · intro hs
    refine ground_sq_plus ?_ ?_ hr0 hr ?_
    · simp; linarith
    · simp; linarith
    · simp; nlinarith

/-- The exact segment along `(1, −1, −1, 1)`: on the plane `v₀ + v₂ = v₁ + v₃`, the `Q = −1` state
`(r − σ, 2, 0, 0, −2, −(r + σ))` of `v` (`σ = v₀ − v₃`, `r² = σ² + 4`) is a ground state of
`v + ε (1, −1, −1, 1)` if and only if `(v₀ − v₁ + 2ε)² ≤ σ²` (the mirror of
`square_segment_plus`). -/
theorem square_segment_minus {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {σ r : ℝ}
    (hσ : v 0 - v 3 = σ) (hr0 : 0 < r) (hr : r ^ 2 = σ ^ 2 + 4) (ε : ℝ) :
    IsGroundState (hamN H0sq occ4 (v + ε • ![1, -1, -1, 1])) ![r - σ, 2, 0, 0, -2, -(r + σ)] ↔
      (v 0 - v 1 + 2 * ε) ^ 2 ≤ σ ^ 2 := by
  constructor
  · intro hψ
    by_contra hlt
    rw [not_le] at hlt
    subst hσ
    have hs0 : 0 < Real.sqrt ((v 0 - v 1 + 2 * ε) ^ 2 + 4) := Real.sqrt_pos.mpr (by positivity)
    have hs : Real.sqrt ((v 0 - v 1 + 2 * ε) ^ 2 + 4) ^ 2 = (v 0 - v 1 + 2 * ε) ^ 2 + 4 :=
      Real.sq_sqrt (by positivity)
    set s := Real.sqrt ((v 0 - v 1 + 2 * ε) ^ 2 + 4)
    have hrs : r < s := by nlinarith
    have h2 : v 2 = v 1 + v 3 - v 0 := by linarith
    have hid : qf (hamN H0sq occ4 (v + ε • ![1, -1, -1, 1]))
          ![0, 2, s - (v 0 - v 1 + 2 * ε), s + (v 0 - v 1 + 2 * ε), 2, 0] *
          (![r - (v 0 - v 3), 2, 0, 0, -2, -(r + (v 0 - v 3))] ⬝ᵥ
            ![r - (v 0 - v 3), 2, 0, 0, -2, -(r + (v 0 - v 3))]) -
        qf (hamN H0sq occ4 (v + ε • ![1, -1, -1, 1]))
            ![r - (v 0 - v 3), 2, 0, 0, -2, -(r + (v 0 - v 3))] *
          (![0, 2, s - (v 0 - v 1 + 2 * ε), s + (v 0 - v 1 + 2 * ε), 2, 0] ⬝ᵥ
            ![0, 2, s - (v 0 - v 1 + 2 * ε), s + (v 0 - v 1 + 2 * ε), 2, 0]) =
        16 * r ^ 2 * s ^ 2 * (r - s) := by
      rw [qf_sq, qf_sq]
      simp [dotProduct, Fin.sum_univ_succ]
      linear_combination
        (-32*ε^2*s - 24*ε*s*v 0 + 24*ε*s*v 1 + 8*ε*s*v 2 - 8*ε*s*v 3 - 16*r*s^2 + 16*s^3 -
          4*s*v 0^2 + 8*s*v 0*v 1 + 4*s*v 0*v 2 - 4*s*v 0*v 3 - 4*s*v 1^2 - 4*s*v 1*v 2 +
          4*s*v 1*v 3 - 32*s) * hr +
        (-12*r*v 0^2 + 4*r*v 0*v 1 - 4*r*v 0*v 2 + 24*r*v 0*v 3 - 4*r*v 1*v 3 + 4*r*v 2*v 3 -
          12*r*v 3^2 - 32*r + 16*s*v 0^2 - 32*s*v 0*v 3 + 16*s*v 3^2 + 64*s) * hs +
        (-32*ε^2*r*v 0 + 32*ε^2*r*v 3 - 32*ε*r*v 0^2 + 32*ε*r*v 0*v 1 + 32*ε*r*v 0*v 3 -
          32*ε*r*v 1*v 3 + 16*ε*s*v 0^2 - 32*ε*s*v 0*v 3 + 16*ε*s*v 3^2 + 64*ε*s - 8*r*v 0^3 +
          16*r*v 0^2*v 1 + 8*r*v 0^2*v 3 - 8*r*v 0*v 1^2 - 16*r*v 0*v 1*v 3 - 32*r*v 0 +
          8*r*v 1^2*v 3 + 32*r*v 3 + 8*s*v 0^3 - 8*s*v 0^2*v 1 - 16*s*v 0^2*v 3 +
          16*s*v 0*v 1*v 3 + 8*s*v 0*v 3^2 + 32*s*v 0 - 8*s*v 1*v 3^2 - 32*s*v 1) * h2
    have key := hψ.2 ![0, 2, s - (v 0 - v 1 + 2 * ε), s + (v 0 - v 1 + 2 * ε), 2, 0]
    have hpos : 0 < 16 * r ^ 2 * s ^ 2 * (s - r) := by
      have := sub_pos.mpr hrs
      positivity
    linarith
  · intro hs
    refine ground_sq_minus ?_ ?_ hr0 hr ?_
    · simp; linarith
    · simp; linarith
    · simp; nlinarith

/-- The square counterexample `v = (3/4, −3/4, −3/4, 3/4)`, `Ψ_A ∝ (0, 2, 1, 4, 2, 0)`: `Ψ_A` is a
ground state of `v + ε (1, 1, −1, −1)` exactly for `|ε| ≤ 3/4`, three times the bound `g/2 = 1/4`
of `square_wall_plus` (here `σ = 0`, so its direction is `(1, 1, −1, −1)`; gap `g = 1/2`:
`square_gap₀`, `square_gap₀_sharp`). Beyond the segment `Ψ_A` is still an eigenvector
(`eigen_sq_plus`), not a ground state. -/
theorem square_example_segment (ε : ℝ) :
    IsGroundState (hamN H0sq occ4 (![3/4, -3/4, -3/4, 3/4] + ε • ![1, 1, -1, -1]))
      ![0, 2, 1, 4, 2, 0] ↔ |ε| ≤ 3/4 := by
  have h := square_segment_plus (v := ![3/4, -3/4, -3/4, 3/4]) (δ := 3/2) (r := 5/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ε
  have hvec : (![0, 2, 5/2 - 3/2, 5/2 + 3/2, 2, 0] : Fin 6 → ℝ) = ![0, 2, 1, 4, 2, 0] := by
    norm_num
  rw [hvec] at h
  rw [h, abs_le]
  simp only [Fin.isValue, cons_val_zero, cons_val, sub_self, zero_add]
  constructor
  · intro h1; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; nlinarith

section shared
variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- If `ψ` is a ground state of `H(v)` and of `H(v')`, then `Σᵢ (vᵢ − v'ᵢ) nᵢ(c)` takes one value on
the support of `ψ` (the argument inside `strong_hk`). -/
lemma support_const_of_shared {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    {v v' : V → ℝ} {ψ : C → ℝ} (hψ : IsGroundState (hamN H0 n v) ψ)
    (hψ' : IsGroundState (hamN H0 n v') ψ) :
    ∃ κ : ℝ, ∀ c, ψ c ≠ 0 → ∑ i, (v i - v' i) * n i c = κ := by
  have e1 := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
  have e2 := isGroundState_eigen (hamN_isSymm hH0 n v') hψ'
  refine ⟨qf (hamN H0 n v) ψ / (ψ ⬝ᵥ ψ) - qf (hamN H0 n v') ψ / (ψ ⬝ᵥ ψ), fun c hc => ?_⟩
  have h1 := congrFun e1 c
  have h2 := congrFun e2 c
  rw [hamN_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have hs : ∑ i, (v i - v' i) * n i c = ∑ i, v i * n i c - ∑ i, v' i * n i c := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  apply mul_right_cancel₀ hc
  rw [hs]
  linear_combination h1 - h2

end shared

/-- A ground state of two fermions on the square at a constant potential is a ground state of
`H(v')` only if `v'` is constant (for every state of the twofold-degenerate ground level). -/
theorem square_const_shared (k : ℝ) {ψ : Fin 6 → ℝ} {v' : Fin 4 → ℝ}
    (hψ : IsGroundState (hamN H0sq occ4 fun _ => k) ψ)
    (hψ' : IsGroundState (hamN H0sq occ4 v') ψ) : ∃ c : ℝ, ∀ i, k - v' i = c := by
  -- the ground space of the uniform square: four squares vanish
  have hp := hψ.2 ![0, 1, 1, 1, 1, 0]
  rw [qf_sq, qf_sq] at hp
  simp only [Fin.isValue, dotProduct, Fin.sum_univ_succ, cons_val_zero, mul_zero, cons_val_succ,
      mul_one, Finset.univ_unique, Fin.default_eq_zero, cons_val_fin_one, Finset.sum_const_zero,
      add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      cons_val_one, sub_self, cons_val, one_pow, one_mul, sub_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Fin.reduceSucc, Finset.sum_singleton] at hp
  have hS : 2 * (ψ 2 - (ψ 1 + ψ 4) / 2) ^ 2 + 2 * (ψ 3 - (ψ 1 + ψ 4) / 2) ^ 2 +
      2 * (ψ 0 - (ψ 1 - ψ 4) / 2) ^ 2 + 2 * (ψ 5 + (ψ 1 - ψ 4) / 2) ^ 2 ≤ 0 := by
    linear_combination hp / 4
  have z1 : (ψ 2 - (ψ 1 + ψ 4) / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (ψ 2 - (ψ 1 + ψ 4) / 2), sq_nonneg (ψ 3 - (ψ 1 + ψ 4) / 2),
      sq_nonneg (ψ 0 - (ψ 1 - ψ 4) / 2), sq_nonneg (ψ 5 + (ψ 1 - ψ 4) / 2)]
  have z2 : (ψ 3 - (ψ 1 + ψ 4) / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (ψ 2 - (ψ 1 + ψ 4) / 2), sq_nonneg (ψ 3 - (ψ 1 + ψ 4) / 2),
      sq_nonneg (ψ 0 - (ψ 1 - ψ 4) / 2), sq_nonneg (ψ 5 + (ψ 1 - ψ 4) / 2)]
  have z3 : (ψ 0 - (ψ 1 - ψ 4) / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (ψ 2 - (ψ 1 + ψ 4) / 2), sq_nonneg (ψ 3 - (ψ 1 + ψ 4) / 2),
      sq_nonneg (ψ 0 - (ψ 1 - ψ 4) / 2), sq_nonneg (ψ 5 + (ψ 1 - ψ 4) / 2)]
  have z4 : (ψ 5 + (ψ 1 - ψ 4) / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (ψ 2 - (ψ 1 + ψ 4) / 2), sq_nonneg (ψ 3 - (ψ 1 + ψ 4) / 2),
      sq_nonneg (ψ 0 - (ψ 1 - ψ 4) / 2), sq_nonneg (ψ 5 + (ψ 1 - ψ 4) / 2)]
  have e1 : ψ 1 = ψ 2 + ψ 0 := by
    have := pow_eq_zero_iff two_ne_zero |>.mp z1
    have := pow_eq_zero_iff two_ne_zero |>.mp z3
    linarith
  have e4 : ψ 4 = ψ 2 - ψ 0 := by
    have := pow_eq_zero_iff two_ne_zero |>.mp z1
    have := pow_eq_zero_iff two_ne_zero |>.mp z3
    linarith
  have e3 : ψ 3 = ψ 2 := by
    have := pow_eq_zero_iff two_ne_zero |>.mp z1
    have := pow_eq_zero_iff two_ne_zero |>.mp z2
    linarith
  have e5 : ψ 5 = -ψ 0 := by
    have := pow_eq_zero_iff two_ne_zero |>.mp z3
    have := pow_eq_zero_iff two_ne_zero |>.mp z4
    linarith
  clear hp hS z1 z2 z3 z4
  -- the potential difference is constant on the support
  obtain ⟨κ, hκ⟩ := support_const_of_shared H0sq_isSymm hψ hψ'
  have hκ' : ∀ c, ψ c ≠ 0 → ∑ i, (k - v' i) * occ4 i c = κ := hκ
  have s0 := hκ' 0
  have s1 := hκ' 1
  have s2 := hκ' 2
  have s3 := hκ' 3
  have s4 := hκ' 4
  have s5 := hκ' 5
  simp only [Fin.isValue, ne_eq, occ4, cons_val', cons_val_zero, cons_val_fin_one,
      Fin.sum_univ_succ, mul_one, cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      mul_zero, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const_zero, add_zero,
      cons_val_one, zero_add, cons_val, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_singleton, one_smul, Finset.sum_singleton, Fin.reduceSucc] at s0 s1 s2 s3 s4 s5
  by_cases ha : ψ 2 = 0 <;> by_cases hb : ψ 0 = 0
  · exfalso
    apply hψ.1
    funext i
    fin_cases i <;> simp <;> linarith
  · -- ψ = ψ₀ (1, 1, 0, 0, −1, −1): v' = (p, q, q, p), then p = q
    have t0 := s0 hb
    have t1 := s1 (by rw [e1, ha]; simpa using hb)
    have t4 := s4 (by rw [e4, ha]; simpa using hb)
    have t5 := s5 (by rw [e5]; simpa using hb)
    have h12 : v' 2 = v' 1 := by linarith
    have h30 : v' 3 = v' 0 := by linarith
    have ht := hψ'.2 ![0, 2, 2 - (v' 0 - v' 1), 2 + (v' 0 - v' 1), 2, 0]
    rw [qf_sq, qf_sq] at ht
    simp only [Fin.isValue, dotProduct, Fin.sum_univ_succ, cons_val_zero, mul_zero, cons_val_succ,
        Finset.univ_unique, Fin.default_eq_zero, cons_val_fin_one, Finset.sum_const_zero, add_zero,
        zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, cons_val_one,
        sub_self, cons_val, sub_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
        Finset.sum_singleton] at ht
    rw [e1, e3, e4, e5, ha, h12, h30] at ht
    have hb2 : 0 < ψ 0 ^ 2 := by positivity
    have h16 : ψ 0 ^ 2 * (16 * (v' 0 - v' 1) ^ 2) ≤ 0 := by linear_combination ht
    have hpq : (v' 0 - v' 1) ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < 16 * (v' 0 - v' 1) ^ 2 :=
        mul_pos (by norm_num) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne))
      have := mul_pos hb2 hpos
      linarith
    have h01 : v' 0 = v' 1 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp hpq; linarith
    exact ⟨k - v' 0, fun i => by fin_cases i <;> simp <;> linarith⟩
  · -- ψ = ψ₂ (0, 1, 1, 1, 1, 0): v' = (p, p, q, q), then p = q
    have t1 := s1 (by rw [e1, hb]; simpa using ha)
    have t2 := s2 ha
    have t3 := s3 (by rw [e3]; exact ha)
    have t4 := s4 (by rw [e4, hb]; simpa using ha)
    have h10 : v' 1 = v' 0 := by linarith
    have h32 : v' 3 = v' 2 := by linarith
    have ht := hψ'.2 ![2 - (v' 0 - v' 2), 2, 0, 0, -2, -(2 + (v' 0 - v' 2))]
    rw [qf_sq, qf_sq] at ht
    simp only [Fin.isValue, dotProduct, neg_add_rev, neg_sub, Fin.sum_univ_succ, cons_val_zero,
        cons_val_succ, mul_zero, mul_neg, neg_mul, neg_neg, Finset.univ_unique,
        Fin.default_eq_zero, cons_val_fin_one, Finset.sum_const, Finset.card_singleton, one_smul,
        zero_add, cons_val_one, cons_val, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul, add_zero, neg_zero, even_two, Even.neg_pow, sub_neg_eq_add,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Finset.sum_singleton] at ht
    rw [e1, e3, e4, e5, hb, h10, h32] at ht
    have ha2 : 0 < ψ 2 ^ 2 := by positivity
    have h16 : ψ 2 ^ 2 * (16 * (v' 0 - v' 2) ^ 2) ≤ 0 := by linear_combination ht
    have hpq : (v' 0 - v' 2) ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < 16 * (v' 0 - v' 2) ^ 2 :=
        mul_pos (by norm_num) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne))
      have := mul_pos ha2 hpos
      linarith
    have h02 : v' 0 = v' 2 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp hpq; linarith
    exact ⟨k - v' 0, fun i => by fin_cases i <;> simp <;> linarith⟩
  · -- both amplitudes nonzero: at least five configurations, all couplings equal
    have t0 := s0 hb
    have t2 := s2 ha
    have t3 := s3 (by rw [e3]; exact ha)
    have t5 := s5 (by rw [e5]; simpa using hb)
    by_cases hab : ψ 2 + ψ 0 = 0
    · have t4 := s4 (by rw [e4]; intro h; exact ha (by linarith))
      exact ⟨k - v' 0, fun i => by fin_cases i <;> simp <;> linarith only [t0, t2, t3, t5, t4]⟩
    · have t1 := s1 (by rw [e1]; exact hab)
      exact ⟨k - v' 0, fun i => by fin_cases i <;> simp <;> linarith only [t0, t2, t3, t5, t1]⟩

/-- **`square_wall` with the direction fixed.** The direction `w` of `square_wall` is
existential, so its bound `|ε| ≤ g/2` carries no information as stated (rescaling `w` rescales the
bound). The proof's witness is one of the two directions with entries ±1, `(1, 1, −1, −1)` (sector
`Q = +1`) and `(1, −1, −1, 1)` (sector `Q = −1`), for which `|ε| ≤ g/2` is the bound proved. -/
theorem square_wall_unit {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {ψ : Fin 6 → ℝ}
    (hψ : IsGroundState (hamN H0sq occ4 v) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamN H0sq occ4 v) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamN H0sq occ4 v) χ) :
    ∃ w : Fin 4 → ℝ, (w = ![1, 1, -1, -1] ∨ w = ![1, -1, -1, 1]) ∧
      ∀ ε : ℝ, |ε| * 2 ≤ g → IsGroundState (hamN H0sq occ4 (v + ε • w)) ψ := by
  set H := hamN H0sq occ4 v
  have hS : H.IsSymm := hamN_isSymm H0sq_isSymm occ4 v
  -- Qψ is also a ground state, hence a multiple of ψ
  have hQ : IsGroundState H (Qsq ψ) := by
    refine ⟨fun h => hψ.1 ?_, fun φ => ?_⟩
    · have h' : Qsq ψ ⬝ᵥ Qsq ψ = 0 := by rw [h]; simp
      rw [dot_Qsq] at h'; exact dotProduct_self_eq_zero.mp h'
    · rw [qf_Qsq hv, dot_Qsq]; exact hψ.2 φ
  have hc := unique_of_gap hS hψ hN hg hgap hQ
  set c := ψ ⬝ᵥ Qsq ψ
  have e : ∀ i, Qsq ψ i = c * ψ i := fun i => by
    have := congrFun hc i; simpa using this
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  simp only [Qsq, Fin.isValue, cons_val_zero, cons_val_one, cons_val] at e0 e1 e2 e3 e4 e5
  -- c² = 1
  have p0 : (c ^ 2 - 1) * ψ 0 = 0 := by linear_combination (-c + 1) * e0
  have p1 : (c ^ 2 - 1) * ψ 1 = 0 := by linear_combination -e4 - c * e1
  have p2 : (c ^ 2 - 1) * ψ 2 = 0 := by linear_combination (-c - 1) * e2
  have p3 : (c ^ 2 - 1) * ψ 3 = 0 := by linear_combination (-c - 1) * e3
  have p4 : (c ^ 2 - 1) * ψ 4 = 0 := by linear_combination -e1 - c * e4
  have p5 : (c ^ 2 - 1) * ψ 5 = 0 := by linear_combination (-c + 1) * e5
  have hc2 : ∀ i, (c ^ 2 - 1) * ψ i = 0 := by
    intro i; fin_cases i
    exacts [p0, p1, p2, p3, p4, p5]
  have hcc : c ^ 2 = 1 := by
    by_contra hne
    exact hψ.1 (funext fun i => by
      have := hc2 i; rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linarith) hne
      · simpa using h)
  have hc' : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hc' with h1 | h1
  · -- sector Q = +1: ψ(01) = ψ(23) = 0; invisible w = (1, 1, -1, -1)
    have z0 : ψ 0 = 0 := by rw [h1] at e0; linarith
    have z5 : ψ 5 = 0 := by rw [h1] at e5; linarith
    refine ⟨![1, 1, -1, -1], Or.inl rfl, fun ε hε => ?_⟩
    refine persist_of_gap H0sq_isSymm hψ hN hgap (κ := 0) (m := 2) ?_ ?_ hε
    · intro c hc; fin_cases c
      · exact absurd z0 hc
      all_goals first | exact absurd z5 hc | simp [occ4, Fin.sum_univ_succ]
    · intro c; fin_cases c <;> norm_num [occ4, Fin.sum_univ_succ]
  · -- sector Q = -1: ψ(03) = ψ(12) = 0; invisible w = (1, -1, -1, 1)
    have z2 : ψ 2 = 0 := by rw [h1] at e2; linarith
    have z3 : ψ 3 = 0 := by rw [h1] at e3; linarith
    refine ⟨![1, -1, -1, 1], Or.inr rfl, fun ε hε => ?_⟩
    refine persist_of_gap H0sq_isSymm hψ hN hgap (κ := 0) (m := 2) ?_ ?_ hε
    · intro c hc; fin_cases c
      all_goals first | exact absurd z2 hc | exact absurd z3 hc | simp [occ4, Fin.sum_univ_succ]
    · intro c; fin_cases c <;> norm_num [occ4, Fin.sum_univ_succ]

/-- **The direction of the wall.** On the plane `v₀ + v₂ = v₁ + v₃`, at a gapped ground state, if
`(v₀ − v₃)² ≤ (v₀ − v₁)²` (paper: `|v₁ − v₄| ≤ |v₁ − v₂|`) the ground state is shared along
`w = (1, 1, −1, −1)`: by the gap it is a multiple of the explicit state of `ground_sq_plus`, which
vanishes on the configurations `01` and `23`. -/
theorem square_wall_plus {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {ψ : Fin 6 → ℝ}
    (hψ : IsGroundState (hamN H0sq occ4 v) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamN H0sq occ4 v) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamN H0sq occ4 v) χ)
    (hs : (v 0 - v 3) ^ 2 ≤ (v 0 - v 1) ^ 2) :
    ∀ ε : ℝ, |ε| * 2 ≤ g → IsGroundState (hamN H0sq occ4 (v + ε • ![1, 1, -1, -1])) ψ := by
  have hS : (hamN H0sq occ4 v).IsSymm := hamN_isSymm H0sq_isSymm occ4 v
  set r := Real.sqrt ((v 0 - v 1) ^ 2 + 4)
  have hp := ground_sq_plus hv rfl (Real.sqrt_pos.2 (by positivity))
    (Real.sq_sqrt (by positivity)) hs
  have hu := unique_of_gap hS hψ hN hg hgap hp
  set a := ψ ⬝ᵥ ![0, 2, r - (v 0 - v 1), r + (v 0 - v 1), 2, 0]
  have h1 := congrFun hu 1
  have h0 := congrFun hu 0
  have h5 := congrFun hu 5
  simp only [Pi.smul_apply, smul_eq_mul, Fin.isValue, cons_val_one, cons_val_zero] at h0 h1
  have ha : a ≠ 0 := by
    intro ha; rw [ha, zero_mul] at h1; norm_num at h1
  have z0 : ψ 0 = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exact absurd h ha
    · exact h
  have z5 : ψ 5 = 0 := by
    have h5' : (0 : ℝ) = a * ψ 5 := by simpa using h5
    rcases mul_eq_zero.1 h5'.symm with h | h
    · exact absurd h ha
    · exact h
  intro ε hε
  refine persist_of_gap H0sq_isSymm hψ hN hgap (κ := 0) (m := 2) ?_ ?_ hε
  · intro c hc; fin_cases c
    · exact absurd z0 hc
    all_goals first | exact absurd z5 hc | simp [occ4, Fin.sum_univ_succ]
  · intro c; fin_cases c <;> norm_num [occ4, Fin.sum_univ_succ]

/-- The other case: if `(v₀ − v₁)² ≤ (v₀ − v₃)²` the gapped ground state is shared along
`w = (1, −1, −1, 1)` (a multiple of the state of `ground_sq_minus`, vanishing on `03` and `12`). -/
theorem square_wall_minus {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {ψ : Fin 6 → ℝ}
    (hψ : IsGroundState (hamN H0sq occ4 v) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamN H0sq occ4 v) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamN H0sq occ4 v) χ)
    (hs : (v 0 - v 1) ^ 2 ≤ (v 0 - v 3) ^ 2) :
    ∀ ε : ℝ, |ε| * 2 ≤ g → IsGroundState (hamN H0sq occ4 (v + ε • ![1, -1, -1, 1])) ψ := by
  have hS : (hamN H0sq occ4 v).IsSymm := hamN_isSymm H0sq_isSymm occ4 v
  set r := Real.sqrt ((v 0 - v 3) ^ 2 + 4)
  have hp := ground_sq_minus hv rfl (Real.sqrt_pos.2 (by positivity))
    (Real.sq_sqrt (by positivity)) hs
  have hu := unique_of_gap hS hψ hN hg hgap hp
  set a := ψ ⬝ᵥ ![r - (v 0 - v 3), 2, 0, 0, -2, -(r + (v 0 - v 3))]
  have h1 := congrFun hu 1
  have h2 := congrFun hu 2
  have h3 := congrFun hu 3
  simp only [Pi.smul_apply, smul_eq_mul, Fin.isValue, cons_val_one, cons_val_zero] at h1
  have ha : a ≠ 0 := by
    intro ha; rw [ha, zero_mul] at h1; norm_num at h1
  have z2 : ψ 2 = 0 := by
    have h2' : (0 : ℝ) = a * ψ 2 := by simpa using h2
    rcases mul_eq_zero.1 h2'.symm with h | h
    · exact absurd h ha
    · exact h
  have z3 : ψ 3 = 0 := by
    have h3' : (0 : ℝ) = a * ψ 3 := by simpa using h3
    rcases mul_eq_zero.1 h3'.symm with h | h
    · exact absurd h ha
    · exact h
  intro ε hε
  refine persist_of_gap H0sq_isSymm hψ hN hgap (κ := 0) (m := 2) ?_ ?_ hε
  · intro c hc; fin_cases c
    all_goals first | exact absurd z2 hc | exact absurd z3 hc | simp [occ4, Fin.sum_univ_succ]
  · intro c; fin_cases c <;> norm_num [occ4, Fin.sum_univ_succ]

/-- **Every non-constant potential of the plane `v₀ + v₂ = v₁ + v₃` is exceptional** for two
fermions on the square (non-uniquely v-representable, `NonUV`), with no gap hypothesis. This
formalizes the plane of Penz and van Leeuwen (J. Chem. Phys. 155, 244111 (2021), Secs. III C and
IV B, Eqs. (45)–(49), Fig. 4), whose explicit states are `ground_sq_plus`, `ground_sq_minus`. -/
theorem square_plane_exceptional {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3)
    (hnc : ¬ ∃ k : ℝ, ∀ i, v i = k) : NonUV H0sq occ4 v :=
  square_plane_shared hv hnc

/-- **The uniform square is not exceptional**: a constant potential lies on the plane
`v₀ + v₂ = v₁ + v₃` but is not `NonUV`. With `square_plane_exceptional`: on the plane, exactly the
non-constant potentials are exceptional. -/
theorem square_const_not_exceptional (k : ℝ) : ¬ NonUV H0sq occ4 (fun _ => k) := by
  rintro ⟨ψ, v', h1, h2, h3⟩
  obtain ⟨c, hc⟩ := square_const_shared k h1 h2
  exact h3 ⟨c, hc⟩

/-- **The exceptional set of the square is not closed.** The potentials `(t, 0, 0, t)`, `t ≠ 0`, lie
on the plane and are exceptional (`square_plane_exceptional`); they tend to `0`, which is not
exceptional (`square_const_not_exceptional`). So the exceptional set is contained in a closed,
nowhere dense, null set (`square_generic_hk_ae`) but is not itself closed. -/
theorem square_exceptional_not_closed :
    ¬ IsClosed {v : Fin 4 → ℝ | NonUV H0sq occ4 v} := by
  intro hcl
  have hmem : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) • (![1, 0, 0, 1] : Fin 4 → ℝ) ∈
      {v : Fin 4 → ℝ | NonUV H0sq occ4 v} := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact square_plane_exceptional
      (v := (1 / ((n : ℝ) + 1)) • ![1, 0, 0, 1]) (by simp) (by
        rintro ⟨k, hk⟩
        have e0 := hk 0
        have e1 := hk 1
        simp at e0 e1
        have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
        linarith)
  have hlim : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • (![1, 0, 0, 1] : Fin 4 → ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := h1.smul_const (![1, 0, 0, 1] : Fin 4 → ℝ)
    simpa using this
  exact square_const_not_exceptional 0 (hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem))

/-- A nonzero multiple of a ground state is a ground state. -/
lemma isGroundState_smul {V : Type*} [Fintype V] {M : Matrix V V ℝ} {ψ : V → ℝ}
    (h : IsGroundState M ψ) {a : ℝ} (ha : a ≠ 0) : IsGroundState M (a • ψ) := by
  refine ⟨smul_ne_zero ha h.1, fun φ => ?_⟩
  have h2 := h.2 φ
  have hq : qf M (a • ψ) = a ^ 2 * qf M ψ := by
    simp only [qf, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  have hn : (a • ψ) ⬝ᵥ (a • ψ) = a ^ 2 * (ψ ⬝ᵥ ψ) := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  rw [hq, hn]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg a)]

section sharedDens

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- Densities of normalized ground states of two potentials that differ by more than a constant
(the densities "produced by more than one potential"; real pure states, degenerate ground states
allowed; `SharedEnsDens` is the ensemble version). -/
def SharedDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) : Set (V → ℝ) :=
  {ρ | ∃ (v v' : V → ℝ) (ψ ψ' : C → ℝ), IsGroundState (hamN H0 n v) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧
      IsGroundState (hamN H0 n v') ψ' ∧ ψ' ⬝ᵥ ψ' = 1 ∧ dens n ψ = ρ ∧ dens n ψ' = ρ ∧
      ¬ ∃ k, ∀ i, v i - v' i = k}

end sharedDens

/-- The normalized `Q = +1` state of `ground_sq_plus` along `δ = t`: `(0, 2, r − t, r + t, 2, 0)`
with `r = √(t² + 4)`, divided by its norm `√(16 + 4t²)`. -/
noncomputable def psiSq (t : ℝ) : Fin 6 → ℝ :=
  (1 / Real.sqrt (16 + 4 * t ^ 2)) •
    ![0, 2, Real.sqrt (t ^ 2 + 4) - t, Real.sqrt (t ^ 2 + 4) + t, 2, 0]

lemma psiSq_norm (t : ℝ) : psiSq t ⬝ᵥ psiSq t = 1 := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ t ^ 2 + 4 by positivity)
  have hN := Real.sq_sqrt (show (0 : ℝ) ≤ 16 + 4 * t ^ 2 by positivity)
  simp [psiSq, dotProduct, Fin.sum_univ_succ]
  field_simp
  nlinarith [hr, hN]

lemma psiSq_ground {v : Fin 4 → ℝ} (hv : v 0 + v 2 = v 1 + v 3) {t : ℝ} (hδ : v 0 - v 1 = t)
    (hs : (v 0 - v 3) ^ 2 ≤ t ^ 2) : IsGroundState (hamN H0sq occ4 v) (psiSq t) := by
  exact isGroundState_smul (ground_sq_plus hv hδ (Real.sqrt_pos.2 (by positivity))
    (Real.sq_sqrt (by positivity)) hs) (by positivity)

lemma continuous_dens_psiSq : Continuous fun t => dens occ4 (psiSq t) := by
  unfold dens psiSq
  fun_prop (disch := intro x; positivity)

/-- For `t ≠ 0`, the density of `psiSq t` is produced by `(t, 0, 0, t)` and by
`(t, 0, 0, t) + (t/2)·(1, 1, −1, −1)`. -/
lemma psiSq_mem_sharedDens {t : ℝ} (ht : t ≠ 0) : dens occ4 (psiSq t) ∈ SharedDens H0sq occ4 := by
  refine ⟨![t, 0, 0, t], ![t + t / 2, t / 2, -(t / 2), t - t / 2], psiSq t, psiSq t,
    psiSq_ground (by simp) (by simp) (by simpa using sq_nonneg t), psiSq_norm t,
    psiSq_ground (by simp) (by simp) (by simp), psiSq_norm t, rfl, rfl, ?_⟩
  rintro ⟨k, hk⟩
  have e0 := hk 0
  have e2 := hk 2
  simp at e0 e2
  exact ht (by linarith)

/-- The uniform density `(1/2, 1/2, 1/2, 1/2)` of `psiSq 0` is produced only by constant
potentials: by the weak Hohenberg–Kohn argument, any potential producing it has `psiSq 0`, a
ground state of the uniform square, as a ground state, and `square_const_shared` forces it to be
constant. -/
lemma psiSq_zero_not_mem_sharedDens : dens occ4 (psiSq 0) ∉ SharedDens H0sq occ4 := by
  rintro ⟨v, v', ψ, ψ', hψ, hN, hψ', hN', hd, hd', hnc⟩
  have hχ : IsGroundState (hamN H0sq occ4 fun _ => (0 : ℝ)) (psiSq 0) :=
    psiSq_ground (by simp) (by simp) (by simp)
  obtain ⟨c, hc⟩ := square_const_shared 0 hχ (weak_hk hχ hψ (psiSq_norm 0) hN hd.symm).1
  obtain ⟨c', hc'⟩ := square_const_shared 0 hχ (weak_hk hχ hψ' (psiSq_norm 0) hN' hd'.symm).1
  exact hnc ⟨c' - c, fun i => by linarith [hc i, hc' i]⟩

/-- **The densities produced by more than one potential do not form a closed set** (two fermions
on the square). The densities of `psiSq t`, `t ≠ 0`, are produced by two potentials
(`psiSq_mem_sharedDens`); as `t → 0` they tend to the uniform density, which only constant
potentials produce (`psiSq_zero_not_mem_sharedDens`). -/
theorem square_sharedDens_not_closed : ¬ IsClosed (SharedDens H0sq occ4) := by
  intro hcl
  have hlim : Filter.Tendsto (fun k : ℕ => dens occ4 (psiSq (1 / ((k : ℝ) + 1))))
      Filter.atTop (nhds (dens occ4 (psiSq 0))) :=
    (continuous_dens_psiSq.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact psiSq_zero_not_mem_sharedDens (hcl.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun k => psiSq_mem_sharedDens (by positivity)))

/-- The uniform density: `dens occ4 (psiSq 0) = (1/2, 1/2, 1/2, 1/2)`. -/
lemma dens_psiSq_zero : dens occ4 (psiSq 0) = fun _ => 1 / 2 := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  funext i
  fin_cases i <;> simp [dens, psiSq, occ4, Fin.sum_univ_succ, h16, h4] <;> norm_num

section ensDens

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- Densities of ground-state ensembles of `H(v)`: convex combinations of the densities of
finitely many normalized (real) ground states. -/
def EnsDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Set (V → ℝ) :=
  {ρ | ∃ (m : ℕ) (w : Fin m → ℝ) (ψ : Fin m → C → ℝ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (∀ k, IsGroundState (hamN H0 n v) (ψ k) ∧ ψ k ⬝ᵥ ψ k = 1) ∧ ∑ k, w k • dens n (ψ k) = ρ}

/-- Densities of ground-state ensembles of two potentials that differ by more than a constant (the
non-uniquely v-representable densities of Penz and van Leeuwen, for real states). -/
def SharedEnsDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) : Set (V → ℝ) :=
  {ρ | ∃ v v' : V → ℝ, ρ ∈ EnsDens H0 n v ∧ ρ ∈ EnsDens H0 n v' ∧ ¬ ∃ k, ∀ i, v i - v' i = k}

/-- A pure-state density is an ensemble density (one state, weight one). -/
lemma dens_mem_ensDens {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v : V → ℝ} {ψ : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) (hN : ψ ⬝ᵥ ψ = 1) : dens n ψ ∈ EnsDens H0 n v :=
  ⟨1, fun _ => 1, fun _ => ψ, fun _ => zero_le_one, by simp, fun _ => ⟨hψ, hN⟩, by simp⟩

lemma sharedDens_subset_sharedEnsDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) :
    SharedDens H0 n ⊆ SharedEnsDens H0 n := by
  rintro ρ ⟨v, v', ψ, ψ', hψ, hN, hψ', hN', rfl, hd', hnc⟩
  exact ⟨v, v', dens_mem_ensDens hψ hN, hd' ▸ dens_mem_ensDens hψ' hN', hnc⟩

/-- **Weak Hohenberg–Kohn for ensembles**: if a normalized ground state `χ` of `H(v)` has the
density of a ground-state ensemble of `H(v')`, then `χ` is a ground state of `H(v')`. -/
theorem weak_hk_ens {H0 : Matrix C C ℝ} {n : V → C → ℝ} {v v' : V → ℝ} {χ : C → ℝ}
    (hχ : IsGroundState (hamN H0 n v) χ) (hNχ : χ ⬝ᵥ χ = 1) (hens : dens n χ ∈ EnsDens H0 n v') :
    IsGroundState (hamN H0 n v') χ := by
  obtain ⟨m, w, ψ, hw, hw1, hψ, hd⟩ := hens
  -- the potential energies of the ensemble are those of χ
  have hpot : ∀ u : V → ℝ, ∑ k, w k * ∑ i, u i * dens n (ψ k) i = ∑ i, u i * dens n χ i := by
    intro u
    rw [← hd]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  -- variational inequalities, state by state
  have ha : ∀ k, qf H0 χ ≤ qf H0 (ψ k) + ∑ i, v i * dens n (ψ k) i - ∑ i, v i * dens n χ i := by
    intro k
    have := hχ.2 (ψ k)
    rw [(hψ k).2, hNχ, mul_one, mul_one, qf_hamN, qf_hamN] at this
    linarith
  have hb : ∀ k, qf H0 (ψ k) + ∑ i, v' i * dens n (ψ k) i ≤ qf H0 χ + ∑ i, v' i * dens n χ i := by
    intro k
    have := (hψ k).1.2 χ
    rw [(hψ k).2, hNχ, mul_one, mul_one, qf_hamN, qf_hamN] at this
    exact this
  -- weighted sums: the inequalities hb are equalities
  have hA : qf H0 χ ≤ ∑ k, w k * qf H0 (ψ k) := by
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => mul_le_mul_of_nonneg_left (ha k) (hw k)
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hpot,
      ← Finset.sum_mul, hw1, one_mul] at this
    linarith
  have hgap : ∀ k, 0 ≤ (qf H0 χ + ∑ i, v' i * dens n χ i) -
      (qf H0 (ψ k) + ∑ i, v' i * dens n (ψ k) i) := fun k => sub_nonneg.2 (hb k)
  have hsum : ∑ k, w k * ((qf H0 χ + ∑ i, v' i * dens n χ i) -
      (qf H0 (ψ k) + ∑ i, v' i * dens n (ψ k) i)) = 0 := by
    have hle : ∑ k, w k * ((qf H0 χ + ∑ i, v' i * dens n χ i) -
        (qf H0 (ψ k) + ∑ i, v' i * dens n (ψ k) i)) ≤ 0 := by
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hpot,
        ← Finset.sum_mul, hw1, one_mul]
      linarith
    exact le_antisymm hle (Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (hgap k))
  obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, (fun _ => (0 : ℝ)) k < w k :=
    Finset.exists_lt_of_sum_lt (by simp [hw1])
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hw k) (hgap k)).1 hsum k
    (Finset.mem_univ k)
  have heq : qf (hamN H0 n v') χ = qf (hamN H0 n v') (ψ k) := by
    rw [qf_hamN, qf_hamN]
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h hk.ne'
    · linarith
  refine ⟨hχ.1, fun φ => ?_⟩
  have := (hψ k).1.2 φ
  rw [(hψ k).2, mul_one] at this
  rw [heq, hNχ, mul_one]
  exact this

/-- The uniform density is not in the ensemble version of the shared densities either. -/
lemma psiSq_zero_not_mem_sharedEnsDens : dens occ4 (psiSq 0) ∉ SharedEnsDens H0sq occ4 := by
  rintro ⟨v, v', hv, hv', hnc⟩
  have hχ : IsGroundState (hamN H0sq occ4 fun _ => (0 : ℝ)) (psiSq 0) :=
    psiSq_ground (by simp) (by simp) (by simp)
  obtain ⟨c, hc⟩ := square_const_shared 0 hχ (weak_hk_ens hχ (psiSq_norm 0) hv)
  obtain ⟨c', hc'⟩ := square_const_shared 0 hχ (weak_hk_ens hχ (psiSq_norm 0) hv')
  exact hnc ⟨c' - c, fun i => by linarith [hc i, hc' i]⟩

/-- **The non-uniquely v-representable densities of Penz and van Leeuwen (ensembles, real states)
do not form a closed set** for two fermions on the square. -/
theorem square_sharedEnsDens_not_closed : ¬ IsClosed (SharedEnsDens H0sq occ4) := by
  intro hcl
  have hlim : Filter.Tendsto (fun k : ℕ => dens occ4 (psiSq (1 / ((k : ℝ) + 1))))
      Filter.atTop (nhds (dens occ4 (psiSq 0))) :=
    (continuous_dens_psiSq.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact psiSq_zero_not_mem_sharedEnsDens (hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall
    fun k => sharedDens_subset_sharedEnsDens _ _ (psiSq_mem_sharedDens (by positivity))))

/-- The uniform density is ensemble-v-representable (at `v = 0`), is produced by no two potentials
that differ by more than a constant, and is a limit of densities that are. -/
theorem square_uv_in_closure_nonuv :
    ((∃ v, dens occ4 (psiSq 0) ∈ EnsDens H0sq occ4 v) ∧
      dens occ4 (psiSq 0) ∉ SharedEnsDens H0sq occ4) ∧
    dens occ4 (psiSq 0) ∈ closure (SharedEnsDens H0sq occ4) := by
  refine ⟨⟨⟨fun _ => 0, dens_mem_ensDens (psiSq_ground (by simp) (by simp) (by simp))
    (psiSq_norm 0)⟩, psiSq_zero_not_mem_sharedEnsDens⟩, ?_⟩
  have hlim : Filter.Tendsto (fun k : ℕ => dens occ4 (psiSq (1 / ((k : ℝ) + 1))))
      Filter.atTop (nhds (dens occ4 (psiSq 0))) :=
    (continuous_dens_psiSq.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall
    fun k => sharedDens_subset_sharedEnsDens _ _ (psiSq_mem_sharedDens (by positivity)))

/-- **The uniquely v-representable densities are not relatively open** (two fermions on the square,
real ensembles): no open `U` cuts out, from the ensemble-v-representable densities, exactly those
produced by a single potential. (Densities satisfy `Σ ρ = 2`, so openness in `ℝ⁴` would be
vacuous; openness relative to a larger density domain containing these sets fails a fortiori.)
So the conjecture of Penz and van Leeuwen (J. Chem. Phys. 155, 244111 (2021)) that the uv
densities form an open set does not hold for this example. -/
theorem square_uvDens_not_relOpen :
    ¬ ∃ U : Set (Fin 4 → ℝ), IsOpen U ∧
      U ∩ {ρ | ∃ v, ρ ∈ EnsDens H0sq occ4 v} =
        {ρ | (∃ v, ρ ∈ EnsDens H0sq occ4 v) ∧ ρ ∉ SharedEnsDens H0sq occ4} := by
  rintro ⟨U, hU, hEq⟩
  obtain ⟨⟨hrep, hnot⟩, hcl⟩ := square_uv_in_closure_nonuv
  have h0 : dens occ4 (psiSq 0) ∈ U := by
    have : dens occ4 (psiSq 0) ∈ U ∩ {ρ | ∃ v, ρ ∈ EnsDens H0sq occ4 v} := by
      rw [hEq]; exact ⟨hrep, hnot⟩
    exact this.1
  obtain ⟨ρ, hρU, hρS⟩ := mem_closure_iff.1 hcl U hU h0
  have hrepρ : ∃ v, ρ ∈ EnsDens H0sq occ4 v := by
    obtain ⟨v, v', h, -, -⟩ := hρS; exact ⟨v, h⟩
  have : ρ ∈ U ∩ {ρ | ∃ v, ρ ∈ EnsDens H0sq occ4 v} := ⟨hρU, hrepρ⟩
  rw [hEq] at this
  exact this.2 hρS

end ensDens

section complexEns

variable {C V : Type*} [Fintype C] [Fintype V]

/-- `Re ⟨ψ, M ψ⟩` for a complex vector `ψ`. -/
noncomputable def qfC (M : Matrix C C ℂ) (ψ : C → ℂ) : ℝ := (star ψ ⬝ᵥ (M *ᵥ ψ)).re

/-- `‖ψ‖²` for a complex vector `ψ`. -/
noncomputable def normSqC (ψ : C → ℂ) : ℝ := ∑ c, Complex.normSq (ψ c)

/-- `ψ` is a ground state of the complex matrix `M`: `ψ ≠ 0` minimises the Rayleigh quotient over
all complex vectors (written without division). Meant for Hermitian `M`; here it is used only for
real symmetric matrices viewed as complex ones. -/
def IsGroundStateC (M : Matrix C C ℂ) (ψ : C → ℂ) : Prop :=
  ψ ≠ 0 ∧ ∀ φ : C → ℂ, qfC M ψ * normSqC φ ≤ qfC M φ * normSqC ψ

/-- Density of a complex state: `ρ_ψ(i) = Σ_c n_i(c) |ψ(c)|²`. -/
noncomputable def densC (n : V → C → ℝ) (ψ : C → ℂ) : V → ℝ :=
  fun i => ∑ c, n i c * Complex.normSq (ψ c)

/-- For a real matrix, `Re ⟨ψ, M ψ⟩` splits into the real and imaginary parts of `ψ`. -/
lemma qfC_map_ofReal (M : Matrix C C ℝ) (ψ : C → ℂ) :
    qfC (M.map ((↑) : ℝ → ℂ)) ψ = qf M (fun c => (ψ c).re) + qf M (fun c => (ψ c).im) := by
  simp only [qfC, qf, dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.map_apply,
    Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma normSqC_eq (ψ : C → ℂ) :
    normSqC ψ = (fun c => (ψ c).re) ⬝ᵥ (fun c => (ψ c).re) +
      (fun c => (ψ c).im) ⬝ᵥ (fun c => (ψ c).im) := by
  simp only [normSqC, dotProduct, Complex.normSq_apply, ← Finset.sum_add_distrib]

omit [Fintype V] in
lemma densC_eq (n : V → C → ℝ) (ψ : C → ℂ) :
    densC n ψ = dens n (fun c => (ψ c).re) + dens n (fun c => (ψ c).im) := by
  funext i
  simp only [densC, dens, Pi.add_apply, Complex.normSq_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma qfC_ofReal (M : Matrix C C ℝ) (x : C → ℝ) :
    qfC (M.map ((↑) : ℝ → ℂ)) (fun c => (x c : ℂ)) = qf M x := by
  rw [qfC_map_ofReal]; simp [qf]

lemma normSqC_ofReal (x : C → ℝ) : normSqC (fun c => (x c : ℂ)) = x ⬝ᵥ x := by
  rw [normSqC_eq]; simp

omit [Fintype V] in
lemma densC_ofReal (n : V → C → ℝ) (x : C → ℝ) : densC n (fun c => (x c : ℂ)) = dens n x := by
  rw [densC_eq]; funext i; simp [dens]

lemma dotProduct_self_pos {x : C → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun c _ => mul_self_nonneg (x c))
    (fun h => hx (dotProduct_self_eq_zero.1 h.symm))

/-- A real ground state is a ground state over complex vectors too. -/
lemma isGroundStateC_ofReal {M : Matrix C C ℝ} {x : C → ℝ} (h : IsGroundState M x) :
    IsGroundStateC (M.map ((↑) : ℝ → ℂ)) (fun c => (x c : ℂ)) := by
  refine ⟨fun h0 => h.1 (funext fun c => by simpa using congrFun h0 c), fun φ => ?_⟩
  rw [qfC_ofReal, normSqC_ofReal, qfC_map_ofReal, normSqC_eq]
  have ha := h.2 (fun c => (φ c).re)
  have hb := h.2 (fun c => (φ c).im)
  linarith

/-- The real and imaginary parts of a complex ground state of a real matrix, when nonzero, are
real ground states. -/
lemma isGroundState_of_C {M : Matrix C C ℝ} {ψ : C → ℂ}
    (h : IsGroundStateC (M.map ((↑) : ℝ → ℂ)) ψ) {x : C → ℝ}
    (hx : x = (fun c => (ψ c).re) ∨ x = (fun c => (ψ c).im)) (hne : x ≠ 0) :
    IsGroundState M x := by
  set a : C → ℝ := fun c => (ψ c).re with ha_def
  set b : C → ℝ := fun c => (ψ c).im with hb_def
  have hQ : qfC (M.map ((↑) : ℝ → ℂ)) ψ = qf M a + qf M b := qfC_map_ofReal M ψ
  have hN : normSqC ψ = a ⬝ᵥ a + b ⬝ᵥ b := normSqC_eq ψ
  -- minimality against real test vectors
  have hreal : ∀ y : C → ℝ, (qf M a + qf M b) * (y ⬝ᵥ y) ≤ qf M y * (a ⬝ᵥ a + b ⬝ᵥ b) := by
    intro y
    have := h.2 (fun c => (y c : ℂ))
    rwa [qfC_ofReal, normSqC_ofReal, hQ, hN] at this
  have hA := hreal a
  have hB := hreal b
  have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hne
  have haa : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun c _ => mul_self_nonneg (a c)
  have hbb : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun c _ => mul_self_nonneg (b c)
  -- the two inequalities sum to an equality, so each is one
  have hEx : (qf M a + qf M b) * (x ⬝ᵥ x) = qf M x * (a ⬝ᵥ a + b ⬝ᵥ b) := by
    rcases hx with rfl | rfl <;> nlinarith
  have hNpos : 0 < a ⬝ᵥ a + b ⬝ᵥ b := by
    rcases hx with rfl | rfl <;> linarith
  refine ⟨hne, fun φ => ?_⟩
  have hφ := hreal φ
  have key : qf M x * (φ ⬝ᵥ φ) * (a ⬝ᵥ a + b ⬝ᵥ b) ≤
      qf M φ * (x ⬝ᵥ x) * (a ⬝ᵥ a + b ⬝ᵥ b) := by
    have := mul_le_mul_of_nonneg_left hφ hxx.le
    calc qf M x * (φ ⬝ᵥ φ) * (a ⬝ᵥ a + b ⬝ᵥ b)
        = (qf M a + qf M b) * (x ⬝ᵥ x) * (φ ⬝ᵥ φ) := by rw [hEx]; ring
      _ = x ⬝ᵥ x * ((qf M a + qf M b) * (φ ⬝ᵥ φ)) := by ring
      _ ≤ x ⬝ᵥ x * (qf M φ * (a ⬝ᵥ a + b ⬝ᵥ b)) := this
      _ = qf M φ * (x ⬝ᵥ x) * (a ⬝ᵥ a + b ⬝ᵥ b) := by ring
  exact le_of_mul_le_mul_right key hNpos

omit [Fintype V] in
lemma dens_smul (n : V → C → ℝ) (s : ℝ) (x : C → ℝ) : dens n (s • x) = s ^ 2 • dens n x := by
  funext i
  simp only [dens, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

omit [Fintype V] in
/-- A nonzero real ground state, normalized. -/
lemma exists_normalized {M : Matrix C C ℝ} (n : V → C → ℝ) {z : C → ℝ} (hz : IsGroundState M z) :
    ∃ x, IsGroundState M x ∧ x ⬝ᵥ x = 1 ∧ (z ⬝ᵥ z) • dens n x = dens n z := by
  have hpos := dotProduct_self_pos hz.1
  have hs : Real.sqrt (z ⬝ᵥ z) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hsq := Real.sq_sqrt hpos.le
  refine ⟨(1 / Real.sqrt (z ⬝ᵥ z)) • z, isGroundState_smul hz (by positivity), ?_, ?_⟩
  · simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
    linarith
  · rw [dens_smul, smul_smul]
    have : z ⬝ᵥ z * (1 / Real.sqrt (z ⬝ᵥ z)) ^ 2 = 1 := by
      rw [div_pow, hsq]; field_simp
    rw [this, one_smul]

omit [Fintype V] in
/-- **A complex ground state of a real Hamiltonian has the density of a real ensemble**: with
`ψ = a + i b`, the parts `a`, `b` are real ground states (when nonzero) and
`|ψ|² = a² + b²`, so `ρ_ψ = ‖a‖² ρ_(a/‖a‖) + ‖b‖² ρ_(b/‖b‖)`. -/
lemma densC_eq_two_real {M : Matrix C C ℝ} (n : V → C → ℝ) {ψ : C → ℂ}
    (h : IsGroundStateC (M.map ((↑) : ℝ → ℂ)) ψ) (hN : normSqC ψ = 1) :
    ∃ (x y : C → ℝ) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ IsGroundState M x ∧ x ⬝ᵥ x = 1 ∧
      IsGroundState M y ∧ y ⬝ᵥ y = 1 ∧ densC n ψ = t • dens n x + (1 - t) • dens n y := by
  set a : C → ℝ := fun c => (ψ c).re with ha_def
  set b : C → ℝ := fun c => (ψ c).im with hb_def
  have hN' : a ⬝ᵥ a + b ⬝ᵥ b = 1 := by rw [← normSqC_eq, hN]
  have haa : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun c _ => mul_self_nonneg (a c)
  have hbb : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun c _ => mul_self_nonneg (b c)
  -- some normalized real ground state exists (from whichever part is nonzero)
  obtain ⟨g, hg, hgN⟩ : ∃ g, IsGroundState M g ∧ g ⬝ᵥ g = 1 := by
    by_cases ha0 : a = 0
    · have hb0 : b ≠ 0 := by
        rintro hb0; rw [ha0, hb0] at hN'; simp at hN'
      obtain ⟨x, hx, hxN, -⟩ := exists_normalized n (isGroundState_of_C h (Or.inr rfl) hb0)
      exact ⟨x, hx, hxN⟩
    · obtain ⟨x, hx, hxN, -⟩ := exists_normalized n (isGroundState_of_C h (Or.inl rfl) ha0)
      exact ⟨x, hx, hxN⟩
  have part : ∀ z : C → ℝ, (z = a ∨ z = b) →
      ∃ x, IsGroundState M x ∧ x ⬝ᵥ x = 1 ∧ (z ⬝ᵥ z) • dens n x = dens n z := by
    intro z hz
    by_cases hz0 : z = 0
    · refine ⟨g, hg, hgN, ?_⟩
      subst hz0; funext i; simp [dens]
    · exact exists_normalized n (isGroundState_of_C h hz hz0)
  obtain ⟨x, hx, hxN, hxd⟩ := part a (Or.inl rfl)
  obtain ⟨y, hy, hyN, hyd⟩ := part b (Or.inr rfl)
  refine ⟨x, y, a ⬝ᵥ a, haa, by linarith, hx, hxN, hy, hyN, ?_⟩
  rw [densC_eq, show 1 - a ⬝ᵥ a = b ⬝ᵥ b by linarith, hxd, hyd]

variable [DecidableEq C]

/-- Densities of ground-state ensembles of `H(v)` with complex states: convex combinations of the
densities of finitely many normalized complex ground states of `H(v)`, viewed as a complex matrix.
(A ground-state density matrix is such a combination, by its spectral decomposition; Penz and van
Leeuwen 2023, Eq. (2).) -/
def EnsDensC (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : Set (V → ℝ) :=
  {ρ | ∃ (m : ℕ) (w : Fin m → ℝ) (ψ : Fin m → C → ℂ), (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      (∀ k, IsGroundStateC ((hamN H0 n v).map ((↑) : ℝ → ℂ)) (ψ k) ∧ normSqC (ψ k) = 1) ∧
      ∑ k, w k • densC n (ψ k) = ρ}

/-- Densities of complex ground-state ensembles of two potentials that differ by more than a
constant: the non-uniquely v-representable densities of Penz and van Leeuwen, in their setting
(complex Hilbert space, real `H0`, ensembles). -/
def SharedEnsDensC (H0 : Matrix C C ℝ) (n : V → C → ℝ) : Set (V → ℝ) :=
  {ρ | ∃ v v' : V → ℝ, ρ ∈ EnsDensC H0 n v ∧ ρ ∈ EnsDensC H0 n v' ∧ ¬ ∃ k, ∀ i, v i - v' i = k}

/-- **Complex states give no new ensemble densities** for a real Hamiltonian. -/
theorem ensDensC_eq_ensDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) :
    EnsDensC H0 n v = EnsDens H0 n v := by
  ext ρ
  constructor
  · rintro ⟨m, w, ψ, hw, hw1, hψ, rfl⟩
    choose x y t ht0 ht1 hx hxN hy hyN hd using fun k => densC_eq_two_real n (hψ k).1 (hψ k).2
    refine ⟨m + m, Fin.append (fun k => w k * t k) (fun k => w k * (1 - t k)), Fin.append x y,
      ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · rw [Fin.append_left]; exact mul_nonneg (hw k) (ht0 k)
      · rw [Fin.append_right]; exact mul_nonneg (hw k) (sub_nonneg.2 (ht1 k))
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, ← Finset.sum_add_distrib]
      have hsplit : ∀ k, w k * t k + w k * (1 - t k) = w k := fun k => by ring
      simp only [hsplit, hw1]
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · rw [Fin.append_left]; exact ⟨hx k, hxN k⟩
      · rw [Fin.append_right]; exact ⟨hy k, hyN k⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hd k, smul_add, smul_smul, smul_smul, mul_smul, mul_smul]
  · rintro ⟨m, w, ψ, hw, hw1, hψ, rfl⟩
    refine ⟨m, w, fun k c => (ψ k c : ℂ), hw, hw1,
      fun k => ⟨isGroundStateC_ofReal (hψ k).1, by rw [normSqC_ofReal]; exact (hψ k).2⟩, ?_⟩
    simp only [densC_ofReal]

theorem sharedEnsDensC_eq_sharedEnsDens (H0 : Matrix C C ℝ) (n : V → C → ℝ) :
    SharedEnsDensC H0 n = SharedEnsDens H0 n := by
  simp only [SharedEnsDensC, SharedEnsDens, ensDensC_eq_ensDens]

end complexEns

/-- **The closedness statement of Corollary 10 of Penz and van Leeuwen (Phys. Rev. A 108, 032810
(2023)) does not hold, in their setting** (complex states, ensembles): the non-uniquely
v-representable densities of two fermions on the square do not form a closed set. (Closedness is
taken in `ℝ⁴`; since the density domain `P_{4,2}` is closed in `ℝ⁴` and contains the set, this is
the same as closedness in `P_{4,2}`.) This theorem does not concern the measure-zero statement of
that corollary. -/
theorem square_sharedEnsDensC_not_closed : ¬ IsClosed (SharedEnsDensC H0sq occ4) := by
  rw [sharedEnsDensC_eq_sharedEnsDens]
  exact square_sharedEnsDens_not_closed

/-- `square_uvDens_not_relOpen` with complex states. -/
theorem square_uvDensC_not_relOpen :
    ¬ ∃ U : Set (Fin 4 → ℝ), IsOpen U ∧
      U ∩ {ρ | ∃ v, ρ ∈ EnsDensC H0sq occ4 v} =
        {ρ | (∃ v, ρ ∈ EnsDensC H0sq occ4 v) ∧ ρ ∉ SharedEnsDensC H0sq occ4} := by
  simp only [ensDensC_eq_ensDens, sharedEnsDensC_eq_sharedEnsDens]
  exact square_uvDens_not_relOpen

end DFT
