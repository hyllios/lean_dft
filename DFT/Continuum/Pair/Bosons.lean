/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Pair.Strong
import DFT.Continuum.Pair.MaxPrinciple
import DFT.Continuum.General.Lieb

/-!
# Two interacting bosons in a box

For two bosons on `[0, 1]` with a continuous symmetric interaction, unique continuation is reduced
to the sign of the ground state:

* `strong_eq` (`Continuum/Pair/Strong`): ground states solve `-ΔΦ + (w + v(x₁) + v(x₂) - E) Φ = 0`
  classically;
* `strong_max_principle` (`Continuum/Pair/MaxPrinciple`): Hopf's strong maximum principle on the
  square;
* `pos_of_nonneg_gs`: a nonnegative ground state is positive on the square;
* `ucp_bosons`: a ground state that does not change sign has no zeros in the square;
* `hk_bosons`: **Hohenberg–Kohn for two interacting bosons**, assuming only that the ground state
  does not change sign (the Perron–Frobenius property, whose proof needs `H¹` functions).
-/
namespace DFT.Continuum.Pair

open MeasureTheory Set Box

/-- The negative of a ground state is a ground state. -/
lemma isGS_neg {X : Type*} [MeasurableSpace X] {μ : Measure X} {P : Type*} [AddCommGroup P]
    [Module ℝ P] {S : Setting μ P} {v : P} {ψ : X → ℝ} (h : IsGS S v ψ) : IsGS S v (-ψ) := by
  have hn : -ψ = (-1 : ℝ) • ψ := by simp
  obtain ⟨hD, hpos, hmin⟩ := h
  refine ⟨S.D.neg_mem hD, ?_, fun φ hφ => ?_⟩
  · rw [hn, ip_smul_self]; linarith
  · rw [hn, ip_smul_self, Q_smul_self v _ hD]
    have := hmin φ hφ
    linarith

/-- A nonnegative ground state of interacting bosons is positive on the square. -/
lemma pos_of_nonneg_gs {w : ℝ × ℝ → ℝ} {hw : Continuous w} (hws : ∀ p, w p.swap = w p)
    {v : Pot} {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ) (hnn : ∀ p ∈ Sq, 0 ≤ Φ p) :
    ∀ p ∈ Sq, 0 < Φ p := by
  set E := Q (setting2 1 w hw) v Φ / ip (μ := μ2) Φ Φ
  set V : ℝ × ℝ → ℝ := fun p => w p + L2 v p - E
  have hV : Continuous V := (hw.add (continuous_L2 v)).sub continuous_const
  have heq := strong_eq hws hΦ
  intro p0 hp0
  rcases (hnn p0 hp0).lt_or_eq with h | h
  · exact h
  exfalso
  have hzero := strong_max_principle (u := Φ) (c := fun p => max (V p) 0) hΦ.1.1
    (hV.max continuous_const) (fun p => le_max_right _ _)
    (fun p hp => by
      have e := heq p hp
      have h1 : 0 ≤ (max (V p) 0 - V p) * Φ p :=
        mul_nonneg (by linarith [le_max_left (V p) 0]) (hnn p hp)
      simp only [V] at e h1 ⊢
      nlinarith)
    hnn hp0 h.symm
  have hpos := hΦ.2.1
  have : ip (μ := μ2) Φ Φ = 0 := by
    simp only [ip]
    rw [setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      (g := fun _ => (0 : ℝ)) (fun p hp => by simp [hzero p hp])]
    simp
  linarith

/-- **Unique continuation for interacting bosons, given the sign.** A ground state that does not
change sign on the square has no zeros there. -/
theorem ucp_bosons {w : ℝ × ℝ → ℝ} {hw : Continuous w} (hws : ∀ p, w p.swap = w p) {v : Pot}
    {Φ : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ)
    (hsign : (∀ p ∈ Sq, 0 ≤ Φ p) ∨ ∀ p ∈ Sq, Φ p ≤ 0) : ∀ᵐ p ∂μ2, Φ p ≠ 0 := by
  have hall : ∀ p ∈ Sq, Φ p ≠ 0 := by
    rcases hsign with h | h
    · exact fun p hp => (pos_of_nonneg_gs hws hΦ h p hp).ne'
    · intro p hp
      have := pos_of_nonneg_gs hws (isGS_neg hΦ) (fun q hq => by simp [h q hq]) p hp
      simp only [Pi.neg_apply, neg_pos] at this
      exact this.ne
  exact (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 (ae_of_all _ hall)

/-- **Hohenberg–Kohn for two interacting bosons in a box, given the sign of the ground state.** -/
theorem hk_bosons {w : ℝ × ℝ → ℝ} {hw : Continuous w} (hws : ∀ p, w p.swap = w p)
    {v v' : Pot} {Φ Φ' : ℝ × ℝ → ℝ} (hΦ : IsGS (setting2 1 w hw) v Φ)
    (hΦ' : IsGS (setting2 1 w hw) v' Φ')
    (hρ : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, Φ (x, y) ^ 2 =
      ∫ y in Ioo (0 : ℝ) 1, Φ' (x, y) ^ 2)
    (hsign : (∀ p ∈ Sq, 0 ≤ Φ p) ∨ ∀ p ∈ Sq, Φ p ≤ 0) : ∃ k : ℝ, v - v' = k • one :=
  hk_pair_of_ucp (by norm_num) hΦ hΦ' hρ (ucp_bosons hws hΦ hsign)

end DFT.Continuum.Pair
