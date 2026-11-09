/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Nodal
import DFT.Continuum.Line.Hopf

/-!
# `N` interacting fermions on a line: the nodal set is the collision set

For `n + 1` fermions on `[0, 1]` with a continuous interaction invariant under relabelling, the
ground state vanishes in the open cube exactly where two particles meet. That set is null, so
unique continuation holds and Hohenberg–Kohn needs no further assumption.

* `Ch`: the ordered chamber `{0 < x₀ < x₁ < ⋯ < xₙ < 1}`, open and convex.
* `gs_pos_or_nonpos_ch`: on the chamber a ground state is positive everywhere or nonpositive
  everywhere (Hopf's lemma, with the critical zeros of `Nodal`).
* `gs_ne_zero_line`: a ground state has no zeros in the cube away from collisions.
* `ucp_line`: unique continuation, `Φ ≠ 0` almost everywhere.
* `hk_interacting_fermions_line`: **Hohenberg–Kohn for `N` interacting fermions on a line**.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ} {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

/-- The ordered chamber `{0 < x₀ < x₁ < ⋯ < xₙ < 1}`. -/
def Ch (n : ℕ) : Set (Cfg n) := Cube n ∩ {x | ∀ j : Fin n, x j.castSucc < x j.succ}

lemma mem_Ch {x : Cfg n} : x ∈ Ch n ↔ x ∈ Cube n ∧ StrictMono x := by
  simp [Ch, Fin.strictMono_iff_lt_succ]

lemma isOpen_Ch : IsOpen (Ch n) := by
  refine isOpen_cube.inter ?_
  have : {x : Cfg n | ∀ j : Fin n, x j.castSucc < x j.succ} =
      ⋂ j : Fin n, {x | x j.castSucc < x j.succ} := by ext; simp
  rw [this]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply _) (continuous_apply _)

lemma convex_Ch : Convex ℝ (Ch n) := by
  refine (convex_pi fun _ _ => convex_Ioo 0 1).inter ?_
  intro x hx y hy s t hs ht hst j
  simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  rcases hs.lt_or_eq with hs' | hs'
  · nlinarith [mul_lt_mul_of_pos_left (hx j) hs', mul_le_mul_of_nonneg_left (hy j).le ht]
  · subst hs'; simp only [zero_add] at hst; subst hst; simpa using hy j

/-- On the ordered chamber a fermionic ground state is positive everywhere or nonpositive
everywhere. -/
lemma gs_pos_or_nonpos_ch (hws : ∀ σ x, w (pm σ x) = w x) {Φ : Cfg n → ℝ}
    (hΦ : IsGS (settingF n w hw) v Φ) :
    (∀ x ∈ Ch n, 0 < Φ x) ∨ ∀ x ∈ Ch n, Φ x ≤ 0 := by
  set E := Q (settingF n w hw) v Φ / ip (μ := μN n) Φ Φ
  set V : Cfg n → ℝ := fun x => w x + LN n v x - E
  have hV : Continuous V := (hw.add (continuous_LN v)).sub continuous_const
  have heq := strong_eq_line hws hΦ
  refine pos_or_nonpos_on isOpen_Ch convex_Ch.isPreconnected (c := fun x => max (V x) 0)
    hΦ.1.1 (hV.max continuous_const) (fun x => le_max_right _ _) (fun x hx hpos => ?_)
    (fun x hx h0 => grad_zero_at_zero_line hΦ x (mem_Ch.1 hx).1 (mem_Ch.1 hx).2.injective h0)
  have e := heq x hx.1
  have h1 : 0 ≤ (max (V x) 0 - V x) * Φ x :=
    mul_nonneg (by linarith [le_max_left (V x) 0]) hpos.le
  simp only [V] at e h1 ⊢
  nlinarith

/-- **A fermionic ground state has no zeros away from collisions.** -/
theorem gs_ne_zero_line (hws : ∀ σ x, w (pm σ x) = w x) {Φ : Cfg n → ℝ}
    (hΦ : IsGS (settingF n w hw) v Φ) :
    ∀ x ∈ Cube n, Function.Injective x → Φ x ≠ 0 := by
  have hD : Φ ∈ DomF n := hΦ.1
  have hsgn : ∀ σ : Equiv.Perm (Fin (n + 1)), sgn σ ≠ 0 := fun σ h => by
    have := sgn_mul_self σ; rw [h, mul_zero] at this; exact zero_ne_one this
  -- no zeros on the chamber
  have hch : ∀ x ∈ Ch n, Φ x ≠ 0 := by
    intro x0 hx0 h0
    rcases gs_pos_or_nonpos_ch hws hΦ with h | h
    · exact (h x0 hx0).ne' h0
    rcases gs_pos_or_nonpos_ch hws (isGS_neg_line hΦ) with h' | h'
    · exact (h' x0 hx0).ne' (by simp [h0])
    -- otherwise `Φ = 0` on the chamber, hence on the cube
    have hz : ∀ x ∈ Ch n, Φ x = 0 := fun x hx =>
      le_antisymm (h x hx) (by have := h' x hx; simp only [Pi.neg_apply] at this; linarith)
    have hzS : ∀ x ∈ Cube n, Φ x = 0 := by
      intro x hx
      by_cases hinj : Function.Injective x
      · obtain ⟨σ, hσ⟩ := exists_strictMono hinj
        have := hz (pm σ x) (mem_Ch.2 ⟨pm_mem_cube.2 hx, hσ⟩)
        rw [anti hD σ x] at this
        exact (mul_eq_zero.1 this).resolve_left (hsgn σ)
      · simp only [Function.Injective, not_forall] at hinj
        obtain ⟨i, j, hij, hne⟩ := hinj
        exact eq_zero_of_collision hD hne hij
    have hip : ip (μ := μN n) Φ Φ = 0 := by
      unfold ip
      refine integral_eq_zero_of_ae ?_
      refine (ae_restrict_iff' measurableSet_cube).2 (ae_of_all _ fun x hx => ?_)
      simp [hzS x hx]
    exact absurd hΦ.2.1 (by rw [hip]; exact lt_irrefl 0)
  intro x hx hinj h0
  obtain ⟨σ, hσ⟩ := exists_strictMono hinj
  exact hch (pm σ x) (mem_Ch.2 ⟨pm_mem_cube.2 hx, hσ⟩) (by rw [anti hD σ x, h0, mul_zero])

/-- The collision set is null. -/
lemma mu_collision : μN n (NearS 0) = 0 := by
  rw [NearS_eq]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · refine le_antisymm ?_ (zero_le)
    refine (measure_mono (s := {x : Cfg n | i ≠ j ∧ |x i - x j| ≤ 0})
      (t := {x : Cfg n | |x i - x j| ≤ 0}) fun x hx => hx.2).trans ?_
    simpa using mu_strip_le (n := n) le_rfl hij

/-- **Unique continuation for `N` fermions**: the ground state vanishes only on the collision
set, a null set. -/
theorem ucp_line (hws : ∀ σ x, w (pm σ x) = w x) {Φ : Cfg n → ℝ}
    (hΦ : IsGS (settingF n w hw) v Φ) : ∀ᵐ x ∂μN n, Φ x ≠ 0 := by
  have hcube : ∀ᵐ x ∂μN n, x ∈ Cube n := ae_restrict_mem measurableSet_cube
  have hnear : ∀ᵐ x ∂μN n, x ∉ NearS (n := n) 0 := measure_eq_zero_iff_ae_notMem.1 mu_collision
  filter_upwards [hcube, hnear] with x hx hxn
  refine gs_ne_zero_line hws hΦ x hx fun i j hij => ?_
  by_contra hne
  exact hxn fun hfar => by
    have := hfar i j hne
    rw [hij, sub_self, abs_zero] at this
    exact lt_irrefl 0 this

/-- **Hohenberg–Kohn for `N` interacting fermions on a line.** For `n + 1` fermions on `[0, 1]`
with any continuous interaction invariant under relabelling, if ground states of continuous
potentials `v` and `v'` have the same one-body density, then `v - v'` is constant. No
unique-continuation hypothesis is needed. -/
theorem hk_interacting_fermions_line (hws : ∀ σ x, w (pm σ x) = w x) {v' : Pot}
    {Φ Φ' : Cfg n → ℝ} (hΦ : IsGS (settingF n w hw) v Φ) (hΦ' : IsGS (settingF n w hw) v' Φ')
    (hρ : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
      ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) : ∃ k : ℝ, v - v' = k • one :=
  hk_line_of_ucp hΦ hΦ' hρ (ucp_line hws hΦ)

end DFT.Continuum.Line
