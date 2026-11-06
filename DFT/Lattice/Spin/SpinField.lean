/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Spin.SpinResolved
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Spin-DFT language: scalar potential and magnetic field

Write the spin-dependent potential as a scalar potential `v` and a (collinear) magnetic field `B`,
`v↑ = v - B`, `v↓ = v + B` (Zeeman coupling `-B (n↑ - n↓)`, units with `μ_B = 1`). A pair `(v, B)`
is stored as `x : Fin M ⊕ Fin M → ℝ` with `x (inl i) = v i` and `x (inr i) = B i`; `zeeman x` is the
corresponding spin-dependent potential.

* `isGroundState_add_const`: a potential change that is constant on every configuration does not
  change the ground states.
* `groundState_field_shift`: in particular, adding a uniform constant to `v` and a uniform constant
  to `B` does not change the ground states. A uniform magnetic field is therefore never determined
  by the ground state (the non-uniqueness of spin-DFT; Capelle–Vignale, Eschrig–Pickett).
* `generic_hk_spin_field`: for almost every `(v, B)` this is the only non-uniqueness: a shared
  ground state forces `v - v'` and `B - B'` to be constant.
-/

namespace DFT

open Matrix MeasureTheory

section

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- A potential change `w` that is constant (`κ`) on every configuration does not change the ground
states. -/
theorem isGroundState_add_const (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v w : V → ℝ) {κ : ℝ}
    (hw : ∀ c, ∑ i, w i * n i c = κ) (ψ : C → ℝ) :
    IsGroundState (hamN H0 n (v + w)) ψ ↔ IsGroundState (hamN H0 n v) ψ := by
  have hq : ∀ φ : C → ℝ, qf (hamN H0 n (v + w)) φ = qf (hamN H0 n v) φ + κ * (φ ⬝ᵥ φ) := by
    intro φ
    rw [qf_hamN, qf_hamN]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [dens_weighted n w φ]
    simp only [hw, ← Finset.mul_sum, dotProduct, ← sq]
    ring
  unfold IsGroundState
  simp only [hq]
  constructor
  · rintro ⟨h0, h⟩; exact ⟨h0, fun φ => by have := h φ; nlinarith⟩
  · rintro ⟨h0, h⟩; exact ⟨h0, fun φ => by have := h φ; nlinarith⟩

end

variable {M Nu Nd : ℕ}

lemma sum_occF' {N : ℕ} (s : Conf M N) : ∑ i, occF i s = (N : ℝ) := by
  simp [occF, Finset.sum_ite_mem, s.2]

/-- Separate constants on the two spins are constant on every configuration. -/
lemma sum_spinConst {w : Fin M ⊕ Fin M → ℝ} (hw : w ∈ spinConst) :
    ∃ κ, ∀ x : Conf M Nu × Conf M Nd, ∑ i, w i * occS i x = κ := by
  obtain ⟨a, b, hab⟩ := hw
  refine ⟨a * Nu + b * Nd, fun x => ?_⟩
  rw [sum_occS]
  simp only [wC, (hab _).1, (hab _).2, ← Finset.mul_sum, sum_occF']

/-- The spin-dependent potential of a scalar potential and a magnetic field:
`v↑ = v - B`, `v↓ = v + B`. -/
def zeeman (x : Fin M ⊕ Fin M → ℝ) : Fin M ⊕ Fin M → ℝ :=
  Sum.elim (fun i => x (Sum.inl i) - x (Sum.inr i)) (fun i => x (Sum.inl i) + x (Sum.inr i))

/-- `zeeman` as a linear equivalence (inverse: `v = (v↑ + v↓)/2`, `B = (v↓ - v↑)/2`). -/
noncomputable def zeemanEquiv : (Fin M ⊕ Fin M → ℝ) ≃ₗ[ℝ] (Fin M ⊕ Fin M → ℝ) where
  toFun := zeeman
  invFun y := Sum.elim (fun i => (y (Sum.inl i) + y (Sum.inr i)) / 2)
    (fun i => (y (Sum.inr i) - y (Sum.inl i)) / 2)
  map_add' x y := by
    funext σi; cases σi <;> simp only [zeeman, Pi.add_apply,
      Sum.elim_inl, Sum.elim_inr] <;> ring
  map_smul' c x := by
    funext σi; cases σi <;> simp only [zeeman, Pi.smul_apply, smul_eq_mul,
      Sum.elim_inl, Sum.elim_inr, RingHom.id_apply] <;> ring
  left_inv x := by
    funext σi; cases σi <;> simp only [zeeman,
      Sum.elim_inl, Sum.elim_inr] <;> ring
  right_inv y := by
    funext σi; cases σi <;> simp only [zeeman,
      Sum.elim_inl, Sum.elim_inr] <;> ring

/-- **A uniform magnetic field is not determined by the ground state.** Adding constants to the
scalar potential and to the magnetic field leaves every ground state a ground state. -/
theorem groundState_field_shift (H0 : Matrix (Conf M Nu × Conf M Nd) (Conf M Nu × Conf M Nd) ℝ)
    (x : Fin M ⊕ Fin M → ℝ) (a b : ℝ) (ψ : Conf M Nu × Conf M Nd → ℝ) :
    IsGroundState (hamN H0 occS (zeeman (x + Sum.elim (fun _ => a) (fun _ => b)))) ψ ↔
      IsGroundState (hamN H0 occS (zeeman x)) ψ := by
  have hz : zeeman (x + Sum.elim (fun _ => a) (fun _ => b)) =
      zeeman x + Sum.elim (fun _ => a - b) (fun _ => a + b) := by
    funext σi; cases σi <;> simp [zeeman] <;> ring
  obtain ⟨κ, hκ⟩ := sum_spinConst (Nu := Nu) (Nd := Nd)
    (w := Sum.elim (fun _ => a - b) (fun _ => a + b)) ⟨a - b, a + b, fun i => ⟨rfl, rfl⟩⟩
  rw [hz]
  exact isGroundState_add_const H0 occS _ _ hκ ψ

/-- Non-uniqueness in spin-DFT language: some ground state at `(v, B)` is also a ground state at a
`(v', B')` with `v - v'` or `B - B'` not constant. -/
def NonUVField (H0 : Matrix (Conf M Nu × Conf M Nd) (Conf M Nu × Conf M Nd) ℝ)
    (x : Fin M ⊕ Fin M → ℝ) : Prop :=
  ∃ (ψ : Conf M Nu × Conf M Nd → ℝ) (x' : Fin M ⊕ Fin M → ℝ),
    IsGroundState (hamN H0 occS (zeeman x)) ψ ∧ IsGroundState (hamN H0 occS (zeeman x')) ψ ∧
      ¬ ∃ a b : ℝ, ∀ i, x (Sum.inl i) - x' (Sum.inl i) = a ∧ x (Sum.inr i) - x' (Sum.inr i) = b

lemma nonUVField_imp (H0 : Matrix (Conf M Nu × Conf M Nd) (Conf M Nu × Conf M Nd) ℝ)
    {x : Fin M ⊕ Fin M → ℝ} (h : NonUVField H0 x) : NonUVMod spinConst H0 occS (zeeman x) := by
  obtain ⟨ψ, x', h1, h2, hne⟩ := h
  refine ⟨ψ, zeeman x', h1, h2, fun ⟨a, b, hab⟩ => hne ⟨(a + b) / 2, (b - a) / 2, fun i => ?_⟩⟩
  have e1 := (hab i).1
  have e2 := (hab i).2
  simp only [zeeman, Sum.elim_inl, Sum.elim_inr] at e1 e2
  constructor <;> linarith

/-- **Generic Hohenberg–Kohn theorem in spin-DFT language.** For almost every scalar potential and
magnetic field `(v, B)`, a ground state shared with `(v', B')` forces `v - v'` and `B - B'` to be
constant; and constant shifts are always possible (`groundState_field_shift`). The exceptional
`(v, B)` lie in a closed, nowhere dense, Lebesgue-null set. -/
theorem generic_hk_spin_field {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hNu0 : 0 < Nu) (hNuM : Nu < M) (hNd0 : 0 < Nd)
    (hNdM : Nd < M) (Vint : Conf M Nu × Conf M Nd → ℝ) :
    ∃ Z : Set (Fin M ⊕ Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      {x | NonUVField (H0S G t Vint) x} ⊆ Z := by
  obtain ⟨Z0, hcl, hint, hvol, hsub⟩ :=
    generic_hk_spin hG htsym hts hNu0 hNuM hNd0 hNdM Vint
  set e : (Fin M ⊕ Fin M → ℝ) ≃L[ℝ] (Fin M ⊕ Fin M → ℝ) :=
    (zeemanEquiv (M := M)).toContinuousLinearEquiv
  refine ⟨e ⁻¹' Z0, hcl.preimage e.continuous, ?_, ?_, fun x hx => hsub (nonUVField_imp _ hx)⟩
  · have := e.toHomeomorph.preimage_interior Z0
    rw [hint, Set.preimage_empty] at this
    exact this.symm
  · rw [Measure.addHaar_preimage_continuousLinearEquiv, hvol, mul_zero]

end DFT
