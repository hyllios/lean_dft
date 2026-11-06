/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.GenericHK
import DFT.Lattice.Spin.KronSum

/-!
# The spin-resolved generic Hohenberg–Kohn theorem

`Nu` spin-up and `Nd` spin-down electrons on a lattice with `M` sites. A configuration is a pair
`(x↑, x↓)`; the hopping conserves spin (Kronecker sum of the two spinless hopping operators); the
interaction is any diagonal function of the configuration, e.g. the Hubbard interaction. The
potential is spin dependent, `v : Fin M ⊕ Fin M → ℝ` with `v (inl i) = v↑ i` and `v (inr i) = v↓ i`,
as in collinear spin-DFT.

Shifting `v↑` and `v↓` by separate constants changes no ground state (both particle numbers are
fixed). `generic_hk_spin`: for almost every potential this is the only non-uniqueness.
-/

namespace DFT

open Matrix MvPolynomial

variable {M Nu Nd : ℕ}

/-- Spin occupations: `occS (inl i) = n_{i↑}`, `occS (inr i) = n_{i↓}`. -/
def occS : Fin M ⊕ Fin M → Conf M Nu × Conf M Nd → ℝ :=
  fun σi x => Sum.elim (fun i => occF i x.1) (fun i => occF i x.2) σi

/-- The two-species Hamiltonian without potential: spin-conserving hopping `t` and a diagonal
interaction `Vint`. -/
noncomputable def H0S (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : Fin M → Fin M → ℝ)
    (Vint : Conf M Nu × Conf M Nd → ℝ) : Matrix (Conf M Nu × Conf M Nd) (Conf M Nu × Conf M Nd) ℝ :=
  kronSum (Γ (-hopM G t)) (Γ (-hopM G t)) + diagonal Vint

/-- The Hubbard interaction `U Σ_i n_{i↑} n_{i↓}`. -/
noncomputable def hubbard (U : ℝ) : Conf M Nu × Conf M Nd → ℝ :=
  fun x => U * ∑ i, occF i x.1 * occF i x.2

/-- Trivial shifts of a spin-dependent potential: a constant on each spin. -/
def spinConst : Set (Fin M ⊕ Fin M → ℝ) :=
  {w | ∃ a b : ℝ, ∀ i, w (Sum.inl i) = a ∧ w (Sum.inr i) = b}

lemma H0S_isSymm (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] {t : Fin M → Fin M → ℝ}
    (ht : ∀ a b, t a b = t b a) (Vint : Conf M Nu × Conf M Nd → ℝ) : (H0S G t Vint).IsSymm :=
  (kronSum_isSymm (gamma_isSymm (hopM_isSymm G ht).neg) (gamma_isSymm (hopM_isSymm G ht).neg)).add
    (isSymm_diagonal Vint)

lemma sum_occS (w : Fin M ⊕ Fin M → ℝ) (x : Conf M Nu × Conf M Nd) :
    ∑ σi, w σi * occS σi x = wC (fun i => w (Sum.inl i)) x.1 + wC (fun i => w (Sum.inr i)) x.2 := by
  simp [occS, wC, Fintype.sum_sum_type]

lemma conf_nonempty {N : ℕ} (hN : N ≤ M) : Nonempty (Conf M N) := by
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin M)))
    (by simpa using hN)
  exact ⟨⟨s, hs⟩⟩

/-- **Rigidity for two species**: modulo a constant on each spin. -/
theorem rigid_occS (hNu0 : 0 < Nu) (hNuM : Nu < M) (hNd0 : 0 < Nd) (hNdM : Nd < M) :
    RigidMod spinConst (occS : Fin M ⊕ Fin M → Conf M Nu × Conf M Nd → ℝ) := by
  intro w κ h
  obtain ⟨x0⟩ := conf_nonempty (M := M) hNuM.le
  obtain ⟨y0⟩ := conf_nonempty (M := M) hNdM.le
  have hu : ∀ x : Conf M Nu, ∑ i, (fun i => w (Sum.inl i)) i * occF i x =
      κ - wC (fun i => w (Sum.inr i)) y0 := by
    intro x; have := h (x, y0); rw [sum_occS] at this; simp only [wC] at this ⊢; linarith
  have hd : ∀ y : Conf M Nd, ∑ i, (fun i => w (Sum.inr i)) i * occF i y =
      κ - wC (fun i => w (Sum.inl i)) x0 := by
    intro y; have := h (x0, y); rw [sum_occS] at this; simp only [wC] at this ⊢; linarith
  obtain ⟨a, ha⟩ := rigid_occF hNu0 hNuM _ _ hu
  obtain ⟨b, hb⟩ := rigid_occF hNd0 hNdM _ _ hd
  exact ⟨a, b, fun i => ⟨ha i, hb i⟩⟩

lemma alphaRep_congr {C : Type*} [Fintype C] [DecidableEq C] {A : Matrix C C ℝ} {w w' : C → ℝ}
    (h : w = w') (hw : Function.Injective w) (hw' : Function.Injective w') {d : C → ℕ}
    (hL : Lip A d) {c : C} (hc : d c = 0) (y z : C) :
    alphaRep A w hw d hL c hc y z = alphaRep A w' hw' d hL c hc y z := by
  subst h; rfl

/-- `formW s s' + a` is a nonzero polynomial for `s ≠ s'`. -/
lemma formW_add_C_ne_zero {N : ℕ} {s s' : Conf M N} (h : s ≠ s') (a : ℝ) :
    formW s s' + C a ≠ 0 := by
  intro h0
  have e0 := congrArg (eval (0 : Fin M → ℝ)) h0
  simp only [map_add, eval_C, eval_formW, map_zero] at e0
  have ha : a = 0 := by simpa [wC] using e0
  rw [ha, map_zero, add_zero] at h0
  exact formW_ne_zero h h0

/-- **(H*) for two spin species** with hopping of a common sign and any diagonal interaction. -/
theorem hstar_spin {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} {s : ℝ} (hts : ∀ a b, G.Adj a b → 0 < s * t a b)
    (c : Conf M Nu × Conf M Nd) (Vint : Conf M Nu × Conf M Nd → ℝ) :
    krylovPoly (H0S G t Vint) occS c
      (fun j => (Fintype.equivFin (Conf M Nu × Conf M Nd) j : ℕ)) ≠ 0 := by
  classical
  obtain ⟨u1, hw1, hα1, -⟩ := exists_good_u hG hts c.1 (κ := Empty) (fun k => k.elim)
    (fun k => k.elim)
  -- the down-spin potential avoids all coincidences of combined energies
  set κ := {p : (Conf M Nu × Conf M Nu) × (Conf M Nd × Conf M Nd) // p.2.1 ≠ p.2.2}
  obtain ⟨u2, hw2, hα2, hR⟩ := exists_good_u hG hts c.2 (κ := κ)
    (fun p => formW p.1.2.1 p.1.2.2 + C (wC u1 p.1.1.1 - wC u1 p.1.1.2))
    (fun p => formW_add_C_ne_zero p.2 _)
  set W : Conf M Nu × Conf M Nd → ℝ := fun y => wC u1 y.1 + wC u2 y.2
  have hW : Function.Injective W := by
    intro y z hyz
    by_cases e2 : y.2 = z.2
    · have : wC u1 y.1 = wC u1 z.1 := by simp only [W, e2] at hyz; linarith
      exact Prod.ext (hw1 this) e2
    · exfalso
      apply hR ⟨((y.1, z.1), (y.2, z.2)), e2⟩
      simp only [map_add, eval_C, eval_formW]
      simp only [W] at hyz; linarith
  set u : Fin M ⊕ Fin M → ℝ := Sum.elim u1 u2
  have hfun : (fun y => ∑ i, u i * occS i y) = W := by
    funext y; rw [sum_occS]; rfl
  have hw : Function.Injective (fun y => ∑ i, u i * occS i y) := hfun ▸ hW
  have hL := lip_kronSum (lip_mopt hG t c.1) (lip_mopt hG t c.2)
  have hc : (fun y : Conf M Nu × Conf M Nd => mopt G c.1 y.1 + mopt G c.2 y.2) c = 0 := by
    simp [mopt_self]
  have hα : ∀ y, alphaRep (kronSum (Γ (-hopM G t)) (Γ (-hopM G t))) _ hw _ hL c hc y y ≠ 0 := by
    intro y
    rw [alphaRep_congr hfun hw hW]
    rw [alpha_kronSum (wC u1) (wC u2) (lip_mopt hG t c.1) (lip_mopt hG t c.2) (mopt_self G c.1)
      (mopt_self G c.2) hw1 hw2 hW y]
    exact mul_ne_zero (hα1 y.1) (hα2 y.2)
  exact hstar_of_alpha hL hc occS u hw hα Vint

/-- **Spin-resolved generic Hohenberg–Kohn theorem.** For `Nu` spin-up and `Nd` spin-down electrons
(`0 < Nσ < M`) on a connected graph, with symmetric hopping amplitudes of a common sign and any
diagonal interaction, the spin-dependent potentials at which some ground state is shared with a
potential differing by more than a separate constant on each spin lie in a closed, nowhere dense,
Lebesgue-null set. -/
theorem generic_hk_spin {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hNu0 : 0 < Nu) (hNuM : Nu < M) (hNd0 : 0 < Nd)
    (hNdM : Nd < M) (Vint : Conf M Nu × Conf M Nd → ℝ) :
    ∃ Z : Set (Fin M ⊕ Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUVMod spinConst (H0S G t Vint) occS v} ⊆ Z :=
  generic_hk_ae_mod (H0S_isSymm G htsym Vint) (rigid_occS hNu0 hNuM hNd0 hNdM) _
    (fun c => hstar_spin hG hts c Vint)

/-- **Spin-resolved generic Hohenberg–Kohn theorem for the Hubbard model** with uniform hopping
`t ≠ 0`. -/
theorem generic_hk_hubbard {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : ℝ} (ht : t ≠ 0) (U : ℝ) (hNu0 : 0 < Nu) (hNuM : Nu < M) (hNd0 : 0 < Nd)
    (hNdM : Nd < M) :
    ∃ Z : Set (Fin M ⊕ Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ MeasureTheory.volume Z = 0 ∧
      {v | NonUVMod spinConst (H0S G (fun _ _ => t) (hubbard (Nu := Nu) (Nd := Nd) U)) occS v} ⊆
          Z :=
  generic_hk_spin hG (fun _ _ => rfl) (s := t) (fun _ _ _ => mul_self_pos.mpr ht) hNu0 hNuM hNd0
    hNdM (hubbard (Nu := Nu) (Nd := Nd) U)

end DFT
