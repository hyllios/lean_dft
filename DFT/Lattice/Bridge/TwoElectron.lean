/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.Spin.TwoElectron
import DFT.Lattice.Spin.SpinResolved
import DFT.Lattice.Bridge.Hubbard
import DFT.Lattice.Bridge.Square

/-!
# Bridge: one up and one down electron of `H0S` is one particle on `G □ G`

`Spin/TwoElectron.lean` proves total-density Hohenberg–Kohn for `ham2`, a single particle on the
product graph `G □ G`. This file shows that `ham2` is the library's two-species Hamiltonian `H0S` at
one electron per spin, on any graph on `Fin M`, with uniform hopping `t`, any configuration-diagonal
interaction `Vint` and the total-density coupling `nTot i = n_{i↑} + n_{i↓}`. The basis is `(a, b) ↦
(one M a, one M b)` (up electron on `a`, down electron on `b`); one electron per species means no
fermion sign.

* `oneEquiv`, `Γ_one`: `Fin M ≃ Conf M 1`, and `Γ A` on one electron is `A`;
* `hamN_H0S_eq_ham2` (entries), `hamN_H0S_submatrix` (matrices);
* `two_electron_hk_H0S`: a ground state shared by `v` and `v'` forces `v − v'` constant;
* `two_electron_density_determines_potential`: so does a shared ground-state density.
* `two_electron_ground_ne_zero`: every ground state has no zero amplitude (`t > 0`, connected
  graph).
-/

namespace DFT

open Matrix

namespace Bridge.TwoElectron

open Bridge.Hubbard Bridge.Square

variable {M : ℕ}

/-- Every one-electron configuration is `one M a` for some site `a`. -/
lemma one_surjective (M : ℕ) : Function.Surjective (one M) := by
  rintro ⟨s, hs⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  exact ⟨a, rfl⟩

/-- Sites are one-electron configurations: `a ↦ {a}`. -/
noncomputable def oneEquiv (M : ℕ) : Fin M ≃ Conf M 1 :=
  Equiv.ofBijective (one M) ⟨fun a b h => (one_inj M a b).mp h, one_surjective M⟩

/-- `oneEquiv` is `one`. -/
@[simp] lemma oneEquiv_apply (M : ℕ) (a : Fin M) : oneEquiv M a = one M a := rfl

/-- The second quantization of a single-particle matrix on one electron is the matrix itself (no
fermion sign). -/
lemma Γ_one (A : Matrix (Fin M) (Fin M) ℝ) (a b : Fin M) : Γ A (one M a) (one M b) = A a b := by
  simp [Γ, amp, slater, τs_one, Matrix.det_unique]

/-- The total occupation `n_{i↑} + n_{i↓}` on one up and one down electron. -/
def nTot (i : Fin M) (x : Conf M 1 × Conf M 1) : ℝ := occF i x.1 + occF i x.2

/-- The total-density potential energy of the configuration (up on `a`, down on `b`). -/
lemma sum_nTot_one (v : Fin M → ℝ) (a b : Fin M) :
    ∑ i, v i * nTot i (one M a, one M b) = v a + v b := by
  simp [nTot, occF_one, mul_add, Finset.sum_add_distrib]

/-- **The physical two-electron Hamiltonian is `ham2`.** One up and one down electron of `H0S` with
uniform hopping `t` and interaction `Vint`, in the total-density potential `v`, is the single
particle on `G □ G` of `ham2`, entry by entry (up on `a`, down on `b` ↦ vertex `(a, b)`). Sign
conventions agree: `H0S` hops with `Γ (-hopM G t)`, `ham` with `-t • adjMatrix`. -/
theorem hamN_H0S_eq_ham2 (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : ℝ)
    (Vint : Conf M 1 × Conf M 1 → ℝ) (v : Fin M → ℝ) (a b c d : Fin M) :
    hamN (H0S G (fun _ _ => t) Vint) nTot v (one M a, one M b) (one M c, one M d) =
      ham2 G t (fun p => Vint (one M p.1, one M p.2)) v (a, b) (c, d) := by
  simp only [hamN, H0S, ham2, ham, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    kronSum_apply, Γ_one, Matrix.neg_apply, hopM, Matrix.one_apply, Matrix.diagonal_apply,
    one_inj, Prod.mk.injEq, sum_nTot_one, SimpleGraph.adjMatrix_apply, SimpleGraph.boxProd_adj,
    smul_eq_mul]
  by_cases hac : a = c <;> by_cases hbd : b = d <;> simp [hac, hbd, eq_comm]
  ring

/-- `hamN_H0S_eq_ham2` as an equality of matrices: reindexing by `(a, b) ↦ (one M a, one M b)`. -/
theorem hamN_H0S_submatrix (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (t : ℝ)
    (Vint : Conf M 1 × Conf M 1 → ℝ) (v : Fin M → ℝ) :
    (hamN (H0S G (fun _ _ => t) Vint) nTot v).submatrix
        ((oneEquiv M).prodCongr (oneEquiv M)) ((oneEquiv M).prodCongr (oneEquiv M)) =
      ham2 G t (fun p => Vint (one M p.1, one M p.2)) v := by
  ext ⟨a, b⟩ ⟨c, d⟩
  exact hamN_H0S_eq_ham2 G t Vint v a b c d

/-- **Total-density HK for one up and one down electron of `H0S`, every potential.** For uniform
hopping `t > 0` on a connected graph and any interaction `Vint`, a ground state shared by `v` and
`v'` forces `v − v'` constant. -/
theorem two_electron_hk_H0S (G : SimpleGraph (Fin M)) [DecidableRel G.Adj] (hG : G.Connected)
    {t : ℝ} (ht : 0 < t) (Vint : Conf M 1 × Conf M 1 → ℝ) {v v' : Fin M → ℝ}
    {ψ : Conf M 1 × Conf M 1 → ℝ}
    (h : IsGroundState (hamN (H0S G (fun _ _ => t) Vint) nTot v) ψ)
    (h' : IsGroundState (hamN (H0S G (fun _ _ => t) Vint) nTot v') ψ) :
    ∃ k : ℝ, ∀ i, v i - v' i = k := by
  rw [← isGroundState_reindex ((oneEquiv M).prodCongr (oneEquiv M)), hamN_H0S_submatrix] at h h'
  exact two_electron_hk G hG ht _ h h'

/-- **The total density determines the potential.** For uniform hopping `t > 0` on a connected graph
and any interaction `Vint`, normalized ground states of `v` and of `v'` with the same total density
force `v − v'` constant. -/
theorem two_electron_density_determines_potential (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (hG : G.Connected) {t : ℝ} (ht : 0 < t) (Vint : Conf M 1 × Conf M 1 → ℝ) {v v' : Fin M → ℝ}
    {ψ ψ' : Conf M 1 × Conf M 1 → ℝ}
    (hψ : IsGroundState (hamN (H0S G (fun _ _ => t) Vint) nTot v) ψ)
    (hψ' : IsGroundState (hamN (H0S G (fun _ _ => t) Vint) nTot v') ψ')
    (hN : ψ ⬝ᵥ ψ = 1) (hN' : ψ' ⬝ᵥ ψ' = 1) (hd : dens nTot ψ = dens nTot ψ') :
    ∃ k : ℝ, ∀ i, v i - v' i = k :=
  two_electron_hk_H0S G hG ht Vint hψ (weak_hk hψ hψ' hN hN' hd).1

/-- **No zero amplitude.** With one electron of each spin, uniform hopping `t > 0` on a connected
graph and any interaction `Vint`, every ground state of the total-density Hamiltonian has no zero
amplitude, for every potential. -/
theorem two_electron_ground_ne_zero (G : SimpleGraph (Fin M)) [DecidableRel G.Adj]
    (hG : G.Connected) {t : ℝ} (ht : 0 < t) (Vint : Conf M 1 × Conf M 1 → ℝ) {v : Fin M → ℝ}
    {ψ : Conf M 1 × Conf M 1 → ℝ}
    (h : IsGroundState (hamN (H0S G (fun _ _ => t) Vint) nTot v) ψ) : ∀ x, ψ x ≠ 0 := by
  set e := (oneEquiv M).prodCongr (oneEquiv M)
  rw [← isGroundState_reindex e, hamN_H0S_submatrix] at h
  have hbox : (G □ G).Connected := hG.boxProd hG
  have hpos := pos_of_nonneg (G □ G) hbox ht (abs_isGroundState (G □ G) ht h)
    (fun _ => abs_nonneg _)
  intro x hx
  have := hpos (e.symm x)
  simp only [Function.comp_apply, Equiv.apply_symm_apply, hx, abs_zero, lt_self_iff_false] at this

end Bridge.TwoElectron

end DFT
