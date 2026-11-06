/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.TDDFT.ForceBalance
import DFT.Lattice.TDDFT.Existence

/-!
# Lattice TDDFT starting from a ground state

For a real state `ψ0` (the point `(ψ0, 0)` in real coordinates) the force-balance matrix of the
dynamics is minus the static one: `wᵀ K(ψ0, 0) w = -wᵀ kMat(ψ0) w` (`kfb_quad_real`). Hence:

* `mem_omega_of_definite`: if `kMat(ψ0)` is negative semidefinite with only constant zero modes,
  then `(ψ0, 0) ∈ Ω`.
* `generic_ground_mem_omega`: for spinless lattice fermions, outside a closed, nowhere dense, null
  set of static potentials, every ground state is in `Ω`; by `td_existence` and `td_uniqueness`,
  every density consistent with it is then locally v-representable, with a unique potential (the
  corrected Theorem 2 of Farzanehpour & Tokatly).
-/

namespace DFT

open Matrix MeasureTheory

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- For a real state the dynamical force-balance form is minus the static one. -/
theorem kfb_quad_real {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (x : C → ℝ)
    (w : V → ℝ) :
    w ⬝ᵥ (kfb H0 n (x, 0) *ᵥ w) = -(w ⬝ᵥ (kMat H0 n x *ᵥ w)) := by
  rw [kMat_form]
  set d := potW n w
  -- the dynamical form, written as a double sum over configurations
  have hD : ∑ i, w i • Nmat n i = diagonal d := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Nmat, diagonal_apply, smul_eq_mul, d, potW]
    split_ifs <;> simp
  have hM : ∑ i, ∑ j, (w i * w j) • (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i) =
      H0 * diagonal d * diagonal d - diagonal d * H0 * diagonal d := by
    rw [← hD]
    simp only [smul_sub, Finset.sum_sub_distrib, Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm,
      smul_mul_assoc, smul_smul, Matrix.mul_assoc, Finset.smul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (w i)]
  have hdyn : w ⬝ᵥ (kfb H0 n (x, 0) *ᵥ w) =
      -2 * ∑ c, ∑ c', H0 c c' * x c * x c' * (d c' ^ 2 - d c * d c') := by
    have h1 : w ⬝ᵥ (kfb H0 n (x, 0) *ᵥ w) =
        -2 * Qf (∑ i, ∑ j, (w i * w j) • (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i))
          (x, 0) := by
      simp only [Qf_sum, Qf_smul, dotProduct, mulVec, kfb, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    rw [h1, hM]
    simp only [Qf, Pi.zero_apply, add_zero, dotProduct, mulVec,
      Matrix.sub_apply, Matrix.mul_apply,
      diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.sum_const_zero]
    congr 1
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c' _
    ring
  have hsym : ∑ c, ∑ c', H0 c c' * x c * x c' * d c ^ 2 =
      ∑ c, ∑ c', H0 c c' * x c * x c' * d c' ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro c' _
    rw [hH0.apply c c']; ring
  rw [hdyn]
  have hexp : ∀ c c', H0 c c' * x c * x c' * (d c - d c') ^ 2 =
      H0 c c' * x c * x c' * d c ^ 2 + 2 * (H0 c c' * x c * x c' * (d c' ^ 2 - d c * d c')) -
        H0 c c' * x c * x c' * d c' ^ 2 := by intro c c'; ring
  simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsym]
  ring

/-- A real state whose static force-balance matrix is negative semidefinite with only constant zero
modes lies in the v-representability set. -/
theorem mem_omega_of_definite [Nonempty V] {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm)
    {n : V → C → ℝ} {x : C → ℝ} (hneg : ∀ w, w ⬝ᵥ (kMat H0 n x *ᵥ w) ≤ 0)
    (hdef : ∀ w, w ⬝ᵥ (kMat H0 n x *ᵥ w) = 0 → ∃ k, ∀ i, w i = k) :
    ((x, 0) : (C → ℝ) × (C → ℝ)) ∈ omega H0 n := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have hq : w ⬝ᵥ (kJ H0 n (x, 0) *ᵥ w) = 0 := by rw [hw, dotProduct_zero]
  have hJ : w ⬝ᵥ ((onesM : Matrix V V ℝ) *ᵥ w) = (∑ j, w j) ^ 2 := by
    rw [onesM_mulVec]; simp [dotProduct, ← Finset.sum_mul, sq]
  rw [kJ, add_mulVec, dotProduct_add, hJ, kfb_quad_real hH0] at hq
  have h1 := hneg w
  have hk : w ⬝ᵥ (kMat H0 n x *ᵥ w) = 0 := by nlinarith [sq_nonneg (∑ j, w j)]
  have hs : ∑ j, w j = 0 := by nlinarith [sq_nonneg (∑ j, w j)]
  obtain ⟨k, hk'⟩ := hdef w hk
  apply hw0
  have hk0 : k = 0 := by
    simp only [hk', Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact absurd h (by exact_mod_cast Fintype.card_ne_zero)
    · exact h
  funext i; rw [hk' i, hk0]; rfl

variable {M N : ℕ}

/-- **Lattice TDDFT from the ground state, for almost every potential** (corrected Theorem 2 of
Farzanehpour–Tokatly). Spinless lattice fermions on a connected graph, symmetric hopping of a common
sign, any interaction: outside a closed, nowhere dense, Lebesgue-null set of static potentials `v0`,
every (real) ground state of `H(v0)` lies in the v-representability set `Ω`. Then `td_existence` and
`td_uniqueness` give, for every density consistent with it, a unique potential locally in time. -/
theorem generic_ground_mem_omega [NeZero M] {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M)
    (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ v0 ∉ Z, ∀ ψ0, IsGroundState (hamN (H0Fw G t Vint) occF v0) ψ0 →
        ((ψ0, 0) : (Conf M N → ℝ) × (Conf M N → ℝ)) ∈ omega (H0Fw G t Vint) occF := by
  obtain ⟨Z, hcl, hint, hvol, hZ⟩ := generic_td_vrep hG htsym hts hN0 hNM Vint
  refine ⟨Z, hcl, hint, hvol, fun v0 hv0 ψ0 hψ0 => ?_⟩
  have hH0 := H0Fw_isSymm G htsym Vint
  exact mem_omega_of_definite hH0 (kMat_nonpos hH0 hψ0) (hZ v0 hv0 ψ0 hψ0)

end DFT
