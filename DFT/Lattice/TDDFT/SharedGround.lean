/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.Generic.SquarePlane
import DFT.Lattice.TDDFT.GroundStart

/-!
# Shared ground states lie outside Ω; the density determines the potential

* `kfb_real_mulVec`, `kfb_real_mulVec_eq_zero`: `K(x, 0)` applied to a change of potential `u`, for
  a real state `x`; a change constant on the support of `x` is a zero mode (the library has the
  quadratic-form version `kfb_quad_real`).
* `shared_ground_state_not_mem_omega`: every ground state shared by two potentials that differ by
  more than a constant lies outside `Ω` (any symmetric `H0`, fixed particle number).
  `shared_ground_state_pair_not_mem_omega`: the same for a complex ground state `x + i y` (with
  `kfb_split`, `rayleigh_eq_of_ground`).
* `Qf_split`, `kfb_split`: the force-balance matrix of a pair `(x, y)` splits into the two real
  parts. `mem_omega_of_definite_pair`, the pair version of `mem_omega_of_definite` (not used
  elsewhere in the library): a pair whose static forms are negative semidefinite, the first with
  only constant zero modes, lies in `Ω`.
* `density_determines_potential`: the generic Hohenberg–Kohn theorem
  (`generic_hk_lattice_fermions_w`) with `weak_hk`: outside the exceptional set the ground-state
  density determines the potential up to a constant.
-/

namespace DFT

open Matrix MeasureTheory

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- K(x, 0) applied to u, for a real state x: a double sum over configurations weighted by the
change of the potential energy d = potW n u between them. -/
lemma kfb_real_mulVec (H0 : Matrix C C ℝ) (n : V → C → ℝ) (x : C → ℝ) (u : V → ℝ) (i : V) :
    (kfb H0 n (x, 0) *ᵥ u) i =
      -2 * ∑ c, ∑ c', H0 c c' * x c * x c' * n i c' * (potW n u c' - potW n u c) := by
  simp only [mulVec, dotProduct, kfb, Qf, Nmat, Matrix.sub_apply, Matrix.mul_assoc,
    diagonal_mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, potW, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1 <;>
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun j _ => ?_
    ring

omit [DecidableEq V] in
/-- A change of potential that is constant on the support of a real state is a zero mode of K(x, 0).
-/
lemma kfb_real_mulVec_eq_zero (H0 : Matrix C C ℝ) (n : V → C → ℝ) {x : C → ℝ} {u : V → ℝ} {κ : ℝ}
    (hd : ∀ c, x c ≠ 0 → potW n u c = κ) : kfb H0 n (x, 0) *ᵥ u = 0 := by
  funext i
  rw [kfb_real_mulVec, Pi.zero_apply]
  have hz : ∀ c c', H0 c c' * x c * x c' * n i c' * (potW n u c' - potW n u c) = 0 := by
    intro c c'
    by_cases hc : x c = 0
    · simp [hc]
    by_cases hc' : x c' = 0
    · simp [hc']
    rw [hd c hc, hd c' hc', sub_self, mul_zero]
  simp [hz]

/-- **Shared ground states lie outside Ω.** A ground state shared by two potentials that differ by
more than a constant lies outside Ω (fixed particle number Ntot in every configuration, symmetric
`H0`). -/
theorem shared_ground_state_not_mem_omega [Nonempty V] {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm)
    {n : V → C → ℝ} {Ntot : ℝ} (hN : ∀ c, ∑ i, n i c = Ntot) {v v' : V → ℝ} {ψ : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) (hψ' : IsGroundState (hamN H0 n v') ψ)
    (hne : ¬ ∃ k, ∀ i, v i - v' i = k) :
    ((ψ, 0) : (C → ℝ) × (C → ℝ)) ∉ omega H0 n := by
  -- on the support of ψ, the potential energy of v − v' is a constant κ
  obtain ⟨κ, hw⟩ := support_const_of_shared hH0 hψ hψ'
  -- remove the mean of v − v', so that the vector also sums to zero
  set m : ℝ := (∑ i, (v i - v' i)) / Fintype.card V
  set u : V → ℝ := fun i => v i - v' i - m
  have hu : ∀ c, ψ c ≠ 0 → potW n u c = κ - m * Ntot := by
    intro c hc
    have h := hw c hc
    simp only [potW]
    simp only [u, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hN c] at h ⊢
    rw [h]
  have hK : kfb H0 n (ψ, 0) *ᵥ u = 0 := kfb_real_mulVec_eq_zero H0 n hu
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ i, u i = 0 := by
    simp only [u, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
    field_simp
    ring
  have hu0 : u ≠ 0 := by
    intro h
    apply hne
    refine ⟨m, fun i => ?_⟩
    have := congrFun h i
    simp only [u, Pi.zero_apply] at this
    linarith
  intro hω
  apply hω
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨u, hu0, ?_⟩
  rw [kJ, add_mulVec, hK, onesM_mulVec, zero_add]
  funext i
  simp [hsum]

omit [DecidableEq C] [Fintype V] [DecidableEq V] in
/-- Two ground states of the same matrix have the same Rayleigh quotient. -/
lemma rayleigh_eq_of_ground {A : Matrix C C ℝ} {a b : C → ℝ} (ha : IsGroundState A a)
    (hb : IsGroundState A b) : qf A a / (a ⬝ᵥ a) = qf A b / (b ⬝ᵥ b) := by
  have pa : 0 < a ⬝ᵥ a := lt_of_le_of_ne
    (by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i))
    (Ne.symm (dotProduct_self_eq_zero.not.mpr ha.1))
  have pb : 0 < b ⬝ᵥ b := lt_of_le_of_ne
    (by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (b i))
    (Ne.symm (dotProduct_self_eq_zero.not.mpr hb.1))
  have h1 := ha.2 b
  have h2 := hb.2 a
  rw [div_eq_div_iff pa.ne' pb.ne']
  linarith

omit [DecidableEq C] in
lemma Qf_split (M : Matrix C C ℝ) (X Y : C → ℝ) : Qf M (X, Y) = Qf M (X, 0) + Qf M (Y, 0) := by
  simp [Qf]

omit [Fintype V] [DecidableEq V] in
/-- The force-balance matrix of a pair splits into the two real parts. -/
lemma kfb_split (H : Matrix C C ℝ) (n : V → C → ℝ) (X Y : C → ℝ) :
    kfb H n (X, Y) = kfb H n (X, 0) + kfb H n (Y, 0) := by
  ext i j
  simp only [kfb, Matrix.add_apply]
  rw [Qf_split]; ring

/-- A pair of real states whose static forms are negative semidefinite, the first with only
constant zero modes, lies in `Ω`. -/
theorem mem_omega_of_definite_pair [Nonempty V] {H : Matrix C C ℝ} (hH : H.IsSymm)
    {n : V → C → ℝ} {X Y : C → ℝ} (hX : ∀ w, w ⬝ᵥ (kMat H n X *ᵥ w) ≤ 0)
    (hY : ∀ w, w ⬝ᵥ (kMat H n Y *ᵥ w) ≤ 0)
    (hdef : ∀ w, w ⬝ᵥ (kMat H n X *ᵥ w) = 0 → ∃ k, ∀ i, w i = k) :
    ((X, Y) : (C → ℝ) × (C → ℝ)) ∈ omega H n := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have hq : w ⬝ᵥ (kJ H n (X, Y) *ᵥ w) = 0 := by rw [hw, dotProduct_zero]
  have hJ : w ⬝ᵥ ((onesM : Matrix V V ℝ) *ᵥ w) = (∑ j, w j) ^ 2 := by
    rw [onesM_mulVec]; simp [dotProduct, ← Finset.sum_mul, sq]
  rw [kJ, kfb_split, add_mulVec, add_mulVec, dotProduct_add, dotProduct_add, hJ,
    kfb_quad_real hH, kfb_quad_real hH] at hq
  have h1 := hX w
  have h2 := hY w
  have hk : w ⬝ᵥ (kMat H n X *ᵥ w) = 0 := by nlinarith [sq_nonneg (∑ j, w j)]
  have hs : ∑ j, w j = 0 := by nlinarith [sq_nonneg (∑ j, w j)]
  obtain ⟨k, hk'⟩ := hdef w hk
  apply hw0
  have hk0 : k = 0 := by
    simp only [hk', Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact absurd h (by exact_mod_cast Fintype.card_ne_zero)
    · exact h
  funext i; rw [hk' i, hk0]; rfl

/-- **A complex ground state shared by two potentials lies outside Ω.** For `ψ = x + i y` with real
symmetric `H(v)`, `H(v')`, each of `x`, `y` is zero or a ground state of both (this is what a
complex ground state of a real Hamiltonian is; the equivalence itself is not formalized here, it is
the hypothesis); if `v − v'` is not constant, `(x, y)` is not in `Ω` (fixed particle number). The
real case is `shared_ground_state_not_mem_omega`. -/
theorem shared_ground_state_pair_not_mem_omega [Nonempty V] {H0 : Matrix C C ℝ}
    (hH0 : H0.IsSymm) {n : V → C → ℝ} {Ntot : ℝ} (hN : ∀ c, ∑ i, n i c = Ntot) {v v' : V → ℝ}
    {x y : C → ℝ}
    (hx : x ≠ 0 → IsGroundState (hamN H0 n v) x ∧ IsGroundState (hamN H0 n v') x)
    (hy : y ≠ 0 → IsGroundState (hamN H0 n v) y ∧ IsGroundState (hamN H0 n v') y)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hne : ¬ ∃ k, ∀ i, v i - v' i = k) :
    ((x, y) : (C → ℝ) × (C → ℝ)) ∉ omega H0 n := by
  -- a reference ground state z, shared by both potentials
  obtain ⟨z, hz, hz'⟩ : ∃ z, IsGroundState (hamN H0 n v) z ∧ IsGroundState (hamN H0 n v') z := by
    rcases hxy with h | h
    · exact ⟨x, hx h⟩
    · exact ⟨y, hy h⟩
  set E := qf (hamN H0 n v) z / (z ⬝ᵥ z)
  set E' := qf (hamN H0 n v') z / (z ⬝ᵥ z)
  -- every nonzero component a of (x, y): on its support, potW (v − v') = E − E'
  have hcomp : ∀ a : C → ℝ, (a ≠ 0 → IsGroundState (hamN H0 n v) a ∧
      IsGroundState (hamN H0 n v') a) →
      ∀ c, a c ≠ 0 → potW n (fun i => v i - v' i) c = E - E' := by
    intro a ha c hc
    have ha0 : a ≠ 0 := fun h => hc (by simp [h])
    obtain ⟨g, g'⟩ := ha ha0
    have hE := isGroundState_eigen (hamN_isSymm hH0 n v) g
    have hE' := isGroundState_eigen (hamN_isSymm hH0 n v') g'
    rw [rayleigh_eq_of_ground g hz] at hE
    rw [rayleigh_eq_of_ground g' hz'] at hE'
    have e1 := congrFun hE c
    have e2 := congrFun hE' c
    rw [hamN_mulVec_apply] at e1 e2
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    have : (∑ i, (v i - v' i) * n i c) * a c = (E - E') * a c := by
      simp only [sub_mul, Finset.sum_sub_distrib]; linarith
    exact mul_right_cancel₀ hc this
  set m : ℝ := (∑ i, (v i - v' i)) / Fintype.card V
  set u : V → ℝ := fun i => v i - v' i - m
  have hu : ∀ a : C → ℝ, (a ≠ 0 → IsGroundState (hamN H0 n v) a ∧
      IsGroundState (hamN H0 n v') a) → ∀ c, a c ≠ 0 → potW n u c = E - E' - m * Ntot := by
    intro a ha c hc
    have h := hcomp a ha c hc
    simp only [potW] at h ⊢
    simp only [u, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hN c] at h ⊢
    rw [h]
  have hK : kfb H0 n (x, y) *ᵥ u = 0 := by
    rw [kfb_split, add_mulVec, kfb_real_mulVec_eq_zero H0 n (hu x hx),
      kfb_real_mulVec_eq_zero H0 n (hu y hy), add_zero]
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ i, u i = 0 := by
    simp only [u, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
    field_simp
    ring
  have hu0 : u ≠ 0 := by
    intro h
    apply hne
    refine ⟨m, fun i => ?_⟩
    have := congrFun h i
    simp only [u, Pi.zero_apply] at this
    linarith
  intro hω
  apply hω
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨u, hu0, ?_⟩
  rw [kJ, add_mulVec, hK, onesM_mulVec, zero_add]
  funext i
  simp [hsum]

variable {M N : ℕ}

/-- **The density determines the potential, outside the exceptional set** of the generic
Hohenberg–Kohn theorem (hopping `t_ab` of a common sign `s` on the edges of a connected graph, any
interaction): a normalized ground state of any other potential `v'` with the same density forces `v
− v'` constant. -/
theorem density_determines_potential {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M)
    (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ v ∉ Z, ∀ (v' : Fin M → ℝ) (ψ ψ' : Conf M N → ℝ),
        IsGroundState (hamN (H0Fw G t Vint) occF v) ψ →
        IsGroundState (hamN (H0Fw G t Vint) occF v') ψ' →
        ψ ⬝ᵥ ψ = 1 → ψ' ⬝ᵥ ψ' = 1 → dens occF ψ = dens occF ψ' →
        ∃ k, ∀ i, v i - v' i = k := by
  obtain ⟨Z, hcl, hint, hvol, hZ⟩ := generic_hk_lattice_fermions_w hG htsym hts hN0 hNM Vint
  refine ⟨Z, hcl, hint, hvol, fun v hv v' ψ ψ' h h' hn hn' hd => ?_⟩
  by_contra hne
  exact hv (hZ ⟨ψ, v', h, (weak_hk h h' hn hn' hd).1, hne⟩)

end DFT
