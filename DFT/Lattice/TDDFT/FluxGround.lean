/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.TDDFT.ComplexHopping
import DFT.Lattice.Generic.NullSets
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Lattice TDDFT with flux, starting from a ground state

With complex hopping `A + iB` the ground states are genuinely complex. In the doubled real
description (`dblH`) the state `ψ = x + iy` is the pair `X = (x, y)`, `JX = (y, -x)` (`Jop`, the
multiplication by `i`), and both are ground states of the doubled Hamiltonian.

* `kfb_dbl_split`: the force-balance form of `dbl ψ` is `-(kMat X) - (kMat JX)`; each is
  negative semidefinite at a ground state.
* `det_kryC_eq_zero`, `eigen_unique_of_hstarC`: the doubled Krylov criterion. If all doubled Krylov
  determinants (columns `H̃ᵏ e_(c,0)`, `H̃ᵏ e_(c,1)`) are nonzero, complex eigenvectors have no
  zeros and the eigenvalues are simple over `ℂ`.
* `mem_omegaC_of_hstarC`: then every complex ground state lies in `Ω`.
* `generic_flux_ground_mem_omegaC`: for lattice fermions with common-sign hopping `A` and any flux
  pattern `B`, for all but finitely many flux strengths `λ`, outside a closed, nowhere dense, null
  set of potentials every ground state of `A + iλB` lies in `Ω`.
-/

namespace DFT

open Matrix Set MeasureTheory

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

/-- Multiplication by `i` in the doubled description: `(x, y) ↦ (y, -x)`. -/
def Jop (X : C × Bool → ℝ) : C × Bool → ℝ := fun p => cond p.2 (-X (p.1, false)) (X (p.1, true))

omit [Fintype C] [DecidableEq C] in
@[simp] lemma Jop_false (X : C × Bool → ℝ) (c : C) : Jop X (c, false) = X (c, true) := rfl

omit [Fintype C] [DecidableEq C] in
@[simp] lemma Jop_true (X : C × Bool → ℝ) (c : C) : Jop X (c, true) = -X (c, false) := rfl

omit [Fintype C] [DecidableEq C] in
lemma dbl_eq_Jop (ψ : (C → ℝ) × (C → ℝ)) : dbl ψ = ((dbl ψ).1, Jop (dbl ψ).1) := by
  ext ⟨c, b⟩ <;> cases b <;> rfl

omit [DecidableEq C] in
lemma dot_Jop (X Y : C × Bool → ℝ) : Jop X ⬝ᵥ Jop Y = X ⬝ᵥ Y := by
  simp only [dotProduct, Fintype.sum_prod_type, Fintype.sum_bool, Jop_false, Jop_true]
  exact Finset.sum_congr rfl fun c _ => by ring

omit [DecidableEq C] in
lemma dot_Jop_self (X : C × Bool → ℝ) : X ⬝ᵥ Jop X = 0 := by
  simp only [dotProduct, Fintype.sum_prod_type, Fintype.sum_bool, Jop_false, Jop_true]
  exact Finset.sum_eq_zero fun c _ => by ring

omit [DecidableEq C] in
/-- The doubled Hamiltonian commutes with `J`. -/
lemma dblH_mulVec_Jop (M B : Matrix C C ℝ) (X : C × Bool → ℝ) :
    dblH M B *ᵥ Jop X = Jop (dblH M B *ᵥ X) := by
  have h1 : blk (Jop X) false = blk X true := rfl
  have h2 : blk (Jop X) true = -blk X false := rfl
  ext ⟨c, b⟩
  cases b
  · rw [dblH_mulVec_false, Jop_false, dblH_mulVec_true, h1, h2, mulVec_neg, Pi.neg_apply]; ring
  · rw [dblH_mulVec_true, Jop_true, dblH_mulVec_false, h1, h2, mulVec_neg, Pi.neg_apply]; ring

omit [DecidableEq C] in
lemma qf_Jop (M B : Matrix C C ℝ) (X : C × Bool → ℝ) :
    qf (dblH M B) (Jop X) = qf (dblH M B) X := by
  rw [qf, dblH_mulVec_Jop, dot_Jop, qf]

omit [DecidableEq V] in
/-- `J` maps ground states of the doubled Hamiltonian to ground states. -/
lemma isGroundState_Jop {A B : Matrix C C ℝ} {n : V → C → ℝ} {v : V → ℝ} {X : C × Bool → ℝ}
    (hX : IsGroundState (hamN (dblH A B) (dblN n) v) X) :
    IsGroundState (hamN (dblH A B) (dblN n) v) (Jop X) := by
  rw [hamN_dbl] at hX ⊢
  refine ⟨fun h => hX.1 ?_, fun φ => ?_⟩
  · have := congrArg (fun Y => Y ⬝ᵥ Y) h
    simp only [dot_Jop, dotProduct_zero] at this
    exact dotProduct_self_eq_zero.mp this
  · rw [qf_Jop, dot_Jop]; exact hX.2 φ

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

/-- A ground state for the hopping `A + iB`: `ψ` minimises `⟨ψ|H(v)|ψ⟩ / ⟨ψ|ψ⟩`, i.e. its doubled
real part is a ground state of the doubled Hamiltonian. -/
def IsGroundStateC (A B : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (ψ : (C → ℝ) × (C → ℝ)) :
    Prop :=
  IsGroundState (hamN (dblH A B) (dblN n) v) (dbl ψ).1

/-- Doubled Krylov matrix of configuration `c`: columns `H̃^(ord j) e_(c,b)`. -/
def kryC {R : Type*} [CommRing R] (H : Matrix (C × Bool) (C × Bool) R) (c : C) (ord : C → ℕ) :
    Matrix (C × Bool) (C × Bool) R :=
  fun i j => (H ^ ord j.1) i (c, j.2)

/-- An eigenvector vanishing at both components of `c` makes the doubled Krylov matrix singular. -/
lemma det_kryC_eq_zero {H : Matrix (C × Bool) (C × Bool) ℝ} (hS : H.IsSymm) {X : C × Bool → ℝ}
    {E : ℝ} (hX : X ≠ 0) (hE : H *ᵥ X = E • X) {c : C} (h0 : X (c, false) = 0)
    (h1 : X (c, true) = 0) (ord : C → ℕ) : (kryC H c ord).det = 0 := by
  rw [← exists_vecMul_eq_zero_iff]
  refine ⟨X, hX, ?_⟩
  have hl : X ᵥ* H = E • X := by
    conv_lhs => rw [← hS.eq]
    rw [vecMul_transpose, hE]
  have hv : ∀ k : ℕ, X ᵥ* (H ^ k) = E ^ k • X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, smul_vecMul, hl, smul_smul, pow_succ]
  funext j
  have := congrFun (hv (ord j.1)) (c, j.2)
  have hz : X (c, j.2) = 0 := by cases h : j.2 <;> simp [h0, h1]
  simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, hz, mul_zero] at this
  simpa [vecMul, dotProduct, kryC] using this

omit [Fintype C] [DecidableEq C] in
lemma Jop_smul (r : ℝ) (X : C × Bool → ℝ) : Jop (r • X) = r • Jop X := by
  funext ⟨c, b⟩; cases b <;> simp [Jop]

/-- **Doubled Krylov criterion.** If every doubled Krylov determinant is nonzero, an eigenvector
has no complex zeros and every eigenvector with the same eigenvalue is `μ X + ν J X`
(simple over `ℂ`). -/
lemma eigen_unique_of_hstarC {H : Matrix (C × Bool) (C × Bool) ℝ} (hS : H.IsSymm)
    (hJ : ∀ X, H *ᵥ Jop X = Jop (H *ᵥ X)) {ord : C → ℕ} (hv : ∀ c, (kryC H c ord).det ≠ 0)
    {X Y : C × Bool → ℝ} {E : ℝ} (hX0 : X ≠ 0) (hX : H *ᵥ X = E • X) (hY : H *ᵥ Y = E • Y) :
    (∀ c, X (c, false) ^ 2 + X (c, true) ^ 2 ≠ 0) ∧ ∃ μ ν : ℝ, Y = μ • X + ν • Jop X := by
  have hfull : ∀ c, X (c, false) ^ 2 + X (c, true) ^ 2 ≠ 0 := by
    intro c hc
    have h0 : X (c, false) = 0 := by nlinarith [sq_nonneg (X (c, false)), sq_nonneg (X (c, true))]
    have h1 : X (c, true) = 0 := by nlinarith [sq_nonneg (X (c, false)), sq_nonneg (X (c, true))]
    exact hv c (det_kryC_eq_zero hS hX0 hX h0 h1 ord)
  obtain ⟨c0⟩ : Nonempty C := by
    by_contra h; rw [not_nonempty_iff] at h
    exact hX0 (funext fun p => (h.false p.1).elim)
  refine ⟨hfull, ?_⟩
  have hs := hfull c0
  set μ := (X (c0, false) * Y (c0, false) + X (c0, true) * Y (c0, true)) /
    (X (c0, false) ^ 2 + X (c0, true) ^ 2)
  set ν := (X (c0, true) * Y (c0, false) - X (c0, false) * Y (c0, true)) /
    (X (c0, false) ^ 2 + X (c0, true) ^ 2)
  refine ⟨μ, ν, ?_⟩
  by_contra hne
  set Z := Y - (μ • X + ν • Jop X)
  have hZ0 : Z ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hJX : H *ᵥ Jop X = E • Jop X := by rw [hJ, hX, Jop_smul]
  have hZ : H *ᵥ Z = E • Z := by
    simp only [Z, mulVec_sub, mulVec_add, mulVec_smul, hY, hX, hJX, smul_sub, smul_add,
      smul_comm E]
  have hz0 : Z (c0, false) = 0 := by
    simp only [Z, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Jop_false, μ, ν]
    field_simp
    ring
  have hz1 : Z (c0, true) = 0 := by
    simp only [Z, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Jop_true, μ, ν]
    field_simp
    ring
  exact hv c0 (det_kryC_eq_zero hS hZ0 hZ hz0 hz1 ord)

omit [DecidableEq V] in
/-- **Corrected Farzanehpour–Tokatly Theorem 2 with flux, conditional form.** If all doubled
Krylov determinants of `H(v)` are nonzero and the occupations are rigid, every ground state of the
doubled Hamiltonian has a static force-balance form with only constant zero modes. -/
theorem kMat_definite_of_hstarC {A B : Matrix C C ℝ} (hA : A.IsSymm) (hB : Bᵀ = -B)
    {n : V → C → ℝ} (hR : Rigid n) {v : V → ℝ} {ord : C → ℕ}
    (hv : ∀ c, (kryC (hamN (dblH A B) (dblN n) v) c ord).det ≠ 0) {X : C × Bool → ℝ}
    (hX : IsGroundState (hamN (dblH A B) (dblN n) v) X) {w : V → ℝ}
    (hw : w ⬝ᵥ (kMat (dblH A B) (dblN n) X *ᵥ w) = 0) : ∃ k, ∀ i, w i = k := by
  have hH := dblH_isSymm hA hB
  have hS := hamN_isSymm hH (dblN n) v
  have hJ : ∀ Y, hamN (dblH A B) (dblN n) v *ᵥ Jop Y = Jop (hamN (dblH A B) (dblN n) v *ᵥ Y) := by
    intro Y; rw [hamN_dbl]; exact dblH_mulVec_Jop _ _ _
  have hE := isGroundState_eigen hS hX
  set E := qf (hamN (dblH A B) (dblN n) v) X / (X ⬝ᵥ X)
  set φ : C × Bool → ℝ := fun p => potW (dblN n) w p * X p
  rw [kMat_form_eigen hH (dblN n) v hE] at hw
  have hqφ : qf (hamN (dblH A B) (dblN n) v) φ = E * (φ ⬝ᵥ φ) := by linarith
  have hXX : 0 < X ⬝ᵥ X := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (X i)))
    (fun h => hX.1 (dotProduct_self_eq_zero.mp h.symm))
  -- `φ` is an eigenvector at the ground-state energy (or zero)
  have hφE : hamN (dblH A B) (dblN n) v *ᵥ φ = E • φ := by
    by_cases hφ0 : φ = 0
    · rw [hφ0, mulVec_zero, smul_zero]
    have hφgs : IsGroundState (hamN (dblH A B) (dblN n) v) φ := by
      refine ⟨hφ0, fun χ => ?_⟩
      have h1 := hX.2 χ
      have hEχ : E * (χ ⬝ᵥ χ) ≤ qf (hamN (dblH A B) (dblN n) v) χ := by
        have : qf (hamN (dblH A B) (dblN n) v) X / (X ⬝ᵥ X) * (χ ⬝ᵥ χ) ≤
            qf (hamN (dblH A B) (dblN n) v) χ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hXX]; linarith
        exact this
      rw [hqφ]
      have hφφ : 0 ≤ φ ⬝ᵥ φ := Finset.sum_nonneg (fun i _ => mul_self_nonneg (φ i))
      nlinarith
    have hEφ := isGroundState_eigen hS hφgs
    have hφφ : 0 < φ ⬝ᵥ φ := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (φ i)))
      (fun h => hφ0 (dotProduct_self_eq_zero.mp h.symm))
    have hEeq : qf (hamN (dblH A B) (dblN n) v) φ / (φ ⬝ᵥ φ) = E := by
      rw [hqφ]; field_simp
    rwa [hEeq] at hEφ
  obtain ⟨hfull, μ, ν, hμ⟩ := eigen_unique_of_hstarC hS hJ hv hX.1 hE hφE
  apply hR w μ
  intro c
  have e0 := congrFun hμ (c, false)
  have e1 := congrFun hμ (c, true)
  simp only [φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Jop_false, Jop_true] at e0 e1
  have hd : potW (dblN n) w (c, false) = ∑ i, w i * n i c := rfl
  have hd' : potW (dblN n) w (c, true) = ∑ i, w i * n i c := rfl
  rw [hd] at e0
  rw [hd'] at e1
  have key : (∑ i, w i * n i c) * (X (c, false) ^ 2 + X (c, true) ^ 2) =
      μ * (X (c, false) ^ 2 + X (c, true) ^ 2) := by
    have : (∑ i, w i * n i c) * X (c, false) * X (c, false) +
        (∑ i, w i * n i c) * X (c, true) * X (c, true) =
        (μ * X (c, false) + ν * X (c, true)) * X (c, false) +
        (μ * X (c, true) + ν * -X (c, false)) * X (c, true) := by rw [e0, e1]
    linear_combination this
  exact mul_right_cancel₀ (hfull c) key

/-- **Ground states with flux lie in `Ω`** (conditional on the doubled Krylov criterion). -/
theorem mem_omegaC_of_hstarC [Nonempty V] {A B : Matrix C C ℝ} (hA : A.IsSymm) (hB : Bᵀ = -B)
    {n : V → C → ℝ} (hR : Rigid n) {v : V → ℝ} {ord : C → ℕ}
    (hv : ∀ c, (kryC (hamN (dblH A B) (dblN n) v) c ord).det ≠ 0) {ψ : (C → ℝ) × (C → ℝ)}
    (hψ : IsGroundStateC A B n v ψ) : ψ ∈ omegaC A B n := by
  have hH := dblH_isSymm hA hB
  change dbl ψ ∈ omega (dblH A B) (dblN n)
  rw [dbl_eq_Jop]
  exact mem_omega_of_definite_pair hH (kMat_nonpos hH hψ) (kMat_nonpos hH (isGroundState_Jop hψ))
    (fun w hw => kMat_definite_of_hstarC hA hB hR hv hψ hw)

section generic

/-- The doubled Krylov polynomial of configuration `c` (a polynomial in the potential). -/
noncomputable def krylovPolyC (A B : Matrix C C ℝ) (n : V → C → ℝ) (c : C) (ord : C → ℕ) :
    MvPolynomial V ℝ :=
  (kryC (hamP (dblH A B) (dblN n)) c ord).det

omit [DecidableEq V] in
lemma eval_krylovPolyC (A B : Matrix C C ℝ) (n : V → C → ℝ) (c : C) (ord : C → ℕ) (v : V → ℝ) :
    MvPolynomial.eval v (krylovPolyC A B n c ord) =
      (kryC (hamN (dblH A B) (dblN n) v) c ord).det := by
  rw [krylovPolyC, RingHom.map_det, ← hamP_eval]
  congr 1
  ext i j
  have hp : ((hamP (dblH A B) (dblN n)).map (MvPolynomial.eval v)) ^ ord j.1 =
      ((hamP (dblH A B) (dblN n)) ^ ord j.1).map (MvPolynomial.eval v) := by
    rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
  simp only [kryC, RingHom.mapMatrix_apply, Matrix.map_apply, hp]

/-- **Generic ground states with flux** (conditional on nonzero doubled Krylov polynomials):
outside a closed, nowhere dense, null set of potentials, every ground state lies in `Ω`. -/
theorem generic_ground_mem_omegaC [Nonempty V] {A B : Matrix C C ℝ} (hA : A.IsSymm)
    (hB : Bᵀ = -B) {n : V → C → ℝ} (hR : Rigid n) {ord : C → ℕ}
    (hstar : ∀ c, krylovPolyC A B n c ord ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ v ∉ Z, ∀ ψ, IsGroundStateC A B n v ψ → ψ ∈ omegaC A B n := by
  set Q := ∏ c, krylovPolyC A B n c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hstar c
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun v hv ψ hψ => ?_⟩
  have hv' : ∀ c, (kryC (hamN (dblH A B) (dblN n) v) c ord).det ≠ 0 := by
    intro c hc
    apply hv
    change MvPolynomial.eval v Q = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [eval_krylovPolyC]; exact hc)
  exact mem_omegaC_of_hstarC hA hB hR hv' hψ

omit [Fintype C] [DecidableEq C] in
lemma dblH_zero_eq (M : Matrix C C ℝ) : dblH M 0 = blockDiagonal fun _ : Bool => M := by
  ext ⟨a, x⟩ ⟨b, y⟩
  cases x <;> cases y <;> simp [dblH, blockDiagonal_apply]

/-- Without flux the doubled Krylov determinant is the square of the real one. -/
lemma det_kryC_zero (M : Matrix C C ℝ) (c : C) (ord : C → ℕ) :
    (kryC (dblH M 0) c ord).det = (kry M c ord).det ^ 2 := by
  have h : kryC (dblH M 0) c ord = blockDiagonal fun _ : Bool => kry M c ord := by
    ext ⟨i, x⟩ ⟨j, y⟩
    simp only [kryC, dblH_zero_eq, ← blockDiagonal_pow, blockDiagonal_apply, kry]
    rfl
  rw [h, det_blockDiagonal, Fintype.prod_bool, sq]

omit [Fintype C] [DecidableEq C] in
lemma dblH_smul_split (A B : Matrix C C ℝ) (r : ℝ) :
    dblH A (r • B) = dblH A 0 + r • dblH 0 B := by
  ext ⟨a, x⟩ ⟨b, y⟩
  cases x <;> cases y <;> simp [dblH]

open Polynomial in
/-- The doubled Krylov determinant along the flux family `A + i r B`, at a fixed potential, is a
polynomial in the flux strength `r`. -/
lemma exists_poly_flux (H0 H1 : Matrix (C × Bool) (C × Bool) ℝ) (c : C) (ord : C → ℕ) :
    ∃ f : ℝ[X], ∀ r : ℝ, f.eval r = (kryC (H0 + r • H1) c ord).det := by
  set HP : Matrix (C × Bool) (C × Bool) ℝ[X] :=
    H0.map Polynomial.C + (Polynomial.X : ℝ[X]) • H1.map Polynomial.C
  refine ⟨(kryC HP c ord).det, fun r => ?_⟩
  have hev : HP.map (Polynomial.evalRingHom r) = H0 + r • H1 := by
    ext i j; simp [HP]; ring
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det, ← hev]
  congr 1
  ext i j
  have hp : (HP.map (Polynomial.evalRingHom r)) ^ ord j.1 =
      (HP ^ ord j.1).map (Polynomial.evalRingHom r) := by
    rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
  simp only [kryC, RingHom.mapMatrix_apply, Matrix.map_apply, hp]

omit [DecidableEq V] in
/-- **Generic flux strengths.** If the real Krylov polynomials of `A` are nonzero, then for all but
finitely many `r` the doubled Krylov polynomials of `A + i r B` are nonzero. -/
theorem hstarC_of_hstar {A : Matrix C C ℝ} (B : Matrix C C ℝ) {n : V → C → ℝ} {ord : C → ℕ}
    (hstar : ∀ c, krylovPoly A n c ord ≠ 0) :
    ∃ Λ : Set ℝ, Λ.Finite ∧ ∀ r ∉ Λ, ∀ c, krylovPolyC A (r • B) n c ord ≠ 0 := by
  -- a potential at which all real Krylov determinants are nonzero
  set Q := ∏ c, krylovPoly A n c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hstar c
  obtain ⟨v0, hv0⟩ : ∃ v0, MvPolynomial.eval v0 Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (MvPolynomial.funext fun v => by simpa using h v)
  have hv0c : ∀ c, (kry (hamN A n v0) c ord).det ≠ 0 := by
    intro c hc
    apply hv0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [eval_krylovPoly]; exact hc)
  -- along the flux family the determinant is a polynomial in `r`, nonzero at `r = 0`
  have hsplit : ∀ r : ℝ, hamN (dblH A (r • B)) (dblN n) v0 =
      dblH (hamN A n v0) 0 + r • dblH 0 B := by
    intro r; rw [hamN_dbl, dblH_smul_split]
  choose f hf using fun c => exists_poly_flux (dblH (hamN A n v0) 0) (dblH 0 B) c ord
  have hf0 : ∀ c, f c ≠ 0 := by
    intro c h
    have := hf c 0
    rw [h, Polynomial.eval_zero, zero_smul, add_zero, det_kryC_zero] at this
    exact pow_ne_zero 2 (hv0c c) this.symm
  refine ⟨⋃ c, {r | (f c).IsRoot r}, Set.finite_iUnion fun c =>
    Polynomial.finite_setOfPred_isRoot (hf0 c), fun r hr c hc => ?_⟩
  apply hr
  refine Set.mem_iUnion.mpr ⟨c, ?_⟩
  change (f c).eval r = 0
  rw [hf c, ← hsplit, ← eval_krylovPolyC, hc, map_zero]

end generic

section fermions

variable {M N : ℕ}

/-- **TDDFT with flux from the ground state, lattice fermions.** Spinless fermions on a connected
graph, symmetric hopping `A` of a common sign, any interaction, and any flux pattern `B`
(antisymmetric; the hopping is `A + i r B`). For all but finitely many flux strengths `r`, outside a
closed, nowhere dense, Lebesgue-null set of potentials, every (complex) ground state lies in `Ω`;
`td_existence_complex`, `td_uniqueness_complex` and `td_global_complex` then apply to it. -/
theorem generic_flux_ground_mem_omegaC [NeZero M] {G : SimpleGraph (Fin M)} [DecidableRel G.Adj]
    (hG : G.Connected) {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M)
    (Vint : Conf M N → ℝ) {B : Matrix (Conf M N) (Conf M N) ℝ} (hB : Bᵀ = -B) :
    ∃ Λ : Set ℝ, Λ.Finite ∧ ∀ r ∉ Λ,
      ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
        ∀ v ∉ Z, ∀ ψ, IsGroundStateC (H0Fw G t Vint) (r • B) occF v ψ →
          ψ ∈ omegaC (H0Fw G t Vint) (r • B) occF := by
  set ord : Conf M N → ℕ := fun j => (Fintype.equivFin (Conf M N) j : ℕ)
  obtain ⟨Λ, hΛ, hgen⟩ := hstarC_of_hstar (ord := ord) B
    (fun c => hstar_lattice_fermions_w hG hts c Vint)
  have hrB : ∀ r : ℝ, (r • B)ᵀ = -(r • B) := fun r => by
    rw [transpose_smul, hB, smul_neg]
  exact ⟨Λ, hΛ, fun r hr => generic_ground_mem_omegaC (H0Fw_isSymm G htsym Vint) (hrB r)
    (rigid_occF hN0 hNM) (hgen r hr)⟩

end fermions

end DFT
