/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.GenericHK
import LatticeDFT.HK.SquareWall

/-!
# The force-balance matrix of lattice TDDFT at a ground state

In lattice TDDFT (Farzanehpour & Tokatly, *Phys. Rev. B* **86**, 125130 (2012)) the potential is
determined from the density by the force-balance equation `K(ψ) v = n̈ + q(ψ)`. Lattice TDDFT exists
locally (by Picard–Lindelöf) for initial states where `K(ψ)` has no zero eigenvalue besides the
constant potentials. For a real state `ψ` the quadratic form of `K` is
`wᵀ K(ψ) w = Σ_{c,c'} H0(c,c') ψ_c ψ_{c'} (d_c - d_{c'})²`, `d_c = Σ_i w_i n_i(c)` (`kMat`; diagonal
parts of `H0`, such as the interaction, drop out).

* `kMat_form_eigen`: for an eigenvector, `wᵀ K w = 2 (E |dψ|² - ⟨dψ| H |dψ⟩)` (an f-sum rule).
* `kMat_nonpos`: at a ground state `K(ψ)` is negative semidefinite.
* `kMat_mulVec_eq_zero`: if `d` is constant on the support of `ψ`, then `K(ψ) w = 0`.
* `kMat_degenerate_of_nonUV`: every ground state shared by two potentials that differ by more than a
  constant has a non-constant zero mode. With `hk_fails_square` this disproves Theorem 2 of
  Farzanehpour–Tokatly ("every ground state on a connected lattice is in the v-representability
  set"): `square_kMat_degenerate`. Their proof assumes that `v̂ ψ₀ = λ ψ₀` forces `v` constant,
  which fails when `ψ₀` has zero amplitudes.
* `kMat_definite_of_hstar`, `generic_td_vrep`: the corrected statement. For almost every static
  potential (outside a closed, nowhere dense, null set), every ground state of lattice fermions has
  `K(ψ)` negative definite modulo constants, so lattice TDDFT exists starting from it.
-/

namespace LatticeDFT

open Matrix MvPolynomial MeasureTheory

section

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- The density-coupled multiplication operator `d_c = Σ_i w_i n_i(c)`. -/
def potW (n : V → C → ℝ) (w : V → ℝ) : C → ℝ := fun c => ∑ i, w i * n i c

/-- The force-balance matrix `K(ψ)` of a real state. -/
def kMat (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : C → ℝ) : Matrix V V ℝ :=
  fun i j => ∑ c, ∑ c', H0 c c' * ψ c * ψ c' * (n i c - n i c') * (n j c - n j c')

omit [DecidableEq C] in
lemma kMat_mulVec (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : C → ℝ) (w : V → ℝ) (i : V) :
    (kMat H0 n ψ *ᵥ w) i =
      ∑ c, ∑ c', H0 c c' * ψ c * ψ c' * (n i c - n i c') * (potW n w c - potW n w c') := by
  simp only [mulVec, dotProduct, kMat, potW, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c' _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

omit [DecidableEq C] in
lemma kMat_form (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : C → ℝ) (w : V → ℝ) :
    w ⬝ᵥ (kMat H0 n ψ *ᵥ w) =
      ∑ c, ∑ c', H0 c c' * ψ c * ψ c' * (potW n w c - potW n w c') ^ 2 := by
  simp only [dotProduct, kMat_mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c' _
  have hd : potW n w c - potW n w c' = ∑ i, w i * (n i c - n i c') := by
    simp only [potW, ← Finset.sum_sub_distrib, mul_sub]
  calc ∑ i, w i * (H0 c c' * ψ c * ψ c' * (n i c - n i c') * (potW n w c - potW n w c'))
      = ∑ i, (H0 c c' * ψ c * ψ c' * (potW n w c - potW n w c')) * (w i * (n i c - n i c')) := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ = H0 c c' * ψ c * ψ c' * (potW n w c - potW n w c') * (potW n w c - potW n w c') := by
        rw [← Finset.mul_sum, ← hd]
    _ = _ := by ring

/-- Diagonal entries do not contribute: `K` is the same for `H0` and for `H(v)`. -/
lemma kMat_hamN (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (ψ : C → ℝ) :
    kMat (hamN H0 n v) n ψ = kMat H0 n ψ := by
  ext i j
  simp only [kMat, hamN, Matrix.add_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro c' _
  by_cases h : c = c'
  · subst h; simp
  · simp [h]

omit [DecidableEq C] in
/-- **f-sum rule.** For a symmetric `A` and an eigenvector `A ψ = E ψ`,
`Σ A_{cc'} ψ_c ψ_{c'} (d_c - d_{c'})² = 2 (E |dψ|² - ⟨dψ, A dψ⟩)`. -/
lemma sum_sq_eigen {A : Matrix C C ℝ} (hA : A.IsSymm) {ψ : C → ℝ} {E : ℝ}
    (hE : A *ᵥ ψ = E • ψ) (d : C → ℝ) :
    ∑ c, ∑ c', A c c' * ψ c * ψ c' * (d c - d c') ^ 2 =
      2 * (E * ((fun c => d c * ψ c) ⬝ᵥ (fun c => d c * ψ c)) -
        qf A (fun c => d c * ψ c)) := by
  have hrow : ∀ c, ∑ c', A c c' * ψ c' = E * ψ c := by
    intro c; have := congrFun hE c; simpa [mulVec, dotProduct] using this
  have hcol : ∀ c', ∑ c, A c c' * ψ c = E * ψ c' := by
    intro c'; rw [← hrow c']
    apply Finset.sum_congr rfl; intro c _
    rw [← hA.apply c c']
  have e1 : ∑ c, ∑ c', A c c' * ψ c * ψ c' * d c ^ 2 = ∑ c, E * (d c * ψ c) ^ 2 := by
    apply Finset.sum_congr rfl; intro c _
    have := hrow c
    calc ∑ c', A c c' * ψ c * ψ c' * d c ^ 2 = (ψ c * d c ^ 2) * ∑ c', A c c' * ψ c' := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c' _; ring
      _ = _ := by rw [this]; ring
  have e2 : ∑ c, ∑ c', A c c' * ψ c * ψ c' * d c' ^ 2 = ∑ c', E * (d c' * ψ c') ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c' _
    have := hcol c'
    calc ∑ c, A c c' * ψ c * ψ c' * d c' ^ 2 = (ψ c' * d c' ^ 2) * ∑ c, A c c' * ψ c := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
      _ = _ := by rw [this]; ring
  have e3 : ∑ c, ∑ c', A c c' * ψ c * ψ c' * (d c * d c') = qf A (fun c => d c * ψ c) := by
    simp only [qf, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro c' _
    ring
  have hexp : ∀ c c', A c c' * ψ c * ψ c' * (d c - d c') ^ 2 =
      A c c' * ψ c * ψ c' * d c ^ 2 + A c c' * ψ c * ψ c' * d c' ^ 2 -
        2 * (A c c' * ψ c * ψ c' * (d c * d c')) := by intro c c'; ring
  simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e1, e2, e3]
  simp only [dotProduct, ← Finset.mul_sum, sq]
  ring

lemma kMat_form_eigen {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (v : V → ℝ)
    {ψ : C → ℝ} {E : ℝ} (hE : hamN H0 n v *ᵥ ψ = E • ψ) (w : V → ℝ) :
    w ⬝ᵥ (kMat H0 n ψ *ᵥ w) =
      2 * (E * ((fun c => potW n w c * ψ c) ⬝ᵥ (fun c => potW n w c * ψ c)) -
        qf (hamN H0 n v) (fun c => potW n w c * ψ c)) := by
  rw [← kMat_hamN H0 n v, kMat_form]
  exact sum_sq_eigen (hamN_isSymm hH0 n v) hE _

/-- **At a ground state the force-balance matrix is negative semidefinite.** -/
theorem kMat_nonpos {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {v : V → ℝ}
    {ψ : C → ℝ} (hψ : IsGroundState (hamN H0 n v) ψ) (w : V → ℝ) :
    w ⬝ᵥ (kMat H0 n ψ *ᵥ w) ≤ 0 := by
  have hE := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
  rw [kMat_form_eigen hH0 n v hE]
  set φ : C → ℝ := fun c => potW n w c * ψ c
  have hψψ : 0 < ψ ⬝ᵥ ψ := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (ψ i)))
    (fun h => hψ.1 (dotProduct_self_eq_zero.mp h.symm))
  have h2 := hψ.2 φ
  have : qf (hamN H0 n v) ψ / (ψ ⬝ᵥ ψ) * (φ ⬝ᵥ φ) ≤ qf (hamN H0 n v) φ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hψψ]; linarith
  linarith

omit [DecidableEq C] in
/-- If `d` is constant on the support of `ψ`, then `w` is a zero mode of `K(ψ)`. -/
theorem kMat_mulVec_eq_zero (H0 : Matrix C C ℝ) (n : V → C → ℝ) {ψ : C → ℝ} {w : V → ℝ} {κ : ℝ}
    (hd : ∀ c, ψ c ≠ 0 → potW n w c = κ) : kMat H0 n ψ *ᵥ w = 0 := by
  funext i
  rw [kMat_mulVec, Pi.zero_apply]
  apply Finset.sum_eq_zero; intro c _
  apply Finset.sum_eq_zero; intro c' _
  by_cases hc : ψ c = 0
  · simp [hc]
  by_cases hc' : ψ c' = 0
  · simp [hc']
  rw [hd c hc, hd c' hc', sub_self, mul_zero]

/-- A ground state shared by `v` and `v'` has `v - v'` as a zero mode of the force-balance
matrix. -/
theorem kMat_shared {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} {v v' : V → ℝ}
    {ψ : C → ℝ} (hψ : IsGroundState (hamN H0 n v) ψ) (hψ' : IsGroundState (hamN H0 n v') ψ) :
    kMat H0 n ψ *ᵥ (fun i => v i - v' i) = 0 := by
  have hE := isGroundState_eigen (hamN_isSymm hH0 n v) hψ
  have hE' := isGroundState_eigen (hamN_isSymm hH0 n v') hψ'
  set E := qf (hamN H0 n v) ψ / (ψ ⬝ᵥ ψ)
  set E' := qf (hamN H0 n v') ψ / (ψ ⬝ᵥ ψ)
  refine kMat_mulVec_eq_zero H0 n (κ := E - E') ?_
  intro c hc
  have e1 := congrFun hE c
  have e2 := congrFun hE' c
  rw [hamN_mulVec_apply] at e1 e2
  simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
  have : (∑ i, (v i - v' i) * n i c) * ψ c = (E - E') * ψ c := by
    simp only [sub_mul, Finset.sum_sub_distrib]; linarith
  exact mul_right_cancel₀ hc this

/-- **A ground state shared by two genuinely different potentials has a non-constant zero mode of
the force-balance matrix.** -/
theorem kMat_degenerate_of_nonUV {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    {v : V → ℝ} (h : NonUV H0 n v) :
    ∃ ψ, IsGroundState (hamN H0 n v) ψ ∧ ∃ w : V → ℝ, (¬ ∃ k, ∀ i, w i = k) ∧
      kMat H0 n ψ *ᵥ w = 0 := by
  obtain ⟨ψ, v', hψ, hψ', hne⟩ := h
  exact ⟨ψ, hψ, _, hne, kMat_shared hH0 hψ hψ'⟩

/-- If (H*) holds at `v` (every Krylov determinant nonzero), eigenvectors have full support and the
eigenvalues are simple. -/
lemma eigen_unique_of_hstar {A : Matrix C C ℝ} (hA : A.IsSymm) {ord : C → ℕ}
    (hv : ∀ c, (kry A c ord).det ≠ 0) {ψ φ : C → ℝ} {E : ℝ} (hψ0 : ψ ≠ 0)
    (hψ : A *ᵥ ψ = E • ψ) (hφ : A *ᵥ φ = E • φ) :
    (∀ c, ψ c ≠ 0) ∧ ∃ μ : ℝ, φ = μ • ψ := by
  have hfull : ∀ c, ψ c ≠ 0 := fun c hc => hv c (det_kry_eq_zero hA hψ0 hψ hc ord)
  obtain ⟨c0⟩ : Nonempty C := by
    by_contra h; rw [not_nonempty_iff] at h; exact hψ0 (funext fun c => (h.false c).elim)
  refine ⟨hfull, φ c0 / ψ c0, ?_⟩
  by_contra hne
  set χ := φ - (φ c0 / ψ c0) • ψ
  have hχ0 : χ ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hχ : A *ᵥ χ = E • χ := by
    simp only [χ, mulVec_sub, mulVec_smul, hψ, hφ, smul_sub, smul_comm E]
  have hχc : χ c0 = 0 := by
    simp only [χ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hfull c0]; ring
  exact hv c0 (det_kry_eq_zero hA hχ0 hχ hχc ord)

/-- **Corrected Farzanehpour–Tokatly Theorem 2, conditional form.** If (H*) holds at `v` and the
occupations are rigid, every ground state of `H(v)` has `K(ψ)` negative definite modulo constants.
-/
theorem kMat_definite_of_hstar {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    (hR : Rigid n) {v : V → ℝ} {ord : C → ℕ}
    (hv : ∀ c, eval v (krylovPoly H0 n c ord) ≠ 0) {ψ : C → ℝ}
    (hψ : IsGroundState (hamN H0 n v) ψ) {w : V → ℝ} (hw : w ⬝ᵥ (kMat H0 n ψ *ᵥ w) = 0) :
    ∃ k, ∀ i, w i = k := by
  have hS := hamN_isSymm hH0 n v
  have hv' : ∀ c, (kry (hamN H0 n v) c ord).det ≠ 0 := by
    intro c; rw [← eval_krylovPoly]; exact hv c
  have hE := isGroundState_eigen hS hψ
  set E := qf (hamN H0 n v) ψ / (ψ ⬝ᵥ ψ)
  set φ : C → ℝ := fun c => potW n w c * ψ c
  -- `φ` attains the ground-state energy
  rw [kMat_form_eigen hH0 n v hE] at hw
  have hqφ : qf (hamN H0 n v) φ = E * (φ ⬝ᵥ φ) := by linarith
  have hψψ : 0 < ψ ⬝ᵥ ψ := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (ψ i)))
    (fun h => hψ.1 (dotProduct_self_eq_zero.mp h.symm))
  have hfull : ∀ c, ψ c ≠ 0 := (eigen_unique_of_hstar hS hv' hψ.1 hE hE).1
  -- `φ = μ ψ`
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, φ = μ • ψ := by
    by_cases hφ0 : φ = 0
    · exact ⟨0, by rw [hφ0, zero_smul]⟩
    have hφgs : IsGroundState (hamN H0 n v) φ := by
      refine ⟨hφ0, fun χ => ?_⟩
      have h1 := hψ.2 χ
      have hEχ : E * (χ ⬝ᵥ χ) ≤ qf (hamN H0 n v) χ := by
        have : qf (hamN H0 n v) ψ / (ψ ⬝ᵥ ψ) * (χ ⬝ᵥ χ) ≤ qf (hamN H0 n v) χ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hψψ]; linarith
        exact this
      rw [hqφ]
      have hφφ : 0 ≤ φ ⬝ᵥ φ := Finset.sum_nonneg (fun i _ => mul_self_nonneg (φ i))
      nlinarith
    have hEφ := isGroundState_eigen hS hφgs
    have hφφ : 0 < φ ⬝ᵥ φ := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (φ i)))
      (fun h => hφ0 (dotProduct_self_eq_zero.mp h.symm))
    have hEeq : qf (hamN H0 n v) φ / (φ ⬝ᵥ φ) = E := by
      rw [hqφ]; field_simp
    rw [hEeq] at hEφ
    exact (eigen_unique_of_hstar hS hv' hψ.1 hE hEφ).2
  -- `d` is constant, so rigidity applies
  apply hR w μ
  intro c
  have := congrFun hμ c
  simp only [φ, potW, Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ (hfull c) this

end

/-- **Counterexample to Farzanehpour–Tokatly Theorem 2.** Two fermions on the square at the
potential `(3/4, -3/4, -3/4, 3/4)`: the (non-degenerate) ground state `(0, 2, 1, 4, 2, 0)` has a
non-constant zero mode of the force-balance matrix, so it lies outside the v-representability set
although the lattice is connected. -/
theorem square_kMat_degenerate :
    IsGroundState (hamN H0sq occ4 ![3/4, -3/4, -3/4, 3/4]) ![0, 2, 1, 4, 2, 0] ∧
      ∃ w : Fin 4 → ℝ, (¬ ∃ k, ∀ i, w i = k) ∧ kMat H0sq occ4 ![0, 2, 1, 4, 2, 0] *ᵥ w = 0 := by
  obtain ⟨h0, h1, hne⟩ := hk_fails_square
  exact ⟨h0, _, hne, kMat_shared H0sq_isSymm h0 h1⟩

section

variable {M N : ℕ}

/-- **Lattice TDDFT exists from the ground state for almost every static potential.** Spinless
lattice fermions on a connected graph, symmetric hopping of a common sign, any interaction: outside
a closed, nowhere dense, Lebesgue-null set of static potentials `v`, every ground state of `H(v)`
has its force-balance matrix negative definite modulo constants (so it lies in the
v-representability set of Farzanehpour–Tokatly, and their local existence theorem applies). -/
theorem generic_td_vrep {G : SimpleGraph (Fin M)} [DecidableRel G.Adj] (hG : G.Connected)
    {t : Fin M → Fin M → ℝ} (htsym : ∀ a b, t a b = t b a) {s : ℝ}
    (hts : ∀ a b, G.Adj a b → 0 < s * t a b) (hN0 : 0 < N) (hNM : N < M) (Vint : Conf M N → ℝ) :
    ∃ Z : Set (Fin M → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      ∀ v ∉ Z, ∀ ψ, IsGroundState (hamN (H0Fw G t Vint) occF v) ψ →
        ∀ w : Fin M → ℝ, w ⬝ᵥ (kMat (H0Fw G t Vint) occF ψ *ᵥ w) = 0 → ∃ k, ∀ i, w i = k := by
  set ord : Conf M N → ℕ := fun j => (Fintype.equivFin (Conf M N) j : ℕ)
  set Q := ∏ c, krylovPoly (H0Fw G t Vint) occF c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun c _ => hstar_lattice_fermions_w hG hts c Vint)
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun v hv ψ hψ w hw => ?_⟩
  have hv' : ∀ c, eval v (krylovPoly (H0Fw G t Vint) occF c ord) ≠ 0 := by
    intro c hc
    apply hv
    change eval v Q = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) hc
  exact kMat_definite_of_hstar (H0Fw_isSymm G htsym Vint) (rigid_occF hN0 hNM) hv' hψ hw

end

end LatticeDFT
