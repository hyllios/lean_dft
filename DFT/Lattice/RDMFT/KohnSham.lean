/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.KohnSham.Aufbau
import DFT.Lattice.RDMFT.Stabilizer

/-!
# No Kohn–Sham scheme for RDMFT

A non-degenerate ground state of non-interacting fermions has an idempotent one-body reduced density
matrix, `γ² = γ`. So a `γ` that is not idempotent, as interacting ground states generically are, is
the `γ` of no gapped non-interacting ground state, whatever the one-body operator `h`. A Kohn–Sham
scheme for RDMFT is impossible with pure non-interacting states.

The proof goes through Pauli's principle rather than through explicit Slater-determinant algebra.
* `Γ` preserves positivity, so `γ ≥ 0` (`qf_gamma_nonneg`). The bound
  `⟨ψ, Γ(x xᵀ) ψ⟩ ≤ ‖x‖² ‖ψ‖²` gives `γ ≤ 1` (`qf_gamma_rank_one_le`). Both follow from the
  variational bound `qf_gamma_ge` in an eigenbasis.
* For the Slater determinant of orbitals `S` of an orthonormal basis `φ`, `⟨φ_c, γ φ_c⟩ = [c ∈ S]`.
  A positive semidefinite matrix with a zero diagonal entry kills that basis vector, so
  `γ φ_c = [c ∈ S] φ_c` (`rdm_slater_mulVec`). Hence `γ² = γ` (`rdm_slater_idem`).
* A gapped non-interacting ground state is that Slater determinant up to sign (`aufbau`,
  `unique_of_gap`), so its `γ` is idempotent (`rdm_idem_of_gap`).

Degenerate non-interacting ground states, and ensembles of them, are not covered. They are where
fractional occupations at the Fermi level enter.

* `gamma_transpose`, `rdm_isSymm`, `dot_rdm_mulVec`.
* `qf_gamma_nonneg`, `qf_gamma_rank_one_le`: `0 ≤ γ ≤ 1`.
* `rdm_slater_mulVec`, `rdm_slater_idem`.
* `rdm_idem_of_gap`: **non-interacting ⇒ idempotent**.
* `not_ks_of_not_idem`: **no Kohn–Sham system for a non-idempotent `γ`**.
* `gamma_rdm_mulVec_of_idem`: an idempotent `γ` stabilizes its state, `Γ(γ) ψ = N ψ`.
* `not_idem_of_trivialStab`: **a trivial one-body stabilizer forces a non-idempotent `γ`**.
* `not_rdmDetermines_of_idem`: a gapped interacting ground state that is a Slater determinant
  defeats RDMFT-HK.
-/

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-! ### Transposition and symmetry of `γ` -/

theorem gamma_transpose (h : Matrix (Fin M) (Fin M) ℝ) :
    (Γ h : Matrix (Conf M N) (Conf M N) ℝ)ᵀ = Γ hᵀ := by
  ext s s'
  rw [Matrix.transpose_apply, gamma_leibniz, gamma_leibniz]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))]
  apply Finset.sum_congr rfl; intro σ _
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl; intro j0 _
  have e1 : σ⁻¹ (σ j0) = j0 := by simp
  rw [e1, Matrix.transpose_apply]
  congr 1
  rw [← Equiv.prod_comp σ]
  apply Finset.prod_congr rfl; intro j _
  have e2 : σ⁻¹ (σ j) = j := by simp
  rw [e2]
  by_cases hj : j = j0
  · simp [hj]
  · have : σ j ≠ σ j0 := fun h' => hj (σ.injective h')
    simp [hj, this, eq_comm]

lemma qf_transpose {C : Type*} [Fintype C] (A : Matrix C C ℝ) (ψ : C → ℝ) :
    qf Aᵀ ψ = qf A ψ := by
  unfold qf
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]

lemma rdm_isSymm (ψ : Conf M N → ℝ) : (rdm ψ).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, rdm]
  rw [show Matrix.single j i (1 : ℝ) = (Matrix.single i j 1)ᵀ from
    (Matrix.transpose_single i j 1).symm, ← gamma_transpose, qf_transpose]

lemma rdm_smul (a : ℝ) (ψ : Conf M N → ℝ) : rdm (a • ψ) = a ^ 2 • rdm ψ := by
  ext i j; simp [rdm, qf_smul]

/-- `yᵀ γ x = ⟨ψ, Γ(y xᵀ) ψ⟩`. -/
lemma dot_rdm_mulVec (ψ : Conf M N → ℝ) (x y : Fin M → ℝ) :
    y ⬝ᵥ (rdm ψ *ᵥ x) = qf (Γ (vecMulVec y x)) ψ := by
  rw [qf_gamma]
  simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma vecMulVec_mulVec' (x y z : Fin M → ℝ) : vecMulVec x y *ᵥ z = (y ⬝ᵥ z) • x := by
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _; ring

lemma vecMulVec_self_isSymm (x : Fin M → ℝ) : (vecMulVec x x).IsSymm := by
  ext i j; simp [vecMulVec_apply, mul_comm]

lemma dot_vecMulVec_self (x z : Fin M → ℝ) : z ⬝ᵥ (vecMulVec x x *ᵥ z) = (x ⬝ᵥ z) ^ 2 := by
  rw [vecMulVec_mulVec', dotProduct_smul, smul_eq_mul, dotProduct_comm z x, sq]

/-! ### Orthonormal bases of `ℝ^M` -/

section Basis

variable {φ : Fin M → Fin M → ℝ} (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0)
include hON

lemma complete_of_orthonormal (i j : Fin M) :
    ∑ a, φ a i * φ a j = if i = j then 1 else 0 := by
  let Φ : Matrix (Fin M) (Fin M) ℝ := Matrix.of φ
  have h1 : Φ * Φᵀ = 1 := by
    ext a b; simp [Φ, Matrix.mul_apply, hON, Matrix.one_apply]
  have h2 : Φᵀ * Φ = 1 := mul_eq_one_comm.mp h1
  have := congrFun (congrFun h2 i) j
  simpa [Φ, Matrix.mul_apply, Matrix.one_apply] using this

lemma expand_orthonormal (v : Fin M → ℝ) : v = ∑ c, (φ c ⬝ᵥ v) • φ c := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
  calc v i = ∑ x, v x * (if x = i then 1 else 0) := by simp
    _ = ∑ x, v x * ∑ c, φ c x * φ c i := by simp_rw [complete_of_orthonormal hON]
    _ = ∑ c, (∑ x, φ c x * v x) * φ c i := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro x _
      ring

lemma parseval_orthonormal (x : Fin M → ℝ) : ∑ c, (φ c ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := by
  have e : ∀ c, (φ c ⬝ᵥ x) ^ 2 = ∑ i, ∑ j, x i * x j * (φ c i * φ c j) := by
    intro c
    simp only [dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [Finset.sum_congr rfl (fun c _ => e c), Finset.sum_comm]
  simp only [dotProduct]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, complete_of_orthonormal hON]
  simp

end Basis

/-! ### Pauli: `0 ≤ γ ≤ 1` -/

/-- `Γ` preserves positivity. -/
lemma qf_gamma_nonneg {A : Matrix (Fin M) (Fin M) ℝ} (hA : A.IsSymm)
    (hpos : ∀ y, 0 ≤ y ⬝ᵥ (A *ᵥ y)) (v : Conf M N → ℝ) : 0 ≤ qf (Γ A) v := by
  obtain ⟨ε, φ, hφ, hON⟩ := exists_eigenbasis A hA
  have hε : ∀ a, 0 ≤ ε a := by
    intro a
    have h1 := hpos (φ a)
    have hn : φ a ⬝ᵥ φ a = 1 := by simpa [dotProduct] using hON a a
    rwa [hφ a, dotProduct_smul, smul_eq_mul, hn, mul_one] at h1
  have := qf_gamma_ge A hφ hON (E := 0)
    (fun S => by unfold orbEnergy; exact Finset.sum_nonneg fun j _ => hε _) v
  simpa using this

/-- **Pauli principle**: `⟨ψ, Γ(x xᵀ) ψ⟩ ≤ ‖x‖² ‖ψ‖²`. -/
lemma qf_gamma_rank_one_le (x : Fin M → ℝ) (v : Conf M N → ℝ) :
    qf (Γ (vecMulVec x x)) v ≤ (x ⬝ᵥ x) * (v ⬝ᵥ v) := by
  set A := vecMulVec x x
  obtain ⟨ε, φ, hφ, hON⟩ := exists_eigenbasis A (vecMulVec_self_isSymm x)
  have hε : ∀ a, ε a = (φ a ⬝ᵥ x) ^ 2 := by
    intro a
    have hn : φ a ⬝ᵥ φ a = 1 := by simpa [dotProduct] using hON a a
    have h1 : φ a ⬝ᵥ (A *ᵥ φ a) = ε a := by rw [hφ a, dotProduct_smul, hn, smul_eq_mul, mul_one]
    rw [← h1, dot_vecMulVec_self, dotProduct_comm]
  have hle : ∀ S : Conf M N, -(x ⬝ᵥ x) ≤ orbEnergy (-ε) S := by
    intro S
    rw [orbEnergy_eq_sum, ← parseval_orthonormal hON x]
    simp only [Pi.neg_apply, Finset.sum_neg_distrib, neg_le_neg_iff, hε]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => sq_nonneg _)
  have hφ' : ∀ a, (-A) *ᵥ φ a = (-ε) a • φ a := by
    intro a; rw [Matrix.neg_mulVec, hφ a, Pi.neg_apply, neg_smul]
  have h := qf_gamma_ge (-A) hφ' hON hle v
  have hneg : qf (Γ (-A)) v = -qf (Γ A) v := by
    rw [show (Γ (-A) : Matrix (Conf M N) (Conf M N) ℝ) = -Γ A from map_neg gammaL A]
    simp [qf, Matrix.neg_mulVec]
  linarith

/-! ### Slater determinants have idempotent `γ` -/

/-- The natural orbitals of a Slater determinant are its orbitals, with occupations 0 and 1. -/
theorem rdm_slater_mulVec {φ : Fin M → Fin M → ℝ}
    (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) (S : Conf M N) (c : Fin M) :
    rdm (slaterSub φ S) *ᵥ φ c = (if c ∈ S.1 then (1 : ℝ) else 0) • φ c := by
  set ψ := slaterSub φ S
  set γ := rdm ψ
  have hnorm : ψ ⬝ᵥ ψ = 1 := by
    have := slater_orthonormal hON S S; simpa [dotProduct] using this
  have hγS : γ.IsSymm := rdm_isSymm ψ
  have hpos : ∀ y, 0 ≤ y ⬝ᵥ (γ *ᵥ y) := fun y => by
    rw [dot_rdm_mulVec]
    exact qf_gamma_nonneg (vecMulVec_self_isSymm y)
      (fun z => by rw [dot_vecMulVec_self]; exact sq_nonneg _) ψ
  have hpos' : ∀ y, 0 ≤ y ⬝ᵥ ((1 - γ) *ᵥ y) := fun y => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dot_rdm_mulVec]
    have := qf_gamma_rank_one_le y ψ
    rw [hnorm, mul_one] at this
    linarith
  have hnc : φ c ⬝ᵥ φ c = 1 := by simpa [dotProduct] using hON c c
  have hdiag : φ c ⬝ᵥ (γ *ᵥ φ c) = if c ∈ S.1 then 1 else 0 := by
    rw [dot_rdm_mulVec]
    have hP : ∀ a, vecMulVec (φ c) (φ c) *ᵥ φ a = (if a = c then (1 : ℝ) else 0) • φ a := by
      intro a
      rw [vecMulVec_mulVec']
      have : φ c ⬝ᵥ φ a = if c = a then 1 else 0 := by simpa [dotProduct] using hON c a
      rw [this]
      by_cases hac : a = c
      · subst hac; simp
      · simp [hac, Ne.symm hac]
    have hE := slaterSub_eigen _ hP S
    rw [qf, hE, dotProduct_smul, hnorm, smul_eq_mul, mul_one, orbEnergy_eq_sum]
    simp [Finset.sum_ite_eq']
  by_cases hc : c ∈ S.1
  · rw [ite_eq_left hc, one_smul]
    have h0 : (1 - γ) *ᵥ φ c = 0 := mulVec_eq_zero_of_psd (Matrix.isSymm_one.sub hγS).eq hpos'
      (by rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hdiag, ite_eq_left hc, hnc,
        sub_self])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0.symm
  · rw [ite_eq_right hc, zero_smul]
    exact mulVec_eq_zero_of_psd hγS.eq hpos (by rw [hdiag, ite_eq_right hc])

/-- **The `γ` of a Slater determinant is idempotent.** -/
theorem rdm_slater_idem {φ : Fin M → Fin M → ℝ}
    (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) (S : Conf M N) :
    rdm (slaterSub φ S) * rdm (slaterSub φ S) = rdm (slaterSub φ S) := by
  set γ := rdm (slaterSub φ S)
  have hv : ∀ v, (γ * γ) *ᵥ v = γ *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, expand_orthonormal hON v]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, γ, rdm_slater_mulVec hON S]
    apply Finset.sum_congr rfl; intro c _
    split_ifs <;> simp
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v

/-! ### Non-interacting ground states and the Kohn–Sham no-go -/

lemma le_of_isGroundState {H : Matrix (Conf M N) (Conf M N) ℝ} {ψ : Conf M N → ℝ}
    (hψ : IsGroundState H ψ) : N ≤ M := by
  by_contra hlt
  push Not at hlt
  apply hψ.1
  funext s
  exfalso
  have := Finset.card_le_univ s.1
  rw [s.2, Fintype.card_fin] at this
  omega

/-- **A gapped non-interacting ground state has an idempotent `γ`.** -/
theorem rdm_idem_of_gap {h : Matrix (Fin M) (Fin M) ℝ} (hS : h.IsSymm) {ψ : Conf M N → ℝ}
    (hψ : IsGroundState (Γ h) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (Γ h) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (Γ h) χ) :
    rdm ψ * rdm ψ = rdm ψ := by
  obtain ⟨ε, φ, S0, hφ, hON, -, hgs, -⟩ := aufbau h hS (le_of_isGroundState hψ)
  have hu := unique_of_gap (gamma_isSymm hS) hψ hN hg hgap hgs
  have hn1 : slaterSub φ S0 ⬝ᵥ slaterSub φ S0 = 1 := by
    have := slater_orthonormal hON S0 S0; simpa [dotProduct] using this
  set a := ψ ⬝ᵥ slaterSub φ S0
  have ha : a ^ 2 = 1 := by
    rw [hu, dotProduct_smul, smul_dotProduct, hN, smul_eq_mul, smul_eq_mul] at hn1
    nlinarith [hn1]
  have : rdm ψ = rdm (slaterSub φ S0) := by rw [hu, rdm_smul, ha, one_smul]
  rw [this]
  exact rdm_slater_idem hON S0

/-- **No Kohn–Sham system for RDMFT.** A `γ` that is not idempotent is the one-body reduced density
matrix of no gapped ground state of any non-interacting Hamiltonian `Γ(h)`. -/
theorem not_ks_of_not_idem {γ0 : Matrix (Fin M) (Fin M) ℝ} (hγ : γ0 * γ0 ≠ γ0) :
    ¬ ∃ h : Matrix (Fin M) (Fin M) ℝ, h.IsSymm ∧ ∃ ψ : Conf M N → ℝ, ∃ g : ℝ, 0 < g ∧
      IsGroundState (Γ h) ψ ∧ ψ ⬝ᵥ ψ = 1 ∧
      (∀ χ, ψ ⬝ᵥ χ = 0 → (qf (Γ h) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (Γ h) χ) ∧ rdm ψ = γ0 := by
  rintro ⟨h, hS, ψ, g, hg, hψ, hN, hgap, rfl⟩
  exact hγ (rdm_idem_of_gap hS hψ hN hg hgap)

/-! ### Idempotent `γ` forces a one-body stabilizer -/

lemma gamma_one : (Γ (1 : Matrix (Fin M) (Fin M) ℝ) : Matrix (Conf M N) (Conf M N) ℝ) =
    (N : ℝ) • 1 := by
  rw [← Matrix.diagonal_one, gamma_diagonal]
  ext s s'
  have hs : ∑ i, (1 : ℝ) * occF i s = N := by
    have := sum_tau s (fun _ => (1 : ℝ)); simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at this; simpa using this.symm
  by_cases h : s = s'
  · subst h; simpa using hs
  · simp [h]

/-- `tr γ = N ‖ψ‖²`. -/
lemma trace_rdm (ψ : Conf M N → ℝ) : ∑ i, rdm ψ i i = N * (ψ ⬝ᵥ ψ) := by
  have h := qf_gamma (1 : Matrix (Fin M) (Fin M) ℝ) ψ
  rw [gamma_one] at h
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h
  rw [← h]
  simp [qf, Matrix.smul_mulVec, dotProduct_smul]

/-- **An idempotent `γ` is a one-body stabilizer of its state**: `Γ(γ) ψ = N ψ`. In the language
of the generalized Pauli constraints, a Slater determinant is pinned to the Pauli boundary. -/
theorem gamma_rdm_mulVec_of_idem {ψ : Conf M N → ℝ} (hN : ψ ⬝ᵥ ψ = 1)
    (hidem : rdm ψ * rdm ψ = rdm ψ) :
    (Γ (rdm ψ) : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ = (N : ℝ) • ψ := by
  set γ := rdm ψ
  have hγS : γ.IsSymm := rdm_isSymm ψ
  -- `1 - γ` is positive semidefinite (Pauli), hence so is `Γ(1 - γ)`
  have hpos' : ∀ y, 0 ≤ y ⬝ᵥ ((1 - γ) *ᵥ y) := fun y => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dot_rdm_mulVec]
    have := qf_gamma_rank_one_le y ψ
    rw [hN, mul_one] at this
    linarith
  have hΓpos : ∀ v, 0 ≤ v ⬝ᵥ ((Γ (1 - γ) : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ v) :=
    fun v => qf_gamma_nonneg (Matrix.isSymm_one.sub hγS) hpos' v
  -- `⟨ψ, Γ(1 - γ) ψ⟩ = tr((1 - γ) γ) = tr γ - tr γ² = 0`
  have hsq : ∑ i, ∑ j, γ i j * γ i j = ∑ i, γ i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (congrFun hidem i) i
    rw [Matrix.mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγS.apply j i]
  have hzero : ψ ⬝ᵥ ((Γ (1 - γ) : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ) = 0 := by
    change qf (Γ (1 - γ)) ψ = 0
    rw [qf_gamma]
    simp only [Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hsq, sub_self]
  have h0 := mulVec_eq_zero_of_psd (gamma_isSymm (Matrix.isSymm_one.sub hγS)).eq hΓpos hzero
  rw [gamma_sub, gamma_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at h0
  exact h0.symm

/-- For `0 < N < M` an idempotent `γ` of a normalised state is not a multiple of the identity. -/
lemma rdm_ne_smul_one_of_idem (hN0 : 0 < N) (hNM : N < M) {ψ : Conf M N → ℝ}
    (hN : ψ ⬝ᵥ ψ = 1) (hidem : rdm ψ * rdm ψ = rdm ψ) (c : ℝ) : rdm ψ ≠ c • 1 := by
  intro hc
  have htr := trace_rdm ψ
  rw [hN, mul_one, hc] at htr
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htr
  have hcc : c * c = c := by
    have := congrFun (congrFun hidem ⟨0, by omega⟩) ⟨0, by omega⟩
    rw [hc] at this
    simpa [Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq'] using this
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rcases (show c = 0 ∨ c = 1 by
    rcases mul_eq_zero.mp (show c * (c - 1) = 0 by linarith) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)) with h | h
  · rw [h, mul_zero] at htr
    have : (N : ℝ) = 0 := htr.symm
    exact absurd (by exact_mod_cast this : N = 0) (by omega)
  · rw [h, mul_one] at htr
    have : (M : ℝ) = N := htr
    exact absurd (by exact_mod_cast this : M = N) (by omega)

/-- **A trivial one-body stabilizer forces a non-idempotent `γ`.** So wherever the RDMFT
Hohenberg–Kohn theorem holds through `rdmDetermines_of_trivialStab`, the ground state is not a
Slater determinant and has no Kohn–Sham system (`not_ks_of_not_idem`). -/
theorem not_idem_of_trivialStab (hN0 : 0 < N) (hNM : N < M) {ψ : Conf M N → ℝ}
    (hN : ψ ⬝ᵥ ψ = 1) (hstab : TrivialStab ψ) : rdm ψ * rdm ψ ≠ rdm ψ := by
  intro hidem
  obtain ⟨c, hc⟩ := hstab (rdm ψ) (rdm_isSymm ψ) N (gamma_rdm_mulVec_of_idem hN hidem)
  exact rdm_ne_smul_one_of_idem hN0 hNM hN hidem c hc

/-- **An interacting ground state with idempotent `γ` defeats RDMFT-HK.** If the gapped ground
state of `Γ(h) + W` is a Slater determinant, `γ` does not determine `h`. -/
theorem not_rdmDetermines_of_idem (hN0 : 0 < N) (hNM : N < M)
    {W : Matrix (Conf M N) (Conf M N) ℝ} (hW : W.IsSymm)
    {h : Matrix (Fin M) (Fin M) ℝ} (hh : h.IsSymm) {ψ : Conf M N → ℝ}
    (hψ : IsGroundState (hamR W h) ψ) (hN : ψ ⬝ᵥ ψ = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ χ, ψ ⬝ᵥ χ = 0 → (qf (hamR W h) ψ + g) * (χ ⬝ᵥ χ) ≤ qf (hamR W h) χ)
    (hidem : rdm ψ * rdm ψ = rdm ψ) : ¬ RDMDetermines W h :=
  not_rdmDetermines_of_stab hW hh hψ hN hg hgap (rdm_isSymm ψ)
    (rdm_ne_smul_one_of_idem hN0 hNM hN hidem) (gamma_rdm_mulVec_of_idem hN hidem)

/-! ### Idempotent `γ` means a Slater determinant -/

/-- **A normalised state with idempotent `γ` is a Slater determinant**, up to a scalar. -/
theorem exists_slater_of_idem {ψ : Conf M N → ℝ} (hN : ψ ⬝ᵥ ψ = 1)
    (hidem : rdm ψ * rdm ψ = rdm ψ) :
    ∃ (φ : Fin M → Fin M → ℝ) (S : Conf M N) (c : ℝ),
      (∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) ∧ ψ = c • slaterSub φ S := by
  classical
  set γ := rdm ψ
  obtain ⟨ε, φ, hφ, hON⟩ := exists_eigenbasis γ (rdm_isSymm ψ)
  have hnφ : ∀ a, φ a ⬝ᵥ φ a = 1 := fun a => by simpa [dotProduct] using hON a a
  -- the eigenvalues are 0 or 1
  have hε01 : ∀ a, ε a = 0 ∨ ε a = 1 := by
    intro a
    have h1 : (γ * γ) *ᵥ φ a = (ε a * ε a) • φ a := by
      rw [← Matrix.mulVec_mulVec, hφ, Matrix.mulVec_smul, hφ, smul_smul]
    rw [hidem, hφ] at h1
    have h2 := congrArg (φ a ⬝ᵥ ·) h1
    simp only [dotProduct_smul, hnφ, smul_eq_mul, mul_one] at h2
    have h3 : ε a * (ε a - 1) = 0 := by rw [mul_sub, mul_one, ← h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  -- `Σ ε = tr γ = N`
  have hsum : ∑ a, ε a = N := by
    have htr := trace_rdm ψ
    rw [hN, mul_one] at htr
    rw [← htr]
    have hεa : ∀ a, ε a = φ a ⬝ᵥ (γ *ᵥ φ a) := fun a => by
      rw [hφ, dotProduct_smul, hnφ, smul_eq_mul, mul_one]
    simp_rw [hεa]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    calc ∑ a, ∑ i, ∑ j, φ a i * (γ i j * φ a j)
        = ∑ i, ∑ j, γ i j * ∑ a, φ a i * φ a j := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
      _ = ∑ i, γ i i := by simp [complete_of_orthonormal hON]
  set S1 : Finset (Fin M) := Finset.univ.filter (fun a => ε a = 1)
  have hcardN : S1.card = N := by
    have hite : ∀ a, ε a = if ε a = 1 then 1 else 0 := fun a => by
      rcases hε01 a with h | h <;> simp [h]
    have : (S1.card : ℝ) = N := by
      rw [← hsum, Finset.sum_congr rfl (fun a _ => hite a), Finset.sum_boole]
    exact_mod_cast this
  -- the Slater basis of the natural orbitals
  set P := slaterMat (N := N) φ with hP
  have hPt : Pᵀ * P = 1 := slaterMat_orth hON
  have hPP : P * Pᵀ = 1 := mul_eq_one_comm.mp hPt
  have hGP : (Γ γ : Matrix (Conf M N) (Conf M N) ℝ) * P = P * diagonal (orbEnergy ε) := by
    ext s S
    have := congrFun (slaterSub_eigen γ hφ S) s
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [hP, slaterMat, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [this, mul_comm]
  set cv := Pᵀ *ᵥ ψ
  have hψP : ψ = P *ᵥ cv := by rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have hcS : ∀ S, orbEnergy ε S * cv S = N * cv S := by
    have h1 : (Γ γ : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ ψ = (N : ℝ) • ψ :=
      gamma_rdm_mulVec_of_idem hN hidem
    rw [hψP, Matrix.mulVec_mulVec, hGP, ← Matrix.mulVec_mulVec] at h1
    have h2 := congrArg (Pᵀ *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPt, Matrix.one_mul,
      Matrix.mulVec_smul, Matrix.one_mulVec] at h2
    intro S
    have := congrFun h2 S
    simpa [Matrix.mulVec_diagonal] using this
  -- only the configuration `S1` carries weight
  have hsupp : ∀ S : Conf M N, cv S ≠ 0 → S.1 = S1 := by
    intro S hS
    have hE : orbEnergy ε S = N := mul_right_cancel₀ hS (hcS S)
    rw [orbEnergy_eq_sum] at hE
    have hcardS : (S.1.card : ℝ) = N := by exact_mod_cast S.2
    have h0 : ∑ a ∈ S.1, (1 - ε a) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcardS, hE, sub_self]
    have hall : ∀ a ∈ S.1, ε a = 1 := fun a ha => by
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => by rcases hε01 b with h | h <;> simp [h])).mp h0 a ha
      linarith
    apply Finset.eq_of_subset_of_card_le
    · intro a ha; simp [S1, hall a ha]
    · rw [hcardN, S.2]
  have hψ0 : ψ ≠ 0 := by intro h; rw [h] at hN; simp at hN
  obtain ⟨S0, hS0⟩ : ∃ S, cv S ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hψ0
    rw [hψP, show cv = 0 from funext hc, Matrix.mulVec_zero]
  refine ⟨φ, S0, cv S0, hON, ?_⟩
  rw [hψP]
  funext s
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single S0]
  · simp only [hP, slaterMat]; ring
  · intro S _ hS
    have : cv S = 0 := by
      by_contra hc
      exact hS (Subtype.ext ((hsupp S hc).trans (hsupp S0 hS0).symm))
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

end

end DFT
