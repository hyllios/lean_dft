/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import LatticeDFT.HK.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Lattice quantum dynamics: continuity and force balance

The Schrödinger equation `i ψ̇ = H(v(t)) ψ` with real `H(v) = H0 + diag(Σ_i v_i n_i)`, written for
`ψ = x + i y` as the real system `ẋ = H y`, `ẏ = -H x` (`schr`). With `N_i = diag(n_i)` and the
quadratic form `Q(A)(x, y) = xᵀ A x + yᵀ A y`:

* density `ρ_i = Q(N_i)` (`tdens`), current `j_i = 2 (yᵀ H0 N_i x - xᵀ H0 N_i y)` (`tcur`);
* `tdens_hasDerivAt` (continuity): along any trajectory `ρ̇_i = j_i`, whatever the potential;
* `tcur_hasDerivAt` (force balance): along any trajectory `j̇_i = q_i - Σ_j K_ij v_j`, with
  `q_i = 2 Q(H0 N_i H0 - H0 H0 N_i)` (`qsrc`) and `K_ij = -2 Q(H0 N_i N_j - N_j H0 N_i)` (`kfb`).

`K` and `q` depend only on the instantaneous state: the second time derivative of the density
determines the potential through `K(ψ) v = q(ψ) - ρ̈` (Farzanehpour & Tokatly, *Phys. Rev. B*
**86**, 125130 (2012)). With a fixed particle number, `K` annihilates constant potentials
(`kfb_sum_right`), its column sums vanish (`kfb_sum_left`), and `Σ_i q_i = 0` (`qsrc_sum`).
-/

namespace LatticeDFT

open Matrix

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V]

/-- The occupation operator `N_i = diag(n_i)`. -/
def Nmat (n : V → C → ℝ) (i : V) : Matrix C C ℝ := diagonal (n i)

/-- The quadratic form `Q(A)(x, y) = xᵀ A x + yᵀ A y` (the expectation value of `A` in `x + i y` for
symmetric `A`). -/
def Qf (A : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : ℝ :=
  ψ.1 ⬝ᵥ (A *ᵥ ψ.1) + ψ.2 ⬝ᵥ (A *ᵥ ψ.2)

/-- The Schrödinger vector field in real coordinates: `ẋ = H y`, `ẏ = -H x`. -/
noncomputable def schr (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) (ψ : (C → ℝ) × (C → ℝ)) :
    (C → ℝ) × (C → ℝ) :=
  (hamN H0 n v *ᵥ ψ.2, -(hamN H0 n v *ᵥ ψ.1))

/-- Site occupations of a state. -/
def tdens (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) : ℝ := Qf (Nmat n i) ψ

/-- The current into site `i` (the right-hand side of the continuity equation). -/
def tcur (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) : ℝ :=
  2 * (ψ.2 ⬝ᵥ ((H0 * Nmat n i) *ᵥ ψ.1) - ψ.1 ⬝ᵥ ((H0 * Nmat n i) *ᵥ ψ.2))

/-- The potential-independent part of the force balance. -/
def qsrc (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) (i : V) : ℝ :=
  2 * Qf (H0 * Nmat n i * H0 - H0 * H0 * Nmat n i) ψ

/-- The force-balance matrix `K(ψ)`. -/
def kfb (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Matrix V V ℝ :=
  fun i j => -2 * Qf (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i) ψ

section algebra

omit [DecidableEq C] in
lemma Qf_add (A B : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Qf (A + B) ψ = Qf A ψ + Qf B ψ := by
  simp only [Qf, add_mulVec, dotProduct_add]; ring

omit [DecidableEq C] in
lemma Qf_sub (A B : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Qf (A - B) ψ = Qf A ψ - Qf B ψ := by
  simp only [Qf, sub_mulVec, dotProduct_sub]; ring

omit [DecidableEq C] in
lemma Qf_smul (a : ℝ) (A : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) :
    Qf (a • A) ψ = a * Qf A ψ := by
  simp only [Qf, smul_mulVec, dotProduct_smul, smul_eq_mul]; ring

omit [DecidableEq C] in
lemma Qf_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) :
    Qf (∑ k ∈ s, A k) ψ = ∑ k ∈ s, Qf (A k) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Qf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Qf_add, ih]

omit [DecidableEq C] in
/-- `x ⬝ (A y) = y ⬝ (Aᵀ x)`. -/
lemma dot_mulVec_swap (A : Matrix C C ℝ) (x y : C → ℝ) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (Aᵀ *ᵥ x) := by
  rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

omit [DecidableEq C] in
/-- `(A u) ⬝ (M w) = u ⬝ ((Aᵀ M) w)`. -/
lemma dot_mulVec_left (A M : Matrix C C ℝ) (u w : C → ℝ) :
    (A *ᵥ u) ⬝ᵥ (M *ᵥ w) = u ⬝ᵥ ((Aᵀ * M) *ᵥ w) := by
  rw [← vecMul_transpose A u, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]

omit [DecidableEq C] in
lemma Qf_transpose (A : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Qf Aᵀ ψ = Qf A ψ := by
  simp only [Qf]
  rw [dot_mulVec_swap Aᵀ ψ.1, dot_mulVec_swap Aᵀ ψ.2, Matrix.transpose_transpose]

/-- The antisymmetric form `W(M)(x, y) = yᵀ M x - xᵀ M y`. -/
def Wf (M : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : ℝ :=
  ψ.2 ⬝ᵥ (M *ᵥ ψ.1) - ψ.1 ⬝ᵥ (M *ᵥ ψ.2)

omit [DecidableEq C] in
lemma Wf_add (A B : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Wf (A + B) ψ = Wf A ψ + Wf B ψ := by
  simp only [Wf, add_mulVec, dotProduct_add]; ring

omit [DecidableEq C] in
lemma Wf_sub (A B : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Wf (A - B) ψ = Wf A ψ - Wf B ψ := by
  simp only [Wf, sub_mulVec, dotProduct_sub]; ring

omit [DecidableEq C] in
lemma Wf_transpose (M : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Wf Mᵀ ψ = -Wf M ψ := by
  simp only [Wf]
  rw [dot_mulVec_swap Mᵀ ψ.2, dot_mulVec_swap Mᵀ ψ.1, Matrix.transpose_transpose]; ring

omit [Fintype C] in
lemma hamN_eq_sum (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) :
    hamN H0 n v = H0 + ∑ j, v j • Nmat n j := by
  rw [hamN]
  congr 1
  ext a b
  simp only [diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Nmat]
  split_ifs <;> simp

omit [Fintype C] [Fintype V] in
lemma Nmat_transpose (n : V → C → ℝ) (i : V) : (Nmat n i)ᵀ = Nmat n i := diagonal_transpose _

omit [Fintype V] in
lemma Nmat_comm (n : V → C → ℝ) (i j : V) : Nmat n i * Nmat n j = Nmat n j * Nmat n i := by
  simp only [Nmat, diagonal_mul_diagonal, mul_comm]

end algebra

section derivatives

variable {f g : ℝ → C → ℝ} {f' g' : C → ℝ} {t : ℝ}

omit [DecidableEq C] in
lemma hasDerivAt_dotProduct (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have h : ∀ c, HasDerivAt (fun s => f s c * g s c) (f' c * g t c + f t c * g' c) t :=
    fun c => (hasDerivAt_pi.1 hf c).mul (hasDerivAt_pi.1 hg c)
  have := HasDerivAt.sum (u := Finset.univ) (fun c _ => h c)
  simp only [dotProduct, ← Finset.sum_add_distrib]
  convert this using 1
  ext s; simp

omit [DecidableEq C] in
lemma hasDerivAt_mulVec (A : Matrix C C ℝ) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => A *ᵥ g s) (A *ᵥ g') t := by
  rw [hasDerivAt_pi]
  intro c
  simp only [mulVec, dotProduct]
  convert HasDerivAt.sum (u := Finset.univ) (fun d _ => (hasDerivAt_pi.1 hg d).const_mul (A c d))
    using 1
  ext s; simp

omit [DecidableEq C] in
lemma hasDerivAt_bil (A : Matrix C C ℝ) (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ (A *ᵥ g s)) (f' ⬝ᵥ (A *ᵥ g t) + f t ⬝ᵥ (A *ᵥ g')) t :=
  hasDerivAt_dotProduct hf (hasDerivAt_mulVec A hg)

omit [DecidableEq C] in
lemma hasDerivAt_fst' {ψ : ℝ → (C → ℝ) × (C → ℝ)} {ψ' : (C → ℝ) × (C → ℝ)}
    (h : HasDerivAt ψ ψ' t) : HasDerivAt (fun s => (ψ s).1) ψ'.1 t :=
  (hasFDerivAt_fst (𝕜 := ℝ) (E := C → ℝ) (F := C → ℝ) (p := ψ t)).comp_hasDerivAt t h

omit [DecidableEq C] in
lemma hasDerivAt_snd' {ψ : ℝ → (C → ℝ) × (C → ℝ)} {ψ' : (C → ℝ) × (C → ℝ)}
    (h : HasDerivAt ψ ψ' t) : HasDerivAt (fun s => (ψ s).2) ψ'.2 t :=
  (hasFDerivAt_snd (𝕜 := ℝ) (E := C → ℝ) (F := C → ℝ) (p := ψ t)).comp_hasDerivAt t h

end derivatives

omit [DecidableEq C] in
lemma Qf_zero (ψ : (C → ℝ) × (C → ℝ)) : Qf (0 : Matrix C C ℝ) ψ = 0 := by simp [Qf]

omit [DecidableEq C] in
lemma Qf_sub_transpose (A : Matrix C C ℝ) (ψ : (C → ℝ) × (C → ℝ)) : Qf (A - Aᵀ) ψ = 0 := by
  rw [Qf_sub, Qf_transpose, sub_self]

section gauge

variable (H0 : Matrix C C ℝ) {n : V → C → ℝ} {Ntot : ℝ} (hN : ∀ c, ∑ i, n i c = Ntot)
include hN

omit [Fintype C] in
lemma sum_Nmat : ∑ i, Nmat n i = Ntot • (1 : Matrix C C ℝ) := by
  ext a b
  simp only [Matrix.sum_apply, Nmat, diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs with h
  · subst h; simp [hN]
  · simp

/-- `K` annihilates constant potentials. -/
lemma kfb_sum_right (ψ : (C → ℝ) × (C → ℝ)) (i : V) : ∑ j, kfb H0 n ψ i j = 0 := by
  have hM : ∑ j, (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul, sum_Nmat hN]
    simp
  simp only [kfb, ← Finset.mul_sum, ← Qf_sum, hM, Qf_zero, mul_zero]

/-- The column sums of `K` vanish. -/
lemma kfb_sum_left (hH0 : H0.IsSymm) (ψ : (C → ℝ) × (C → ℝ)) (j : V) :
    ∑ i, kfb H0 n ψ i j = 0 := by
  have hM : ∑ i, (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i) =
      Ntot • (H0 * Nmat n j - (H0 * Nmat n j)ᵀ) := by
    rw [Matrix.transpose_mul, Nmat_transpose, hH0.eq, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_Nmat hN]
    simp [smul_sub]
  simp only [kfb, ← Finset.mul_sum, ← Qf_sum, hM, Qf_smul, Qf_sub_transpose, mul_zero]

/-- The source terms sum to zero. -/
lemma qsrc_sum (ψ : (C → ℝ) × (C → ℝ)) : ∑ i, qsrc H0 n ψ i = 0 := by
  have hM : ∑ i, (H0 * Nmat n i * H0 - H0 * H0 * Nmat n i) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, sum_Nmat hN]
    simp
  simp only [qsrc, ← Finset.mul_sum, ← Qf_sum, hM, Qf_zero, mul_zero]

end gauge

variable {H0 : Matrix C C ℝ} {n : V → C → ℝ}

section trajectory

variable (hH0 : H0.IsSymm) {ψ : ℝ → (C → ℝ) × (C → ℝ)} {v : V → ℝ} {t : ℝ}
  (hψ : HasDerivAt ψ (schr H0 n v (ψ t)) t)
include hH0 hψ

/-- Along a trajectory, `d/dt Q(A) = W(H A - A H)`. -/
lemma Qf_hasDerivAt (A : Matrix C C ℝ) :
    HasDerivAt (fun s => Qf A (ψ s)) (Wf (hamN H0 n v * A - A * hamN H0 n v) (ψ t)) t := by
  have h1 := hasDerivAt_bil A (hasDerivAt_fst' hψ) (hasDerivAt_fst' hψ)
  have h2 := hasDerivAt_bil A (hasDerivAt_snd' hψ) (hasDerivAt_snd' hψ)
  refine (h1.add h2).congr_deriv ?_
  have hH : (hamN H0 n v)ᵀ = hamN H0 n v := (hamN_isSymm hH0 n v).eq
  simp only [schr, Wf, mulVec_neg, neg_dotProduct, dotProduct_neg, sub_mulVec, dotProduct_sub]
  rw [dot_mulVec_left, hH, dot_mulVec_left, hH]
  simp only [← mulVec_mulVec]
  ring

/-- Along a trajectory, `d/dt W(M) = Q(M H - H M)`. -/
lemma Wf_hasDerivAt (M : Matrix C C ℝ) :
    HasDerivAt (fun s => Wf M (ψ s)) (Qf (M * hamN H0 n v - hamN H0 n v * M) (ψ t)) t := by
  have h1 := hasDerivAt_bil M (hasDerivAt_snd' hψ) (hasDerivAt_fst' hψ)
  have h2 := hasDerivAt_bil M (hasDerivAt_fst' hψ) (hasDerivAt_snd' hψ)
  refine (h1.sub h2).congr_deriv ?_
  have hH : (hamN H0 n v)ᵀ = hamN H0 n v := (hamN_isSymm hH0 n v).eq
  simp only [schr, Qf, mulVec_neg, neg_dotProduct, dotProduct_neg, sub_mulVec, dotProduct_sub]
  rw [dot_mulVec_left, hH, dot_mulVec_left, hH]
  simp only [← mulVec_mulVec]
  ring

/-- **Continuity equation.** Along any Schrödinger trajectory, `ρ̇_i = j_i`, whatever the potential.
-/
theorem tdens_hasDerivAt (i : V) :
    HasDerivAt (fun s => tdens n (ψ s) i) (tcur H0 n (ψ t) i) t := by
  refine (Qf_hasDerivAt hH0 hψ (Nmat n i)).congr_deriv ?_
  have hD : hamN H0 n v * Nmat n i - Nmat n i * hamN H0 n v = H0 * Nmat n i - (H0 * Nmat n i)ᵀ := by
    rw [Matrix.transpose_mul, Nmat_transpose, hH0.eq]
    simp only [hamN, add_mul, mul_add, Nmat, diagonal_mul_diagonal, mul_comm (n i _)]
    abel
  rw [hD, Wf_sub, Wf_transpose, tcur, Wf]
  ring

/-- **Force balance.** Along any Schrödinger trajectory, `j̇_i = q_i - Σ_j K_ij v_j`. -/
theorem tcur_hasDerivAt (i : V) :
    HasDerivAt (fun s => tcur H0 n (ψ s) i)
      (qsrc H0 n (ψ t) i - ∑ j, kfb H0 n (ψ t) i j * v j) t := by
  have h := (Wf_hasDerivAt hH0 hψ (H0 * Nmat n i)).const_mul 2
  have hexp : H0 * Nmat n i * hamN H0 n v - hamN H0 n v * (H0 * Nmat n i) =
      (H0 * Nmat n i * H0 - H0 * H0 * Nmat n i) +
        ∑ j, v j • (H0 * Nmat n i * Nmat n j - Nmat n j * H0 * Nmat n i) := by
    rw [hamN_eq_sum]
    simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      smul_sub, Finset.sum_sub_distrib, Matrix.mul_assoc]
    abel
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  · rw [hexp, Qf_add, Qf_sum]
    simp only [Qf_smul, qsrc, kfb, mul_add, Finset.mul_sum, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  · simp only [tcur, Wf]

end trajectory

end LatticeDFT
