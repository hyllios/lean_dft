/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.RDM

/-!
# The two-body reduced density matrix

`D_{ij,kl} = ⟨Ψ, c_i† c_j† c_l c_k Ψ⟩` (`rdm2`) is antisymmetric in each pair of indices and
Hermitian. For an `N`-particle state it contracts to the one-body matrix,
`Σ_k D_{ik,jk} = (N - 1) γ_ij`, and has trace `N (N - 1)`. It satisfies the three classical
necessary conditions of N-representability (Garrod–Percus): the matrices `P = D`,
`Q_{ij,kl} = ⟨c_i c_j c_l† c_k†⟩` and `G_{ij,kl} = ⟨c_i† c_j c_l† c_k⟩` are positive semidefinite,
and `Q`, `G` are explicit affine functions of `D` and `γ` (`qMat`, `gMat`).

## Main results

* `numTot_mul_ann`, `numTotOp_annOp`: `N̂ c_j = c_j (N̂ - 1)`.
* `rdm2_swap_left`, `rdm2_swap_right`, `rdm2_isHermitian`: antisymmetry and Hermiticity.
* `sum_rdm2_contract`, `sum_rdm2_trace`: `Σ_k D_{ik,jk} = (N - 1) γ_ij` and `Σ_ij D_{ij,ij} = N (N - 1)`.
* `rdm2_posSemidef` (**P**), `qMat_posSemidef` (**Q**), `gMat_posSemidef` (**G**), with
  `qMat_eq_inner` and `gMat_eq_inner` identifying the formulas with the expectation values.
* The same for ensembles: `rdm2Ens_isHermitian`, `sum_rdm2Ens_contract`, `sum_rdm2Ens_trace`,
  `rdm2Ens_posSemidef`, `qMatEns_posSemidef`, `gMatEns_posSemidef`.
-/

namespace QM.ManyBody

open Matrix Finset
open scoped ComplexOrder

variable {M : ℕ}

/-! ### The number operator and annihilation -/

/-- `n̂_i c_j = c_j n̂_i - δ_ij c_j`. -/
lemma num_mul_ann (i j : Fin M) :
    num i * ann j = ann j * num i - (if i = j then ann j else 0) := by
  have hA : ann i * ann j = -(ann j * ann i) := eq_neg_of_add_eq_zero_left (ann_mul_ann_add i j)
  have hB : cre i * ann j = (if j = i then (1 : FockOp M) else 0) - ann j * cre i :=
    eq_sub_of_add_eq' (ann_mul_cre_add j i)
  unfold num
  rw [mul_assoc, hA, mul_neg, ← mul_assoc, hB]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
    noncomm_ring
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
    noncomm_ring

/-- `N̂ c_j = c_j N̂ - c_j`. -/
lemma numTot_mul_ann (j : Fin M) : numTot * ann j = ann j * numTot - ann j := by
  rw [numTot, Finset.sum_mul, Finset.mul_sum]
  simp_rw [num_mul_ann, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq']
  simp

/-- `N̂ (c_j Ψ) = c_j (N̂ Ψ) - c_j Ψ`. -/
lemma numTotOp_annOp (j : Fin M) (Ψ : Fock M) :
    numTotOp (annOp j Ψ) = annOp j (numTotOp Ψ) - annOp j Ψ := by
  have h := congrArg (fun A : FockOp M => toFockCLM A Ψ) (numTot_mul_ann j)
  simpa [numTotOp, annOp, map_sub, map_mul] using h

/-- `c_j` lowers the particle number by one. -/
lemma numTotOp_annOp_of {N : ℕ} {Ψ : Fock M} (hΨ : numTotOp Ψ = (N : ℂ) • Ψ) (j : Fin M) :
    numTotOp (annOp j Ψ) = ((N : ℂ) - 1) • annOp j Ψ := by
  rw [numTotOp_annOp, hΨ, map_smul, sub_smul, one_smul]

/-! ### Symmetries -/

lemma creOp_creOp (i j : Fin M) (v : Fock M) : creOp j (creOp i v) = -creOp i (creOp j v) := by
  have h := congrArg (fun A : Fock M →L[ℂ] Fock M => A v) (creOp_mul_creOp_add i j)
  simp only [_root_.add_apply, _root_.mul_apply_eq_comp, _root_.zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h

lemma annOp_annOp (i j : Fin M) (v : Fock M) : annOp j (annOp i v) = -annOp i (annOp j v) := by
  have h := congrArg (fun A : Fock M →L[ℂ] Fock M => A v) (annOp_mul_annOp_add i j)
  simp only [_root_.add_apply, _root_.mul_apply_eq_comp, _root_.zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h

/-- `c_a c_b† v = δ_ab v - c_b† c_a v`. -/
lemma annOp_creOp (a b : Fin M) (v : Fock M) :
    annOp a (creOp b v) = (if a = b then v else 0) - creOp b (annOp a v) := by
  have h := congrArg (fun A : Fock M →L[ℂ] Fock M => A v) (annOp_mul_creOp_add a b)
  simp only [_root_.add_apply, _root_.mul_apply_eq_comp] at h
  rw [eq_sub_iff_add_eq, h]
  split_ifs <;> simp

/-- `D_{ji,kl} = -D_{ij,kl}`. -/
theorem rdm2_swap_left (Ψ : Fock M) (i j : Fin M) (q : Fin M × Fin M) :
    rdm2 Ψ (j, i) q = -rdm2 Ψ (i, j) q := by
  simp only [rdm2]
  rw [creOp_creOp, inner_neg_right]

/-- `D_{ij,lk} = -D_{ij,kl}`. -/
theorem rdm2_swap_right (Ψ : Fock M) (p : Fin M × Fin M) (k l : Fin M) :
    rdm2 Ψ p (l, k) = -rdm2 Ψ p (k, l) := by
  simp only [rdm2]
  rw [annOp_annOp, map_neg, map_neg, inner_neg_right]

/-- `D_{ij,kl} = ⟨c_j c_i Ψ, c_l c_k Ψ⟩`. -/
lemma rdm2_eq_inner (Ψ : Fock M) (p q : Fin M × Fin M) :
    rdm2 Ψ p q = inner ℂ (annOp p.2 (annOp p.1 Ψ)) (annOp q.2 (annOp q.1 Ψ)) := by
  rw [rdm2, inner_creOp, inner_creOp]

/-- `D` is Hermitian: `D_{kl,ij} = conj D_{ij,kl}`. -/
theorem rdm2_isHermitian (Ψ : Fock M) : (rdm2 Ψ).IsHermitian := by
  ext p q
  simp only [conjTranspose_apply, rdm2_eq_inner]
  rw [← inner_conj_symm]
  simp

/-! ### Contraction and trace -/

/-- **`Σ_k D_{ik,jk} = (N - 1) γ_ij`** for an `N`-particle state. -/
theorem sum_rdm2_contract {N : ℕ} {Ψ : Fock M} (hΨ : numTotOp Ψ = (N : ℂ) • Ψ) (i j : Fin M) :
    ∑ k, rdm2 Ψ (i, k) (j, k) = ((N : ℂ) - 1) * rdm1 Ψ i j := by
  have h : ∑ k, rdm2 Ψ (i, k) (j, k) = inner ℂ Ψ (creOp i (numTotOp (annOp j Ψ))) := by
    rw [numTotOp_eq_sum]
    simp [rdm2, inner_sum, _root_.sum_apply]
  rw [h, numTotOp_annOp_of hΨ, map_smul, inner_smul_right, rdm1]

/-- **`Σ_ij D_{ij,ij} = N (N - 1)`** for an `N`-particle state. -/
theorem sum_rdm2_trace {N : ℕ} {Ψ : Fock M} (hΨ : IsNState N Ψ) :
    ∑ i, ∑ j, rdm2 Ψ (i, j) (i, j) = (N : ℂ) * ((N : ℂ) - 1) := by
  simp_rw [sum_rdm2_contract hΨ.2, ← Finset.mul_sum]
  rw [show ∑ i, rdm1 Ψ i i = (rdm1 Ψ).trace from rfl, trace_rdm1 hΨ]
  ring

/-! ### The P condition -/

/-- `Σ_pq x̄_p D_pq x_q = ‖Σ_q x_q c_l c_k Ψ‖²` (with `q = (k, l)`). -/
theorem quad_rdm2 (Ψ : Fock M) (x : Fin M × Fin M → ℂ) :
    star x ⬝ᵥ (rdm2 Ψ *ᵥ x) =
      inner ℂ (∑ p, x p • annOp p.2 (annOp p.1 Ψ)) (∑ q, x q • annOp q.2 (annOp q.1 Ψ)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, rdm2_eq_inner, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [RCLike.star_def]
  ring

lemma inner_self_nonneg' (v : Fock M) : 0 ≤ inner ℂ v v := by
  rw [inner_self_eq_norm_sq_to_K]
  simp

/-- **P condition**: `D ≥ 0`. -/
theorem rdm2_posSemidef (Ψ : Fock M) : (rdm2 Ψ).PosSemidef :=
  posSemidef_iff_dotProduct_mulVec.mpr
    ⟨rdm2_isHermitian Ψ, fun x => by rw [quad_rdm2]; exact inner_self_nonneg' _⟩

/-! ### The G condition -/

/-- The Kronecker delta. -/
def kd (a b : Fin M) : ℂ := if a = b then 1 else 0

/-- `G_{ij,kl} = δ_jl γ_ik - D_{il,kj}`. -/
def gMat (γ : Matrix (Fin M) (Fin M) ℂ) (D : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ) :
    Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ :=
  fun p q => kd p.2 q.2 * γ p.1 q.1 - D (p.1, q.2) (q.1, p.2)

/-- **`G_{ij,kl} = ⟨Ψ, c_i† c_j c_l† c_k Ψ⟩`.** -/
theorem gMat_eq_inner (Ψ : Fock M) (p q : Fin M × Fin M) :
    gMat (rdm1 Ψ) (rdm2 Ψ) p q =
      inner ℂ Ψ (creOp p.1 (annOp p.2 (creOp q.2 (annOp q.1 Ψ)))) := by
  rw [annOp_creOp, map_sub, inner_sub_right, gMat, kd, rdm1, rdm2, annOp_annOp q.1 p.2, map_neg,
    map_neg, inner_neg_right, sub_neg_eq_add]
  by_cases h : p.2 = q.2
  · simp [h]
  · simp [h]

/-- `Σ_pq x̄_p G_pq x_q = ‖Σ_q x_q c_l† c_k Ψ‖²` (with `q = (k, l)`). -/
theorem quad_gMat (Ψ : Fock M) (x : Fin M × Fin M → ℂ) :
    star x ⬝ᵥ (gMat (rdm1 Ψ) (rdm2 Ψ) *ᵥ x) =
      inner ℂ (∑ p, x p • creOp p.2 (annOp p.1 Ψ)) (∑ q, x q • creOp q.2 (annOp q.1 Ψ)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, gMat_eq_inner, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [inner_creOp, inner_annOp]
  simp only [RCLike.star_def]
  ring

lemma gMat_isHermitian (Ψ : Fock M) : (gMat (rdm1 Ψ) (rdm2 Ψ)).IsHermitian := by
  ext p q
  simp only [conjTranspose_apply, gMat_eq_inner]
  rw [← inner_conj_symm, inner_creOp, inner_annOp, inner_creOp, inner_annOp]
  simp

/-- **G condition**: `G ≥ 0`. -/
theorem gMat_posSemidef (Ψ : Fock M) : (gMat (rdm1 Ψ) (rdm2 Ψ)).PosSemidef :=
  posSemidef_iff_dotProduct_mulVec.mpr
    ⟨gMat_isHermitian Ψ, fun x => by rw [quad_gMat]; exact inner_self_nonneg' _⟩

/-! ### The Q condition -/

/-- `Q_{ij,kl} = δ_ik δ_jl - δ_il δ_jk - δ_jl γ_ki + δ_jk γ_li + δ_il γ_kj - δ_ik γ_lj + D_{kl,ij}`. -/
def qMat (γ : Matrix (Fin M) (Fin M) ℂ) (D : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ) :
    Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ :=
  fun p q => kd p.1 q.1 * kd p.2 q.2 - kd p.1 q.2 * kd p.2 q.1 - kd p.2 q.2 * γ q.1 p.1 +
    kd p.2 q.1 * γ q.2 p.1 + kd p.1 q.2 * γ q.1 p.2 - kd p.1 q.1 * γ q.2 p.2 + D q p

/-- **`Q_{ij,kl} = ⟨Ψ, c_i c_j c_l† c_k† Ψ⟩`** for a unit vector (normal ordering with the
anticommutation relations). -/
theorem qMat_eq_inner {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) (p q : Fin M × Fin M) :
    qMat (rdm1 Ψ) (rdm2 Ψ) p q =
      inner ℂ Ψ (annOp p.1 (annOp p.2 (creOp q.2 (creOp q.1 Ψ)))) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  have hn : inner ℂ Ψ Ψ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΨ]; simp
  have hD : rdm2 Ψ (k, l) (i, j) = rdm2 Ψ (l, k) (j, i) := by
    rw [rdm2_swap_left, rdm2_swap_right, neg_neg]
  simp only [qMat]
  rw [hD]
  simp only [kd, rdm1, rdm2]
  simp only [annOp_creOp, map_sub, apply_ite (annOp i), apply_ite (creOp l), map_zero,
    inner_sub_right, apply_ite (inner ℂ Ψ), inner_zero_right, hn]
  split_ifs <;> subst_vars <;> ring

/-- `Q_{ij,kl} = ⟨c_j† c_i† Ψ, c_l† c_k† Ψ⟩`. -/
lemma qMat_eq_inner' {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) (p q : Fin M × Fin M) :
    qMat (rdm1 Ψ) (rdm2 Ψ) p q = inner ℂ (creOp p.2 (creOp p.1 Ψ)) (creOp q.2 (creOp q.1 Ψ)) := by
  rw [qMat_eq_inner hΨ, inner_annOp, inner_annOp]

/-- `Σ_pq x̄_p Q_pq x_q = ‖Σ_q x_q c_l† c_k† Ψ‖²` (with `q = (k, l)`). -/
theorem quad_qMat {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) (x : Fin M × Fin M → ℂ) :
    star x ⬝ᵥ (qMat (rdm1 Ψ) (rdm2 Ψ) *ᵥ x) =
      inner ℂ (∑ p, x p • creOp p.2 (creOp p.1 Ψ)) (∑ q, x q • creOp q.2 (creOp q.1 Ψ)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, qMat_eq_inner' hΨ, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [RCLike.star_def]
  ring

lemma qMat_isHermitian {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) : (qMat (rdm1 Ψ) (rdm2 Ψ)).IsHermitian := by
  ext p q
  simp only [conjTranspose_apply, qMat_eq_inner' hΨ, RCLike.star_def, inner_conj_symm]

/-- **Q condition**: `Q ≥ 0`. -/
theorem qMat_posSemidef {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) : (qMat (rdm1 Ψ) (rdm2 Ψ)).PosSemidef :=
  posSemidef_iff_dotProduct_mulVec.mpr
    ⟨qMat_isHermitian hΨ, fun x => by rw [quad_qMat hΨ]; exact inner_self_nonneg' _⟩

/-! ### Ensembles -/

section Ensemble

variable {ι : Type*} [Fintype ι]

/-- `D` of an ensemble is Hermitian. -/
theorem rdm2Ens_isHermitian (w : ι → ℝ) (Ψ : ι → Fock M) : (rdm2Ens w Ψ).IsHermitian :=
  isSelfAdjoint_sum _ fun k _ =>
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (rdm2_isHermitian (Ψ k))

/-- Antisymmetry for ensembles: `D_{ji,kl} = -D_{ij,kl}` and `D_{ij,lk} = -D_{ij,kl}`. -/
theorem rdm2Ens_swap (w : ι → ℝ) (Ψ : ι → Fock M) (i j k l : Fin M) :
    rdm2Ens w Ψ (j, i) (k, l) = -rdm2Ens w Ψ (i, j) (k, l) ∧
      rdm2Ens w Ψ (i, j) (l, k) = -rdm2Ens w Ψ (i, j) (k, l) := by
  simp only [rdm2Ens, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩ <;> rw [← Finset.sum_neg_distrib] <;> refine Finset.sum_congr rfl fun a _ => ?_
  · rw [rdm2_swap_left, mul_neg]
  · rw [rdm2_swap_right, mul_neg]

/-- **`Σ_k D_{ik,jk} = (N - 1) γ_ij`** for an `N`-particle ensemble. -/
theorem sum_rdm2Ens_contract {N : ℕ} {w : ι → ℝ} {Ψ : ι → Fock M} (h : IsNEnsemble N w Ψ)
    (i j : Fin M) :
    ∑ k, rdm2Ens w Ψ (i, k) (j, k) = ((N : ℂ) - 1) * rdm1Ens w Ψ i j := by
  simp only [rdm2Ens, rdm1Ens, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum, sum_rdm2_contract (h.2.2 a).2]
  ring

/-- **`Σ_ij D_{ij,ij} = N (N - 1)`** for an `N`-particle ensemble. -/
theorem sum_rdm2Ens_trace {N : ℕ} {w : ι → ℝ} {Ψ : ι → Fock M} (h : IsNEnsemble N w Ψ) :
    ∑ i, ∑ j, rdm2Ens w Ψ (i, j) (i, j) = (N : ℂ) * ((N : ℂ) - 1) := by
  simp_rw [sum_rdm2Ens_contract h, ← Finset.mul_sum]
  rw [show ∑ i, rdm1Ens w Ψ i i = (rdm1Ens w Ψ).trace from rfl, trace_rdm1Ens h]
  ring

/-- **P condition** for ensembles. -/
theorem rdm2Ens_posSemidef {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (Ψ : ι → Fock M) :
    (rdm2Ens w Ψ).PosSemidef :=
  posSemidef_sum _ fun k _ => (rdm2_posSemidef (Ψ k)).smul (by exact_mod_cast hw k)

lemma gMat_ens (w : ι → ℝ) (Ψ : ι → Fock M) :
    gMat (rdm1Ens w Ψ) (rdm2Ens w Ψ) = ∑ k, (w k : ℂ) • gMat (rdm1 (Ψ k)) (rdm2 (Ψ k)) := by
  ext p q
  simp only [gMat, rdm1Ens, rdm2Ens, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma qMat_ens {N : ℕ} {w : ι → ℝ} {Ψ : ι → Fock M} (h : IsNEnsemble N w Ψ) :
    qMat (rdm1Ens w Ψ) (rdm2Ens w Ψ) = ∑ k, (w k : ℂ) • qMat (rdm1 (Ψ k)) (rdm2 (Ψ k)) := by
  have hw : ∑ k, (w k : ℂ) = 1 := by rw [← Complex.ofReal_sum, h.2.1, Complex.ofReal_one]
  have e : ∀ (a : ι → ℂ) (c : ℂ), ∑ k, (w k : ℂ) * (c * a k) = c * ∑ k, (w k : ℂ) * a k := by
    intro a c; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have e1 : ∀ c : ℂ, ∑ k, (w k : ℂ) * c = c := by intro c; rw [← Finset.sum_mul, hw, one_mul]
  ext p q
  simp only [qMat, rdm1Ens, rdm2Ens, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e, e1]

/-- **G condition** for ensembles. -/
theorem gMatEns_posSemidef {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (Ψ : ι → Fock M) :
    (gMat (rdm1Ens w Ψ) (rdm2Ens w Ψ)).PosSemidef := by
  rw [gMat_ens]
  exact posSemidef_sum _ fun k _ => (gMat_posSemidef (Ψ k)).smul (by exact_mod_cast hw k)

/-- **Q condition** for `N`-particle ensembles. -/
theorem qMatEns_posSemidef {N : ℕ} {w : ι → ℝ} {Ψ : ι → Fock M} (h : IsNEnsemble N w Ψ) :
    (qMat (rdm1Ens w Ψ) (rdm2Ens w Ψ)).PosSemidef := by
  rw [qMat_ens h]
  exact posSemidef_sum _ fun k _ =>
    (qMat_posSemidef (h.2.2 k).1).smul (by exact_mod_cast h.1 k)

end Ensemble

end QM.ManyBody
