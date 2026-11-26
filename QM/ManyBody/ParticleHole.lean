/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.Number
import QM.ManyBody.OneBody

/-!
# The particle–hole transformation

The particle–hole transformation `P` exchanges occupied and empty modes, `P |s⟩ = |sᶜ⟩`. It is a
self-adjoint unitary involution of the Fock space. With the Jordan–Wigner signs it turns creation
into annihilation up to the staggered sign `(-1)^i`, because the modes below `i` are either in `s` or
in `sᶜ`, so `jwSign i s * jwSign i sᶜ = (-1)^i`.

## Main definitions

* `QM.ManyBody.ph`: the particle–hole transformation `P |s⟩ = |sᶜ⟩`.
* `QM.ManyBody.stag h`: the staggered matrix `(-1)^(i+j) h_ij`.

## Main results

* `ph_mul_ph`, `ph_isHermitian`, `ph_mul_conjTranspose`: `P² = 1`, `P = P†`, `P P† = 1`.
* `ph_mulVec_single`: `P |s⟩ = |sᶜ⟩`, so `P` maps `N` particles to `M - N` particles
  (`card_compl_conf`).
* `ph_cre_ph`, `ph_ann_ph`: `P c_i† P = (-1)^i c_i` and `P c_i P = (-1)^i c_i†`.
* `ph_num_ph`, `ph_numTot_ph`: `P n̂_i P = 1 - n̂_i` and `P N̂ P = M - N̂`.
* `ph_oneBody_ph`: `P (Σ_ij h_ij c_i† c_j) P = (tr h) 1 - Σ_ij (stag h)_ji c_i† c_j`.
* `phOp_isSelfAdjoint`, `phOp_mul_phOp`: the same on the Fock Hilbert space.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-! ### The sign identity -/

/-- Every mode below `i` lies either in `s` or in its complement. -/
lemma below_add_below_compl (i : Fin M) (s : Finset (Fin M)) : below i s + below i sᶜ = i := by
  unfold below
  rw [← Finset.card_union_of_disjoint]
  · have : s.filter (· < i) ∪ sᶜ.filter (· < i) = Finset.Iio i := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl, Finset.mem_Iio]
      tauto
    rw [this, Fin.card_Iio]
  · exact Finset.disjoint_filter_filter disjoint_compl_right

/-- `jwSign i sᶜ = (-1)^i jwSign i s`. -/
lemma jwSign_compl (i : Fin M) (s : Finset (Fin M)) :
    jwSign i sᶜ = (-1) ^ (i : ℕ) * jwSign i s := by
  unfold jwSign
  rw [← below_add_below_compl i s, pow_add]
  have h : ((-1 : ℂ) ^ below i s) * (-1) ^ below i s = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-(-1 : ℂ) ^ below i sᶜ) * h

/-! ### The transformation -/

/-- The particle–hole transformation `P |s⟩ = |sᶜ⟩`. -/
def ph : FockOp M := fun t s => if t = sᶜ then 1 else 0

lemma ph_mulVec (v : Finset (Fin M) → ℂ) (u : Finset (Fin M)) : (ph *ᵥ v) u = v uᶜ := by
  simp only [mulVec, dotProduct, ph]
  rw [Finset.sum_eq_single uᶜ]
  · simp
  · intro s _ hs
    rw [ite_eq_right (fun h => hs (by rw [h, compl_compl]))]
    simp
  · simp

/-- `P |s⟩ = |sᶜ⟩`. -/
theorem ph_mulVec_single (s : Finset (Fin M)) : ph *ᵥ Pi.single s 1 = Pi.single sᶜ 1 := by
  funext u
  rw [ph_mulVec]
  by_cases h : u = sᶜ
  · subst h; simp
  · have : uᶜ ≠ s := fun e => h (by rw [← e, compl_compl])
    simp [h, this]

/-- The hole configuration of `N` particles has `M - N` particles. -/
theorem card_compl_conf (s : Finset (Fin M)) : sᶜ.card = M - s.card := by
  rw [Finset.card_compl, Fintype.card_fin]

/-- `P² = 1`. -/
theorem ph_mul_ph : (ph : FockOp M) * ph = 1 := by
  refine ext_of_mulVec fun v => ?_
  funext u
  rw [← Matrix.mulVec_mulVec, ph_mulVec, ph_mulVec, compl_compl, Matrix.one_mulVec]

/-- `P` is self-adjoint. -/
theorem ph_isHermitian : (ph : FockOp M).IsHermitian := by
  ext t s
  simp only [conjTranspose_apply, ph]
  by_cases h : s = tᶜ
  · subst h; simp
  · have : t ≠ sᶜ := fun e => h (by rw [e, compl_compl])
    simp [h, this]

/-- `P` is unitary. -/
theorem ph_mul_conjTranspose : (ph : FockOp M) * phᴴ = 1 := by
  rw [ph_isHermitian.eq, ph_mul_ph]

/-! ### Conjugating the creation and annihilation operators -/

/-- `P c_i† = (-1)^i c_i P`. -/
lemma ph_mul_cre (i : Fin M) : ph * cre i = ((-1) ^ (i : ℕ) : ℂ) • (ann i * ph) := by
  refine ext_of_mulVec fun v => ?_
  funext u
  rw [← Matrix.mulVec_mulVec, ph_mulVec, cre_mulVec, Matrix.smul_mulVec, Pi.smul_apply,
    ← Matrix.mulVec_mulVec, ann_mulVec, ph_mulVec]
  by_cases hi : i ∈ u
  · simp [hi]
  · have h1 : i ∈ uᶜ := Finset.mem_compl.mpr hi
    have hs : jwSign i (insert i u) = jwSign i u := by
      unfold jwSign below
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl i)]
    rw [ite_eq_left h1, ite_eq_left hi, ← Finset.compl_insert, smul_eq_mul, jwSign_compl, hs]
    ring

/-- **`P c_i† P = (-1)^i c_i`**. -/
theorem ph_cre_ph (i : Fin M) : ph * cre i * ph = ((-1) ^ (i : ℕ) : ℂ) • ann i := by
  rw [ph_mul_cre, Matrix.smul_mul, mul_assoc, ph_mul_ph, mul_one]

/-- **`P c_i P = (-1)^i c_i†`**. -/
theorem ph_ann_ph (i : Fin M) : ph * ann i * ph = ((-1) ^ (i : ℕ) : ℂ) • cre i := by
  have h := congrArg Matrix.conjTranspose (ph_cre_ph i)
  rw [conjTranspose_mul, conjTranspose_mul, ph_isHermitian.eq, conjTranspose_smul] at h
  simpa [ann, mul_assoc] using h

/-! ### Number and one-body operators -/

lemma ph_conj_mul (A B : FockOp M) : ph * (A * B) * ph = (ph * A * ph) * (ph * B * ph) := by
  rw [show ph * A * ph * (ph * B * ph) = ph * A * (ph * ph) * B * ph by noncomm_ring, ph_mul_ph]
  noncomm_ring

lemma sign_mul_self (i : Fin M) : ((-1) ^ (i : ℕ) : ℂ) * (-1) ^ (i : ℕ) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

/-- `P c_i† c_j P = (-1)^(i+j) c_i c_j†`. -/
lemma ph_hop_ph (i j : Fin M) :
    ph * (cre i * ann j) * ph = (((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ) : ℂ)) • (ann i * cre j) := by
  rw [ph_conj_mul, ph_cre_ph, ph_ann_ph, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- **`P n̂_i P = 1 - n̂_i`**. -/
theorem ph_num_ph (i : Fin M) : ph * num i * ph = 1 - num i := by
  rw [num, ph_hop_ph, sign_mul_self, one_smul, eq_sub_iff_add_eq]
  simpa using ann_mul_cre_add i i

/-- **`P N̂ P = M - N̂`**. -/
theorem ph_numTot_ph : ph * numTot * ph = (M : ℂ) • (1 : FockOp M) - numTot := by
  rw [numTot, Finset.mul_sum, Finset.sum_mul]
  simp_rw [ph_num_ph]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Nat.cast_smul_eq_nsmul ℂ]

/-- The staggered matrix `(-1)^(i+j) h_ij`. -/
def stag (h : Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => (-1) ^ (i : ℕ) * (-1) ^ (j : ℕ) * h i j

/-- **The particle–hole transform of a one-body operator**:
`P (Σ_ij h_ij c_i† c_j) P = (tr h) 1 - Σ_ij (stag h)_ji c_i† c_j`. -/
theorem ph_oneBody_ph (h : Matrix (Fin M) (Fin M) ℂ) :
    ph * oneBody h * ph = h.trace • (1 : FockOp M) - oneBody (stag h)ᵀ := by
  have hc : ∀ i j : Fin M, ann i * cre j = (if i = j then (1 : FockOp M) else 0) - cre j * ann i :=
    fun i j => eq_sub_of_add_eq (ann_mul_cre_add i j)
  have e : ∀ i j : Fin M, ph * (h i j • (cre i * ann j)) * ph =
      (if i = j then h i i else 0) • (1 : FockOp M) - (stag h)ᵀ j i • (cre j * ann i) := by
    intro i j
    rw [Matrix.mul_smul, Matrix.smul_mul, ph_hop_ph, hc, smul_smul, smul_sub]
    congr 1
    · by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, ite_eq_left rfl, sign_mul_self, mul_one]
      · rw [ite_eq_right hij, ite_eq_right hij, smul_zero, zero_smul]
    · congr 1
      simp only [stag, Matrix.transpose_apply]
      ring
  calc ph * oneBody h * ph = ∑ i, ∑ j, ph * (h i j • (cre i * ann j)) * ph := by
        rw [oneBody, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ j, ((if i = j then h i i else 0) • (1 : FockOp M) -
          (stag h)ᵀ j i • (cre j * ann i)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j
    _ = h.trace • (1 : FockOp M) - oneBody (stag h)ᵀ := by
        simp only [Finset.sum_sub_distrib]
        refine congrArg₂ (fun x y => x - y) ?_ ?_
        · rw [Matrix.trace, Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · rw [ite_eq_left rfl, Matrix.diag_apply]
          · intro j _ hj; rw [ite_eq_right (Ne.symm hj), zero_smul]
          · intro hi; exact absurd (Finset.mem_univ i) hi
        · rw [oneBody, Finset.sum_comm]

/-! ### On the Fock Hilbert space -/

/-- The particle–hole transformation as a bounded operator on the Fock space. -/
noncomputable def phOp : Fock M →L[ℂ] Fock M := toFockCLM ph

/-- `P` is self-adjoint on the Fock space. -/
theorem phOp_isSelfAdjoint : IsSelfAdjoint (phOp : Fock M →L[ℂ] Fock M) := by
  unfold phOp
  rw [IsSelfAdjoint, ← map_star]
  exact congrArg toFockCLM ph_isHermitian

/-- `P² = 1` on the Fock space; with self-adjointness, `P` is unitary. -/
theorem phOp_mul_phOp : (phOp : Fock M →L[ℂ] Fock M) * phOp = 1 := by
  unfold phOp
  rw [← map_mul, ph_mul_ph, map_one]

/-- `P c_i† P = (-1)^i c_i` on the Fock space. -/
theorem phOp_creOp_phOp (i : Fin M) :
    phOp * creOp i * phOp = ((-1) ^ (i : ℕ) : ℂ) • annOp i := by
  unfold phOp creOp annOp
  rw [← map_mul, ← map_mul, ph_cre_ph, map_smul]

end QM.ManyBody
