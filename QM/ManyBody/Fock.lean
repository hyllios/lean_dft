/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Powerset

/-!
# The fermionic Fock space of `M` modes

A configuration is a set of occupied modes, `s : Finset (Fin M)`. The Fock space `Fock M` is the
Hilbert space of complex functions on all configurations, `EuclideanSpace ℂ (Finset (Fin M))`, with
`⟪Ψ, Φ⟫ = Σ_s conj (Ψ s) * Φ s`; it has dimension `2 ^ M` (`finrank_fock`). Operators are matrices
indexed by configurations (`FockOp M`); a matrix `A` acts on `Fock M` as `A.toEuclideanLin`, and the
adjoint of that operator is the operator of the conjugate transpose `Aᴴ`.

The creation operator `cre i` (`c_i†`) adds mode `i` with the Jordan–Wigner sign
`jwSign i s = (-1) ^ #{j ∈ s | j < i}`; the annihilation operator is its adjoint, `ann i = (cre i)ᴴ`
(`c_i`).

## Main definitions

* `QM.ManyBody.Fock M`, `QM.ManyBody.FockOp M`: the Fock space and its operators (matrices).
* `QM.ManyBody.jwSign i s`: the Jordan–Wigner sign.
* `QM.ManyBody.cre i`, `QM.ManyBody.ann i`: creation and annihilation operators.

## Main results

* `finrank_fock`: `dim Fock M = 2 ^ M`.
* `cre_mulVec`, `ann_mulVec`: the action on functions of configurations.
* `cre_mulVec_single`, `ann_mulVec_single`: the action on basis vectors `|s⟩`.
* `ann_eq_adjoint`: `c_i` is the Hilbert-space adjoint of `c_i†`.
* **Canonical anticommutation relations**: `ann_mul_cre_add` (`{c_i, c_j†} = δ_ij`),
  `ann_mul_ann_add` (`{c_i, c_j} = 0`), `cre_mul_cre_add` (`{c_i†, c_j†} = 0`), as matrix identities.
* The same on the Hilbert space: `creOp i`, `annOp i : Fock M →L[ℂ] Fock M` (bounded operators),
  `annOp_eq_adjoint` (`c_i = (c_i†)†` as Hilbert-space adjoint), `annOp_mul_creOp_add`,
  `annOp_mul_annOp_add`, `creOp_mul_creOp_add`. They follow from the matrix identities through
  `Matrix.toEuclideanCLM`, a star-algebra equivalence between matrices and bounded operators.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-- The fermionic Fock space of `M` modes: complex functions on configurations
(sets of occupied modes), with the `ℓ²` inner product. -/
abbrev Fock (M : ℕ) := EuclideanSpace ℂ (Finset (Fin M))

/-- The Fock space of `M` modes has dimension `2 ^ M`. -/
theorem finrank_fock : Module.finrank ℂ (Fock M) = 2 ^ M := by
  simp [Fock, finrank_euclideanSpace, Fintype.card_finset]

/-- Operators on the Fock space, as matrices indexed by configurations. -/
abbrev FockOp (M : ℕ) := Matrix (Finset (Fin M)) (Finset (Fin M)) ℂ

/-! ### The Jordan–Wigner sign -/

/-- The number of occupied modes of `s` below mode `i`. -/
def below (i : Fin M) (s : Finset (Fin M)) : ℕ := (s.filter (· < i)).card

/-- The Jordan–Wigner sign `(-1) ^ #{j ∈ s | j < i}`. -/
def jwSign (i : Fin M) (s : Finset (Fin M)) : ℂ := (-1) ^ below i s

lemma jwSign_mul_self (i : Fin M) (s : Finset (Fin M)) : jwSign i s * jwSign i s = 1 := by
  rw [jwSign, ← pow_add, ← two_mul, pow_mul]; norm_num

lemma star_jwSign (i : Fin M) (s : Finset (Fin M)) : star (jwSign i s) = jwSign i s := by
  simp [jwSign]

/-- The sign factor picked up when mode `j` is added below mode `i`. -/
def exch (j i : Fin M) : ℂ := if j < i then -1 else 1

/-- Adding an unoccupied mode `j` changes the sign at `i` by `-1` exactly when `j < i`. -/
lemma jwSign_insert {i j : Fin M} {s : Finset (Fin M)} (hj : j ∉ s) :
    jwSign i (insert j s) = exch j i * jwSign i s := by
  unfold jwSign below exch
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => hj (Finset.mem_filter.mp hm).1), pow_succ]; ring
  · ring

/-- For distinct modes exactly one of `j < i`, `i < j` holds, so the two exchange factors
multiply to `-1`. -/
lemma exch_mul_exch {i j : Fin M} (h : i ≠ j) : exch j i * exch i j = -1 := by
  unfold exch
  rcases lt_or_gt_of_ne h with hij | hji
  · simp [hij, not_lt.mpr hij.le]
  · simp [hji, not_lt.mpr hji.le]

/-! ### Creation and annihilation operators -/

/-- The creation operator `c_i†`: `c_i† |s⟩ = jwSign i s |s ∪ {i}⟩` if `i ∉ s`, and `0` otherwise. -/
def cre (i : Fin M) : FockOp M := fun t s => if i ∉ s ∧ t = insert i s then jwSign i s else 0

/-- The annihilation operator `c_i`, the adjoint (conjugate transpose) of `c_i†`. -/
def ann (i : Fin M) : FockOp M := (cre i)ᴴ

/-- `c_i` is the Hilbert-space adjoint of `c_i†`. -/
theorem ann_eq_adjoint (i : Fin M) :
    (ann i).toEuclideanLin = LinearMap.adjoint (cre i).toEuclideanLin :=
  Matrix.toEuclideanLin_conjTranspose_eq_adjoint _

lemma ann_apply (i : Fin M) (u w : Finset (Fin M)) :
    ann i u w = if i ∉ u ∧ w = insert i u then jwSign i u else 0 := by
  simp only [ann, conjTranspose_apply, cre]
  split_ifs <;> simp [star_jwSign]

/-- Action of `c_i†` on a function of configurations. -/
theorem cre_mulVec (i : Fin M) (v : Finset (Fin M) → ℂ) (t : Finset (Fin M)) :
    (cre i *ᵥ v) t = if i ∈ t then jwSign i (t.erase i) * v (t.erase i) else 0 := by
  simp only [mulVec, dotProduct, cre]
  by_cases ht : i ∈ t
  · rw [ite_eq_left ht, Finset.sum_eq_single (t.erase i)]
    · rw [ite_eq_left ⟨Finset.notMem_erase i t, (Finset.insert_erase ht).symm⟩]
    · intro s _ hs
      rw [ite_eq_right]; · simp
      rintro ⟨his, rfl⟩
      exact hs (Finset.erase_insert his).symm
    · simp
  · rw [ite_eq_right ht]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [ite_eq_right]; · simp
    rintro ⟨-, rfl⟩
    exact ht (Finset.mem_insert_self i s)

/-- Action of `c_i` on a function of configurations. -/
theorem ann_mulVec (i : Fin M) (v : Finset (Fin M) → ℂ) (u : Finset (Fin M)) :
    (ann i *ᵥ v) u = if i ∉ u then jwSign i u * v (insert i u) else 0 := by
  simp only [mulVec, dotProduct, ann_apply]
  by_cases hu : i ∉ u
  · rw [ite_eq_left hu, Finset.sum_eq_single (insert i u)]
    · rw [ite_eq_left ⟨hu, rfl⟩]
    · intro w _ hw
      rw [ite_eq_right]; · simp
      exact fun h => hw h.2
    · simp
  · rw [ite_eq_right hu]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [ite_eq_right]; · simp
    exact fun h => hu h.1

/-- `c_i† |s⟩ = jwSign i s |s ∪ {i}⟩` if `i ∉ s`, and `0` otherwise (`|s⟩ = Pi.single s 1`). -/
theorem cre_mulVec_single (i : Fin M) (s : Finset (Fin M)) :
    cre i *ᵥ Pi.single s 1 = if i ∉ s then jwSign i s • Pi.single (insert i s) 1 else 0 := by
  funext t
  rw [cre_mulVec]
  by_cases hs : i ∈ s
  · have hne : t.erase i ≠ s := fun h => Finset.notMem_erase i t (h ▸ hs)
    simp [hs, hne]
  · by_cases ht : i ∈ t
    · by_cases hts : t.erase i = s
      · have h : t = insert i s := by rw [← hts, Finset.insert_erase ht]
        subst h
        simp [hs, Finset.erase_insert hs]
      · have hne : t ≠ insert i s := fun h => hts (by rw [h, Finset.erase_insert hs])
        simp [hs, ht, hts, hne]
    · have hne : t ≠ insert i s := fun h => ht (h ▸ Finset.mem_insert_self i s)
      simp [hs, ht, hne]

/-- `c_i |s⟩ = jwSign i (s \ {i}) |s \ {i}⟩` if `i ∈ s`, and `0` otherwise. -/
theorem ann_mulVec_single (i : Fin M) (s : Finset (Fin M)) :
    ann i *ᵥ Pi.single s 1 = if i ∈ s then jwSign i (s.erase i) • Pi.single (s.erase i) 1 else 0 := by
  funext u
  rw [ann_mulVec]
  by_cases hs : i ∈ s
  · by_cases hiu : i ∈ u
    · have hne : u ≠ s.erase i := fun h => Finset.notMem_erase i s (h ▸ hiu)
      simp [hs, hiu, hne]
    · by_cases hus : u = s.erase i
      · subst hus
        simp [hs, Finset.insert_erase hs]
      · have hne : insert i u ≠ s := fun h => hus (by rw [← h, Finset.erase_insert hiu])
        simp [hs, hiu, hus, hne]
  · have hne : insert i u ≠ s := fun h => hs (h ▸ Finset.mem_insert_self i u)
    simp [hs, hne]

/-- Sanity check with two modes: adding mode `1` to `{0}` gives a minus sign, since the occupied
mode `0` lies below it: `c_1† |{0}⟩ = -|{0, 1}⟩`. -/
example : cre (1 : Fin 2) *ᵥ Pi.single {0} 1 = -Pi.single {0, 1} 1 := by
  rw [cre_mulVec_single]
  have hb : below (1 : Fin 2) {0} = 1 := by decide
  have h : jwSign (1 : Fin 2) {0} = -1 := by simp [jwSign, hb]
  simp only [h, Finset.notMem_singleton, neg_smul, one_smul]
  rw [Finset.pair_comm, ite_eq_left (by decide : (1 : Fin 2) ≠ 0)]

/-! ### Canonical anticommutation relations -/

/-- `{c_i, c_j†} = δ_ij` on vectors. -/
theorem ann_cre_mulVec_add (i j : Fin M) (v : Finset (Fin M) → ℂ) :
    ann i *ᵥ (cre j *ᵥ v) + cre j *ᵥ (ann i *ᵥ v) = if i = j then v else 0 := by
  funext u
  simp only [Pi.add_apply, ann_mulVec, cre_mulVec]
  by_cases hij : i = j
  · subst hij
    by_cases hu : i ∈ u
    · simp [hu, Finset.insert_erase hu, ← mul_assoc, jwSign_mul_self]
    · simp [hu, Finset.erase_insert hu, ← mul_assoc, jwSign_mul_self]
  · rw [ite_eq_right hij, Pi.zero_apply]
    by_cases hi : i ∈ u <;> by_cases hj : j ∈ u
    · -- `c_i` kills both terms
      simp [hi, hj, Finset.mem_erase, hij]
    · simp [hi, hj]
    · -- the only nontrivial case: `i ∉ u`, `j ∈ u`
      have hj' : j ∉ u.erase j := Finset.notMem_erase j u
      have hi' : i ∉ u.erase j := fun h => hi (Finset.mem_of_mem_erase h)
      have e1 : (insert i u).erase j = insert i (u.erase j) := Finset.erase_insert_of_ne hij
      have s1 : jwSign i u = exch j i * jwSign i (u.erase j) := by
        conv_lhs => rw [← Finset.insert_erase hj]
        exact jwSign_insert hj'
      have s2 : jwSign j (insert i (u.erase j)) = exch i j * jwSign j (u.erase j) :=
        jwSign_insert hi'
      have hx := exch_mul_exch hij
      simp only [hi, hj, not_false_eq_true, ite_true, Finset.mem_insert, or_true, e1, s2, s1,
        Finset.mem_erase, ne_eq, hij, and_false]
      linear_combination (jwSign i (u.erase j) * jwSign j (u.erase j) *
        v (insert i (u.erase j))) * hx
    · simp [hi, hj, Ne.symm hij]

/-- `{c_i, c_j} = 0` on vectors. -/
theorem ann_ann_mulVec_add (i j : Fin M) (v : Finset (Fin M) → ℂ) :
    ann i *ᵥ (ann j *ᵥ v) + ann j *ᵥ (ann i *ᵥ v) = 0 := by
  funext u
  simp only [Pi.add_apply, ann_mulVec, Pi.zero_apply]
  by_cases hij : i = j
  · subst hij; simp
  by_cases hi : i ∈ u
  · by_cases hj : j ∈ u
    · simp [hi, hj]
    · simp [hi, hj, hij]
  · by_cases hj : j ∈ u
    · simp [hi, hj, Ne.symm hij]
    · have s1 : jwSign j (insert i u) = exch i j * jwSign j u := jwSign_insert hi
      have s2 : jwSign i (insert j u) = exch j i * jwSign i u := jwSign_insert hj
      have hx := exch_mul_exch hij
      have hcomm : insert i (insert j u) = insert j (insert i u) := Finset.insert_comm i j u
      have hexch : exch i j + exch j i = 0 := by
        unfold exch
        rcases lt_or_gt_of_ne hij with h | h
        · simp [h, not_lt.mpr h.le]
        · simp [h, not_lt.mpr h.le]
      simp only [hi, hj, not_false_eq_true, ite_true, Finset.mem_insert, hij, Ne.symm hij,
        false_or, s1, s2, hcomm]
      linear_combination (jwSign i u * jwSign j u * v (insert j (insert i u))) * hexch

/-! ### The anticommutation relations as operator identities -/

lemma ext_of_mulVec {A B : FockOp M} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

/-- **Canonical anticommutation relation** `{c_i, c_j†} = δ_ij 𝟙`. -/
theorem ann_mul_cre_add (i j : Fin M) :
    ann i * cre j + cre j * ann i = if i = j then (1 : FockOp M) else 0 := by
  refine ext_of_mulVec fun v => ?_
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ann_cre_mulVec_add]
  split_ifs <;> simp

/-- **Canonical anticommutation relation** `{c_i, c_j} = 0`. -/
theorem ann_mul_ann_add (i j : Fin M) : ann i * ann j + ann j * ann i = (0 : FockOp M) := by
  refine ext_of_mulVec fun v => ?_
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ann_ann_mulVec_add]
  simp

/-- **Canonical anticommutation relation** `{c_i†, c_j†} = 0` (the adjoint of `{c_j, c_i} = 0`). -/
theorem cre_mul_cre_add (i j : Fin M) : cre i * cre j + cre j * cre i = (0 : FockOp M) := by
  have h := congrArg Matrix.conjTranspose (ann_mul_ann_add j i)
  simpa [ann, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, add_comm] using h

/-! ### The anticommutation relations on the Hilbert space -/

/-- The star-algebra equivalence between matrices indexed by configurations and bounded operators
on the Fock space. -/
noncomputable abbrev toFockCLM : FockOp M ≃⋆ₐ[ℂ] (Fock M →L[ℂ] Fock M) :=
  Matrix.toEuclideanCLM (n := Finset (Fin M)) (𝕜 := ℂ)

/-- The creation operator `c_i†` as a bounded operator on the Fock (Hilbert) space. -/
noncomputable def creOp (i : Fin M) : Fock M →L[ℂ] Fock M := toFockCLM (cre i)

/-- The annihilation operator `c_i` as a bounded operator on the Fock (Hilbert) space. -/
noncomputable def annOp (i : Fin M) : Fock M →L[ℂ] Fock M := toFockCLM (ann i)

/-- `c_i` is the Hilbert-space adjoint of `c_i†`. -/
theorem annOp_eq_adjoint (i : Fin M) : annOp i = ContinuousLinearMap.adjoint (creOp i) := by
  unfold annOp creOp
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  rfl

/-- **CAR on the Fock space** `{c_i, c_j†} = δ_ij 𝟙`. -/
theorem annOp_mul_creOp_add (i j : Fin M) :
    annOp i * creOp j + creOp j * annOp i = if i = j then 1 else 0 := by
  unfold annOp creOp
  rw [← map_mul, ← map_mul, ← map_add, ann_mul_cre_add]
  split_ifs <;> simp

/-- **CAR on the Fock space** `{c_i, c_j} = 0`. -/
theorem annOp_mul_annOp_add (i j : Fin M) : annOp i * annOp j + annOp j * annOp i = 0 := by
  unfold annOp
  rw [← map_mul, ← map_mul, ← map_add, ann_mul_ann_add, map_zero]

/-- **CAR on the Fock space** `{c_i†, c_j†} = 0`. -/
theorem creOp_mul_creOp_add (i j : Fin M) : creOp i * creOp j + creOp j * creOp i = 0 := by
  unfold creOp
  rw [← map_mul, ← map_mul, ← map_add, cre_mul_cre_add, map_zero]

end QM.ManyBody
