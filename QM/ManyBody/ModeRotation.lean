/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import QM.ManyBody.RDM

/-!
# Mode rotations

A unitary `u` of the one-particle space `ℂ^M` induces a unitary `U(u)` of the Fock space. It sends
the configuration `|s⟩ = c_{s₁}† ⋯ c_{s_N}† |∅⟩` to the creation string of the rotated orbitals
`u e_{s₁}, …, u e_{s_N}`.

Everything rests on two facts about creation strings `c†(φ₁) ⋯ c†(φ_N) |∅⟩` of general orbitals,
where `c†(φ) = Σ_j φ_j c_j†`. An orbital annihilator `c(χ)` acts on a string by Laplace expansion
(`annV_mulVec_strV`), and the overlap of two strings is the Gram determinant `det ⟨φ_a, ψ_b⟩`
(`strV_overlap`). Both follow from the CAR `{c(χ), c†(φ)} = ⟨χ, φ⟩` by induction on the length.
The Gram determinant of orthonormal orbitals gives unitarity, and the Laplace expansion gives the
intertwining law `U c_i U† = c(u e_i)`.

## Main results

* `annV_mul_creV_add`: the CAR for orbital operators.
* `strV_overlap`: the overlap of two creation strings is the Gram determinant.
* `modeRot u`: the mode rotation, with `modeRot_mulVec_vac`, `modeRot_unitary`,
  `modeRot_mul_cre` (`U c_i† U† = Σ_j u_ji c_j†`), `numTot_mul_modeRot` and `modeRot_mul`
  (`U(uv) = U(u) U(v)`).
* `rdm1_modeRotOp`: `γ(U(u) Ψ) = ū γ(Ψ) uᵀ`.
* `rdm1_basis`: the one-body matrix of a configuration is the diagonal of its occupations.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-! ### Orbital creation and annihilation operators -/

/-- The creation operator of the orbital `φ`, `c†(φ) = Σ_j φ_j c_j†`. -/
noncomputable def creV (φ : Fin M → ℂ) : FockOp M := ∑ j, φ j • cre j

/-- The annihilation operator of the orbital `φ`, `c(φ) = c†(φ)† = Σ_j φ̄_j c_j`. -/
noncomputable def annV (φ : Fin M → ℂ) : FockOp M := (creV φ)ᴴ

lemma annV_eq (φ : Fin M → ℂ) : annV φ = ∑ j, star (φ j) • ann j := by
  simp [annV, creV, conjTranspose_sum, conjTranspose_smul, ann]

lemma creV_add (φ ψ : Fin M → ℂ) : creV (φ + ψ) = creV φ + creV ψ := by
  simp [creV, add_smul, Finset.sum_add_distrib]

lemma creV_smul (c : ℂ) (φ : Fin M → ℂ) : creV (c • φ) = c • creV φ := by
  simp [creV, Finset.smul_sum, smul_smul]

lemma creV_sum {ι : Type*} (S : Finset ι) (φ : ι → Fin M → ℂ) :
    creV (∑ k ∈ S, φ k) = ∑ k ∈ S, creV (φ k) := by
  simp only [creV, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- The CAR for orbital operators, `{c(χ), c†(φ)} = ⟨χ, φ⟩`. -/
theorem annV_mul_creV_add (χ φ : Fin M → ℂ) :
    annV χ * creV φ + creV φ * annV χ = (star χ ⬝ᵥ φ) • (1 : FockOp M) := by
  rw [annV_eq, creV, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := univ) (t := univ)
    (f := fun i j => (φ i • cre i) * (star (χ j) • ann j)), ← Finset.sum_add_distrib]
  have h : ∀ j k, star (χ j) • ann j * (φ k • cre k) + φ k • cre k * (star (χ j) • ann j) =
      (star (χ j) * φ k) • (ann j * cre k + cre k * ann j) := by
    intro j k
    rw [smul_mul_smul_comm, smul_mul_smul_comm, smul_add, mul_comm (φ k)]
  simp_rw [← Finset.sum_add_distrib, h, ann_mul_cre_add, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct, Pi.star_apply, Finset.sum_smul]

lemma annV_creV_mulVec (χ φ : Fin M → ℂ) (v : Finset (Fin M) → ℂ) :
    annV χ *ᵥ (creV φ *ᵥ v) = (star χ ⬝ᵥ φ) • v - creV φ *ᵥ (annV χ *ᵥ v) := by
  have h := congrArg (· *ᵥ v) (annV_mul_creV_add χ φ)
  simp only [add_mulVec, ← mulVec_mulVec, smul_mulVec, one_mulVec] at h
  rw [← h, add_sub_cancel_right]

/-! ### Creation strings -/

/-- The vacuum `|∅⟩`. -/
def vac : Finset (Fin M) → ℂ := Pi.single ∅ 1

lemma ann_mulVec_vac (i : Fin M) : ann i *ᵥ (vac : Finset (Fin M) → ℂ) = 0 := by
  rw [vac, ann_mulVec_single]; simp

lemma annV_mulVec_vac (χ : Fin M → ℂ) : annV χ *ᵥ (vac : Finset (Fin M) → ℂ) = 0 := by
  simp [annV_eq, sum_mulVec, smul_mulVec, ann_mulVec_vac]

/-- The creation string `c†(Φ 0) ⋯ c†(Φ (N-1)) |∅⟩`. -/
noncomputable def strV : {N : ℕ} → (Fin N → Fin M → ℂ) → Finset (Fin M) → ℂ
  | 0, _ => vac
  | _ + 1, Φ => creV (Φ 0) *ᵥ strV (Fin.tail Φ)

lemma strV_zero (Φ : Fin 0 → Fin M → ℂ) : strV Φ = vac := rfl

lemma strV_succ {N : ℕ} (Φ : Fin (N + 1) → Fin M → ℂ) :
    strV Φ = creV (Φ 0) *ᵥ strV (Fin.tail Φ) := rfl

/-- A string of `N` orbitals lives in the `N`-particle sector. -/
lemma strV_apply_eq_zero {N : ℕ} (Φ : Fin N → Fin M → ℂ) {u : Finset (Fin M)} (hu : u.card ≠ N) :
    strV Φ u = 0 := by
  induction N generalizing u with
  | zero =>
    rw [strV_zero, vac, Pi.single_eq_of_ne (by rintro rfl; exact hu rfl)]
  | succ N ih =>
    rw [strV_succ, creV, sum_mulVec, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_mulVec, Pi.smul_apply, cre_mulVec]
    split_ifs with hj
    · have hpos := Finset.card_pos.mpr ⟨j, hj⟩
      have hne : (u.erase j).card ≠ N := by rw [Finset.card_erase_of_mem hj]; omega
      rw [ih (Fin.tail Φ) hne, mul_zero, smul_zero]
    · rw [smul_zero]

/-- `N̂` acts on a string of `N` orbitals as multiplication by `N`. -/
theorem numTot_mulVec_strV {N : ℕ} (Φ : Fin N → Fin M → ℂ) :
    numTot *ᵥ strV Φ = (N : ℂ) • strV Φ := by
  funext u
  rw [numTot_mulVec, Pi.smul_apply, smul_eq_mul]
  by_cases hu : u.card = N
  · rw [hu]
  · rw [strV_apply_eq_zero Φ hu, mul_zero, mul_zero]

/-- **An orbital annihilator on a creation string** (Laplace expansion):
`c(χ) c†(Φ₀) ⋯ |∅⟩ = Σ_b (-1)^b ⟨χ, Φ_b⟩ c†(Φ₀) ⋯ (omit b) ⋯ |∅⟩`. -/
theorem annV_mulVec_strV (χ : Fin M → ℂ) {N : ℕ} (Φ : Fin (N + 1) → Fin M → ℂ) :
    annV χ *ᵥ strV Φ =
      ∑ b : Fin (N + 1), ((-1) ^ (b : ℕ) * (star χ ⬝ᵥ Φ b)) • strV (Φ ∘ b.succAbove) := by
  induction N with
  | zero =>
    rw [strV_succ, annV_creV_mulVec, strV_zero, annV_mulVec_vac, mulVec_zero, sub_zero,
      Fin.sum_univ_one, strV_zero]
    simp
  | succ N ih =>
    rw [strV_succ, annV_creV_mulVec, ih, mulVec_sum, Fin.sum_univ_succ (n := N + 1), sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      rfl
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [mulVec_smul, strV_succ (Φ ∘ (b.succ).succAbove)]
      have h0 : (Φ ∘ (b.succ).succAbove) 0 = Φ 0 := by simp
      have ht : Fin.tail (Φ ∘ (b.succ).succAbove) = Fin.tail Φ ∘ b.succAbove := by
        funext k; simp [Fin.tail]
      rw [h0, ht, ← neg_smul]
      congr 1
      simp [Fin.tail, pow_succ]

/-- **Overlap of creation strings**: `⟨c†(Φ) |∅⟩, c†(Ψ) |∅⟩⟩ = det ⟨Φ_a, Ψ_b⟩`. -/
theorem strV_overlap {N : ℕ} (Φ Ψ : Fin N → Fin M → ℂ) :
    star (strV Φ) ⬝ᵥ strV Ψ = (Matrix.of fun a b => star (Φ a) ⬝ᵥ Ψ b).det := by
  induction N with
  | zero =>
    rw [strV_zero, strV_zero, vac, dotProduct, Finset.sum_eq_single ∅]
    · simp
    · intro w _ hw; simp [Pi.single_eq_of_ne hw]
    · simp
  | succ N ih =>
    rw [strV_succ Φ, star_mulVec, ← dotProduct_mulVec, ← annV, annV_mulVec_strV, dotProduct_sum,
      det_succ_row_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dotProduct_smul, ih, smul_eq_mul]
    simp only [of_apply]
    rfl

/-! ### Mode rotations -/

/-- Orthonormality of the columns of a unitary matrix. -/
lemma col_overlap {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ) (i j : Fin M) :
    star (u.col i) ⬝ᵥ u.col j = if i = j then 1 else 0 := by
  have h := congrFun (congrFun ((mem_unitaryGroup_iff').mp hu) i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa [dotProduct, star_apply, col_apply] using h

/-- The rotated orbitals `u e_{s_k}` of the sorted modes of `s`. -/
def rotOrb (u : Matrix (Fin M) (Fin M) ℂ) (s : Finset (Fin M)) {n : ℕ} (h : s.card = n) :
    Fin n → Fin M → ℂ :=
  fun k => u.col (s.orderEmbOfFin h k)

/-- **The mode rotation** `U(u)`: `U(u) |s⟩ = c†(u e_{s₁}) ⋯ c†(u e_{s_N}) |∅⟩`. -/
noncomputable def modeRot (u : Matrix (Fin M) (Fin M) ℂ) : FockOp M :=
  Matrix.of fun t s => strV (rotOrb u s rfl) t

lemma modeRot_mulVec_single (u : Matrix (Fin M) (Fin M) ℂ) (s : Finset (Fin M)) {n : ℕ}
    (h : s.card = n) : modeRot u *ᵥ Pi.single s 1 = strV (rotOrb u s h) := by
  subst h
  funext t
  simp [modeRot]

/-- `U(u) |∅⟩ = |∅⟩`. -/
theorem modeRot_mulVec_vac (u : Matrix (Fin M) (Fin M) ℂ) : modeRot u *ᵥ vac = vac := by
  rw [vac, modeRot_mulVec_single u ∅ (Finset.card_empty), strV_zero, vac]

/-- The Gram determinant of two sorted families of distinct basis vectors. -/
lemma det_sorted (s t : Finset (Fin M)) {n : ℕ} (hs : s.card = n) (ht : t.card = n) :
    (Matrix.of fun a b : Fin n =>
      if s.orderEmbOfFin hs a = t.orderEmbOfFin ht b then (1 : ℂ) else 0).det =
      if s = t then 1 else 0 := by
  by_cases hst : s = t
  · subst hst
    have h1 : (Matrix.of fun a b : Fin n =>
        if s.orderEmbOfFin hs a = s.orderEmbOfFin ht b then (1 : ℂ) else 0) = 1 := by
      ext a b
      simp [Matrix.one_apply, (s.orderEmbOfFin hs).injective.eq_iff]
    rw [h1, det_one, ite_eq_left rfl]
  · rw [ite_eq_right hst]
    obtain ⟨x, hxs, hxt⟩ : ∃ x ∈ s, x ∉ t := by
      by_contra hc
      push Not at hc
      exact hst (Finset.eq_of_subset_of_card_le hc (by rw [hs, ht]))
    have hx : x ∈ Set.range (s.orderEmbOfFin hs) := by rw [Finset.range_orderEmbOfFin]; exact hxs
    obtain ⟨a, rfl⟩ := hx
    refine det_eq_zero_of_row_eq_zero a fun b => ?_
    rw [of_apply, ite_eq_right]
    intro h
    exact hxt (h ▸ Finset.orderEmbOfFin_mem _ _ _)

/-- The rotated configurations are orthonormal. -/
theorem rotOrb_overlap {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s t : Finset (Fin M)) {n m : ℕ} (hs : s.card = n) (ht : t.card = m) :
    star (strV (rotOrb u s hs)) ⬝ᵥ strV (rotOrb u t ht) = if s = t then 1 else 0 := by
  by_cases hnm : n = m
  · subst hnm
    rw [strV_overlap]
    have h : ∀ a b, star (rotOrb u s hs a) ⬝ᵥ rotOrb u t ht b =
        if s.orderEmbOfFin hs a = t.orderEmbOfFin ht b then 1 else 0 :=
      fun a b => col_overlap hu _ _
    simp only [h]
    exact det_sorted s t hs ht
  · have hst : s ≠ t := by rintro rfl; exact hnm (hs.symm.trans ht)
    rw [ite_eq_right hst]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hw : w.card = n
    · rw [strV_apply_eq_zero _ (show w.card ≠ m by omega), mul_zero]
    · rw [Pi.star_apply, strV_apply_eq_zero _ hw, star_zero, zero_mul]

/-- `U(u)` is unitary: `U† U = 1`. -/
theorem modeRot_conjTranspose_mul {u : Matrix (Fin M) (Fin M) ℂ}
    (hu : u ∈ unitaryGroup (Fin M) ℂ) : (modeRot u)ᴴ * modeRot u = 1 := by
  ext s t
  rw [Matrix.mul_apply, Matrix.one_apply, ← rotOrb_overlap hu s t rfl rfl]
  rfl

/-- `U(u)` is unitary: `U U† = 1`. -/
theorem modeRot_mul_conjTranspose {u : Matrix (Fin M) (Fin M) ℂ}
    (hu : u ∈ unitaryGroup (Fin M) ℂ) : modeRot u * (modeRot u)ᴴ = 1 :=
  mul_eq_one_comm.mp (modeRot_conjTranspose_mul hu)

/-- `U(u)` commutes with `N̂`. -/
theorem numTot_mul_modeRot (u : Matrix (Fin M) (Fin M) ℂ) :
    numTot * modeRot u = modeRot u * numTot := by
  refine ext_of_mulVec_single fun s => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, numTot_mulVec_single, mulVec_smul,
    modeRot_mulVec_single u s rfl, numTot_mulVec_strV]

/-- **Intertwining law for annihilators**: `c(u e_i) U(u) = U(u) c_i`. -/
theorem annV_mul_modeRot {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (i : Fin M) : annV (u.col i) * modeRot u = modeRot u * ann i := by
  refine ext_of_mulVec_single fun t => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, ann_mulVec_single]
  by_cases hit : i ∈ t
  · obtain ⟨n, hn⟩ : ∃ n, t.card = n + 1 :=
      ⟨t.card - 1, by have := Finset.card_pos.mpr ⟨i, hit⟩; omega⟩
    have hr : i ∈ Set.range (t.orderEmbOfFin hn) := by rw [Finset.range_orderEmbOfFin]; exact hit
    obtain ⟨b, rfl⟩ := hr
    have hn' : (t.erase (t.orderEmbOfFin hn b)).card = n := by
      rw [Finset.card_erase_of_mem hit, hn]; rfl
    rw [ite_eq_left hit, mulVec_smul, modeRot_mulVec_single u _ hn', modeRot_mulVec_single u t hn,
      annV_mulVec_strV, Finset.sum_eq_single b]
    · have hG : star (u.col (t.orderEmbOfFin hn b)) ⬝ᵥ rotOrb u t hn b = 1 := by
        rw [show rotOrb u t hn b = u.col (t.orderEmbOfFin hn b) from rfl, col_overlap hu,
          ite_eq_left rfl]
      have hE : rotOrb u t hn ∘ b.succAbove = rotOrb u _ hn' := by
        funext k
        change u.col _ = u.col _
        rw [orderEmbOfFin_erase t hn b hn', Function.comp_apply]
      have hj : jwSign (t.orderEmbOfFin hn b) (t.erase (t.orderEmbOfFin hn b)) =
          (-1) ^ (b : ℕ) := by
        rw [jwSign, below, Finset.filter_erase, Finset.erase_eq_of_notMem (by simp),
          card_filter_lt_orderEmbOfFin]
      rw [hG, hE, hj, mul_one]
    · intro c _ hc
      rw [show rotOrb u t hn c = u.col (t.orderEmbOfFin hn c) from rfl, col_overlap hu,
        ite_eq_right, mul_zero, zero_smul]
      exact fun h => hc ((t.orderEmbOfFin hn).injective h).symm
    · simp
  · rw [ite_eq_right hit, mulVec_zero]
    cases hc : t.card with
    | zero => rw [modeRot_mulVec_single u t hc, strV_zero, annV_mulVec_vac]
    | succ n =>
      rw [modeRot_mulVec_single u t hc, annV_mulVec_strV]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [show rotOrb u t hc c = u.col (t.orderEmbOfFin hc c) from rfl, col_overlap hu,
        ite_eq_right, mul_zero, zero_smul]
      rintro rfl
      exact hit (Finset.orderEmbOfFin_mem _ _ _)

/-- **Intertwining law for creators**: `c†(u e_i) U(u) = U(u) c_i†`. -/
theorem creV_mul_modeRot {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (i : Fin M) : creV (u.col i) * modeRot u = modeRot u * cre i := by
  have h := congrArg conjTranspose (annV_mul_modeRot hu i)
  rw [conjTranspose_mul, conjTranspose_mul, annV, conjTranspose_conjTranspose, ann,
    conjTranspose_conjTranspose] at h
  calc creV (u.col i) * modeRot u
      = modeRot u * (modeRot u)ᴴ * creV (u.col i) * modeRot u := by
        rw [modeRot_mul_conjTranspose hu, one_mul]
    _ = modeRot u * ((modeRot u)ᴴ * creV (u.col i)) * modeRot u := by
        simp only [mul_assoc]
    _ = modeRot u * cre i := by
        rw [h, mul_assoc, mul_assoc, modeRot_conjTranspose_mul hu, mul_one]

/-- **`U(u) c_i† U(u)† = Σ_j u_ji c_j†`.** -/
theorem modeRot_mul_cre {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (i : Fin M) : modeRot u * cre i * (modeRot u)ᴴ = ∑ j, u j i • cre j := by
  rw [← creV_mul_modeRot hu, mul_assoc, modeRot_mul_conjTranspose hu, mul_one, creV]
  rfl

/-- The intertwining law for a general orbital: `c†(u φ) U(u) = U(u) c†(φ)`. -/
theorem creV_mulVec_mul_modeRot {u : Matrix (Fin M) (Fin M) ℂ}
    (hu : u ∈ unitaryGroup (Fin M) ℂ) (φ : Fin M → ℂ) :
    creV (u *ᵥ φ) * modeRot u = modeRot u * creV φ := by
  have h : u *ᵥ φ = ∑ i, φ i • u.col i := by
    funext j
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h, creV_sum, Finset.sum_mul, creV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [creV_smul, smul_mul_assoc, creV_mul_modeRot hu, mul_smul_comm]

/-- `U(u)` rotates every orbital of a creation string. -/
theorem modeRot_mulVec_strV {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    {N : ℕ} (Φ : Fin N → Fin M → ℂ) : modeRot u *ᵥ strV Φ = strV fun k => u *ᵥ Φ k := by
  induction N with
  | zero => rw [strV_zero, strV_zero, modeRot_mulVec_vac]
  | succ N ih =>
    rw [strV_succ, strV_succ, mulVec_mulVec, ← creV_mulVec_mul_modeRot hu, ← mulVec_mulVec, ih]
    rfl

/-- **`U(uv) = U(u) U(v)`.** -/
theorem modeRot_mul {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (v : Matrix (Fin M) (Fin M) ℂ) : modeRot (u * v) = modeRot u * modeRot v := by
  refine ext_of_mulVec_single fun s => ?_
  rw [← mulVec_mulVec, modeRot_mulVec_single _ s rfl, modeRot_mulVec_single _ s rfl,
    modeRot_mulVec_strV hu]
  congr 1

/-! ### Mode rotations on the Hilbert space -/

/-- The mode rotation `U(u)` as a bounded operator on the Fock space. -/
noncomputable def modeRotOp (u : Matrix (Fin M) (Fin M) ℂ) : Fock M →L[ℂ] Fock M :=
  toFockCLM (modeRot u)

/-- `U(u)` is a unitary operator. -/
theorem modeRotOp_mem_unitary {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ) :
    modeRotOp u ∈ unitary (Fock M →L[ℂ] Fock M) := by
  rw [Unitary.mem_iff]
  unfold modeRotOp
  rw [← map_star, ← map_mul, ← map_mul, star_eq_conjTranspose, modeRot_conjTranspose_mul hu,
    modeRot_mul_conjTranspose hu, map_one]
  exact ⟨rfl, rfl⟩

/-- `U(u) |∅⟩ = |∅⟩`. -/
theorem modeRotOp_vac (u : Matrix (Fin M) (Fin M) ℂ) :
    modeRotOp u (EuclideanSpace.single ∅ 1) = EuclideanSpace.single ∅ 1 := by
  unfold modeRotOp
  rw [EuclideanSpace.single, PiLp.single, toEuclideanCLM_toLp]
  exact congrArg _ (modeRot_mulVec_vac u)

/-- **`U(u) c_i† U(u)† = Σ_j u_ji c_j†`** on the Hilbert space. -/
theorem modeRotOp_creOp {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (i : Fin M) : modeRotOp u * creOp i * star (modeRotOp u) = ∑ j, u j i • creOp j := by
  unfold modeRotOp creOp
  rw [← map_star, ← map_mul, ← map_mul, star_eq_conjTranspose, modeRot_mul_cre hu, map_sum]
  simp_rw [map_smul]

/-- `U(u)` commutes with `N̂`. -/
theorem numTotOp_mul_modeRotOp (u : Matrix (Fin M) (Fin M) ℂ) :
    numTotOp * modeRotOp u = modeRotOp u * numTotOp := by
  unfold numTotOp modeRotOp
  rw [← map_mul, ← map_mul, numTot_mul_modeRot]

/-- **`U(uv) = U(u) U(v)`** on the Hilbert space. -/
theorem modeRotOp_mul {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (v : Matrix (Fin M) (Fin M) ℂ) : modeRotOp (u * v) = modeRotOp u * modeRotOp v := by
  unfold modeRotOp
  rw [modeRot_mul hu, map_mul]

/-- A mode rotation maps `N`-particle states to `N`-particle states. -/
theorem IsNState.modeRotOp {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    {N : ℕ} {Ψ : Fock M} (hΨ : IsNState N Ψ) : IsNState N (modeRotOp u Ψ) := by
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.norm_map_of_mem_unitary (modeRotOp_mem_unitary hu), hΨ.1]
  · have h := congrArg (fun T : Fock M →L[ℂ] Fock M => T Ψ) (numTotOp_mul_modeRotOp u)
    simp only [_root_.mul_apply_eq_comp] at h
    rw [h, hΨ.2, map_smul]

/-- `c_a = Σ_i ū_ai c†(u e_i)` for a unitary `u`. -/
lemma cre_eq_sum {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ) (a : Fin M) :
    cre a = ∑ i, star (u a i) • creV (u.col i) := by
  have hU := (mem_unitaryGroup_iff).mp hu
  have h : ∀ j, ∑ i, star (u a i) * u j i = if j = a then 1 else 0 := fun j => by
    have := congrFun (congrFun hU j) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [star_apply, mul_comm] using this
  simp only [creV, Finset.smul_sum, smul_smul, col_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul]
  simp

/-- `c_b = Σ_k u_bk c(u e_k)` for a unitary `u`. -/
lemma ann_eq_sum {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ) (b : Fin M) :
    ann b = ∑ k, u b k • annV (u.col k) := by
  have h := congrArg conjTranspose (cre_eq_sum hu b)
  rw [conjTranspose_sum] at h
  simp_rw [conjTranspose_smul, star_star] at h
  exact h

/-- `U† c_a† U = Σ_i ū_ai c_i†`. -/
lemma modeRot_conj_cre {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (a : Fin M) : (modeRot u)ᴴ * cre a * modeRot u = ∑ i, star (u a i) • cre i := by
  rw [cre_eq_sum hu a, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, mul_assoc, creV_mul_modeRot hu, ← mul_assoc,
    modeRot_conjTranspose_mul hu, one_mul]

/-- `U† c_b U = Σ_k u_bk c_k`. -/
lemma modeRot_conj_ann {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (b : Fin M) : (modeRot u)ᴴ * ann b * modeRot u = ∑ k, u b k • ann k := by
  rw [ann_eq_sum hu b, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, mul_assoc, annV_mul_modeRot hu, ← mul_assoc,
    modeRot_conjTranspose_mul hu, one_mul]

/-- **Transformation law of the one-body matrix**: `γ(U(u) Ψ) = ū γ(Ψ) uᵀ`. -/
theorem rdm1_modeRotOp {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (Ψ : Fock M) : rdm1 (modeRotOp u Ψ) = u.map star * rdm1 Ψ * uᵀ := by
  have hmat : ∀ a b, (modeRot u)ᴴ * (cre a * ann b) * modeRot u =
      ∑ i, ∑ k, (star (u a i) * u b k) • (cre i * ann k) := by
    intro a b
    have h : (modeRot u)ᴴ * (cre a * ann b) * modeRot u =
        ((modeRot u)ᴴ * cre a * modeRot u) * ((modeRot u)ᴴ * ann b * modeRot u) := by
      calc (modeRot u)ᴴ * (cre a * ann b) * modeRot u
          = (modeRot u)ᴴ * cre a * (modeRot u * (modeRot u)ᴴ) * ann b * modeRot u := by
            rw [modeRot_mul_conjTranspose hu]; simp only [mul_one, mul_assoc]
        _ = _ := by simp only [mul_assoc]
    rw [h, modeRot_conj_cre hu, modeRot_conj_ann hu, Finset.sum_mul_sum]
    simp_rw [smul_mul_smul_comm]
  have hop : ∀ a b, star (modeRotOp u) * (creOp a * annOp b) * modeRotOp u =
      ∑ i, ∑ k, (star (u a i) * u b k) • (creOp i * annOp k) := by
    intro a b
    unfold modeRotOp creOp annOp
    rw [← map_star, ← map_mul, ← map_mul, ← map_mul, star_eq_conjTranspose, hmat, map_sum]
    simp_rw [map_sum, map_smul, map_mul]
  ext a b
  have h1 : rdm1 (modeRotOp u Ψ) a b =
      inner ℂ Ψ ((star (modeRotOp u) * (creOp a * annOp b) * modeRotOp u) Ψ) := by
    rw [rdm1, ContinuousLinearMap.star_eq_adjoint]
    simp only [_root_.mul_apply_eq_comp]
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [h1, hop]
  simp only [_root_.sum_apply, _root_.smul_apply, inner_sum, inner_smul_right,
    _root_.mul_apply_eq_comp]
  simp only [Matrix.mul_apply, Matrix.map_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [rdm1]
  ring

/-! ### Configurations -/

/-- A configuration with `N` occupied modes is an `N`-particle state. -/
theorem isNState_single (s : Finset (Fin M)) : IsNState s.card (EuclideanSpace.single s 1) := by
  refine ⟨by simp, ?_⟩
  unfold numTotOp
  rw [EuclideanSpace.single, PiLp.single, toEuclideanCLM_toLp, numTot_mulVec_single]
  rfl

/-- **The one-body matrix of a configuration** is the diagonal of its occupations. -/
theorem rdm1_single (s : Finset (Fin M)) :
    rdm1 (EuclideanSpace.single s 1) = diagonal fun i => if i ∈ s then 1 else 0 := by
  ext i j
  have hv : creOp i (annOp j (EuclideanSpace.single s 1)) =
      WithLp.toLp 2 (cre i *ᵥ (ann j *ᵥ Pi.single s 1)) := by
    unfold creOp annOp
    rw [EuclideanSpace.single, PiLp.single, toEuclideanCLM_toLp, toEuclideanCLM_toLp]
  rw [rdm1, hv, EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.toLp_apply, cre_mulVec,
    diagonal_apply]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi, ann_mulVec]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left (Finset.notMem_erase i s), Finset.insert_erase hi, Pi.single_eq_same,
        ite_eq_left rfl, ite_eq_left hi, mul_one, jwSign_mul_self]
    · rw [ite_eq_right hij]
      by_cases hj : j ∈ s.erase i
      · rw [ite_eq_right (not_not.mpr hj), mul_zero]
      · rw [ite_eq_left hj]
        have hne : insert j (s.erase i) ≠ s := fun h =>
          hj (Finset.mem_erase.mpr ⟨Ne.symm hij, h ▸ Finset.mem_insert_self j _⟩)
        rw [Pi.single_eq_of_ne hne, mul_zero, mul_zero]
  · rw [ite_eq_right hi]
    simp [hi]

end QM.ManyBody
