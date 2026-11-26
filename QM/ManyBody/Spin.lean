/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.Number
import QM.ManyBody.OneBody

/-!
# Spin-1/2 fermions on `M` sites

The `2M` spin modes are ordered with all spin-up modes first: `i↑ = i` and `i↓ = M + i` in
`Fin (M + M)`. A configuration `w` of the spin modes is the pair of its up part and its down part,
`w = spinConf (upPart w) (dnPart w)`. With this ordering the Fock space factorizes without signs
on the up modes. A down-mode operator picks up the parity `(-1)^{N↑}` of the up electrons, which
cancels in every hopping term `c_{i↓}† c_{j↓}`.

Functions of the form `tens f g (w) = f (upPart w) · g (dnPart w)` play the role of product vectors.

## Main definitions

* `upM i`, `dnM i`: the modes `i↑` and `i↓`.
* `spinConf u v`, `upPart w`, `dnPart w`: configurations as pairs.
* `tens f g`: the product of a function of up configurations and one of down configurations.
* `spinOneBody h↑ h↓ = Σ_ij (h↑_ij c_{i↑}† c_{j↑} + h↓_ij c_{i↓}† c_{j↓})`.
* `hubbardOp U = U Σ_i n_{i↑} n_{i↓}`.

## Main results

* `cre_upM_mulVec_tens`, `ann_upM_mulVec_tens`, `cre_dnM_mulVec_tens`, `ann_dnM_mulVec_tens`:
  the creation and annihilation operators on product functions.
* `spinOneBody_mulVec_tens`: `spinOneBody h↑ h↓ (f ⊗ g) = (Σ h↑ c†c) f ⊗ g + f ⊗ (Σ h↓ c†c) g`.
* `hubbardOp_mulVec`: the Hubbard operator is diagonal, with entry `U Σ_i [i ∈ u][i ∈ v]` on
  `spinConf u v`.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-! ### Spin modes and configurations -/

/-- The spin-up mode `i↑ = i`. -/
def upM (i : Fin M) : Fin (M + M) := Fin.castAdd M i

/-- The spin-down mode `i↓ = M + i`. -/
def dnM (i : Fin M) : Fin (M + M) := Fin.natAdd M i

lemma upM_injective : Function.Injective (upM : Fin M → Fin (M + M)) :=
  Fin.castAdd_injective M M

lemma dnM_injective : Function.Injective (dnM : Fin M → Fin (M + M)) :=
  Fin.natAdd_injective M M

lemma upM_lt_dnM (i j : Fin M) : upM i < dnM j := by
  rw [Fin.lt_def]; simp only [upM, dnM, Fin.val_castAdd, Fin.val_natAdd]; omega

lemma upM_ne_dnM (i j : Fin M) : upM i ≠ dnM j := (upM_lt_dnM i j).ne

lemma upM_lt_upM {i j : Fin M} : upM i < upM j ↔ i < j := Iff.rfl

lemma dnM_lt_dnM {i j : Fin M} : dnM i < dnM j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; simp only [dnM, Fin.val_natAdd]; omega

/-- Every spin mode is an up mode or a down mode. -/
lemma upM_or_dnM (a : Fin (M + M)) : (∃ i, a = upM i) ∨ ∃ i, a = dnM i := by
  induction a using Fin.addCases with
  | left i => exact Or.inl ⟨i, rfl⟩
  | right i => exact Or.inr ⟨i, rfl⟩

/-- The spin-up modes as an embedding. -/
def upEmb : Fin M ↪ Fin (M + M) := ⟨upM, upM_injective⟩

/-- The spin-down modes as an embedding. -/
def dnEmb : Fin M ↪ Fin (M + M) := ⟨dnM, dnM_injective⟩

/-- The configuration with spin-up sites `u` and spin-down sites `v`. -/
def spinConf (u v : Finset (Fin M)) : Finset (Fin (M + M)) := u.map upEmb ∪ v.map dnEmb

/-- The occupied spin-up sites of a configuration. -/
def upPart (w : Finset (Fin (M + M))) : Finset (Fin M) := univ.filter fun i => upM i ∈ w

/-- The occupied spin-down sites of a configuration. -/
def dnPart (w : Finset (Fin (M + M))) : Finset (Fin M) := univ.filter fun i => dnM i ∈ w

@[simp] lemma upM_mem_spinConf (i : Fin M) (u v : Finset (Fin M)) :
    upM i ∈ spinConf u v ↔ i ∈ u := by
  simp only [spinConf, mem_union, mem_map]
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, _, h⟩)
    · rwa [← upM_injective h]
    · exact absurd h.symm (upM_ne_dnM i j)
  · exact fun h => Or.inl ⟨i, h, rfl⟩

@[simp] lemma dnM_mem_spinConf (i : Fin M) (u v : Finset (Fin M)) :
    dnM i ∈ spinConf u v ↔ i ∈ v := by
  simp only [spinConf, mem_union, mem_map]
  constructor
  · rintro (⟨j, _, h⟩ | ⟨j, hj, h⟩)
    · exact absurd h (upM_ne_dnM j i)
    · rwa [← dnM_injective h]
  · exact fun h => Or.inr ⟨i, h, rfl⟩

@[simp] lemma upPart_spinConf (u v : Finset (Fin M)) : upPart (spinConf u v) = u := by
  ext i; simp [upPart]

@[simp] lemma dnPart_spinConf (u v : Finset (Fin M)) : dnPart (spinConf u v) = v := by
  ext i; simp [dnPart]

lemma spinConf_parts (w : Finset (Fin (M + M))) : spinConf (upPart w) (dnPart w) = w := by
  ext a
  rcases upM_or_dnM a with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp [upPart, dnPart]

lemma spinConf_inj {u v u' v' : Finset (Fin M)} :
    spinConf u v = spinConf u' v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    exact ⟨by rw [← upPart_spinConf u v, h, upPart_spinConf],
      by rw [← dnPart_spinConf u v, h, dnPart_spinConf]⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Two functions on spin configurations agree if they agree on every `spinConf u v`. -/
lemma funext_spin {β : Type*} {F G : Finset (Fin (M + M)) → β}
    (h : ∀ u v, F (spinConf u v) = G (spinConf u v)) : F = G := by
  funext w; rw [← spinConf_parts w]; exact h _ _

lemma spinConf_erase_upM (u v : Finset (Fin M)) (i : Fin M) :
    (spinConf u v).erase (upM i) = spinConf (u.erase i) v := by
  ext a; rcases upM_or_dnM a with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [upM_injective.eq_iff]
  · simp [(upM_ne_dnM i j).symm]

lemma spinConf_erase_dnM (u v : Finset (Fin M)) (i : Fin M) :
    (spinConf u v).erase (dnM i) = spinConf u (v.erase i) := by
  ext a; rcases upM_or_dnM a with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [upM_ne_dnM j i]
  · simp [dnM_injective.eq_iff]

lemma insert_upM_spinConf (u v : Finset (Fin M)) (i : Fin M) :
    insert (upM i) (spinConf u v) = spinConf (insert i u) v := by
  ext a; rcases upM_or_dnM a with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [upM_injective.eq_iff]
  · simp [(upM_ne_dnM i j).symm]

lemma insert_dnM_spinConf (u v : Finset (Fin M)) (i : Fin M) :
    insert (dnM i) (spinConf u v) = spinConf u (insert i v) := by
  ext a; rcases upM_or_dnM a with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [upM_ne_dnM j i]
  · simp [dnM_injective.eq_iff]

/-! ### Jordan–Wigner signs -/

lemma below_upM (i : Fin M) (u v : Finset (Fin M)) : below (upM i) (spinConf u v) = below i u := by
  have : (spinConf u v).filter (· < upM i) = (u.filter (· < i)).map upEmb := by
    ext a; rcases upM_or_dnM a with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [upM_lt_upM, upEmb]
    · simp only [mem_filter, dnM_mem_spinConf, mem_map]
      constructor
      · rintro ⟨-, h⟩; exact absurd (h.trans (upM_lt_dnM i j)) (lt_irrefl _)
      · rintro ⟨k, -, h⟩; exact absurd h (upM_ne_dnM k j)
  rw [below, this, card_map, below]

lemma below_dnM (i : Fin M) (u v : Finset (Fin M)) :
    below (dnM i) (spinConf u v) = u.card + below i v := by
  have : (spinConf u v).filter (· < dnM i) = u.map upEmb ∪ (v.filter (· < i)).map dnEmb := by
    ext a; rcases upM_or_dnM a with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [mem_filter, upM_mem_spinConf, mem_union, mem_map]
      constructor
      · rintro ⟨h, -⟩; exact Or.inl ⟨j, h, rfl⟩
      · rintro (⟨k, hk, h⟩ | ⟨k, -, h⟩)
        · obtain rfl := upM_injective h; exact ⟨hk, upM_lt_dnM k i⟩
        · exact absurd h.symm (upM_ne_dnM j k)
    · simp only [mem_filter, dnM_mem_spinConf, mem_union, mem_map, dnM_lt_dnM]
      constructor
      · rintro ⟨h, h'⟩; exact Or.inr ⟨j, ⟨h, h'⟩, rfl⟩
      · rintro (⟨k, -, h⟩ | ⟨k, hk, h⟩)
        · exact absurd h (upM_ne_dnM k j)
        · obtain rfl := dnM_injective h; exact hk
  rw [below, this, card_union_of_disjoint, card_map, card_map, below]
  rw [disjoint_left]
  rintro a ha hb
  obtain ⟨j, -, rfl⟩ := mem_map.mp ha
  obtain ⟨k, -, h⟩ := mem_map.mp hb
  exact upM_ne_dnM j k h.symm

lemma jwSign_upM (i : Fin M) (u v : Finset (Fin M)) :
    jwSign (upM i) (spinConf u v) = jwSign i u := by
  rw [jwSign, below_upM, jwSign]

lemma jwSign_dnM (i : Fin M) (u v : Finset (Fin M)) :
    jwSign (dnM i) (spinConf u v) = (-1) ^ u.card * jwSign i v := by
  rw [jwSign, below_dnM, pow_add, jwSign]

/-! ### Product functions -/

/-- The product `(f ⊗ g)(w) = f (upPart w) · g (dnPart w)` of a function of up configurations and
one of down configurations. -/
def tens (f g : Finset (Fin M) → ℂ) : Finset (Fin (M + M)) → ℂ :=
  fun w => f (upPart w) * g (dnPart w)

@[simp] lemma tens_spinConf (f g : Finset (Fin M) → ℂ) (u v : Finset (Fin M)) :
    tens f g (spinConf u v) = f u * g v := by
  simp [tens]

/-- The parity `(-1)^{|u|} f(u)` of a function of up configurations. -/
def par (f : Finset (Fin M) → ℂ) : Finset (Fin M) → ℂ := fun u => (-1) ^ u.card * f u

lemma tens_single (u v : Finset (Fin M)) :
    tens (Pi.single u 1) (Pi.single v 1) = Pi.single (spinConf u v) 1 := by
  refine funext_spin fun u' v' => ?_
  rw [tens_spinConf]
  by_cases h : u' = u ∧ v' = v
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [Pi.single_eq_of_ne (fun e => h (spinConf_inj.mp e))]
    rcases not_and_or.mp h with h | h <;> simp [Pi.single_eq_of_ne h]

lemma tens_add_left (f f' g : Finset (Fin M) → ℂ) : tens (f + f') g = tens f g + tens f' g := by
  funext w; simp [tens, add_mul]

lemma tens_add_right (f g g' : Finset (Fin M) → ℂ) : tens f (g + g') = tens f g + tens f g' := by
  funext w; simp [tens, mul_add]

lemma tens_smul_left (c : ℂ) (f g : Finset (Fin M) → ℂ) : tens (c • f) g = c • tens f g := by
  funext w; simp [tens, mul_assoc]

lemma tens_smul_right (c : ℂ) (f g : Finset (Fin M) → ℂ) : tens f (c • g) = c • tens f g := by
  funext w; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

lemma tens_par_par (f g : Finset (Fin M) → ℂ) : tens (par (par f)) g = tens f g := by
  funext w
  simp only [tens, par, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

lemma cre_upM_mulVec_tens (i : Fin M) (f g : Finset (Fin M) → ℂ) :
    cre (upM i) *ᵥ tens f g = tens (cre i *ᵥ f) g := by
  refine funext_spin fun u v => ?_
  rw [cre_mulVec, tens_spinConf, cre_mulVec]
  simp only [upM_mem_spinConf]
  split_ifs with h
  · rw [spinConf_erase_upM, jwSign_upM, tens_spinConf]; ring
  · ring

lemma ann_upM_mulVec_tens (i : Fin M) (f g : Finset (Fin M) → ℂ) :
    ann (upM i) *ᵥ tens f g = tens (ann i *ᵥ f) g := by
  refine funext_spin fun u v => ?_
  rw [ann_mulVec, tens_spinConf, ann_mulVec]
  simp only [upM_mem_spinConf]
  split_ifs with h
  · ring
  · rw [insert_upM_spinConf, jwSign_upM, tens_spinConf]; ring

lemma cre_dnM_mulVec_tens (i : Fin M) (f g : Finset (Fin M) → ℂ) :
    cre (dnM i) *ᵥ tens f g = tens (par f) (cre i *ᵥ g) := by
  refine funext_spin fun u v => ?_
  rw [cre_mulVec, tens_spinConf, cre_mulVec, par]
  simp only [dnM_mem_spinConf]
  split_ifs with h
  · rw [spinConf_erase_dnM, jwSign_dnM, tens_spinConf]; ring
  · ring

lemma ann_dnM_mulVec_tens (i : Fin M) (f g : Finset (Fin M) → ℂ) :
    ann (dnM i) *ᵥ tens f g = tens (par f) (ann i *ᵥ g) := by
  refine funext_spin fun u v => ?_
  rw [ann_mulVec, tens_spinConf, ann_mulVec, par]
  simp only [dnM_mem_spinConf]
  split_ifs with h
  · ring
  · rw [insert_dnM_spinConf, jwSign_dnM, tens_spinConf]; ring

/-- An up hopping term acts on the up factor. -/
lemma hop_upM_mulVec_tens (i j : Fin M) (f g : Finset (Fin M) → ℂ) :
    (cre (upM i) * ann (upM j)) *ᵥ tens f g = tens ((cre i * ann j) *ᵥ f) g := by
  rw [← mulVec_mulVec, ann_upM_mulVec_tens, cre_upM_mulVec_tens, mulVec_mulVec]

/-- A down hopping term acts on the down factor. The two parities cancel. -/
lemma hop_dnM_mulVec_tens (i j : Fin M) (f g : Finset (Fin M) → ℂ) :
    (cre (dnM i) * ann (dnM j)) *ᵥ tens f g = tens f ((cre i * ann j) *ᵥ g) := by
  rw [← mulVec_mulVec, ann_dnM_mulVec_tens, cre_dnM_mulVec_tens, tens_par_par, mulVec_mulVec]

/-! ### Spin Hamiltonians -/

/-- The spin-conserving one-body operator `Σ_ij (h↑_ij c_{i↑}† c_{j↑} + h↓_ij c_{i↓}† c_{j↓})`. -/
noncomputable def spinOneBody (hu hd : Matrix (Fin M) (Fin M) ℂ) : FockOp (M + M) :=
  ∑ i, ∑ j, (hu i j • (cre (upM i) * ann (upM j)) + hd i j • (cre (dnM i) * ann (dnM j)))

/-- **The spin one-body operator on product functions.** -/
theorem spinOneBody_mulVec_tens (hu hd : Matrix (Fin M) (Fin M) ℂ) (f g : Finset (Fin M) → ℂ) :
    spinOneBody hu hd *ᵥ tens f g = tens (oneBody hu *ᵥ f) g + tens f (oneBody hd *ᵥ g) := by
  have hl : ∀ (F : Fin M → Fin M → Finset (Fin M) → ℂ),
      tens (∑ i, ∑ j, F i j) g = ∑ i, ∑ j, tens (F i j) g := by
    intro F; funext w; simp [tens, Finset.sum_apply, Finset.sum_mul]
  have hr : ∀ (F : Fin M → Fin M → Finset (Fin M) → ℂ),
      tens f (∑ i, ∑ j, F i j) = ∑ i, ∑ j, tens f (F i j) := by
    intro F; funext w; simp [tens, Finset.sum_apply, Finset.mul_sum]
  simp only [spinOneBody, oneBody, sum_mulVec, add_mulVec, smul_mulVec, hop_upM_mulVec_tens,
    hop_dnM_mulVec_tens, hl, hr, tens_smul_left, tens_smul_right, Finset.sum_add_distrib]

/-- The Hubbard interaction `U Σ_i n_{i↑} n_{i↓}`. -/
noncomputable def hubbardOp (U : ℂ) : FockOp (M + M) := U • ∑ i, num (upM i) * num (dnM i)

/-- **The Hubbard operator is diagonal**, with entry `U Σ_i [i ∈ u][i ∈ v]` on `spinConf u v`. -/
theorem hubbardOp_mulVec (U : ℂ) (F : Finset (Fin (M + M)) → ℂ) (u v : Finset (Fin M)) :
    (hubbardOp U *ᵥ F) (spinConf u v) =
      U * (∑ i, (if i ∈ u then 1 else 0) * (if i ∈ v then 1 else 0)) * F (spinConf u v) := by
  rw [hubbardOp, smul_mulVec, Pi.smul_apply, sum_mulVec, Finset.sum_apply, smul_eq_mul, mul_assoc,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mulVec_mulVec, num_mulVec, num_mulVec]
  simp only [upM_mem_spinConf, dnM_mem_spinConf]
  ring

end QM.ManyBody
