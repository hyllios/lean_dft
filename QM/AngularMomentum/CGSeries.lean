/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.LinearCombination
import QM.AngularMomentum.Coupling

/-!
# The Clebsch–Gordan series

The product `V_{j₁} ⊗ V_{j₂}` of two spin representations is realized as the functions on pairs
`Fin (n₁ + 1) × Fin (n₂ + 1) → K`, with `L` acting on the first index and `S` on the second
(`onFst`, `onSnd`). For `p ≤ min(n₁, n₂)` the vector `Σ_{a+b=p} c_a e_a ⊗ e_b`, with
`c_{a+1} = -c_a (p - a)(n₂ - p + a + 1) / ((a + 1)(n₁ - a))`, is a highest weight of weight
`J = j₁ + j₂ - p`. Its ladder stops after `2J + 1` vectors, and the ladders of all these highest
weights form a basis: `V_{j₁} ⊗ V_{j₂} ≅ ⊕_{J = |j₁ - j₂|}^{j₁ + j₂} V_J`.

## Main results

* `isSU2_pair`: `J = L + S` on the pair model.
* `pairJp_hw`, `pairJz_hw`: the highest weights.
* `cg_series` (**Clebsch–Gordan series**): the ladder vectors form a basis.
* `spin_orbit`: for `V_l ⊗ V_{1/2}`, `L·S = l/2` on `J = l + ½` and `-(l+1)/2` on `J = l - ½`.
-/

namespace QM

open Module

variable {K : Type*} [Field K] [CharZero K] {a b : ℕ}

/-! ### Operators acting on one index -/

/-- An operator on the first index of a function of pairs. -/
def onFst (A : End K (Fin a → K)) : End K (Fin a × Fin b → K) where
  toFun f p := A (fun i => f (i, p.2)) p.1
  map_add' f g := by funext p; exact congrFun (map_add A _ _) p.1
  map_smul' c f := by funext p; exact congrFun (map_smul A c _) p.1

/-- An operator on the second index of a function of pairs. -/
def onSnd (B : End K (Fin b → K)) : End K (Fin a × Fin b → K) where
  toFun f p := B (fun j => f (p.1, j)) p.2
  map_add' f g := by funext p; exact congrFun (map_add B _ _) p.2
  map_smul' c f := by funext p; exact congrFun (map_smul B c _) p.2

omit [CharZero K] in
lemma onFst_apply (A : End K (Fin a → K)) (f : Fin a × Fin b → K) (p : Fin a × Fin b) :
    onFst A f p = A (fun i => f (i, p.2)) p.1 := rfl

omit [CharZero K] in
lemma onSnd_apply (B : End K (Fin b → K)) (f : Fin a × Fin b → K) (p : Fin a × Fin b) :
    onSnd B f p = B (fun j => f (p.1, j)) p.2 := rfl

/-- `onFst` as an algebra homomorphism. -/
def onFstHom : End K (Fin a → K) →ₐ[K] End K (Fin a × Fin b → K) where
  toFun := onFst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- `onSnd` as an algebra homomorphism. -/
def onSndHom : End K (Fin b → K) →ₐ[K] End K (Fin a × Fin b → K) where
  toFun := onSnd
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [CharZero K] in
/-- The su(2) relations are preserved by algebra homomorphisms. -/
theorem IsSU2.map {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {Sp Sm Sz : End K V} (h : IsSU2 Sp Sm Sz) (φ : End K V →ₐ[K] End K V') :
    IsSU2 (φ Sp) (φ Sm) (φ Sz) where
  comm_pm := by rw [← map_mul, ← map_mul, ← map_sub, h.comm_pm, map_smul]
  comm_zp := by rw [← map_mul, ← map_mul, ← map_sub, h.comm_zp]
  comm_zm := by rw [← map_mul, ← map_mul, ← map_sub, h.comm_zm, map_neg]

omit [CharZero K] in
/-- Operators on different indices commute. -/
lemma onFst_mul_onSnd (A : End K (Fin a → K)) (B : End K (Fin b → K)) :
    onFst A * onSnd B = onSnd B * (onFst A : End K (Fin a × Fin b → K)) := by
  refine LinearMap.ext fun f => funext fun p => ?_
  change A (fun i => B (fun j => f (i, j)) p.2) p.1 = B (fun j => A (fun i => f (i, j)) p.1) p.2
  have hAg : ∀ g : Fin a → K, A g p.1 = ∑ i, g i * A (fun i' => if i = i' then 1 else 0) p.1 := by
    intro g; rw [LinearMap.pi_apply_eq_sum_univ A]; simp [Finset.sum_apply]
  have hBg : ∀ g : Fin b → K, B g p.2 = ∑ j, g j * B (fun j' => if j = j' then 1 else 0) p.2 := by
    intro g; rw [LinearMap.pi_apply_eq_sum_univ B]; simp [Finset.sum_apply]
  have e1 : ∀ i, B (fun j => f (i, j)) p.2 =
      ∑ j, f (i, j) * B (fun j' => if j = j' then 1 else 0) p.2 := fun i => hBg _
  have e2 : ∀ j, A (fun i => f (i, j)) p.1 =
      ∑ i, f (i, j) * A (fun i' => if i = i' then 1 else 0) p.1 := fun j => hAg _
  rw [hAg, hBg]
  simp only [e1, e2, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [CharZero K] in
lemma commutes_pair (Lp Lm Lz : End K (Fin a → K)) (Sp Sm Sz : End K (Fin b → K)) :
    Commutes (onFst Lp) (onFst Lm) (onFst Lz) (onSnd Sp) (onSnd Sm) (onSnd Sz) :=
  ⟨onFst_mul_onSnd _ _, onFst_mul_onSnd _ _, onFst_mul_onSnd _ _, onFst_mul_onSnd _ _,
    onFst_mul_onSnd _ _, onFst_mul_onSnd _ _, onFst_mul_onSnd _ _, onFst_mul_onSnd _ _,
    onFst_mul_onSnd _ _⟩

/-! ### Joint eigenvectors -/

/-- Common eigenvectors of two operators with distinct pairs of eigenvalues are linearly
independent. -/
theorem linearIndependent_of_joint_eigen {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module K V]
    (A B : End K V) (w : ι → V) (α β : ι → K) (hw : ∀ i, w i ≠ 0)
    (hA : ∀ i, A (w i) = α i • w i) (hB : ∀ i, B (w i) = β i • w i)
    (hinj : Function.Injective fun i => (α i, β i)) : LinearIndependent K w := by
  classical
  set S : Finset K := (Finset.univ ×ˢ Finset.univ).image
    (fun q : ι × ι => (α q.1 - α q.2) / (β q.2 - β q.1))
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset S
  refine Module.End.eigenvectors_linearIndependent' (A + t • B) (fun i => α i + t * β i) ?_ w
    fun i => Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, hw i⟩
  · intro i k hik
    simp only at hik
    by_cases hb : β i = β k
    · have ha : α i = α k := by rw [hb] at hik; exact add_right_cancel hik
      exact hinj (Prod.ext ha hb)
    · exfalso
      apply ht
      refine Finset.mem_image.mpr ⟨(i, k), by simp, ?_⟩
      have hne : β k - β i ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
      field_simp
      linear_combination hik
  · rw [LinearMap.add_apply, LinearMap.smul_apply, hA, hB, smul_smul, ← add_smul]

/-! ### The pair model of `V_{j₁} ⊗ V_{j₂}` -/

section CG

variable (n₁ n₂ : ℕ)

/-- `J₊ = L₊ ⊗ 1 + 1 ⊗ S₊` on the pair model. -/
def pairJp : End K (Fin (n₁ + 1) × Fin (n₂ + 1) → K) := onFst (spinSp n₁) + onSnd (spinSp n₂)

/-- `J₋ = L₋ ⊗ 1 + 1 ⊗ S₋` on the pair model. -/
def pairJm : End K (Fin (n₁ + 1) × Fin (n₂ + 1) → K) := onFst (spinSm n₁) + onSnd (spinSm n₂)

/-- `J_z = L_z ⊗ 1 + 1 ⊗ S_z` on the pair model. -/
def pairJz : End K (Fin (n₁ + 1) × Fin (n₂ + 1) → K) := onFst (spinSz n₁) + onSnd (spinSz n₂)

/-- **The coupled angular momentum satisfies the su(2) relations.** -/
theorem isSU2_pair : IsSU2 (pairJp (K := K) n₁ n₂) (pairJm n₁ n₂) (pairJz n₁ n₂) :=
  ((isSU2_spinRep (K := K) n₁).map (onFstHom (a := n₁ + 1) (b := n₂ + 1))).add
    ((isSU2_spinRep (K := K) n₂).map (onSndHom (a := n₁ + 1) (b := n₂ + 1)))
    (commutes_pair _ _ _ _ _ _)

variable {n₁ n₂}

lemma pairJp_apply (f : Fin (n₁ + 1) × Fin (n₂ + 1) → K) (x : Fin (n₁ + 1)) (y : Fin (n₂ + 1)) :
    pairJp n₁ n₂ f (x, y) =
      (if h : (x : ℕ) < n₁ then (((x : K) + 1) * ((n₁ : K) - x)) * f (⟨x + 1, by omega⟩, y)
        else 0) +
      (if h : (y : ℕ) < n₂ then (((y : K) + 1) * ((n₂ : K) - y)) * f (x, ⟨y + 1, by omega⟩)
        else 0) := rfl

lemma pairJz_apply (f : Fin (n₁ + 1) × Fin (n₂ + 1) → K) (x : Fin (n₁ + 1)) (y : Fin (n₂ + 1)) :
    pairJz n₁ n₂ f (x, y) = ((n₁ : K) / 2 - x) * f (x, y) + ((n₂ : K) / 2 - y) * f (x, y) := rfl

variable (n₁ n₂) in
/-- The coefficients of the highest weight of weight `j₁ + j₂ - p`:
`c_0 = 1`, `c_{a+1} = -c_a (p - a)(n₂ - p + a + 1) / ((a + 1)(n₁ - a))`. -/
def cgc (p : ℕ) : ℕ → K
  | 0 => 1
  | k + 1 => -cgc p k * (((p : K) - k) * ((n₂ : K) - p + k + 1)) / (((k : K) + 1) * ((n₁ : K) - k))

variable (n₁ n₂) in
/-- The highest weight `Σ_{a+b=p} c_a e_a ⊗ e_b`. -/
def hw (p : ℕ) : Fin (n₁ + 1) × Fin (n₂ + 1) → K :=
  fun q => if (q.1 : ℕ) + q.2 = p then cgc n₁ n₂ p q.1 else 0

lemma hw_of_eq {p : ℕ} {q : Fin (n₁ + 1) × Fin (n₂ + 1)} (h : (q.1 : ℕ) + q.2 = p) :
    hw (K := K) n₁ n₂ p q = cgc n₁ n₂ p q.1 := if_pos h

lemma hw_of_ne {p : ℕ} {q : Fin (n₁ + 1) × Fin (n₂ + 1)} (h : (q.1 : ℕ) + q.2 ≠ p) :
    hw (K := K) n₁ n₂ p q = 0 := if_neg h

/-- `J₊` annihilates the highest weight. -/
theorem pairJp_hw {p : ℕ} (hp : p ≤ min n₁ n₂) : pairJp n₁ n₂ (hw (K := K) n₁ n₂ p) = 0 := by
  have hp1 : p ≤ n₁ := le_trans hp (min_le_left _ _)
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  funext ⟨x, y⟩
  rw [pairJp_apply, Pi.zero_apply]
  by_cases hxy : (x : ℕ) + y + 1 = p
  · have hx : (x : ℕ) < n₁ := by omega
    have hy : (y : ℕ) < n₂ := by omega
    rw [dite_eq_left hx, dite_eq_left hy,
      hw_of_eq (q := (⟨x + 1, by omega⟩, y)) (show (x : ℕ) + 1 + y = p by omega),
      hw_of_eq (q := (x, ⟨y + 1, by omega⟩)) (show (x : ℕ) + (y + 1) = p by omega)]
    simp only [cgc]
    have hpK : (p : K) = x + y + 1 := by rw [← hxy]; push_cast; ring
    have hx1 : (x : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    have hn : (n₁ : K) - x ≠ 0 := by
      rw [sub_ne_zero]; intro h; have : (x : ℕ) = n₁ := by exact_mod_cast h.symm
      omega
    field_simp
    rw [hpK]; ring
  · have e1 : ∀ hx : (x : ℕ) < n₁,
        hw (K := K) n₁ n₂ p (⟨x + 1, by omega⟩, y) = 0 := fun hx => by
      exact hw_of_ne (show (x : ℕ) + 1 + y ≠ p by omega)
    have e2 : ∀ hy : (y : ℕ) < n₂,
        hw (K := K) n₁ n₂ p (x, ⟨y + 1, by omega⟩) = 0 := fun hy => by
      exact hw_of_ne (show (x : ℕ) + (y + 1) ≠ p by omega)
    split_ifs with hx hy hy
    · rw [e1 hx, e2 hy]; ring
    · rw [e1 hx]; ring
    · rw [e2 hy]; ring
    · ring

/-- The highest weight has `J_z = j₁ + j₂ - p`. -/
theorem pairJz_hw (p : ℕ) :
    pairJz n₁ n₂ (hw (K := K) n₁ n₂ p) = ((n₁ + n₂ : K) / 2 - p) • hw n₁ n₂ p := by
  funext ⟨x, y⟩
  rw [pairJz_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hw]
  split_ifs with h
  · have hK : (x : K) + y = p := by rw [← h]; push_cast; ring
    rw [← hK]; ring
  · ring

theorem hw_ne_zero {p : ℕ} (hp : p ≤ min n₁ n₂) : hw (K := K) n₁ n₂ p ≠ 0 := by
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  intro h
  have := congrFun h (0, ⟨p, by omega⟩)
  simp [hw, cgc] at this

variable (n₁ n₂) in
/-- **The ladder of the highest weight of weight `J = j₁ + j₂ - p` stops after `2J + 1`
vectors.** -/
theorem hw_ladder_stop {p : ℕ} (hp : p ≤ min n₁ n₂) :
    (isSU2_pair (K := K) n₁ n₂).ladder (hw n₁ n₂ p) (n₁ + n₂ - 2 * p) ≠ 0 ∧
      (isSU2_pair (K := K) n₁ n₂).ladder (hw n₁ n₂ p) (n₁ + n₂ - 2 * p + 1) = 0 := by
  have hp1 : p ≤ n₁ := le_trans hp (min_le_left _ _)
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  obtain ⟨N, hN, hN1⟩ := (isSU2_pair (K := K) n₁ n₂).exists_ladder_stop (pairJz_hw p)
    (hw_ne_zero hp)
  have h2 := (isSU2_pair (K := K) n₁ n₂).two_m_eq (pairJp_hw hp) (pairJz_hw p) hN hN1
  have hNe : N = n₁ + n₂ - 2 * p := by
    have hK : ((N : ℕ) : K) = ((n₁ + n₂ - 2 * p : ℕ) : K) := by
      rw [Nat.cast_sub (by omega), ← h2]; push_cast; ring
    exact_mod_cast hK
  subst hNe
  exact ⟨hN, hN1⟩

variable (n₁ n₂) in
/-- The labels `(p, k)` of the coupled states: `J = j₁ + j₂ - p`, `M = J - k`. -/
abbrev CGIdx := Σ p : Fin (min n₁ n₂ + 1), Fin (n₁ + n₂ - 2 * p + 1)

variable (n₁ n₂) in
/-- The coupled states `|J, M⟩` (unnormalized): the ladders of the highest weights. -/
def cgVec (i : CGIdx n₁ n₂) : Fin (n₁ + 1) × Fin (n₂ + 1) → K :=
  (isSU2_pair (K := K) n₁ n₂).ladder (hw n₁ n₂ i.1) i.2

lemma sum_mul_two_range (n : ℕ) : (∑ p ∈ Finset.range n, (p : ℤ)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

/-- The dimension count `Σ_{p ≤ min(n₁,n₂)} (n₁ + n₂ - 2p + 1) = (n₁ + 1)(n₂ + 1)`. -/
lemma sum_cg_dims (n₁ n₂ : ℕ) :
    ∑ p : Fin (min n₁ n₂ + 1), (n₁ + n₂ - 2 * (p : ℕ) + 1) = (n₁ + 1) * (n₂ + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun p => n₁ + n₂ - 2 * p + 1)]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  have h : ∀ p ∈ Finset.range (min n₁ n₂ + 1),
      ((n₁ + n₂ - 2 * p : ℕ) : ℤ) + 1 = (n₁ + n₂ + 1 : ℤ) - 2 * p := by
    intro p hp
    have := Finset.mem_range.mp hp
    have h1 : 2 * p ≤ n₁ + n₂ := by omega
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum]
  have hs := sum_mul_two_range (min n₁ n₂ + 1)
  rcases le_total n₁ n₂ with h12 | h12
  · rw [min_eq_left h12] at hs ⊢
    push_cast at hs ⊢
    linear_combination -hs
  · rw [min_eq_right h12] at hs ⊢
    push_cast at hs ⊢
    linear_combination -hs

variable (n₁ n₂) in
/-- **The Clebsch–Gordan series** `V_{j₁} ⊗ V_{j₂} ≅ ⊕_{J = |j₁ - j₂|}^{j₁ + j₂} V_J`. For each
`p ≤ min(n₁, n₂)` the vector `hw p` is a nonzero highest weight of weight `J = j₁ + j₂ - p` whose
ladder stops after `2J + 1` vectors, and the ladder vectors `|J, M⟩` of all these `J` form a basis
of `V_{j₁} ⊗ V_{j₂}`. -/
theorem cg_series :
    (∀ p ≤ min n₁ n₂, hw (K := K) n₁ n₂ p ≠ 0 ∧ pairJp n₁ n₂ (hw (K := K) n₁ n₂ p) = 0 ∧
      pairJz n₁ n₂ (hw (K := K) n₁ n₂ p) = ((n₁ + n₂ : K) / 2 - p) • hw n₁ n₂ p ∧
      (isSU2_pair (K := K) n₁ n₂).ladder (hw n₁ n₂ p) (n₁ + n₂ - 2 * p + 1) = 0) ∧
    LinearIndependent K (cgVec (K := K) n₁ n₂) ∧
    Submodule.span K (Set.range (cgVec (K := K) n₁ n₂)) = ⊤ := by
  have hJ := isSU2_pair (K := K) n₁ n₂
  set Jv : CGIdx n₁ n₂ → K := fun i => (n₁ + n₂ : K) / 2 - (i.1 : ℕ)
  have hli : LinearIndependent K (cgVec (K := K) n₁ n₂) := by
    refine linearIndependent_of_joint_eigen (isSU2_pair (K := K) n₁ n₂).S2 (pairJz n₁ n₂)
      (cgVec n₁ n₂) (fun i => Jv i * (Jv i + 1)) (fun i => Jv i - (i.2 : ℕ)) ?_ ?_ ?_ ?_
    · intro i
      have hp : (i.1 : ℕ) ≤ min n₁ n₂ := Nat.lt_succ_iff.mp i.1.2
      exact (isSU2_pair n₁ n₂).ladder_ne_zero_of_le (hw_ladder_stop n₁ n₂ hp).1
        (Nat.lt_succ_iff.mp i.2.2)
    · intro i
      have hp : (i.1 : ℕ) ≤ min n₁ n₂ := Nat.lt_succ_iff.mp i.1.2
      exact (isSU2_pair n₁ n₂).S2_ladder (pairJp_hw hp) (pairJz_hw _) _
    · intro i
      exact (isSU2_pair n₁ n₂).Sz_ladder (pairJz_hw _) _
    · rintro ⟨p, k⟩ ⟨q, l⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hp : (p : ℕ) ≤ min n₁ n₂ := Nat.lt_succ_iff.mp p.2
      have hq : (q : ℕ) ≤ min n₁ n₂ := Nat.lt_succ_iff.mp q.2
      have hsum : ((n₁ + n₂ - (p : ℕ) - q : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
      have hcast : ((n₁ + n₂ - (p : ℕ) - q : ℕ) : K) = n₁ + n₂ - p - q := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      have hpq : (p : ℕ) = q := by
        have : (Jv ⟨p, k⟩ - Jv ⟨q, l⟩) * (Jv ⟨p, k⟩ + Jv ⟨q, l⟩ + 1) = 0 := by
          linear_combination h1
        have h3 : Jv ⟨p, k⟩ + Jv ⟨q, l⟩ + 1 ≠ 0 := by
          simp only [Jv]; rw [hcast] at hsum
          convert hsum using 1; ring
        have h4 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h3)
        simp only [Jv, sub_right_inj] at h4
        exact_mod_cast h4
      have hpq' : p = q := Fin.ext hpq
      subst hpq'
      have hkl : (k : ℕ) = l := by
        have := sub_right_inj.mp h2
        exact_mod_cast this
      rw [Fin.ext hkl]
  refine ⟨fun p hp => ⟨hw_ne_zero hp, pairJp_hw hp, pairJz_hw p,
    (hw_ladder_stop n₁ n₂ hp).2⟩, hli, ?_⟩
  refine hli.span_eq_top_of_card_eq_finrank ?_
  rw [Fintype.card_sigma, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  simp only [Fintype.card_fin]
  exact sum_cg_dims n₁ n₂

/-! ### Spin–orbit coupling -/

omit [CharZero K] in
lemma IsSU2.map_S2 {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {Sp Sm Sz : End K V} (h : IsSU2 Sp Sm Sz) (φ : End K V →ₐ[K] End K V') :
    (h.map φ).S2 = φ h.S2 := by
  simp only [IsSU2.S2, map_add, map_mul]

/-- **Spin–orbit coupling** for `V_l ⊗ V_{1/2}` (`l = n/2 ≥ 1/2`): `L·S = l/2` on the multiplet
`J = l + ½` (`p = 0`) and `L·S = -(l + 1)/2` on `J = l - ½` (`p = 1`). -/
theorem spin_orbit {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p ≤ 1) (k : ℕ) :
    spinOrbit (onFst (spinSp n)) (onFst (spinSm n)) (onFst (spinSz n))
        (onSnd (spinSp 1)) (onSnd (spinSm 1)) (onSnd (spinSz 1))
        ((isSU2_pair (K := K) n 1).ladder (hw n 1 p) k) =
      (if p = 0 then (n : K) / 4 else -((n : K) / 2 + 1) / 2) •
        (isSU2_pair (K := K) n 1).ladder (hw n 1 p) k := by
  have hp' : p ≤ min n 1 := le_min (by omega) hp
  set w := (isSU2_pair (K := K) n 1).ladder (hw n 1 p) k
  set LS := spinOrbit (onFst (spinSp n)) (onFst (spinSm n)) (onFst (spinSz n))
    (onSnd (spinSp 1)) (onSnd (spinSm 1)) (onSnd (spinSz 1)) (K := K) (V := Fin (n + 1) × Fin 2 → K)
  have hS2 := (isSU2_pair (K := K) n 1).S2_ladder (pairJp_hw hp') (pairJz_hw p) k
  have hadd := IsSU2.add_S2 ((isSU2_spinRep (K := K) n).map (onFstHom (a := n + 1) (b := 2)))
    ((isSU2_spinRep (K := K) 1).map (onSndHom (a := n + 1) (b := 2))) (commutes_pair _ _ _ _ _ _)
  have e1 : ((isSU2_spinRep (K := K) n).map (onFstHom (a := n + 1) (b := 2))).S2 =
      ((n : K) / 2 * ((n : K) / 2 + 1)) • 1 := by
    rw [IsSU2.map_S2 (isSU2_spinRep (K := K) n), spinRep_S2, map_smul, map_one]
  have e2 : ((isSU2_spinRep (K := K) 1).map (onSndHom (a := n + 1) (b := 2))).S2 =
      (((1 : ℕ) : K) / 2 * (((1 : ℕ) : K) / 2 + 1)) • 1 := by
    rw [IsSU2.map_S2 (isSU2_spinRep (K := K) 1), spinRep_S2, map_smul, map_one]
  rw [e1, e2] at hadd
  have hw' := congrArg (fun T : End K (Fin (n + 1) × Fin 2 → K) => T w) hadd
  simp only [LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self] at hw'
  change (isSU2_pair (K := K) n 1).S2 w = _ at hw'
  rw [hS2] at hw'
  -- solve for `LS w`
  have key : LS w = (1 / 2 : K) • ((((n + 1 : K) / 2 - p) * ((n + 1 : K) / 2 - p + 1) -
      (n : K) / 2 * ((n : K) / 2 + 1) - (1 : K) / 2 * ((1 : K) / 2 + 1)) • w) := by
    have h2 : (2 : K) • LS w = (((n + 1 : K) / 2 - p) * ((n + 1 : K) / 2 - p + 1) -
        (n : K) / 2 * ((n : K) / 2 + 1) - (1 : K) / 2 * ((1 : K) / 2 + 1)) • w := by
      push_cast at hw'
      rw [sub_smul, sub_smul, hw']
      push_cast
      abel
    rw [← h2, smul_smul]; norm_num
  have hsc : ∀ q : ℕ, q ≤ 1 → (1 / 2 : K) * ((((n + 1 : K) / 2 - q) * ((n + 1 : K) / 2 - q + 1) -
      (n : K) / 2 * ((n : K) / 2 + 1) - (1 : K) / 2 * ((1 : K) / 2 + 1))) =
      if q = 0 then (n : K) / 4 else -((n : K) / 2 + 1) / 2 := by
    intro q hq
    interval_cases q <;> simp <;> ring
  rw [key, smul_smul, hsc p hp]

end CG

end QM
