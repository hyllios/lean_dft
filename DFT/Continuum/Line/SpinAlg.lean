/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.LiebMattisSpin

/-!
# The spin algebra of `N` spin-½ particles

Spin states are functions `u : SpinC n → V` on spin configurations `s : Fin N → Bool` (`true` is
spin up), with values in a real vector space `V` (later: spatial wave functions).

* `nup s`, `Mz s = nup s - N/2`: the number of spins up and the `S_z` eigenvalue.
* `Sp`, `Sm`, `Sz`: `S₊ = Σ_i σ_i⁺`, `S₋ = Σ_i σ_i⁻` and `S_z`, as linear maps;
  `S2 = ½ (S₊S₋ + S₋S₊) + S_z²` is the total spin squared `S_x² + S_y² + S_z²`.
* `comm_Sp_Sm`, `comm_Sz_Sp`, `comm_Sz_Sm`: `[S₊, S₋] = 2 S_z`, `[S_z, S₊] = S₊`,
  `[S_z, S₋] = -S₋`; hence `S2_comm_Sp`: `[S², S₊] = 0`, and `S2_eq`: `S² = S₋S₊ + S_z² + S_z`.
* `adj_Sp`: `S₊` and `S₋` are adjoint for any bilinear form summed over configurations.
* `Pc c`: the projection on the sector `nup = c`; `Sp_Pc`, `S2_Pc`.
* `rel σ s = s ∘ σ`: relabelling of configurations; `Sp_rel`.
-/

namespace DFT.Continuum.Line

open Function

variable {n : ℕ}

/-- Spin configurations of `n + 1` particles; `true` is spin up. -/
abbrev SpinC (n : ℕ) := Fin (n + 1) → Bool

/-- The number of spins up. -/
def nup (s : SpinC n) : ℕ := (Finset.univ.filter fun i => s i = true).card

/-- The `S_z` eigenvalue `nup - N/2`. -/
noncomputable def Mz (s : SpinC n) : ℝ := (nup s : ℝ) - ((n : ℝ) + 1) / 2

lemma nup_update_false {s : SpinC n} {i : Fin (n + 1)} (h : s i = true) :
    nup (update s i false) + 1 = nup s := by
  have e : (Finset.univ.filter fun j => update s i false j = true) =
      (Finset.univ.filter fun j => s j = true).erase i := by
    ext j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [nup, e, Finset.card_erase_of_mem (by simpa using h)]
  have : 0 < (Finset.univ.filter fun j => s j = true).card :=
    Finset.card_pos.2 ⟨i, by simpa using h⟩
  rw [nup]; omega

lemma nup_update_true {s : SpinC n} {i : Fin (n + 1)} (h : s i = false) :
    nup (update s i true) = nup s + 1 := by
  have e : (Finset.univ.filter fun j => update s i true j = true) =
      insert i (Finset.univ.filter fun j => s j = true) := by
    ext j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [nup, e, Finset.card_insert_of_notMem (by simp [h]), nup]

lemma Mz_update_false {s : SpinC n} {i : Fin (n + 1)} (h : s i = true) :
    Mz (update s i false) = Mz s - 1 := by
  have := nup_update_false h
  simp only [Mz]
  have : (nup (update s i false) : ℝ) + 1 = nup s := by exact_mod_cast this
  linarith

lemma Mz_update_true {s : SpinC n} {i : Fin (n + 1)} (h : s i = false) :
    Mz (update s i true) = Mz s + 1 := by
  simp only [Mz, nup_update_true h]; push_cast; ring

lemma nup_le (s : SpinC n) : nup s ≤ n + 1 :=
  (Finset.card_le_univ _).trans (by simp)

lemma upd_true {s : SpinC n} {i : Fin (n + 1)} (h : s i = true) : update s i true = s := by
  conv_lhs => rw [← h]
  exact update_eq_self i s

lemma upd_false {s : SpinC n} {i : Fin (n + 1)} (h : s i = false) : update s i false = s := by
  conv_lhs => rw [← h]
  exact update_eq_self i s

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma sum_ite_up (s : SpinC n) (c : V) :
    ∑ i, (if s i = true then c else 0) = (nup s : ℝ) • c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nup,
    Nat.cast_smul_eq_nsmul]

lemma sum_ite_down (s : SpinC n) (c : V) :
    ∑ i, (if s i = true then 0 else c) = ((n : ℝ) + 1 - nup s) • c := by
  have h : ∑ i, (if s i = true then 0 else c) + ∑ i, (if s i = true then c else 0) =
      ∑ _i : Fin (n + 1), c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  rw [sum_ite_up, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  rw [eq_sub_of_add_eq h, sub_smul, ← Nat.cast_smul_eq_nsmul ℝ]
  push_cast; rfl

omit [Module ℝ V] in
/-- Diagonal and off-diagonal parts of double sums. -/
lemma sum_sub_offdiag {m : ℕ} {a b : Fin m → Fin m → V} (h : ∀ i j, i ≠ j → a i j = b j i) :
    ∑ i, ∑ j, a i j - ∑ i, ∑ j, b i j = ∑ i, a i i - ∑ i, b i i := by
  have hsplit : ∀ c : Fin m → Fin m → V, ∑ i, ∑ j, c i j =
      ∑ i, c i i + ∑ i, ∑ j, (if j = i then 0 else c i j) := by
    intro c
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, c i j = ∑ j, (if j = i then c i j else 0) + ∑ j, (if j = i then 0 else c i j) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    rw [this, Finset.sum_ite_eq' Finset.univ i (fun j => c i j)]
    simp
  have hoff : ∑ i, ∑ j, (if j = i then 0 else a i j) = ∑ i, ∑ j, (if j = i then 0 else b i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : j = i
    · subst hij; simp
    · simp only [hij, Ne.symm hij, ite_false, h i j (Ne.symm hij)]
  rw [hsplit a, hsplit b, hoff]; abel

/-! ### The operators -/

/-- `S₊`: `(S₊ u)(s) = Σ_{i : s_i = ↑} u(s with i ↓)`. -/
def Sp : (SpinC n → V) →ₗ[ℝ] (SpinC n → V) where
  toFun u s := ∑ i, if s i = true then u (update s i false) else 0
  map_add' u u' := by
    funext s; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  map_smul' c u := by
    funext s; simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- `S₋`: `(S₋ u)(s) = Σ_{i : s_i = ↓} u(s with i ↑)`. -/
def Sm : (SpinC n → V) →ₗ[ℝ] (SpinC n → V) where
  toFun u s := ∑ i, if s i = true then 0 else u (update s i true)
  map_add' u u' := by
    funext s; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  map_smul' c u := by
    funext s; simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- `S_z`. -/
noncomputable def Sz : (SpinC n → V) →ₗ[ℝ] (SpinC n → V) where
  toFun u s := Mz s • u s
  map_add' u u' := by funext s; simp [smul_add]
  map_smul' c u := by funext s; simp [smul_comm (Mz s) c]

/-- The total spin squared `S² = ½ (S₊S₋ + S₋S₊) + S_z²`. -/
noncomputable def S2 : (SpinC n → V) →ₗ[ℝ] (SpinC n → V) :=
  (1 / 2 : ℝ) • (Sp ∘ₗ Sm + Sm ∘ₗ Sp) + Sz ∘ₗ Sz

lemma Sp_apply (u : SpinC n → V) (s : SpinC n) :
    Sp u s = ∑ i, if s i = true then u (update s i false) else 0 := rfl

lemma Sm_apply (u : SpinC n → V) (s : SpinC n) :
    Sm u s = ∑ i, if s i = true then 0 else u (update s i true) := rfl

lemma Sz_apply (u : SpinC n → V) (s : SpinC n) : Sz u s = Mz s • u s := rfl

/-! ### Commutators -/

/-- **`[S₊, S₋] = 2 S_z`.** -/
lemma comm_Sp_Sm (u : SpinC n → V) :
    Sp (Sm u) - Sm (Sp u) = (2 : ℝ) • Sz u := by
  funext s
  simp only [Pi.sub_apply, Pi.smul_apply, Sp_apply, Sm_apply, Sz_apply]
  set a : Fin (n + 1) → Fin (n + 1) → V := fun i j => if s i = true then
    (if update s i false j = true then 0 else u (update (update s i false) j true)) else 0
  set b : Fin (n + 1) → Fin (n + 1) → V := fun i j => if s i = true then 0 else
    (if update s i true j = true then u (update (update s i true) j false) else 0)
  have ea : ∀ i, (if s i = true then ∑ j, (if update s i false j = true then 0 else
      u (update (update s i false) j true)) else 0) = ∑ j, a i j := fun i => by
    simp only [a]; split_ifs <;> simp
  have eb : ∀ i, (if s i = true then 0 else ∑ j, (if update s i true j = true then
      u (update (update s i true) j false) else 0)) = ∑ j, b i j := fun i => by
    simp only [b]; split_ifs <;> simp
  simp only [ea, eb]
  rw [sum_sub_offdiag (a := a) (b := b) fun i j hij => ?_]
  · have da : ∀ i, a i i = if s i = true then u s else 0 := fun i => by
      simp only [a]
      by_cases hi : s i = true
      · simp [hi, update_idem, upd_true hi]
      · simp [hi]
    have db : ∀ i, b i i = if s i = true then 0 else u s := fun i => by
      simp only [b]
      by_cases hi : s i = true
      · simp [hi]
      · have hi' : s i = false := by simpa using hi
        simp [hi, update_idem, upd_false hi']
    simp only [da, db, sum_ite_up, sum_ite_down, ← sub_smul, smul_smul, Mz]
    congr 1; ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [a, b, update_of_ne hji, update_of_ne hij]
    by_cases hsi : s i = true <;> by_cases hsj : s j = true <;>
      simp [hsi, hsj, update_comm hij]

/-- **`[S_z, S₊] = S₊`.** -/
lemma comm_Sz_Sp (u : SpinC n → V) : Sz (Sp u) - Sp (Sz u) = Sp u := by
  funext s
  simp only [Pi.sub_apply, Sp_apply, Sz_apply, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : s i = true
  · simp only [hi, ↓reduceIte, Mz_update_false hi]
    rw [sub_smul, one_smul]; abel
  · simp [hi]

/-- **`[S_z, S₋] = -S₋`.** -/
lemma comm_Sz_Sm (u : SpinC n → V) : Sz (Sm u) - Sm (Sz u) = -Sm u := by
  funext s
  simp only [Pi.sub_apply, Pi.neg_apply, Sm_apply, Sz_apply, Finset.smul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : s i = true
  · simp [hi]
  · have hi' : s i = false := by simpa using hi
    rw [ite_eq_right hi, ite_eq_right hi, Mz_update_true hi', add_smul, one_smul]; abel

/-! ### Consequences in the endomorphism ring -/

lemma comm_Sp_Sm' : (Sp : Module.End ℝ (SpinC n → V)) * Sm - Sm * Sp = (2 : ℝ) • Sz :=
  LinearMap.ext comm_Sp_Sm

lemma comm_Sz_Sp' : (Sz : Module.End ℝ (SpinC n → V)) * Sp - Sp * Sz = Sp :=
  LinearMap.ext comm_Sz_Sp

lemma S2_def' : (S2 : Module.End ℝ (SpinC n → V)) = (1 / 2 : ℝ) • (Sp * Sm + Sm * Sp) + Sz * Sz :=
  rfl

/-- **`S² = S₋S₊ + S_z² + S_z`.** -/
lemma S2_eq : (S2 : Module.End ℝ (SpinC n → V)) = Sm * Sp + Sz * Sz + Sz := by
  rw [S2_def']
  have h := comm_Sp_Sm' (n := n) (V := V)
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  module

/-- **`[S², S₊] = 0`.** -/
lemma S2_comm_Sp : (S2 : Module.End ℝ (SpinC n → V)) * Sp = Sp * S2 := by
  rw [S2_eq]
  have h1 := comm_Sp_Sm' (n := n) (V := V)
  have h2 := comm_Sz_Sp' (n := n) (V := V)
  set P : Module.End ℝ (SpinC n → V) := Sp
  set M : Module.End ℝ (SpinC n → V) := Sm
  set Z : Module.End ℝ (SpinC n → V) := Sz
  rw [two_smul, sub_eq_iff_eq_add] at h1
  rw [sub_eq_iff_eq_add] at h2
  have hX : M * P * P = P * (M * P) - (Z * P + Z * P) := by
    rw [← mul_assoc P M P, h1]; noncomm_ring
  have h3 : Z * (Z * P) = Z * P + Z * P * Z := by
    conv_lhs => rw [h2]
    rw [mul_add, ← mul_assoc]
  calc (M * P + Z * Z + Z) * P = M * P * P + Z * (Z * P) + Z * P := by noncomm_ring
    _ = P * (M * P) - (Z * P + Z * P) + Z * (Z * P) + Z * P := by rw [hX]
    _ = P * (M * P) - (Z * P + Z * P) + (Z * P + Z * P * Z) + Z * P := by rw [h3]
    _ = P * (M * P) - ((P + P * Z) + (P + P * Z)) +
          ((P + P * Z) + (P + P * Z) * Z) + (P + P * Z) := by rw [h2]
    _ = P * (M * P + Z * Z + Z) := by noncomm_ring

/-! ### Adjointness -/

/-- **`S₊` and `S₋` are adjoint** for any bilinear form summed over configurations. -/
lemma adj_Sp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v : SpinC n → V) :
    ∑ s, B (Sp u s) (v s) = ∑ s, B (u s) (Sm v s) := by
  have L : ∀ s : SpinC n, B (Sp u s) (v s) =
      ∑ i, (if s i = true then B (u (update s i false)) (v s) else 0) := fun s => by
    rw [Sp_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have R : ∀ s : SpinC n, B (u s) (Sm v s) =
      ∑ i, (if s i = true then 0 else B (u s) (v (update s i true))) := fun s => by
    rw [Sm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  simp only [L, R]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- reindex by flipping spin `i`
  have hinv : Function.Involutive fun s : SpinC n => update s i (!s i) := fun s => by
    funext j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [← Equiv.sum_comp (hinv.toPerm _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Function.Involutive.coe_toPerm]
  by_cases ht : t i = true
  · simp [ht]
  · have ht' : t i = false := by simpa using ht
    have h1 : update (update t i true) i false = t := by rw [update_idem]; exact upd_false ht'
    simp [ht', h1]

/-! ### Sectors -/

/-- The projection on the sector with `c` spins up. -/
def Pc (c : ℕ) : (SpinC n → V) →ₗ[ℝ] (SpinC n → V) where
  toFun u s := if nup s = c then u s else 0
  map_add' u u' := by funext s; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r u := by funext s; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

lemma Pc_apply (c : ℕ) (u : SpinC n → V) (s : SpinC n) : Pc c u s = if nup s = c then u s else 0 :=
  rfl

lemma Sp_Pc (c : ℕ) (u : SpinC n → V) : Sp (Pc c u) = Pc (c + 1) (Sp u) := by
  funext s
  simp only [Sp_apply, Pc_apply]
  split_ifs with hs
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : s i = true
    · have := nup_update_false hi; simp [hi]; omega
    · simp [hi]
  · refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : s i = true
    · have := nup_update_false hi
      simp only [hi, ite_true]
      rw [ite_eq_right (by omega)]
    · simp [hi]

lemma Sm_Pc (c : ℕ) (u : SpinC n → V) :
    Sm (Pc (c + 1) u) = Pc c (Sm u) := by
  funext s
  simp only [Sm_apply, Pc_apply]
  split_ifs with hs
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : s i = true
    · simp [hi]
    · have hi' : s i = false := by simpa using hi
      simp [hi, nup_update_true hi', hs]
  · refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : s i = true
    · simp [hi]
    · have hi' : s i = false := by simpa using hi
      simp [hi, nup_update_true hi', hs]

lemma Sz_Pc (c : ℕ) (u : SpinC n → V) : Sz (Pc c u) = Pc c (Sz u) := by
  funext s; simp only [Sz_apply, Pc_apply]; split_ifs <;> simp

lemma Sm_Pc_zero (u : SpinC n → V) : Sm (Pc 0 u) = 0 := by
  funext s
  simp only [Sm_apply, Pc_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : s i = true
  · simp [hi]
  · have hi' : s i = false := by simpa using hi
    simp [hi, nup_update_true hi']

lemma Pc_Pc_ne {c d : ℕ} (h : c ≠ d) (u : SpinC n → V) : Pc c (Pc d u) = 0 := by
  funext s; simp only [Pc_apply, Pi.zero_apply]; split_ifs with h1 h2 <;> simp_all

lemma Pc_Pc (c : ℕ) (u : SpinC n → V) : Pc c (Pc c u) = Pc c u := by
  funext s; simp only [Pc_apply]; split_ifs <;> simp

/-- **`S²` preserves the sectors.** -/
lemma S2_Pc (c : ℕ) (u : SpinC n → V) : S2 (Pc c u) = Pc c (S2 u) := by
  have hSmSp : Sm (Sp (Pc c u)) = Pc c (Sm (Sp u)) := by rw [Sp_Pc, Sm_Pc]
  have hSpSm : Sp (Sm (Pc c u)) = Pc c (Sp (Sm u)) := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · rw [Sm_Pc_zero, map_zero]
      funext s
      simp only [Pi.zero_apply, Pc_apply, Sp_apply, Sm_apply]
      split_ifs with hs
      · symm
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : s i = true
        · have := nup_update_false hi; omega
        · simp [hi]
      · rfl
    · obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      rw [Sm_Pc, Sp_Pc]
  change (1 / 2 : ℝ) • (Sp (Sm (Pc c u)) + Sm (Sp (Pc c u))) + Sz (Sz (Pc c u)) =
    Pc c ((1 / 2 : ℝ) • (Sp (Sm u) + Sm (Sp u)) + Sz (Sz u))
  rw [hSmSp, hSpSm, Sz_Pc, Sz_Pc, map_add, map_smul, map_add]

/-! ### Relabelling -/

/-- Relabelling of spin configurations. -/
def rel (σ : Equiv.Perm (Fin (n + 1))) (s : SpinC n) : SpinC n := fun i => s (σ i)

lemma rel_update (σ : Equiv.Perm (Fin (n + 1))) (s : SpinC n) (i : Fin (n + 1)) (b : Bool) :
    update (rel σ s) i b = rel σ (update s (σ i) b) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [rel]
  · rw [update_of_ne hj]; simp only [rel]
    rw [update_of_ne (fun h => hj (σ.injective h))]

lemma nup_eq_sum (s : SpinC n) : nup s = ∑ i, if s i = true then 1 else 0 :=
  Finset.card_filter _ _

lemma nup_rel (σ : Equiv.Perm (Fin (n + 1))) (s : SpinC n) : nup (rel σ s) = nup s := by
  rw [nup_eq_sum, nup_eq_sum]
  exact Equiv.sum_comp σ (fun i => if s i = true then 1 else 0)

lemma Sp_rel (σ : Equiv.Perm (Fin (n + 1))) (u : SpinC n → V) (s : SpinC n) :
    Sp u (rel σ s) = Sp (fun t => u (rel σ t)) s := by
  simp only [Sp_apply, rel_update]
  exact Equiv.sum_comp σ (fun j => if s j = true then u (rel σ (update s j false)) else 0)

end DFT.Continuum.Line
