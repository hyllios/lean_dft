/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.AngularMomentum.Ladder

/-!
# The spin-`j` representation

For `n ∈ ℕ` and `j = n/2` the spin-`j` representation is `V_j = K^{n+1}` with the unnormalized
ladder basis `e_0, …, e_n`: `S_z e_k = (j - k) e_k`, `S₋ e_k = e_{k+1}` (`e_{n+1} = 0`),
`S₊ e_0 = 0`, `S₊ e_{k+1} = (k + 1)(n - k) e_k`. It satisfies the su(2) relations, it is
irreducible, and
`S² = j(j + 1)`. Every ladder that stops at `v_n` spans a copy of `V_{n/2}`.

## Main definitions

* `QM.spinSz n`, `QM.spinSm n`, `QM.spinSp n`: the operators on `Fin (n + 1) → K`.

## Main results

* `isSU2_spinRep`: the su(2) relations.
* `spinRep_S2`: `S² = j(j + 1)`.
* `spinRep_irreducible`: every subspace invariant under `S₊` and `S₋` is `⊥` or `⊤`.
* `IsSU2.exists_spinRep_iso`: a ladder that stops at `v_n` spans a copy of `V_{n/2}`.
-/

namespace QM

open Module

variable {K : Type*} [Field K] [CharZero K] (n : ℕ)

/-- `S_z e_k = (n/2 - k) e_k`. -/
def spinSz : End K (Fin (n + 1) → K) where
  toFun v i := ((n : K) / 2 - i) * v i
  map_add' _ _ := by funext i; simp [mul_add]
  map_smul' _ _ := by funext i; simp; ring

/-- `S₋ e_k = e_{k+1}`, that is `(S₋ v)_i = v_{i-1}`. -/
def spinSm : End K (Fin (n + 1) → K) where
  toFun v i := if h : i = 0 then 0 else v ⟨i - 1, by omega⟩
  map_add' _ _ := by funext i; by_cases h : i = 0 <;> simp [h]
  map_smul' _ _ := by funext i; by_cases h : i = 0 <;> simp [h]

/-- `S₊ e_{k+1} = (k + 1)(n - k) e_k`, that is `(S₊ v)_i = (i + 1)(n - i) v_{i+1}`. -/
def spinSp : End K (Fin (n + 1) → K) where
  toFun v i := if h : (i : ℕ) < n then (((i : K) + 1) * ((n : K) - i)) * v ⟨i + 1, by omega⟩ else 0
  map_add' _ _ := by funext i; by_cases h : (i : ℕ) < n <;> simp [h, mul_add]
  map_smul' _ _ := by funext i; by_cases h : (i : ℕ) < n <;> simp [h]; ring

variable {n}

lemma spinSz_apply (v : Fin (n + 1) → K) (i : Fin (n + 1)) :
    spinSz n v i = ((n : K) / 2 - i) * v i := rfl

omit [CharZero K] in
lemma spinSm_apply (v : Fin (n + 1) → K) (i : Fin (n + 1)) :
    spinSm n v i = if h : i = 0 then 0 else v ⟨i - 1, by omega⟩ := rfl

omit [CharZero K] in
lemma spinSp_apply (v : Fin (n + 1) → K) (i : Fin (n + 1)) :
    spinSp n v i =
      if h : (i : ℕ) < n then (((i : K) + 1) * ((n : K) - i)) * v ⟨i + 1, by omega⟩ else 0 := rfl

lemma spinSp_spinSm (v : Fin (n + 1) → K) (i : Fin (n + 1)) :
    spinSp n (spinSm n v) i = (((i : K) + 1) * ((n : K) - i)) * v i := by
  rw [spinSp_apply]
  split_ifs with h
  · rw [spinSm_apply, dite_eq_right (fun h' => by simpa using congrArg Fin.val h')]
    congr 2
  · have : (i : ℕ) = n := by omega
    rw [show ((i : ℕ) : K) = n by exact_mod_cast this]; ring

lemma spinSm_spinSp (v : Fin (n + 1) → K) (i : Fin (n + 1)) :
    spinSm n (spinSp n v) i = ((i : K) * ((n : K) - i + 1)) * v i := by
  rw [spinSm_apply]
  split_ifs with h
  · subst h; simp
  · have hi : (i : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
    rw [spinSp_apply, dite_eq_left (by simp; omega)]
    have h3 : (⟨((i : ℕ) - 1 : ℕ) + 1, by omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp; omega)
    simp only [h3]
    have hc : (((i : ℕ) - 1 : ℕ) : K) = (i : K) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hc]; ring

variable (n) in
/-- **The spin-`j` representation satisfies the su(2) relations.** -/
theorem isSU2_spinRep : IsSU2 (spinSp n : End K _) (spinSm n) (spinSz n) where
  comm_pm := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, spinSp_spinSm, spinSm_spinSp, spinSz_apply]
    ring
  comm_zp := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, Pi.sub_apply, spinSp_apply,
      spinSz_apply]
    split_ifs with h
    · push_cast; ring
    · ring
  comm_zm := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.neg_apply, Pi.sub_apply,
      Pi.neg_apply, spinSm_apply, spinSz_apply]
    by_cases h : i = 0
    · simp [h]
    · have hi : (i : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
      rw [dite_eq_right h, dite_eq_right h]
      have hc : (((i : ℕ) - 1 : ℕ) : K) = (i : K) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      simp only [hc]; ring

/-! ### The total spin -/

variable (n) in
/-- **`S² = j(j + 1)`** on the spin-`j` representation. -/
theorem spinRep_S2 : (isSU2_spinRep (K := K) n).S2 = ((n : K) / 2 * ((n : K) / 2 + 1)) • 1 := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [IsSU2.S2, LinearMap.add_apply, mul_apply_eq_comp, Pi.add_apply, spinSm_spinSp,
    spinSz_apply, LinearMap.smul_apply, one_apply_eq_self, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Basis vectors -/

/-- The basis vector `e_k`. -/
def spinE (k : Fin (n + 1)) : Fin (n + 1) → K := Pi.single k 1

lemma spinSz_spinE (k : Fin (n + 1)) :
    spinSz n (spinE k) = ((n : K) / 2 - k) • (spinE k : Fin (n + 1) → K) := by
  funext i
  simp only [spinSz_apply, spinE, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

omit [CharZero K] in
lemma spinSm_spinE (k : Fin (n + 1)) (hk : (k : ℕ) < n) :
    spinSm n (spinE k) = (spinE ⟨k + 1, by omega⟩ : Fin (n + 1) → K) := by
  funext i
  rw [spinSm_apply]
  by_cases h0 : i = 0
  · rw [dite_eq_left h0, spinE, Pi.single_eq_of_ne (fun h => by
      have := congrArg Fin.val h; rw [h0] at this; simp at this)]
  · rw [dite_eq_right h0]
    have hi : (i : ℕ) ≠ 0 := fun h' => h0 (Fin.ext h')
    by_cases h : (i : ℕ) = k + 1
    · have e1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 1)) = k := Fin.ext (by simp; omega)
      have e2 : i = ⟨k + 1, by omega⟩ := Fin.ext h
      rw [e1, e2]; simp [spinE]
    · have e1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 1)) ≠ k := fun h' => by
        have := congrArg Fin.val h'; simp at this; omega
      have e2 : i ≠ ⟨k + 1, by omega⟩ := fun h' => h (congrArg Fin.val h')
      simp [spinE, Pi.single_eq_of_ne e1, Pi.single_eq_of_ne e2]

omit [CharZero K] in
lemma spinSm_spinE_last : spinSm n (spinE (Fin.last n)) = (0 : Fin (n + 1) → K) := by
  funext i
  rw [spinSm_apply]
  split_ifs with h0
  · rfl
  · have hi : (i : ℕ) ≠ 0 := fun h' => h0 (Fin.ext h')
    have e1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := fun h' => by
      have := congrArg Fin.val h'; simp at this; omega
    simp [spinE, Pi.single_eq_of_ne e1]

omit [CharZero K] in
lemma spinSp_spinE_zero : spinSp n (spinE 0) = (0 : Fin (n + 1) → K) := by
  funext i
  rw [spinSp_apply]
  split_ifs with h
  · have e : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1)) ≠ 0 := fun h' => by
      have := congrArg Fin.val h'; simp at this
    simp [spinE]
  · rfl

omit [CharZero K] in
lemma spinSp_spinE_succ (k : ℕ) (hk : k < n) :
    spinSp n (spinE ⟨k + 1, by omega⟩) =
      (((k : K) + 1) * ((n : K) - k)) • (spinE ⟨k, by omega⟩ : Fin (n + 1) → K) := by
  have hk' : k < n + 1 := by omega
  funext i
  rw [spinSp_apply, Pi.smul_apply, smul_eq_mul]
  simp only [spinE]
  by_cases h : (i : ℕ) = k
  · have e : i = ⟨k, hk'⟩ := Fin.ext h
    subst e
    simp [hk]
  · rw [Pi.single_eq_of_ne (fun h' => h (congrArg Fin.val h')), mul_zero]
    split_ifs with h2
    · rw [Pi.single_eq_of_ne (fun h' => by have := congrArg Fin.val h'; simp at this; omega),
        mul_zero]
    · rfl

/-! ### Irreducibility -/

/-- An invariant subspace that contains a nonzero vector contains a basis vector. -/
lemma exists_spinE_mem {W : Submodule K (Fin (n + 1) → K)}
    (hz : ∀ w ∈ W, spinSz n w ∈ W) :
    ∀ w ∈ W, w ≠ 0 → ∃ k, (spinE k : Fin (n + 1) → K) ∈ W := by
  classical
  intro w
  induction h : (Finset.univ.filter fun i => w i ≠ 0).card using Nat.strong_induction_on
    generalizing w with
  | _ c ih =>
  intro hw hw0
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hc; push Not at hc; exact hw0 (funext hc)
  by_cases hone : ∀ i, i ≠ k → w i = 0
  · refine ⟨k, ?_⟩
    have : w = w k • (spinE k : Fin (n + 1) → K) := by
      funext i
      by_cases hi : i = k
      · subst hi; simp [spinE]
      · simp [spinE, Pi.single_eq_of_ne hi, hone i hi]
    rw [this] at hw
    have := W.smul_mem (w k)⁻¹ hw
    rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at this
  · push Not at hone
    obtain ⟨l, hlk, hl⟩ := hone
    -- `w' = (S_z - λ_k) w` kills the `k` coordinate and keeps the `l` coordinate
    set w' := spinSz n w - ((n : K) / 2 - k) • w with hw'
    have hw'W : w' ∈ W := W.sub_mem (hz w hw) (W.smul_mem _ hw)
    have hw'i : ∀ i, w' i = ((k : K) - i) * w i := by
      intro i; simp [hw', spinSz_apply]; ring
    have hlk' : ((k : K) - l) ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hlk (Fin.ext (by exact_mod_cast h.symm))
    have hw'0 : w' ≠ 0 := fun h0 => by
      have := congrFun h0 l
      rw [hw'i] at this
      exact hl ((mul_eq_zero.mp this).resolve_left hlk')
    refine ih _ ?_ w' rfl hw'W hw'0
    rw [← h]
    apply Finset.card_lt_card
    refine ⟨fun i hi => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro h0; apply hi; rw [hw'i, h0, mul_zero]
    · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      apply this; rw [hw'i, sub_self, zero_mul]

/-- **The spin-`j` representation is irreducible**: a subspace invariant under `S₊` and `S₋` is
`⊥` or `⊤`. -/
theorem spinRep_irreducible (W : Submodule K (Fin (n + 1) → K))
    (hp : ∀ w ∈ W, spinSp n w ∈ W) (hm : ∀ w ∈ W, spinSm n w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hz : ∀ w ∈ W, spinSz n w ∈ W := by
    intro w hw
    have h := congrArg (fun T : End K _ => T w) (isSU2_spinRep (K := K) n).comm_pm
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply] at h
    have : (2 : K) • spinSz n w ∈ W := h ▸ W.sub_mem (hp _ (hm w hw)) (hm _ (hp w hw))
    have := W.smul_mem (2 : K)⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at this
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨k, hk⟩ := exists_spinE_mem hz w hw hw0
  -- going down with `S₊`
  have hdown : ∀ j : ℕ, ∀ hj : j ≤ (k : ℕ),
      (spinE ⟨(k : ℕ) - j, by omega⟩ : Fin (n + 1) → K) ∈ W := by
    intro j
    induction j with
    | zero => intro _; simpa using hk
    | succ j ih =>
      intro hj
      have h1 := hp _ (ih (by omega))
      have e : (⟨(k : ℕ) - j, by omega⟩ : Fin (n + 1)) = ⟨((k : ℕ) - (j + 1)) + 1, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, spinSp_spinE_succ _ (by omega)] at h1
      have hc : (((k - (j + 1) : ℕ) : K) + 1) * ((n : K) - (k - (j + 1) : ℕ)) ≠ 0 := by
        refine mul_ne_zero (Nat.cast_add_one_ne_zero _) ?_
        rw [sub_ne_zero]; intro h
        have : ((k : ℕ) - (j + 1) : ℕ) = n := by exact_mod_cast h.symm
        omega
      have := W.smul_mem (((((k : ℕ) - (j + 1) : ℕ) : K) + 1) *
        ((n : K) - (((k : ℕ) - (j + 1) : ℕ) : K)))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have h0 : (spinE 0 : Fin (n + 1) → K) ∈ W := by
    have := hdown k le_rfl
    simpa using this
  -- going up with `S₋`
  have hup : ∀ j : ℕ, ∀ hj : j ≤ n, (spinE ⟨j, by omega⟩ : Fin (n + 1) → K) ∈ W := by
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ j ih =>
      intro hj
      have := hm _ (ih (by omega))
      rwa [spinSm_spinE _ (by simp; omega)] at this
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, v i • (spinE i : Fin (n + 1) → K) := by
    funext x; simp [spinE, Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact W.sum_mem fun i _ => W.smul_mem _ (by simpa using hup i (by omega))

/-! ### Every stopped ladder is a copy of `V_j` -/

omit [CharZero K] in
lemma single_eq_smul_spinE (i : Fin (n + 1)) (x : K) :
    (Pi.single i x : Fin (n + 1) → K) = x • spinE i := by
  funext l; by_cases h : l = i
  · subst h; simp [spinE]
  · simp [spinE, Pi.single_eq_of_ne h]

/-- **Every stopped ladder spans a copy of `V_{N/2}`**: if `v` is a highest-weight vector whose
ladder
stops at `v_N`, the map `e_k ↦ v_k` is injective, its range is the span of the ladder, and it
intertwines `S₊`, `S₋` and `S_z`. -/
theorem IsSU2.exists_spinRep_iso {V : Type*} [AddCommGroup V] [Module K V] {Sp Sm Sz : End K V}
    (h : IsSU2 Sp Sm Sz) {v : V} {m : K} (hp : Sp v = 0) (hz : Sz v = m • v) {N : ℕ}
    (hN : h.ladder v N ≠ 0) (hN1 : h.ladder v (N + 1) = 0) :
    ∃ φ : (Fin (N + 1) → K) →ₗ[K] V, Function.Injective φ ∧
      LinearMap.range φ = h.ladderSpan (v := v) N ∧
      φ ∘ₗ spinSp N = Sp ∘ₗ φ ∧ φ ∘ₗ spinSm N = Sm ∘ₗ φ ∧ φ ∘ₗ spinSz N = Sz ∘ₗ φ := by
  classical
  have hm : 2 * m = N := h.two_m_eq hp hz hN hN1
  set φ := Fintype.linearCombination K (fun k : Fin (N + 1) => h.ladder v k)
  have hφ : ∀ k, φ (spinE k) = h.ladder v k := fun k => by
    rw [spinE, Fintype.linearCombination_apply_single, one_smul]
  have hext : ∀ {f g : (Fin (N + 1) → K) →ₗ[K] V}, (∀ k, f (spinE k) = g (spinE k)) → f = g := by
    intro f g hfg
    refine LinearMap.pi_ext fun i x => ?_
    rw [single_eq_smul_spinE, map_smul, map_smul, hfg]
  refine ⟨φ, linearIndependent_iff_injective_fintypeLinearCombination.mp
    (h.ladder_linearIndependent hz hN), Fintype.range_linearCombination K _, ?_, ?_, ?_⟩
  · refine hext fun k => ?_
    simp only [LinearMap.comp_apply]
    rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
    · have e : k = 0 := Fin.ext hk
      subst e
      rw [spinSp_spinE_zero, map_zero, hφ]
      exact (h.Sp_ladder_zero hp).symm
    · obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_lt hk
      have hk'N : k' + 1 < N + 1 := by omega
      have e : k = ⟨k' + 1, hk'N⟩ := Fin.ext (by simp; omega)
      subst e
      rw [spinSp_spinE_succ k' (by omega), map_smul, hφ, hφ]
      rw [h.Sp_ladder_succ hp hz k', hm]
  · refine hext fun k => ?_
    simp only [LinearMap.comp_apply]
    rw [hφ, ← h.ladder_succ]
    by_cases hk : (k : ℕ) < N
    · rw [spinSm_spinE k hk, hφ]
    · have e : k = Fin.last N := Fin.ext (by simp; omega)
      subst e
      rw [spinSm_spinE_last, map_zero]
      simpa using hN1.symm
  · refine hext fun k => ?_
    simp only [LinearMap.comp_apply]
    rw [spinSz_spinE, map_smul, hφ, h.Sz_ladder hz, show (N : K) / 2 = m by
      rw [← hm]; ring]

end QM
