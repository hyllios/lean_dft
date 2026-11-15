/-
Copyright (c) 2026 Miguel A. L. Marques, Stefano Pittalis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/
import DFT.Lattice.Bridge.Square

/-!
# The square with edge-dependent hopping: zero patterns need a symmetry of the hopping

Two spinless fermions on the 4-cycle `0 – 1 – 2 – 3 – 0` with real symmetric hopping `t a b` on the
edges, any potential and any configuration-diagonal interaction (`H0Fw sqG t Vint`). In the basis
`cfg` = `01, 02, 03, 12, 13, 23` the hopping part is the explicit matrix `hopSq t` (`H0Fw_square`,
with the fermionic signs). Consequences:

* `square_zero_pattern_hopping`: an eigenvector that vanishes on `01` and `23`, with `ψ(02)` and
  `ψ(13)` not both zero, exists only if `t₁₂² = t₃₀²` (the zero pattern of Penz and van Leeuwen's
  `Ψ_A`);
  `square_zero_pattern_hopping'`: vanishing on `03` and `12` instead needs `t₀₁² = t₂₃²`;
* `square_shared_hopping_sharp`: a ground state shared by `v` and `v + ε (1, 1, −1, −1)`, `ε ≠ 0`,
  exists only if `t₁₂² = t₃₀²` or `t₀₁ = t₂₃ = 0`; with all four hoppings nonzero only
  `t₁₂² = t₃₀²` is left. If `ψ` is supported in `{03, 12}`, the basis state at a configuration
  where it is nonzero is a ground state too (`offdiag_zero_of_diag_ground`), so no hopping leaves
  it;
  `square_shared_hopping`: the weaker form `t₁₂² = t₃₀²` or `t₀₁² = t₂₃²`.

These are necessary conditions on the hopping; nothing here says they are sufficient.

Also `hamN_H0Fw_row`, `hamN_H0Fw_entry`, `sq_eq_sq_of_block`, `shift_sq_cfg`.
-/

namespace DFT

open Matrix

namespace Bridge.Square

/-- The hopping part of `H0Fw sqG t 0` in the basis `cfg`. -/
def hopSq (t : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, -t 1 2, 0, 0, t 0 3, 0;
     -t 2 1, 0, -t 2 3, -t 0 1, 0, t 0 3;
     0, -t 3 2, 0, 0, -t 0 1, 0;
     0, -t 1 0, 0, 0, -t 2 3, 0;
     t 3 0, 0, -t 1 0, -t 3 2, 0, -t 1 2;
     0, t 3 0, 0, 0, -t 2 1, 0]

/-- Entry `(cfg i, cfg j)` of `H0Fw sqG t Vint` is `hopSq t i j`, plus `Vint` on the diagonal; no
symmetry of `t` is assumed (entry `(s, s')` is `−t a b` times the fermionic sign, with `a` the site
vacated from `s` and `b` the site gained in `s'`). -/
theorem H0Fw_square (t : Fin 4 → Fin 4 → ℝ) (Vint : Conf 4 2 → ℝ) (i j : Fin 6) :
    H0Fw sqG t Vint (cfg i) (cfg j) = hopSq t i j + if i = j then Vint (cfg i) else 0 := by
  have hinj : cfg i = cfg j ↔ i = j := cfg_bijective.1.eq_iff
  simp only [H0Fw, Matrix.add_apply, Matrix.diagonal_apply, hinj, Γ, amp, slater, τs_cfg]
  fin_cases i <;> fin_cases j <;>
    simp +decide [Fin.sum_univ_succ, Matrix.det_fin_two, Function.update, hopM, sqG, pos, hopSq]

/-- Row `cfg c` of `H(v) ψ`, in the basis `cfg`. -/
lemma hamN_H0Fw_row (t : Fin 4 → Fin 4 → ℝ) (Vint : Conf 4 2 → ℝ) (v : Fin 4 → ℝ)
    (ψ : Conf 4 2 → ℝ) (c : Fin 6) :
    (hamN (H0Fw sqG t Vint) occF v *ᵥ ψ) (cfg c) =
      ∑ j, hopSq t c j * ψ (cfg j) + (Vint (cfg c) + ∑ i, v i * occF i (cfg c)) * ψ (cfg c) := by
  rw [hamN_mulVec_apply]
  have hsum : (H0Fw sqG t Vint *ᵥ ψ) (cfg c) = ∑ j, H0Fw sqG t Vint (cfg c) (e j) * ψ (e j) := by
    simp only [Matrix.mulVec, dotProduct]
    exact (Equiv.sum_comp e (fun s => H0Fw sqG t Vint (cfg c) s * ψ s)).symm
  rw [hsum]
  simp only [e, Equiv.ofBijective_apply, H0Fw_square, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- A `2 × 2` block `[[a, b], [b, a]]` with a nonzero kernel vector has `a² = b²`. -/
lemma sq_eq_sq_of_block {a b x y : ℝ} (h1 : a * x + b * y = 0) (h2 : b * x + a * y = 0)
    (hxy : x ≠ 0 ∨ y ≠ 0) : a ^ 2 = b ^ 2 := by
  have hx : (a ^ 2 - b ^ 2) * x = 0 := by linear_combination a * h1 - b * h2
  have hy : (a ^ 2 - b ^ 2) * y = 0 := by linear_combination a * h2 - b * h1
  rcases hxy with hx0 | hy0
  · linarith [(mul_eq_zero.mp hx).resolve_right hx0]
  · linarith [(mul_eq_zero.mp hy).resolve_right hy0]

/-- An eigenvector of the two-fermion square with edge-dependent hopping that vanishes on the
configurations `01` and `23`, with `ψ(02)` and `ψ(13)` not both zero, forces `t₁₂² = t₃₀²`. -/
theorem square_zero_pattern_hopping {t : Fin 4 → Fin 4 → ℝ} (ht : ∀ a b, t a b = t b a)
    (Vint : Conf 4 2 → ℝ) (v : Fin 4 → ℝ) {ψ : Conf 4 2 → ℝ} {E : ℝ}
    (hψ : hamN (H0Fw sqG t Vint) occF v *ᵥ ψ = E • ψ) (h0 : ψ (cfg 0) = 0) (h5 : ψ (cfg 5) = 0)
    (h14 : ψ (cfg 1) ≠ 0 ∨ ψ (cfg 4) ≠ 0) : t 1 2 ^ 2 = t 3 0 ^ 2 := by
  have r0 := congrFun hψ (cfg 0)
  have r5 := congrFun hψ (cfg 5)
  rw [hamN_H0Fw_row] at r0 r5
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hopSq, Pi.smul_apply, smul_eq_mul] at r0 r5
  simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      cons_val, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, neg_mul, mul_zero,
      zero_mul, add_zero, zero_add, h0, h5] at r0 r5
  have e1 := ht 0 3
  have e2 := ht 2 1
  have hsq := sq_eq_sq_of_block (a := -t 1 2) (b := t 3 0) (x := ψ (cfg 1)) (y := ψ (cfg 4))
    (by linear_combination r0 - ψ (cfg 4) * e1) (by linear_combination r5 + ψ (cfg 4) * e2) h14
  linear_combination hsq

/-- The mirror zero pattern: an eigenvector that vanishes on `03` and `12`, with `ψ(02)` and
`ψ(13)` not both zero, forces `t₀₁² = t₂₃²`. -/
theorem square_zero_pattern_hopping' {t : Fin 4 → Fin 4 → ℝ} (ht : ∀ a b, t a b = t b a)
    (Vint : Conf 4 2 → ℝ) (v : Fin 4 → ℝ) {ψ : Conf 4 2 → ℝ} {E : ℝ}
    (hψ : hamN (H0Fw sqG t Vint) occF v *ᵥ ψ = E • ψ) (h2 : ψ (cfg 2) = 0) (h3 : ψ (cfg 3) = 0)
    (h14 : ψ (cfg 1) ≠ 0 ∨ ψ (cfg 4) ≠ 0) : t 0 1 ^ 2 = t 2 3 ^ 2 := by
  have r2 := congrFun hψ (cfg 2)
  have r3 := congrFun hψ (cfg 3)
  rw [hamN_H0Fw_row] at r2 r3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hopSq, Pi.smul_apply, smul_eq_mul] at r2 r3
  simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      cons_val, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, neg_mul, mul_zero,
      zero_mul, add_zero, zero_add, h2, h3] at r2 r3
  have e1 := ht 3 2
  have e2 := ht 1 0
  have hsq := sq_eq_sq_of_block (a := -t 2 3) (b := -t 0 1) (x := ψ (cfg 1)) (y := ψ (cfg 4))
    (by linear_combination r2 + ψ (cfg 1) * e1) (by linear_combination r3 + ψ (cfg 1) * e2) h14
  linear_combination -hsq

/-- The potential difference `v − (v + ε (1, 1, −1, −1))` seen by each configuration. -/
lemma shift_sq_cfg (v : Fin 4 → ℝ) (ε : ℝ) (c : Fin 6) :
    ∑ i, (v i - (v + ε • ![1, 1, -1, -1] : Fin 4 → ℝ) i) * occF i (cfg c) =
      ![-2 * ε, 0, 0, 0, 0, 2 * ε] c := by
  fin_cases c <;> simp +decide [Fin.sum_univ_succ, occF, cfg] <;> ring

/-- If a ground state `ψ` of a symmetric `M` has `M c c` equal to its energy, then the basis vector
at `c` is a ground state too, so `M c' c = 0` for every `c' ≠ c`. -/
lemma offdiag_zero_of_diag_ground {V : Type*} [Fintype V] {M : Matrix V V ℝ}
    (hM : M.IsSymm) {ψ : V → ℝ} (h : IsGroundState M ψ) {c : V}
    (hc : M c c = qf M ψ / (ψ ⬝ᵥ ψ)) {c' : V} (hne : c' ≠ c) : M c' c = 0 := by
  classical
  have hpos : 0 < ψ ⬝ᵥ ψ := by
    obtain ⟨i, hi⟩ : ∃ i, ψ i ≠ 0 := by
      by_contra hcon; push Not at hcon; exact h.1 (funext hcon)
    have hle : ψ i * ψ i ≤ ψ ⬝ᵥ ψ :=
      Finset.single_le_sum (f := fun j => ψ j * ψ j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    nlinarith [mul_self_pos.mpr hi]
  have hqf : qf M (Pi.single c 1) = M c c := by
    simp [qf, Matrix.mulVec_single, dotProduct, Pi.single_apply]
  have hnorm : (Pi.single c 1 : V → ℝ) ⬝ᵥ Pi.single c 1 = 1 := by
    simp [dotProduct, Pi.single_apply]
  have hφ : IsGroundState M (Pi.single c 1) := by
    refine ⟨fun h0 => by simpa using congrFun h0 c, fun χ => ?_⟩
    rw [hqf, hnorm, mul_one, hc, div_mul_eq_mul_div, div_le_iff₀ hpos]
    exact h.2 χ
  have heig := congrFun (isGroundState_eigen hM hφ) c'
  simpa [Matrix.mulVec_single, Pi.single_apply, hne] using heig

/-- Entry `(cfg i, cfg j)` of `H(v)` for the square with edge-dependent hopping. -/
lemma hamN_H0Fw_entry (t : Fin 4 → Fin 4 → ℝ) (Vint : Conf 4 2 → ℝ) (v : Fin 4 → ℝ) (i j : Fin 6) :
    hamN (H0Fw sqG t Vint) occF v (cfg i) (cfg j) =
      hopSq t i j + if i = j then Vint (cfg i) + ∑ k, v k * occF k (cfg i) else 0 := by
  have hinj : cfg i = cfg j ↔ i = j := cfg_bijective.1.eq_iff
  simp only [hamN, Matrix.add_apply, Matrix.diagonal_apply, hinj, H0Fw_square]
  split_ifs with h
  · subst h; ring
  · ring

/-- If one state is a ground state of the two-fermion square with edge-dependent hopping at
`v` and at `v + ε (1, 1, −1, −1)`, `ε ≠ 0`, then `t₁₂² = t₃₀²`, or `t₀₁ = t₂₃ = 0`, for every `v`
and every configuration-diagonal interaction. With all four hoppings nonzero, only `t₁₂² = t₃₀²`
is left. -/
theorem square_shared_hopping_sharp {t : Fin 4 → Fin 4 → ℝ} (ht : ∀ a b, t a b = t b a)
    (Vint : Conf 4 2 → ℝ) (v : Fin 4 → ℝ) {ε : ℝ} (hε : ε ≠ 0) {ψ : Conf 4 2 → ℝ}
    (hA : IsGroundState (hamN (H0Fw sqG t Vint) occF v) ψ)
    (hB : IsGroundState (hamN (H0Fw sqG t Vint) occF (v + ε • ![1, 1, -1, -1])) ψ) :
    t 1 2 ^ 2 = t 3 0 ^ 2 ∨ (t 0 1 = 0 ∧ t 2 3 = 0) := by
  have hS := H0Fw_isSymm sqG ht Vint
  have hMS := hamN_isSymm hS occF v
  obtain ⟨κ, hκ⟩ := support_const_of_shared hS hA hB
  have hval : ∀ c : Fin 6, ψ (cfg c) ≠ 0 → ![-2 * ε, 0, 0, 0, 0, 2 * ε] c = κ := fun c hc => by
    rw [← shift_sq_cfg v ε c]; exact hκ _ hc
  have heig := isGroundState_eigen hMS hA
  set E := qf (hamN (H0Fw sqG t Vint) occF v) ψ / (ψ ⬝ᵥ ψ) with hE
  -- if `κ = 0`, the configurations `{0, 1}` and `{2, 3}` are empty
  have hout : κ = 0 → ψ (cfg 0) = 0 ∧ ψ (cfg 5) = 0 := fun hκ0 =>
    ⟨by_contra fun h => hε (by have := hval 0 h; simp at this; linarith),
     by_contra fun h => hε (by have := hval 5 h; simp at this; linarith)⟩
  -- a basis state `cfg c` whose diagonal entry is `E` has no hopping out of it
  have hoff : ∀ c c' : Fin 6, hamN (H0Fw sqG t Vint) occF v (cfg c) (cfg c) = E → c' ≠ c →
      hopSq t c' c = 0 := fun c c' hd hne => by
    have := offdiag_zero_of_diag_ground hMS hA hd (c' := cfg c')
      (fun h => hne (cfg_bijective.1 h))
    simpa only [hamN_H0Fw_entry, hne, ↓reduceIte, add_zero] using this
  by_cases h14 : ψ (cfg 1) ≠ 0 ∨ ψ (cfg 4) ≠ 0
  · have hκ0 : κ = 0 := by
      rcases h14 with h | h
      · have := hval 1 h; simp at this; linarith
      · have := hval 4 h; simp at this; linarith
    obtain ⟨h0, h5⟩ := hout hκ0
    exact Or.inl (square_zero_pattern_hopping ht Vint v heig h0 h5 h14)
  · simp only [ne_eq, not_or, not_not] at h14
    obtain ⟨h1, h4⟩ := h14
    by_cases h23 : ψ (cfg 2) ≠ 0 ∨ ψ (cfg 3) ≠ 0
    · have hκ0 : κ = 0 := by
        rcases h23 with h | h
        · have := hval 2 h; simp at this; linarith
        · have := hval 3 h; simp at this; linarith
      obtain ⟨h0, h5⟩ := hout hκ0
      -- rows `cfg 2` and `cfg 3` only see `cfg 1` and `cfg 4`, which are empty
      have r2 := congrFun heig (cfg 2)
      have r3 := congrFun heig (cfg 3)
      rw [hamN_H0Fw_row] at r2 r3
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hopSq, Pi.smul_apply, smul_eq_mul] at r2 r3
      simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
          cons_val, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, mul_zero,
          zero_mul, add_zero, zero_add, h0, h1, h4, h5] at r2 r3
      refine Or.inr ?_
      rcases h23 with h | h
      · have hd : hamN (H0Fw sqG t Vint) occF v (cfg 2) (cfg 2) = E := by
          simp only [hamN_H0Fw_entry, ↓reduceIte, hopSq, Fin.isValue, of_apply, cons_val',
            cons_val_zero, cons_val_fin_one, cons_val, zero_add, Fin.sum_univ_four]
          exact mul_right_cancel₀ h (by linear_combination r2)
        have a := hoff 2 1 hd (by decide)
        have b := hoff 2 4 hd (by decide)
        simp only [hopSq, Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
          cons_val_one, cons_val, neg_eq_zero] at a b
        exact ⟨by rw [ht]; exact b, a⟩
      · have hd : hamN (H0Fw sqG t Vint) occF v (cfg 3) (cfg 3) = E := by
          simp only [hamN_H0Fw_entry, ↓reduceIte, hopSq, Fin.isValue, of_apply, cons_val',
            cons_val_zero, cons_val_fin_one, cons_val, zero_add, Fin.sum_univ_four]
          exact mul_right_cancel₀ h (by linear_combination r3)
        have a := hoff 3 1 hd (by decide)
        have b := hoff 3 4 hd (by decide)
        simp only [hopSq, Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
          cons_val_one, cons_val, neg_eq_zero] at a b
        exact ⟨a, by rw [ht]; exact b⟩
    · simp only [ne_eq, not_or, not_not] at h23
      obtain ⟨h2, h3⟩ := h23
      have h05 : ψ (cfg 0) ≠ 0 ∨ ψ (cfg 5) ≠ 0 := by
        by_contra hc
        simp only [ne_eq, not_or, not_not] at hc
        apply hA.1
        funext s
        obtain ⟨j, rfl⟩ := cfg_bijective.2 s
        fin_cases j <;> simp [hc.1, hc.2, h1, h2, h3, h4]
      have r1 := congrFun heig (cfg 1)
      have r4 := congrFun heig (cfg 4)
      rw [hamN_H0Fw_row] at r1 r4
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hopSq, Pi.smul_apply, smul_eq_mul] at r1 r4
      simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
          cons_val, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, neg_mul, mul_zero,
          add_zero, zero_add, h1, h2, h3, h4] at r1 r4
      have e1 := ht 2 1
      have e2 := ht 0 3
      have hsq := sq_eq_sq_of_block (a := -t 1 2) (b := t 3 0) (x := ψ (cfg 0)) (y := ψ (cfg 5))
        (by linear_combination r1 + ψ (cfg 0) * e1 - ψ (cfg 5) * e2) (by linear_combination r4) h05
      exact Or.inl (by linear_combination hsq)

/-- If one state is a ground state of the two-fermion square with edge-dependent hopping at
`v` and at `v + ε (1, 1, −1, −1)`, `ε ≠ 0`, then `t₁₂² = t₃₀²` or `t₀₁² = t₂₃²`, for every `v` and
every configuration-diagonal interaction (the weaker form of `square_shared_hopping_sharp`). -/
theorem square_shared_hopping {t : Fin 4 → Fin 4 → ℝ} (ht : ∀ a b, t a b = t b a)
    (Vint : Conf 4 2 → ℝ) (v : Fin 4 → ℝ) {ε : ℝ} (hε : ε ≠ 0) {ψ : Conf 4 2 → ℝ}
    (hA : IsGroundState (hamN (H0Fw sqG t Vint) occF v) ψ)
    (hB : IsGroundState (hamN (H0Fw sqG t Vint) occF (v + ε • ![1, 1, -1, -1])) ψ) :
    t 1 2 ^ 2 = t 3 0 ^ 2 ∨ t 0 1 ^ 2 = t 2 3 ^ 2 :=
  (square_shared_hopping_sharp ht Vint v hε hA hB).imp id fun h => by rw [h.1, h.2]

end Bridge.Square

end DFT
