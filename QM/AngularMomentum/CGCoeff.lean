/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.WellKnown
import QM.AngularMomentum.CGSeries

/-!
# Clebsch–Gordan coefficients

On `V_j` the unnormalized ladder vectors satisfy `‖e_k‖² = N_k = Π_{i<k} (i + 1)(n - i)` for the
inner product in which `S₊† = S₋` (`spinIp`, `spinIp_Sp`). The normalized states are
`|j, j - k⟩ = e_k / √N_k`. On the product, the coupled states `|J, M⟩` are the normalized ladder
vectors `(J₋)^k hw_p / ‖(J₋)^k hw_p‖` of the highest weights of `QM.cg_series`, and the
Clebsch–Gordan coefficients are their coordinates along the normalized product states (`cgCoeff`,
`cgCoeff_eq_pairIp`). They are real by construction. The labels are `J = j₁ + j₂ - p`, `M = J - k`,
`m₁ = j₁ - x` and `m₂ = j₂ - y` with `j₁ = n₁/2` and `j₂ = n₂/2`.

## Main results

* `spinIp_Sp`, `pairIp_Jp`: `S₊† = S₋` and `J₊† = J₋`.
* `pairIp_prodState`, `pairIp_cgState`: both bases are orthonormal.
* `cgCoeff_eq_zero`: the selection rule `M = m₁ + m₂`.
* `cgCoeff_phase`: the Condon–Shortley phase `⟨j₁ j₁; j₂ (J - j₁) | J J⟩ > 0`.
* `cg_orthogonal_left`, `cg_orthogonal_right`: the two orthogonality relations.
* `cg_recursion`: the recursion obtained from `J₋`.
* `cg_racah`: Racah's closed formula.

## Proof of Racah's formula

With integer labels and `1/n! = 0` for `n < 0` (`invFact`), Racah's sum `S(x, y)` satisfies
`(n₁ - x + 1) S(x - 1, y) + (n₂ - y + 1) S(x, y - 1) = (x + y - p) S(x, y)`. Termwise this leaves an
alternating telescoping sum (`racahZ_rec`). Since `J₋ e_x = e_{x+1}` on the unnormalized basis, the
components of `(J₋)^k hw_p` satisfy the same recursion, and induction on `k` gives
`(J₋)^k hw_p = k! D_p (n₁ - x)! (n₂ - y)! S(x, y)` (`cgAmp_racah`). The norm of `hw_p` follows from
the Vandermonde-type identity `sum_choose_mul_choose`.
-/

namespace QM

open Module

/-! ### The inner product on `V_j` -/

/-- `N_k = Π_{i<k} (i + 1)(n - i)`, the squared norm of `e_k`. -/
noncomputable def spinN (n k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (((i : ℝ) + 1) * ((n : ℝ) - i))

lemma spinN_succ (n k : ℕ) : spinN n (k + 1) = spinN n k * (((k : ℝ) + 1) * ((n : ℝ) - k)) := by
  rw [spinN, Finset.prod_range_succ]; rfl

lemma spinN_pos {n k : ℕ} (hk : k ≤ n) : 0 < spinN n k := by
  refine Finset.prod_pos fun i hi => ?_
  have := Finset.mem_range.mp hi
  have : (i : ℝ) < n := by exact_mod_cast (show i < n by omega)
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith

/-- The inner product on `V_j` in which `e_k` has squared norm `N_k`. -/
noncomputable def spinIp (n : ℕ) (f g : Fin (n + 1) → ℝ) : ℝ := ∑ i, f i * g i * spinN n i

/-- **`S₊† = S₋`.** -/
theorem spinIp_Sp (n : ℕ) (f g : Fin (n + 1) → ℝ) :
    spinIp n (spinSp n f) g = spinIp n f (spinSm n g) := by
  unfold spinIp
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hl : spinSp n f (Fin.last n) = 0 := by
    rw [spinSp_apply, dite_eq_right (by simp)]
  have h0 : spinSm n g 0 = 0 := by rw [spinSm_apply, dite_eq_left rfl]
  rw [hl, h0, zero_mul, zero_mul, add_zero, mul_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < n := j.2
  rw [spinSp_apply, dite_eq_left (by simp [hj]), spinSm_apply,
    dite_eq_right (Fin.succ_ne_zero j)]
  have e1 : (⟨(Fin.castSucc j : ℕ) + 1, by simp⟩ : Fin (n + 1)) = j.succ :=
    Fin.ext (by simp)
  have e2 : (⟨(j.succ : ℕ) - 1, by simp⟩ : Fin (n + 1)) = Fin.castSucc j :=
    Fin.ext (by simp)
  rw [e1, e2]
  simp only [Fin.val_castSucc, Fin.val_succ, spinN_succ]
  ring

lemma spinN_eq (n k : ℕ) : spinN n k = ((k.factorial * n.descFactorial k : ℕ) : ℝ) := by
  induction k with
  | zero => simp [spinN]
  | succ k ih =>
    rw [spinN_succ, ih, Nat.factorial_succ, Nat.descFactorial_succ]
    rcases le_or_gt k n with h | h
    · push_cast [Nat.cast_sub h]; ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr h]; simp

lemma spinN_nonneg (n k : ℕ) : 0 ≤ spinN n k := by rw [spinN_eq]; positivity

lemma spinN_eq_zero {n k : ℕ} (h : n < k) : spinN n k = 0 := by
  rw [spinN_eq, (Nat.descFactorial_eq_zero_iff_lt).mpr h]; simp

/-! ### The inner product on `V_{j₁} ⊗ V_{j₂}` -/

section Pair

variable (n₁ n₂ : ℕ)

/-- The inner product on the product in which `e_x ⊗ e_y` has squared norm `N_x N_y`. -/
noncomputable def pairIp (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) : ℝ :=
  ∑ q, f q * g q * (spinN n₁ q.1 * spinN n₂ q.2)

variable {n₁ n₂}

lemma pairIp_comm (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ f g = pairIp n₁ n₂ g f := by
  unfold pairIp; exact Finset.sum_congr rfl fun _ _ => by ring

lemma pairIp_add_left (f g h : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (f + g) h = pairIp n₁ n₂ f h + pairIp n₁ n₂ g h := by
  unfold pairIp; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply]; ring

lemma pairIp_add_right (f g h : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ f (g + h) = pairIp n₁ n₂ f g + pairIp n₁ n₂ f h := by
  rw [pairIp_comm, pairIp_add_left, pairIp_comm g, pairIp_comm h]

lemma pairIp_smul_left (c : ℝ) (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (c • f) g = c * pairIp n₁ n₂ f g := by
  unfold pairIp; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma pairIp_smul_right (c : ℝ) (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ f (c • g) = c * pairIp n₁ n₂ f g := by
  rw [pairIp_comm, pairIp_smul_left, pairIp_comm]

lemma pairIp_zero_left (g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) : pairIp n₁ n₂ 0 g = 0 := by
  simp [pairIp]

lemma spinN_mul_pos (q : Fin (n₁ + 1) × Fin (n₂ + 1)) : 0 < spinN n₁ q.1 * spinN n₂ q.2 :=
  mul_pos (spinN_pos (Nat.lt_succ_iff.mp q.1.2)) (spinN_pos (Nat.lt_succ_iff.mp q.2.2))

lemma pairIp_self_pos {f : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ} (hf : f ≠ 0) :
    0 < pairIp n₁ n₂ f f := by
  obtain ⟨q, hq⟩ : ∃ q, f q ≠ 0 := by
    by_contra h; exact hf (funext fun q => not_not.mp fun hq => h ⟨q, hq⟩)
  unfold pairIp
  refine Finset.sum_pos' (fun i _ => mul_nonneg (mul_self_nonneg _) (spinN_mul_pos i).le)
    ⟨q, Finset.mem_univ _, mul_pos (mul_self_pos.mpr hq) (spinN_mul_pos q)⟩

lemma pairIp_self_nonneg (f : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) : 0 ≤ pairIp n₁ n₂ f f := by
  by_cases hf : f = 0
  · rw [hf, pairIp_zero_left]
  · exact (pairIp_self_pos hf).le

lemma eq_zero_of_pairIp_self {f : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ}
    (h : pairIp n₁ n₂ f f = 0) : f = 0 := by
  by_contra hf; exact (pairIp_self_pos hf).ne' h

lemma pairIp_onFst (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (onFst (spinSp n₁) f) g = pairIp n₁ n₂ f (onFst (spinSm n₁) g) := by
  unfold pairIp
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h := spinIp_Sp n₁ (fun i => f (i, y)) (fun i => g (i, y))
  simp only [spinIp] at h
  simp only [onFst_apply]
  calc _ = (∑ x, spinSp n₁ (fun i => f (i, y)) x * g (x, y) * spinN n₁ x) * spinN n₂ y := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = (∑ x, f (x, y) * spinSm n₁ (fun i => g (i, y)) x * spinN n₁ x) * spinN n₂ y := by rw [h]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring

lemma pairIp_onSnd (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (onSnd (spinSp n₂) f) g = pairIp n₁ n₂ f (onSnd (spinSm n₂) g) := by
  unfold pairIp
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := spinIp_Sp n₂ (fun j => f (x, j)) (fun j => g (x, j))
  simp only [spinIp] at h
  simp only [onSnd_apply]
  calc _ = (∑ y, spinSp n₂ (fun j => f (x, j)) y * g (x, y) * spinN n₂ y) * spinN n₁ x := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = (∑ y, f (x, y) * spinSm n₂ (fun j => g (x, j)) y * spinN n₂ y) * spinN n₁ x := by rw [h]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring

/-- **`J₊† = J₋`.** -/
theorem pairIp_Jp (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (pairJp n₁ n₂ f) g = pairIp n₁ n₂ f (pairJm n₁ n₂ g) := by
  simp only [pairJp, pairJm, LinearMap.add_apply, pairIp_add_left, pairIp_add_right,
    pairIp_onFst, pairIp_onSnd]

lemma pairIp_Jm (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (pairJm n₁ n₂ f) g = pairIp n₁ n₂ f (pairJp n₁ n₂ g) := by
  rw [pairIp_comm, ← pairIp_Jp, pairIp_comm]

lemma pairIp_Jz (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (pairJz n₁ n₂ f) g = pairIp n₁ n₂ f (pairJz n₁ n₂ g) := by
  unfold pairIp
  exact Finset.sum_congr rfl fun ⟨x, y⟩ _ => by rw [pairJz_apply, pairJz_apply]; ring

lemma pairIp_S2 (f g : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ ((isSU2_pair (K := ℝ) n₁ n₂).S2 f) g =
      pairIp n₁ n₂ f ((isSU2_pair (K := ℝ) n₁ n₂).S2 g) := by
  simp only [IsSU2.S2, LinearMap.add_apply, mul_apply_eq_comp, pairIp_add_left,
    pairIp_add_right, pairIp_Jm, pairIp_Jz, ← pairIp_Jp]

/-- Eigenvectors of a self-adjoint operator for distinct eigenvalues are orthogonal. -/
lemma pairIp_eq_zero_of_eigen {A : End ℝ (Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ)}
    (hA : ∀ f g, pairIp n₁ n₂ (A f) g = pairIp n₁ n₂ f (A g))
    {v w : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ} {a b : ℝ} (hv : A v = a • v) (hw : A w = b • w)
    (hab : a ≠ b) : pairIp n₁ n₂ v w = 0 := by
  have h := hA v w
  rw [hv, hw, pairIp_smul_left, pairIp_smul_right] at h
  have : (a - b) * pairIp n₁ n₂ v w = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hab)

end Pair

/-! ### Clebsch–Gordan coefficients -/

section CG

variable {n₁ n₂ : ℕ}

variable (n₁ n₂) in
/-- The unnormalized coupled state `(J₋)^k hw_p`, with `J = j₁ + j₂ - p` and `M = J - k`. -/
noncomputable abbrev cgLadder (p k : ℕ) : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ :=
  (isSU2_pair (K := ℝ) n₁ n₂).ladder (hw n₁ n₂ p) k

lemma cgLadder_zero (p : ℕ) : cgLadder n₁ n₂ p 0 = hw n₁ n₂ p := by
  simp [cgLadder, IsSU2.ladder]

lemma cgLadder_ne_zero {p k : ℕ} (hp : p ≤ min n₁ n₂) (hk : k ≤ n₁ + n₂ - 2 * p) :
    cgLadder n₁ n₂ p k ≠ 0 :=
  (isSU2_pair n₁ n₂).ladder_ne_zero_of_le (hw_ladder_stop n₁ n₂ hp).1 hk

/-- `‖|J, M - 1⟩‖² = (J + M)(J - M + 1) ‖|J, M⟩‖²` for the unnormalized ladder. -/
lemma pairIp_cgLadder_succ {p : ℕ} (hp : p ≤ min n₁ n₂) (k : ℕ) :
    pairIp n₁ n₂ (cgLadder n₁ n₂ p (k + 1)) (cgLadder n₁ n₂ p (k + 1)) =
      ((k : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - k) *
        pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p k) := by
  have h1 := (isSU2_pair (K := ℝ) n₁ n₂).Sp_ladder_succ (pairJp_hw (K := ℝ) hp)
    (pairJz_hw (K := ℝ) p) k
  rw [cgLadder, IsSU2.ladder_succ, ← pairIp_Jp, ← IsSU2.ladder_succ, h1, pairIp_smul_left]
  ring

variable (n₁ n₂) in
/-- The component of `(J₋)^k hw_p` along `e_x ⊗ e_y`, extended by zero to all `x, y : ℕ`. -/
noncomputable def cgAmp (p k x y : ℕ) : ℝ :=
  if h : x ≤ n₁ ∧ y ≤ n₂ then
    cgLadder n₁ n₂ p k (⟨x, Nat.lt_succ_of_le h.1⟩, ⟨y, Nat.lt_succ_of_le h.2⟩)
  else 0

lemma cgAmp_fin (p k : ℕ) (x : Fin (n₁ + 1)) (y : Fin (n₂ + 1)) :
    cgAmp n₁ n₂ p k x y = cgLadder n₁ n₂ p k (x, y) := by
  rw [cgAmp, dite_eq_left ⟨Nat.lt_succ_iff.mp x.2, Nat.lt_succ_iff.mp y.2⟩]

lemma cgAmp_of_not {p k x y : ℕ} (h : ¬(x ≤ n₁ ∧ y ≤ n₂)) : cgAmp n₁ n₂ p k x y = 0 := by
  rw [cgAmp, dite_eq_right h]

/-- The `J₋` recursion for the unnormalized components. -/
lemma cgAmp_succ {p k x y : ℕ} (hx : x ≤ n₁) (hy : y ≤ n₂) :
    cgAmp n₁ n₂ p (k + 1) x y =
      (if x = 0 then 0 else cgAmp n₁ n₂ p k (x - 1) y) +
        (if y = 0 then 0 else cgAmp n₁ n₂ p k x (y - 1)) := by
  rw [cgAmp, dite_eq_left ⟨hx, hy⟩, cgLadder, IsSU2.ladder_succ]
  change onFst (spinSm (K := ℝ) n₁) _ _ + onSnd (spinSm (K := ℝ) n₂) _ _ = _
  rw [onFst_apply, onSnd_apply, spinSm_apply, spinSm_apply]
  congr 1
  · by_cases h0 : x = 0
    · subst h0; rfl
    · have h0' : (⟨x, Nat.lt_succ_of_le hx⟩ : Fin (n₁ + 1)) ≠ 0 := by
        rw [Ne, Fin.ext_iff]; exact h0
      rw [dite_eq_right h0', ite_eq_right h0, cgAmp, dite_eq_left ⟨by omega, hy⟩]
  · by_cases h0 : y = 0
    · subst h0; rfl
    · have h0' : (⟨y, Nat.lt_succ_of_le hy⟩ : Fin (n₂ + 1)) ≠ 0 := by
        rw [Ne, Fin.ext_iff]; exact h0
      rw [dite_eq_right h0', ite_eq_right h0, cgAmp, dite_eq_left ⟨hx, by omega⟩]

/-- **Selection rule** for the unnormalized components. -/
lemma cgAmp_eq_zero {p k x y : ℕ} (h : x + y ≠ p + k) : cgAmp n₁ n₂ p k x y = 0 := by
  induction k generalizing x y with
  | zero =>
    by_cases hr : x ≤ n₁ ∧ y ≤ n₂
    · rw [cgAmp, dite_eq_left hr, cgLadder_zero]; exact hw_of_ne (by simpa using h)
    · exact cgAmp_of_not hr
  | succ k ih =>
    by_cases hr : x ≤ n₁ ∧ y ≤ n₂
    · rw [cgAmp_succ hr.1 hr.2]
      split_ifs with h1 h2 h2
      · ring
      · rw [ih (by omega)]; ring
      · rw [ih (by omega)]; ring
      · rw [ih (by omega), ih (by omega)]; ring
    · exact cgAmp_of_not hr

variable (n₁ n₂) in
/-- **Clebsch–Gordan coefficients** `⟨j₁ m₁; j₂ m₂ | J M⟩` with `j₁ = n₁/2`, `j₂ = n₂/2`,
`J = j₁ + j₂ - p`, `M = J - k`, `m₁ = j₁ - x` and `m₂ = j₂ - y`: the coordinate of the normalized
`|J, M⟩` along the normalized `|j₁ m₁⟩ ⊗ |j₂ m₂⟩` (`cgCoeff_eq_pairIp`). It vanishes for `x > n₁` or
`y > n₂`. -/
noncomputable def cgCoeff (p k x y : ℕ) : ℝ :=
  cgAmp n₁ n₂ p k x y * √(spinN n₁ x * spinN n₂ y) /
    √(pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p k))

variable (n₁ n₂) in
/-- The normalized coupled state `|J, M⟩`. -/
noncomputable def cgState (p k : ℕ) : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ :=
  (√(pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p k)))⁻¹ • cgLadder n₁ n₂ p k

variable (n₁ n₂) in
/-- The normalized product state `|j₁ m₁⟩ ⊗ |j₂ m₂⟩`. -/
noncomputable def prodState (q : Fin (n₁ + 1) × Fin (n₂ + 1)) : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ :=
  Pi.single q (√(spinN n₁ q.1 * spinN n₂ q.2))⁻¹

lemma pairIp_single_left (q : Fin (n₁ + 1) × Fin (n₂ + 1)) (c : ℝ)
    (f : Fin (n₁ + 1) × Fin (n₂ + 1) → ℝ) :
    pairIp n₁ n₂ (Pi.single q c) f = c * f q * (spinN n₁ q.1 * spinN n₂ q.2) := by
  unfold pairIp
  rw [Finset.sum_eq_single q (fun r _ hr => by simp [hr]) (by simp)]
  simp

/-- The product states are orthonormal. -/
theorem pairIp_prodState (q q' : Fin (n₁ + 1) × Fin (n₂ + 1)) :
    pairIp n₁ n₂ (prodState n₁ n₂ q) (prodState n₁ n₂ q') = if q = q' then 1 else 0 := by
  rw [prodState, pairIp_single_left, prodState]
  by_cases h : q = q'
  · subst h
    rw [Pi.single_eq_same, ← mul_inv, ← sq,
      Real.sq_sqrt (spinN_mul_pos q).le, inv_mul_cancel₀ (spinN_mul_pos q).ne']
    simp
  · rw [Pi.single_eq_of_ne h]; simp [h]

/-- The Clebsch–Gordan coefficient is the coordinate `⟨j₁ m₁; j₂ m₂ | J M⟩` of the normalized
coupled state along the normalized product state. -/
theorem cgCoeff_eq_pairIp (p k : ℕ) (q : Fin (n₁ + 1) × Fin (n₂ + 1)) :
    cgCoeff n₁ n₂ p k q.1 q.2 = pairIp n₁ n₂ (prodState n₁ n₂ q) (cgState n₁ n₂ p k) := by
  rw [prodState, pairIp_single_left, cgState, cgCoeff, cgAmp_fin, Pi.smul_apply, smul_eq_mul]
  rw [show ∀ a b c d : ℝ, a⁻¹ * (b⁻¹ * c) * d = c / b * (d / a) from fun _ _ _ _ => by ring,
    Real.div_sqrt]
  ring

/-- **Selection rule**: `⟨j₁ m₁; j₂ m₂ | J M⟩ = 0` unless `M = m₁ + m₂`. -/
theorem cgCoeff_eq_zero {p k x y : ℕ} (h : x + y ≠ p + k) : cgCoeff n₁ n₂ p k x y = 0 := by
  rw [cgCoeff, cgAmp_eq_zero h]; simp

/-- **Condon–Shortley phase**: `⟨j₁ j₁; j₂ (J - j₁) | J J⟩ > 0`. -/
theorem cgCoeff_phase {p : ℕ} (hp : p ≤ min n₁ n₂) : 0 < cgCoeff n₁ n₂ p 0 0 p := by
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  have h1 : cgAmp n₁ n₂ p 0 0 p = 1 := by
    rw [cgAmp, dite_eq_left ⟨Nat.zero_le _, hp2⟩, cgLadder_zero, hw_of_eq (by simp)]
    rfl
  rw [cgCoeff, h1, one_mul]
  refine div_pos (Real.sqrt_pos.mpr (mul_pos (spinN_pos (Nat.zero_le _)) (spinN_pos hp2)))
    (Real.sqrt_pos.mpr (pairIp_self_pos (cgLadder_ne_zero hp (Nat.zero_le _))))

lemma cgCoeff_of_not {p k x y : ℕ} (h : ¬(x ≤ n₁ ∧ y ≤ n₂)) : cgCoeff n₁ n₂ p k x y = 0 := by
  rw [cgCoeff, cgAmp_of_not h]; simp

lemma cgCoeff_fin (p k : ℕ) (x : Fin (n₁ + 1)) (y : Fin (n₂ + 1)) :
    cgCoeff n₁ n₂ p k x y = cgState n₁ n₂ p k (x, y) * √(spinN n₁ x * spinN n₂ y) := by
  rw [cgCoeff, cgState, cgAmp_fin, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]; ring

lemma cgLadder_eq_zero_of_ne {p p' k k' : ℕ} (hp : p ≤ min n₁ n₂) (hp' : p' ≤ min n₁ n₂)
    (hne : ¬(p = p' ∧ k = k')) :
    pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p' k') = 0 := by
  by_cases hpp : p = p'
  · subst hpp
    have hkk : k ≠ k' := fun h => hne ⟨rfl, h⟩
    refine pairIp_eq_zero_of_eigen pairIp_Jz
      ((isSU2_pair n₁ n₂).Sz_ladder (pairJz_hw (K := ℝ) p) k)
      ((isSU2_pair n₁ n₂).Sz_ladder (pairJz_hw (K := ℝ) p) k') ?_
    intro h; apply hkk; exact_mod_cast sub_right_inj.mp h
  · refine pairIp_eq_zero_of_eigen pairIp_S2
      ((isSU2_pair n₁ n₂).S2_ladder (pairJp_hw (K := ℝ) hp) (pairJz_hw (K := ℝ) p) k)
      ((isSU2_pair n₁ n₂).S2_ladder (pairJp_hw (K := ℝ) hp') (pairJz_hw (K := ℝ) p') k') ?_
    intro h
    have m1 := min_le_left n₁ n₂
    have m2 := min_le_right n₁ n₂
    have h1 : (2 * p : ℝ) ≤ n₁ + n₂ := by exact_mod_cast (show 2 * p ≤ n₁ + n₂ by omega)
    have h2 : (2 * p' : ℝ) ≤ n₁ + n₂ := by exact_mod_cast (show 2 * p' ≤ n₁ + n₂ by omega)
    have h3 : ((p' : ℝ) - p) * ((n₁ + n₂ : ℝ) - p - p' + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hpp (by exact_mod_cast (sub_eq_zero.mp h4).symm)
    · linarith

/-- The normalized coupled states are orthonormal. -/
theorem pairIp_cgState {p p' k k' : ℕ} (hp : p ≤ min n₁ n₂) (hk : k ≤ n₁ + n₂ - 2 * p)
    (hp' : p' ≤ min n₁ n₂) :
    pairIp n₁ n₂ (cgState n₁ n₂ p k) (cgState n₁ n₂ p' k') = if p = p' ∧ k = k' then 1 else 0 := by
  rw [cgState, cgState, pairIp_smul_left, pairIp_smul_right]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    have hpos := pairIp_self_pos (cgLadder_ne_zero hp hk)
    rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  · rw [cgLadder_eq_zero_of_ne hp hp' h]; ring

lemma sum_cgCoeff_mul (p k p' k' : ℕ) :
    ∑ x ∈ Finset.range (n₁ + 1), ∑ y ∈ Finset.range (n₂ + 1),
      cgCoeff n₁ n₂ p k x y * cgCoeff n₁ n₂ p' k' x y =
        pairIp n₁ n₂ (cgState n₁ n₂ p k) (cgState n₁ n₂ p' k') := by
  rw [Finset.sum_range]
  simp_rw [Finset.sum_range]
  unfold pairIp
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [cgCoeff_fin, cgCoeff_fin]
  have hN : √(spinN n₁ x * spinN n₂ y) * √(spinN n₁ x * spinN n₂ y) =
      spinN n₁ x * spinN n₂ y := Real.mul_self_sqrt (spinN_mul_pos (x, y)).le
  linear_combination (cgState n₁ n₂ p k (x, y) * cgState n₁ n₂ p' k' (x, y)) * hN

/-- **First orthogonality relation**
`Σ_{m₁ m₂} ⟨j₁ m₁; j₂ m₂ | J M⟩ ⟨j₁ m₁; j₂ m₂ | J' M'⟩ = δ_{J J'} δ_{M M'}`. -/
theorem cg_orthogonal_left {p p' k k' : ℕ} (hp : p ≤ min n₁ n₂) (hk : k ≤ n₁ + n₂ - 2 * p)
    (hp' : p' ≤ min n₁ n₂) :
    ∑ x ∈ Finset.range (n₁ + 1), ∑ y ∈ Finset.range (n₂ + 1),
      cgCoeff n₁ n₂ p k x y * cgCoeff n₁ n₂ p' k' x y = if p = p' ∧ k = k' then 1 else 0 := by
  rw [sum_cgCoeff_mul, pairIp_cgState hp hk hp']

lemma card_cgIdx : Fintype.card (CGIdx n₁ n₂) = Fintype.card (Fin (n₁ + 1) × Fin (n₂ + 1)) := by
  rw [Fintype.card_sigma, Fintype.card_prod]
  simp only [Fintype.card_fin]
  exact sum_cg_dims n₁ n₂

/-- **Second orthogonality relation**
`Σ_{J M} ⟨j₁ m₁; j₂ m₂ | J M⟩ ⟨j₁ m₁'; j₂ m₂' | J M⟩ = δ_{m₁ m₁'} δ_{m₂ m₂'}`. -/
theorem cg_orthogonal_right {x x' y y' : ℕ} (hx : x ≤ n₁) (hx' : x' ≤ n₁) (hy : y ≤ n₂)
    (hy' : y' ≤ n₂) :
    ∑ p ∈ Finset.range (min n₁ n₂ + 1), ∑ k ∈ Finset.range (n₁ + n₂ - 2 * p + 1),
      cgCoeff n₁ n₂ p k x y * cgCoeff n₁ n₂ p k x' y' = if x = x' ∧ y = y' then 1 else 0 := by
  classical
  let A : Matrix (Fin (n₁ + 1) × Fin (n₂ + 1)) (CGIdx n₁ n₂) ℝ :=
    fun q i => cgCoeff n₁ n₂ i.1 i.2 q.1 q.2
  have hA : A.transpose * A = 1 := by
    ext i i'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    simp only [A]
    have hi := cg_orthogonal_left (k' := i'.2) (Nat.lt_succ_iff.mp i.1.2)
      (Nat.lt_succ_iff.mp i.2.2) (Nat.lt_succ_iff.mp i'.1.2) (n₁ := n₁) (n₂ := n₂)
    rw [Finset.sum_range] at hi
    simp_rw [Finset.sum_range] at hi
    rw [Fintype.sum_prod_type, hi]
    obtain ⟨⟨p, hp⟩, ⟨k, hk⟩⟩ := i
    obtain ⟨⟨p', hp'⟩, ⟨k', hk'⟩⟩ := i'
    by_cases h : p = p' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [ite_eq_right h, ite_eq_right]
      intro he
      simp only [Sigma.mk.injEq, Fin.mk.injEq] at he
      obtain ⟨rfl, he2⟩ := he
      exact h ⟨rfl, by simpa using he2⟩
  have hAA : A * A.transpose = 1 := (Matrix.mul_eq_one_comm_of_card_eq (CGIdx n₁ n₂)
    (Fin (n₁ + 1) × Fin (n₂ + 1)) ℝ card_cgIdx).mp hA
  have h := congrFun (congrFun hAA (⟨x, Nat.lt_succ_of_le hx⟩, ⟨y, Nat.lt_succ_of_le hy⟩))
    (⟨x', Nat.lt_succ_of_le hx'⟩, ⟨y', Nat.lt_succ_of_le hy'⟩)
  rw [Matrix.mul_apply, Fintype.sum_sigma, Matrix.one_apply] at h
  simp only [Matrix.transpose_apply] at h
  simp only [A] at h
  rw [Finset.sum_range]
  simp_rw [Finset.sum_range]
  rw [h]
  simp [Prod.ext_iff, Fin.ext_iff]

/-- **The `J₋` recursion**
`√((J + M)(J - M + 1)) ⟨m₁ m₂ | J, M - 1⟩ =
  √((j₁ - m₁)(j₁ + m₁ + 1)) ⟨m₁ + 1, m₂ | J M⟩ + √((j₂ - m₂)(j₂ + m₂ + 1)) ⟨m₁, m₂ + 1 | J M⟩`
in the labels `M = J - k`, `m₁ = j₁ - x`, `m₂ = j₂ - y`, where `J + M = 2J - k`,
`J - M + 1 = k + 1`, `j₁ - m₁ = x` and `j₁ + m₁ + 1 = n₁ + 1 - x`. -/
theorem cg_recursion {p : ℕ} (hp : p ≤ min n₁ n₂) (k x y : ℕ) :
    √(((k : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - k)) * cgCoeff n₁ n₂ p (k + 1) x y =
      √((x : ℝ) * ((n₁ : ℝ) + 1 - x)) * cgCoeff n₁ n₂ p k (x - 1) y +
        √((y : ℝ) * ((n₂ : ℝ) + 1 - y)) * cgCoeff n₁ n₂ p k x (y - 1) := by
  set P := pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p k) with hPdef
  set a : ℝ := ((k : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - k) with ha
  have hP1 : pairIp n₁ n₂ (cgLadder n₁ n₂ p (k + 1)) (cgLadder n₁ n₂ p (k + 1)) = a * P :=
    pairIp_cgLadder_succ hp k
  have hR : √((x : ℝ) * ((n₁ : ℝ) + 1 - x)) * cgCoeff n₁ n₂ p k (x - 1) y +
        √((y : ℝ) * ((n₂ : ℝ) + 1 - y)) * cgCoeff n₁ n₂ p k x (y - 1) =
      cgAmp n₁ n₂ p (k + 1) x y * √(spinN n₁ x * spinN n₂ y) / √P := by
    by_cases hr : x ≤ n₁ ∧ y ≤ n₂
    · rw [cgAmp_succ hr.1 hr.2, cgCoeff, cgCoeff]
      have t1 : √((x : ℝ) * ((n₁ : ℝ) + 1 - x)) *
          (cgAmp n₁ n₂ p k (x - 1) y * √(spinN n₁ (x - 1) * spinN n₂ y) / √P) =
          (if x = 0 then 0 else cgAmp n₁ n₂ p k (x - 1) y) * √(spinN n₁ x * spinN n₂ y) / √P := by
        split_ifs with h0
        · subst h0; simp
        · obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
          have hx : (0 : ℝ) ≤ ((x' + 1 : ℕ) : ℝ) * ((n₁ : ℝ) + 1 - ((x' + 1 : ℕ) : ℝ)) := by
            have : ((x' + 1 : ℕ) : ℝ) ≤ n₁ := by exact_mod_cast hr.1
            push_cast at this ⊢; nlinarith
          rw [Nat.add_sub_cancel, spinN_succ,
            show spinN n₁ x' * (((x' : ℝ) + 1) * ((n₁ : ℝ) - x')) * spinN n₂ y =
              (((x' + 1 : ℕ) : ℝ) * ((n₁ : ℝ) + 1 - ((x' + 1 : ℕ) : ℝ))) *
                (spinN n₁ x' * spinN n₂ y) by push_cast; ring,
            Real.sqrt_mul hx]
          ring
      have t2 : √((y : ℝ) * ((n₂ : ℝ) + 1 - y)) *
          (cgAmp n₁ n₂ p k x (y - 1) * √(spinN n₁ x * spinN n₂ (y - 1)) / √P) =
          (if y = 0 then 0 else cgAmp n₁ n₂ p k x (y - 1)) * √(spinN n₁ x * spinN n₂ y) / √P := by
        split_ifs with h0
        · subst h0; simp
        · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
          have hy : (0 : ℝ) ≤ ((y' + 1 : ℕ) : ℝ) * ((n₂ : ℝ) + 1 - ((y' + 1 : ℕ) : ℝ)) := by
            have : ((y' + 1 : ℕ) : ℝ) ≤ n₂ := by exact_mod_cast hr.2
            push_cast at this ⊢; nlinarith
          rw [Nat.add_sub_cancel, spinN_succ,
            show spinN n₁ x * (spinN n₂ y' * (((y' : ℝ) + 1) * ((n₂ : ℝ) - y'))) =
              (((y' + 1 : ℕ) : ℝ) * ((n₂ : ℝ) + 1 - ((y' + 1 : ℕ) : ℝ))) *
                (spinN n₁ x * spinN n₂ y') by push_cast; ring,
            Real.sqrt_mul hy]
          ring
      rw [t1, t2]; ring
    · rw [cgAmp_of_not hr, zero_mul, zero_div]
      have t1 : √((x : ℝ) * ((n₁ : ℝ) + 1 - x)) * cgCoeff n₁ n₂ p k (x - 1) y = 0 := by
        by_cases hx1 : x = n₁ + 1
        · subst hx1; push_cast; simp
        · rw [cgCoeff_of_not (by omega), mul_zero]
      have t2 : √((y : ℝ) * ((n₂ : ℝ) + 1 - y)) * cgCoeff n₁ n₂ p k x (y - 1) = 0 := by
        by_cases hy1 : y = n₂ + 1
        · subst hy1; push_cast; simp
        · rw [cgCoeff_of_not (by omega), mul_zero]
      rw [t1, t2, add_zero]
  rw [hR, cgCoeff, hP1]
  by_cases hP0 : P = 0
  · simp [hP0]
  have hPpos : 0 < P := lt_of_le_of_ne (pairIp_self_nonneg _) (Ne.symm hP0)
  by_cases ha0 : a ≤ 0
  · have hz : cgLadder n₁ n₂ p (k + 1) = 0 := by
      refine eq_zero_of_pairIp_self ?_
      rw [hP1]
      exact le_antisymm (mul_nonpos_of_nonpos_of_nonneg ha0 hPpos.le)
        (hP1 ▸ pairIp_self_nonneg _)
    have hamp : cgAmp n₁ n₂ p (k + 1) x y = 0 := by
      unfold cgAmp; split_ifs
      · rw [hz]; rfl
      · rfl
    simp [hamp]
  · push Not at ha0
    rw [Real.sqrt_mul ha0.le]
    have h1 : √a ≠ 0 := (Real.sqrt_pos.mpr ha0).ne'
    have h2 : √P ≠ 0 := (Real.sqrt_pos.mpr hPpos).ne'
    field_simp

end CG

/-! ### Racah's formula -/

/-- `1/n!` for `n ≥ 0`, extended by zero to negative integers. -/
noncomputable def invFact (n : ℤ) : ℝ := if 0 ≤ n then ((n.toNat).factorial : ℝ)⁻¹ else 0

lemma invFact_natCast (n : ℕ) : invFact (n : ℤ) = ((n.factorial : ℕ) : ℝ)⁻¹ := by
  rw [invFact, ite_eq_left (by positivity), Int.toNat_natCast]

lemma invFact_of_neg {n : ℤ} (h : n < 0) : invFact n = 0 := by
  rw [invFact, ite_eq_right (by omega)]

lemma invFact_eq (n : ℤ) : invFact n = ((n : ℝ) + 1) * invFact (n + 1) := by
  rcases lt_or_ge n (-1) with h | h
  · rw [invFact_of_neg (by omega), invFact_of_neg (by omega), mul_zero]
  rcases eq_or_lt_of_le h with h | h
  · subst h; rw [invFact_of_neg (by omega)]; push_cast; ring
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, invFact_natCast, invFact_natCast,
    Nat.factorial_succ]
  push_cast
  field_simp

lemma invFact_sub_one (m : ℤ) : invFact (m - 1) = (m : ℝ) * invFact m := by
  have := invFact_eq (m - 1)
  rw [sub_add_cancel] at this
  rw [this]; push_cast; ring

/-- The six-factor product in Racah's sum. -/
noncomputable def racahTerm (n₁ n₂ p : ℕ) (x y z : ℤ) : ℝ :=
  invFact z * invFact (p - z) * invFact (x - z) * invFact (n₂ - y - z) *
    invFact (n₁ - p - x + z) * invFact (y - p + z)

/-- Racah's sum with integer labels. -/
noncomputable def racahZ (n₁ n₂ p : ℕ) (x y : ℤ) : ℝ :=
  ∑ z ∈ Finset.range (p + 1), (-1 : ℝ) ^ z * racahTerm n₁ n₂ p x y z

lemma racah_term (a b c d e g : ℤ) :
    ((e : ℝ) + b + 1) *
        (invFact a * invFact b * invFact (c - 1) * invFact d * invFact (e + 1) * invFact g) +
      ((d : ℝ) + a + 1) *
        (invFact a * invFact b * invFact c * invFact (d + 1) * invFact e * invFact (g - 1)) =
    ((c : ℝ) + g) * (invFact a * invFact b * invFact c * invFact d * invFact e * invFact g) +
      invFact a * invFact (b - 1) * invFact (c - 1) * invFact d * invFact (e + 1) * invFact g +
      invFact (a - 1) * invFact b * invFact c * invFact (d + 1) * invFact e * invFact (g - 1) := by
  rw [invFact_sub_one c, invFact_sub_one g, invFact_sub_one b, invFact_sub_one a,
    invFact_eq e, invFact_eq d]
  ring

lemma alt_sum_telescope (p : ℕ) (F G : ℕ → ℝ) (hG0 : G 0 = 0) (hGF : ∀ z, G (z + 1) = F z) :
    ∑ z ∈ Finset.range (p + 1), (-1 : ℝ) ^ z * (F z + G z) = (-1) ^ p * F p := by
  induction p with
  | zero => simp [hG0]
  | succ p ih => rw [Finset.sum_range_succ, ih, hGF, pow_succ]; ring

/-- The recursion of Racah's sum. -/
lemma racahZ_rec (n₁ n₂ p : ℕ) (x y : ℤ) :
    ((n₁ : ℝ) - x + 1) * racahZ n₁ n₂ p (x - 1) y + ((n₂ : ℝ) - y + 1) * racahZ n₁ n₂ p x (y - 1) =
      ((x : ℝ) + y - p) * racahZ n₁ n₂ p x y := by
  set F : ℕ → ℝ := fun z => invFact z * invFact ((p : ℤ) - z - 1) * invFact (x - z - 1) *
    invFact (n₂ - y - z) * invFact (n₁ - p - x + z + 1) * invFact (y - p + z)
  set G : ℕ → ℝ := fun z => invFact ((z : ℤ) - 1) * invFact ((p : ℤ) - z) * invFact (x - z) *
    invFact (n₂ - y - z + 1) * invFact (n₁ - p - x + z) * invFact (y - p + z - 1)
  have key : ∀ z : ℕ, ((n₁ : ℝ) - x + 1) * racahTerm n₁ n₂ p (x - 1) y z +
      ((n₂ : ℝ) - y + 1) * racahTerm n₁ n₂ p x (y - 1) z =
      ((x : ℝ) + y - p) * racahTerm n₁ n₂ p x y z + (F z + G z) := by
    intro z
    have h := racah_term (z : ℤ) (p - z) (x - z) (n₂ - y - z) (n₁ - p - x + z) (y - p + z)
    simp only [racahTerm, F, G]
    rw [show x - 1 - (z : ℤ) = x - z - 1 by ring,
      show (n₁ : ℤ) - p - (x - 1) + z = n₁ - p - x + z + 1 by ring,
      show (n₂ : ℤ) - (y - 1) - z = n₂ - y - z + 1 by ring,
      show y - 1 - p + (z : ℤ) = y - p + z - 1 by ring]
    push_cast at h ⊢
    linear_combination h
  have hG0 : G 0 = 0 := by simp only [G]; rw [invFact_of_neg (by norm_num)]; ring
  have hGF : ∀ z, G (z + 1) = F z := by
    intro z
    simp only [F, G]
    push_cast
    rw [show (z : ℤ) + 1 - 1 = z by ring, show (p : ℤ) - (z + 1) = p - z - 1 by ring,
      show x - (z + 1) = x - z - 1 by ring, show (n₂ : ℤ) - y - (z + 1) + 1 = n₂ - y - z by ring,
      show (n₁ : ℤ) - p - x + (z + 1) = n₁ - p - x + z + 1 by ring,
      show y - p + (z + 1) - 1 = y - p + z by ring]
  have hFp : F p = 0 := by
    simp only [F]; rw [invFact_of_neg (show (p : ℤ) - p - 1 < 0 by omega)]; ring
  have htel := alt_sum_telescope p F G hG0 hGF
  rw [hFp, mul_zero] at htel
  simp only [racahZ, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  calc _ = ∑ z ∈ Finset.range (p + 1), ((-1 : ℝ) ^ z * (((x : ℝ) + y - p) *
        racahTerm n₁ n₂ p x y z) + (-1) ^ z * (F z + G z)) :=
        Finset.sum_congr rfl fun z _ => by linear_combination (-1 : ℝ) ^ z * key z
    _ = _ := by
        rw [Finset.sum_add_distrib, htel, add_zero]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-- Racah's sum vanishes outside the range of the labels. -/
lemma racahZ_eq_zero (n₁ n₂ p : ℕ) {x y : ℤ} (h : x < 0 ∨ n₁ < x ∨ y < 0 ∨ n₂ < y) :
    racahZ n₁ n₂ p x y = 0 := by
  refine Finset.sum_eq_zero fun z hz => ?_
  have hz' : z ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hz)
  simp only [racahTerm]
  rcases h with h | h | h | h
  · rw [invFact_of_neg (show x - z < 0 by omega)]; ring
  · rw [invFact_of_neg (show (n₁ : ℤ) - p - x + z < 0 by omega)]; ring
  · rw [invFact_of_neg (show y - p + z < 0 by omega)]; ring
  · rw [invFact_of_neg (show (n₂ : ℤ) - y - z < 0 by omega)]; ring

lemma invFact_zero : invFact 0 = 1 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, invFact_natCast]; simp

/-- Racah's sum `Σ_z (-1)^z / (z! (p-z)! (x-z)! (n₂-y-z)! (n₁-p-x+z)! (y-p+z)!)` over the `z` for
which all six arguments are nonnegative. -/
noncomputable def racahSum (n₁ n₂ p x y : ℕ) : ℝ :=
  ∑ z ∈ (Finset.range (p + 1)).filter (fun z => z ≤ x ∧ z + y ≤ n₂ ∧ x + p ≤ n₁ + z ∧ p ≤ y + z),
    (-1 : ℝ) ^ z / ((z.factorial * (p - z).factorial * (x - z).factorial *
      (n₂ - y - z).factorial * (n₁ + z - p - x).factorial * (y + z - p).factorial : ℕ) : ℝ)

lemma racahZ_eq_racahSum (n₁ n₂ p x y : ℕ) : racahZ n₁ n₂ p x y = racahSum n₁ n₂ p x y := by
  unfold racahZ racahSum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' : z ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hz)
  simp only [racahTerm]
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    rw [show ((p : ℤ) - z) = ((p - z : ℕ) : ℤ) by omega,
      show ((x : ℤ) - z) = ((x - z : ℕ) : ℤ) by omega,
      show ((n₂ : ℤ) - y - z) = ((n₂ - y - z : ℕ) : ℤ) by omega,
      show ((n₁ : ℤ) - p - x + z) = ((n₁ + z - p - x : ℕ) : ℤ) by omega,
      show ((y : ℤ) - p + z) = ((y + z - p : ℕ) : ℤ) by omega]
    simp only [invFact_natCast]
    push_cast
    field_simp
  · simp only [not_and_or, not_le] at h
    rcases h with h | h | h | h
    · rw [invFact_of_neg (show (x : ℤ) - z < 0 by omega)]; ring
    · rw [invFact_of_neg (show (n₂ : ℤ) - y - z < 0 by omega)]; ring
    · rw [invFact_of_neg (show (n₁ : ℤ) - p - x + z < 0 by omega)]; ring
    · rw [invFact_of_neg (show (y : ℤ) - p + z < 0 by omega)]; ring

/-- The prefactor `D_p = p! (n₁ - p)! / n₁!`. -/
noncomputable def racahD (n₁ p : ℕ) : ℝ :=
  ((p.factorial : ℕ) : ℝ) * ((n₁ - p).factorial : ℕ) / (n₁.factorial : ℕ)

section RacahProof

variable {n₁ n₂ : ℕ}

/-- The highest weight in closed form. -/
lemma cgc_racah {p : ℕ} (hp : p ≤ min n₁ n₂) {x : ℕ} (hx : x ≤ p) :
    cgc (K := ℝ) n₁ n₂ p x * invFact ((n₁ : ℤ) - x) * invFact ((n₂ : ℤ) - p + x) =
      racahD n₁ p * ((-1) ^ x * (invFact x * invFact ((p : ℤ) - x) * invFact ((n₂ : ℤ) - p) *
        invFact ((n₁ : ℤ) - p))) := by
  have hp1 : p ≤ n₁ := le_trans hp (min_le_left _ _)
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  induction x with
  | zero =>
    simp only [cgc, Nat.cast_zero, sub_zero, add_zero, pow_zero, one_mul, invFact_zero]
    rw [show ((n₁ : ℤ) - p) = ((n₁ - p : ℕ) : ℤ) by omega,
      show ((n₂ : ℤ) - p) = ((n₂ - p : ℕ) : ℤ) by omega]
    simp only [invFact_natCast, racahD]
    have h1 : ((n₁.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have h2 : ((p.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have h3 : (((n₁ - p).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  | succ x ih =>
    have ih := ih (by omega)
    have hx1 : (x : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero x
    have hn : (n₁ : ℝ) - x ≠ 0 := by
      have : (x : ℝ) < n₁ := by exact_mod_cast (show x < n₁ by omega)
      exact (sub_pos.mpr this).ne'
    have hrec : cgc (K := ℝ) n₁ n₂ p (x + 1) * (((x : ℝ) + 1) * ((n₁ : ℝ) - x)) =
        -cgc n₁ n₂ p x * (((p : ℝ) - x) * ((n₂ : ℝ) - p + x + 1)) := by
      rw [cgc]; field_simp
    have e1 : invFact ((n₁ : ℤ) - ((x + 1 : ℕ) : ℤ)) = ((n₁ : ℝ) - x) * invFact ((n₁ : ℤ) - x) := by
      rw [show (n₁ : ℤ) - ((x + 1 : ℕ) : ℤ) = (n₁ - x) - 1 by push_cast; ring, invFact_sub_one]
      push_cast; ring
    have e2 : invFact ((n₂ : ℤ) - p + x) =
        ((n₂ : ℝ) - p + x + 1) * invFact ((n₂ : ℤ) - p + ((x + 1 : ℕ) : ℤ)) := by
      rw [invFact_eq, show (n₂ : ℤ) - p + x + 1 = n₂ - p + ((x + 1 : ℕ) : ℤ) by push_cast; ring]
      push_cast; ring
    have e3 : invFact (x : ℤ) = ((x : ℝ) + 1) * invFact ((x + 1 : ℕ) : ℤ) := by
      rw [invFact_eq, show (x : ℤ) + 1 = ((x + 1 : ℕ) : ℤ) by push_cast; ring]
      push_cast; ring
    have e4 : invFact ((p : ℤ) - ((x + 1 : ℕ) : ℤ)) = ((p : ℝ) - x) * invFact ((p : ℤ) - x) := by
      rw [show (p : ℤ) - ((x + 1 : ℕ) : ℤ) = (p - x) - 1 by push_cast; ring, invFact_sub_one]
      push_cast; ring
    rw [e2, e3] at ih
    rw [e1, e4]
    apply mul_left_cancel₀ hx1
    linear_combination
      (invFact ((n₁ : ℤ) - x) * invFact ((n₂ : ℤ) - p + ((x + 1 : ℕ) : ℤ))) * hrec -
        ((p : ℝ) - x) * ih

/-- **Racah's sum for the unnormalized components**:
`(J₋)^k hw_p` has component `k! D_p (n₁ - x)! (n₂ - y)! S(x, y)` along `e_x ⊗ e_y`. -/
theorem cgAmp_racah {p : ℕ} (hp : p ≤ min n₁ n₂) (k : ℕ) :
    ∀ x y : ℕ, x + y = p + k →
      cgAmp n₁ n₂ p k x y * invFact ((n₁ : ℤ) - x) * invFact ((n₂ : ℤ) - y) =
        (k.factorial : ℝ) * racahD n₁ p * racahZ n₁ n₂ p x y := by
  induction k with
  | zero =>
    intro x y hxy
    by_cases hr : x ≤ n₁ ∧ y ≤ n₂
    · rw [cgAmp, dite_eq_left hr, cgLadder_zero, hw_of_eq (by simpa using hxy)]
      have hx : x ≤ p := by omega
      have hy : (y : ℤ) = p - x := by omega
      have hZ : racahZ n₁ n₂ p x y = (-1) ^ x * (invFact x * invFact ((p : ℤ) - x) *
          invFact ((n₂ : ℤ) - p) * invFact ((n₁ : ℤ) - p)) := by
        unfold racahZ
        rw [Finset.sum_eq_single x]
        · simp only [racahTerm]
          rw [hy, show (x : ℤ) - x = 0 by ring, show (n₂ : ℤ) - (p - x) - x = n₂ - p by ring,
            show (n₁ : ℤ) - p - x + x = n₁ - p by ring, show (p : ℤ) - x - p + x = 0 by ring,
            invFact_zero]
          ring
        · intro z _ hzx
          simp only [racahTerm]
          rcases lt_or_gt_of_ne hzx with h | h
          · rw [invFact_of_neg (show (y : ℤ) - p + z < 0 by omega)]; ring
          · rw [invFact_of_neg (show (x : ℤ) - z < 0 by omega)]; ring
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [hZ, hy, show (n₂ : ℤ) - (p - x) = n₂ - p + x by ring]
      have := cgc_racah (n₁ := n₁) (n₂ := n₂) hp hx
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
      exact this
    · rw [cgAmp_of_not hr, racahZ_eq_zero n₁ n₂ p (by omega)]; ring
  | succ k ih =>
    intro x y hxy
    by_cases hr : x ≤ n₁ ∧ y ≤ n₂
    · have t1 : (if x = 0 then 0 else cgAmp n₁ n₂ p k (x - 1) y) * invFact ((n₁ : ℤ) - x) *
          invFact ((n₂ : ℤ) - y) =
          ((n₁ : ℝ) - x + 1) *
            ((k.factorial : ℝ) * racahD n₁ p * racahZ n₁ n₂ p ((x : ℤ) - 1) y) := by
        split_ifs with h0
        · subst h0; rw [racahZ_eq_zero n₁ n₂ p (Or.inl (by norm_num))]; ring
        · have := ih (x - 1) y (by omega)
          rw [show ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 by omega] at this
          rw [← this, invFact_eq ((n₁ : ℤ) - x), show (n₁ : ℤ) - x + 1 = n₁ - (x - 1) by ring]
          push_cast; ring
      have t2 : (if y = 0 then 0 else cgAmp n₁ n₂ p k x (y - 1)) * invFact ((n₁ : ℤ) - x) *
          invFact ((n₂ : ℤ) - y) =
          ((n₂ : ℝ) - y + 1) *
            ((k.factorial : ℝ) * racahD n₁ p * racahZ n₁ n₂ p x ((y : ℤ) - 1)) := by
        split_ifs with h0
        · subst h0; rw [racahZ_eq_zero n₁ n₂ p (Or.inr (Or.inr (Or.inl (by norm_num))))]; ring
        · have := ih x (y - 1) (by omega)
          rw [show ((y - 1 : ℕ) : ℤ) = (y : ℤ) - 1 by omega] at this
          rw [← this, invFact_eq ((n₂ : ℤ) - y), show (n₂ : ℤ) - y + 1 = n₂ - (y - 1) by ring]
          push_cast; ring
      rw [cgAmp_succ hr.1 hr.2, add_mul, add_mul, t1, t2]
      have hrec := racahZ_rec n₁ n₂ p x y
      push_cast at hrec
      have hk : (x : ℝ) + y - p = k + 1 := by
        have : ((x + y : ℕ) : ℝ) = ((p + (k + 1) : ℕ) : ℝ) := by rw [hxy]
        push_cast at this; linarith
      rw [hk] at hrec
      rw [Nat.factorial_succ]; push_cast
      linear_combination ((k.factorial : ℝ) * racahD n₁ p) * hrec
    · rw [cgAmp_of_not hr, racahZ_eq_zero n₁ n₂ p (by omega)]; ring

end RacahProof

/-- A Vandermonde-type identity:
`Σ_{x ≤ p} C(r + x, r) C(t + p - x, t) = C(r + t + 1 + p, r + t + 1)`. -/
lemma sum_choose_mul_choose (r t p : ℕ) :
    ∑ x ∈ Finset.range (p + 1), (r + x).choose r * (t + (p - x)).choose t =
      (r + t + 1 + p).choose (r + t + 1) := by
  have h := congrArg (PowerSeries.coeff p)
    (show (PowerSeries.mk 1 : PowerSeries ℤ) ^ (r + 1) * (PowerSeries.mk 1) ^ (t + 1) =
      (PowerSeries.mk 1) ^ ((r + t + 1) + 1) by rw [← pow_add]; congr 1; omega)
  rw [PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.mk_one_pow_eq_mk_choose_add,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mul, PowerSeries.coeff_mk] at h
  simp only [PowerSeries.coeff_mk] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => ((r + i).choose r : ℤ) * ((t + j).choose t : ℤ))] at h
  exact_mod_cast h

section RacahNorm

variable {n₁ n₂ : ℕ}

lemma pairIp_cgLadder_eq_sum (p k : ℕ) :
    pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p k) =
      ∑ x ∈ Finset.range (n₁ + 1), ∑ y ∈ Finset.range (n₂ + 1),
        cgAmp n₁ n₂ p k x y * cgAmp n₁ n₂ p k x y * (spinN n₁ x * spinN n₂ y) := by
  rw [Finset.sum_range]
  simp_rw [Finset.sum_range]
  unfold pairIp
  rw [Fintype.sum_prod_type]
  simp only [cgAmp_fin]

lemma pairIp_hw_eq_sum {p : ℕ} (hp : p ≤ min n₁ n₂) :
    pairIp n₁ n₂ (cgLadder n₁ n₂ p 0) (cgLadder n₁ n₂ p 0) =
      ∑ x ∈ Finset.range (p + 1), cgAmp n₁ n₂ p 0 x (p - x) * cgAmp n₁ n₂ p 0 x (p - x) *
        (spinN n₁ x * spinN n₂ (p - x)) := by
  have hp1 : p ≤ n₁ := le_trans hp (min_le_left _ _)
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  rw [pairIp_cgLadder_eq_sum,
    ← Finset.sum_subset (Finset.range_subset_range.mpr (show p + 1 ≤ n₁ + 1 by omega))]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [Finset.sum_eq_single (p - x)]
    · intro y _ hy; rw [cgAmp_eq_zero (by omega)]; ring
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro x _ hx
    have hx' : p < x := by simpa using hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [cgAmp_eq_zero (by omega)]; ring

/-- The `x`-th term of the norm of the highest weight. -/
lemma hw_term {p : ℕ} (hp : p ≤ min n₁ n₂) {x : ℕ} (hx : x ≤ p) :
    cgAmp n₁ n₂ p 0 x (p - x) * cgAmp n₁ n₂ p 0 x (p - x) * (spinN n₁ x * spinN n₂ (p - x)) =
      racahD n₁ p ^ 2 * (n₁.factorial : ℕ) * (n₂.factorial : ℕ) /
          (((n₂ - p).factorial : ℕ) * ((n₁ - p).factorial : ℕ)) *
        (((n₂ - p + x).choose (n₂ - p) : ℕ) * ((n₁ - p + (p - x)).choose (n₁ - p) : ℕ)) := by
  have hp1 : p ≤ n₁ := le_trans hp (min_le_left _ _)
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  have hA := cgAmp_racah hp 0 x (p - x) (by omega)
  rw [show (n₂ : ℤ) - ((p - x : ℕ) : ℤ) = ((n₂ - p + x : ℕ) : ℤ) by omega,
    show (n₁ : ℤ) - x = ((n₁ - x : ℕ) : ℤ) by omega, invFact_natCast, invFact_natCast,
    racahZ_eq_racahSum] at hA
  -- the sum has the single term `z = x`
  have hS : racahSum n₁ n₂ p x (p - x) = (-1) ^ x / ((x.factorial * (p - x).factorial *
      (n₂ - p).factorial * (n₁ - p).factorial : ℕ) : ℝ) := by
    unfold racahSum
    rw [Finset.sum_eq_single x]
    · congr 2
      rw [Nat.sub_self, show n₂ - (p - x) - x = n₂ - p by omega,
        show n₁ + x - p - x = n₁ - p by omega, show p - x + x - p = 0 by omega]
      simp
    · intro z hz hzx
      simp only [Finset.mem_filter] at hz
      omega
    · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        by omega⟩) h
  rw [hS] at hA
  have e1 : spinN n₁ x =
      (x.factorial : ℕ) * ((n₁.factorial : ℕ) : ℝ) / ((n₁ - x).factorial : ℕ) := by
    rw [spinN_eq, eq_div_iff (by positivity),
      ← Nat.factorial_mul_descFactorial (show x ≤ n₁ by omega)]
    push_cast; ring
  have e2 : spinN n₂ (p - x) = ((p - x).factorial : ℕ) * ((n₂.factorial : ℕ) : ℝ) /
      ((n₂ - p + x).factorial : ℕ) := by
    rw [spinN_eq, eq_div_iff (by positivity), show n₂ - p + x = n₂ - (p - x) by omega,
      ← Nat.factorial_mul_descFactorial (show p - x ≤ n₂ by omega)]
    push_cast; ring
  have c1 : (((n₂ - p + x).choose (n₂ - p) : ℕ) : ℝ) = ((n₂ - p + x).factorial : ℕ) /
      (((n₂ - p).factorial : ℕ) * (x.factorial : ℕ)) := by
    rw [eq_div_iff (by positivity)]
    have := Nat.choose_mul_factorial_mul_factorial (show n₂ - p ≤ n₂ - p + x by omega)
    rw [show n₂ - p + x - (n₂ - p) = x by omega] at this
    rw [← this]; push_cast; ring
  have c2 : (((n₁ - p + (p - x)).choose (n₁ - p) : ℕ) : ℝ) = ((n₁ - x).factorial : ℕ) /
      (((n₁ - p).factorial : ℕ) * ((p - x).factorial : ℕ)) := by
    rw [eq_div_iff (by positivity), show n₁ - p + (p - x) = n₁ - x by omega]
    have := Nat.choose_mul_factorial_mul_factorial (show n₁ - p ≤ n₁ - x by omega)
    rw [show n₁ - x - (n₁ - p) = p - x by omega] at this
    rw [← this]; push_cast; ring
  rw [e1, e2, c1, c2]
  have h1 : ((n₁ - x).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n₂ - p + x).factorial : ℝ) ≠ 0 := by positivity
  have hamp : cgAmp n₁ n₂ p 0 x (p - x) = racahD n₁ p * ((-1) ^ x /
      ((x.factorial * (p - x).factorial * (n₂ - p).factorial * (n₁ - p).factorial : ℕ) : ℝ)) *
        ((n₁ - x).factorial : ℕ) * ((n₂ - p + x).factorial : ℕ) := by
    rw [Nat.factorial_zero, Nat.cast_one, one_mul] at hA
    rw [← hA]; field_simp
  rw [hamp]
  push_cast
  have hx1 : ((x.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hx2 : (((p - x).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hx3 : (((n₂ - p).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hx4 : (((n₁ - p).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [pow_mul', neg_one_sq, one_pow, mul_one]

end RacahNorm

section RacahFinal

variable {n₁ n₂ : ℕ}

/-- The norm of the highest weight. -/
lemma pairIp_hw_closed {p : ℕ} (hp : p ≤ min n₁ n₂) :
    pairIp n₁ n₂ (cgLadder n₁ n₂ p 0) (cgLadder n₁ n₂ p 0) =
      racahD n₁ p ^ 2 * (n₁.factorial : ℕ) * (n₂.factorial : ℕ) /
          (((n₂ - p).factorial : ℕ) * ((n₁ - p).factorial : ℕ)) *
        ((n₂ - p + (n₁ - p) + 1 + p).choose (n₂ - p + (n₁ - p) + 1) : ℕ) := by
  rw [pairIp_hw_eq_sum hp, Finset.sum_congr rfl fun x hx =>
    hw_term hp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)), ← Finset.mul_sum]
  congr 1
  have := sum_choose_mul_choose (n₂ - p) (n₁ - p) p
  exact_mod_cast this

/-- The norm of `(J₋)^k hw_p`. -/
lemma pairIp_cgLadder_closed {p : ℕ} (hp : p ≤ min n₁ n₂) (k : ℕ) :
    pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p k) =
      spinN (n₁ + n₂ - 2 * p) k * pairIp n₁ n₂ (cgLadder n₁ n₂ p 0) (cgLadder n₁ n₂ p 0) := by
  have h2p : 2 * p ≤ n₁ + n₂ := by
    have := min_le_left n₁ n₂; have := min_le_right n₁ n₂; omega
  induction k with
  | zero => simp [spinN]
  | succ k ih =>
    rw [pairIp_cgLadder_succ hp, ih, spinN_succ]
    push_cast [Nat.cast_sub h2p]
    ring

/-- **Racah's formula**
`⟨j₁ m₁; j₂ m₂ | J M⟩ = √((2J + 1)(J + j₁ - j₂)! (J - j₁ + j₂)! (j₁ + j₂ - J)! / (j₁ + j₂ + J + 1)!)
  · √((J + M)! (J - M)! (j₁ - m₁)! (j₁ + m₁)! (j₂ - m₂)! (j₂ + m₂)!)
  · Σ_z (-1)^z / (z! (j₁ + j₂ - J - z)! (j₁ - m₁ - z)! (j₂ + m₂ - z)!
      (J - j₂ + m₁ + z)! (J - j₁ - m₂ + z)!)`
for `M = m₁ + m₂`. In the labels `J = j₁ + j₂ - p`, `M = J - k`, `m₁ = j₁ - x`, `m₂ = j₂ - y` this
reads `2J + 1 = n₁ + n₂ - 2p + 1`, `J + j₁ - j₂ = n₁ - p`, `J - j₁ + j₂ = n₂ - p`,
`j₁ + j₂ - J = p`, `J + M = n₁ + n₂ - 2p - k`, `J - M = k`, `j₁ ∓ m₁ = x, n₁ - x` and
`j₂ ∓ m₂ = y, n₂ - y`, and the sum is `racahSum`. -/
theorem cg_racah {p k x y : ℕ} (hp : p ≤ min n₁ n₂) (hk : k ≤ n₁ + n₂ - 2 * p) (hx : x ≤ n₁)
    (hy : y ≤ n₂) (hxy : x + y = p + k) :
    cgCoeff n₁ n₂ p k x y =
      √(((n₁ + n₂ - 2 * p + 1 : ℕ) : ℝ) * ((n₁ - p).factorial : ℕ) * ((n₂ - p).factorial : ℕ) *
          (p.factorial : ℕ) / ((n₁ + n₂ - p + 1).factorial : ℕ)) *
        √((((n₁ + n₂ - 2 * p - k).factorial : ℕ) : ℝ) * (k.factorial : ℕ) * (x.factorial : ℕ) *
          ((n₁ - x).factorial : ℕ) * (y.factorial : ℕ) * ((n₂ - y).factorial : ℕ)) *
        racahSum n₁ n₂ p x y := by
  have hp1 : p ≤ n₁ := le_trans hp (min_le_left _ _)
  have hp2 : p ≤ n₂ := le_trans hp (min_le_right _ _)
  have hA := cgAmp_racah hp k x y hxy
  rw [show (n₁ : ℤ) - x = ((n₁ - x : ℕ) : ℤ) by omega,
    show (n₂ : ℤ) - y = ((n₂ - y : ℕ) : ℤ) by omega, invFact_natCast, invFact_natCast,
    racahZ_eq_racahSum] at hA
  have ha : (((n₁ - x).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hb : (((n₂ - y).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hamp : cgAmp n₁ n₂ p k x y = (k.factorial : ℕ) * racahD n₁ p *
      (((n₁ - x).factorial : ℕ) * ((n₂ - y).factorial : ℕ)) * racahSum n₁ n₂ p x y := by
    calc cgAmp n₁ n₂ p k x y = cgAmp n₁ n₂ p k x y * (((n₁ - x).factorial : ℕ) : ℝ)⁻¹ *
          (((n₂ - y).factorial : ℕ) : ℝ)⁻¹ *
          ((((n₁ - x).factorial : ℕ) : ℝ) * (((n₂ - y).factorial : ℕ) : ℝ)) := by field_simp
      _ = _ := by rw [hA]; ring
  have hPpos := pairIp_self_pos (cgLadder_ne_zero hp hk)
  have hN : 0 ≤ spinN n₁ x * spinN n₂ y := mul_nonneg (spinN_nonneg _ _) (spinN_nonneg _ _)
  have hD : 0 ≤ racahD n₁ p := by unfold racahD; positivity
  rw [cgCoeff, hamp]
  have hαβ : (k.factorial : ℕ) * racahD n₁ p *
      (((n₁ - x).factorial : ℕ) * ((n₂ - y).factorial : ℕ)) * √(spinN n₁ x * spinN n₂ y) /
        √(pairIp n₁ n₂ (cgLadder n₁ n₂ p k) (cgLadder n₁ n₂ p k)) =
      √(((n₁ + n₂ - 2 * p + 1 : ℕ) : ℝ) * ((n₁ - p).factorial : ℕ) * ((n₂ - p).factorial : ℕ) *
          (p.factorial : ℕ) / ((n₁ + n₂ - p + 1).factorial : ℕ)) *
        √((((n₁ + n₂ - 2 * p - k).factorial : ℕ) : ℝ) * (k.factorial : ℕ) * (x.factorial : ℕ) *
          ((n₁ - x).factorial : ℕ) * (y.factorial : ℕ) * ((n₂ - y).factorial : ℕ)) := by
    have hA1 : 0 ≤ ((n₁ + n₂ - 2 * p + 1 : ℕ) : ℝ) * ((n₁ - p).factorial : ℕ) *
        ((n₂ - p).factorial : ℕ) * (p.factorial : ℕ) / ((n₁ + n₂ - p + 1).factorial : ℕ) := by
      positivity
    have hA2 : 0 ≤ (((n₁ + n₂ - 2 * p - k).factorial : ℕ) : ℝ) * (k.factorial : ℕ) *
        (x.factorial : ℕ) * ((n₁ - x).factorial : ℕ) * (y.factorial : ℕ) *
        ((n₂ - y).factorial : ℕ) := by positivity
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt hN, Real.sq_sqrt hPpos.le, Real.sq_sqrt hA1, Real.sq_sqrt hA2,
      pairIp_cgLadder_closed hp k, pairIp_hw_closed hp,
      show n₂ - p + (n₁ - p) + 1 + p = n₁ + n₂ - p + 1 by omega,
      show n₂ - p + (n₁ - p) + 1 = n₁ + n₂ - 2 * p + 1 by omega]
    have e1 : spinN n₁ x =
        (x.factorial : ℕ) * ((n₁.factorial : ℕ) : ℝ) / ((n₁ - x).factorial : ℕ) := by
      rw [spinN_eq, eq_div_iff (by positivity), ← Nat.factorial_mul_descFactorial hx]
      push_cast; ring
    have e2 : spinN n₂ y =
        (y.factorial : ℕ) * ((n₂.factorial : ℕ) : ℝ) / ((n₂ - y).factorial : ℕ) := by
      rw [spinN_eq, eq_div_iff (by positivity), ← Nat.factorial_mul_descFactorial hy]
      push_cast; ring
    have e3 : spinN (n₁ + n₂ - 2 * p) k =
        (k.factorial : ℕ) * (((n₁ + n₂ - 2 * p).factorial : ℕ) : ℝ) /
          ((n₁ + n₂ - 2 * p - k).factorial : ℕ) := by
      rw [spinN_eq, eq_div_iff (by positivity), ← Nat.factorial_mul_descFactorial hk]
      push_cast; ring
    have e4 : (((n₁ + n₂ - p + 1).choose (n₁ + n₂ - 2 * p + 1) : ℕ) : ℝ) =
        ((n₁ + n₂ - p + 1).factorial : ℕ) / (((n₁ + n₂ - 2 * p + 1 : ℕ) : ℝ) *
          ((n₁ + n₂ - 2 * p).factorial : ℕ) * (p.factorial : ℕ)) := by
      rw [eq_div_iff (by positivity)]
      have := Nat.choose_mul_factorial_mul_factorial
        (show n₁ + n₂ - 2 * p + 1 ≤ n₁ + n₂ - p + 1 by omega)
      rw [show n₁ + n₂ - p + 1 - (n₁ + n₂ - 2 * p + 1) = p by omega, Nat.factorial_succ] at this
      rw [← this]; push_cast; ring
    rw [e1, e2, e3, e4, racahD]
    have f1 : ((n₁.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f2 : ((n₂.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f3 : ((p.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f4 : (((n₁ - p).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f5 : (((n₂ - p).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f6 : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f7 : (((n₁ + n₂ - 2 * p).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f8 : (((n₁ + n₂ - 2 * p - k).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f9 : (((n₁ + n₂ - p + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f10 : (((n₁ + n₂ - 2 * p + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have f11 : ((x.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have f12 : ((y.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [show ∀ a b c d : ℝ, a * b * c / d = a * c / d * b from fun _ _ _ _ => by ring, hαβ]

end RacahFinal

end QM
