/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.Spin.ThreeJ

/-!
# Ladders and the coupling of angular momenta in orthonormal coordinates

A spin system (`SpinSys`) is a space of real functions on a finite set with lowering and raising
operators `L` and `R = Lᵀ`. A ladder of spin `j = n/2` (`IsLadder`) is a sequence
`f 0, f 1, …, f n` with `L f_k = c_k f_{k+1}` and `R f_{k+1} = c_k f_k`, where
`c_k = √((k + 1)(n - k))` (`lc`) is the matrix element of `J₋` between `|j, j - k⟩` and
`|j, j - k - 1⟩`. These two relations alone imply that ladders of different spin, or different `M`,
are orthogonal, and that the overlap of two ladders of the same spin does not depend on `M`
(`IsLadder.dotp_eq_zero`, `IsLadder.dotp_const`).

A single spin is a ladder on `Fin (n + 1)` (`oneSys`, `oneVec`). Two ladders couple to ladders of
the product system with Clebsch–Gordan coefficients (`IsLadder.couple`), which needs the recursion
of the coefficients obtained from `J₊` (`cg_raise`, `cg_raise_top`).

## Main results

* `cg_raise`, `cg_raise_top`: the `J₊` recursion of the Clebsch–Gordan coefficients.
* `IsLadder.dotp_eq_zero`, `IsLadder.dotp_const`: orthogonality and independence of `M`.
* `IsLadder.couple`: coupling two ladders gives a ladder.
-/

namespace QM

/-- `c_k = √((k + 1)(n - k))`, the matrix element of `J₋` from `|j, j - k⟩` to `|j, j - k - 1⟩`
for `n = 2j`. It vanishes for `k ≥ n`. -/
noncomputable def lc (n k : ℕ) : ℝ := √(((k + 1) * (n - k) : ℕ) : ℝ)

lemma lc_eq {n k : ℕ} (h : k ≤ n) : lc n k = √(((k : ℝ) + 1) * ((n : ℝ) - k)) := by
  rw [lc]; push_cast [Nat.cast_sub h]; rfl

lemma lc_of_le {n k : ℕ} (h : n ≤ k) : lc n k = 0 := by
  rw [lc, Nat.sub_eq_zero_of_le h]; simp

lemma lc_mul_self (n k : ℕ) : lc n k * lc n k = (((k + 1) * (n - k) : ℕ) : ℝ) :=
  Real.mul_self_sqrt (Nat.cast_nonneg _)

lemma lc_nonneg (n k : ℕ) : 0 ≤ lc n k := Real.sqrt_nonneg _

/-! ### The `J₊` recursion of the Clebsch–Gordan coefficients -/

section Raise

variable {n₁ n₂ : ℕ}

lemma pairJp_cgLadder_apply (p K : ℕ) {x y : ℕ} (hx : x ≤ n₁) (hy : y ≤ n₂) :
    pairJp n₁ n₂ (cgLadder n₁ n₂ p K) (⟨x, Nat.lt_succ_of_le hx⟩, ⟨y, Nat.lt_succ_of_le hy⟩) =
      ((x : ℝ) + 1) * ((n₁ : ℝ) - x) * cgAmp n₁ n₂ p K (x + 1) y +
        ((y : ℝ) + 1) * ((n₂ : ℝ) - y) * cgAmp n₁ n₂ p K x (y + 1) := by
  rw [pairJp_apply]
  congr 1
  · by_cases h : x < n₁
    · rw [dite_eq_left h, cgAmp, dite_eq_left ⟨h, hy⟩]
    · have : x = n₁ := by omega
      subst this
      rw [dite_eq_right h]; ring
  · by_cases h : y < n₂
    · rw [dite_eq_left h, cgAmp, dite_eq_left ⟨hx, h⟩]
    · have : y = n₂ := by omega
      subst this
      rw [dite_eq_right h]; ring

/-- The `J₊` recursion for the unnormalized components. -/
lemma cgAmp_raise {p : ℕ} (hp : p ≤ min n₁ n₂) (K : ℕ) {x y : ℕ} (hx : x ≤ n₁) (hy : y ≤ n₂) :
    ((x : ℝ) + 1) * ((n₁ : ℝ) - x) * cgAmp n₁ n₂ p (K + 1) (x + 1) y +
        ((y : ℝ) + 1) * ((n₂ : ℝ) - y) * cgAmp n₁ n₂ p (K + 1) x (y + 1) =
      ((K : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - K) * cgAmp n₁ n₂ p K x y := by
  rw [← pairJp_cgLadder_apply _ _ hx hy, cgLadder,
    (isSU2_pair (K := ℝ) n₁ n₂).Sp_ladder_succ (pairJp_hw (K := ℝ) hp) (pairJz_hw (K := ℝ) p) K,
    Pi.smul_apply, smul_eq_mul, cgAmp, dite_eq_left ⟨hx, hy⟩]
  ring

lemma cgAmp_raise_top {p : ℕ} (hp : p ≤ min n₁ n₂) {x y : ℕ} (hx : x ≤ n₁) (hy : y ≤ n₂) :
    ((x : ℝ) + 1) * ((n₁ : ℝ) - x) * cgAmp n₁ n₂ p 0 (x + 1) y +
        ((y : ℝ) + 1) * ((n₂ : ℝ) - y) * cgAmp n₁ n₂ p 0 x (y + 1) = 0 := by
  rw [← pairJp_cgLadder_apply _ _ hx hy, cgLadder_zero, pairJp_hw hp]; rfl

/-- `√((x + 1)(n - x)) √(N_{x+1}) = (x + 1)(n - x) √(N_x)`. -/
lemma lc_mul_sqrt_spinN (n x : ℕ) (c : ℝ) :
    lc n x * √(spinN n (x + 1) * c) = ((x : ℝ) + 1) * ((n : ℝ) - x) * √(spinN n x * c) := by
  rcases le_or_gt n x with h | h
  · rw [lc_of_le h, zero_mul]
    rcases eq_or_lt_of_le h with h' | h'
    · subst h'; ring
    · rw [spinN_eq_zero h']; simp
  · have hw : (0 : ℝ) ≤ ((x : ℝ) + 1) * ((n : ℝ) - x) := by
      have : (x : ℝ) < n := by exact_mod_cast h
      nlinarith
    rw [lc_eq h.le, spinN_succ,
      show spinN n x * (((x : ℝ) + 1) * ((n : ℝ) - x)) * c =
        (((x : ℝ) + 1) * ((n : ℝ) - x)) * (spinN n x * c) by ring,
      Real.sqrt_mul hw, ← mul_assoc, Real.mul_self_sqrt hw]

/-- **The `J₊` recursion** `√((J - M + 1)(J + M)) ⟨m₁ m₂ | J, M⟩ = √((j₁ - m₁ + 1)(j₁ + m₁))
⟨m₁ - 1, m₂ | J, M + 1⟩ + …`, in the labels `M = J - K - 1`: here `lc n x = √((x + 1)(n - x))`. -/
theorem cg_raise {p : ℕ} (hp : p ≤ min n₁ n₂) (K x y : ℕ) :
    lc (n₁ + n₂ - 2 * p) K * cgCoeff n₁ n₂ p K x y =
      lc n₁ x * cgCoeff n₁ n₂ p (K + 1) (x + 1) y +
        lc n₂ y * cgCoeff n₁ n₂ p (K + 1) x (y + 1) := by
  have h2p : 2 * p ≤ n₁ + n₂ := by
    have := min_le_left n₁ n₂; have := min_le_right n₁ n₂; omega
  by_cases hr : x ≤ n₁ ∧ y ≤ n₂
  swap
  · rw [cgCoeff_of_not hr, mul_zero]
    have t1 : lc n₁ x * cgCoeff n₁ n₂ p (K + 1) (x + 1) y = 0 := by
      by_cases hx : n₁ ≤ x
      · rw [lc_of_le hx, zero_mul]
      · rw [cgCoeff_of_not (by omega), mul_zero]
    have t2 : lc n₂ y * cgCoeff n₁ n₂ p (K + 1) x (y + 1) = 0 := by
      by_cases hy : n₂ ≤ y
      · rw [lc_of_le hy, zero_mul]
      · rw [cgCoeff_of_not (by omega), mul_zero]
    rw [t1, t2, add_zero]
  obtain ⟨hx, hy⟩ := hr
  have hP1 := pairIp_cgLadder_succ hp K
  simp only [cgCoeff]
  rw [hP1]
  set P := pairIp n₁ n₂ (cgLadder n₁ n₂ p K) (cgLadder n₁ n₂ p K) with hPdef
  by_cases hP0 : P = 0
  · rw [hP0]; simp
  have hPpos : 0 < P := lt_of_le_of_ne (pairIp_self_nonneg _) (Ne.symm hP0)
  by_cases hK : n₁ + n₂ - 2 * p ≤ K
  · have ha : ((K : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - K) ≤ 0 := by
      have : (n₁ : ℝ) + n₂ - 2 * p ≤ K := by
        have := (Nat.cast_le (α := ℝ)).mpr hK; push_cast [Nat.cast_sub h2p] at this; linarith
      nlinarith
    have hz : cgLadder n₁ n₂ p (K + 1) = 0 := by
      refine eq_zero_of_pairIp_self ?_
      rw [hP1]
      exact le_antisymm (mul_nonpos_of_nonpos_of_nonneg ha hPpos.le)
        (hP1 ▸ pairIp_self_nonneg _)
    have hamp : ∀ a b, cgAmp n₁ n₂ p (K + 1) a b = 0 := by
      intro a b; unfold cgAmp; split_ifs
      · rw [hz]; rfl
      · rfl
    rw [lc_of_le hK, hamp, hamp]; simp
  · push Not at hK
    have ha : 0 < ((K : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - K) := by
      have : (K : ℝ) < n₁ + n₂ - 2 * p := by
        have := (Nat.cast_lt (α := ℝ)).mpr hK; push_cast [Nat.cast_sub h2p] at this; linarith
      nlinarith
    rw [lc_eq hK.le, show (((n₁ + n₂ - 2 * p : ℕ) : ℝ)) = n₁ + n₂ - 2 * p by
      push_cast [Nat.cast_sub h2p]; ring, Real.sqrt_mul ha.le]
    have e1 := lc_mul_sqrt_spinN n₁ x (spinN n₂ y)
    have e2 := lc_mul_sqrt_spinN n₂ y (spinN n₁ x)
    rw [mul_comm (spinN n₂ (y + 1)), mul_comm (spinN n₂ y)] at e2
    have hraise := cgAmp_raise hp K hx hy
    have hs1 : √(((K : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - K)) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    have hs2 : √P ≠ 0 := (Real.sqrt_pos.mpr hPpos).ne'
    have hsq := Real.mul_self_sqrt ha.le
    set a := ((K : ℝ) + 1) * ((n₁ : ℝ) + n₂ - 2 * p - K)
    symm
    calc lc n₁ x * (cgAmp n₁ n₂ p (K + 1) (x + 1) y * √(spinN n₁ (x + 1) * spinN n₂ y) /
            (√a * √P)) +
          lc n₂ y * (cgAmp n₁ n₂ p (K + 1) x (y + 1) * √(spinN n₁ x * spinN n₂ (y + 1)) /
            (√a * √P)) =
        (((x : ℝ) + 1) * ((n₁ : ℝ) - x) * cgAmp n₁ n₂ p (K + 1) (x + 1) y +
          ((y : ℝ) + 1) * ((n₂ : ℝ) - y) * cgAmp n₁ n₂ p (K + 1) x (y + 1)) *
            √(spinN n₁ x * spinN n₂ y) / (√a * √P) := by
          rw [← mul_div_assoc, ← mul_div_assoc, ← mul_assoc, ← mul_assoc,
            mul_comm (lc n₁ x), mul_assoc _ (lc n₁ x), e1, mul_comm (lc n₂ y),
            mul_assoc _ (lc n₂ y), e2]
          ring
      _ = (√a * √a) * cgAmp n₁ n₂ p K x y * √(spinN n₁ x * spinN n₂ y) / (√a * √P) := by
          rw [hraise, hsq]
      _ = _ := by field_simp

lemma lc_eq_real (n k : ℕ) : lc n k = √(((k : ℝ) + 1) * ((n : ℝ) - k)) := by
  rcases le_or_gt k n with h | h
  · exact lc_eq h
  · rw [lc_of_le h.le, eq_comm, Real.sqrt_eq_zero']
    have : (n : ℝ) < k := by exact_mod_cast h
    nlinarith

lemma cgCoeff_raise_top {p : ℕ} (hp : p ≤ min n₁ n₂) (x y : ℕ) :
    lc n₁ x * cgCoeff n₁ n₂ p 0 (x + 1) y + lc n₂ y * cgCoeff n₁ n₂ p 0 x (y + 1) = 0 := by
  by_cases hr : x ≤ n₁ ∧ y ≤ n₂
  swap
  · have t1 : lc n₁ x * cgCoeff n₁ n₂ p 0 (x + 1) y = 0 := by
      by_cases hx : n₁ ≤ x
      · rw [lc_of_le hx, zero_mul]
      · rw [cgCoeff_of_not (by omega), mul_zero]
    have t2 : lc n₂ y * cgCoeff n₁ n₂ p 0 x (y + 1) = 0 := by
      by_cases hy : n₂ ≤ y
      · rw [lc_of_le hy, zero_mul]
      · rw [cgCoeff_of_not (by omega), mul_zero]
    rw [t1, t2, add_zero]
  obtain ⟨hx, hy⟩ := hr
  have e1 := lc_mul_sqrt_spinN n₁ x (spinN n₂ y)
  have e2 := lc_mul_sqrt_spinN n₂ y (spinN n₁ x)
  rw [mul_comm (spinN n₂ (y + 1)), mul_comm (spinN n₂ y)] at e2
  have h0 := cgAmp_raise_top hp hx hy
  simp only [cgCoeff]
  calc lc n₁ x * (cgAmp n₁ n₂ p 0 (x + 1) y * √(spinN n₁ (x + 1) * spinN n₂ y) /
          √(pairIp n₁ n₂ (cgLadder n₁ n₂ p 0) (cgLadder n₁ n₂ p 0))) +
        lc n₂ y * (cgAmp n₁ n₂ p 0 x (y + 1) * √(spinN n₁ x * spinN n₂ (y + 1)) /
          √(pairIp n₁ n₂ (cgLadder n₁ n₂ p 0) (cgLadder n₁ n₂ p 0))) =
      (((x : ℝ) + 1) * ((n₁ : ℝ) - x) * cgAmp n₁ n₂ p 0 (x + 1) y +
        ((y : ℝ) + 1) * ((n₂ : ℝ) - y) * cgAmp n₁ n₂ p 0 x (y + 1)) *
          √(spinN n₁ x * spinN n₂ y) /
            √(pairIp n₁ n₂ (cgLadder n₁ n₂ p 0) (cgLadder n₁ n₂ p 0)) := by
        rw [← mul_div_assoc, ← mul_div_assoc, ← mul_assoc, ← mul_assoc,
          mul_comm (lc n₁ x), mul_assoc _ (lc n₁ x), e1, mul_comm (lc n₂ y),
          mul_assoc _ (lc n₂ y), e2]
        ring
    _ = 0 := by rw [h0, zero_mul, zero_div]

/-- The `J₋` recursion in the form used for ladders. -/
lemma cg_lower {p : ℕ} (hp : p ≤ min n₁ n₂) (K x y : ℕ) :
    lc (n₁ + n₂ - 2 * p) K * cgCoeff n₁ n₂ p (K + 1) x y =
      (if x = 0 then 0 else lc n₁ (x - 1) * cgCoeff n₁ n₂ p K (x - 1) y) +
        (if y = 0 then 0 else lc n₂ (y - 1) * cgCoeff n₁ n₂ p K x (y - 1)) := by
  have h2p : 2 * p ≤ n₁ + n₂ := by
    have := min_le_left n₁ n₂; have := min_le_right n₁ n₂; omega
  have h := cg_recursion hp K x y
  rw [lc_eq_real, show (((n₁ + n₂ - 2 * p : ℕ) : ℝ)) = n₁ + n₂ - 2 * p by
    push_cast [Nat.cast_sub h2p]; ring, h]
  congr 1
  · split_ifs with h0
    · subst h0; simp
    · rw [lc_eq_real, show (((x - 1 : ℕ) : ℝ)) = x - 1 by
        push_cast [Nat.cast_sub (show 1 ≤ x by omega)]; ring]
      congr 2; ring
  · split_ifs with h0
    · subst h0; simp
    · rw [lc_eq_real, show (((y - 1 : ℕ) : ℝ)) = y - 1 by
        push_cast [Nat.cast_sub (show 1 ≤ y by omega)]; ring]
      congr 2; ring

lemma cgCoeff_eq_zero_of_lt {p K : ℕ} (hp : p ≤ min n₁ n₂) (hK : n₁ + n₂ - 2 * p < K)
    (x y : ℕ) : cgCoeff n₁ n₂ p K x y = 0 := by
  have hz : cgLadder n₁ n₂ p K = 0 := by
    by_contra h
    exact (isSU2_pair n₁ n₂).ladder_ne_zero_of_le h (show n₁ + n₂ - 2 * p + 1 ≤ K by omega)
      (hw_ladder_stop n₁ n₂ hp).2
  have : cgAmp n₁ n₂ p K x y = 0 := by
    unfold cgAmp; split_ifs
    · rw [hz]; rfl
    · rfl
  rw [cgCoeff, this]; simp

end Raise

/-! ### Spin systems and ladders -/

section Ladder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The standard inner product on `X → ℝ`. -/
def dotp (f g : X → ℝ) : ℝ := ∑ x, f x * g x

lemma dotp_comm (f g : X → ℝ) : dotp f g = dotp g f := by
  unfold dotp; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma dotp_smul_left (c : ℝ) (f g : X → ℝ) : dotp (c • f) g = c * dotp f g := by
  unfold dotp; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma dotp_smul_right (c : ℝ) (f g : X → ℝ) : dotp f (c • g) = c * dotp f g := by
  rw [dotp_comm, dotp_smul_left, dotp_comm]

/-- A spin system: lowering and raising operators on `X → ℝ`, each the transpose of the other. -/
structure SpinSys (X : Type*) [Fintype X] where
  /-- The lowering operator `J₋`. -/
  L : (X → ℝ) →ₗ[ℝ] X → ℝ
  /-- The raising operator `J₊`. -/
  R : (X → ℝ) →ₗ[ℝ] X → ℝ
  adj : ∀ f g, dotp (L f) g = dotp f (R g)

lemma SpinSys.adj' (S : SpinSys X) (f g : X → ℝ) : dotp (S.R f) g = dotp f (S.L g) := by
  rw [dotp_comm, ← S.adj, dotp_comm]

/-- A ladder of spin `j = n/2` in a spin system: `f k = |j, j - k⟩`. -/
structure IsLadder (S : SpinSys X) (n : ℕ) (f : ℕ → X → ℝ) : Prop where
  lower : ∀ k, S.L (f k) = lc n k • f (k + 1)
  raise : ∀ k, S.R (f (k + 1)) = lc n k • f k
  top : S.R (f 0) = 0
  vanish : ∀ k, n < k → f k = 0

variable {S : SpinSys X} {n n' : ℕ} {f g : ℕ → X → ℝ}

lemma IsLadder.RL (hf : IsLadder S n f) (k : ℕ) :
    S.R (S.L (f k)) = (((k + 1) * (n - k) : ℕ) : ℝ) • f k := by
  rw [hf.lower, map_smul, hf.raise, smul_smul, lc_mul_self]

lemma IsLadder.LR (hf : IsLadder S n f) (k : ℕ) :
    S.L (S.R (f k)) = ((k * (n + 1 - k) : ℕ) : ℝ) • f k := by
  cases k with
  | zero => rw [hf.top, map_zero]; simp
  | succ k =>
    rw [hf.raise, map_smul, hf.lower, smul_smul, lc_mul_self,
      show n + 1 - (k + 1) = n - k by omega]

/-- **Orthogonality of ladders**: `⟨j, m | j', m'⟩ = 0` unless `j = j'` and `m = m'`. -/
theorem IsLadder.dotp_eq_zero (hf : IsLadder S n f) (hg : IsLadder S n' g) {k k' : ℕ}
    (hk : k ≤ n) (hk' : k' ≤ n') (hne : ¬(n = n' ∧ k = k')) : dotp (f k) (g k') = 0 := by
  have e1 : (((k + 1) * (n - k) : ℕ) : ℝ) * dotp (f k) (g k') =
      (((k' + 1) * (n' - k') : ℕ) : ℝ) * dotp (f k) (g k') := by
    rw [← dotp_smul_left, ← hf.RL, S.adj', S.adj, hg.RL, dotp_smul_right]
  have e2 : ((k * (n + 1 - k) : ℕ) : ℝ) * dotp (f k) (g k') =
      ((k' * (n' + 1 - k') : ℕ) : ℝ) * dotp (f k) (g k') := by
    rw [← dotp_smul_left, ← hf.LR, S.adj, S.adj', hg.LR, dotp_smul_right]
  by_contra hd
  have b1 : (k + 1) * (n - k) = (k' + 1) * (n' - k') := by exact_mod_cast mul_right_cancel₀ hd e1
  have b2 : k * (n + 1 - k) = k' * (n' + 1 - k') := by exact_mod_cast mul_right_cancel₀ hd e2
  apply hne
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', n' = k' + d' := ⟨n' - k', by omega⟩
  rw [show k + d - k = d by omega, show k' + d' - k' = d' by omega] at b1
  rw [show k + d + 1 - k = d + 1 by omega, show k' + d' + 1 - k' = d' + 1 by omega] at b2
  have z1 : ((k : ℤ) + 1) * d = ((k' : ℤ) + 1) * d' := by exact_mod_cast b1
  have z2 : (k : ℤ) * (d + 1) = (k' : ℤ) * (d' + 1) := by exact_mod_cast b2
  have z3 : ((k : ℤ) - k') * (d + k' + 1) = 0 := by
    linear_combination (-(k' : ℤ)) * z1 + ((k' : ℤ) + 1) * z2
  have hkk : (k : ℤ) = k' := by
    rcases mul_eq_zero.mp z3 with h | h
    · linarith
    · have : (0 : ℤ) ≤ d := by positivity
      have : (0 : ℤ) ≤ k' := by positivity
      linarith
  have hkk' : k = k' := by exact_mod_cast hkk
  subst hkk'
  constructor
  · have : (d : ℤ) = d' := by linarith
    omega
  · rfl

/-- **The overlap of two ladders of the same spin does not depend on `M`.** -/
theorem IsLadder.dotp_succ (hf : IsLadder S n f) (hg : IsLadder S n g) {k : ℕ} (hk : k < n) :
    dotp (f (k + 1)) (g (k + 1)) = dotp (f k) (g k) := by
  have e := S.adj (f k) (S.L (g k))
  rw [hg.RL, dotp_smul_right, hf.lower, hg.lower, dotp_smul_left, dotp_smul_right,
    ← mul_assoc, lc_mul_self] at e
  have hc : (((k + 1) * (n - k) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < (k + 1) * (n - k) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this.ne'
  exact mul_left_cancel₀ hc e

theorem IsLadder.dotp_const (hf : IsLadder S n f) (hg : IsLadder S n g) {k : ℕ} (hk : k ≤ n) :
    dotp (f k) (g k) = dotp (f 0) (g 0) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hf.dotp_succ hg (by omega), ih (by omega)]

/-! ### A single spin -/

/-- `J₋` on a single spin in the orthonormal basis `x = j - m`. -/
noncomputable def oneL (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ where
  toFun f x := if h : x = 0 then 0 else lc n (x - 1) * f ⟨x - 1, by omega⟩
  map_add' f g := by funext x; by_cases h : x = 0 <;> simp [h, mul_add]
  map_smul' c f := by funext x; by_cases h : x = 0 <;> simp [h]; ring

/-- `J₊` on a single spin in the orthonormal basis `x = j - m`. -/
noncomputable def oneR (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ where
  toFun f x := if h : (x : ℕ) < n then lc n x * f ⟨x + 1, by omega⟩ else 0
  map_add' f g := by funext x; by_cases h : (x : ℕ) < n <;> simp [h, mul_add]
  map_smul' c f := by funext x; by_cases h : (x : ℕ) < n <;> simp [h]; ring

/-- A single spin `j = n/2`. -/
noncomputable def oneSys (n : ℕ) : SpinSys (Fin (n + 1)) where
  L := oneL n
  R := oneR n
  adj f g := by
    unfold dotp
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have h1 : oneL n f 0 = 0 := by simp [oneL]
    have h2 : oneR n g (Fin.last n) = 0 := by simp [oneR]
    rw [h1, h2, zero_mul, mul_zero, zero_add, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [oneL, oneR, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_succ, Fin.val_castSucc,
      Fin.succ_ne_zero, j.2, dite_false, dite_true]
    have e1 : (⟨(j : ℕ) + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc j := Fin.ext (by simp)
    have e2 : (⟨(j : ℕ) + 1, by omega⟩ : Fin (n + 1)) = j.succ := Fin.ext (by simp)
    rw [e1, e2, show (j : ℕ) + 1 - 1 = j by omega]
    ring

/-- The basis state `|j, j - k⟩` of a single spin. -/
def oneVec (n k : ℕ) : Fin (n + 1) → ℝ := fun x => if (x : ℕ) = k then 1 else 0

theorem isLadder_one (n : ℕ) : IsLadder (oneSys n) n (oneVec n) where
  lower k := by
    funext x
    simp only [oneSys, oneL, oneVec, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
    by_cases h0 : x = 0
    · subst h0; simp
    · rw [dite_eq_right h0]
      have hx0 : (x : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      by_cases hk : (x : ℕ) = k + 1
      · simp [hk]
      · have : (x : ℕ) - 1 ≠ k := by omega
        simp [this, hk]
  raise k := by
    funext x
    simp only [oneSys, oneR, oneVec, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
    by_cases hx : (x : ℕ) = k
    · by_cases h : (x : ℕ) < n
      · rw [dite_eq_left h]; simp [hx]
      · rw [dite_eq_right h, lc_of_le (by omega)]; simp
    · by_cases h : (x : ℕ) < n
      · rw [dite_eq_left h]; simp [hx]
      · rw [dite_eq_right h]; simp [hx]
  top := by
    funext x
    simp only [oneSys, oneR, oneVec, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> simp_all
  vanish k hk := by
    funext x
    simp only [oneVec]
    rw [ite_eq_right (by have := x.2; omega)]
    rfl

/-! ### Products -/

/-- `J₋ = J₋ ⊗ 1 + 1 ⊗ J₋` on a product. -/
def prodOp (A : (X → ℝ) →ₗ[ℝ] X → ℝ) (B : (Y → ℝ) →ₗ[ℝ] Y → ℝ) :
    (X × Y → ℝ) →ₗ[ℝ] X × Y → ℝ where
  toFun f q := A (fun x => f (x, q.2)) q.1 + B (fun y => f (q.1, y)) q.2
  map_add' f g := by
    funext q
    simp only [Pi.add_apply]
    rw [show (fun x => f (x, q.2) + g (x, q.2)) = (fun x => f (x, q.2)) + (fun x => g (x, q.2))
      from rfl, show (fun y => f (q.1, y) + g (q.1, y)) = (fun y => f (q.1, y)) +
        (fun y => g (q.1, y)) from rfl, map_add, map_add]
    simp only [Pi.add_apply]; ring
  map_smul' c f := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (fun x => c * f (x, q.2)) = c • (fun x => f (x, q.2)) from rfl,
      show (fun y => c * f (q.1, y)) = c • (fun y => f (q.1, y)) from rfl, map_smul, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- The product of two spin systems. -/
def prodSys (S : SpinSys X) (T : SpinSys Y) : SpinSys (X × Y) where
  L := prodOp S.L T.L
  R := prodOp S.R T.R
  adj f g := by
    unfold dotp
    simp only [prodOp, LinearMap.coe_mk, AddHom.coe_mk, add_mul, mul_add,
      Finset.sum_add_distrib]
    congr 1
    · rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun y _ => S.adj (fun x => f (x, y)) (fun x => g (x, y))
    · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun x _ => T.adj (fun y => f (x, y)) (fun y => g (x, y))

end Ladder

/-! ### Coupling two ladders -/

section Couple

variable {X Y : Type*} [Fintype X] [Fintype Y] {S : SpinSys X} {T : SpinSys Y}

/-- The coupled ladder `|J, M⟩ = Σ ⟨j₁ m₁; j₂ m₂ | J M⟩ |j₁ m₁⟩ ⊗ |j₂ m₂⟩` with
`J = j₁ + j₂ - p` and `M = J - K`. -/
noncomputable def couple (n m p : ℕ) (f : ℕ → X → ℝ) (g : ℕ → Y → ℝ) : ℕ → X × Y → ℝ :=
  fun K q => ∑ t ∈ Finset.range (n + 1), ∑ s ∈ Finset.range (m + 1),
    cgCoeff n m p K t s * (f t q.1 * g s q.2)

lemma sum_range_shift (n : ℕ) (a F : ℕ → ℝ) (ha : a n = 0) :
    ∑ t ∈ Finset.range (n + 1), a t * F (t + 1) =
      ∑ t ∈ Finset.range (n + 1), (if t = 0 then 0 else a (t - 1) * F t) := by
  rw [Finset.sum_range_succ, ha, zero_mul, add_zero, Finset.sum_range_succ']
  simp

lemma apply_sum_sum {Z : Type*} (A : (Z → ℝ) →ₗ[ℝ] Z → ℝ) (N M : ℕ)
    (a : ℕ → ℕ → ℝ) (h : ℕ → ℕ → Z → ℝ) (z : Z) :
    A (fun z' => ∑ t ∈ Finset.range N, ∑ s ∈ Finset.range M, a t s * h t s z') z =
      ∑ t ∈ Finset.range N, ∑ s ∈ Finset.range M, a t s * A (h t s) z := by
  have e : (fun z' => ∑ t ∈ Finset.range N, ∑ s ∈ Finset.range M, a t s * h t s z') =
      ∑ t ∈ Finset.range N, ∑ s ∈ Finset.range M, a t s • h t s := by
    funext z'; simp [Finset.sum_apply]
  rw [e, map_sum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma IsLadder.R_eq (hf : IsLadder S n f) (t : ℕ) :
    S.R (f t) = if t = 0 then 0 else lc n (t - 1) • f (t - 1) := by
  cases t with
  | zero => simp [hf.top]
  | succ t => simp [hf.raise]

variable {n m : ℕ} {f : ℕ → X → ℝ} {g : ℕ → Y → ℝ}

omit [Fintype X] [Fintype Y] in
lemma couple_fst (n m p K : ℕ) (f : ℕ → X → ℝ) (g : ℕ → Y → ℝ) (y : Y) :
    (fun x' => couple n m p f g K (x', y)) = fun x' => ∑ t ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.range (m + 1), (cgCoeff n m p K t s * g s y) * f t x' := by
  funext x'; simp only [couple]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype X] [Fintype Y] in
lemma couple_snd (n m p K : ℕ) (f : ℕ → X → ℝ) (g : ℕ → Y → ℝ) (x : X) :
    (fun y' => couple n m p f g K (x, y')) = fun y' => ∑ t ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.range (m + 1), (cgCoeff n m p K t s * f t x) * g s y' := by
  funext y'; simp only [couple]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Coupling two ladders gives a ladder** of spin `J = j₁ + j₂ - p`. -/
theorem IsLadder.couple (hf : IsLadder S n f) (hg : IsLadder T m g) {p : ℕ}
    (hp : p ≤ min n m) : IsLadder (prodSys S T) (n + m - 2 * p) (couple n m p f g) where
  lower K := by
    funext ⟨x, y⟩
    change S.L (fun x' => QM.couple n m p f g K (x', y)) x +
      T.L (fun y' => QM.couple n m p f g K (x, y')) y =
        lc (n + m - 2 * p) K * QM.couple n m p f g (K + 1) (x, y)
    rw [couple_fst, couple_snd, apply_sum_sum, apply_sum_sum]
    simp only [hf.lower, hg.lower, Pi.smul_apply, smul_eq_mul, QM.couple, Finset.mul_sum]
    have key : ∀ t s, lc (n + m - 2 * p) K * (cgCoeff n m p (K + 1) t s * (f t x * g s y)) =
        (if t = 0 then 0 else lc n (t - 1) * cgCoeff n m p K (t - 1) s) * (f t x * g s y) +
        (if s = 0 then 0 else lc m (s - 1) * cgCoeff n m p K t (s - 1)) * (f t x * g s y) := by
      intro t s; rw [← mul_assoc, cg_lower hp, add_mul]
    simp only [key, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (n + 1))]
      refine Finset.sum_congr rfl fun s _ => ?_
      have := sum_range_shift n (fun t => lc n t * cgCoeff n m p K t s * g s y) (fun t => f t x)
        (by simp [lc_of_le le_rfl])
      rw [show ∑ t ∈ Finset.range (n + 1), cgCoeff n m p K t s * g s y * (lc n t * f (t + 1) x) =
        ∑ t ∈ Finset.range (n + 1), lc n t * cgCoeff n m p K t s * g s y * f (t + 1) x from
          Finset.sum_congr rfl fun _ _ => by ring, this]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> ring
    · refine Finset.sum_congr rfl fun t _ => ?_
      have := sum_range_shift m (fun s => lc m s * cgCoeff n m p K t s * f t x) (fun s => g s y)
        (by simp [lc_of_le le_rfl])
      rw [show ∑ s ∈ Finset.range (m + 1), cgCoeff n m p K t s * f t x * (lc m s * g (s + 1) y) =
        ∑ s ∈ Finset.range (m + 1), lc m s * cgCoeff n m p K t s * f t x * g (s + 1) y from
          Finset.sum_congr rfl fun _ _ => by ring, this]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> ring
  raise K := by
    funext ⟨x, y⟩
    change S.R (fun x' => QM.couple n m p f g (K + 1) (x', y)) x +
      T.R (fun y' => QM.couple n m p f g (K + 1) (x, y')) y =
        lc (n + m - 2 * p) K * QM.couple n m p f g K (x, y)
    rw [couple_fst, couple_snd, apply_sum_sum, apply_sum_sum]
    simp only [hf.R_eq, hg.R_eq, QM.couple, Finset.mul_sum]
    have key : ∀ t s, lc (n + m - 2 * p) K * (cgCoeff n m p K t s * (f t x * g s y)) =
        lc n t * cgCoeff n m p (K + 1) (t + 1) s * (f t x * g s y) +
        lc m s * cgCoeff n m p (K + 1) t (s + 1) * (f t x * g s y) := by
      intro t s; rw [← mul_assoc, cg_raise hp, add_mul]
    simp only [key, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (n + 1))]
      refine Finset.sum_congr rfl fun s _ => ?_
      have := sum_range_shift n (fun t => lc n t * f t x * g s y)
        (fun t => cgCoeff n m p (K + 1) t s) (by simp [lc_of_le le_rfl])
      rw [show ∑ t ∈ Finset.range (n + 1), lc n t * cgCoeff n m p (K + 1) (t + 1) s *
          (f t x * g s y) = ∑ t ∈ Finset.range (n + 1), lc n t * f t x * g s y *
            cgCoeff n m p (K + 1) (t + 1) s from Finset.sum_congr rfl fun _ _ => by ring, this]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp; ring
    · refine Finset.sum_congr rfl fun t _ => ?_
      have := sum_range_shift m (fun s => lc m s * f t x * g s y)
        (fun s => cgCoeff n m p (K + 1) t s) (by simp [lc_of_le le_rfl])
      rw [show ∑ s ∈ Finset.range (m + 1), lc m s * cgCoeff n m p (K + 1) t (s + 1) *
          (f t x * g s y) = ∑ s ∈ Finset.range (m + 1), lc m s * f t x * g s y *
            cgCoeff n m p (K + 1) t (s + 1) from Finset.sum_congr rfl fun _ _ => by ring, this]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> simp; ring
  top := by
    funext ⟨x, y⟩
    change S.R (fun x' => QM.couple n m p f g 0 (x', y)) x +
      T.R (fun y' => QM.couple n m p f g 0 (x, y')) y = 0
    rw [couple_fst, couple_snd, apply_sum_sum, apply_sum_sum]
    simp only [hf.R_eq, hg.R_eq]
    have h1 : ∀ s, ∑ t ∈ Finset.range (n + 1), cgCoeff n m p 0 t s * g s y *
        (if t = 0 then 0 else lc n (t - 1) • f (t - 1)) x =
        ∑ t ∈ Finset.range (n + 1), lc n t * cgCoeff n m p 0 (t + 1) s * (f t x * g s y) := by
      intro s
      have := sum_range_shift n (fun t => lc n t * f t x * g s y)
        (fun t => cgCoeff n m p 0 t s) (by simp [lc_of_le le_rfl])
      rw [show ∑ t ∈ Finset.range (n + 1), lc n t * cgCoeff n m p 0 (t + 1) s * (f t x * g s y) =
        ∑ t ∈ Finset.range (n + 1), lc n t * f t x * g s y * cgCoeff n m p 0 (t + 1) s from
          Finset.sum_congr rfl fun _ _ => by ring, this]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp; ring
    have h2 : ∀ t, ∑ s ∈ Finset.range (m + 1), cgCoeff n m p 0 t s * f t x *
        (if s = 0 then 0 else lc m (s - 1) • g (s - 1)) y =
        ∑ s ∈ Finset.range (m + 1), lc m s * cgCoeff n m p 0 t (s + 1) * (f t x * g s y) := by
      intro t
      have := sum_range_shift m (fun s => lc m s * f t x * g s y)
        (fun s => cgCoeff n m p 0 t s) (by simp [lc_of_le le_rfl])
      rw [show ∑ s ∈ Finset.range (m + 1), lc m s * cgCoeff n m p 0 t (s + 1) * (f t x * g s y) =
        ∑ s ∈ Finset.range (m + 1), lc m s * f t x * g s y * cgCoeff n m p 0 t (s + 1) from
          Finset.sum_congr rfl fun _ _ => by ring, this]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> simp; ring
    rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_congr rfl fun t _ => h2 t,
      Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← add_mul, cgCoeff_raise_top hp, zero_mul]
  vanish K hK := by
    funext ⟨x, y⟩
    simp only [QM.couple, cgCoeff_eq_zero_of_lt hp hK, zero_mul, Finset.sum_const_zero]
    rfl

end Couple

/-! ### Associativity and expansions -/

section Assoc

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype X] [Fintype Y] [Fintype Z] in
lemma prodOp_assoc (A : (X → ℝ) →ₗ[ℝ] X → ℝ) (B : (Y → ℝ) →ₗ[ℝ] Y → ℝ)
    (C : (Z → ℝ) →ₗ[ℝ] Z → ℝ) (F : X × (Y × Z) → ℝ) :
    prodOp (prodOp A B) C (fun q => F (q.1.1, (q.1.2, q.2))) =
      fun q => prodOp A (prodOp B C) F (q.1.1, (q.1.2, q.2)) := by
  funext ⟨⟨x, y⟩, z⟩
  simp only [prodOp, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- A ladder of `S₁ ⊗ (S₂ ⊗ S₃)` is a ladder of `(S₁ ⊗ S₂) ⊗ S₃`. -/
theorem IsLadder.assoc {S₁ : SpinSys X} {S₂ : SpinSys Y} {S₃ : SpinSys Z} {n : ℕ}
    {f : ℕ → X × (Y × Z) → ℝ} (hf : IsLadder (prodSys S₁ (prodSys S₂ S₃)) n f) :
    IsLadder (prodSys (prodSys S₁ S₂) S₃) n (fun k q => f k (q.1.1, (q.1.2, q.2))) where
  lower k := by
    change prodOp (prodOp S₁.L S₂.L) S₃.L _ = _
    rw [prodOp_assoc]
    funext q
    exact congrFun (hf.lower k) (q.1.1, (q.1.2, q.2))
  raise k := by
    change prodOp (prodOp S₁.R S₂.R) S₃.R _ = _
    rw [prodOp_assoc]
    funext q
    exact congrFun (hf.raise k) (q.1.1, (q.1.2, q.2))
  top := by
    change prodOp (prodOp S₁.R S₂.R) S₃.R _ = _
    rw [prodOp_assoc]
    funext q
    exact congrFun hf.top (q.1.1, (q.1.2, q.2))
  vanish k hk := by
    funext q
    exact congrFun (hf.vanish k hk) (q.1.1, (q.1.2, q.2))

/-- Orthonormality of the first `n + 1` vectors of a sequence. -/
def OrthoUpTo (n : ℕ) (f : ℕ → X → ℝ) : Prop :=
  ∀ t ≤ n, ∀ t' ≤ n, dotp (f t) (f t') = if t = t' then 1 else 0

lemma dotp_sum_left {ι : Type*} (I : Finset ι) (v : ι → X → ℝ) (g : X → ℝ) :
    dotp (∑ i ∈ I, v i) g = ∑ i ∈ I, dotp (v i) g := by
  unfold dotp
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma dotp_sum_right {ι : Type*} (I : Finset ι) (f : X → ℝ) (v : ι → X → ℝ) :
    dotp f (∑ i ∈ I, v i) = ∑ i ∈ I, dotp f (v i) := by
  rw [dotp_comm, dotp_sum_left]
  exact Finset.sum_congr rfl fun _ _ => dotp_comm _ _

lemma dotp_sum_smul {ι : Type*} [DecidableEq ι] (I : Finset ι) (v : ι → X → ℝ)
    (hv : ∀ i ∈ I, ∀ j ∈ I, dotp (v i) (v j) = if i = j then 1 else 0) (α β : ι → ℝ) :
    dotp (∑ i ∈ I, α i • v i) (∑ j ∈ I, β j • v j) = ∑ i ∈ I, α i * β i := by
  rw [dotp_sum_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dotp_smul_left, dotp_sum_right,
    Finset.sum_congr rfl fun j hj => by rw [dotp_smul_right, hv i hi j hj]]
  simp [hi]

lemma dotp_prod (a a' : X → ℝ) (b b' : Y → ℝ) :
    dotp (fun q : X × Y => a q.1 * b q.2) (fun q => a' q.1 * b' q.2) =
      dotp a a' * dotp b b' := by
  unfold dotp
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The product vectors `f t ⊗ g s ⊗ h r`. -/
def tensor3 (f : ℕ → X → ℝ) (g : ℕ → Y → ℝ) (h : ℕ → Z → ℝ) (i : ℕ × ℕ × ℕ) :
    (X × Y) × Z → ℝ :=
  fun q => f i.1 q.1.1 * g i.2.1 q.1.2 * h i.2.2 q.2

lemma dotp_tensor3 (f : ℕ → X → ℝ) (g : ℕ → Y → ℝ) (h : ℕ → Z → ℝ) (i j : ℕ × ℕ × ℕ) :
    dotp (tensor3 f g h i) (tensor3 f g h j) =
      dotp (f i.1) (f j.1) * dotp (g i.2.1) (g j.2.1) * dotp (h i.2.2) (h j.2.2) := by
  have e : ∀ k : ℕ × ℕ × ℕ, tensor3 f g h k =
      fun q => (fun p : X × Y => f k.1 p.1 * g k.2.1 p.2) q.1 * h k.2.2 q.2 := fun _ => rfl
  rw [e, e, dotp_prod (fun p : X × Y => f i.1 p.1 * g i.2.1 p.2)
    (fun p => f j.1 p.1 * g j.2.1 p.2), dotp_prod (f i.1) (f j.1) (g i.2.1) (g j.2.1)]

end Assoc

end QM
