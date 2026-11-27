/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.ManyBody.HartreeFock

/-!
# No unfilled shells in Hartree–Fock theory

Bach, Lieb, Loss and Solovej (PRL 72, 2981 (1994)): for a repulsive interaction (`V ⪰ 0` on the
pair space) a Hartree–Fock minimizer has no unfilled shells. With the Fock matrix `F(P)` of a
minimizing rank-`N` projection `P`, every occupied orbital has an energy `⟨x, F x⟩` no higher than
every unoccupied one, and `P` solves the Hartree–Fock equations `[F(P), Pᵀ] = 0`.

Conventions are those of `QM.ManyBody.HartreeFock`: `γ_ij = ⟨c_i† c_j⟩`, so the occupied orbitals
are the vectors `x` with `Pᵀ x = x` (equivalently `x ᵥ* P = x`).

The proof: by Lieb's variational principle (`lieb_variational`), a minimizer over projections
also minimizes over all `0 ≤ γ ≤ 1` with `tr γ = N`. The segment from `P` to any other rank-`N`
projection `Q` is admissible, and `E_HF` is quadratic along it, so its linear coefficient
`Re Σ F(P)_ab (Q - P)_ab` is nonnegative (`hf_first_order`). Exchanging an occupied `x` for an
unoccupied `y` gives the aufbau inequality; rotating `x` towards `y` by the projections onto
`x + s e y` (`s ∈ ℝ`, `|e| = 1`) shows that the off-diagonal block `⟨y, F x⟩` vanishes.

## Main definitions

* `fockMat h V γ`: the Fock matrix
  `F(γ)_ab = h_ab + ½ Σ_ik (V_{ia,kb} + V_{ai,bk} - V_{ia,bk} - V_{ai,kb}) γ_ik`.
* `rankOne u`: the rank-one projection onto `u`, `ū_i u_j / (ū ⬝ u)`.

## Main results

* `hfEnergy_add_smul_fock`: the linear coefficient of `E_HF(A + tΔ)` is `Re Σ F(A)_ab Δ_ab`.
* `fockMat_isHermitian`.
* `hf_first_order`: `Re Σ F(P)_ab (Q - P)_ab ≥ 0` at a minimizer.
* `hf_aufbau` (**no unfilled shells**): `Re ⟨x, F x⟩ ≤ Re ⟨y, F y⟩` for occupied `x` and
  unoccupied `y`.
* `hf_offDiag`, `hf_equation` (**the Hartree–Fock equations**): `F(P) Pᵀ = Pᵀ F(P)`.
-/

namespace QM.ManyBody
open Matrix Finset
open scoped ComplexOrder
variable {M : ℕ} (h : Matrix (Fin M) (Fin M) ℂ) (V : Matrix (Fin M × Fin M) (Fin M × Fin M) ℂ)

/-- **The Fock matrix**
`F(γ)_ab = h_ab + ½ Σ_ik (V_{ia,kb} + V_{ai,bk} - V_{ia,bk} - V_{ai,kb}) γ_ik`. -/
noncomputable def fockMat (γ : Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun a b => h a b + 2⁻¹ * ∑ i, ∑ k,
    (V (i, a) (k, b) + V (a, i) (b, k) - V (i, a) (b, k) - V (a, i) (k, b)) * γ i k

lemma sum_comm₄ (f : Fin M → Fin M → Fin M → Fin M → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
  calc _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := sum_comm
    _ = _ := sum_congr rfl fun c _ => sum_congr rfl fun a _ => sum_comm

/-- The linear term of `E_HF` around `A` is `Σ F(A)_ab Δ_ab`. -/
lemma linear_eq_fockMat (A Δ : Matrix (Fin M) (Fin M) ℂ) :
    ∑ i, ∑ j, h i j * Δ i j + pairForm V A Δ + pairForm V Δ A =
      ∑ a, ∑ b, fockMat h V A a b * Δ a b := by
  have e1 : pairForm V A Δ = 2⁻¹ * ∑ a, ∑ b, ∑ i, ∑ k,
      (V (i, a) (k, b) - V (i, a) (b, k)) * A i k * Δ a b := by
    rw [pairForm]
    conv_rhs => rw [sum_comm₄]
    refine congrArg _ (sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_)
    simp only [mul_sub, sub_mul, sum_sub_distrib]
    congr 1
    · exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
    · rw [sum_comm]; exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  have e2 : pairForm V Δ A = 2⁻¹ * ∑ a, ∑ b, ∑ i, ∑ k,
      (V (a, i) (b, k) - V (a, i) (k, b)) * A i k * Δ a b := by
    rw [pairForm]
    refine congrArg _ (sum_congr rfl fun a _ => ?_)
    simp only [mul_sub, sub_mul, sum_sub_distrib]
    congr 1
    · rw [sum_comm]
      exact sum_congr rfl fun b _ => sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
    · calc _ = ∑ j, ∑ l, ∑ k, V (a, j) (k, l) * (Δ a l * A j k) :=
            sum_congr rfl fun j _ => sum_comm
        _ = ∑ l, ∑ j, ∑ k, V (a, j) (k, l) * (Δ a l * A j k) := sum_comm
        _ = _ := sum_congr rfl fun b _ => sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
  rw [e1, e2, add_assoc, ← mul_add, ← sum_add_distrib, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  simp only [fockMat, Matrix.of_apply]
  rw [add_mul, mul_assoc, sum_mul]
  rw [← sum_add_distrib]
  congr 2
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib, sum_mul]
  exact sum_congr rfl fun k _ => by ring

/-- `hfEnergy_add_smul` with the linear coefficient written through the Fock matrix. -/
lemma hfEnergy_add_smul_fock (A Δ : Matrix (Fin M) (Fin M) ℂ) (t : ℝ) :
    hfEnergy h V (A + (t : ℂ) • Δ) = hfEnergy h V A +
      (∑ a, ∑ b, fockMat h V A a b * Δ a b).re * t + (pairForm V Δ Δ).re * t ^ 2 := by
  rw [hfEnergy_add_smul, linear_eq_fockMat]

lemma fockMat_isHermitian (hh : h.IsHermitian) (hV : V.IsHermitian) {γ : Matrix (Fin M) (Fin M) ℂ}
    (hγ : γ.IsHermitian) : (fockMat h V γ).IsHermitian := by
  ext a b
  have h2 : star (2⁻¹ : ℂ) = 2⁻¹ := by simp
  simp only [conjTranspose_apply, fockMat, Matrix.of_apply, star_add, star_mul', star_sum,
    star_sub, hh.apply, hV.apply, hγ.apply, h2]
  rw [sum_comm]
  exact congrArg _ (congrArg _ (sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring))

variable {h V}

/-! ### Elementary inequalities -/

lemma nonneg_of_forall_lin_quad {l c : ℝ}
    (H : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ l * t + c * t ^ 2) : 0 ≤ l := by
  by_contra hl
  push Not at hl
  have hd : 0 < 2 * (|c| + 1) := by positivity
  set t := min 1 (-l / (2 * (|c| + 1))) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (neg_pos.mpr hl) hd)
  have ht1 : t ≤ 1 := min_le_left _ _
  have h3 : t * (2 * (|c| + 1)) ≤ -l := (le_div_iff₀ hd).mp (min_le_right _ _)
  have h4 : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0.le
  have h5 := H t ht0 ht1
  nlinarith [mul_le_mul_of_nonneg_left h4 ht0.le, mul_pos ht0 ht0]

lemma eq_zero_of_forall_lin_quad {m d : ℝ} (H : ∀ s : ℝ, 0 ≤ m * s + d * s ^ 2) : m = 0 := by
  have h1 := nonneg_of_forall_lin_quad (l := m) (c := d) fun t _ _ => H t
  have h2 := nonneg_of_forall_lin_quad (l := -m) (c := d) fun t _ _ => by
    have := H (-t); ring_nf at this ⊢; linarith
  linarith

/-! ### Rank-one projections -/

/-- The rank-one projection onto `u`, in the convention of one-body matrices:
`(rankOne u)_ij = ū_i u_j / (ū ⬝ u)`. -/
noncomputable def rankOne (u : Fin M → ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  (star u ⬝ᵥ u)⁻¹ • vecMulVec (star u) u

lemma star_dotProduct_self (u : Fin M → ℂ) : star (star u ⬝ᵥ u) = star u ⬝ᵥ u :=
  (star_dotProduct u u).symm

lemma dotProduct_self_ofReal_re (u : Fin M → ℂ) : (((star u ⬝ᵥ u).re : ℝ) : ℂ) = star u ⬝ᵥ u :=
  Complex.conj_eq_iff_re.mp (star_dotProduct_self u)

lemma dotProduct_self_ne_zero {u : Fin M → ℂ} (hu : u ≠ 0) : star u ⬝ᵥ u ≠ 0 :=
  fun h => hu (dotProduct_star_self_eq_zero.mp h)

lemma dotProduct_self_re_nonneg (u : Fin M → ℂ) : 0 ≤ (star u ⬝ᵥ u).re :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg u)).1

lemma dotProduct_self_re_pos {u : Fin M → ℂ} (hu : u ≠ 0) : 0 < (star u ⬝ᵥ u).re := by
  refine (dotProduct_self_re_nonneg u).lt_of_ne fun h => dotProduct_self_ne_zero hu ?_
  rw [← dotProduct_self_ofReal_re, ← h, Complex.ofReal_zero]

lemma rankOne_conjTranspose (u : Fin M → ℂ) : (rankOne u)ᴴ = rankOne u := by
  rw [rankOne, conjTranspose_smul, conjTranspose_vecMulVec, star_star, star_inv₀,
    star_dotProduct_self]

lemma rankOne_mul_self {u : Fin M → ℂ} (hu : u ≠ 0) : rankOne u * rankOne u = rankOne u := by
  have hn := dotProduct_self_ne_zero hu
  rw [rankOne, smul_mul_smul_comm, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul,
    dotProduct_comm u (star u)]
  congr 1
  field_simp

lemma trace_rankOne {u : Fin M → ℂ} (hu : u ≠ 0) : (rankOne u).trace = 1 := by
  rw [rankOne, trace_smul, trace_vecMulVec, smul_eq_mul,
    inv_mul_cancel₀ (dotProduct_self_ne_zero hu)]

lemma mulVec_star_eq {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) {x c : Fin M → ℂ}
    (hx : x ᵥ* P = c) : P *ᵥ star x = star c := by
  rw [← hx, star_vecMul, hPh]

lemma mul_rankOne {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) {u c : Fin M → ℂ}
    (hu : u ᵥ* P = c) : P * rankOne u = (star u ⬝ᵥ u)⁻¹ • vecMulVec (star c) u := by
  rw [rankOne, Matrix.mul_smul, mul_vecMulVec, mulVec_star_eq hPh hu]

lemma rankOne_mul {P : Matrix (Fin M) (Fin M) ℂ} {u c : Fin M → ℂ} (hu : u ᵥ* P = c) :
    rankOne u * P = (star u ⬝ᵥ u)⁻¹ • vecMulVec (star u) c := by
  rw [rankOne, Matrix.smul_mul, vecMulVec_mul, hu]

lemma vecMul_rankOne (w u : Fin M → ℂ) :
    w ᵥ* rankOne u = ((star u ⬝ᵥ u)⁻¹ * (w ⬝ᵥ star u)) • u := by
  rw [rankOne, vecMul_smul, vecMul_vecMulVec, smul_smul]

lemma sum_mul_vecMulVec (G : Matrix (Fin M) (Fin M) ℂ) (u v : Fin M → ℂ) :
    ∑ a, ∑ b, G a b * vecMulVec (star u) v a b = star u ⬝ᵥ (G *ᵥ v) := by
  simp only [vecMulVec_apply, dotProduct, mulVec, mul_sum, Pi.star_apply]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

lemma sum_mul_rankOne (G : Matrix (Fin M) (Fin M) ℂ) (u : Fin M → ℂ) :
    ∑ a, ∑ b, G a b * rankOne u a b = (star u ⬝ᵥ u)⁻¹ * (star u ⬝ᵥ (G *ᵥ u)) := by
  rw [← sum_mul_vecMulVec, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  simp only [rankOne, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Removing an occupied direction from a projection leaves a projection. -/
lemma proj_sub_rankOne {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) (hPP : P * P = P)
    {x : Fin M → ℂ} (hx0 : x ≠ 0) (hx : x ᵥ* P = x) :
    (P - rankOne x)ᴴ = P - rankOne x ∧ (P - rankOne x) * (P - rankOne x) = P - rankOne x := by
  refine ⟨by rw [conjTranspose_sub, hPh, rankOne_conjTranspose], ?_⟩
  have h1 : P * rankOne x = rankOne x := by rw [mul_rankOne hPh hx]; rfl
  have h2 : rankOne x * P = rankOne x := by rw [rankOne_mul hx]; rfl
  rw [sub_mul, mul_sub, mul_sub, hPP, h1, h2, rankOne_mul_self hx0]
  abel

/-- Adding a direction orthogonal to the range of a projection gives a projection. -/
lemma proj_add_rankOne {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) (hPP : P * P = P)
    {u : Fin M → ℂ} (hu0 : u ≠ 0) (hu : u ᵥ* P = 0) :
    (P + rankOne u)ᴴ = P + rankOne u ∧ (P + rankOne u) * (P + rankOne u) = P + rankOne u := by
  refine ⟨by rw [conjTranspose_add, hPh, rankOne_conjTranspose], ?_⟩
  have h1 : P * rankOne u = 0 := by rw [mul_rankOne hPh hu, star_zero, zero_vecMulVec, smul_zero]
  have h2 : rankOne u * P = 0 := by rw [rankOne_mul hu, vecMulVec_zero, smul_zero]
  rw [add_mul, mul_add, mul_add, hPP, h1, h2, rankOne_mul_self hu0]
  abel

/-! ### Projections and the first-order condition -/

lemma posSemidef_of_proj {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) (hPP : P * P = P) :
    P.PosSemidef := by
  have := posSemidef_conjTranspose_mul_self P
  rwa [hPh, hPP] at this

lemma one_sub_proj {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) (hPP : P * P = P) :
    (1 - P)ᴴ = 1 - P ∧ (1 - P) * (1 - P) = 1 - P := by
  refine ⟨by rw [conjTranspose_sub, conjTranspose_one, hPh], ?_⟩
  rw [sub_mul, mul_sub, mul_sub, hPP, one_mul, mul_one, one_mul]
  abel

/-- The segment between two Hermitian projections lies in `{0 ≤ γ ≤ 1}`. -/
lemma admissible_segment {P Q : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) (hPP : P * P = P)
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (P + (t : ℂ) • (Q - P)).PosSemidef ∧ (1 - (P + (t : ℂ) • (Q - P))).PosSemidef := by
  have e1 : P + (t : ℂ) • (Q - P) = ((1 - t : ℝ) : ℂ) • P + (t : ℂ) • Q := by
    push_cast; module
  have e2 : 1 - (P + (t : ℂ) • (Q - P)) = ((1 - t : ℝ) : ℂ) • (1 - P) + (t : ℂ) • (1 - Q) := by
    push_cast; module
  have h1t : (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) := Complex.zero_le_real.mpr (by linarith)
  have ht : (0 : ℂ) ≤ (t : ℂ) := Complex.zero_le_real.mpr ht0
  obtain ⟨hP1h, hP1P⟩ := one_sub_proj hPh hPP
  obtain ⟨hQ1h, hQ1Q⟩ := one_sub_proj hQh hQQ
  rw [e2, e1]
  exact ⟨((posSemidef_of_proj hPh hPP).smul h1t).add ((posSemidef_of_proj hQh hQQ).smul ht),
    ((posSemidef_of_proj hP1h hP1P).smul h1t).add ((posSemidef_of_proj hQ1h hQ1Q).smul ht)⟩

/-- **First-order condition.** If `V ⪰ 0` and `P` minimizes `E_HF` over rank-`N` projections,
then `Re Σ F(P)_ab (Q - P)_ab ≥ 0` for every rank-`N` projection `Q`. -/
theorem hf_first_order (hV : V.PosSemidef) {N : ℕ} {P Q : Matrix (Fin M) (Fin M) ℂ}
    (hPh : Pᴴ = P) (hPP : P * P = P) (hPtr : P.trace = N)
    (hmin : ∀ Q : Matrix (Fin M) (Fin M) ℂ, Qᴴ = Q → Q * Q = Q → Q.trace = N →
      hfEnergy h V P ≤ hfEnergy h V Q)
    (hQh : Qᴴ = Q) (hQQ : Q * Q = Q) (hQtr : Q.trace = N) :
    0 ≤ (∑ a, ∑ b, fockMat h V P a b * (Q - P) a b).re := by
  refine nonneg_of_forall_lin_quad (c := (pairForm V (Q - P) (Q - P)).re) fun t ht0 ht1 => ?_
  obtain ⟨h0, h1⟩ := admissible_segment hPh hPP hQh hQQ ht0.le ht1
  have htr : (P + (t : ℂ) • (Q - P)).trace = N := by
    rw [trace_add, trace_smul, trace_sub, hPtr, hQtr, sub_self, smul_zero, add_zero]
  obtain ⟨R, hRh, hRR, hRtr, hRE⟩ := lieb_variational h V hV h0 h1 htr
  have := (hmin R hRh hRR hRtr).trans hRE
  rw [hfEnergy_add_smul_fock] at this
  linarith

/-! ### No unfilled shells -/

/-- **No unfilled shells (aufbau).** If `V ⪰ 0` and `P` minimizes `E_HF` over rank-`N`
projections, then every occupied orbital lies no higher than every unoccupied one. -/
theorem hf_aufbau (hV : V.PosSemidef) {N : ℕ} {P : Matrix (Fin M) (Fin M) ℂ}
    (hPh : Pᴴ = P) (hPP : P * P = P) (hPtr : P.trace = N)
    (hmin : ∀ Q : Matrix (Fin M) (Fin M) ℂ, Qᴴ = Q → Q * Q = Q → Q.trace = N →
      hfEnergy h V P ≤ hfEnergy h V Q)
    {x y : Fin M → ℂ} (hx : Pᵀ *ᵥ x = x) (hy : Pᵀ *ᵥ y = 0)
    (hx1 : star x ⬝ᵥ x = 1) (hy1 : star y ⬝ᵥ y = 1) :
    (star x ⬝ᵥ (fockMat h V P *ᵥ x)).re ≤ (star y ⬝ᵥ (fockMat h V P *ᵥ y)).re := by
  rw [mulVec_transpose] at hx hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx1
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  obtain ⟨h1h, h1P⟩ := proj_sub_rankOne hPh hPP hx0 hx
  have hyx : y ⬝ᵥ star x = 0 := by
    rw [← mulVec_star_eq hPh hx, dotProduct_mulVec, hy, zero_dotProduct]
  have hy' : y ᵥ* (P - rankOne x) = 0 := by
    rw [vecMul_sub, hy, vecMul_rankOne, hyx, mul_zero, zero_smul, sub_zero]
  obtain ⟨hQh, hQQ⟩ := proj_add_rankOne h1h h1P hy0 hy'
  have hQtr : (P - rankOne x + rankOne y).trace = N := by
    rw [trace_add, trace_sub, hPtr, trace_rankOne hx0, trace_rankOne hy0]; ring
  have := hf_first_order hV hPh hPP hPtr hmin hQh hQQ hQtr
  have e : P - rankOne x + rankOne y - P = rankOne y - rankOne x := by abel
  rw [e] at this
  simp only [Matrix.sub_apply, mul_sub, sum_sub_distrib, sum_mul_rankOne, hx1, hy1, inv_one,
    one_mul, Complex.sub_re] at this
  linarith

/-! ### The Hartree–Fock equations -/

lemma dotProduct_mulVec_swap {G : Matrix (Fin M) (Fin M) ℂ} (hG : G.IsHermitian)
    (x y : Fin M → ℂ) : star x ⬝ᵥ (G *ᵥ y) = star (star y ⬝ᵥ (G *ᵥ x)) := by
  rw [star_dotProduct, star_mulVec, hG.eq, ← dotProduct_mulVec]

lemma dotProduct_mulVec_add_smul (G : Matrix (Fin M) (Fin M) ℂ) (x y : Fin M → ℂ) (c : ℂ) :
    star (x + c • y) ⬝ᵥ (G *ᵥ (x + c • y)) = star x ⬝ᵥ (G *ᵥ x) + c * (star x ⬝ᵥ (G *ᵥ y)) +
      star c * (star y ⬝ᵥ (G *ᵥ x)) + star c * c * (star y ⬝ᵥ (G *ᵥ y)) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- Rotating an occupied orbital `x` towards an unoccupied direction `y` with phase `e`:
the first-order term vanishes. -/
lemma hf_offDiag_re (hV : V.PosSemidef) {N : ℕ} {P : Matrix (Fin M) (Fin M) ℂ}
    (hPh : Pᴴ = P) (hPP : P * P = P) (hPtr : P.trace = N)
    (hmin : ∀ Q : Matrix (Fin M) (Fin M) ℂ, Qᴴ = Q → Q * Q = Q → Q.trace = N →
      hfEnergy h V P ≤ hfEnergy h V Q)
    {x y : Fin M → ℂ} (hx0 : x ≠ 0) (hx : x ᵥ* P = x) (hy : y ᵥ* P = 0) {e : ℂ}
    (he : star e * e = 1) :
    (e * (star x ⬝ᵥ (fockMat h V P *ᵥ y)) + star e * (star y ⬝ᵥ (fockMat h V P *ᵥ x))).re = 0 := by
  set G := fockMat h V P
  set m := (e * (star x ⬝ᵥ (G *ᵥ y)) + star e * (star y ⬝ᵥ (G *ᵥ x))).re
  set nx := (star x ⬝ᵥ x).re
  set ny := (star y ⬝ᵥ y).re
  have hnx : 0 < nx := dotProduct_self_re_pos hx0
  have hny : 0 ≤ ny := dotProduct_self_re_nonneg y
  obtain ⟨h1h, h1P⟩ := proj_sub_rankOne hPh hPP hx0 hx
  have hyx : y ⬝ᵥ star x = 0 := by
    rw [← mulVec_star_eq hPh hx, dotProduct_mulVec, hy, zero_dotProduct]
  have hxy : x ⬝ᵥ star y = 0 := by
    rw [← hx, ← dotProduct_mulVec, mulVec_star_eq hPh hy, star_zero, dotProduct_zero]
  have hsxy : star x ⬝ᵥ y = 0 := by rw [dotProduct_comm, hyx]
  have hsyx : star y ⬝ᵥ x = 0 := by rw [dotProduct_comm, hxy]
  suffices H : nx * m = 0 by
    rcases mul_eq_zero.mp H with h | h
    · exact absurd h hnx.ne'
    · exact h
  refine eq_zero_of_forall_lin_quad (d := nx * (star y ⬝ᵥ (G *ᵥ y)).re -
    ny * (star x ⬝ᵥ (G *ᵥ x)).re) fun s => ?_
  set c : ℂ := (s : ℂ) * e
  set w := x + c • y
  have hwP : w ᵥ* P = x := by rw [add_vecMul, smul_vecMul, hx, hy, smul_zero, add_zero]
  have hw0 : w ≠ 0 := fun h0 => hx0 (by rw [← hwP, h0, zero_vecMul])
  have hw : w ᵥ* (P - rankOne x) = 0 := by
    have hn := dotProduct_self_ne_zero hx0
    rw [vecMul_sub, hwP, vecMul_rankOne, add_dotProduct, smul_dotProduct, hyx, smul_zero,
      add_zero, dotProduct_comm x, inv_mul_cancel₀ hn, one_smul, sub_self]
  obtain ⟨hQh, hQQ⟩ := proj_add_rankOne h1h h1P hw0 hw
  have hQtr : (P - rankOne x + rankOne w).trace = N := by
    rw [trace_add, trace_sub, hPtr, trace_rankOne hx0, trace_rankOne hw0]; ring
  have key := hf_first_order hV hPh hPP hPtr hmin hQh hQQ hQtr
  have e0 : P - rankOne x + rankOne w - P = rankOne w - rankOne x := by abel
  rw [e0] at key
  simp only [Matrix.sub_apply, mul_sub, sum_sub_distrib, sum_mul_rankOne] at key
  have hcc : star c * c = ((s ^ 2 : ℝ) : ℂ) := by
    calc star c * c = (s : ℂ) ^ 2 * (star e * e) := by
          simp only [c, star_mul', Complex.star_def, Complex.conj_ofReal]; ring
      _ = _ := by rw [he]; push_cast; ring
  have hnw : star w ⬝ᵥ w = ((nx + s ^ 2 * ny : ℝ) : ℂ) := by
    have := dotProduct_mulVec_add_smul 1 x y c
    simp only [one_mulVec] at this
    rw [this, hsxy, hsyx, hcc, ← dotProduct_self_ofReal_re x, ← dotProduct_self_ofReal_re y]
    push_cast
    simp only [mul_zero, add_zero, nx, ny]
  have hAw : star w ⬝ᵥ (G *ᵥ w) = star x ⬝ᵥ (G *ᵥ x) +
      (s : ℂ) * (e * (star x ⬝ᵥ (G *ᵥ y)) + star e * (star y ⬝ᵥ (G *ᵥ x))) +
      ((s ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (G *ᵥ y)) := by
    rw [dotProduct_mulVec_add_smul, hcc]
    have : star c = (s : ℂ) * star e := by
      simp only [c, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [this]
    simp only [c]
    ring
  rw [hnw, hAw, ← dotProduct_self_ofReal_re x, inv_mul_eq_div, inv_mul_eq_div, Complex.sub_re,
    Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.add_re, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul] at key
  have hD : 0 < nx + s ^ 2 * ny := by positivity
  have k2 := sub_nonneg.mp key
  rw [div_le_div_iff₀ hnx hD] at k2
  have : (star x ⬝ᵥ (G *ᵥ x)).re * (nx + s ^ 2 * ny) ≤
      ((star x ⬝ᵥ (G *ᵥ x)).re + s * m + s ^ 2 * (star y ⬝ᵥ (G *ᵥ y)).re) * nx := k2
  nlinarith [this]

/-- **The off-diagonal block of the Fock matrix vanishes** at a minimizer: `⟨y, F x⟩ = 0` for
`x` occupied and `y` unoccupied. -/
theorem hf_offDiag (hh : h.IsHermitian) (hV : V.PosSemidef) {N : ℕ}
    {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) (hPP : P * P = P) (hPtr : P.trace = N)
    (hmin : ∀ Q : Matrix (Fin M) (Fin M) ℂ, Qᴴ = Q → Q * Q = Q → Q.trace = N →
      hfEnergy h V P ≤ hfEnergy h V Q)
    {x y : Fin M → ℂ} (hx : x ᵥ* P = x) (hy : y ᵥ* P = 0) :
    star y ⬝ᵥ (fockMat h V P *ᵥ x) = 0 := by
  by_cases hx0 : x = 0
  · rw [hx0, mulVec_zero, dotProduct_zero]
  have hG : (fockMat h V P).IsHermitian := fockMat_isHermitian h V hh hV.1 hPh
  have h1 := hf_offDiag_re hV hPh hPP hPtr hmin hx0 hx hy (e := 1) (by simp)
  have hI := hf_offDiag_re hV hPh hPP hPtr hmin hx0 hx hy (e := Complex.I) (by simp)
  rw [dotProduct_mulVec_swap hG x y] at h1 hI
  set p := star y ⬝ᵥ (fockMat h V P *ᵥ x)
  apply Complex.ext
  · simp at h1 hI ⊢; linarith
  · simp at h1 hI ⊢; linarith

/-- **The Hartree–Fock equations** `[F(P), Pᵀ] = 0` at a minimizer. -/
theorem hf_equation (hh : h.IsHermitian) (hV : V.PosSemidef) {N : ℕ}
    {P : Matrix (Fin M) (Fin M) ℂ} (hPh : Pᴴ = P) (hPP : P * P = P) (hPtr : P.trace = N)
    (hmin : ∀ Q : Matrix (Fin M) (Fin M) ℂ, Qᴴ = Q → Q * Q = Q → Q.trace = N →
      hfEnergy h V P ≤ hfEnergy h V Q) :
    fockMat h V P * Pᵀ = Pᵀ * fockMat h V P := by
  set G := fockMat h V P
  have hG : G.IsHermitian := fockMat_isHermitian h V hh hV.1 hPh
  have hTh : Pᵀᴴ = Pᵀ := by rw [transpose_conjTranspose, ← conjTranspose_transpose, hPh]
  have hTT : Pᵀ * Pᵀ = Pᵀ := by rw [← transpose_mul, hPP]
  obtain ⟨h1h, -⟩ := one_sub_proj hTh hTT
  have hC : (1 - Pᵀ) * G * Pᵀ = 0 := by
    ext i j
    have hij : ((1 - Pᵀ) * G * Pᵀ) i j =
        Pi.single i 1 ⬝ᵥ (((1 - Pᵀ) * G * Pᵀ) *ᵥ Pi.single j 1) := by
      simp
    have hsi : star (Pi.single i 1 : Fin M → ℂ) = Pi.single i 1 := by
      ext k; simp only [Pi.star_apply, Pi.single_apply]; split_ifs <;> simp
    have hy : ((1 - Pᵀ) *ᵥ Pi.single i 1) ᵥ* P = 0 := by
      rw [← mulVec_transpose, mulVec_mulVec, mul_sub, mul_one, hTT, sub_self, zero_mulVec]
    have hx : (Pᵀ *ᵥ Pi.single j 1) ᵥ* P = Pᵀ *ᵥ Pi.single j 1 := by
      rw [← mulVec_transpose, mulVec_mulVec, hTT]
    have := hf_offDiag hh hV hPh hPP hPtr hmin hx hy
    rw [star_mulVec, h1h, hsi, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec] at this
    rw [hij, Matrix.zero_apply, ← this, mul_assoc]
  have e1 : G * Pᵀ = Pᵀ * G * Pᵀ := by
    rw [sub_mul, sub_mul, one_mul] at hC; exact sub_eq_zero.mp hC
  have hC' : Pᵀ * G * (1 - Pᵀ) = 0 := by
    have := congrArg conjTranspose hC
    rwa [conjTranspose_mul, conjTranspose_mul, hTh, hG.eq, h1h, conjTranspose_zero,
      ← mul_assoc] at this
  have e2 : Pᵀ * G = Pᵀ * G * Pᵀ := by
    rw [mul_sub, mul_one] at hC'; exact sub_eq_zero.mp hC'
  exact e1.trans e2.symm

end QM.ManyBody
