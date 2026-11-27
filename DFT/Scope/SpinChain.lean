/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Scope.Ranges

/-!
# Spin chains as a scope

`m` spins `½` (configurations `σ : m → Bool`), any Hermitian `H₀`, and the observables `Z_i`
(diagonal, `Z_i σ = ±1` according to `σ_i`): spin-density functional theory for the `z`-components.

* `expv_diagonal`: for a real diagonal observable, `⟨ψ, D ψ⟩ = Σ_c f_c |ψ_c|²`.
* `spinScope_Bp`, `spinScope_Be`: **both ranges are the cube `[-1, 1]^m`**. Every point of the cube
  is the magnetisation of a product state, with amplitudes `|ψ_σ|² = Π_i (1 + σ_i ρ_i)/2`.
-/

namespace DFT.Scope

open Matrix RCLike Set

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A real diagonal observable: `⟨ψ, diag(f) ψ⟩ = Σ_c f_c |ψ_c|²`. -/
lemma expv_diagonal {d : Type*} [Fintype d] [DecidableEq d] (f : d → ℝ) (ψ : d → 𝕜) :
    expv (diagonal fun c => (f c : 𝕜)) ψ = ∑ c, f c * ‖ψ c‖ ^ 2 := by
  simp only [expv, mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_left_comm, RCLike.star_def, RCLike.conj_mul, ← ofReal_pow, ← ofReal_mul, ofReal_re]

/-- The eigenvalue `±1` of `Z` on a spin. -/
def zsign (b : Bool) : ℝ := if b then 1 else -1

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Spin chains as a scope**: the observables are the `Z_i`. -/
noncomputable def spinScope (H0 : Matrix (m → Bool) (m → Bool) 𝕜) (hH0 : H0.IsHermitian) :
    Scope 𝕜 (m → Bool) m where
  H0 := H0
  B i := diagonal fun σ => ((zsign (σ i) : ℝ) : 𝕜)
  isHermitian_H0 := hH0
  isHermitian_B i := by
    rw [IsHermitian, diagonal_conjTranspose]
    congr 1
    funext σ
    simp

variable {H0 : Matrix (m → Bool) (m → Bool) 𝕜} (hH0 : H0.IsHermitian)

/-- The cube `[-1, 1]^m`. -/
def cube (m : Type*) : Set (m → ℝ) := Set.pi univ fun _ => Icc (-1) 1

lemma spinScope_densPure (ψ : (m → Bool) → 𝕜) (i : m) :
    (spinScope H0 hH0).densPure ψ i = ∑ σ, zsign (σ i) * ‖ψ σ‖ ^ 2 := by
  simp only [densPure, spinScope]
  exact expv_diagonal _ ψ

/-- **The pure range of a spin chain is the cube.** -/
theorem spinScope_Bp : (spinScope H0 hH0).Bp = cube m := by
  ext ρ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩ i -
    have h1 := sum_norm_sq_eq_one hψ
    rw [spinScope_densPure]
    have hz : ∀ σ : m → Bool, -1 ≤ zsign (σ i) ∧ zsign (σ i) ≤ 1 := fun σ => by
      unfold zsign; split_ifs <;> norm_num
    constructor
    · rw [← h1, ← neg_one_mul, Finset.mul_sum]
      exact Finset.sum_le_sum fun σ _ =>
        mul_le_mul_of_nonneg_right (hz σ).1 (sq_nonneg _)
    · rw [← h1]
      exact Finset.sum_le_sum fun σ _ =>
        (mul_le_mul_of_nonneg_right (hz σ).2 (sq_nonneg _)).trans (by rw [one_mul])
  · intro hρ
    set p : m → Bool → ℝ := fun i b => (1 + zsign b * ρ i) / 2 with hp
    have hp0 : ∀ i b, 0 ≤ p i b := fun i b => by
      have := hρ i (mem_univ _)
      simp only [hp, zsign]
      split_ifs <;> linarith [this.1, this.2]
    have hpsum : ∀ i, ∑ b, p i b = 1 := fun i => by
      simp [hp, zsign]; ring
    have hpdiff : ∀ i, ∑ b, zsign b * p i b = ρ i := fun i => by
      simp [hp, zsign]; ring
    set ψ : (m → Bool) → 𝕜 := fun σ => ((Real.sqrt (∏ i, p i (σ i)) : ℝ) : 𝕜)
    have hψ2 : ∀ σ, ‖ψ σ‖ ^ 2 = ∏ i, p i (σ i) := fun σ => by
      simp only [ψ, norm_ofReal, sq_abs]
      exact Real.sq_sqrt (Finset.prod_nonneg fun i _ => hp0 i _)
    refine ⟨ψ, ?_, ?_⟩
    · change star ψ ⬝ᵥ ψ = 1
      rw [star_dotProduct_self_eq]
      simp only [hψ2]
      rw [← Fintype.prod_sum (f := fun i b => p i b)]
      simp only [hpsum, Finset.prod_const_one, ofReal_one]
    · funext i
      rw [spinScope_densPure]
      simp only [hψ2]
      have hprod : ∀ σ : m → Bool, zsign (σ i) * ∏ j, p j (σ j) =
          ∏ j, (if j = i then zsign (σ j) * p j (σ j) else p j (σ j)) := fun σ => by
        have hc : ∏ j ∈ ({i} : Finset m)ᶜ,
            (if j = i then zsign (σ j) * p j (σ j) else p j (σ j)) =
              ∏ j ∈ ({i} : Finset m)ᶜ, p j (σ j) :=
          Finset.prod_congr rfl fun j hj => by
            simp only [Finset.mem_compl, Finset.mem_singleton] at hj; simp only [hj, ↓reduceIte]
        rw [← Finset.prod_mul_prod_compl {i} (fun j => p j (σ j)),
          ← Finset.prod_mul_prod_compl {i}
            (fun j => if j = i then zsign (σ j) * p j (σ j) else p j (σ j)), hc]
        simp only [Finset.prod_singleton, ite_true]
        ring
      simp only [hprod]
      rw [← Fintype.prod_sum (f := fun j b => if j = i then zsign b * p j b else p j b)]
      rw [Finset.prod_eq_single i (fun j _ hj => by simp only [hj, ↓reduceIte]; exact hpsum j)
        (by simp)]
      simp only [ite_true]
      exact hpdiff i

/-- **The ensemble range of a spin chain is the cube.** -/
theorem spinScope_Be : (spinScope H0 hH0).Be = cube m := by
  rw [Be_eq_convexHull_Bp, spinScope_Bp]
  exact (convex_pi fun _ _ => convex_Icc _ _).convexHull_eq

end DFT.Scope
