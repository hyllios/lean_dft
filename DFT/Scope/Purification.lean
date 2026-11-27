/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import DFT.Scope.Functionals

/-!
# Purification of the ensemble functional (stage 3)

After Wang–Liebert–Penz–Schilling, Theorem 7.2. The purified scope lives on `𝕜^d ⊗ 𝕜^d`
(indexed by `d × d`), with `H₀ ⊗ 1` and observables `B_i ⊗ 1`. Every density matrix is the partial
trace of a pure state on the doubled space, and expectation values of `A ⊗ 1` are traces against
the partial trace, so:

* `purify_Bp`: the pure range of the purified scope is the ensemble range of the scope.
* `purify_Fp`: **the pure functional of the purified scope is the ensemble functional**,
  `F_p(S') = F_e(S)`.

Ingredients: `expv_kronecker_one` (`⟨Ψ, (A ⊗ 1) Ψ⟩ = Σ_b ⟨Ψ_b, A Ψ_b⟩` over the columns `Ψ_b`),
`ptrace` (the partial trace `Σ_b |Ψ_b⟩⟨Ψ_b|`), `exists_purification`.
-/

namespace DFT.Scope

open Matrix RCLike Set
open scoped Kronecker ComplexOrder

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [DecidableEq d] [Fintype m] (S : Scope 𝕜 d m)

/-- **The purified scope** on `𝕜^d ⊗ 𝕜^d`: `H₀ ⊗ 1` and `B_i ⊗ 1`. -/
noncomputable def purify : Scope 𝕜 (d × d) m where
  H0 := S.H0 ⊗ₖ (1 : Matrix d d 𝕜)
  B i := S.B i ⊗ₖ (1 : Matrix d d 𝕜)
  isHermitian_H0 := by
    rw [IsHermitian, conjTranspose_kronecker, conjTranspose_one, S.isHermitian_H0.eq]
  isHermitian_B i := by
    rw [IsHermitian, conjTranspose_kronecker, conjTranspose_one, (S.isHermitian_B i).eq]

omit [Fintype m] in
/-- `⟨Ψ, (A ⊗ 1) Ψ⟩ = Σ_b ⟨Ψ_b, A Ψ_b⟩`, with `Ψ_b = Ψ(·, b)`. -/
lemma expv_kronecker_one (A : Matrix d d 𝕜) (Ψ : d × d → 𝕜) :
    expv (A ⊗ₖ (1 : Matrix d d 𝕜)) Ψ = ∑ b, expv A fun a => Ψ (a, b) := by
  simp only [expv, ← map_sum]
  congr 1
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, kronecker_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_eq_single b (fun b' _ hb' => by rw [one_apply_ne (Ne.symm hb')]; ring)
    (by simp), one_apply_eq, mul_one]

/-- The partial trace `Σ_b |Ψ_b⟩⟨Ψ_b|` of a vector of `𝕜^d ⊗ 𝕜^d`. -/
def ptrace (Ψ : d × d → 𝕜) : Matrix d d 𝕜 :=
  ∑ b, vecMulVec (fun a => Ψ (a, b)) (star fun a => Ψ (a, b))

omit [DecidableEq d] [Fintype m] in
lemma trv_ptrace (A : Matrix d d 𝕜) (Ψ : d × d → 𝕜) :
    trv A (ptrace Ψ) = ∑ b, expv A fun a => Ψ (a, b) := by
  simp only [ptrace, trv, Finset.sum_mul, trace_sum, map_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [← trv, trv_pure]

omit [DecidableEq d] [Fintype m] in
lemma ptrace_mem_densMats {Ψ : d × d → 𝕜} (hΨ : Ψ ∈ (unitVecs : Set (d × d → 𝕜))) :
    ptrace Ψ ∈ (densMats : Set (Matrix d d 𝕜)) := by
  refine ⟨posSemidef_sum _ fun b _ => posSemidef_vecMulVec_self_star _, ?_⟩
  have h : star Ψ ⬝ᵥ Ψ = 1 := hΨ
  rw [ptrace, trace_sum, ← h]
  simp only [trace_vecMulVec, dotProduct, Fintype.sum_prod_type, Pi.star_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => mul_comm _ _

omit [DecidableEq d] [Fintype m] in
lemma expv_ofReal_smul (A : Matrix d d 𝕜) (t : ℝ) (x : d → 𝕜) :
    expv A ((t : 𝕜) • x) = t ^ 2 * expv A x := by
  simp only [expv, mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, RCLike.star_def,
    conj_ofReal, smul_eq_mul, ← mul_assoc, ← ofReal_mul, re_ofReal_mul, sq]

omit [Fintype m] in
/-- **Purification**: every density matrix is the partial trace of a unit vector on the doubled
space (as far as expectation values go). -/
lemma exists_purification {Γ : Matrix d d 𝕜} (hΓ : Γ ∈ (densMats : Set (Matrix d d 𝕜))) :
    ∃ Ψ ∈ (unitVecs : Set (d × d → 𝕜)), ∀ A : Matrix d d 𝕜,
      expv (A ⊗ₖ (1 : Matrix d d 𝕜)) Ψ = trv A Γ := by
  obtain ⟨p, u, hp, hp1, hu, -, htr⟩ := exists_decomp hΓ
  set Ψ : d × d → 𝕜 := fun x => ((Real.sqrt (p x.2) : ℝ) : 𝕜) * u x.2 x.1
  have hcol : ∀ b, (fun a => Ψ (a, b)) = ((Real.sqrt (p b) : ℝ) : 𝕜) • u b := fun b => by
    funext a; simp [Ψ]
  refine ⟨Ψ, ?_, fun A => ?_⟩
  · change star Ψ ⬝ᵥ Ψ = 1
    rw [star_dotProduct_self_eq, ← ofReal_one]
    congr 1
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← hp1]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := sum_norm_sq_eq_one (hu b)
    simp only [Ψ, norm_mul, norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hp b), ← Finset.mul_sum, h1, mul_one]
  · rw [expv_kronecker_one, htr]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hcol, expv_ofReal_smul, Real.sq_sqrt (hp b)]

omit [Fintype m] in
lemma purify_densPure (Ψ : d × d → 𝕜) : S.purify.densPure Ψ = S.dens (ptrace Ψ) := by
  funext i
  simp only [densPure, purify, dens, expv_kronecker_one, trv_ptrace]

omit [Fintype m] in
/-- **The pure range of the purified scope is the ensemble range.** -/
theorem purify_Bp : S.purify.Bp = S.Be := by
  ext ρ
  constructor
  · rintro ⟨Ψ, hΨ, rfl⟩
    exact ⟨ptrace Ψ, ptrace_mem_densMats hΨ, (S.purify_densPure Ψ).symm⟩
  · rintro ⟨Γ, hΓ, rfl⟩
    obtain ⟨Ψ, hΨ, hA⟩ := exists_purification hΓ
    exact ⟨Ψ, hΨ, funext fun i => hA (S.B i)⟩

omit [Fintype m] in
/-- **Theorem 7.2**: the pure functional of the purified scope is the ensemble functional. -/
theorem purify_Fp : S.purify.Fp = S.Fe := by
  funext ρ
  refine le_antisymm (le_iInf₂ fun Γ hΓ => ?_) (le_iInf₂ fun Ψ hΨ => ?_)
  · obtain ⟨Ψ, hΨu, hA⟩ := exists_purification hΓ.1
    have hmem : S.purify.densPure Ψ = ρ := by
      rw [← hΓ.2]; exact funext fun i => hA (S.B i)
    exact (iInf₂_le Ψ ⟨hΨu, hmem⟩).trans (le_of_eq (congrArg _ (hA S.H0)))
  · have hmem : S.dens (ptrace Ψ) = ρ := by rw [← hΨ.2, purify_densPure]
    refine (iInf₂_le (ptrace Ψ) ⟨ptrace_mem_densMats hΨ.1, hmem⟩).trans (le_of_eq ?_)
    simp only [purify, expv_kronecker_one, trv_ptrace]

end DFT.Scope
