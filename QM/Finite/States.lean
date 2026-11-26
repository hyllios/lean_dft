/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QuantumInfo.States.Mixed.MState
import QM.Basic

/-!
# States and observables: Physlib and QuantumInfo

Physlib states the basic notions of quantum mechanics for (possibly unbounded) operators
`T : H →ₗ.[ℂ] H` and unit vectors in their domain (`LinearPMap.expectedValue`,
`LinearPMap.variance`). QuantumInfo works with matrices: Hermitian matrices `HermitianMat d ℂ`,
kets `Ket d` and density matrices `MState d` with `MState.exp_val T = tr ρT`. This file connects
the two on `ℂ^d = EuclideanSpace ℂ d`.

## Main definitions

* `QM.obs T`: the Physlib observable of a Hermitian matrix, with domain `ℂ^d`.
* `QM.ketVec ψ`, `QM.ketDom T ψ`: a ket as a vector and as an element of the domain of `obs T`.

## Main results

* `exp_val_pure` (**bridge**): `(pure ψ).exp_val T = ⟨T⟩_ψ` (Physlib's expectation value).
* `variance_obs`: Physlib's variance is `⟨T²⟩ - ⟨T⟩²`.
* `expectedValue_obs_eq_sum` (**Born rule**): `⟨T⟩_ψ = Σ_n λ_n |⟨e_n, ψ⟩|²`, and
  `sum_born_prob`: the probabilities add up to `1`.
* `exp_val_eq_sum` and `exists_exp_val_eq_sum`: for a density matrix, `tr ρT = Σ_k p_k ⟨T⟩_{φ_k}`
  over any decomposition into pure states, in particular over its spectral decomposition.
-/

namespace QM

open Matrix ComplexConjugate

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Physlib observable of a Hermitian matrix: the operator `T` on `ℂ^d`, with domain `ℂ^d`. -/
noncomputable def obs (T : HermitianMat d ℂ) : EuclideanSpace ℂ d →ₗ.[ℂ] EuclideanSpace ℂ d :=
  (Matrix.toEuclideanLin T.mat).toPMap ⊤

/-- A ket as a vector of `ℂ^d`. -/
def ketVec (ψ : Ket d) : EuclideanSpace ℂ d := WithLp.toLp 2 ψ.vec

omit [DecidableEq d] in
lemma norm_ketVec (ψ : Ket d) : ‖ketVec ψ‖ = 1 := by
  have h := ψ.normalized'
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simpa [ketVec] using h

/-- A ket as an element of the domain of `obs T`. -/
def ketDom (T : HermitianMat d ℂ) (ψ : Ket d) : (obs T).domain :=
  ⟨ketVec ψ, Submodule.mem_top⟩

lemma obs_apply (T : HermitianMat d ℂ) (x : (obs T).domain) :
    obs T x = Matrix.toEuclideanLin T.mat x := rfl

lemma obs_isSymmetric (T : HermitianMat d ℂ) : (obs T).IsSymmetric := by
  intro x y
  rw [obs_apply, obs_apply]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr T.H) x y

/-- Physlib's `⟨T⟩_ψ = Re Σ_ij ψ̄_i T_ij ψ_j`. -/
lemma expectedValue_obs (T : HermitianMat d ℂ) (ψ : Ket d) :
    LinearPMap.expectedValue (obs T) (ketDom T ψ) = (star ψ.vec ⬝ᵥ (T.mat *ᵥ ψ.vec)).re := by
  rw [LinearPMap.expectedValue, obs_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toLpLin, dotProduct_comm]
  simp only [ketDom, ketVec, WithLp.ofLp_toLp, Matrix.toLin'_apply]

/-- `tr (|ψ⟩⟨ψ| T) = Σ_ij ψ̄_i T_ij ψ_j`. -/
lemma trace_pure_mul (T : HermitianMat d ℂ) (ψ : Ket d) :
    ((MState.pure ψ).M.mat * T.mat).trace = star ψ.vec ⬝ᵥ (T.mat *ᵥ ψ.vec) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, MState.mat_M, MState.pure_apply,
    dotProduct, mulVec, Pi.star_apply]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Ket.apply, Ket.apply]
  ring

/-- **Bridge**: the expectation value of `T` in the pure state `|ψ⟩⟨ψ|` (QuantumInfo) is Physlib's
expectation value `⟨T⟩_ψ`. -/
theorem exp_val_pure (T : HermitianMat d ℂ) (ψ : Ket d) :
    (MState.pure ψ).exp_val T = LinearPMap.expectedValue (obs T) (ketDom T ψ) := by
  rw [expectedValue_obs, MState.exp_val, HermitianMat.inner_eq_re_trace, trace_pure_mul]
  rfl

/-- `‖Tψ‖² = ⟨ψ, T²ψ⟩`. -/
lemma norm_obs_sq (T : HermitianMat d ℂ) (ψ : Ket d) :
    ‖obs T (ketDom T ψ)‖ ^ 2 = (star ψ.vec ⬝ᵥ ((T ^ 2).mat *ᵥ ψ.vec)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), obs_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm, Matrix.ofLp_toLpLin]
  simp only [ketDom, ketVec, WithLp.ofLp_toLp, Matrix.toLin'_apply]
  rw [HermitianMat.mat_pow, pow_two, ← mulVec_mulVec, star_mulVec, ← dotProduct_mulVec, T.H.eq]
  rfl

/-- **Physlib's variance is `⟨T²⟩ - ⟨T⟩²`.** -/
theorem variance_obs (T : HermitianMat d ℂ) (ψ : Ket d) :
    LinearPMap.variance (obs T) (ketDom T ψ) =
      (MState.pure ψ).exp_val (T ^ 2) - ((MState.pure ψ).exp_val T) ^ 2 := by
  have h := LinearPMap.variance_eq_norm_sq_sub_expectedValue_sq (obs T) (obs_isSymmetric T)
    (ketDom T ψ) (norm_ketVec ψ)
  rw [h, norm_obs_sq, ← exp_val_pure, exp_val_pure (T ^ 2), expectedValue_obs]

/-! ### The Born rule -/

/-- The eigenvectors of `T`. -/
lemma toEuclideanLin_eigenvectorBasis (T : HermitianMat d ℂ) (n : d) :
    Matrix.toEuclideanLin T.mat (T.H.eigenvectorBasis n) =
      ((T.H.eigenvalues n : ℝ) : ℂ) • T.H.eigenvectorBasis n := by
  have h := T.H.mulVec_eigenvectorBasis n
  change Matrix.toEuclideanLin T.mat (WithLp.toLp 2 (WithLp.ofLp (T.H.eigenvectorBasis n))) = _
  rw [Matrix.toLpLin_toLp, Matrix.toLin'_apply, h]
  rfl

/-- **The Born rule**: `⟨T⟩_ψ = Σ_n λ_n |⟨e_n, ψ⟩|²` over an orthonormal eigenbasis of `T`. -/
theorem expectedValue_obs_eq_sum (T : HermitianMat d ℂ) (ψ : Ket d) :
    LinearPMap.expectedValue (obs T) (ketDom T ψ) =
      ∑ n, T.H.eigenvalues n * ‖inner ℂ (T.H.eigenvectorBasis n) (ketVec ψ)‖ ^ 2 := by
  set e := T.H.eigenvectorBasis
  have hT : Matrix.toEuclideanLin T.mat (ketVec ψ) =
      ∑ n, ((T.H.eigenvalues n : ℝ) : ℂ) • (inner ℂ (e n) (ketVec ψ) • e n) := by
    conv_lhs => rw [← e.sum_repr' (ketVec ψ)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, toEuclideanLin_eigenvectorBasis, smul_comm]
  rw [LinearPMap.expectedValue, obs_apply]
  change (inner ℂ (ketVec ψ) (Matrix.toEuclideanLin T.mat (ketVec ψ))).re = _
  rw [hT, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_smul_right, inner_smul_right, ← inner_conj_symm (e n),
    mul_comm ((starRingEnd ℂ) _), Complex.mul_conj', Complex.norm_conj, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The Born probabilities `|⟨e_n, ψ⟩|²` add up to `1`. -/
theorem sum_born_prob (T : HermitianMat d ℂ) (ψ : Ket d) :
    ∑ n, ‖inner ℂ (T.H.eigenvectorBasis n) (ketVec ψ)‖ ^ 2 = 1 := by
  rw [T.H.eigenvectorBasis.sum_sq_norm_inner_right, norm_ketVec, one_pow]

/-! ### Mixed states -/

/-- For a density matrix decomposed into pure states, `tr ρT = Σ_k p_k ⟨T⟩_{φ_k}`. -/
theorem exp_val_eq_sum {ι : Type*} [Fintype ι] (ρ : MState d) (p : ι → ℝ) (φ : ι → Ket d)
    (hρ : ρ.M = ∑ k, p k • (MState.pure (φ k)).M) (T : HermitianMat d ℂ) :
    ρ.exp_val T = ∑ k, p k * LinearPMap.expectedValue (obs T) (ketDom T (φ k)) := by
  rw [MState.exp_val, hρ, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_left, ← MState.exp_val, exp_val_pure]

/-- **Mixed states**: every density matrix is `ρ = Σ_k p_k |φ_k⟩⟨φ_k|` with `p_k ≥ 0`,
`Σ_k p_k = 1` (its spectral decomposition), and then `tr ρT = Σ_k p_k ⟨T⟩_{φ_k}` for every
Hermitian `T`. -/
theorem exists_exp_val_eq_sum (ρ : MState d) :
    ∃ (p : d → ℝ) (φ : d → Ket d), (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧
      ρ.M = ∑ k, p k • (MState.pure (φ k)).M ∧
      ∀ T : HermitianMat d ℂ,
        ρ.exp_val T = ∑ k, p k * LinearPMap.expectedValue (obs T) (ketDom T (φ k)) := by
  obtain ⟨φ, hφ⟩ := ρ.spectralDecomposition
  refine ⟨fun k => ρ.spectrum k, φ, fun k => (ρ.spectrum k).2.1, ρ.spectrum.normalized, hφ,
    fun T => exp_val_eq_sum ρ _ φ hφ T⟩

end QM
