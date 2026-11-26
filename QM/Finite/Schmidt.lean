/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QuantumInfo.States.Mixed.MState

/-!
# The Schmidt decomposition

A unit vector `ψ ∈ ℂ^{d₁} ⊗ ℂ^{d₂}` (QuantumInfo's `Ket (d₁ × d₂)`) has the coefficient matrix
`M_ab = ψ(a, b)`, and its reduced density matrices are `ρ₁ = M M†` and `ρ₂ = (M† M)ᵀ`. Diagonalizing
`ρ₁ = Σ_k λ_k |u_k⟩⟨u_k|` gives the Schmidt decomposition `ψ = Σ_k √λ_k u_k ⊗ v_k`.

## Main results

* `traceRight_pure_m`, `traceLeft_pure_m`: the reduced density matrices of a pure state.
* `schmidt` (**Schmidt decomposition**).
* `trace_pow_traceRight_eq` : `tr ρ₁ⁿ = tr ρ₂ⁿ` for `n ≥ 1`.
* `isProd_iff_traceRight_pure`, `traceRight_pure_iff_rank_one` (**product states**): `ψ` is a
  product if and only if `ρ₁` is pure, if and only if exactly one Schmidt weight is nonzero.
-/

namespace QM

open Matrix ComplexConjugate
open scoped ComplexOrder

variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]

/-- The coefficient matrix `M_ab = ψ(a, b)` of a vector of `ℂ^{d₁} ⊗ ℂ^{d₂}`. -/
def coefMat (ψ : Ket (d₁ × d₂)) : Matrix d₁ d₂ ℂ := fun a b => ψ (a, b)

/-- `ρ₁ = M M†`. -/
theorem traceRight_pure_m (ψ : Ket (d₁ × d₂)) :
    (MState.traceRight (MState.pure ψ)).m = coefMat ψ * (coefMat ψ)ᴴ := by
  ext a a'
  simp only [Matrix.mul_apply, conjTranspose_apply, coefMat, RCLike.star_def]
  change ∑ b, (MState.pure ψ).m (a, b) (a', b) = _
  simp [MState.pure_apply]

/-- `ρ₂ = Mᵀ M̄`. -/
theorem traceLeft_pure_m (ψ : Ket (d₁ × d₂)) :
    (MState.traceLeft (MState.pure ψ)).m = (coefMat ψ)ᵀ * (coefMat ψ).map star := by
  ext b b'
  simp only [Matrix.mul_apply, transpose_apply, map_apply, coefMat, RCLike.star_def]
  change ∑ a, (MState.pure ψ).m (a, b) (a, b') = _
  simp [MState.pure_apply]

/-! ### The trace of powers -/

lemma conjTranspose_mul_pow (M : Matrix d₁ d₂ ℂ) (n : ℕ) :
    (Mᴴ * M) ^ (n + 1) = Mᴴ * (M * Mᴴ) ^ n * M := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

/-- **The two reduced density matrices have the same nonzero spectrum**:
`tr ρ₁ⁿ = tr ρ₂ⁿ` for `n ≥ 1`. -/
theorem trace_pow_traceRight_eq (ψ : Ket (d₁ × d₂)) (n : ℕ) :
    ((MState.traceRight (MState.pure ψ)).m ^ (n + 1)).trace =
      ((MState.traceLeft (MState.pure ψ)).m ^ (n + 1)).trace := by
  set M := coefMat ψ
  have hT : Mᵀ * M.map star = (Mᴴ * M)ᵀ := by
    ext i j; simp [Matrix.mul_apply, mul_comm]
  rw [traceRight_pure_m, traceLeft_pure_m, hT, ← transpose_pow, trace_transpose,
    conjTranspose_mul_pow, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-! ### The Schmidt decomposition -/

section Schmidt

variable (ψ : Ket (d₁ × d₂))

/-- The Hermitian reduced density matrix `ρ₁`. -/
lemma traceRight_isHermitian : (MState.traceRight (MState.pure ψ)).M.mat.IsHermitian :=
  (MState.traceRight (MState.pure ψ)).M.H

/-- The unnormalized partner vectors `c_k = conj (M† u_k)`. -/
noncomputable def schmidtPartner (k : d₁) : d₂ → ℂ :=
  star ((coefMat ψ)ᴴ *ᵥ ⇑((traceRight_isHermitian ψ).eigenvectorBasis k))

lemma mulVec_eigenvectorBasis_rho (k : d₁) :
    (coefMat ψ * (coefMat ψ)ᴴ) *ᵥ ⇑((traceRight_isHermitian ψ).eigenvectorBasis k) =
      ((traceRight_isHermitian ψ).eigenvalues k : ℂ) •
        ⇑((traceRight_isHermitian ψ).eigenvectorBasis k) := by
  have h := (traceRight_isHermitian ψ).mulVec_eigenvectorBasis k
  have e : (MState.traceRight (MState.pure ψ)).M.mat = coefMat ψ * (coefMat ψ)ᴴ := by
    rw [MState.mat_M, traceRight_pure_m]
  rw [← e, h]
  ext i
  simp [Complex.real_smul]

lemma star_dotProduct_eigenvectorBasis (k l : d₁) :
    star ⇑((traceRight_isHermitian ψ).eigenvectorBasis k) ⬝ᵥ
      ⇑((traceRight_isHermitian ψ).eigenvectorBasis l) = if k = l then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (traceRight_isHermitian ψ).eigenvectorBasis.orthonormal k l
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h

lemma mulVec_star_dotProduct (k l : d₁) :
    star ((coefMat ψ)ᴴ *ᵥ ⇑((traceRight_isHermitian ψ).eigenvectorBasis k)) ⬝ᵥ
      ((coefMat ψ)ᴴ *ᵥ ⇑((traceRight_isHermitian ψ).eigenvectorBasis l)) =
      if k = l then ((traceRight_isHermitian ψ).eigenvalues k : ℂ) else 0 := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_eigenvectorBasis_rho, dotProduct_smul, star_dotProduct_eigenvectorBasis]
  split_ifs with h
  · rw [h, smul_eq_mul, mul_one]
  · rw [smul_zero]

/-- `⟨c_k, c_l⟩ = λ_k δ_kl`. -/
lemma schmidtPartner_inner (k l : d₁) :
    star (schmidtPartner ψ k) ⬝ᵥ schmidtPartner ψ l =
      if k = l then ((traceRight_isHermitian ψ).eigenvalues k : ℂ) else 0 := by
  have h2 : star (schmidtPartner ψ k) ⬝ᵥ schmidtPartner ψ l =
      star (star ((coefMat ψ)ᴴ *ᵥ ⇑((traceRight_isHermitian ψ).eigenvectorBasis k)) ⬝ᵥ
        ((coefMat ψ)ᴴ *ᵥ ⇑((traceRight_isHermitian ψ).eigenvectorBasis l))) := by
    unfold schmidtPartner
    rw [star_star, dotProduct, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.star_apply, Pi.star_apply, star_mul', star_star, mul_comm]
  rw [h2, mulVec_star_dotProduct]
  split_ifs
  · exact Complex.conj_ofReal _
  · exact star_zero _

/-- Completeness of the eigenbasis: `Σ_k u_k(a) conj(u_k(a')) = δ_aa'`. -/
lemma sum_eigenvectorBasis_mul_star (a a' : d₁) :
    ∑ k, ((traceRight_isHermitian ψ).eigenvectorBasis k) a *
      star (((traceRight_isHermitian ψ).eigenvectorBasis k) a') = if a = a' then 1 else 0 := by
  have h := congrFun (congrFun
    (mem_unitaryGroup_iff.mp (traceRight_isHermitian ψ).eigenvectorUnitary.2) a) a'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa [Matrix.star_apply] using h

/-- `ψ(a, b) = Σ_k u_k(a) c_k(b)`. -/
lemma coef_eq_sum (a : d₁) (b : d₂) :
    ψ (a, b) = ∑ k, ((traceRight_isHermitian ψ).eigenvectorBasis k) a * schmidtPartner ψ k b := by
  simp only [schmidtPartner, Pi.star_apply, mulVec, dotProduct, conjTranspose_apply, star_sum,
    star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ a', ∑ k, ((traceRight_isHermitian ψ).eigenvectorBasis k) a *
      (coefMat ψ a' b * star (((traceRight_isHermitian ψ).eigenvectorBasis k) a')) =
      coefMat ψ a' b * if a = a' then 1 else 0 := by
    intro a'
    rw [← sum_eigenvectorBasis_mul_star ψ a a', Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-- **The Schmidt decomposition.** A unit vector `ψ ∈ ℂ^{d₁} ⊗ ℂ^{d₂}` is
`ψ = Σ_k √λ_k u_k ⊗ v_k`, where `u_k` is an orthonormal eigenbasis of `ρ₁ = tr₂ |ψ⟩⟨ψ|` with
eigenvalues `λ_k ≥ 0`, `Σ_k λ_k = 1`, the `v_k` with `λ_k > 0` are orthonormal and the others
vanish. -/
theorem schmidt :
    ∃ (lam : d₁ → ℝ) (u : OrthonormalBasis d₁ ℂ (EuclideanSpace ℂ d₁)) (v : d₁ → d₂ → ℂ),
      (∀ k, (MState.traceRight (MState.pure ψ)).m *ᵥ ⇑(u k) = (lam k : ℂ) • ⇑(u k)) ∧
      (∀ k, 0 ≤ lam k) ∧ ∑ k, lam k = 1 ∧
      (∀ k l, star (v k) ⬝ᵥ v l = if k = l ∧ 0 < lam k then 1 else 0) ∧
      (∀ k, lam k = 0 → v k = 0) ∧
      ∀ a b, ψ (a, b) = ∑ k, (Real.sqrt (lam k) : ℂ) * (u k) a * v k b := by
  set hρ := traceRight_isHermitian ψ
  set lam := hρ.eigenvalues
  set c := schmidtPartner ψ
  have hlam0 : ∀ k, 0 ≤ lam k := fun k =>
    (MState.traceRight (MState.pure ψ)).psd.eigenvalues_nonneg k
  have hc0 : ∀ k, lam k = 0 → c k = 0 := by
    intro k hk
    have := schmidtPartner_inner ψ k k
    rw [ite_eq_left rfl] at this
    exact dotProduct_star_self_eq_zero.mp (by rw [this]; exact_mod_cast hk)
  refine ⟨lam, hρ.eigenvectorBasis, fun k => ((Real.sqrt (lam k) : ℂ))⁻¹ • c k, ?_, hlam0, ?_, ?_,
    ?_, ?_⟩
  · intro k
    have h := hρ.mulVec_eigenvectorBasis k
    change (MState.traceRight (MState.pure ψ)).M.mat *ᵥ _ = _
    rw [h]
    ext i
    simp [Complex.real_smul, lam]
  · have h := hρ.sum_eigenvalues_eq_trace
    have h2 : ((∑ i, hρ.eigenvalues i : ℝ) : ℂ) = 1 := h.trans (MState.tr' _)
    exact_mod_cast h2
  · intro k l
    rw [star_smul, dotProduct_smul, smul_dotProduct, schmidtPartner_inner]
    by_cases hkl : k = l
    · subst hkl
      by_cases hk : 0 < lam k
      · rw [ite_eq_left rfl, ite_eq_left ⟨rfl, hk⟩]
        have hs : (Real.sqrt (lam k) : ℂ) ≠ 0 := by
          exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
        have hsq : ((Real.sqrt (lam k) : ℂ)) * (Real.sqrt (lam k) : ℂ) = (lam k : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam0 k)]
        rw [smul_eq_mul, smul_eq_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal, ← hsq]
        field_simp
      · have h0 : lam k = 0 := le_antisymm (not_lt.mp hk) (hlam0 k)
        rw [ite_eq_right (show ¬(k = k ∧ 0 < lam k) from fun h => hk h.2)]
        simp [h0]
    · rw [ite_eq_right hkl, ite_eq_right (fun h => hkl h.1)]
      simp
  · intro k hk
    simp only [hk, Real.sqrt_zero, Complex.ofReal_zero, _root_.inv_zero, zero_smul]
  · intro a b
    rw [coef_eq_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = _ * _ * ((Real.sqrt (lam k) : ℂ)⁻¹ • c k) b
    by_cases hk : lam k = 0
    · have h0 := hc0 k hk
      simp only [c] at h0
      rw [h0, hk]; simp
    · have hs : (Real.sqrt (lam k) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (lt_of_le_of_ne (hlam0 k) (Ne.symm hk))).ne'
      simp only [Pi.smul_apply, smul_eq_mul, c]
      field_simp

end Schmidt

/-! ### Product states -/

/-- **Product states**: `ψ` is a product if and only if its reduced density matrix `ρ₁` is pure. -/
theorem isProd_iff_traceRight_pure (ψ : Ket (d₁ × d₂)) :
    ψ.IsProd ↔ ∃ ξ, MState.traceRight (MState.pure ψ) = MState.pure ξ := by
  constructor
  · rintro ⟨ξ, φ, rfl⟩
    refine ⟨ξ, MState.ext_m ?_⟩
    rw [traceRight_pure_m]
    ext a a'
    have hφ : ∑ b, φ b * conj (φ b) = 1 := by
      have h := φ.normalized
      simp_rw [Complex.mul_conj]
      exact_mod_cast h
    simp only [Matrix.mul_apply, conjTranspose_apply, coefMat, MState.pure_apply, RCLike.star_def]
    have e : ∀ b, (ξ ⊗ᵠ φ) (a, b) * conj ((ξ ⊗ᵠ φ) (a', b)) =
        ξ a * conj (ξ a') * (φ b * conj (φ b)) := by
      intro b
      simp only [Ket.prod, Ket.apply, map_mul]
      ring
    simp_rw [e, ← Finset.mul_sum, hφ, mul_one]
  · rintro ⟨ξ, hξ⟩
    set M := coefMat ψ
    set P := (MState.pure ξ).m
    have hP : M * Mᴴ = P := by rw [← traceRight_pure_m, hξ]
    have hPP : P * P = P := MState.pure_mul_self ξ
    have hPH : Pᴴ = P := (MState.pure ξ).Hermitian
    have hA : ((1 - P) * M) * ((1 - P) * M)ᴴ = 0 := by
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc M, hP, ← Matrix.mul_assoc,
        Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, Matrix.zero_mul]
    have hM : M = P * M := by
      have h0 := self_mul_conjTranspose_eq_zero.mp hA
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
      exact h0
    have hfac : ∀ a b, ψ (a, b) = ξ a * ∑ a', conj (ξ a') * ψ (a', b) := by
      intro a b
      have := congrFun (congrFun hM a) b
      simp only [Matrix.mul_apply, P, MState.pure_apply, M, coefMat] at this
      rw [Finset.mul_sum]
      convert this using 2 with a' _
      ring
    rw [Ket.IsProd_iff_mul_eq_mul]
    intro i₁ i₂ j₁ j₂
    rw [hfac i₁ j₁, hfac i₂ j₂, hfac i₁ j₂, hfac i₂ j₁]
    ring

/-- **Schmidt rank one**: `ρ₁` is pure if and only if exactly one Schmidt weight is nonzero. -/
theorem traceRight_pure_iff_rank_one (ψ : Ket (d₁ × d₂)) :
    (∃ ξ, MState.traceRight (MState.pure ψ) = MState.pure ξ) ↔
      (Finset.univ.filter fun k => (traceRight_isHermitian ψ).eigenvalues k ≠ 0).card = 1 := by
  set ρ := MState.traceRight (MState.pure ψ)
  have hspec : ∀ k, ((ρ.spectrum k : Prob) : ℝ) = (traceRight_isHermitian ψ).eigenvalues k :=
    fun k => rfl
  have hsum : ∑ k, (traceRight_isHermitian ψ).eigenvalues k = 1 := by
    simpa [hspec] using ρ.spectrum.normalized
  have hnn : ∀ k, 0 ≤ (traceRight_isHermitian ψ).eigenvalues k := fun k => by
    rw [← hspec]; exact (ρ.spectrum k).2.1
  rw [MState.pure_iff_constant_spectrum, Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, Finset.ext fun k => ?_⟩
    have h1 : (traceRight_isHermitian ψ).eigenvalues k = if i = k then 1 else 0 := by
      have := congrArg (fun p : ProbDistribution d₁ => ((p k : Prob) : ℝ)) hi
      rw [← hspec]
      simpa [ProbDistribution.constant, apply_ite] using this
    rw [Finset.mem_filter, Finset.mem_singleton, h1]
    by_cases h : k = i
    · subst h; simp
    · simp [Ne.symm h, h]
  · rintro ⟨i, hi⟩
    have hk : ∀ k, k ≠ i → (traceRight_isHermitian ψ).eigenvalues k = 0 := by
      intro k hk
      by_contra h
      have : k ∈ Finset.univ.filter fun k => (traceRight_isHermitian ψ).eigenvalues k ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hi, Finset.mem_singleton] at this
      exact hk this
    have hi1 : (traceRight_isHermitian ψ).eigenvalues i = 1 := by
      rw [← hsum, Finset.sum_eq_single i (fun k _ h => hk k h) (by simp)]
    refine ⟨i, ProbDistribution.ext fun k => Subtype.ext ?_⟩
    change (traceRight_isHermitian ψ).eigenvalues k = _
    by_cases h : k = i
    · subst h
      simp only [MState.traceRight_M, HermitianMat.traceRight_mat, MState.mat_M,
        ProbDistribution.constant_eq, ↓reduceIte, Set.Icc.coe_one]
      exact hi1
    · rw [hk k h]; simp [ProbDistribution.constant, Ne.symm h]

end QM
