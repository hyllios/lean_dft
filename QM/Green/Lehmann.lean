/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import QM.ManyBody.RDM

/-!
# The Lehmann representation

Let `H` be a Hermitian operator on the Fock space `Fock M` (a matrix indexed by configurations),
`U(t) = e^{-iHt}` its time evolution and `c_i(t) = e^{iHt} c_i e^{-iHt}`. For an eigenstate `Ψ`
of `H` with energy `E₀` the retarded Green's function is
`G^R_ij(t) = -i θ(t) ⟨Ψ, {c_i(t), c_j†} Ψ⟩`, and its Fourier–Laplace transform is
`G_ij(z) = ∫_0^∞ e^{izt} G^R_ij(t) dt` for `Im z > 0`.

Expanding in an orthonormal eigenbasis `φ_n` of `H` (energies `E_n`) gives the **Lehmann
representation**
`G_ij(z) = Σ_n ⟨Ψ|c_i|φ_n⟩⟨φ_n|c_j†|Ψ⟩ / (z - (E_n - E₀))`
  `+ Σ_m ⟨Ψ|c_j†|φ_m⟩⟨φ_m|c_i|Ψ⟩ / (z + (E_m - E₀))`.
The numerators are positive semidefinite rank-one matrices in `(i, j)`, and by the CAR they add up
to the identity for a normalized `Ψ`.

## Main definitions

* `evol H t = e^{-iHt}` (the exponential of a bounded operator).
* `greenRet H Ψ i j t`: the retarded Green's function in the state `Ψ`.
* `greenZ H Ψ i j z`: its Fourier–Laplace transform.
* `lehmannPole`, `lehmannWeight`: the poles `E_n - E₀`, `E₀ - E_m` and the weight matrices.

## Main results

* `evol_apply_of_eigen`: `e^{-iHt} φ = e^{-iEt} φ` for an eigenvector.
* `greenRet_eq_sum`: the Lehmann representation in time.
* `greenZ_eq_sum` (**Lehmann representation**): `G(z) = Σ_k W_k / (z - ω_k)` for `Im z > 0`.
* `lehmannWeight_posSemidef`, `sum_lehmannWeight`: the weights are positive semidefinite and add up
  to the identity.
-/

namespace QM.Green

open Matrix Complex QM.ManyBody MeasureTheory
open scoped ComplexOrder

variable {M : ℕ}

/-! ### Time evolution -/

/-- The time evolution `U(t) = e^{-iHt}`. -/
noncomputable def evol (H : FockOp M) (t : ℝ) : Fock M →L[ℂ] Fock M :=
  NormedSpace.exp ((-(t : ℂ) * I) • toFockCLM H)

/-- The Heisenberg picture `A(t) = e^{iHt} A e^{-iHt}`. -/
noncomputable def heis (H : FockOp M) (t : ℝ) (A : Fock M →L[ℂ] Fock M) : Fock M →L[ℂ] Fock M :=
  evol H (-t) * A * evol H t

/-- The exponential of `c A` on an eigenvector of `A`. -/
lemma exp_smul_apply_of_eigen {A : Fock M →L[ℂ] Fock M} {φ : Fock M} {E : ℂ} (h : A φ = E • φ)
    (c : ℂ) : NormedSpace.exp (c • A) φ = Complex.exp (c * E) • φ := by
  have hpow : ∀ n : ℕ, ((c • A) ^ n) φ = (c * E) ^ n • φ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, show ((c • A) ^ n * (c • A)) φ = ((c • A) ^ n) ((c • A) φ) from rfl,
        _root_.smul_apply, h, smul_smul, map_smul, ih, smul_smul, pow_succ]
      ring_nf
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • A)).mapL
    (ContinuousLinearMap.apply ℂ (Fock M) φ)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c * E)).smul_const φ
  rw [← Complex.exp_eq_exp_ℂ] at h2
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp [hpow, smul_smul]

lemma toFockCLM_isSelfAdjoint {H : FockOp M} (hH : H.IsHermitian) :
    IsSelfAdjoint (toFockCLM H) := by
  rw [IsSelfAdjoint, ← map_star]
  exact congrArg toFockCLM hH

/-- `U(t)† = U(-t)`. -/
lemma star_evol {H : FockOp M} (hH : H.IsHermitian) (t : ℝ) : star (evol H t) = evol H (-t) := by
  rw [evol, evol, NormedSpace.star_exp, star_smul, (toFockCLM_isSelfAdjoint hH).star_eq]
  congr 2
  simp [Complex.conj_ofReal]

/-- **Time evolution of an eigenvector**: `e^{-iHt} φ = e^{-iEt} φ`. -/
theorem evol_apply_of_eigen {H : FockOp M} {φ : Fock M} {E : ℝ} (h : toFockCLM H φ = (E : ℂ) • φ)
    (t : ℝ) : evol H t φ = Complex.exp (-(t : ℂ) * I * E) • φ :=
  exp_smul_apply_of_eigen h _

/-- An eigenvector as a bra: `⟨Ψ| e^{-iHs} = e^{-iE₀s} ⟨Ψ|`. -/
lemma inner_evol_of_eigen {H : FockOp M} (hH : H.IsHermitian) {Ψ : Fock M} {E₀ : ℝ}
    (hΨ : toFockCLM H Ψ = (E₀ : ℂ) • Ψ) (s : ℝ) (w : Fock M) :
    inner ℂ Ψ (evol H s w) = Complex.exp (-(s : ℂ) * I * E₀) * inner ℂ Ψ w := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    star_evol hH, evol_apply_of_eigen hΨ, inner_smul_left, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_ofReal]

/-! ### The eigenbasis of `H` -/

/-- The eigenvectors of `H` are eigenvectors of the operator on the Fock space. -/
lemma toFockCLM_eigenvectorBasis {H : FockOp M} (hH : H.IsHermitian) (n : Finset (Fin M)) :
    toFockCLM H (hH.eigenvectorBasis n) = ((hH.eigenvalues n : ℝ) : ℂ) • hH.eigenvectorBasis n := by
  have h := hH.mulVec_eigenvectorBasis n
  change toFockCLM H (WithLp.toLp 2 (WithLp.ofLp (hH.eigenvectorBasis n))) = _
  rw [toEuclideanCLM_toLp, h]
  rfl

/-- `⟨a, e^{-iHs} b⟩ = Σ_n ⟨a, φ_n⟩ ⟨φ_n, b⟩ e^{-iE_n s}`. -/
lemma inner_evol_eq_sum {H : FockOp M} (hH : H.IsHermitian) (s : ℝ) (a b : Fock M) :
    inner ℂ a (evol H s b) = ∑ n, inner ℂ a (hH.eigenvectorBasis n) *
      inner ℂ (hH.eigenvectorBasis n) b * Complex.exp (-(s : ℂ) * I * hH.eigenvalues n) := by
  conv_lhs => rw [← hH.eigenvectorBasis.sum_repr' b]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, evol_apply_of_eigen (toFockCLM_eigenvectorBasis hH n), smul_smul,
    inner_smul_right]
  ring

/-! ### The retarded Green's function -/

/-- The retarded Green's function `G^R_ij(t) = -i θ(t) ⟨Ψ, {c_i(t), c_j†} Ψ⟩` in the state `Ψ`. -/
noncomputable def greenRet (H : FockOp M) (Ψ : Fock M) (i j : Fin M) (t : ℝ) : ℂ :=
  if 0 < t then
    -I * inner ℂ Ψ ((heis H t (annOp i) * creOp j + creOp j * heis H t (annOp i)) Ψ)
  else 0

/-- The Fourier–Laplace transform `G_ij(z) = ∫_0^∞ e^{izt} G^R_ij(t) dt`. -/
noncomputable def greenZ (H : FockOp M) (Ψ : Fock M) (i j : Fin M) (z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), Complex.exp (I * z * t) * greenRet H Ψ i j t

/-- The poles of the Lehmann representation: `E_n - E₀` (particle) and `E₀ - E_m` (hole). -/
noncomputable def lehmannPole {H : FockOp M} (hH : H.IsHermitian) (E₀ : ℝ) :
    Finset (Fin M) ⊕ Finset (Fin M) → ℝ
  | .inl n => hH.eigenvalues n - E₀
  | .inr m => E₀ - hH.eigenvalues m

/-- The weights of the Lehmann representation: `⟨Ψ|c_i|φ_n⟩⟨φ_n|c_j†|Ψ⟩` (particle) and
`⟨Ψ|c_j†|φ_m⟩⟨φ_m|c_i|Ψ⟩` (hole). -/
noncomputable def lehmannWeight {H : FockOp M} (hH : H.IsHermitian) (Ψ : Fock M) :
    Finset (Fin M) ⊕ Finset (Fin M) → Matrix (Fin M) (Fin M) ℂ
  | .inl n => fun i j => inner ℂ Ψ (annOp i (hH.eigenvectorBasis n)) *
      inner ℂ (hH.eigenvectorBasis n) (creOp j Ψ)
  | .inr m => fun i j => inner ℂ Ψ (creOp j (hH.eigenvectorBasis m)) *
      inner ℂ (hH.eigenvectorBasis m) (annOp i Ψ)

/-- **The Lehmann representation in time**:
`G^R_ij(t) = -i Σ_k W_k,ij e^{-iω_k t}` for `t > 0`. -/
theorem greenRet_eq_sum {H : FockOp M} (hH : H.IsHermitian) {Ψ : Fock M} {E₀ : ℝ}
    (hΨ : toFockCLM H Ψ = (E₀ : ℂ) • Ψ) (i j : Fin M) {t : ℝ} (ht : 0 < t) :
    greenRet H Ψ i j t = -I * ∑ k, lehmannWeight hH Ψ k i j *
      Complex.exp (-I * (lehmannPole hH E₀ k : ℂ) * t) := by
  have hT1 : inner ℂ Ψ (evol H (-t) (annOp i (evol H t (creOp j Ψ)))) =
      ∑ n, lehmannWeight hH Ψ (.inl n) i j *
        Complex.exp (-I * (lehmannPole hH E₀ (.inl n) : ℂ) * t) := by
    rw [inner_evol_of_eigen hH hΨ, inner_annOp, inner_evol_eq_sum hH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [lehmannWeight, lehmannPole]
    rw [← inner_annOp]
    have : Complex.exp (-(-(t : ℝ) : ℂ) * I * E₀) * Complex.exp (-(t : ℂ) * I * hH.eigenvalues n) =
        Complex.exp (-I * ((hH.eigenvalues n - E₀ : ℝ) : ℂ) * t) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [← this]; push_cast; ring_nf
  have hT2 : inner ℂ Ψ (creOp j (evol H (-t) (annOp i (evol H t Ψ)))) =
      ∑ m, lehmannWeight hH Ψ (.inr m) i j *
        Complex.exp (-I * (lehmannPole hH E₀ (.inr m) : ℂ) * t) := by
    rw [inner_creOp, evol_apply_of_eigen hΨ, map_smul, inner_evol_eq_sum hH, Finset.sum_congr rfl]
    intro m _
    simp only [lehmannWeight, lehmannPole]
    rw [inner_smul_right, ← inner_creOp]
    have : Complex.exp (-(-(t : ℝ) : ℂ) * I * hH.eigenvalues m) * Complex.exp (-(t : ℂ) * I * E₀) =
        Complex.exp (-I * ((E₀ - hH.eigenvalues m : ℝ) : ℂ) * t) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [← this]; push_cast; ring_nf
  rw [greenRet, ite_eq_left ht, Fintype.sum_sum_type, ← hT1, ← hT2, ← inner_add_right]
  simp only [heis, _root_.add_apply, mul_apply_eq_comp]

/-- **The Lehmann representation**: for `Im z > 0`,
`G_ij(z) = Σ_n ⟨Ψ|c_i|φ_n⟩⟨φ_n|c_j†|Ψ⟩ / (z - (E_n - E₀))`
  `+ Σ_m ⟨Ψ|c_j†|φ_m⟩⟨φ_m|c_i|Ψ⟩ / (z + (E_m - E₀))`. -/
theorem greenZ_eq_sum {H : FockOp M} (hH : H.IsHermitian) {Ψ : Fock M} {E₀ : ℝ}
    (hΨ : toFockCLM H Ψ = (E₀ : ℂ) • Ψ) (i j : Fin M) {z : ℂ} (hz : 0 < z.im) :
    greenZ H Ψ i j z = ∑ k, lehmannWeight hH Ψ k i j / (z - lehmannPole hH E₀ k) := by
  have hre : ∀ k, (I * (z - lehmannPole hH E₀ k)).re < 0 := by
    intro k; simp [Complex.mul_re]; linarith
  have hne : ∀ k, I * (z - lehmannPole hH E₀ k) ≠ 0 := by
    intro k h; have := hre k; rw [h] at this; simp at this
  have heq : Set.EqOn (fun t : ℝ => Complex.exp (I * z * t) * greenRet H Ψ i j t)
      (fun t : ℝ => ∑ k, (-I * lehmannWeight hH Ψ k i j) *
        Complex.exp (I * (z - lehmannPole hH E₀ k) * t)) (Set.Ioi 0) := by
    intro t ht
    simp only
    rw [greenRet_eq_sum hH hΨ i j ht, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Complex.exp (I * z * t) * Complex.exp (-I * (lehmannPole hH E₀ k : ℂ) * t) =
        Complex.exp (I * (z - lehmannPole hH E₀ k) * t) := by
      rw [← Complex.exp_add]; ring_nf
    rw [← this]; ring
  rw [greenZ, setIntegral_congr_fun measurableSet_Ioi heq, integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hre k), Complex.ofReal_zero, mul_zero,
      Complex.exp_zero]
    have hz' : z - lehmannPole hH E₀ k ≠ 0 := fun h => hne k (by rw [h, mul_zero])
    field_simp
  · intro k _
    exact (integrableOn_exp_mul_complex_Ioi (hre k) 0).const_mul _

/-! ### The spectral weights -/

/-- **The Lehmann weights are positive semidefinite** (rank one). -/
theorem lehmannWeight_posSemidef {H : FockOp M} (hH : H.IsHermitian) (Ψ : Fock M)
    (k : Finset (Fin M) ⊕ Finset (Fin M)) : (lehmannWeight hH Ψ k).PosSemidef := by
  rcases k with n | m
  · have h : lehmannWeight hH Ψ (.inl n) = vecMulVec
        (fun i => inner ℂ Ψ (annOp i (hH.eigenvectorBasis n)))
        (star fun i => inner ℂ Ψ (annOp i (hH.eigenvectorBasis n))) := by
      ext i j
      simp only [lehmannWeight, vecMulVec_apply, Pi.star_apply]
      rw [inner_creOp, ← inner_conj_symm (annOp j _) Ψ]
      rfl
    rw [h]; exact posSemidef_vecMulVec_self_star _
  · have h : lehmannWeight hH Ψ (.inr m) = vecMulVec
        (fun i => inner ℂ (hH.eigenvectorBasis m) (annOp i Ψ))
        (star fun i => inner ℂ (hH.eigenvectorBasis m) (annOp i Ψ)) := by
      ext i j
      simp only [lehmannWeight, vecMulVec_apply, Pi.star_apply]
      rw [mul_comm, inner_creOp, ← inner_conj_symm (annOp j Ψ) _]
      rfl
    rw [h]; exact posSemidef_vecMulVec_self_star _

/-- **Sum rule**: for a normalized state the Lehmann weights add up to the identity
(`{c_i, c_j†} = δ_ij`). -/
theorem sum_lehmannWeight {H : FockOp M} (hH : H.IsHermitian) {Ψ : Fock M} (hΨ : ‖Ψ‖ = 1) :
    ∑ k, lehmannWeight hH Ψ k = 1 := by
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_sum_type]
  simp only [lehmannWeight]
  have h1 : ∑ n, inner ℂ Ψ (annOp i (hH.eigenvectorBasis n)) *
      inner ℂ (hH.eigenvectorBasis n) (creOp j Ψ) = inner ℂ Ψ (annOp i (creOp j Ψ)) := by
    simp_rw [inner_annOp]
    exact hH.eigenvectorBasis.sum_inner_mul_inner _ _
  have h2 : ∑ m, inner ℂ Ψ (creOp j (hH.eigenvectorBasis m)) *
      inner ℂ (hH.eigenvectorBasis m) (annOp i Ψ) = inner ℂ Ψ (creOp j (annOp i Ψ)) := by
    simp_rw [inner_creOp]
    exact hH.eigenvectorBasis.sum_inner_mul_inner _ _
  rw [h1, h2, ← inner_add_right]
  have h := congrArg (fun T : Fock M →L[ℂ] Fock M => T Ψ) (annOp_mul_creOp_add i j)
  simp only [_root_.add_apply, mul_apply_eq_comp] at h
  rw [h, Matrix.one_apply]
  split_ifs
  · rw [_root_.one_apply_eq_self, inner_self_eq_norm_sq_to_K, hΨ]; simp
  · simp

end QM.Green
