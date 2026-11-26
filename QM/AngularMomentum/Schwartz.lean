/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Physlib.Mathematics.InnerProductSpace.Gaussian
import Physlib.QuantumMechanics.Operators.AngularMomentum.DimThree
import QM.AngularMomentum.Orbital

/-!
# Orbital angular momentum on Schwartz functions

The bridge between the orbital angular momentum `L = -i r × ∇` on polynomials
(`QM/AngularMomentum/Orbital`) and Physlib's angular momentum operators `𝐋ᵢⱼ = 𝐱ᵢ𝐩ⱼ - 𝐱ⱼ𝐩ᵢ` on
the Schwartz space `𝓢(Space 3, ℂ)`. A polynomial `p` is sent to `p(x) e^{-|x|²/2}`
(`gaussPoly`). Since `∂ⱼ e^{-|x|²/2} = -xⱼ e^{-|x|²/2}` and `xᵢxⱼ - xⱼxᵢ = 0`, Physlib's
operators act on `p(x) e^{-|x|²/2}` as `ℏ L` acts on `p`. Hence the image of the harmonic
polynomials of degree `l` is a `(2l + 1)`-dimensional space of Schwartz functions carrying the
spin-`l` representation of Physlib's `𝐋⁺, 𝐋⁻, 𝐋_z`, with `𝐋² = ℏ² l(l + 1)`.

## Main definitions

* `gaussPoly`: `p ↦ p(x) e^{-|x|²/2}`, from polynomials to Schwartz functions.
* `schwartzHarmonic l`: the image of the harmonic polynomials of degree `l`.

## Main results

* `gaussPoly_apply`, `gaussPoly_injective`.
* `angularMomentum_gaussPoly_x`, `_y`, `_z`, `raising_gaussPoly`, `lowering_gaussPoly`:
  Physlib's operators on `p e^{-|x|²/2}` are `ℏ` times `Lx, Ly, Lz, L₊, L₋` on `p`.
* `angularMomentumSqr_gaussPoly`: `𝐋² = ℏ² l(l + 1)` on `schwartzHarmonic l`.
* `finrank_schwartzHarmonic`, `schwartzHarmonic_spinRep_iso`: it is the spin-`l` representation.
* `exists_L2_Lz_eigen`: for every `l ∈ ℕ` and integer `|m| ≤ l` there is a nonzero Schwartz
  function with `𝐋² ψ = ℏ² l(l + 1) ψ` and `𝐋_z ψ = ℏ m ψ`.
-/

namespace QM.AngularMomentum

open MvPolynomial Complex QuantumMechanics SchwartzMap Module Constants

/-- The Gaussian `e^{-|x|²/2}` as a Schwartz function on `Space 3`. -/
noncomputable def gauss : 𝓢(Space 3, ℂ) := InnerProductSpace.stdGaussian (Space 3) ℂ

lemma gauss_apply (x : Space 3) : gauss x = ((Real.exp (-2⁻¹ * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  simp [gauss]

lemma gauss_ne_zero (x : Space 3) : gauss x ≠ 0 := by
  rw [gauss_apply]; exact_mod_cast (Real.exp_pos _).ne'

/-- `∂ⱼ e^{-|x|²/2} = -xⱼ e^{-|x|²/2}`, that is `𝐩ⱼ G = iℏ 𝐱ⱼ G`. -/
lemma momentum_gauss (j : Fin 3) : 𝐩 j gauss = (I * ℏ) • 𝐱 j gauss := by
  ext x
  have h1 : HasFDerivAt (fun y : Space 3 => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := ((h1.const_mul (-2⁻¹)).exp)
  have h3 := (Complex.ofRealCLM.hasFDerivAt (x := Real.exp (-2⁻¹ * ‖x‖ ^ 2))).comp x h2
  have hfun : (gauss : Space 3 → ℂ) =
      (Complex.ofRealCLM ∘ fun y : Space 3 => Real.exp (-2⁻¹ * ‖y‖ ^ 2)) := by
    funext y; simp [gauss_apply]
  rw [momentumCLM_apply, Space.deriv_eq, hfun, h3.fderiv]
  simp [gauss_apply, Space.inner_basis]
  ring

/-! ### Monomials times the Gaussian -/

/-- Powers of a position operator act pointwise. -/
lemma position_pow_apply (i : Fin 3) (a : ℕ) (ψ : 𝓢(Space 3, ℂ)) (x : Space 3) :
    ((𝐱 i) ^ a) ψ x = ((x i : ℂ)) ^ a * ψ x := by
  induction a generalizing ψ with
  | zero => simp
  | succ a ih => rw [pow_succ, mul_apply_eq_comp, ih, positionCLM_apply]; ring

lemma position_commute (i j : Fin 3) : Commute (𝐱 i : 𝓢(Space 3, ℂ) →L[ℂ] _) (𝐱 j) := by
  have h := position_commutation_position (d := 3) i j
  rw [Ring.lie_def, sub_eq_zero] at h
  exact h

/-- `x^a y^b z^c e^{-|x|²/2}`. -/
noncomputable def monoG (m : Fin 3 →₀ ℕ) : 𝓢(Space 3, ℂ) :=
  ((𝐱 0 ^ m 0 * 𝐱 1 ^ m 1 * 𝐱 2 ^ m 2 : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ))) gauss

lemma monoG_apply (m : Fin 3 →₀ ℕ) (x : Space 3) :
    monoG m x = (x 0 : ℂ) ^ (m 0) * (x 1 : ℂ) ^ (m 1) * (x 2 : ℂ) ^ (m 2) * gauss x := by
  simp only [monoG, mul_apply_eq_comp, position_pow_apply]
  ring

lemma monoG_add_single (m : Fin 3 →₀ ℕ) (k : Fin 3) :
    monoG (m + Finsupp.single k 1) = 𝐱 k (monoG m) := by
  simp only [monoG, ← mul_apply_eq_comp]
  congr 1
  have c01 := position_commute 0 1
  have c02 := position_commute 0 2
  have c12 := position_commute 1 2
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Finsupp.add_apply,
    Finsupp.single_eq_same, Finsupp.single_apply, Fin.reduceEq, ite_false, add_zero, pow_succ']
  · simp only [mul_assoc]
  · rw [← mul_assoc (𝐱 0 ^ m 0), ← (c01.symm.pow_right (m 0)).eq]; simp only [mul_assoc]
  · have h : Commute (𝐱 2) (𝐱 0 ^ m 0 * 𝐱 1 ^ m 1) :=
      (c02.symm.pow_right _).mul_right (c12.symm.pow_right _)
    rw [← mul_assoc (𝐱 0 ^ m 0 * 𝐱 1 ^ m 1), ← h.eq]; simp only [mul_assoc]

/-! ### Polynomials times the Gaussian -/

/-- **`p ↦ p(x) e^{-|x|²/2}`**, from polynomials to Schwartz functions. -/
noncomputable def gaussPoly : Poly3 →ₗ[ℂ] 𝓢(Space 3, ℂ) :=
  (basisMonomials (Fin 3) ℂ).constr ℂ monoG

lemma gaussPoly_monomial (m : Fin 3 →₀ ℕ) (c : ℂ) : gaussPoly (monomial m c) = c • monoG m := by
  rw [show monomial m c = c • monomial m (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, gaussPoly, show monomial m (1 : ℂ) = basisMonomials (Fin 3) ℂ m by
      rw [coe_basisMonomials], Basis.constr_basis]

lemma gaussPoly_C (c : ℂ) : gaussPoly (C c) = c • gauss := by
  rw [← monomial_zero', gaussPoly_monomial]; simp [monoG]

lemma gaussPoly_X_mul (k : Fin 3) (p : Poly3) : gaussPoly (X k * p) = 𝐱 k (gaussPoly p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [X, monomial_mul_monomial, one_mul, gaussPoly_monomial, gaussPoly_monomial, map_smul,
      add_comm, monoG_add_single]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, map_add]

/-- **`gaussPoly p x = p(x) e^{-|x|²/2}`.** -/
theorem gaussPoly_apply (p : Poly3) (x : Space 3) :
    gaussPoly p x = eval (fun i => (x i : ℂ)) p * gauss x := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [gaussPoly_monomial, smul_apply, monoG_apply, eval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three, smul_eq_mul]
    ring
  | add p q hp hq => rw [map_add, add_apply, hp, hq, map_add, add_mul]

/-- **`p ↦ p(x) e^{-|x|²/2}` is injective**: a complex polynomial vanishing on `ℝ³` is zero. -/
theorem gaussPoly_injective : Function.Injective gaussPoly := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  have hev : ∀ x : Space 3, eval (fun i => (x i : ℂ)) p = 0 := fun x => by
    have := congrArg (fun ψ : 𝓢(Space 3, ℂ) => ψ x) hp
    simp only [gaussPoly_apply, zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_right (gauss_ne_zero x)
  refine (funext_set (p := p) (q := 0) (fun _ => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective ofReal_injective) fun y hy => ?_)
  choose r hr using fun i => hy i (Set.mem_univ i)
  have hy' : y = fun i => (((⟨r⟩ : Space 3) i : ℝ) : ℂ) := funext fun i => (hr i).symm
  rw [map_zero, hy']
  exact hev ⟨r⟩

/-- **`𝐩ⱼ (p G) = -iℏ (∂ⱼp) G + iℏ (xⱼ p) G`.** -/
theorem momentum_gaussPoly (j : Fin 3) (p : Poly3) :
    𝐩 j (gaussPoly p) = (-I * ℏ) • gaussPoly (pderiv j p) + (I * ℏ) • gaussPoly (X j * p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hX : gaussPoly (X j * C c) = c • 𝐱 j gauss := by
      rw [gaussPoly_X_mul, gaussPoly_C, map_smul]
    rw [gaussPoly_C, map_smul, momentum_gauss, hX, pderiv_C, map_zero, smul_zero, zero_add,
      smul_comm]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, smul_add]; abel
  | mul_X p k hp =>
    rw [mul_comm p (X k), gaussPoly_X_mul]
    have hc := congrArg (fun T : 𝓢(Space 3, ℂ) →L[ℂ] _ => T (gaussPoly p))
      (momentum_comp_position_eq (d := 3) k j)
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      smul_apply, ContinuousLinearMap.id_apply] at hc
    rw [hc, hp, map_add, map_smul, map_smul, ← gaussPoly_X_mul, ← gaussPoly_X_mul,
      Derivation.leibniz, pderiv_X]
    rcases eq_or_ne k j with rfl | hkj
    · simp only [Pi.single_eq_same, KroneckerDelta.eq_one_of_same, smul_eq_mul, one_smul,
        mul_one, map_add, smul_add]
      module
    · simp only [Pi.single_eq_of_ne hkj, KroneckerDelta.eq_zero_of_ne hkj, smul_zero,
        zero_smul, add_zero, sub_zero, smul_eq_mul, mul_zero]
      rw [mul_left_comm (X k) (X j) p]

/-! ### Angular momentum -/

/-- Physlib's `𝐋ᵢⱼ = 𝐱ᵢ𝐩ⱼ - 𝐱ⱼ𝐩ᵢ` on `p G` is `ℏ` times `-i(xᵢ∂ⱼ - xⱼ∂ᵢ)` on `p`. -/
theorem angularMomentum_gaussPoly (a b : Fin 3) (p : Poly3) :
    𝐋 a b (gaussPoly p) = (ℏ : ℂ) • gaussPoly (((-I) • (xd a b - xd b a)) p) := by
  rw [angularMomentumCLM_apply_fun, momentum_gaussPoly, momentum_gaussPoly]
  simp only [map_add, map_smul, ← gaussPoly_X_mul]
  rw [← mul_assoc, ← mul_assoc, mul_comm (X a) (X b)]
  simp only [smul_apply, FunLike.coe_sub, Pi.sub_apply, xd_apply, smul_sub,
    map_sub, map_smul]
  module

theorem angularMomentum_gaussPoly_x (p : Poly3) :
    angularMomentumOperator3D 0 (gaussPoly p) = (ℏ : ℂ) • gaussPoly (Lx p) :=
  angularMomentum_gaussPoly 1 2 p

theorem angularMomentum_gaussPoly_y (p : Poly3) :
    angularMomentumOperator3D 1 (gaussPoly p) = (ℏ : ℂ) • gaussPoly (Ly p) :=
  angularMomentum_gaussPoly 2 0 p

theorem angularMomentum_gaussPoly_z (p : Poly3) :
    angularMomentumOperator3D 2 (gaussPoly p) = (ℏ : ℂ) • gaussPoly (Lz p) :=
  angularMomentum_gaussPoly 0 1 p

theorem raising_gaussPoly (p : Poly3) :
    angularMomentumRaisingCLM (gaussPoly p) = (ℏ : ℂ) • gaussPoly (Lp p) := by
  rw [angularMomentumRaisingCLM, add_apply, smul_apply,
    angularMomentum_gaussPoly_x, angularMomentum_gaussPoly_y, Lp]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, map_add,
    map_smul, smul_add]
  rw [smul_comm]

theorem lowering_gaussPoly (p : Poly3) :
    angularMomentumLoweringCLM (gaussPoly p) = (ℏ : ℂ) • gaussPoly (Lm p) := by
  rw [angularMomentumLoweringCLM, sub_apply, smul_apply,
    angularMomentum_gaussPoly_x, angularMomentum_gaussPoly_y, Lm]
  simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, map_sub,
    map_smul, smul_sub]
  rw [smul_comm]

/-- **`𝐋² = ℏ² l(l + 1)` on `p e^{-|x|²/2}` for `p` harmonic of degree `l`.** -/
theorem angularMomentumSqr_gaussPoly {l : ℕ} {p : Poly3} (hp : p ∈ harmonic l) :
    angularMomentumOperatorSqr (d := 3) (gaussPoly p) =
      ((ℏ : ℂ) ^ 2 * ((l : ℂ) * (l + 1))) • gaussPoly p := by
  rw [angularMomentumOperatorSqr_eq_sum_dimThree, sum_apply,
    Fin.sum_univ_three]
  simp only [ContinuousLinearMap.comp_apply, angularMomentum_gaussPoly_x,
    angularMomentum_gaussPoly_y, angularMomentum_gaussPoly_z, map_smul, smul_smul, ← smul_add,
    ← map_add]
  have h := harmonic_L2 hp
  simp only [LinearMap.add_apply, mul_apply_eq_comp] at h
  rw [show (⇑Lx (Lx p) + Ly (Ly p) + Lz (Lz p) : Poly3) = ((l : ℂ) * (l + 1)) • p from h,
    map_smul, smul_smul, sq]

/-! ### The spin-`l` representation on Schwartz functions -/

/-- **The Schwartz functions `p(x) e^{-|x|²/2}` with `p` harmonic of degree `l`.** -/
noncomputable def schwartzHarmonic (l : ℕ) : Submodule ℂ 𝓢(Space 3, ℂ) :=
  (harmonic l).map gaussPoly

/-- `harmonic l ≃ schwartzHarmonic l`. -/
noncomputable def harmonicEquivSchwartz (l : ℕ) : harmonic l ≃ₗ[ℂ] schwartzHarmonic l :=
  Submodule.equivMapOfInjective gaussPoly gaussPoly_injective (harmonic l)

lemma harmonicEquivSchwartz_apply (l : ℕ) (p : harmonic l) :
    (harmonicEquivSchwartz l p : 𝓢(Space 3, ℂ)) = gaussPoly p := rfl

/-- **`dim schwartzHarmonic l = 2l + 1`.** -/
theorem finrank_schwartzHarmonic (l : ℕ) : finrank ℂ (schwartzHarmonic l) = 2 * l + 1 := by
  rw [← (harmonicEquivSchwartz l).finrank_eq, finrank_harmonic]

/-- **`schwartzHarmonic l` is the spin-`l` representation of Physlib's `𝐋⁺, 𝐋⁻, 𝐋_z`**: a linear
isomorphism `V_l = ℂ^{2l+1} ≃ schwartzHarmonic l` maps `ℏS₊, ℏS₋, ℏS_z` to `𝐋⁺, 𝐋⁻, 𝐋_z`. -/
theorem schwartzHarmonic_spinRep_iso (l : ℕ) :
    ∃ φ : (Fin (2 * l + 1) → ℂ) ≃ₗ[ℂ] schwartzHarmonic l, ∀ v,
      angularMomentumRaisingCLM (φ v : 𝓢(Space 3, ℂ)) = (ℏ : ℂ) • (φ (spinSp (2 * l) v)) ∧
      angularMomentumLoweringCLM (φ v : 𝓢(Space 3, ℂ)) = (ℏ : ℂ) • (φ (spinSm (2 * l) v)) ∧
      angularMomentumOperator3D 2 (φ v : 𝓢(Space 3, ℂ)) = (ℏ : ℂ) • (φ (spinSz (2 * l) v)) := by
  obtain ⟨φ₀, h₁, h₂, h₃⟩ := harmonic_spinRep_iso l
  refine ⟨φ₀.trans (harmonicEquivSchwartz l), fun v => ⟨?_, ?_, ?_⟩⟩ <;>
    simp only [LinearEquiv.trans_apply, harmonicEquivSchwartz_apply]
  · rw [raising_gaussPoly, ← LpH_apply]
    exact congrArg (fun q : harmonic l => (ℏ : ℂ) • gaussPoly (q : Poly3))
      (LinearMap.congr_fun h₁ v).symm
  · rw [lowering_gaussPoly, ← LmH_apply]
    exact congrArg (fun q : harmonic l => (ℏ : ℂ) • gaussPoly (q : Poly3))
      (LinearMap.congr_fun h₂ v).symm
  · rw [angularMomentum_gaussPoly_z, ← LzH_apply]
    exact congrArg (fun q : harmonic l => (ℏ : ℂ) • gaussPoly (q : Poly3))
      (LinearMap.congr_fun h₃ v).symm

/-- **Every `l ∈ ℕ` and every integer `|m| ≤ l` occur**: there is a nonzero Schwartz function
with `𝐋² ψ = ℏ² l(l + 1) ψ` and `𝐋_z ψ = ℏ m ψ`. -/
theorem exists_L2_Lz_eigen (l : ℕ) (m : ℤ) (hm : |m| ≤ l) :
    ∃ ψ : 𝓢(Space 3, ℂ), ψ ≠ 0 ∧
      angularMomentumOperatorSqr (d := 3) ψ = ((ℏ : ℂ) ^ 2 * ((l : ℂ) * (l + 1))) • ψ ∧
      angularMomentumOperator3D 2 ψ = ((ℏ : ℂ) * m) • ψ := by
  obtain ⟨φ, hφ⟩ := schwartzHarmonic_spinRep_iso l
  have hk : (l - m).toNat < 2 * l + 1 := by have := abs_le.mp hm; omega
  set k : Fin (2 * l + 1) := ⟨(l - m).toNat, hk⟩
  refine ⟨φ (spinE k), ?_, ?_, ?_⟩
  · intro h
    have h' : φ (spinE k) = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at h'
    have := congrFun h' k
    simp [spinE] at this
  · obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (φ (spinE k)).2
    rw [← hpe, angularMomentumSqr_gaussPoly hp]
  · rw [(hφ _).2.2, spinSz_spinE, map_smul, Submodule.coe_smul, smul_smul]
    congr 1
    have hkm : ((k : ℕ) : ℂ) = (l : ℂ) - m := by
      have : ((k : ℕ) : ℤ) = l - m := by simp [k]; have := abs_le.mp hm; omega
      exact_mod_cast this
    rw [hkm]; push_cast; ring

end QM.AngularMomentum
