/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import QM.Finite.Propagator

/-!
# The adiabatic theorem

Kato's argument in finite dimension. Let `U` be the propagator of `i ε U' = H(s) U`
(`QM.IsPropagator`). If `[H, P] = 0` and `X` solves the commutator equation `[H, X] = P'`, then
`G = U† P U + iε U† X U` has derivative `iε U† X' U`, so `U(1)† P(1) U(1) - P(0) = O(ε)`. For an
eigenvalue `E(s)` with eigenprojection `P(s)` and a gap `g`, the reduced resolvent
`R = (H - E + P)⁻¹ (1 - P)` gives the solution `X = R P' P - P P' R`.

## Main results

* `commutator_eq`: `[H, X] = P'` for `X = K(1 - P)P'P - PP'K(1 - P)`, `K = (H - E + P)⁻¹`.
* `adiabatic_estimate`, `adiabatic_leakage`: the estimate along the propagator.
* `adiabatic` (**adiabatic theorem**): `‖(1 - P(1)) U_ε(1) P(0)‖ ≤ C ε` for a gapped eigenvalue with
  a `C²` eigenprojection.
-/

namespace QM

open Set Complex

section Algebra

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- **The commutator equation** `[H, X] = P'`. Let `HP = PH = eP`, `P² = P`, `P'P + PP' = P'`, and
let `K` be the inverse of `H - e + P`. Then `X = K(1 - P)P'P - PP'K(1 - P)` satisfies
`[H, X] = P'`. -/
lemma commutator_eq {H P P' K : B} {e : ℂ} (hHP : H * P = e • P) (hPH : P * H = e • P)
    (hPP : P * P = P) (hP' : P' * P + P * P' = P') (hAK : (H - e • 1 + P) * K = 1)
    (hKA : K * (H - e • 1 + P) = 1) :
    H * (K * (1 - P) * P' * P - P * P' * (K * (1 - P))) -
      (K * (1 - P) * P' * P - P * P' * (K * (1 - P))) * H = P' := by
  -- `K` commutes with `P`: `(H - e + P) P = P = P (H - e + P)`
  have hAP : (H - e • 1 + P) * P = P := by
    rw [add_mul, sub_mul, hHP, smul_mul_assoc, one_mul, hPP, sub_self, zero_add]
  have hPA : P * (H - e • 1 + P) = P := by
    rw [mul_add, mul_sub, hPH, mul_smul_comm, mul_one, hPP, sub_self, zero_add]
  have hKP : K * P = P := by
    calc K * P = K * ((H - e • 1 + P) * P) := by rw [hAP]
      _ = P := by rw [← mul_assoc, hKA, one_mul]
  have hPK : P * K = P := by
    calc P * K = P * (H - e • 1 + P) * K := by rw [hPA]
      _ = P := by rw [mul_assoc, hAK, mul_one]
  -- `R = K (1 - P)` satisfies `H R = R H = (1 - P) + e R`
  obtain ⟨R, hR⟩ : ∃ R, R = K * (1 - P) := ⟨_, rfl⟩
  rw [← hR]
  have hR' : R = K - P := by rw [hR, mul_sub, mul_one, hKP]
  have hHK : H * K = 1 + e • K - P := by
    have h := hAK
    rw [add_mul, sub_mul, smul_mul_assoc, one_mul, hPK] at h
    rw [← h]; abel
  have hKH : K * H = 1 + e • K - P := by
    have h := hKA
    rw [mul_add, mul_sub, mul_smul_comm, mul_one, hKP] at h
    rw [← h]; abel
  have hHR : H * R = (1 - P) + e • R := by
    rw [hR', mul_sub, hHK, hHP, smul_sub]; abel
  have hRH : R * H = (1 - P) + e • R := by
    rw [hR', sub_mul, hKH, hPH, smul_sub]; abel
  -- `P P' P = 0`
  have hPP'P : P * P' * P = 0 := by
    have h := congrArg (P * ·) hP'
    simp only [mul_add, ← mul_assoc, hPP] at h
    have h2 : P * P' * P + P * P' - P * P' = 0 := by rw [h, sub_self]
    rwa [add_sub_cancel_right] at h2
  have e1 : H * (R * P' * P) = ((1 - P) + e • R) * P' * P := by
    rw [← hHR]; simp only [mul_assoc]
  have e2 : R * P' * P * H = e • (R * P' * P) := by
    rw [mul_assoc, hPH, mul_smul_comm]
  have e3 : H * (P * P' * R) = e • (P * P' * R) := by
    rw [← mul_assoc, ← mul_assoc, hHP, smul_mul_assoc, smul_mul_assoc]
  have e4 : P * P' * R * H = P * P' * ((1 - P) + e • R) := by
    rw [mul_assoc, hRH]
  rw [mul_sub, sub_mul, e1, e2, e3, e4]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, hPP'P]
  conv_rhs => rw [← hP']
  abel

/-- The algebra of the derivative of `U† P U + iε U† X U`. -/
lemma deriv_algebra {sU U H P P' X X' : B} {c d : ℂ} (hdc : d * c = 1) (hHP : H * P = P * H)
    (hHX : H * X - X * H = P') :
    (sU * (-(c • H)) * P + sU * P') * U + sU * P * ((c • H) * U) +
      d • ((sU * (-(c • H)) * X + sU * X') * U + sU * X * ((c • H) * U)) =
      d • (sU * X' * U) := by
  have h1 : sU * (H * (P * U)) = sU * (P * (H * U)) := by
    rw [← mul_assoc H P U, hHP, mul_assoc]
  have h2 : sU * (H * (X * U)) = sU * (X * (H * U)) + sU * (P' * U) := by
    rw [← mul_assoc H X U, show H * X = X * H + P' by rw [← hHX]; abel, add_mul, mul_add,
      mul_assoc]
  simp only [mul_neg, neg_mul, smul_mul_assoc, mul_smul_comm, add_mul, mul_assoc, smul_add,
    smul_neg, smul_smul, h1, h2, hdc, one_smul]
  abel

end Algebra

/-! ### The adiabatic estimate -/

section Estimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma norm_le_one_of_mem_unitary {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) : ‖U‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [ContinuousLinearMap.norm_map_of_mem_unitary hU, one_mul]

/-- **The adiabatic estimate.** If `[H, P] = 0` and `[H, X] = P'` with `‖X'‖ ≤ K` on `[0, 1]`, then
`‖U(1)† P(1) U(1) - P(0)‖ ≤ ε (K + ‖X(0)‖ + ‖X(1)‖)`. -/
theorem adiabatic_estimate {H P X P' X' : ℝ → E →L[ℂ] E} (hsa : ∀ s, IsSelfAdjoint (H s))
    {ε : ℝ} (hε : 0 < ε) {U : ℝ → E →L[ℂ] E} (hU : IsPropagator H ε U)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (P' s) (Icc 0 1) s)
    (hX : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt X (X' s) (Icc 0 1) s)
    (hHP : ∀ s ∈ Icc (0 : ℝ) 1, H s * P s = P s * H s)
    (hHX : ∀ s ∈ Icc (0 : ℝ) 1, H s * X s - X s * H s = P' s)
    {K : ℝ} (hK : ∀ s ∈ Icc (0 : ℝ) 1, ‖X' s‖ ≤ K) :
    ‖star (U 1) * P 1 * U 1 - P 0‖ ≤ ε * (K + ‖X 0‖ + ‖X 1‖) := by
  set c : ℂ := -(I / ε)
  set d : ℂ := I * ε
  have hdc : d * c = 1 := by
    have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    simp only [d, c]
    field_simp
    rw [I_sq]; norm_num
  set G : ℝ → E →L[ℂ] E := fun s =>
    star (U s) * P s * U s + d • (star (U s) * X s * U s)
  have hG : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt G (d • (star (U s) * X' s * U s)) (Icc 0 1) s := by
    intro s hs
    have hUs := (hU.2 s hs).star
    have hstar : star (c • H s * U s) = star (U s) * (-(c • H s)) := by
      rw [star_mul, star_gen (hsa s)]
    rw [hstar] at hUs
    have h := ((hUs.mul (hP s hs)).mul (hU.2 s hs)).add
      (((hUs.mul (hX s hs)).mul (hU.2 s hs)).const_smul d)
    convert h using 1
    exact (deriv_algebra hdc (hHP s hs) (hHX s hs)).symm
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖d • (star (U s) * X' s * U s)‖ ≤ ε * K := by
    intro s hs
    have hu := propagator_mem_unitary hsa hU (Ico_subset_Icc_self hs)
    have hd : ‖d‖ = ε := by simp [d, abs_of_pos hε]
    rw [norm_smul, hd]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    calc ‖star (U s) * X' s * U s‖ ≤ ‖star (U s)‖ * ‖X' s‖ * ‖U s‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖X' s‖ * 1 := by
          gcongr
          · exact norm_le_one_of_mem_unitary (Unitary.star_mem hu)
          · exact norm_le_one_of_mem_unitary hu
      _ ≤ K := by simpa using hK s (Ico_subset_Icc_self hs)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hG hbound
  have hu1 := propagator_mem_unitary hsa hU (right_mem_Icc.mpr zero_le_one)
  have hX1 : ‖star (U 1) * X 1 * U 1‖ ≤ ‖X 1‖ := by
    calc ‖star (U 1) * X 1 * U 1‖ ≤ ‖star (U 1)‖ * ‖X 1‖ * ‖U 1‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 * ‖X 1‖ * 1 := by
          gcongr
          · exact norm_le_one_of_mem_unitary (Unitary.star_mem hu1)
          · exact norm_le_one_of_mem_unitary hu1
      _ = ‖X 1‖ := by ring
  have hG0 : G 0 = P 0 + d • X 0 := by simp [G, hU.1]
  have hd : ‖d‖ = ε := by simp [d, abs_of_pos hε]
  have heq : star (U 1) * P 1 * U 1 - P 0 =
      (G 1 - G 0) - d • (star (U 1) * X 1 * U 1) + d • X 0 := by
    rw [hG0]; simp only [G]; abel
  rw [heq]
  calc ‖(G 1 - G 0) - d • (star (U 1) * X 1 * U 1) + d • X 0‖
      ≤ ‖G 1 - G 0‖ + ‖d • (star (U 1) * X 1 * U 1)‖ + ‖d • X 0‖ := by
        refine (norm_add_le _ _).trans ?_
        exact add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ε * K + ε * ‖X 1‖ + ε * ‖X 0‖ := by
        rw [norm_smul, norm_smul, hd]
        gcongr
    _ = ε * (K + ‖X 0‖ + ‖X 1‖) := by ring

/-- **Adiabatic leakage**: under the hypotheses of `adiabatic_estimate`, if `P(0)` is an orthogonal
projection then `‖(1 - P(1)) U(1) P(0)‖ ≤ ε (K + ‖X(0)‖ + ‖X(1)‖)`. -/
theorem adiabatic_leakage {H P X P' X' : ℝ → E →L[ℂ] E} (hsa : ∀ s, IsSelfAdjoint (H s))
    {ε : ℝ} (hε : 0 < ε) {U : ℝ → E →L[ℂ] E} (hU : IsPropagator H ε U)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (P' s) (Icc 0 1) s)
    (hX : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt X (X' s) (Icc 0 1) s)
    (hHP : ∀ s ∈ Icc (0 : ℝ) 1, H s * P s = P s * H s)
    (hHX : ∀ s ∈ Icc (0 : ℝ) 1, H s * X s - X s * H s = P' s)
    {K : ℝ} (hK : ∀ s ∈ Icc (0 : ℝ) 1, ‖X' s‖ ≤ K) (hP0 : IsStarProjection (P 0)) :
    ‖(1 - P 1) * U 1 * P 0‖ ≤ ε * (K + ‖X 0‖ + ‖X 1‖) := by
  have hest := adiabatic_estimate hsa hε hU hP hX hHP hHX hK
  have hu1 := propagator_mem_unitary hsa hU (right_mem_Icc.mpr zero_le_one)
  have hUU : U 1 * star (U 1) = 1 := (Unitary.mem_iff.mp hu1).2
  have hPP : P 0 * P 0 = P 0 := hP0.isIdempotentElem.eq
  have h : (1 - P 1) * U 1 * P 0 = U 1 * ((P 0 - star (U 1) * P 1 * U 1) * P 0) := by
    calc (1 - P 1) * U 1 * P 0 = U 1 * P 0 - P 1 * U 1 * P 0 := by noncomm_ring
      _ = U 1 * (P 0 * P 0) - (U 1 * star (U 1)) * P 1 * U 1 * P 0 := by
        rw [hPP, hUU, one_mul]
      _ = _ := by noncomm_ring
  rw [h]
  calc ‖U 1 * ((P 0 - star (U 1) * P 1 * U 1) * P 0)‖
      ≤ ‖U 1‖ * (‖P 0 - star (U 1) * P 1 * U 1‖ * ‖P 0‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖star (U 1) * P 1 * U 1 - P 0‖ * 1) := by
        rw [norm_sub_rev]
        gcongr
        · exact norm_le_one_of_mem_unitary hu1
        · exact hP0.norm_le
    _ ≤ ε * (K + ‖X 0‖ + ‖X 1‖) := by simpa using hest

/-! ### A gapped eigenvalue -/

omit [CompleteSpace E] in
/-- In finite dimension an injective operator is invertible. -/
lemma isUnit_of_injective {T : E →L[ℂ] E} (h : Function.Injective T) : IsUnit T := by
  have hs : Function.Surjective (T : E →ₗ[ℂ] E) :=
    LinearMap.injective_iff_surjective.mp h
  set e := LinearEquiv.ofBijective (T : E →ₗ[ℂ] E) ⟨h, hs⟩
  set S : E →L[ℂ] E := LinearMap.toContinuousLinearMap (e.symm : E →ₗ[ℂ] E)
  refine isUnit_iff_exists.mpr ⟨S, ?_, ?_⟩
  · ext x
    change T (e.symm x) = x
    exact e.apply_symm_apply x
  · ext x
    change e.symm (T x) = x
    exact e.symm_apply_apply x

omit [FiniteDimensional ℂ E] in
/-- `P H = E P` follows from `H P = E P` by taking adjoints. -/
lemma mul_eq_of_mul_eq {H P : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hP : IsSelfAdjoint P) {e : ℝ}
    (h : H * P = (e : ℂ) • P) : P * H = (e : ℂ) • P := by
  have := congrArg star h
  rwa [star_mul, hH.star_eq, hP.star_eq, star_smul, hP.star_eq, Complex.star_def,
    Complex.conj_ofReal] at this

omit [FiniteDimensional ℂ E] in
/-- `H - E + P` is injective under the gap condition. -/
lemma injective_shift {H P : E →L[ℂ] E} (hP : IsStarProjection P) {e : ℝ}
    (hPH : P * H = (e : ℂ) • P) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ v, P v = 0 → g * ‖v‖ ≤ ‖(H - (e : ℂ) • 1) v‖) :
    Function.Injective ((H - (e : ℂ) • 1 + P : E →L[ℂ] E) : E → E) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hPP : P * P = P := hP.isIdempotentElem.eq
  -- apply `P`: the `P`-component of `v` vanishes
  have hPv : P v = 0 := by
    have h := congrArg P hv
    have e1 : P ((H - (e : ℂ) • 1 + P) v) = P v := by
      change (P * (H - (e : ℂ) • 1 + P)) v = P v
      rw [mul_add, mul_sub, hPH, mul_smul_comm, mul_one, hPP, sub_self, zero_add]
    rw [e1, map_zero] at h
    exact h
  have h2 : (H - (e : ℂ) • 1) v = 0 := by
    have : (H - (e : ℂ) • 1 + P) v = (H - (e : ℂ) • 1) v + P v := rfl
    rw [this, hPv, add_zero] at hv
    exact hv
  have h3 := hgap v hPv
  rw [h2, norm_zero] at h3
  have : ‖v‖ = 0 := le_antisymm (by nlinarith [norm_nonneg v]) (norm_nonneg v)
  exact norm_eq_zero.mp this

/-- **The adiabatic theorem.** Let `H(s)` be a `C¹` family of self-adjoint operators, `E(s)` a real
`C¹` function and `P(s)` a `C²` family of orthogonal projections with `H(s) P(s) = E(s) P(s)`, and
assume a gap `g > 0`: `‖(H(s) - E(s)) v‖ ≥ g ‖v‖` whenever `P(s) v = 0`, for `s ∈ [0, 1]`. Then
there is `C` such that for every `ε > 0` the propagator satisfies
`‖(1 - P(1)) U_ε(1) P(0)‖ ≤ C ε`. -/
theorem adiabatic {H P : ℝ → E →L[ℂ] E} {Ev : ℝ → ℝ} (hH : ContDiff ℝ 1 H)
    (hsa : ∀ s, IsSelfAdjoint (H s)) (hEv : ContDiff ℝ 1 Ev) (hP : ContDiff ℝ 2 P)
    (hproj : ∀ s, IsStarProjection (P s)) (hHP : ∀ s, H s * P s = (Ev s : ℂ) • P s)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v, P s v = 0 → g * ‖v‖ ≤ ‖(H s - (Ev s : ℂ) • 1) v‖) :
    ∃ C, ∀ ε > 0, ∀ U, IsPropagator H ε U → ‖(1 - P 1) * U 1 * P 0‖ ≤ C * ε := by
  have hPH : ∀ s, P s * H s = (Ev s : ℂ) • P s := fun s =>
    mul_eq_of_mul_eq (hsa s) (hproj s).isSelfAdjoint (hHP s)
  -- the shifted operator and its inverse
  set A : ℝ → E →L[ℂ] E := fun s => H s - (Ev s : ℂ) • 1 + P s with hAdef
  have hEvC : ContDiff ℝ 1 (fun s => (Ev s : ℂ) • (1 : E →L[ℂ] E)) := by
    have : (fun s => (Ev s : ℂ) • (1 : E →L[ℂ] E)) = fun s => Ev s • (1 : E →L[ℂ] E) := by
      funext s; exact Complex.coe_smul _ _
    rw [this]; exact hEv.smul contDiff_const
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  have hA : ContDiff ℝ 1 A := (hH.sub hEvC).add hP1
  set O : Set ℝ := {s | IsUnit (A s)}
  have hO : IsOpen O := Units.isOpen.preimage hA.continuous
  have hIO : Icc (0 : ℝ) 1 ⊆ O := fun s hs =>
    isUnit_of_injective (injective_shift (hproj s) (hPH s) hg (hgap s hs))
  set K : ℝ → E →L[ℂ] E := fun s => Ring.inverse (A s)
  have hK : ContDiffOn ℝ 1 K O := by
    intro s hs
    have h1 : ContDiffAt ℝ 1 (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E)) (A s) := by
      have := contDiffAt_ringInverse (n := 1) ℝ hs.unit
      rwa [IsUnit.unit_spec] at this
    exact (h1.comp s hA.contDiffAt).contDiffWithinAt
  -- the derivative of `P`
  have hP' : ContDiff ℝ 1 (deriv P) := (contDiff_succ_iff_deriv.mp hP).2.2
  have hPd : ∀ s, HasDerivAt P (deriv P s) s := fun s =>
    (hP1.differentiable one_ne_zero s).hasDerivAt
  have hPid : ∀ s, deriv P s * P s + P s * deriv P s = deriv P s := by
    intro s
    have h1 := (hPd s).mul (hPd s)
    have h2 : P * P = P := funext fun s => (hproj s).isIdempotentElem.eq
    rw [h2] at h1
    exact h1.unique (hPd s)
  -- the solution `X` of `[H, X] = P'`
  set X : ℝ → E →L[ℂ] E := fun s =>
    K s * (1 - P s) * deriv P s * P s - P s * deriv P s * (K s * (1 - P s))
  have hX : ContDiffOn ℝ 1 X O := by
    have hP1O := hP1.contDiffOn (s := O)
    have hP'O := hP'.contDiffOn (s := O)
    exact ((((hK.mul (contDiffOn_const.sub hP1O)).mul hP'O).mul hP1O).sub
      ((hP1O.mul hP'O).mul (hK.mul (contDiffOn_const.sub hP1O))))
  have hXd : ∀ s ∈ O, HasDerivAt X (deriv X s) s := fun s hs =>
    ((hX.contDiffAt (hO.mem_nhds hs)).differentiableAt one_ne_zero).hasDerivAt
  have hXc : ContinuousOn (deriv X) (Icc 0 1) :=
    (hX.continuousOn_deriv_of_isOpen hO le_rfl).mono hIO
  obtain ⟨Kb, hKb⟩ := isCompact_Icc.exists_bound_of_continuousOn hXc
  have hHX : ∀ s ∈ Icc (0 : ℝ) 1, H s * X s - X s * H s = deriv P s := by
    intro s hs
    have hu : IsUnit (A s) := hIO hs
    exact commutator_eq (hHP s) (hPH s) (hproj s).isIdempotentElem.eq (hPid s)
      (Ring.mul_inverse_cancel _ hu) (Ring.inverse_mul_cancel _ hu)
  refine ⟨Kb + ‖X 0‖ + ‖X 1‖, fun ε hε U hU => ?_⟩
  have h := adiabatic_leakage hsa hε hU (fun s _ => (hPd s).hasDerivWithinAt)
    (fun s hs => (hXd s (hIO hs)).hasDerivWithinAt)
    (fun s _ => (hHP s).trans (hPH s).symm) hHX hKb (hproj 0)
  rw [mul_comm] at h
  exact h

end Estimate

end QM
