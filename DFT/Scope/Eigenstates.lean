/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DFT.Scope.Functionals
import DFT.Scope.HK

/-!
# Representability by eigenstates (stage 2)

**`eigenstate_vrep`** (Wang–Liebert–Penz–Schilling, Theorem 5.3(i)): every regular value `ρ ∈ B_r`
is the density of a unit vector `ψ` with `H(v) ψ = λ ψ` for some potential `v`, and `ψ` attains
`F_p(ρ)`. No non-redundancy is needed.

The proof is the Lagrange multiplier rule (in Fritz John form) at a minimiser `ψ` of the constrained
search `F_p(ρ)`. The constraints are the norm and the densities `⟨B_a⟩` for `a` in a basis of a
complement `U` of `W = {a : ι(a) ∈ ℝ·1}`; on unit vectors the densities along `W` are fixed, so
these constraints still cut out the fibre. If the multiplier of `⟨H₀⟩` vanished, `ψ` would be an
eigenvector of `ι(u)`, `u ∈ U`; since `ψ` is not critical, `ι(u) ∈ ℝ·1`, so `u ∈ W ∩ U = 0` and all
multipliers vanish. Hence it does not vanish, and the multiplier rule is the eigenvalue equation.

* `reForm A`: `(x, y) ↦ Re⟨x, A y⟩` as a continuous real bilinear form.
* `hasStrictFDerivAt_expv`: `ψ ↦ Re⟨ψ, A ψ⟩` has derivative `h ↦ 2 Re⟨ψ, A h⟩` (`A` Hermitian).
-/

namespace DFT.Scope

open Matrix RCLike Set

variable {𝕜 d m : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] (S : Scope 𝕜 d m)

omit [Fintype d] in
lemma pot_sum {ι : Type*} (s : Finset ι) (v : ι → m → ℝ) :
    S.pot (∑ j ∈ s, v j) = ∑ j ∈ s, S.pot (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, pot_add, ih]

lemma expv_pot (a : m → ℝ) (x : d → 𝕜) : expv (S.pot a) x = S.densPure x ⬝ᵥ a := by
  have h := S.expv_ham a x
  rw [ham, expv_add] at h
  linarith

/-- `(x, y) ↦ Re⟨x, A y⟩` as a continuous real bilinear form. -/
noncomputable def reForm (A : Matrix d d 𝕜) : (d → 𝕜) →L[ℝ] (d → 𝕜) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap
        { toFun := fun y => re (star x ⬝ᵥ (A *ᵥ y))
          map_add' := fun y z => by simp [mulVec_add, dotProduct_add]
          map_smul' := fun r y => by
            simp [mulVec_smul, dotProduct_smul, RCLike.smul_re] }
      map_add' := fun x z => by ext y; simp [star_add, add_dotProduct]
      map_smul' := fun r x => by ext y; simp [star_smul, smul_dotProduct, RCLike.smul_re] }

lemma reForm_apply (A : Matrix d d 𝕜) (x y : d → 𝕜) :
    reForm A x y = re (star x ⬝ᵥ (A *ᵥ y)) := rfl

/-- For Hermitian `A`, `Re⟨x, A y⟩ = Re⟨y, A x⟩`. -/
lemma re_dotProduct_mulVec_comm {A : Matrix d d 𝕜} (hA : A.IsHermitian) (x y : d → 𝕜) :
    re (star x ⬝ᵥ (A *ᵥ y)) = re (star y ⬝ᵥ (A *ᵥ x)) := by
  rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec, hA.eq, RCLike.star_def, conj_re]

/-- The derivative of `ψ ↦ Re⟨ψ, A ψ⟩` is `h ↦ 2 Re⟨ψ, A h⟩`. -/
lemma hasStrictFDerivAt_expv {A : Matrix d d 𝕜} (hA : A.IsHermitian) (ψ : d → 𝕜) :
    HasStrictFDerivAt (expv A) ((2 : ℝ) • reForm A ψ) ψ := by
  have h := (reForm A).hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id ψ)
    (hasStrictFDerivAt_id ψ)
  have hfun : (fun y => reForm A (id y) (id y)) = expv A := rfl
  rw [hfun] at h
  refine h.congr_fderiv ?_
  ext h'
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.coe_id', id, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, reForm_apply]
  rw [re_dotProduct_mulVec_comm hA h' ψ]
  ring

/-- **Representability by eigenstates**: every regular value is the density of an eigenstate of
some `H(v)`, which attains `F_p`. -/
theorem eigenstate_vrep [DecidableEq d] {ρ : m → ℝ} (hρ : ρ ∈ S.Br) :
    ∃ ψ ∈ unitVecs, S.densPure ψ = ρ ∧ S.Fp ρ = expv S.H0 ψ ∧
      ∃ (v : m → ℝ) (lam : ℝ), S.ham v *ᵥ ψ = (lam : 𝕜) • ψ := by
  classical
  obtain ⟨ψ, hψ, hρψ, hF⟩ := S.Fp_attained hρ.1
  refine ⟨ψ, hψ, hρψ, hF, ?_⟩
  have hψ1 : star ψ ⬝ᵥ ψ = 1 := hψ
  -- potentials whose term is a multiple of the identity, and a complement
  let W : Submodule ℝ (m → ℝ) :=
    { carrier := {a | ∃ c : ℝ, S.pot a = (c : 𝕜) • 1}
      add_mem' := by
        rintro a a' ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', by rw [pot_add, hc, hc', ofReal_add, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r a ⟨c, hc⟩
        exact ⟨r * c, by rw [pot_smul, hc, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul,
          ofReal_mul]⟩ }
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl W
  set b := Module.finBasis ℝ U
  -- the constraints: the norm and the densities along `U`
  set Aop : Option (Fin (Module.finrank ℝ U)) → Matrix d d 𝕜 :=
    fun o => o.elim 1 fun j => S.pot (b j)
  have hAop : ∀ o, (Aop o).IsHermitian := by
    rintro (_ | j)
    · exact isHermitian_one
    · exact S.isHermitian_pot _
  have hexpv1 : ∀ x : d → 𝕜, expv 1 x = ∑ i, ‖x i‖ ^ 2 := fun x => by
    simp [expv, star_dotProduct_self_eq]
  -- on unit vectors, the densities along `W` are fixed
  have hW : ∀ w ∈ W, ∀ x ∈ (unitVecs : Set (d → 𝕜)), S.densPure x ⬝ᵥ w = S.densPure ψ ⬝ᵥ w := by
    rintro w ⟨c, hc⟩ x hx
    rw [← expv_pot, ← expv_pot, hc, ← RCLike.real_smul_eq_coe_smul (K := 𝕜), expv_smul,
      expv_smul, hexpv1, hexpv1, sum_norm_sq_eq_one hx, sum_norm_sq_eq_one hψ]
  -- the constraint set is the fibre
  have hfib : ∀ x, (∀ o, expv (Aop o) x = expv (Aop o) ψ) →
      x ∈ (unitVecs : Set (d → 𝕜)) ∧ S.densPure x = ρ := by
    intro x hx
    have hxu : x ∈ (unitVecs : Set (d → 𝕜)) := by
      have h := hx none
      simp only [Aop, Option.elim, hexpv1, sum_norm_sq_eq_one hψ] at h
      change star x ⬝ᵥ x = 1
      rw [star_dotProduct_self_eq, h, ofReal_one]
    refine ⟨hxu, ?_⟩
    have hall : ∀ a, S.densPure x ⬝ᵥ a = S.densPure ψ ⬝ᵥ a := fun a => by
      obtain ⟨w, hw, u, hu, rfl⟩ :=
        Submodule.mem_sup.1 (hU.sup_eq_top ▸ Submodule.mem_top (x := a))
      rw [dotProduct_add, dotProduct_add, hW w hw x hxu]
      congr 1
      have hrepr := b.sum_repr ⟨u, hu⟩
      have hu' : u = ∑ j, (b.repr ⟨u, hu⟩ j) • (b j : m → ℝ) := by
        have := congrArg Subtype.val hrepr
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hu', dotProduct_sum, dotProduct_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dotProduct_smul, dotProduct_smul, ← expv_pot, ← expv_pot]
      exact congrArg _ (hx (some j))
    rw [← hρψ]
    funext i
    simpa [dotProduct_single] using hall (Pi.single i 1)
  have hext : IsLocalExtrOn (expv S.H0) {x | ∀ o, expv (Aop o) x = expv (Aop o) ψ} ψ := by
    refine IsMinOn.isLocalMinOn (fun x hx => ?_) |>.isExtrFilter
    obtain ⟨hxu, hxρ⟩ := hfib x hx
    have h := S.Fp_le hxu
    rw [hxρ, hF] at h
    exact EReal.coe_le_coe_iff.1 h
  obtain ⟨Λ, Λ₀, hne, hsum⟩ := hext.exists_multipliers_of_hasStrictFDerivAt
    (fun o => hasStrictFDerivAt_expv (hAop o) ψ) (hasStrictFDerivAt_expv S.isHermitian_H0 ψ)
  -- the multiplier rule as a vector equation
  set X : d → 𝕜 := ∑ o, Λ o • (Aop o *ᵥ ψ) + Λ₀ • (S.H0 *ᵥ ψ) with hXdef
  have hX : X = 0 := by
    have hh : ∀ h : d → 𝕜, re (star h ⬝ᵥ X) = 0 := fun h => by
      have := congrArg (fun L : StrongDual ℝ (d → 𝕜) => L h) hsum
      simp only [add_apply, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, reForm_apply, zero_apply] at this
      simp only [hXdef, dotProduct_add, dotProduct_sum, map_add, map_sum,
        RCLike.real_smul_eq_coe_smul (K := 𝕜), dotProduct_smul, smul_eq_mul, re_ofReal_mul]
      simp only [re_dotProduct_mulVec_comm (hAop _) _ h,
        re_dotProduct_mulVec_comm S.isHermitian_H0 _ h] at this ⊢
      simp only [mul_left_comm _ (2 : ℝ), ← Finset.mul_sum] at this
      linarith
    have h0 := hh X
    rw [star_dotProduct_self_eq, ofReal_re] at h0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖X i‖).1 h0 i
      (Finset.mem_univ _)
    simpa using this
  -- the potential collected from the multipliers of `U`
  set uU : U := ∑ j, Λ (some j) • b j
  set u : m → ℝ := (uU : m → ℝ)
  have hu : u = ∑ j, Λ (some j) • (b j : m → ℝ) := by simp [u, uU]
  have hpotu : S.pot u *ᵥ ψ = ∑ j, Λ (some j) • (S.pot (b j) *ᵥ ψ) := by
    rw [hu, pot_sum, sum_mulVec]
    exact Finset.sum_congr rfl fun j _ => by rw [pot_smul, smul_mulVec]
  have hX' : Λ none • ψ + S.pot u *ᵥ ψ + Λ₀ • (S.H0 *ᵥ ψ) = 0 := by
    rw [← hX, hXdef, Fintype.sum_option, hpotu]
    simp [Aop]
  by_cases hΛ₀ : Λ₀ = 0
  · -- impossible: `ψ` would be critical or all multipliers would vanish
    exfalso
    rw [hΛ₀, zero_smul, add_zero] at hX'
    have hcrit : ∃ c : ℝ, S.pot u = (c : 𝕜) • 1 := by
      by_contra hc
      push Not at hc
      refine hρ.2 ⟨ψ, ⟨hψ, u, hc, ((-Λ none : ℝ) : 𝕜), ?_⟩, hρψ⟩
      rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜), neg_smul]
      exact eq_neg_of_add_eq_zero_right hX'
    have hu0 : uU = 0 := by
      have hmem : (uU : m → ℝ) ∈ W ⊓ U := Submodule.mem_inf.2 ⟨hcrit, uU.2⟩
      rw [hU.inf_eq_bot, Submodule.mem_bot] at hmem
      exact Subtype.ext hmem
    have hΛj : ∀ j, Λ (some j) = 0 :=
      Fintype.linearIndependent_iff.1 b.linearIndependent _ hu0
    have hupot : S.pot u = 0 := by
      rw [show u = 0 from by simp [u, hu0], pot_zero]
    rw [hupot, zero_mulVec, add_zero, smul_eq_zero] at hX'
    have hψ0 : ψ ≠ 0 := ne_zero_of_mem_unitVecs hψ
    have hΛn : Λ none = 0 := hX'.resolve_right hψ0
    apply hne
    rw [Prod.mk_eq_zero]
    exact ⟨funext fun o => by cases o with
      | none => exact hΛn
      | some j => exact hΛj j, hΛ₀⟩
  · refine ⟨Λ₀⁻¹ • u, -(Λ₀⁻¹ * Λ none), ?_⟩
    have h2 := congrArg (fun y => Λ₀⁻¹ • y) hX'
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hΛ₀, one_smul, smul_zero] at h2
    rw [ham, add_mulVec, pot_smul, smul_mulVec, ← RCLike.real_smul_eq_coe_smul (K := 𝕜),
      neg_smul, eq_neg_iff_add_eq_zero]
    convert h2 using 1
    abel

end DFT.Scope
