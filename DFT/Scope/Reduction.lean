/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Scope.Functionals

/-!
# Reduction of scope (stage 3)

After Wang–Liebert–Penz–Schilling, §VII.A. For a linear map `f : ℝ^r → ℝ^m` and a fixed potential
`v₀`, the reduced scope `S_r = (ι ∘ f, H₀ + ι(v₀))` has the observables `ι(f e_j)`. Its densities are
the pull-backs `f*ρ`, `(f*ρ)_j = ρ · f e_j` (`pullback`).

* `reduce_ham`: `H_r(v') = H(v₀ + f v')`, hence `reduce_E`.
* `reduce_densPure`, `reduce_dens`: `ρ_r = f* ρ`.
* `reduce_Bp`, `reduce_Be`: `B_p(S_r) = f* B_p(S)`, `B_e(S_r) = f* B_e(S)`.
* `reduce_Fp`, `reduce_Fe` (Proposition 7.1): `F_r(ρ') = inf {ρ · v₀ + F(ρ) : f* ρ = ρ'}`.

Example: RDMFT reduces to lattice DFT with `f` the diagonal embedding and `v₀` the hopping.
-/

namespace DFT.Scope

open Matrix RCLike Set

variable {𝕜 d m r : Type*} [RCLike 𝕜] [Fintype d] [Fintype m] [DecidableEq r]
  (S : Scope 𝕜 d m)

/-- The pull-back of densities along `f`: `(f* ρ)_j = ρ · f e_j`. -/
def pullback (f : (r → ℝ) →ₗ[ℝ] (m → ℝ)) (ρ : m → ℝ) : r → ℝ := fun j => ρ ⬝ᵥ f (Pi.single j 1)

/-- **The reduced scope** `(ι ∘ f, H₀ + ι(v₀))`. -/
noncomputable def reduce (f : (r → ℝ) →ₗ[ℝ] (m → ℝ)) (v₀ : m → ℝ) : Scope 𝕜 d r where
  H0 := S.H0 + S.pot v₀
  B j := S.pot (f (Pi.single j 1))
  isHermitian_H0 := S.isHermitian_H0.add (S.isHermitian_pot v₀)
  isHermitian_B _ := S.isHermitian_pot _

variable (f : (r → ℝ) →ₗ[ℝ] (m → ℝ)) (v₀ : m → ℝ)

omit [Fintype d] in
lemma pot_eq_sum_single [Fintype r] (v' : r → ℝ) :
    S.pot (f v') = ∑ j, v' j • S.pot (f (Pi.single j 1)) := by
  have hv : v' = ∑ j, v' j • (Pi.single j (1 : ℝ) : r → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, pot_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, pot_smul]

omit [Fintype d] in
lemma reduce_ham [Fintype r] (v' : r → ℝ) : (S.reduce f v₀).ham v' = S.ham (v₀ + f v') := by
  change S.H0 + S.pot v₀ + ∑ j, v' j • S.pot (f (Pi.single j 1)) = S.H0 + S.pot (v₀ + f v')
  rw [pot_add, pot_eq_sum_single, add_assoc]

lemma reduce_E [Fintype r] (v' : r → ℝ) : (S.reduce f v₀).E v' = S.E (v₀ + f v') := by
  simp only [E, reduce_ham]

lemma reduce_densPure (ψ : d → 𝕜) :
    (S.reduce f v₀).densPure ψ = pullback f (S.densPure ψ) := by
  funext j
  simp only [densPure, reduce, pullback]
  exact S.expv_pot _ ψ

lemma reduce_dens (Γ : Matrix d d 𝕜) : (S.reduce f v₀).dens Γ = pullback f (S.dens Γ) := by
  funext j
  simp only [dens, reduce, pullback]
  exact S.trv_pot _ Γ

/-- The pure range of the reduced scope is the pull-back of the pure range. -/
theorem reduce_Bp : (S.reduce f v₀).Bp = pullback f '' S.Bp := by
  simp only [Bp, image_image, reduce_densPure]

/-- The ensemble range of the reduced scope is the pull-back of the ensemble range. -/
theorem reduce_Be : (S.reduce f v₀).Be = pullback f '' S.Be := by
  simp only [Be, image_image, reduce_dens]

/-- **Proposition 7.1**: `F_p(S_r)(ρ') = inf {ρ · v₀ + F_p(S)(ρ) : f* ρ = ρ'}`. -/
theorem reduce_Fp (ρ' : r → ℝ) :
    (S.reduce f v₀).Fp ρ' = ⨅ ρ ∈ {ρ | pullback f ρ = ρ'}, ((ρ ⬝ᵥ v₀ : ℝ) : EReal) + S.Fp ρ := by
  refine le_antisymm (le_iInf₂ fun ρ hρ => ?_) (le_iInf₂ fun ψ hψ => ?_)
  · by_cases hB : ρ ∈ S.Bp
    · obtain ⟨ψ, hψ, rfl, he⟩ := S.Fp_attained hB
      rw [he, ← EReal.coe_add]
      refine (iInf₂_le ψ ⟨hψ, by rw [reduce_densPure]; exact hρ⟩).trans ?_
      rw [EReal.coe_le_coe_iff]
      simp only [reduce, expv_add, expv_pot]
      linarith
    · rw [S.Fp_eq_top hB, EReal.coe_add_top]
      exact le_top
  · obtain ⟨hψu, hψρ⟩ := hψ
    refine (iInf₂_le (S.densPure ψ) ((S.reduce_densPure f v₀ ψ).symm.trans hψρ)).trans ?_
    refine (add_le_add_right (S.Fp_le hψu) _).trans ?_
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    simp only [reduce, expv_add, expv_pot]
    linarith

/-- **Proposition 7.1**, ensembles: `F_e(S_r)(ρ') = inf {ρ · v₀ + F_e(S)(ρ) : f* ρ = ρ'}`. -/
theorem reduce_Fe (ρ' : r → ℝ) :
    (S.reduce f v₀).Fe ρ' = ⨅ ρ ∈ {ρ | pullback f ρ = ρ'}, ((ρ ⬝ᵥ v₀ : ℝ) : EReal) + S.Fe ρ := by
  refine le_antisymm (le_iInf₂ fun ρ hρ => ?_) (le_iInf₂ fun Γ hΓ => ?_)
  · by_cases hB : ρ ∈ S.Be
    · obtain ⟨Γ, hΓ, rfl, he⟩ := S.Fe_attained hB
      rw [he, ← EReal.coe_add]
      refine (iInf₂_le Γ ⟨hΓ, by rw [reduce_dens]; exact hρ⟩).trans ?_
      rw [EReal.coe_le_coe_iff]
      simp only [reduce, trv_add, trv_pot]
      linarith
    · rw [S.Fe_eq_top hB, EReal.coe_add_top]
      exact le_top
  · obtain ⟨hΓu, hΓρ⟩ := hΓ
    refine (iInf₂_le (S.dens Γ) ((S.reduce_dens f v₀ Γ).symm.trans hΓρ)).trans ?_
    refine (add_le_add_right (S.Fe_le hΓu) _).trans ?_
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    simp only [reduce, trv_add, trv_pot]
    linarith

end DFT.Scope
