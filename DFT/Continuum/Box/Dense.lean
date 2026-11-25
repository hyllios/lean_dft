/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Box.Lieb
import DFT.Continuum.Box.VRep
import DFT.Continuum.General.Ekeland

/-!
# Supergradient densities are dense (one particle in a box)

Potentials are `C([0, 1])`, a Banach space, and densities are continuous linear functionals on it.

* `gsEr`: the ground-state energy as a real function, `gsE = gsEr`.
* `densL`: the density of a normalised state as a functional of norm `≤ 1`.
* `gsEr_concave`, `gsEr_lipschitz`: `E` is concave and `1`-Lipschitz.
* `supergrad_of_isNGS`: **Hellmann–Feynman inequality.** The density of a ground state of `v` is
  a supergradient of `E` at `v`.
* `liebF_of_supergrad`: a supergradient `ρ'` of `E` at `v` has `F(ρ') = E(v) - ρ'(v)`, that is,
  `-v` is a subgradient of `F` at `ρ'`.
* `dense_supergrad`: **every density with finite Lieb functional is, within any `η > 0` in the
  dual norm, a supergradient density** (Brøndsted–Rockafellar).

What remains for the density of v-representable densities is the converse of Hellmann–Feynman:
every supergradient of `E` at `v` is the density of the ground state of `v`.
-/

namespace DFT

namespace Continuum

namespace Box

open MeasureTheory Set

/-- The ground-state energy, as a real number. -/
noncomputable def gsEr (v : Pot) : ℝ := Q setting v (Classical.choose (exists_isNGS v))

lemma gsEr_spec (v : Pot) : IsNGS setting v (Classical.choose (exists_isNGS v)) :=
  Classical.choose_spec (exists_isNGS v)

lemma gsE_eq (v : Pot) : gsE setting v = ((gsEr v : ℝ) : EReal) := gsE_of_isNGS (gsEr_spec v)

lemma gsEr_le (v : Pot) {ψ : ℝ → ℝ} (hψ : ψ ∈ Nst setting) : gsEr v ≤ Q setting v ψ :=
  (gsEr_spec v).2 ψ hψ

lemma gsEr_eq_of_isNGS {v : Pot} {ψ : ℝ → ℝ} (h : IsNGS setting v ψ) : gsEr v = Q setting v ψ :=
  le_antisymm (gsEr_le v h.1) (h.2 _ (gsEr_spec v).1)

section densL

variable {ψ : ℝ → ℝ}

lemma cont_sq (hψ : ψ ∈ Dom) : Continuous fun t => ψ t ^ 2 := hψ.1.continuous.pow 2

lemma dens_add' (hψ : ψ ∈ Dom) (u w : Pot) :
    dens setting ψ (u + w) = dens setting ψ u + dens setting ψ w := by
  rw [dens_eq_sq]
  simp only
  rw [← integral_add (f := fun t => ext u t * ψ t ^ 2) (g := fun t => ext w t * ψ t ^ 2)
    (integrable_of_continuous ((continuous_ext u).mul (cont_sq hψ)))
    (integrable_of_continuous ((continuous_ext w).mul (cont_sq hψ)))]
  congr 1; funext t; simp only [ext, ContinuousMap.add_apply]; ring

lemma dens_smul' (a : ℝ) (u : Pot) : dens setting ψ (a • u) = a * dens setting ψ u := by
  rw [dens_eq_sq]
  simp only
  rw [← integral_const_mul]
  congr 1; funext t; simp only [ext, ContinuousMap.smul_apply, smul_eq_mul]; ring

lemma abs_dens_le (hψ : ψ ∈ Nst setting) (u : Pot) : |dens setting ψ u| ≤ ‖u‖ := by
  have hD : ψ ∈ Dom := hψ.1
  have hn : ∫ t, ψ t ^ 2 ∂μ1 = 1 := by rw [← ip_eq_sq]; exact hψ.2
  rw [dens_eq_sq, ← Real.norm_eq_abs]
  calc ‖∫ t, ext u t * ψ t ^ 2 ∂μ1‖ ≤ ∫ t, ‖u‖ * ψ t ^ 2 ∂μ1 := by
        refine norm_integral_le_of_norm_le
          (integrable_of_continuous (continuous_const.mul (cont_sq hD)))
          (Filter.Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (ψ t))]
        exact mul_le_mul_of_nonneg_right (abs_ext_le u t) (sq_nonneg _)
    _ = ‖u‖ := by rw [integral_const_mul, hn, mul_one]

/-- The density of a normalised state, as a continuous linear functional of norm `≤ 1`. -/
noncomputable def densL (hψ : ψ ∈ Nst setting) : StrongDual ℝ Pot :=
  LinearMap.mkContinuous
    { toFun := dens setting ψ
      map_add' := dens_add' hψ.1
      map_smul' := fun a u => by rw [dens_smul']; rfl }
    1 (fun u => by rw [one_mul, Real.norm_eq_abs]; exact abs_dens_le hψ u)

@[simp] lemma densL_apply (hψ : ψ ∈ Nst setting) (u : Pot) : densL hψ u = dens setting ψ u := rfl

lemma norm_densL_le (hψ : ψ ∈ Nst setting) : ‖densL hψ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma Q_shift (hψ : ψ ∈ Dom) (v w : Pot) :
    Q setting w ψ = Q setting v ψ + dens setting ψ (w - v) := by
  rw [Q_eq, Q_eq, add_assoc, ← dens_add' hψ, add_sub_cancel]

end densL

/-- **Hellmann–Feynman inequality.** The density of a normalised ground state of `v` is a
supergradient of the ground-state energy at `v`. -/
theorem supergrad_of_isNGS {v : Pot} {ψ : ℝ → ℝ} (h : IsNGS setting v ψ) (w : Pot) :
    gsEr w ≤ gsEr v + densL h.1 (w - v) := by
  rw [densL_apply, gsEr_eq_of_isNGS h, ← Q_shift h.1.1]
  exact gsEr_le w h.1

/-- The ground-state energy is `1`-Lipschitz in the sup norm. -/
theorem gsEr_lipschitz (v w : Pot) : |gsEr v - gsEr w| ≤ ‖v - w‖ := by
  have h1 := supergrad_of_isNGS (gsEr_spec w) v
  have h2 := supergrad_of_isNGS (gsEr_spec v) w
  have b1 := abs_dens_le (gsEr_spec w).1 (v - w)
  have b2 := abs_dens_le (gsEr_spec v).1 (w - v)
  rw [densL_apply] at h1 h2
  rw [norm_sub_rev] at b2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (dens setting (Classical.choose (exists_isNGS w)) (v - w)),
    le_abs_self (dens setting (Classical.choose (exists_isNGS v)) (w - v))]

theorem continuous_gsEr : Continuous gsEr :=
  (LipschitzWith.of_dist_le_mul fun v w => by
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]; exact gsEr_lipschitz v w).continuous

/-- The ground-state energy is concave. -/
theorem gsEr_concave : ConcaveOn ℝ univ gsEr := by
  refine ⟨convex_univ, fun v _ w _ a b ha hb hab => ?_⟩
  set ψ := Classical.choose (exists_isNGS (a • v + b • w))
  have hψ := gsEr_spec (a • v + b • w)
  have hD : ψ ∈ Dom := hψ.1.1
  have hv := gsEr_le v hψ.1
  have hw := gsEr_le w hψ.1
  have hQ : Q setting (a • v + b • w) ψ = a * Q setting v ψ + b * Q setting w ψ := by
    rw [Q_eq, Q_eq, Q_eq, dens_add' hD, dens_smul', dens_smul']
    linear_combination (-(setting.h0 ψ ψ)) * hab
  simp only [smul_eq_mul]
  change a * gsEr v + b * gsEr w ≤ Q setting (a • v + b • w) ψ
  rw [hQ]
  exact add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)

/-- A finite Lieb functional bounds `E - ρ`. -/
lemma gsEr_sub_le {ρ : Pot → ℝ} {c : ℝ} (hF : liebF setting ρ ≤ (c : EReal)) (v : Pot) :
    gsEr v - ρ v ≤ c := by
  have := gsE_le_liebF_add (v := v) hF
  rw [gsE_eq, EReal.coe_le_coe_iff] at this
  linarith

/-- At a supergradient `ρ'` of `E` at `v`, `F(ρ') = E(v) - ρ'(v)`: `-v` is a subgradient of the
Lieb functional at `ρ'`. -/
theorem liebF_of_supergrad {v : Pot} {ρ' : Pot → ℝ} (hρ' : ∀ w, gsEr w - ρ' w ≤ gsEr v - ρ' v) :
    liebF setting ρ' = ((gsEr v - ρ' v : ℝ) : EReal) := by
  refine le_antisymm (iSup_le fun w => ?_) ?_
  · rw [gsE_eq, ← EReal.coe_sub, EReal.coe_le_coe_iff]; exact hρ' w
  · have := le_liebF (S := setting) v ρ'
    rwa [gsE_eq, ← EReal.coe_sub] at this

/-- **Supergradient densities are dense.** Every density `ρ` (a continuous linear functional on
`C([0, 1])`) with finite Lieb functional is within any `η > 0`, in the dual norm, of a
supergradient `ρ'` of the ground-state energy at some potential `v`; then `F(ρ') = E(v) - ρ'(v)`. -/
theorem dense_supergrad (ρ : StrongDual ℝ Pot) {c : ℝ} (hF : liebF setting ρ ≤ (c : EReal))
    {η : ℝ} (hη : 0 < η) :
    ∃ (v : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - ρ‖ ≤ η ∧ (∀ w, gsEr w ≤ gsEr v + ρ' (w - v)) ∧
      liebF setting ρ' = ((gsEr v - ρ' v : ℝ) : EReal) := by
  obtain ⟨v, ρ', hn, hs⟩ := exists_supergrad_near gsEr_concave continuous_gsEr.upperSemicontinuous
    ρ ⟨c, by rintro _ ⟨v, rfl⟩; exact gsEr_sub_le hF v⟩ hη
  refine ⟨v, ρ', hn, hs, liebF_of_supergrad fun w => ?_⟩
  have := hs w
  rw [map_sub] at this
  linarith

/-- Every N-representable density (the density of a normalised state) has finite Lieb functional,
so it is a limit of supergradient densities. -/
theorem dense_supergrad_of_nst {ψ : ℝ → ℝ} (hψ : ψ ∈ Nst setting) {η : ℝ} (hη : 0 < η) :
    ∃ (v : Pot) (ρ' : StrongDual ℝ Pot), ‖ρ' - densL hψ‖ ≤ η ∧
      (∀ w, gsEr w ≤ gsEr v + ρ' (w - v)) ∧ liebF setting ρ' = ((gsEr v - ρ' v : ℝ) : EReal) :=
  dense_supergrad (densL hψ) (liebF_le_h0 hψ) hη

end Box

end Continuum

end DFT
