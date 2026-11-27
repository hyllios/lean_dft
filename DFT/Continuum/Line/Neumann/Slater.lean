/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.H1.Represent
import DFT.Continuum.Line.Neumann.Slices

/-!
# Slater determinants and product states of `H¹` orbitals (Neumann walls)

For orbitals `e_j ∈ H1E`, orthonormal in `L²(0, 1)`, read as continuous functions
`orbF e_j = t ↦ e_j(projIcc t)`:

* the normalised Slater determinant `Ψ = det [e_j(x_i)] / √N!` (`slN`) is a fermionic Neumann
  state with `∫ Ψ² = 1`, kinetic energy `Σ_j ∫ e_j'²` (**`kinN_slN`**) and density `Σ_j e_j²`
  (**`rhoE_slN`**); its energy in `v` is `Σ_j (∫ e_j'² + v(e_j²))`;
* the product state `e(x₀) ⋯ e(xₙ)` (`prN`) is a bosonic Neumann state with kinetic energy
  `N ∫ e'²` and density `N e²`.

The kinetic energy of the determinant: `∂ₖ det = Σ_σ sgn σ ⊗_i u^σ_i` with `u^σ_k = e'_{σ k}`, and
`∫ ⊗_i a_i ⊗_i c_i = Π_i ∫ a_i c_i`; orthonormality leaves only `σ = τ` (`perm_eq_of_agree`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology
open scoped InnerProductSpace

variable {n : ℕ}

/-! ### Orbitals -/

/-- An element of `H1E` as a continuous function, constant outside `[0, 1]`. -/
noncomputable def orbF (e : H1E) : ℝ → ℝ := iccExt (evE e)

lemma continuous_orbF (e : H1E) : Continuous (orbF e) := continuous_iccExt _

lemma orbF_eq (e : H1E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : orbF e t = fnE e t := ext_evE ht

lemma h1N_orbF (e : H1E) : H1N (orbF e) := (h1N_fnE e).congr fun _ ht => (orbF_eq e ht).symm

lemma kinM_orbF (e : H1E) : kinM (orbF e) = ‖e.snd‖ ^ 2 := by
  rw [← kinM_fnE]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    simp only [H1N.deriv_eq_of_eqOn (fun s hs => orbF_eq e hs) ht]

lemma integral_orbF_mul (e h : H1E) : ∫ t, orbF e t * orbF h t ∂vol01 = ⟪JE e, JE h⟫_ℝ := by
  rw [inner_JE]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    simp only [orbF_eq _ (Ioo_subset_Icc_self ht)]

lemma intU_dE (u : C01) (e : H1E) : intU u (dE e) = ∫ t, iccExt u t * orbF e t ^ 2 ∂vol01 := by
  rw [intU_apply]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    have htI := Ioo_subset_Icc_self ht
    simp only [ext_evE htI, fnE_dE _ htI, orbF_eq _ htI, sq]

/-- `∫ (⊗ a)(⊗ c) = Π ∫ a_i c_i` on the cube. -/
lemma integral_tens_mul (a c : Fin (n + 1) → ℝ → ℝ) :
    ∫ x, tens a x * tens c x ∂μN n = ∏ i, ∫ t, a i t * c i t ∂vol01 := by
  have e : ∀ x : Cfg n, tens a x * tens c x = ∏ i, (a i (x i) * c i (x i)) := fun x => by
    simp only [tens, Finset.prod_mul_distrib]
  simp only [e]
  exact integral_prod_cube (fun i t => a i t * c i t)

/-! ### Slater determinants -/

section slater

variable (e : Fin (n + 1) → H1E)

/-- The orbitals as functions. -/
noncomputable def orbs : Fin (n + 1) → ℝ → ℝ := fun j => orbF (e j)

/-- **The normalised Slater determinant** `det [e_j(x_i)] / √N!`. -/
noncomputable def slN : Cfg n → ℝ := (√(Nat.factorial (n + 1) : ℝ))⁻¹ • slater (orbs e)

lemma slater_orbs_memN : slater (orbs e) ∈ DomN .fer n :=
  slater_memN (φ := orbs e) (fun j => h1N_orbF (e j)) (fun j => continuous_orbF (e j))

lemma slN_memN : slN e ∈ DomN .fer n := Submodule.smul_mem _ _ (slater_orbs_memN e)

variable {e} (hon : ∀ a b, ⟪JE (e a), JE (e b)⟫_ℝ = if a = b then 1 else 0)
include hon

lemma orbs_on (a b : Fin (n + 1)) :
    ∫ t, orbs e a t * orbs e b t ∂vol01 = if a = b then 1 else 0 := by
  simp only [orbs, integral_orbF_mul, hon]

lemma integral_slN_sq : ∫ x, slN e x * slN e x ∂μN n = 1 := by
  have h := integral_slater_sq (φ := orbs e) (fun j => continuous_orbF (e j)) (orbs_on hon)
  have hf : (0 : ℝ) < Nat.factorial (n + 1) := by exact_mod_cast Nat.factorial_pos _
  simp only [slN, Pi.smul_apply, smul_eq_mul]
  have e1 : (fun x => (√(Nat.factorial (n + 1) : ℝ))⁻¹ * slater (orbs e) x *
      ((√(Nat.factorial (n + 1) : ℝ))⁻¹ * slater (orbs e) x)) =
      fun x => ((Nat.factorial (n + 1) : ℝ))⁻¹ * (slater (orbs e) x * slater (orbs e) x) := by
    funext x
    have : (√(Nat.factorial (n + 1) : ℝ))⁻¹ * (√(Nat.factorial (n + 1) : ℝ))⁻¹ =
        ((Nat.factorial (n + 1) : ℝ))⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hf.le]
    rw [← this]; ring
  rw [e1, integral_const_mul, h, inv_mul_cancel₀ hf.ne']

/-- The weak derivative of the determinant along `k`, one term per permutation. -/
noncomputable def dSl (k : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) : Fin (n + 1) → ℝ → ℝ :=
  Function.update (fun i => orbs e (σ i)) k (deriv (orbs e (σ k)))

omit hon in
lemma memLp_tens_dSl (k : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
    MemLp (tens (dSl (e := e) k σ)) 2 (μN n) :=
  (isWDN_tens (fun i => h1N_orbF (e (σ i))) (fun i => continuous_orbF (e (σ i))) k).1

/-- `∫ (∂ₖ det)² = Σ_σ ∫ e_{σ k}'²`: only the diagonal survives. -/
lemma integral_dSl_sq (k : Fin (n + 1)) :
    ∫ x, (∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ * tens (dSl (e := e) k σ) x) *
      (∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ * tens (dSl (e := e) k σ) x) ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ‖(e (σ k)).snd‖ ^ 2 := by
  have hm := memLp_tens_dSl (e := e) k
  have hpt : ∀ x, (∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ * tens (dSl (e := e) k σ) x) *
      (∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ * tens (dSl (e := e) k σ) x) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ τ : Equiv.Perm (Fin (n + 1)),
        sgn σ * sgn τ * (tens (dSl (e := e) k σ) x * tens (dSl (e := e) k τ) x) := fun x => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
  have hint : ∀ σ τ : Equiv.Perm (Fin (n + 1)), Integrable (fun x =>
      sgn σ * sgn τ * (tens (dSl (e := e) k σ) x * tens (dSl (e := e) k τ) x)) (μN n) :=
    fun σ τ => ((hm σ).integrable_mul (hm τ)).const_mul _
  simp only [hpt]
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ => hint σ τ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ fun τ _ => hint σ τ, Finset.sum_eq_single σ]
  · rw [integral_const_mul, integral_tens_mul, Finset.prod_eq_single k]
    · simp only [dSl, Function.update_self]
      rw [sgn_mul_self σ, one_mul]
      have := kinM_orbF (e (σ k))
      simp only [kinM] at this
      simpa only [orbs, sq] using this
    · intro i _ hik
      simp only [dSl, Function.update_of_ne hik, orbs_on hon, ↓reduceIte]
    · exact fun h => absurd (Finset.mem_univ k) h
  · intro τ _ hτ
    obtain ⟨i, hik, hi⟩ : ∃ i, i ≠ k ∧ σ i ≠ τ i := by
      by_contra hc
      push Not at hc
      exact hτ (perm_eq_of_agree k hc).symm
    rw [integral_const_mul, integral_tens_mul, Finset.prod_eq_zero (Finset.mem_univ i)]
    · ring
    · simp only [dSl, Function.update_of_ne hik, orbs_on hon, hi, ↓reduceIte]
  · exact fun h => absurd (Finset.mem_univ σ) h

/-- **The kinetic energy of a Slater determinant**: `T(det) = N! Σ_j ∫ e_j'²`. -/
lemma kinN_slater_orbs :
    kinN (slater (orbs e)) = (Nat.factorial (n + 1) : ℝ) * ∑ j, ‖(e j).snd‖ ^ 2 := by
  have hk : ∀ k, ∫ x, dWN k (slater (orbs e)) x * dWN k (slater (orbs e)) x ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ‖(e (σ k)).snd‖ ^ 2 := fun k => by
    rw [← integral_dSl_sq hon k]
    refine integral_congr_ae ?_
    filter_upwards [dWN_ae_eq (isWDN_slater (φ := orbs e) (fun j => h1N_orbF (e j))
      (fun j => continuous_orbF (e j)) k)] with x hx
    rw [hx]; rfl
  simp only [kinN, hk]
  rw [Finset.sum_comm]
  simp only [fun σ : Equiv.Perm (Fin (n + 1)) =>
    Equiv.sum_comp σ (fun j => ‖(e j).snd‖ ^ 2), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- **The kinetic energy of the normalised determinant** is `Σ_j ∫ e_j'²`. -/
theorem kinN_slN : kinN (slN e) = ∑ j, ‖(e j).snd‖ ^ 2 := by
  have hf : (0 : ℝ) < Nat.factorial (n + 1) := by exact_mod_cast Nat.factorial_pos _
  rw [slN, kinN_smul (h1NW_of_mem (slater_orbs_memN e)), kinN_slater_orbs hon, inv_pow,
    Real.sq_sqrt hf.le, ← mul_assoc, inv_mul_cancel₀ hf.ne', one_mul]

/-- **The density of the normalised determinant** is `Σ_j e_j²`. -/
theorem rhoE_slN : rhoE .fer (slN e) = ∑ j, dE (e j) := by
  have hf : (0 : ℝ) < Nat.factorial (n + 1) := by exact_mod_cast Nat.factorial_pos _
  refine eq_of_int fun u => ?_
  rw [int_rhoE (slN_memN e), ← intU_apply, map_sum]
  simp only [intU_dE]
  have hL := integral_LN_slater (φ := orbs e) (fun j => continuous_orbF (e j)) (orbs_on hon) u
  have hpt : ∀ x : Cfg n, (∑ k, iccExt u (x k)) * (slN e x * slN e x) =
      ((Nat.factorial (n + 1) : ℝ))⁻¹ * (LN n u x * (slater (orbs e) x * slater (orbs e) x)) :=
    fun x => by
      simp only [slN, Pi.smul_apply, smul_eq_mul, LN, LinearMap.coe_mk, AddHom.coe_mk]
      have : (√(Nat.factorial (n + 1) : ℝ))⁻¹ * (√(Nat.factorial (n + 1) : ℝ))⁻¹ =
          ((Nat.factorial (n + 1) : ℝ))⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hf.le]
      rw [← this]; ring
  rw [pfN]
  simp only [hpt]
  rw [integral_const_mul, hL, ← mul_assoc, inv_mul_cancel₀ hf.ne', one_mul,
    ← integral_finsetSum _ fun j _ => integrable_of_continuous
      (F := fun t => iccExt u t * orbF (e j) t ^ 2)
      ((continuous_iccExt u).mul ((continuous_orbF (e j)).pow 2))]
  congr 1; funext t
  rw [Finset.mul_sum]
  rfl

/-- **The energy of the normalised determinant** without interaction. -/
theorem QNH_slN (v : PotH) :
    QNH .fer 0 v (slN e) = ∑ j, (‖(e j).snd‖ ^ 2 + v (dE (e j))) := by
  simp only [QNH, Pi.zero_apply, zero_mul, integral_zero, add_zero, kinN_slN hon, rhoE_slN hon,
    map_sum, Finset.sum_add_distrib]

end slater

/-! ### Product states -/

section product

variable (e : H1E)

/-- **The product state** `e(x₀) ⋯ e(xₙ)`. -/
noncomputable def prN : Cfg n → ℝ := prodS (orbF e)

lemma prN_memN : prN (n := n) e ∈ DomN .bos n := prodS_memN (h1N_orbF e) (continuous_orbF e)

variable {e} (he : ‖JE e‖ = 1)
include he

lemma integral_orbF_sq : ∫ t, orbF e t ^ 2 ∂vol01 = 1 := by
  simp only [sq, integral_orbF_mul, real_inner_self_eq_norm_sq, he, mul_one]

lemma integral_prN_sq : ∫ x, prN (n := n) e x * prN e x ∂μN n = 1 := by
  have h := integral_prodS_sq (n := n) (integral_orbF_sq he)
  simp only [sq] at h
  exact h

theorem kinN_prN : kinN (prN (n := n) e) = ((n : ℝ) + 1) * ‖e.snd‖ ^ 2 := by
  rw [prN, kinN_prodS (h1N_orbF e) (continuous_orbF e) (integral_orbF_sq he), kinM_orbF]

theorem rhoE_prN : rhoE .bos (prN (n := n) e) = ((n : ℝ) + 1) • dE e := by
  refine eq_of_int fun u => ?_
  rw [int_rhoE (prN_memN e), ← intU_apply, map_smul, intU_dE, pfN, smul_eq_mul,
    ← integral_const_mul]
  have h := dens_prodS (n := n) (continuous_orbF e) (integral_orbF_sq he) u
  simp only [LN, LinearMap.coe_mk, AddHom.coe_mk] at h
  rw [prN, h]
  congr 1; funext t; ring

theorem QNH_prN (v : PotH) :
    QNH .bos 0 v (prN (n := n) e) = ((n : ℝ) + 1) * (‖e.snd‖ ^ 2 + v (dE e)) := by
  simp only [QNH, Pi.zero_apply, zero_mul, integral_zero, add_zero, kinN_prN he, rhoE_prN he,
    map_smul, smul_eq_mul]
  ring

end product

end DFT.Continuum.Line
