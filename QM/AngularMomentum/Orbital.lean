/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.Algebra.MvPolynomial.Harmonic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Derivation.Lie
import QM.Spin.SpinRep

/-!
# Orbital angular momentum on harmonic polynomials

On the complex polynomials in `x, y, z` (with `ℏ = 1`) the orbital angular momentum
`L = -i r × ∇` has components `L_x = -i(y∂_z - z∂_y)`, `L_y = -i(z∂_x - x∂_z)`,
`L_z = -i(x∂_y - y∂_x)`. They are derivations, so their commutators are fixed by their values on
`x, y, z`: `[L_x, L_y] = i L_z` and cyclically, and `L_± = L_x ± i L_y`, `L_z` satisfy the su(2)
relations with `L² = L_x² + L_y² + L_z²`. Each `L_k` preserves the degree and commutes with the
Laplacian, so the harmonic polynomials `H_l` of degree `l` are invariant. `(x + iy)^l ∈ H_l` is a
highest weight of `L_z = l`; its ladder spans a copy of the spin-`l` representation, and since
`dim H_l ≤ 2l + 1` (`MvPolynomial.finrank_harmonicSubmodule_le`) this copy is all of `H_l`.

## Main definitions

* `QM.AngularMomentum.Lx`, `Ly`, `Lz`, `Lp`, `Lm`: `L = -i r × ∇` and `L_± = L_x ± i L_y`.
* `QM.AngularMomentum.harmonic l`: the harmonic polynomials of degree `l`, and `LpH`, `LmH`, `LzH`
  the restrictions of `L_±`, `L_z` to it.

## Main results

* `Lx_comm_Ly`, `Ly_comm_Lz`, `Lz_comm_Lx`: `[L_x, L_y] = i L_z` and cyclically.
* `isSU2_L`, `isSU2_L_S2`: the su(2) relations and `L² = L_x² + L_y² + L_z²`.
* `laplacian_Lp`, `laplacian_Lm`, `laplacian_Lz`, `L_mem_harmonic`: `H_l` is invariant.
* `hw_mem_harmonic`, `Lp_hw`, `Lz_hw`: `(x + iy)^l` is a highest weight in `H_l`.
* `finrank_harmonic`: `dim H_l = 2l + 1`.
* `harmonic_spinRep_iso`: `H_l` is a copy of the spin-`l` representation.
* `harmonic_irreducible`, `harmonic_L2`: `H_l` is irreducible and `L² = l(l + 1)` on it.
-/

namespace QM.AngularMomentum

open MvPolynomial Complex Module

/-- Complex polynomials in `x, y, z`. -/
abbrev Poly3 := MvPolynomial (Fin 3) ℂ

/-- The derivation `X_j ∂_i`. -/
noncomputable def xd (j i : Fin 3) : Derivation ℂ Poly3 Poly3 := (X j : Poly3) • pderiv i

/-- `L_x = -i (y ∂_z - z ∂_y)`. -/
noncomputable def Lx : Derivation ℂ Poly3 Poly3 := (-I) • (xd 1 2 - xd 2 1)

/-- `L_y = -i (z ∂_x - x ∂_z)`. -/
noncomputable def Ly : Derivation ℂ Poly3 Poly3 := (-I) • (xd 2 0 - xd 0 2)

/-- `L_z = -i (x ∂_y - y ∂_x)`. -/
noncomputable def Lz : Derivation ℂ Poly3 Poly3 := (-I) • (xd 0 1 - xd 1 0)

/-- The raising operator `L₊ = L_x + i L_y`. -/
noncomputable def Lp : Derivation ℂ Poly3 Poly3 := Lx + I • Ly

/-- The lowering operator `L₋ = L_x - i L_y`. -/
noncomputable def Lm : Derivation ℂ Poly3 Poly3 := Lx - I • Ly

lemma xd_apply (j i : Fin 3) (p : Poly3) : xd j i p = X j * pderiv i p := by
  simp [xd]

lemma xd_X (j i k : Fin 3) : xd j i (X k) = if i = k then X j else 0 := by
  classical
  rw [xd_apply, pderiv_X]
  by_cases h : i = k
  · subst h; simp
  · simp [Ne.symm h, h]

/-! ### Commutators -/

/-- The commutator of two derivations as endomorphisms. -/
lemma toEnd_comm (D₁ D₂ : Derivation ℂ Poly3 Poly3) :
    (D₁ : End ℂ Poly3) * D₂ - D₂ * D₁ = (⁅D₁, D₂⁆ : Derivation ℂ Poly3 Poly3) := by
  rw [Derivation.commutator_coe_linear_map, Ring.lie_def]

lemma Lx_X (k : Fin 3) : Lx (X k) = ![0, I • X 2, -I • X 1] k := by
  fin_cases k <;> simp [Lx, xd_X]

lemma Ly_X (k : Fin 3) : Ly (X k) = ![-I • X 2, 0, I • X 0] k := by
  fin_cases k <;> simp [Ly, xd_X]

lemma Lz_X (k : Fin 3) : Lz (X k) = ![I • X 1, -I • X 0, 0] k := by
  fin_cases k <;> simp [Lz, xd_X]

lemma Lp_X (k : Fin 3) : Lp (X k) = ![X 2, I • X 2, -X 0 - I • X 1] k := by
  fin_cases k <;> simp [Lp, Lx_X, Ly_X, smul_smul]
  module

lemma Lm_X (k : Fin 3) : Lm (X k) = ![-X 2, I • X 2, X 0 - I • X 1] k := by
  fin_cases k <;> simp [Lm, Lx_X, Ly_X, smul_smul]
  module

/-- `[L_x, L_y] = i L_z`. -/
theorem Lx_comm_Ly : (Lx : End ℂ Poly3) * Ly - Ly * Lx = I • (Lz : End ℂ Poly3) := by
  rw [toEnd_comm]
  have : ⁅Lx, Ly⁆ = I • Lz := by
    refine MvPolynomial.derivation_ext fun k => ?_
    rw [Derivation.commutator_apply, FunLike.coe_smul, Pi.smul_apply]
    fin_cases k <;> simp [Lx_X, Ly_X, Lz_X, smul_smul]
  rw [this]; ext p; simp

/-- `[L_y, L_z] = i L_x`. -/
theorem Ly_comm_Lz : (Ly : End ℂ Poly3) * Lz - Lz * Ly = I • (Lx : End ℂ Poly3) := by
  rw [toEnd_comm]
  have : ⁅Ly, Lz⁆ = I • Lx := by
    refine MvPolynomial.derivation_ext fun k => ?_
    rw [Derivation.commutator_apply, FunLike.coe_smul, Pi.smul_apply]
    fin_cases k <;> simp [Lx_X, Ly_X, Lz_X, smul_smul]
  rw [this]; ext p; simp

/-- `[L_z, L_x] = i L_y`. -/
theorem Lz_comm_Lx : (Lz : End ℂ Poly3) * Lx - Lx * Lz = I • (Ly : End ℂ Poly3) := by
  rw [toEnd_comm]
  have : ⁅Lz, Lx⁆ = I • Ly := by
    refine MvPolynomial.derivation_ext fun k => ?_
    rw [Derivation.commutator_apply, FunLike.coe_smul, Pi.smul_apply]
    fin_cases k <;> simp [Lx_X, Ly_X, Lz_X, smul_smul]
  rw [this]; ext p; simp

/-- **The su(2) relations** for `L₊`, `L₋`, `L_z`. -/
theorem isSU2_L : IsSU2 (Lp : End ℂ Poly3) Lm Lz where
  comm_pm := by
    rw [toEnd_comm]
    have : ⁅Lp, Lm⁆ = (2 : ℂ) • Lz := by
      refine MvPolynomial.derivation_ext fun k => ?_
      rw [Derivation.commutator_apply, FunLike.coe_smul, Pi.smul_apply]
      fin_cases k <;> simp [Lp_X, Lm_X, Lz_X, smul_smul] <;> module
    rw [this]; ext p; simp
  comm_zp := by
    rw [toEnd_comm]
    have : ⁅Lz, Lp⁆ = Lp := by
      refine MvPolynomial.derivation_ext fun k => ?_
      rw [Derivation.commutator_apply]
      fin_cases k <;> simp [Lp_X, Lz_X, smul_smul]
      module
    rw [this]
  comm_zm := by
    rw [toEnd_comm]
    have : ⁅Lz, Lm⁆ = -Lm := by
      refine MvPolynomial.derivation_ext fun k => ?_
      rw [Derivation.commutator_apply, neg_apply]
      fin_cases k <;> simp [Lm_X, Lz_X, smul_smul]
    rw [this]; ext p; simp

lemma Lp_toEnd : (Lp : End ℂ Poly3) = (Lx : End ℂ Poly3) + I • (Ly : End ℂ Poly3) := by
  ext p; simp [Lp]

lemma Lm_toEnd : (Lm : End ℂ Poly3) = (Lx : End ℂ Poly3) - I • (Ly : End ℂ Poly3) := by
  ext p; simp [Lm]

/-- **`L² = L_x² + L_y² + L_z²`**: the Casimir of the su(2) relations is the sum of the squares
of the components. -/
theorem isSU2_L_S2 : isSU2_L.S2 =
    (Lx : End ℂ Poly3) * Lx + (Ly : End ℂ Poly3) * Ly + (Lz : End ℂ Poly3) * Lz := by
  rw [IsSU2.S2, Lp_toEnd, Lm_toEnd]
  set A : End ℂ Poly3 := Lx.toLinearMap
  set B : End ℂ Poly3 := Ly.toLinearMap
  set Cz : End ℂ Poly3 := Lz.toLinearMap
  have h : A * B = B * A + I • Cz := by rw [← Lx_comm_Ly]; abel
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, h]
  match_scalars <;> ring_nf <;> simp [I_sq]

/-! ### Invariance of the harmonic polynomials -/

/-- `[∂_i, X_a ∂_b] = δ_{ia} ∂_b`. -/
lemma pderiv_xd (i a b : Fin 3) (q : Poly3) :
    pderiv i (xd a b q) = xd a b (pderiv i q) + if i = a then pderiv b q else 0 := by
  classical
  rw [xd_apply, xd_apply, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul,
    pderiv_comm i b]
  by_cases h : i = a
  · subst h; simp
  · simp [Ne.symm h, h]

/-- `Δ (X_a ∂_b q) = X_a ∂_b Δq + 2 ∂_a ∂_b q`. -/
lemma laplacian_xd (a b : Fin 3) (q : Poly3) :
    laplacian (Fin 3) ℂ (xd a b q) =
      xd a b (laplacian (Fin 3) ℂ q) + 2 * pderiv a (pderiv b q) := by
  classical
  simp only [laplacian_apply, pderiv_xd, map_add, map_sum, Finset.sum_add_distrib]
  have e : ∀ i, pderiv i (if i = a then pderiv b q else 0) =
      if i = a then pderiv a (pderiv b q) else 0 := fun i => by
    split_ifs with h
    · rw [h]
    · simp
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    pderiv_comm b a]
  ring

/-- A rotation generator `c (X_a ∂_b - X_b ∂_a)` commutes with the Laplacian. -/
lemma laplacian_rot (c : ℂ) (a b : Fin 3) (q : Poly3) :
    laplacian (Fin 3) ℂ ((c • (xd a b - xd b a)) q) =
      (c • (xd a b - xd b a)) (laplacian (Fin 3) ℂ q) := by
  simp only [FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sub, Pi.sub_apply, map_smul,
    map_sub, laplacian_xd, pderiv_comm a b]
  congr 1; ring

lemma laplacian_Lx (q : Poly3) : laplacian (Fin 3) ℂ (Lx q) = Lx (laplacian (Fin 3) ℂ q) :=
  laplacian_rot _ _ _ q

lemma laplacian_Ly (q : Poly3) : laplacian (Fin 3) ℂ (Ly q) = Ly (laplacian (Fin 3) ℂ q) :=
  laplacian_rot _ _ _ q

lemma laplacian_Lz (q : Poly3) : laplacian (Fin 3) ℂ (Lz q) = Lz (laplacian (Fin 3) ℂ q) :=
  laplacian_rot _ _ _ q

lemma laplacian_Lp (q : Poly3) : laplacian (Fin 3) ℂ (Lp q) = Lp (laplacian (Fin 3) ℂ q) := by
  simp [Lp, laplacian_Lx, laplacian_Ly]

lemma laplacian_Lm (q : Poly3) : laplacian (Fin 3) ℂ (Lm q) = Lm (laplacian (Fin 3) ℂ q) := by
  simp [Lm, laplacian_Lx, laplacian_Ly]

/-- `X_a ∂_b` preserves the degree. -/
lemma xd_mem_homogeneous {n : ℕ} {p : Poly3} (hp : p ∈ homogeneousSubmodule (Fin 3) ℂ n)
    (a b : Fin 3) : xd a b p ∈ homogeneousSubmodule (Fin 3) ℂ n := by
  rw [mem_homogeneousSubmodule] at hp ⊢
  rw [xd_apply]
  rcases n with _ | k
  · obtain ⟨c, rfl⟩ : ∃ c, p = C c :=
      ⟨p.coeff 0, (totalDegree_eq_zero_iff_eq_C).mp
        (Nat.le_zero.mp (hp.totalDegree_le))⟩
    simpa using isHomogeneous_zero (Fin 3) ℂ 0
  · simpa [add_comm] using (isHomogeneous_X ℂ a).mul (hp.pderiv (i := b))

lemma rot_mem_homogeneous {n : ℕ} {p : Poly3} (hp : p ∈ homogeneousSubmodule (Fin 3) ℂ n)
    (c : ℂ) (a b : Fin 3) : (c • (xd a b - xd b a)) p ∈ homogeneousSubmodule (Fin 3) ℂ n := by
  simp only [FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sub, Pi.sub_apply]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (xd_mem_homogeneous hp a b)
    (xd_mem_homogeneous hp b a))

/-- The harmonic polynomials of degree `l`. -/
noncomputable abbrev harmonic (l : ℕ) : Submodule ℂ Poly3 := harmonicSubmodule (Fin 3) ℂ l

/-- **`L₊`, `L₋`, `L_z` map `H_l` to itself.** -/
theorem L_mem_harmonic {l : ℕ} {p : Poly3} (hp : p ∈ harmonic l) :
    Lp p ∈ harmonic l ∧ Lm p ∈ harmonic l ∧ Lz p ∈ harmonic l := by
  have hh : p ∈ homogeneousSubmodule (Fin 3) ℂ l := hp.1
  have hΔ : laplacian (Fin 3) ℂ p = 0 := hp.2
  have hx := rot_mem_homogeneous hh (-I) 1 2
  have hy := rot_mem_homogeneous hh (-I) 2 0
  have hz := rot_mem_homogeneous hh (-I) 0 1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨hz, ?_⟩⟩
  · simp only [Lp, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply]
    exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hy)
  · change laplacian (Fin 3) ℂ (Lp p) = 0
    rw [laplacian_Lp, hΔ, map_zero]
  · simp only [Lm, FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hy)
  · change laplacian (Fin 3) ℂ (Lm p) = 0
    rw [laplacian_Lm, hΔ, map_zero]
  · change laplacian (Fin 3) ℂ (Lz p) = 0
    rw [laplacian_Lz, hΔ, map_zero]

/-! ### The highest weight `(x + iy)^l` -/

/-- `x + iy`. -/
noncomputable def xiy : Poly3 := X 0 + C I * X 1

lemma Lp_xiy : Lp xiy = 0 := by
  have : C I * X 1 = I • (X 1 : Poly3) := (smul_eq_C_mul _ _).symm
  have h0 : Lp (X 0) = X 2 := by simpa using Lp_X 0
  have h1 : Lp (X 1) = I • X 2 := by simpa using Lp_X 1
  rw [xiy, this, map_add, Derivation.map_smul, h0, h1, smul_smul, I_mul_I]
  module

lemma Lz_xiy : Lz xiy = xiy := by
  have : C I * X 1 = I • (X 1 : Poly3) := (smul_eq_C_mul _ _).symm
  have h0 : Lz (X 0) = I • X 1 := by simpa using Lz_X 0
  have h1 : Lz (X 1) = -I • X 0 := by simpa using Lz_X 1
  rw [xiy, this, map_add, Derivation.map_smul, h0, h1, smul_smul]
  simp only [mul_neg, I_mul_I, neg_neg, one_smul]
  abel

/-- `(x + iy)^l` is harmonic of degree `l`. -/
theorem hw_mem_harmonic (l : ℕ) : xiy ^ l ∈ harmonic l :=
  pow_mem_harmonicSubmodule I_mul_I l

/-- `L₊ (x + iy)^l = 0`. -/
theorem Lp_hw (l : ℕ) : Lp (xiy ^ l) = 0 := by
  rw [Derivation.leibniz_pow, Lp_xiy, smul_zero, smul_zero]

/-- `L_z (x + iy)^l = l (x + iy)^l`. -/
theorem Lz_hw (l : ℕ) : Lz (xiy ^ l) = (l : ℂ) • xiy ^ l := by
  rw [Derivation.leibniz_pow, Lz_xiy]
  rcases l with _ | k
  · simp
  · rw [smul_eq_mul, ← pow_succ, Nat.add_sub_cancel, Nat.cast_smul_eq_nsmul]

/-! ### `H_l` is the spin-`l` representation -/

/-- `L₊` on `H_l`. -/
noncomputable def LpH (l : ℕ) : End ℂ (harmonic l) :=
  (Lp : End ℂ Poly3).restrict fun _ hp => (L_mem_harmonic hp).1

/-- `L₋` on `H_l`. -/
noncomputable def LmH (l : ℕ) : End ℂ (harmonic l) :=
  (Lm : End ℂ Poly3).restrict fun _ hp => (L_mem_harmonic hp).2.1

/-- `L_z` on `H_l`. -/
noncomputable def LzH (l : ℕ) : End ℂ (harmonic l) :=
  (Lz : End ℂ Poly3).restrict fun _ hp => (L_mem_harmonic hp).2.2

lemma LpH_apply (l : ℕ) (p : harmonic l) : (LpH l p : Poly3) = Lp p := rfl
lemma LmH_apply (l : ℕ) (p : harmonic l) : (LmH l p : Poly3) = Lm p := rfl
lemma LzH_apply (l : ℕ) (p : harmonic l) : (LzH l p : Poly3) = Lz p := rfl

/-- The su(2) relations on `H_l`. -/
theorem isSU2_LH (l : ℕ) : IsSU2 (LpH l) (LmH l) (LzH l) where
  comm_pm := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := LinearMap.congr_fun isSU2_L.comm_pm (x : Poly3)
    simpa [mul_apply_eq_comp, LpH_apply, LmH_apply, LzH_apply] using this
  comm_zp := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := LinearMap.congr_fun isSU2_L.comm_zp (x : Poly3)
    simpa [mul_apply_eq_comp, LpH_apply, LzH_apply] using this
  comm_zm := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := LinearMap.congr_fun isSU2_L.comm_zm (x : Poly3)
    simpa [mul_apply_eq_comp, LmH_apply, LzH_apply] using this

/-- `(x + iy)^l` as an element of `H_l`. -/
noncomputable def hwH (l : ℕ) : harmonic l := ⟨xiy ^ l, hw_mem_harmonic l⟩

lemma LpH_hwH (l : ℕ) : LpH l (hwH l) = 0 := Subtype.ext (Lp_hw l)

lemma LzH_hwH (l : ℕ) : LzH l (hwH l) = (l : ℂ) • hwH l := Subtype.ext (Lz_hw l)

lemma hwH_ne_zero (l : ℕ) : hwH l ≠ 0 := by
  have hx : xiy ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![1, 0, 0]) h
    simp [xiy] at this
  intro h
  exact pow_ne_zero l hx (congrArg Subtype.val h)

/-- **`H_l` is a copy of the spin-`l` representation**: a linear isomorphism
`V_l = ℂ^{2l+1} ≃ H_l` maps `S₊`, `S₋`, `S_z` to `L₊`, `L₋`, `L_z`. -/
theorem harmonic_spinRep_iso (l : ℕ) :
    ∃ φ : (Fin (2 * l + 1) → ℂ) ≃ₗ[ℂ] harmonic l,
      (φ : (Fin (2 * l + 1) → ℂ) →ₗ[ℂ] harmonic l) ∘ₗ spinSp (2 * l) = LpH l ∘ₗ φ ∧
      (φ : (Fin (2 * l + 1) → ℂ) →ₗ[ℂ] harmonic l) ∘ₗ spinSm (2 * l) = LmH l ∘ₗ φ ∧
      (φ : (Fin (2 * l + 1) → ℂ) →ₗ[ℂ] harmonic l) ∘ₗ spinSz (2 * l) = LzH l ∘ₗ φ := by
  have h := isSU2_LH l
  obtain ⟨N, hN, hN1⟩ := h.exists_ladder_stop (LzH_hwH l) (hwH_ne_zero l)
  have h2 := h.two_m_eq (LpH_hwH l) (LzH_hwH l) hN hN1
  obtain rfl : N = 2 * l := by exact_mod_cast h2.symm
  obtain ⟨φ, hinj, -, h₁, h₂, h₃⟩ := h.exists_spinRep_iso (LpH_hwH l) (LzH_hwH l) hN hN1
  have hrank : finrank ℂ (Fin (2 * l + 1) → ℂ) = finrank ℂ (harmonic l) := by
    have e₁ := LinearMap.finrank_le_finrank_of_injective hinj
    have e₂ : finrank ℂ (harmonic l) ≤ 2 * l + 1 := finrank_harmonicSubmodule_le l
    rw [Module.finrank_fin_fun] at e₁ ⊢
    omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  refine ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, ?_, ?_, ?_⟩ <;>
    refine LinearMap.ext fun x => ?_ <;>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  · exact LinearMap.congr_fun h₁ x
  · exact LinearMap.congr_fun h₂ x
  · exact LinearMap.congr_fun h₃ x

/-- **`dim H_l = 2l + 1`.** -/
theorem finrank_harmonic (l : ℕ) : finrank ℂ (harmonic l) = 2 * l + 1 := by
  obtain ⟨φ, -⟩ := harmonic_spinRep_iso l
  rw [← φ.finrank_eq, Module.finrank_fin_fun]

/-- **`H_l` is irreducible**: a subspace invariant under `L₊` and `L₋` is `⊥` or `⊤`. -/
theorem harmonic_irreducible (l : ℕ) (W : Submodule ℂ (harmonic l))
    (hp : ∀ w ∈ W, LpH l w ∈ W) (hm : ∀ w ∈ W, LmH l w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨φ, h₁, h₂, -⟩ := harmonic_spinRep_iso l
  set f : (Fin (2 * l + 1) → ℂ) →ₗ[ℂ] harmonic l := φ.toLinearMap
  have hW : Submodule.map f (W.comap f) = W :=
    Submodule.map_comap_eq_of_surjective φ.surjective W
  rcases spinRep_irreducible (W.comap f)
      (fun w hw => by
        rw [Submodule.mem_comap, ← LinearMap.comp_apply, h₁, LinearMap.comp_apply]
        exact hp _ hw)
      (fun w hw => by
        rw [Submodule.mem_comap, ← LinearMap.comp_apply, h₂, LinearMap.comp_apply]
        exact hm _ hw) with h | h
  · left; rw [← hW, h, Submodule.map_bot]
  · right; rw [← hW, h, Submodule.map_top, LinearMap.range_eq_top.mpr φ.surjective]

/-- **`L² = l(l + 1)` on `H_l`.** -/
theorem harmonic_L2 {l : ℕ} {p : Poly3} (hp : p ∈ harmonic l) :
    ((Lx : End ℂ Poly3) * Lx + (Ly : End ℂ Poly3) * Ly + (Lz : End ℂ Poly3) * Lz) p =
      ((l : ℂ) * (l + 1)) • p := by
  obtain ⟨φ, h₁, h₂, h₃⟩ := harmonic_spinRep_iso l
  have c₁ : ∀ y, φ (spinSp (2 * l) y) = LpH l (φ y) := fun y => LinearMap.congr_fun h₁ y
  have c₂ : ∀ y, φ (spinSm (2 * l) y) = LmH l (φ y) := fun y => LinearMap.congr_fun h₂ y
  have c₃ : ∀ y, φ (spinSz (2 * l) y) = LzH l (φ y) := fun y => LinearMap.congr_fun h₃ y
  obtain ⟨x, hx⟩ := φ.surjective ⟨p, hp⟩
  have hS := LinearMap.congr_fun (spinRep_S2 (K := ℂ) (2 * l)) x
  simp only [IsSU2.S2, LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self] at hS
  have e := congrArg (fun y => ((φ y : harmonic l) : Poly3)) hS
  simp only [map_add, map_smul, c₁, c₂, c₃, hx, Submodule.coe_add, Submodule.coe_smul,
    LpH_apply, LmH_apply, LzH_apply] at e
  rw [← isSU2_L_S2]
  simp only [IsSU2.S2, LinearMap.add_apply, mul_apply_eq_comp]
  refine e.trans ?_
  congr 1
  push_cast
  ring

end QM.AngularMomentum
