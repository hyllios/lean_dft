/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.General.HK
import DFT.Continuum.Line.FreeFermions
import DFT.Continuum.Sine.Coeff

/-!
# Which densities come from states on a line (`N`-representability)

Densities of `N = n + 1` particles on `[0, 1]`, as functionals `v ↦ ∫₀¹ v ρ`. Every
`ρ = N g²` with `g ∈ C²`, `g(0) = g(1) = 0` and `∫₀¹ g² = 1` is the density of a normalised
bosonic state (the product `Π g(x_k)`) and of a normalised fermionic state (a Slater determinant
of the real Harriman-type orbitals `g · e_j(F)`, `F(x) = ∫₀ˣ g²`, where `e_j` runs over `1` (if
`N` is odd) and pairs `√2 cos(2π k u)`, `√2 sin(2π k u)`, so that `Σ_j e_j² = N`). In particular
the Lieb functional is finite at every such density.

* `integral_prod_cube`: Fubini for products on the cube.
* `integral_W_slater`, `integral_slater_sq`, `integral_LN_slater`: the norm and the density of a
  Slater determinant of orthonormal orbitals: `∫ det² = N!` and
  `∫ (Σ_k v(x_k)) det² = N! Σ_j ∫ v φ_j²`.
* `nrep_bos`, `nrep_fer`: **`N`-representability**; `liebF_lt_top_bos`, `liebF_lt_top_fer`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real

variable {n : ℕ}

/-- Fubini for products on the cube. -/
lemma integral_prod_cube (f : Fin (n + 1) → ℝ → ℝ) :
    ∫ x, ∏ i, f i (x i) ∂μN n = ∏ i, ∫ t, f i t ∂μ1 := by
  rw [Sine.muN_eq]
  exact integral_fintype_prod_eq_prod (f := f)

lemma prod_ite_mul (k : Fin (n + 1)) (a b : Fin (n + 1) → ℝ) :
    ∏ i, (if i = k then a i * b i else b i) = a k * ∏ i, b i := by
  calc ∏ i, (if i = k then a i * b i else b i) = ∏ i, ((if i = k then a i else 1) * b i) :=
        Finset.prod_congr rfl fun i _ => by split_ifs <;> ring
    _ = (∏ i, if i = k then a i else 1) * ∏ i, b i := Finset.prod_mul_distrib
    _ = a k * ∏ i, b i := by
        rw [Finset.prod_eq_single k (fun i _ hi => ite_eq_right hi)
          (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl]

/-! ### Bosons: the product state -/

section bos

variable {w : Cfg n → ℝ} {hw : Continuous w} {g : ℝ → ℝ}

lemma integral_LN_mul (v : Pot) {F : Cfg n → ℝ} (hF : Continuous F) :
    ∫ x, LN n v x * F x ∂μN n = ∑ k, ∫ x, ext v (x k) * F x ∂μN n := by
  rw [← integral_finsetSum (f := fun k x => ext v (x k) * F x) _ fun k _ => integrableN
    (((continuous_ext v).comp (continuous_apply k)).mul hF)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change (∑ k, ext v (x k)) * F x = _
  rw [Finset.sum_mul]

/-- **Bosonic `N`-representability**: `Π g(x_k)` is normalised with density `N g²`. -/
theorem nrep_bos (hg : g ∈ Box.Dom) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    prodS (n := n) g ∈ Nst (setting .bos n w hw) ∧
      ∀ v, dens (setting .bos n w hw) (prodS g) v = ∫ t, ext v t * ((n + 1) * g t ^ 2) ∂μ1 := by
  have hgc := hg.1.continuous
  have hsq : ∀ x : Cfg n, prodS g x * prodS g x = ∏ i, g (x i) ^ 2 := fun x => by
    simp only [prodS, ← Finset.prod_mul_distrib, sq]
  have hip : ip (μ := μN n) (prodS g) (prodS g) = 1 := by
    simp only [ip, hsq, integral_prod_cube (fun _ t => g t ^ 2), hnorm, Finset.prod_const_one]
  refine ⟨⟨prodS_mem hg, hip⟩, fun v => ?_⟩
  have hPc : Continuous fun x : Cfg n => prodS g x * prodS g x :=
    (prodS_mem hg).1.continuous.mul (prodS_mem hg).1.continuous
  change ∫ x, LN n v x * (prodS g x * prodS g x) ∂μN n = _
  rw [integral_LN_mul v hPc]
  have hk : ∀ k : Fin (n + 1), ∫ x, ext v (x k) * (prodS g x * prodS g x) ∂μN n =
      ∫ t, ext v t * g t ^ 2 ∂μ1 := fun k => by
    have e : (fun x : Cfg n => ext v (x k) * (prodS g x * prodS g x)) = fun x =>
        ∏ i, (if i = k then fun t => ext v t * g t ^ 2 else fun t => g t ^ 2) (x i) := by
      funext x
      rw [hsq, ← prod_ite_mul k (fun i => ext v (x i)) (fun i => g (x i) ^ 2)]
      exact Finset.prod_congr rfl fun i _ => by split_ifs with h <;> simp [h]
    rw [e, integral_prod_cube]
    simp only [apply_ite (fun f : ℝ → ℝ => ∫ t, f t ∂μ1), hnorm]
    rw [Finset.prod_eq_single k (fun i _ hi => ite_eq_right hi)
      (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl]
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← integral_const_mul]
  push_cast
  exact integral_congr_ae (ae_of_all _ fun t => by ring)

end bos

/-! ### The norm and density of a Slater determinant -/

section slater

variable {φ : Fin (n + 1) → ℝ → ℝ}

lemma slater_eq_sum (φ : Fin (n + 1) → ℝ → ℝ) (x : Cfg n) :
    slater φ x = ∑ σ : Equiv.Perm (Fin (n + 1)), sgn σ * ∏ i, φ (σ i) (x i) := by
  rw [slater, ← Matrix.det_transpose, Matrix.det_apply']
  rfl

/-- Two permutations that agree off one point are equal. -/
lemma perm_eq_of_agree {σ τ : Equiv.Perm (Fin (n + 1))} (k : Fin (n + 1))
    (h : ∀ i, i ≠ k → σ i = τ i) : σ = τ := by
  refine Equiv.ext fun i => ?_
  by_cases hi : i = k
  · subst hi
    by_contra hne
    have hm : τ.symm (σ i) ≠ i := fun hm => hne ((τ.symm_apply_eq).1 hm)
    have h2 := h _ hm
    rw [Equiv.apply_symm_apply] at h2
    exact hm (σ.injective h2)
  · exact h i hi

/-- The weighted square of a Slater determinant, integrated. -/
lemma integral_W_slater (W : Fin (n + 1) → ℝ → ℝ) (hW : ∀ i, Continuous (W i))
    (hφ : ∀ j, Continuous (φ j)) :
    ∫ x, (∏ i, W i (x i)) * (slater φ x * slater φ x) ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ τ : Equiv.Perm (Fin (n + 1)),
        sgn σ * sgn τ * ∏ i, ∫ t, W i t * (φ (σ i) t * φ (τ i) t) ∂μ1 := by
  have e : ∀ x : Cfg n, (∏ i, W i (x i)) * (slater φ x * slater φ x) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ τ : Equiv.Perm (Fin (n + 1)),
        sgn σ * sgn τ * ∏ i, (W i (x i) * (φ (σ i) (x i) * φ (τ i) (x i))) := fun x => by
    rw [slater_eq_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Finset.prod_mul_distrib]
    ring
  have hc : ∀ (σ τ : Equiv.Perm (Fin (n + 1))), Continuous fun x : Cfg n =>
      sgn σ * sgn τ * ∏ i, (W i (x i) * (φ (σ i) (x i) * φ (τ i) (x i))) := fun σ τ => by
    fun_prop
  simp only [e]
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ => integrableN (hc σ τ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ fun τ _ => integrableN (hc σ τ)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul,
    integral_prod_cube (fun i t => W i t * (φ (σ i) t * φ (τ i) t))]

variable (hφ : ∀ j, Continuous (φ j))
  (hon : ∀ a b, ∫ t, φ a t * φ b t ∂μ1 = if a = b then 1 else 0)
include hφ hon

/-- With one weighted coordinate, only the diagonal `σ = τ` survives. -/
lemma integral_W1_slater (k : Fin (n + 1)) {V : ℝ → ℝ} (hV : Continuous V) :
    ∫ x, V (x k) * (slater φ x * slater φ x) ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∫ t, V t * (φ (σ k) t * φ (σ k) t) ∂μ1 := by
  set W : Fin (n + 1) → ℝ → ℝ := fun i => if i = k then V else fun _ => 1
  have hW : ∀ i, Continuous (W i) := fun i => by
    simp only [W]; split_ifs
    exacts [hV, continuous_const]
  have hprod : ∀ x : Cfg n, ∏ i, W i (x i) = V (x k) := fun x => by
    simp only [W]
    rw [Finset.prod_eq_single k (fun i _ hi => by simp [hi])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  have h := integral_W_slater W hW hφ
  simp only [hprod] at h
  rw [h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single σ]
  · rw [Finset.prod_eq_single k]
    · simp only [W, ↓reduceIte]
      rw [sgn_mul_self σ, one_mul]
    · intro i _ hi
      simp [W, hi, hon]
    · exact fun h => absurd (Finset.mem_univ k) h
  · intro τ _ hτ
    obtain ⟨i, hik, hi⟩ : ∃ i, i ≠ k ∧ σ i ≠ τ i := by
      by_contra hc
      push Not at hc
      exact hτ (perm_eq_of_agree k hc).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · ring
    · simp [W, hik, hon, hi]
  · exact fun h => absurd (Finset.mem_univ σ) h

/-- **`∫ det² = N!`.** -/
lemma integral_slater_sq :
    ∫ x, slater φ x * slater φ x ∂μN n = (Nat.factorial (n + 1) : ℝ) := by
  have h := integral_W1_slater hφ hon 0 (V := fun _ => 1) continuous_const
  simp only [one_mul, hon, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h

/-- **The density of a Slater determinant**: `∫ (Σ_k v(x_k)) det² = N! Σ_j ∫ v φ_j²`. -/
lemma integral_LN_slater (v : Pot) :
    ∫ x, LN n v x * (slater φ x * slater φ x) ∂μN n =
      (Nat.factorial (n + 1) : ℝ) * ∫ t, ext v t * ∑ j, φ j t ^ 2 ∂μ1 := by
  have hS : Continuous fun x : Cfg n => slater φ x * slater φ x := by
    have : Continuous (slater φ) := by
      rw [show slater φ = fun x => _ from funext (slater_eq_sum φ)]
      exact continuous_finsetSum _ fun σ _ => by fun_prop
    exact this.mul this
  rw [integral_LN_mul v hS]
  simp only [integral_W1_slater hφ hon _ (continuous_ext v)]
  rw [Finset.sum_comm]
  have hj : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∑ k, ∫ t, ext v t * (φ (σ k) t * φ (σ k) t) ∂μ1 =
        ∫ t, ext v t * ∑ j, φ j t ^ 2 ∂μ1 := fun σ => by
    rw [Equiv.sum_comp σ (fun j => ∫ t, ext v t * (φ j t * φ j t) ∂μ1),
      ← integral_finsetSum (f := fun j t => ext v t * (φ j t * φ j t)) _
        fun j _ => integrable_of_continuous
        ((continuous_ext v).mul ((hφ j).mul (hφ j)))]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [Finset.mul_sum, sq]
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

end slater

/-! ### Real Harriman orbitals -/

/-- `∫₀¹ cos(2π m u + c) du = [m = 0] cos c` for integers `m`. -/
lemma integral_cos_affine (m : ℤ) (c : ℝ) :
    ∫ u in (0 : ℝ)..1, Real.cos (2 * π * m * u + c) = if m = 0 then Real.cos c else 0 := by
  split_ifs with hm
  · simp [hm]
  · have ha : (2 * π * m : ℝ) ≠ 0 := by
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      positivity
    rw [intervalIntegral.integral_comp_mul_add (fun x => Real.cos x) ha c, integral_cos]
    have : Real.sin (2 * π * m + c) = Real.sin c := by
      rw [show 2 * π * m + c = c + m * (2 * π) by ring, Real.sin_add_int_mul_two_pi]
    simp [this]

/-- The index set of the orbitals: a constant if `N` is odd, and `N / 2` cosine–sine pairs. -/
abbrev Hix (N : ℕ) := Fin (N % 2) ⊕ (Fin (N / 2) × Fin 2)

lemma card_Hix (N : ℕ) : Fintype.card (Hix N) = N := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- The functions `1`, `√2 cos(2π k u)`, `√2 sin(2π k u)` on `[0, 1]`. -/
noncomputable def eH {N : ℕ} : Hix N → ℝ → ℝ
  | .inl _, _ => 1
  | .inr (k, p), u => √2 * Real.cos (2 * π * ((k : ℕ) + 1 : ℕ) * u - (p : ℕ) * (π / 2))

lemma contDiff_eH {N : ℕ} (a : Hix N) : ContDiff ℝ ⊤ (eH a) := by
  rcases a with a | ⟨k, p⟩
  · exact contDiff_const
  · exact contDiff_const.mul (Real.contDiff_cos.comp (by fun_prop))

lemma sum_eH_sq (N : ℕ) (u : ℝ) : ∑ a : Hix N, eH a u ^ 2 = N := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [eH, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_mul,
    sub_zero, one_mul, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Real.cos_sub_pi_div_two]
  have : ∀ k : Fin (N / 2), 2 * Real.cos (2 * π * ((k : ℕ) + 1 : ℕ) * u) ^ 2 +
      2 * Real.sin (2 * π * ((k : ℕ) + 1 : ℕ) * u) ^ 2 = 2 := fun k => by
    nlinarith [Real.sin_sq_add_cos_sq (2 * π * ((k : ℕ) + 1 : ℕ) * u)]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := Nat.mod_add_div N 2
  have : ((N % 2 : ℕ) : ℝ) + ((N / 2 : ℕ) : ℝ) * 2 = N := by
    exact_mod_cast (by omega : N % 2 + N / 2 * 2 = N)
  linarith

lemma two_cos_mul (A B : ℝ) : √2 * Real.cos A * (√2 * Real.cos B) =
    Real.cos (A - B) + Real.cos (A + B) := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Real.cos_sub, Real.cos_add]
  linear_combination Real.cos A * Real.cos B * h2

lemma integral_cos_nat (k : ℕ) (c : ℝ) :
    ∫ u in (0 : ℝ)..1, Real.cos (2 * π * ((k + 1 : ℕ) : ℝ) * u - c) = 0 := by
  have := integral_cos_affine ((k + 1 : ℕ) : ℤ) (-c)
  rw [ite_eq_right (by omega)] at this
  refine Eq.trans ?_ this
  exact intervalIntegral.integral_congr fun u _ => by congr 1

lemma integral_cos_pair (k k' : ℕ) (p p' : Fin 2) :
    ∫ u in (0 : ℝ)..1, √2 * Real.cos (2 * π * ((k + 1 : ℕ) : ℝ) * u - (p : ℕ) * (π / 2)) *
      (√2 * Real.cos (2 * π * ((k' + 1 : ℕ) : ℝ) * u - (p' : ℕ) * (π / 2))) =
      if k = k' ∧ p = p' then 1 else 0 := by
  have e : ∀ u : ℝ, √2 * Real.cos (2 * π * ((k + 1 : ℕ) : ℝ) * u - (p : ℕ) * (π / 2)) *
      (√2 * Real.cos (2 * π * ((k' + 1 : ℕ) : ℝ) * u - (p' : ℕ) * (π / 2))) =
      Real.cos (2 * π * (((k : ℤ) - k' : ℤ) : ℝ) * u + ((p' : ℕ) - (p : ℕ)) * (π / 2)) +
      Real.cos (2 * π * (((k : ℤ) + k' + 2 : ℤ) : ℝ) * u - ((p : ℕ) + (p' : ℕ)) * (π / 2)) := by
    intro u
    have eA : 2 * π * (((k : ℤ) - k' : ℤ) : ℝ) * u + ((p' : ℕ) - (p : ℕ)) * (π / 2) =
        (2 * π * ((k + 1 : ℕ) : ℝ) * u - (p : ℕ) * (π / 2)) -
          (2 * π * ((k' + 1 : ℕ) : ℝ) * u - (p' : ℕ) * (π / 2)) := by push_cast; ring
    have eB : 2 * π * (((k : ℤ) + k' + 2 : ℤ) : ℝ) * u - ((p : ℕ) + (p' : ℕ)) * (π / 2) =
        (2 * π * ((k + 1 : ℕ) : ℝ) * u - (p : ℕ) * (π / 2)) +
          (2 * π * ((k' + 1 : ℕ) : ℝ) * u - (p' : ℕ) * (π / 2)) := by push_cast; ring
    rw [eA, eB]
    exact two_cos_mul _ _
  simp only [e]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show (fun u : ℝ => Real.cos (2 * π * (((k : ℤ) + k' + 2 : ℤ) : ℝ) * u -
      ((p : ℕ) + (p' : ℕ)) * (π / 2))) =
      fun u => Real.cos (2 * π * (((k : ℤ) + k' + 2 : ℤ) : ℝ) * u +
      -(((p : ℕ) + (p' : ℕ)) * (π / 2))) from funext fun u => by ring_nf]
  rw [integral_cos_affine, integral_cos_affine,
    ite_eq_right (show ((k : ℤ) + k' + 2) ≠ 0 by omega), add_zero]
  by_cases hk : k = k'
  · subst hk
    simp only [sub_self, ↓reduceIte, true_and]
    fin_cases p <;> fin_cases p' <;> simp
  · rw [ite_eq_right (show ((k : ℤ) - k') ≠ 0 by omega), ite_eq_right (by tauto)]

/-- **The functions `eH` are orthonormal on `[0, 1]`.** -/
lemma integral_eH (N : ℕ) (a b : Hix N) :
    ∫ u in (0 : ℝ)..1, eH a u * eH b u = if a = b then 1 else 0 := by
  rcases a with a | ⟨k, p⟩ <;> rcases b with b | ⟨k', p'⟩
  · have : a = b := Fin.ext (by have := a.2; have := b.2; have := Nat.mod_lt N two_pos; omega)
    simp [eH, this]
  · simp only [eH, one_mul, reduceCtorEq, ↓reduceIte]
    rw [intervalIntegral.integral_const_mul, integral_cos_nat, mul_zero]
  · simp only [eH, mul_one, reduceCtorEq, ↓reduceIte]
    rw [intervalIntegral.integral_const_mul, integral_cos_nat, mul_zero]
  · simp only [eH]
    rw [integral_cos_pair]
    simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.val_inj]

/-! ### The change of variables `u = F(x)` -/

section change

variable {g : ℝ → ℝ} (hg : g ∈ Box.Dom) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1)

/-- The normalised cumulative density `F(x) = ∫₀ˣ g²`. -/
noncomputable def cumF (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, g t ^ 2

include hg in
lemma hasDerivAt_cumF (x : ℝ) : HasDerivAt (cumF g) (g x ^ 2) x :=
  ((hg.1.continuous.pow 2).integral_hasStrictDerivAt 0 x).hasDerivAt

include hg in
lemma contDiff_cumF : ContDiff ℝ 2 (cumF g) := by
  have hd : deriv (cumF g) = fun x => g x ^ 2 := funext fun x => (hasDerivAt_cumF hg x).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_cumF hg x).differentiableAt, by simp, ?_⟩
  rw [hd]
  exact (hg.1.of_le (by norm_num)).pow 2

include hg hnorm in
/-- **Change of variables**: `∫₀¹ g(x)² h(F(x)) dx = ∫₀¹ h(u) du`. -/
lemma integral_cumF {h : ℝ → ℝ} (hh : Continuous h) :
    ∫ t, g t ^ 2 * h (cumF g t) ∂μ1 = ∫ u in (0 : ℝ)..1, h u := by
  have h0 : cumF g 0 = 0 := intervalIntegral.integral_same
  have h1 : cumF g 1 = 1 := by rw [cumF, ← Box.integral_mu1, hnorm]
  rw [Box.integral_mu1]
  have := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := 1) (f := cumF g)
    (f' := fun x => g x ^ 2) (g := h) (fun x _ => hasDerivAt_cumF hg x)
    (hg.1.continuous.pow 2).continuousOn hh
  rw [h0, h1] at this
  rw [← this]
  exact intervalIntegral.integral_congr fun x _ => by simp only [Function.comp]; ring

end change

/-! ### Fermions: the Slater determinant of Harriman orbitals -/

section fer

variable {w : Cfg n → ℝ} {hw : Continuous w} {g : ℝ → ℝ}

/-- **Fermionic `N`-representability**: every density `N g²` (`g ∈ C²`, `g(0) = g(1) = 0`,
`∫ g² = 1`) is the density of a normalised antisymmetric state. -/
theorem nrep_fer (hg : g ∈ Box.Dom) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    ∃ ψ ∈ Nst (setting .fer n w hw),
      ∀ v, dens (setting .fer n w hw) ψ v = ∫ t, ext v t * ((n + 1) * g t ^ 2) ∂μ1 := by
  set N := n + 1
  let e : Fin N ≃ Hix N := (Fintype.equivFinOfCardEq (card_Hix N)).symm
  set φ : Fin N → ℝ → ℝ := fun j x => g x * eH (e j) (cumF g x)
  have hgc := hg.1.continuous
  have hφD : ∀ j, φ j ∈ Box.Dom := fun j =>
    ⟨hg.1.mul (((contDiff_eH (e j)).of_le le_top).comp (contDiff_cumF hg)),
      by simp [φ, hg.2.1], by simp [φ, hg.2.2]⟩
  have hφc : ∀ j, Continuous (φ j) := fun j => (hφD j).1.continuous
  have hon : ∀ a b, ∫ t, φ a t * φ b t ∂μ1 = if a = b then 1 else 0 := fun a b => by
    have := integral_cumF hg hnorm (h := fun u => eH (e a) u * eH (e b) u)
      (((contDiff_eH _).continuous).mul (contDiff_eH _).continuous)
    simp only [integral_eH, e.injective.eq_iff] at this
    rw [← this]
    exact integral_congr_ae (ae_of_all _ fun t => by simp only [φ]; ring)
  have hsum : ∀ t, ∑ j, φ j t ^ 2 = N * g t ^ 2 := fun t => by
    simp only [φ, mul_pow, ← Finset.mul_sum]
    rw [e.sum_comp (fun a => eH a (cumF g t) ^ 2), sum_eH_sq]; ring
  have hfac : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  set c := (√(Nat.factorial N : ℝ))⁻¹
  have hc2 : c * c * (Nat.factorial N : ℝ) = 1 := by
    simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hfac.le, inv_mul_cancel₀ hfac.ne']
  have hD : c • slater φ ∈ DomF n := (DomF n).smul_mem c (slater_mem hφD)
  refine ⟨c • slater φ, ⟨hD, ?_⟩, fun v => ?_⟩
  · change ∫ x, (c • slater φ) x * (c • slater φ) x ∂μN n = 1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (fun x => c * slater φ x * (c * slater φ x)) =
      fun x => (c * c) * (slater φ x * slater φ x) from funext fun x => by ring,
      integral_const_mul, integral_slater_sq hφc hon, hc2]
  · change ∫ x, LN n v x * ((c • slater φ) x * (c • slater φ) x) ∂μN n = _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (fun x => LN n v x * (c * slater φ x * (c * slater φ x))) =
      fun x => (c * c) * (LN n v x * (slater φ x * slater φ x)) from funext fun x => by ring,
      integral_const_mul, integral_LN_slater hφc hon, ← mul_assoc, hc2, one_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [hsum t]
    simp only [N]
    push_cast
    ring

end fer

/-! ### The Lieb functional is finite at every such density -/

/-- The density `v ↦ ∫₀¹ v · N g²`. -/
noncomputable def rhoG (n : ℕ) (g : ℝ → ℝ) (v : Pot) : ℝ := ∫ t, ext v t * ((n + 1) * g t ^ 2) ∂μ1

theorem liebF_ne_top {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w} {g : ℝ → ℝ}
    (hg : g ∈ Box.Dom) (hnorm : ∫ t, g t ^ 2 ∂μ1 = 1) :
    liebF (setting τ n w hw) (rhoG n g) ≠ ⊤ := by
  obtain ⟨ψ, hψ, hd⟩ : ∃ ψ ∈ Nst (setting τ n w hw),
      ∀ v, dens (setting τ n w hw) ψ v = rhoG n g v := by
    cases τ
    · exact ⟨_, (nrep_bos hg hnorm).1, (nrep_bos hg hnorm).2⟩
    · exact nrep_fer hg hnorm
  have h := liebF_le_h0 hψ
  rw [show dens (setting τ n w hw) ψ = rhoG n g from funext hd] at h
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h

end DFT.Continuum.Line
