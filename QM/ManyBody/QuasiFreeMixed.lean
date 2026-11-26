/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import ForMathlib.LinearAlgebra.Matrix.CauchyBinet
import QM.ManyBody.QuasiFree

/-!
# Mixed quasi-free states

For occupations `n : Fin M → ℝ` and a unitary `v`, the (gauge-invariant) quasi-free state is the
mixture of the Slater states `U(v)|s⟩` with the product weights
`w_s = Π_k (n_k if k ∈ s else 1 - n_k)`: `ρ = U(v) diag(w) U(v)†` (`quasiFreeOf v n`). Every
Hermitian `γ` with `0 ≤ γ ≤ 1` is `v̄ diag(n) vᵀ` with `0 ≤ n ≤ 1` (natural orbitals), which defines
`quasiFree γ`.

**Wick's theorem** holds for it: `tr(ρ c_{i₀}† ⋯ c_{iₙ₋₁}† c_{jₙ₋₁} ⋯ c_{j₀}) = det (γ_{i_a j_b})`.
Each Slater state gives `det (A D_s B)` with `D_s = diag(occ s)` (Wick for Slater states), and by
Cauchy–Binet `det (A D B) = Σ_K det A_{·K} det B_{K·} Π_{k ∈ K} d_k` is linear in each product
`Π_{k ∈ K} d_k`, whose average over the product weights is `Π_{k ∈ K} n_k`.

## Main definitions

* `confWeight n s`: the product weight of the configuration `s`.
* `quasiFreeOf v n`, `quasiFree γ hγ`: the quasi-free density matrix.

## Main results

* `sum_confWeight`, `sum_confWeight_mul_prod`: the weights sum to `1`, and the average of
  `Π_{k ∈ K} [k ∈ s]` is `Π_{k ∈ K} n_k`.
* `det_mul_diagonal_mul`: `det (A diag(d) B) = Σ_K det A_{·K} det B_{K·} Π_{k ∈ K} d_k`.
* `quasiFree_isDensityMatrix`: `ρ_γ ⪰ 0` and `tr ρ_γ = 1` for `0 ≤ γ ≤ 1`.
* `wick_quasiFree` (**Wick's theorem**) and `rdm1_quasiFree`: `tr(ρ_γ c_i† c_j) = γ_ij`.
-/

namespace QM.ManyBody

open Matrix Finset

variable {M : ℕ}

/-! ### Product weights -/

/-- The weight `Π_k (n_k if k ∈ s else 1 - n_k)` of the configuration `s`. -/
def confWeight (n : Fin M → ℝ) (s : Finset (Fin M)) : ℝ :=
  ∏ k, if k ∈ s then n k else 1 - n k

/-- `Σ_s Π_k (a_k if k ∈ s else b_k) = Π_k (a_k + b_k)`. -/
lemma sum_prod_ite_mem {R : Type*} [CommRing R] (a b : Fin M → R) :
    ∑ s : Finset (Fin M), ∏ k, (if k ∈ s then a k else b k) = ∏ k, (a k + b k) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1
  apply Finset.prod_congr
  · ext k; simp
  · intro k _; rfl

/-- The weights sum to `1`. -/
theorem sum_confWeight (n : Fin M → ℝ) : ∑ s, confWeight n s = 1 := by
  simp only [confWeight]
  rw [sum_prod_ite_mem]
  simp

/-- The average of `Π_{k ∈ K} [k ∈ s]` is `Π_{k ∈ K} n_k`. -/
theorem sum_confWeight_mul_prod (n : Fin M → ℝ) (K : Finset (Fin M)) :
    ∑ s, (confWeight n s : ℂ) * ∏ k ∈ K, (if k ∈ s then (1 : ℂ) else 0) = ∏ k ∈ K, (n k : ℂ) := by
  calc ∑ s, (confWeight n s : ℂ) * ∏ k ∈ K, (if k ∈ s then (1 : ℂ) else 0)
      = ∑ s : Finset (Fin M), ∏ k, (if k ∈ s then (n k : ℂ)
          else (1 - (n k : ℂ)) * (if k ∈ K then 0 else 1)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [confWeight, Complex.ofReal_prod, ← Finset.prod_ite_mem_eq K, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hs : k ∈ s <;> by_cases hK : k ∈ K <;> simp [hs, hK]
    _ = ∏ k, ((n k : ℂ) + (1 - (n k : ℂ)) * (if k ∈ K then 0 else 1)) := sum_prod_ite_mem _ _
    _ = ∏ k ∈ K, (n k : ℂ) := by
        rw [← Finset.prod_ite_mem_eq K]
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hK : k ∈ K <;> simp [hK]

/-! ### Determinants of `A diag(d) B` -/

lemma prod_orderEmbOfFin {p : ℕ} (S : Finset (Fin M)) (h : S.card = p) (f : Fin M → ℂ) :
    ∏ c, f (S.orderEmbOfFin h c) = ∏ k ∈ S, f k := by
  rw [← Finset.prod_coe_sort S f, ← Equiv.prod_comp (S.orderIsoOfFin h).toEquiv]
  simp [Finset.coe_orderIsoOfFin_apply]

/-- `det (A diag(d) B) = Σ_K det A_{·K} det B_{K·} Π_{k ∈ K} d_k`. -/
lemma det_mul_diagonal_mul {p : ℕ} (A : Matrix (Fin p) (Fin M) ℂ) (d : Fin M → ℂ)
    (B : Matrix (Fin M) (Fin p) ℂ) :
    (A * diagonal d * B).det = ∑ S : {S : Finset (Fin M) // S.card = p},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det *
        ∏ k ∈ S.1, d k := by
  rw [det_mul_eq_sum_det_mul_det]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : (A * diagonal d).submatrix id (S.1.orderEmbOfFin S.2) =
      A.submatrix id (S.1.orderEmbOfFin S.2) * diagonal (d ∘ S.1.orderEmbOfFin S.2) := by
    ext a c; simp [mul_diagonal]
  rw [h, det_mul, det_diagonal]
  simp only [Function.comp_apply]
  rw [prod_orderEmbOfFin]
  ring

/-! ### The quasi-free density matrix -/

/-- The diagonal matrix of the weights. -/
noncomputable def qfDiag (n : Fin M → ℝ) : FockOp M := diagonal fun s => (confWeight n s : ℂ)

/-- **The quasi-free state** `U(v) diag(w) U(v)†`. -/
noncomputable def quasiFreeOf (v : Matrix (Fin M) (Fin M) ℂ) (n : Fin M → ℝ) : FockOp M :=
  modeRot v * qfDiag n * (modeRot v)ᴴ

lemma conj_diag_apply (A X : FockOp M) (s : Finset (Fin M)) :
    (Aᴴ * X * A) s s = star (A *ᵥ Pi.single s 1) ⬝ᵥ (X *ᵥ (A *ᵥ Pi.single s 1)) := by
  have hA : A *ᵥ Pi.single s 1 = fun t => A t s := by
    funext t; simp [mulVec, dotProduct, Pi.single_apply]
  rw [hA, Matrix.mul_assoc, Matrix.mul_apply, dotProduct]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [mulVec, dotProduct, Matrix.mul_apply]

lemma slaterState_ofLp' (u : Matrix (Fin M) (Fin M) ℂ) (s : Finset (Fin M)) :
    (slaterState u s).ofLp = modeRot u *ᵥ Pi.single s 1 := by
  rw [slaterState, modeRotOp, EuclideanSpace.single, PiLp.single, toEuclideanCLM_toLp]

/-- `tr(ρ X) = Σ_s w_s ⟨U(v)|s⟩, X U(v)|s⟩⟩`. -/
lemma trace_quasiFreeOf_mul (v : Matrix (Fin M) (Fin M) ℂ) (n : Fin M → ℝ) (X : FockOp M) :
    (quasiFreeOf v n * X).trace =
      ∑ s, (confWeight n s : ℂ) * inner ℂ (slaterState v s) (toFockCLM X (slaterState v s)) := by
  have h : (quasiFreeOf v n * X).trace = (qfDiag n * ((modeRot v)ᴴ * X * modeRot v)).trace := by
    calc (quasiFreeOf v n * X).trace = ((modeRot v * qfDiag n) * ((modeRot v)ᴴ * X)).trace := by
          rw [quasiFreeOf]; simp only [mul_assoc]
      _ = (((modeRot v)ᴴ * X) * (modeRot v * qfDiag n)).trace := trace_mul_comm _ _
      _ = (((modeRot v)ᴴ * X * modeRot v) * qfDiag n).trace := by simp only [mul_assoc]
      _ = _ := trace_mul_comm _ _
  rw [h]
  simp only [Matrix.trace, Matrix.diag, qfDiag, diagonal_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [conj_diag_apply, inner_toFockCLM, slaterState_ofLp']

lemma rdm1_slaterState_eq {u : Matrix (Fin M) (Fin M) ℂ} (hu : u ∈ unitaryGroup (Fin M) ℂ)
    (s : Finset (Fin M)) :
    rdm1 (slaterState u s) = u.map star * diagonal (fun i => if i ∈ s then 1 else 0) * uᵀ := by
  rw [slaterState, rdm1_modeRotOp hu, rdm1_single]

lemma of_mul_diagonal_mul {p : ℕ} (v : Matrix (Fin M) (Fin M) ℂ) (d : Fin M → ℂ)
    (i j : Fin p → Fin M) :
    (of fun a b => (v.map star * diagonal d * vᵀ) (i a) (j b)) =
      (v.map star).submatrix i id * diagonal d * vᵀ.submatrix id j := by
  ext a b; simp only [of_apply, Matrix.mul_apply, submatrix_apply, id_eq]

/-- **Wick's theorem for `quasiFreeOf v n`**, with `γ = v̄ diag(n) vᵀ`. -/
theorem wick_quasiFreeOf {v : Matrix (Fin M) (Fin M) ℂ} (hv : v ∈ unitaryGroup (Fin M) ℂ)
    (n : Fin M → ℝ) {p : ℕ} (i j : Fin p → Fin M) :
    (quasiFreeOf v n * (creStr i * annStr j)).trace =
      (of fun a b => (v.map star * diagonal (fun k => (n k : ℂ)) * vᵀ) (i a) (j b)).det := by
  rw [trace_quasiFreeOf_mul]
  simp_rw [wick_slater hv, rdm1_slaterState_eq hv, of_mul_diagonal_mul, det_mul_diagonal_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← sum_confWeight_mul_prod n S.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-! ### Quasi-free states from one-body matrices -/

section FromGamma

variable {γ : Matrix (Fin M) (Fin M) ℂ} (hγ : γ.IsHermitian)

/-- The unitary `v` with `γ = v̄ diag(n) vᵀ` (natural orbitals). -/
noncomputable def qfU : Matrix (Fin M) (Fin M) ℂ := star (exists_diag_conj hγ).choose

lemma qfU_mem : qfU hγ ∈ unitaryGroup (Fin M) ℂ :=
  Unitary.star_mem (exists_diag_conj hγ).choose_spec.1

lemma gamma_eq_qfU : γ = (qfU hγ).map star * diagonal (fun k => (hγ.eigenvalues k : ℂ)) *
    (qfU hγ)ᵀ := by
  obtain ⟨hu, hd⟩ := (exists_diag_conj hγ).choose_spec
  set u := (exists_diag_conj hγ).choose
  have huu : uᵀ * u.map star = 1 := by
    have h := (mem_unitaryGroup_iff').mp hu
    have := congrArg transpose h
    rwa [transpose_mul, transpose_one, star_eq_conjTranspose, conjTranspose, transpose_map,
      transpose_transpose] at this
  have h1 : (qfU hγ).map star = uᵀ := by
    ext a b; simp [qfU, u, star_eq_conjTranspose]
  have h2 : (qfU hγ)ᵀ = u.map star := by
    ext a b; simp [qfU, u, star_eq_conjTranspose]
  rw [h1, h2, ← hd]
  calc γ = (uᵀ * u.map star) * γ * (uᵀ * u.map star) := by rw [huu, one_mul, mul_one]
    _ = _ := by simp only [mul_assoc]

/-- **The quasi-free state with one-body matrix `γ`.** -/
noncomputable def quasiFree : FockOp M :=
  quasiFreeOf (qfU hγ) fun k => hγ.eigenvalues k

/-- **Wick's theorem for quasi-free states**:
`tr(ρ_γ c_{i₀}† ⋯ c_{iₙ₋₁}† c_{jₙ₋₁} ⋯ c_{j₀}) = det (γ_{i_a j_b})`. -/
theorem wick_quasiFree {p : ℕ} (i j : Fin p → Fin M) :
    (quasiFree hγ * (creStr i * annStr j)).trace = (of fun a b => γ (i a) (j b)).det := by
  rw [quasiFree, wick_quasiFreeOf (qfU_mem hγ), ← gamma_eq_qfU]

/-- **The one-body matrix of `ρ_γ` is `γ`**: `tr(ρ_γ c_i† c_j) = γ_ij`. -/
theorem rdm1_quasiFree (i j : Fin M) : (quasiFree hγ * (cre i * ann j)).trace = γ i j := by
  have h := wick_quasiFree hγ ![i] ![j]
  simp only [creStr, annStr, mul_one, one_mul, det_unique, of_apply, Fin.default_eq_zero,
    Matrix.cons_val_fin_one] at h
  exact h

open scoped ComplexOrder in
/-- **`ρ_γ` is a density matrix** when `0 ≤ γ ≤ 1`. -/
theorem quasiFree_isDensityMatrix (h0 : γ.PosSemidef) (h1 : (1 - γ).PosSemidef) :
    (quasiFree h0.1).PosSemidef ∧ (quasiFree h0.1).trace = 1 := by
  have hγ := gamma_eq_qfU h0.1
  have hv := qfU_mem h0.1
  set v := qfU h0.1
  set ev : Fin M → ℝ := fun k => h0.1.eigenvalues k
  -- `0 ≤ n_k ≤ 1`
  have hvv : vᵀ * v.map star = 1 := by
    have h := (mem_unitaryGroup_iff').mp hv
    have := congrArg transpose h
    rwa [transpose_mul, transpose_one, star_eq_conjTranspose, conjTranspose, transpose_map,
      transpose_transpose] at this
  have hconj : (vᵀ)ᴴ = v.map star := by ext a b; simp
  have hD : diagonal (fun k => (ev k : ℂ)) = vᵀ * γ * (vᵀ)ᴴ := by
    rw [hconj, hγ]
    calc diagonal (fun k => (ev k : ℂ)) = (vᵀ * v.map star) * diagonal (fun k => (ev k : ℂ)) *
          (vᵀ * v.map star) := by rw [hvv, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]; rfl
  have hD1 : 1 - diagonal (fun k => (ev k : ℂ)) = vᵀ * (1 - γ) * (vᵀ)ᴴ := by
    rw [mul_sub, sub_mul, mul_one, ← hD, hconj, hvv]
  have hb : ∀ k, 0 ≤ ev k ∧ ev k ≤ 1 := by
    intro k
    constructor
    · exact h0.eigenvalues_nonneg k
    · have h := (h1.mul_mul_conjTranspose_same vᵀ).diag_nonneg (i := k)
      rw [← hD1, Matrix.sub_apply, Matrix.one_apply_eq, diagonal_apply_eq] at h
      have h' := (Complex.nonneg_iff.mp h).1
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at h'
      linarith
  have hw : ∀ s, 0 ≤ confWeight ev s := fun s =>
    Finset.prod_nonneg fun k _ => by split_ifs <;> linarith [hb k]
  refine ⟨?_, ?_⟩
  · refine PosSemidef.mul_mul_conjTranspose_same ?_ (modeRot v)
    rw [qfDiag, posSemidef_diagonal_iff]
    intro s
    exact_mod_cast hw s
  · rw [quasiFree, quasiFreeOf, trace_mul_comm, ← mul_assoc, modeRot_conjTranspose_mul hv,
      one_mul, qfDiag, trace_diagonal]
    exact_mod_cast sum_confWeight ev

end FromGamma

end QM.ManyBody
