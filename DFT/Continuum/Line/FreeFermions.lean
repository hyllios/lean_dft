/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Free
import DFT.Continuum.Line.Pauli
import DFT.Continuum.Spectral.Expand

/-!
# Free fermions on a line: ground states exist

For `n + 1` non-interacting fermions on `[0, 1]` with a continuous potential `v`, take the
`n + 1` lowest one-particle eigenfunctions `φⱼ` (energies `λⱼ`, `Continuum/Spectral/Expand`).
The Slater determinant `Φ(x) = det [φⱼ(xᵢ)]` is an `(n + 1)`-fermion ground state with energy
`Σⱼ λⱼ`, so Hohenberg–Kohn and Lieb's form of it hold with no assumption at all.

* `exists_det_ne`: linearly independent functions have a nonzero determinant at some points.
* `slater_mem`, `lapN_slater`, `Q_slater`: the determinant is a state, solves
  `-ΔΦ + Σₖ v(xₖ) Φ = (Σⱼ λⱼ) Φ` on the closed cube (Laplace expansion along a row and
  `adj M · M = det M`), so its energy is `Σⱼ λⱼ`; `ip_slater_pos`: it is not zero.
* `lower_bound_fer`: every state has energy at least `Σⱼ λⱼ`. Along each coordinate the
  one-particle bound `Λ ‖ψ‖² - Σⱼ (Λ - λⱼ) ⟪φⱼ, ψ⟫² ≤ ⟨ψ, hψ⟩` holds slice by slice, and the
  Pauli principle (`Continuum/Line/Pauli`) bounds the occupation of each `φⱼ` by one.
* `hk_free_fermions_line`, `lieb_free_fermions_line`: **unconditional** Hohenberg–Kohn and
  Lieb's form of it for `N` free fermions.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Filter Topology Box

variable {n : ℕ}

/-! ### A nonzero determinant -/

/-- **Linearly independent functions have a nonzero determinant**: if no nontrivial combination
of `g₀, …, g_{m-1}` vanishes on `U`, there are points `xᵢ ∈ U` with `det [gⱼ(xᵢ)] ≠ 0`. -/
lemma exists_det_ne {X : Type*} {m : ℕ} (g : Fin m → X → ℝ) (U : Set X)
    (hind : ∀ a : Fin m → ℝ, (∀ t ∈ U, ∑ j, a j * g j t = 0) → a = 0) :
    ∃ x : Fin m → X, (∀ i, x i ∈ U) ∧ (Matrix.of fun i j => g j (x i)).det ≠ 0 := by
  classical
  set row : X → (Fin m → ℝ) := fun t j => g j t
  set R := row '' U
  -- the rows span everything
  have hspan : Submodule.span ℝ R = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := (Submodule.span ℝ R).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    have hfv : ∀ w : Fin m → ℝ, f w = ∑ j, w j * f (Pi.single j 1) := by
      intro w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (Pi.single j (w j) : Fin m → ℝ) = w j • Pi.single j 1 by
        rw [← Pi.single_smul]; simp, map_smul, smul_eq_mul]
    have ha := hind (fun j => f (Pi.single j 1)) fun t ht => by
      have h1 : f (row t) = 0 := hle (Submodule.subset_span ⟨t, ht, rfl⟩)
      rw [hfv] at h1
      simpa [row, mul_comm] using h1
    apply hf0
    refine LinearMap.ext fun w => ?_
    rw [hfv w]
    simp [show ∀ j, f (Pi.single j 1) = 0 from fun j => congrFun ha j]
  -- a basis among the rows
  obtain ⟨b, hbR, hbspan, hli⟩ := exists_linearIndependent ℝ R
  have : Finite b := hli.finite_of_isNoetherian
  let _ := Fintype.ofFinite b
  have hcard : Fintype.card b = m := by
    have h := finrank_span_eq_card hli
    rw [Subtype.range_coe, hbspan, hspan, finrank_top, Module.finrank_fin_fun] at h
    exact h.symm
  let e : Fin m ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpt : ∀ i, ∃ t ∈ U, row t = (e i : Fin m → ℝ) := fun i => hbR (e i).2
  choose x hxU hx using hpt
  refine ⟨x, hxU, ?_⟩
  have hrows : LinearIndependent ℝ (Matrix.of fun i j => g j (x i)).row := by
    have : (Matrix.of fun i j => g j (x i)).row = fun i => (e i : Fin m → ℝ) := by
      funext i; exact hx i
    rw [this]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_row_iff_isUnit.1 hrows)).ne_zero

/-! ### The Slater determinant -/

section slater

variable (φ : Fin (n + 1) → ℝ → ℝ)

/-- The matrix `[φⱼ(xᵢ)]`. -/
def slM (x : Cfg n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => φ j (x i)

/-- The Slater determinant `det [φⱼ(xᵢ)]`. -/
noncomputable def slater (x : Cfg n) : ℝ := (slM φ x).det

lemma slater_eq_alt : slater φ = alt .fer fun x => ∏ i, φ i (x i) := by
  funext x
  simp only [slater, slM, Matrix.det_apply', alt, ch_fer, sgn, pm_apply, Matrix.of_apply]

/-- The rows other than `k` do not see `xₖ`. -/
lemma updateRow_slM (x : Cfg n) (k : Fin (n + 1)) (t : ℝ) (r : Fin (n + 1) → ℝ) :
    (slM φ (Function.update x k t)).updateRow k r = (slM φ x).updateRow k r := by
  ext i j
  by_cases hik : i = k
  · subst hik; simp
  · simp [Matrix.updateRow_ne hik, slM, Function.update_of_ne hik]

/-- The cofactors along row `k`. -/
noncomputable def cof (x : Cfg n) (k j : Fin (n + 1)) : ℝ := (slM φ x).adjugate j k

variable {φ} (hφ : ∀ j, φ j ∈ Box.Dom)
include hφ

lemma slater_mem : slater φ ∈ DomF n := by
  refine ⟨?_, fun σ x => ?_, fun x k hk => ?_⟩
  · rw [slater_eq_alt]
    exact contDiff_alt .fer (contDiff_prod fun i _ => (hφ i).1.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i).contDiff)
  · rw [slater_eq_alt, alt_pm]
  · refine Matrix.det_eq_zero_of_row_eq_zero k fun j => ?_
    simp only [slM, Matrix.of_apply]
    rcases hk with h | h <;> rw [h]
    exacts [(hφ j).2.1, (hφ j).2.2]

omit hφ in
/-- **Laplace expansion along row `k`**: the slice through `x` along `k` is `Σⱼ φⱼ(t) cⱼ`. -/
lemma slater_update (x : Cfg n) (k : Fin (n + 1)) (t : ℝ) :
    slater φ (Function.update x k t) = ∑ j, φ j t * cof φ x k j := by
  rw [slater, Matrix.det_eq_sum_mul_adjugate_row _ k]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cof, Matrix.adjugate_apply, updateRow_slM φ x k t]
  simp [slM]

omit hφ in
lemma slater_eq_cof (x : Cfg n) (k : Fin (n + 1)) :
    slater φ x = ∑ j, φ j (x k) * cof φ x k j := by
  rw [← slater_update x k (x k), Function.update_eq_self]

lemma dk_slater_update (x : Cfg n) (k : Fin (n + 1)) (t : ℝ) :
    dk k (slater φ) (Function.update x k t) = ∑ j, deriv (φ j) t * cof φ x k j := by
  have h1 := hasDerivAt_slice (diffF (slater_mem hφ)) x k t
  have h2 : HasDerivAt (fun s => slater φ (Function.update x k s))
      (∑ j, deriv (φ j) t * cof φ x k j) t := by
    have : (fun s => slater φ (Function.update x k s)) = fun s => ∑ j, φ j s * cof φ x k j :=
      funext fun s => slater_update x k s
    rw [this]
    exact HasDerivAt.fun_sum fun j _ =>
      (((hφ j).1.differentiable (by norm_num)) t).hasDerivAt.mul_const _
  exact h1.unique h2

/-- `∂ₖₖ Φ (x) = Σⱼ φⱼ''(xₖ) cⱼ`. -/
lemma dkk_slater (x : Cfg n) (k : Fin (n + 1)) :
    dkk k (slater φ) x = ∑ j, deriv (deriv (φ j)) (x k) * cof φ x k j := by
  have hd : Differentiable ℝ (dk k (slater φ)) :=
    (contDiff_dk (slater_mem hφ).1 k).differentiable one_ne_zero
  have h1 := hasDerivAt_slice hd x k (x k)
  rw [Function.update_eq_self] at h1
  have h2 : HasDerivAt (fun s => dk k (slater φ) (Function.update x k s))
      (∑ j, deriv (deriv (φ j)) (x k) * cof φ x k j) (x k) := by
    have : (fun s => dk k (slater φ) (Function.update x k s)) =
        fun s => ∑ j, deriv (φ j) s * cof φ x k j :=
      funext fun s => dk_slater_update hφ x k s
    rw [this]
    exact HasDerivAt.fun_sum fun j _ =>
      ((((contDiff_succ_iff_deriv.1 (hφ j).1).2.2).differentiable one_ne_zero)
        (x k)).hasDerivAt.mul_const _
  exact h1.unique h2

/-- **The Schrödinger equation** on the closed cube:
`ΔΦ = (Σₖ v(xₖ) - Σⱼ λⱼ) Φ` when `φⱼ'' = (v - λⱼ) φⱼ`. -/
lemma lapN_slater {v : Pot} {lam : Fin (n + 1) → ℝ}
    (hode : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv (φ j)) x = (ext v x - lam j) * φ j x)
    {x : Cfg n} (hx : x ∈ CubeC n) :
    lapN (slater φ) x = (LN n v x - ∑ j, lam j) * slater φ x := by
  have hk : ∀ k, dkk k (slater φ) x =
      ext v (x k) * slater φ x - ∑ j, lam j * (φ j (x k) * cof φ x k j) := by
    intro k
    rw [dkk_slater hφ, slater_eq_cof x k, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hode j (x k) (hx k (mem_univ k))]; ring
  -- `Σₖ φⱼ(xₖ) cofⱼₖ = det`
  have hcol : ∀ j, ∑ k, φ j (x k) * cof φ x k j = slater φ x := by
    intro j
    have h := congrFun (congrFun (Matrix.adjugate_mul (slM φ x)) j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [slater, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [cof, slM, mul_comm]
  simp only [lapN, hk, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, ← Finset.sum_mul]
  simp only [← Finset.mul_sum, hcol, ← Finset.sum_mul]
  simp only [LN, LinearMap.coe_mk, AddHom.coe_mk]
  ring

end slater

/-! ### The energy of the Slater determinant -/

section energy

variable {φ : Fin (n + 1) → ℝ → ℝ} (hφ : ∀ j, φ j ∈ Box.Dom) {v : Pot} {lam : Fin (n + 1) → ℝ}
  (hode : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv (φ j)) x = (ext v x - lam j) * φ j x)
include hφ hode

/-- **The Slater determinant has energy `Σⱼ λⱼ`.** -/
lemma Q_slater :
    Q (freeS .fer n) v (slater φ) = (∑ j, lam j) * ip (μ := μN n) (slater φ) (slater φ) := by
  have hD := slater_mem hφ
  set Φ := slater φ
  have hc := hD.1.continuous
  have hkin : ∫ x, ∑ k, dk k Φ x * dk k Φ x ∂μN n = -∫ x, lapN Φ x * Φ x ∂μN n := by
    rw [integral_finsetSum (f := fun k x => dk k Φ x * dk k Φ x) _
      fun k _ => integrableN ((cont_dk hD k).mul (cont_dk hD k))]
    simp only [ibpN hD.1 hD]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum (f := fun k x => dkk k Φ x * Φ x) _
      fun k _ => integrableN ((continuous_dkk hD.1 k).mul hc)]
    congr 2; funext x; simp only [lapN, Finset.sum_mul]
  have hlap : ∫ x, lapN Φ x * Φ x ∂μN n =
      ∫ x, LN n v x * (Φ x * Φ x) ∂μN n - (∑ j, lam j) * ∫ x, Φ x * Φ x ∂μN n := by
    rw [← integral_const_mul, ← integral_sub (f := fun x => LN n v x * (Φ x * Φ x))
      (g := fun x => (∑ j, lam j) * (Φ x * Φ x)) (integrableN ((continuous_LN v).mul (hc.mul hc)))
      (integrableN (continuous_const.mul (hc.mul hc)))]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_cube] with x hx
    rw [lapN_slater hφ hode (cube_subset hx)]; ring
  simp only [Q, freeS, setting, h0N, pf, ip, zero_mul, integral_zero, add_zero]
  rw [hkin, hlap]
  ring

end energy

/-- A continuous nonnegative function that is positive somewhere in the cube has positive
integral. -/
lemma integral_pos_of_pt {F : Cfg n → ℝ} (hF : Continuous F) (h0 : ∀ x, 0 ≤ F x) {x0 : Cfg n}
    (hx0 : x0 ∈ Cube n) (hpos : 0 < F x0) : 0 < ∫ x, F x ∂μN n := by
  rw [integral_pos_iff_support_of_nonneg h0 (integrableN hF),
    Measure.restrict_apply' measurableSet_cube]
  exact (hF.isOpen_support.inter isOpen_cube).measure_pos volume ⟨x0, hpos.ne', hx0⟩

/-- **The Slater determinant of orthonormal orbitals is not zero.** -/
lemma ip_slater_pos {φ : Fin (n + 1) → ℝ → ℝ} (hφ : ∀ j, φ j ∈ Box.Dom)
    (hon : ∀ j k, ∫ x, φ j x * φ k x ∂μ1 = if j = k then 1 else 0) :
    0 < ip (μ := μN n) (slater φ) (slater φ) := by
  have hind : ∀ a : Fin (n + 1) → ℝ, (∀ t ∈ Ioo (0 : ℝ) 1, ∑ j, a j * φ j t = 0) → a = 0 := by
    intro a ha
    funext k
    have h0 : ∫ t, (∑ j, a j * φ j t) * φ k t ∂μ1 = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [ha t ht, zero_mul]; rfl
    rw [show (fun t => (∑ j, a j * φ j t) * φ k t) = fun t => ∑ j, a j * (φ j t * φ k t) from
        funext fun t => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring,
      integral_finsetSum (f := fun j t => a j * (φ j t * φ k t)) _ fun j _ =>
        (integrable_of_continuous ((hφ j).1.continuous.mul (hφ k).1.continuous)).const_mul _] at h0
    simp only [integral_const_mul, hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h0
    exact h0
  obtain ⟨x0, hx0, hdet⟩ := exists_det_ne φ (Ioo (0 : ℝ) 1) hind
  have hD := slater_mem hφ
  exact integral_pos_of_pt (hD.1.continuous.mul hD.1.continuous) (fun x => mul_self_nonneg _)
    (fun i _ => hx0 i) (mul_self_pos.2 hdet)

/-! ### The lower bound -/

section lower

variable {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomF n)

include hΦ in
lemma slice_update_mem (k : Fin (n + 1)) (x : Cfg n) :
    (fun t => Φ (Function.update x k t)) ∈ Box.Dom := by
  have h := slice_mem hΦ k (Fin.removeNth k x)
  simp only [Fin.insertNth_removeNth] at h
  exact h

variable (v : Pot) {φ : Fin (n + 1) → ℝ → ℝ} {lam : Fin (n + 1) → ℝ} {Λ : ℝ}
  (hφ : ∀ j, φ j ∈ Box.Dom)
  (hbound : ∀ ψ ∈ Box.Dom, Λ * ip (μ := μ1) ψ ψ -
    ∑ j, (Λ - lam j) * (∫ x, φ j x * ψ x ∂μ1) ^ 2 ≤ Q Box.setting v ψ)
include hΦ hφ hbound

/-- The one-particle bound along coordinate `k`, integrated over the other coordinates. -/
lemma slice_bound (k : Fin (n + 1)) :
    Λ * ∫ x, Φ x * Φ x ∂μN n - ∑ j, (Λ - lam j) * ∫ x, Φ x * pK Φ (φ j) k x ∂μN n ≤
      ∫ x, sk v 0 k Φ x ∂μN n := by
  have hc := hΦ.1.continuous
  have hP : ∀ j, Continuous (pK Φ (φ j) k) := fun j => continuous_pK hΦ (hφ j).1.continuous k
  set H : Cfg n → ℝ := fun x => sk v 0 k Φ x - Λ * (Φ x * Φ x) +
    ∑ j, (Λ - lam j) * (Φ x * pK Φ (φ j) k x)
  have hHc : Continuous H := (((continuous_sk v 0 k hΦ).sub (continuous_const.mul (hc.mul hc))).add
    (continuous_finsetSum _ fun j _ => continuous_const.mul (hc.mul (hP j))))
  -- the average over coordinate `k` is a one-particle energy gap, hence nonnegative
  have havg : ∀ x, 0 ≤ avgK k H x := by
    intro x
    set ψ : ℝ → ℝ := fun t => Φ (Function.update x k t)
    have hψ : ψ ∈ Box.Dom := slice_update_mem hΦ k x
    have hψc := hψ.1.continuous
    have hG : ∀ j, gK Φ (φ j) k x = ∫ t, φ j t * ψ t ∂μ1 := fun j => gK_apply k x
    have hpt : ∀ t, H (Function.update x k t) = (deriv ψ t ^ 2 + Wof v 0 t * ψ t ^ 2) -
        Λ * (ψ t * ψ t) + ∑ j, ((Λ - lam j) * gK Φ (φ j) k x) * (φ j t * ψ t) := by
      intro t
      have hd : deriv ψ t = dk k Φ (Function.update x k t) :=
        (hasDerivAt_slice (diffF hΦ) x k t).deriv
      simp only [H, sk, pK, Function.update_self, gK_update, hd, ψ]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have i1 : Integrable (fun t => deriv ψ t ^ 2 + Wof v 0 t * ψ t ^ 2) μ1 :=
      integrable_of_continuous (((cont_deriv_of_mem hψ).pow 2).add
        ((continuous_Wof v 0).mul (hψc.pow 2)))
    have i2 : Integrable (fun t => Λ * (ψ t * ψ t)) μ1 :=
      integrable_of_continuous (continuous_const.mul (hψc.mul hψc))
    have i3 : Integrable (fun t => ∑ j, ((Λ - lam j) * gK Φ (φ j) k x) * (φ j t * ψ t)) μ1 :=
      integrable_of_continuous (continuous_finsetSum _ fun j _ =>
        continuous_const.mul ((hφ j).1.continuous.mul hψc))
    have hval : avgK k H x = (Q Box.setting v ψ - 0 * ip (μ := μ1) ψ ψ) -
        Λ * ip (μ := μ1) ψ ψ + ∑ j, (Λ - lam j) * (∫ t, φ j t * ψ t ∂μ1) ^ 2 := by
      simp only [avgK, hpt]
      rw [integral_add (f := fun t => deriv ψ t ^ 2 + Wof v 0 t * ψ t ^ 2 - Λ * (ψ t * ψ t))
          (g := fun t => ∑ j, ((Λ - lam j) * gK Φ (φ j) k x) * (φ j t * ψ t)) (i1.sub i2) i3,
        integral_sub (f := fun t => deriv ψ t ^ 2 + Wof v 0 t * ψ t ^ 2)
          (g := fun t => Λ * (ψ t * ψ t)) i1 i2, Q_sub_eq v 0 hψ,
        integral_finsetSum (f := fun j t => ((Λ - lam j) * gK Φ (φ j) k x) * (φ j t * ψ t)) _
          fun j _ => integrable_of_continuous (continuous_const.mul
            ((hφ j).1.continuous.mul hψc)),
        integral_const_mul]
      simp only [integral_const_mul, hG, ip]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hval]
    have := hbound ψ hψ
    linarith
  have h0 : 0 ≤ ∫ x, H x ∂μN n := by
    rw [← integral_avgK k hHc]; exact integral_nonneg havg
  have e : ∫ x, H x ∂μN n = ∫ x, sk v 0 k Φ x ∂μN n - Λ * ∫ x, Φ x * Φ x ∂μN n +
      ∑ j, (Λ - lam j) * ∫ x, Φ x * pK Φ (φ j) k x ∂μN n := by
    simp only [H]
    rw [integral_add (f := fun x => sk v 0 k Φ x - Λ * (Φ x * Φ x))
        (g := fun x => ∑ j, (Λ - lam j) * (Φ x * pK Φ (φ j) k x))
        ((integrableN (continuous_sk v 0 k hΦ)).sub
        (integrableN (continuous_const.mul (hc.mul hc))))
        (integrableN (continuous_finsetSum _ fun j _ => continuous_const.mul (hc.mul (hP j)))),
      integral_sub (f := fun x => sk v 0 k Φ x) (g := fun x => Λ * (Φ x * Φ x))
        (integrableN (continuous_sk v 0 k hΦ))
        (integrableN (continuous_const.mul (hc.mul hc))), integral_const_mul,
      integral_finsetSum (f := fun j x => (Λ - lam j) * (Φ x * pK Φ (φ j) k x)) _
        fun j _ => integrableN (continuous_const.mul (hc.mul (hP j)))]
    simp only [integral_const_mul]
  linarith

/-- **Lower bound.** With `λⱼ ≤ Λ` and orthonormal `φⱼ`, every state of `n + 1` fermions has
energy at least `Σⱼ λⱼ`. -/
theorem lower_bound_fer (hle : ∀ j, lam j ≤ Λ) (hnorm : ∀ j, ∫ x, φ j x * φ j x ∂μ1 = 1) :
    (∑ j, lam j) * ip (μ := μN n) Φ Φ ≤ Q (freeS .fer n) v Φ := by
  have hQ := Q_slices (τ := .fer) v 0 hΦ
  have hk := fun k => slice_bound hΦ v hφ hbound k
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
  rw [Finset.sum_sub_distrib, Finset.sum_comm] at hsum
  have hpauli : ∀ j, (Λ - lam j) * ∑ k, ∫ x, Φ x * pK Φ (φ j) k x ∂μN n ≤
      (Λ - lam j) * ∫ x, Φ x * Φ x ∂μN n := fun j =>
    mul_le_mul_of_nonneg_left (pauli hΦ (hφ j).1.continuous (hnorm j)) (sub_nonneg.2 (hle j))
  have hp := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpauli j
  simp only [← Finset.mul_sum] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  simp only [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hp
  simp only [ip]
  push_cast at hsum hp
  nlinarith

end lower

/-! ### Unconditional theorems -/

/-- **The Slater determinant of the lowest orbitals is an `(n + 1)`-fermion ground state.** -/
theorem slater_isGS (v : Pot) : ∃ Ψ E, IsGS (freeS .fer n) v Ψ ∧
    Q (freeS .fer n) v Ψ = E * ip (μ := μN n) Ψ Ψ ∧
    ∀ φ ∈ DomF n, E * ip (μ := μN n) φ φ ≤ Q (freeS .fer n) v φ := by
  obtain ⟨φ, lam, Λ, hφ, hode, hon, hle, hbound⟩ := Spectral.exists_orbitals v n
  have hnorm : ∀ j, ∫ x, φ j x * φ j x ∂μ1 = 1 := fun j => by rw [hon]; simp
  have hD := slater_mem hφ
  have hQ := Q_slater hφ hode
  have hpos := ip_slater_pos hφ hon
  have hlow : ∀ φ' ∈ DomF n, (∑ j, lam j) * ip (μ := μN n) φ' φ' ≤ Q (freeS .fer n) v φ' :=
    fun φ' h => lower_bound_fer h v hφ hbound hle hnorm
  refine ⟨slater φ, ∑ j, lam j, ⟨hD, hpos, fun φ' hφ' => ?_⟩, hQ, hlow⟩
  rw [hQ]
  nlinarith [mul_le_mul_of_nonneg_left (hlow φ' hφ') hpos.le]

/-- **Hohenberg–Kohn for `N` free fermions on a line, unconditional.** Every continuous potential
has an `(n + 1)`-fermion ground state, and ground states of two continuous potentials with the same
one-body density force the potentials to differ by a constant. -/
theorem hk_free_fermions_line (v v' : Pot) :
    (∃ Φ, IsGS (freeS .fer n) v Φ) ∧ ∀ Φ Φ', IsGS (freeS .fer n) v Φ →
      IsGS (freeS .fer n) v' Φ' →
      (∀ t ∈ Ioo (0 : ℝ) 1, ∫ y in Cube' n, Φ (Fin.cons t y) ^ 2 =
        ∫ y in Cube' n, Φ' (Fin.cons t y) ^ 2) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨Ψ, -, hΨ, -⟩ := slater_isGS (n := n) v
  exact ⟨⟨Ψ, hΨ⟩, fun _ _ h h' hρ => hk_interacting_fermions_line (fun _ _ => rfl) h h' hρ⟩

/-- **Normalised ground states exist** for `N` free fermions. -/
theorem exists_isNGS_free_fer (v : Pot) : ∃ ψ, IsNGS (freeS .fer n) v ψ := by
  obtain ⟨Ψ, E, hΨ, hQΨ, hlow⟩ := slater_isGS (n := n) v
  obtain ⟨hD, hpos, -⟩ := hΨ
  set c := (Real.sqrt (ip (μ := μN n) Ψ Ψ))⁻¹
  have hs : 0 < Real.sqrt (ip (μ := μN n) Ψ Ψ) := Real.sqrt_pos.mpr hpos
  have hc2 : c * c * ip (μ := μN n) Ψ Ψ = 1 := by
    simp only [c]; field_simp; rw [Real.sq_sqrt hpos.le]
  have hcD : c • Ψ ∈ DomF n := (DomF n).smul_mem c hD
  refine ⟨c • Ψ, ⟨hcD, by rw [ip_smul_self, hc2]⟩, fun φ hφ => ?_⟩
  rw [Q_smul_self (S := freeS .fer n) v c hD, hQΨ]
  have := hlow φ hφ.1
  rw [hφ.2, mul_one] at this
  calc c * c * (E * ip (μ := μN n) Ψ Ψ) = E * (c * c * ip (μ := μN n) Ψ Ψ) := by ring
    _ = E := by rw [hc2, mul_one]
    _ ≤ Q (freeS .fer n) v φ := this

/-- **The Lieb functional for `N` free fermions on a line, unconditional.** For every continuous
potential `v` there is a normalised ground state `ψ`; at its density the Lieb functional equals the
kinetic energy of `ψ`, `-v` is a subgradient, and every other subgradient `-v'` has `v - v'`
constant. -/
theorem lieb_free_fermions_line (v : Pot) : ∃ ψ, IsNGS (freeS .fer n) v ψ ∧
    liebF (freeS .fer n) (dens (freeS .fer n) ψ) = (((freeS .fer n).h0 ψ ψ : ℝ) : EReal) ∧
    (∀ ρ : Pot → ℝ, (((freeS .fer n).h0 ψ ψ + dens (freeS .fer n) ψ v - ρ v : ℝ) : EReal) ≤
      liebF (freeS .fer n) ρ) ∧
    ∀ v' : Pot, (∀ ρ : Pot → ℝ,
      (((freeS .fer n).h0 ψ ψ + dens (freeS .fer n) ψ v' - ρ v' : ℝ) : EReal) ≤
        liebF (freeS .fer n) ρ) → ∃ k : ℝ, v - v' = k • one := by
  obtain ⟨ψ, hψ⟩ := exists_isNGS_free_fer (n := n) v
  exact ⟨ψ, hψ, lieb_line (fun _ _ => rfl) hψ⟩

end DFT.Continuum.Line
