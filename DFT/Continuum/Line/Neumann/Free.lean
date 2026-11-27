/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Algebra.QuadraticDiscriminant
import DFT.Continuum.Line.Neumann.Slater

/-!
# Non-interacting ground states with Neumann walls

For `v ∈ H⁻¹` and no interaction, the ground-state energy of `N` fermions is the sum of the `N`
lowest Neumann eigenvalues `λ_j` of `-d²/dx² + v` (`Neumann/Spec`), and that of `N` bosons is
`N λ₀`.

* `lower_smooth_fer`, `lower_smooth_bos`: the lower bounds for `C²` states, from the one-particle
  bound on each slice and, for fermions, the Pauli principle (`Neumann/Slices`).
* `tendsto_kinN_truncC`, `tendsto_sq_truncC`, `tendsto_v_truncC`: the energy of the cosine
  truncations converges.
* **`lower_fer`**, **`lower_bos`**: the lower bounds for all `H¹` states.
* **`gs_free_fer`**: `E₀ = Σ_{j<N} λ_j`, the Slater determinant of the `N` lowest orbitals
  (`Neumann/Slater`) is a ground state, and `λ_{N-1} < λ_N` (otherwise replacing `φ_{N-1}` by
  `φ_N` would give a second, orthogonal ground state, against `gsNH_unique`).
* **`gs_free_bos`**: `E₀ = N λ₀`, and the product state `φ₀^{⊗N}` is a ground state.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction

variable {n : ℕ} {τ : Stat} {X : Cfg n → ℝ}

/-! ### Lower bounds for smooth states -/

section lower

variable (v : PotH) {φ : ℕ → H1E} {lam : ℕ → ℝ} {b : HilbertBasis ℕ ℝ HL}
  (hJ : ∀ k, JE (φ k) = b k)
  (hbd : ∀ (N : ℕ) (ψ : H1E), ∑ j ∈ Finset.range N, lam j * ⟪b j, JE ψ⟫_ℝ ^ 2 +
    lam N * (‖JE ψ‖ ^ 2 - ∑ j ∈ Finset.range N, ⟪b j, JE ψ⟫_ℝ ^ 2) ≤ ‖ψ.snd‖ ^ 2 + v (dE ψ))

lemma continuous_snd_sE (hX : X ∈ DomC τ n) : Continuous fun y => (sE hX y).snd :=
  continuous_snd.comp ((WithLp.prod_continuous_ofLp 2 ℝ HL).comp (continuous_sE hX))

lemma int_snd_sq (hX : X ∈ DomC τ n) :
    Integrable (fun y => ‖(sE hX y).snd‖ ^ 2) (volume.restrict (Cube' n)) :=
  integrableOn_cube'_of_continuous (g := fun y => ‖(sE hX y).snd‖ ^ 2)
    ((continuous_snd_sE hX).norm.pow 2)

lemma int_v_dE (hX : X ∈ DomC τ n) :
    Integrable (fun y => v (dE (sE hX y))) (volume.restrict (Cube' n)) :=
  integrableOn_cube'_of_continuous (g := fun y => v (dE (sE hX y)))
    (v.continuous.comp (continuous_dE.comp (continuous_sE hX)))

lemma int_JE_sq (hX : X ∈ DomC τ n) :
    Integrable (fun y => ‖JE (sE hX y)‖ ^ 2) (volume.restrict (Cube' n)) :=
  integrableOn_cube'_of_continuous (g := fun y => ‖JE (sE hX y)‖ ^ 2)
    ((JE.continuous.comp (continuous_sE hX)).norm.pow 2)

/-- The slice energy `‖s_y'‖² + v(s_y²)` integrates to the energy over `N`. -/
lemma integral_slice_energy (hX : X ∈ DomC τ n) (hXN : X ∈ DomN τ n) :
    ((n : ℝ) + 1) * ∫ y in Cube' n, (‖(sE hX y).snd‖ ^ 2 + v (dE (sE hX y))) =
      kinN X + v (rhoE τ X) := by
  rw [integral_add (int_snd_sq hX) (int_v_dE v hX), mul_add, kinN_eq_slices hX,
    v_rhoE_eq_slices hX hXN]

include hJ in
lemma norm_orbital (hb1 : ∀ k, ‖b k‖ = 1) (k : ℕ) :
    ∫ t, iccExt (evE (φ k)) t * iccExt (evE (φ k)) t ∂vol01 = 1 := by
  have h := norm_JE_sq (φ k)
  rw [hJ, hb1, one_pow] at h
  refine (setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_).trans h.symm
  simp only [ext_evE (Ioo_subset_Icc_self ht), sq]

include hJ hbd in
/-- **Lower bound for smooth fermionic states**: `Σ_{j ≤ n} λ_j ∫ X² ≤ T(X) + v(ρ_X)`. -/
theorem lower_smooth_fer (hmono : Monotone lam) {X : Cfg n → ℝ} (hX : X ∈ DomC .fer n)
    (hXN : X ∈ DomN .fer n) :
    (∑ j ∈ Finset.range (n + 1), lam j) * ∫ x, X x * X x ∂μN n ≤ kinN X + v (rhoE .fer X) := by
  set Λ := lam (n + 1)
  set c : ℕ → (Fin n → ℝ) → ℝ := fun j y => ⟪b j, JE (sE hX y)⟫_ℝ
  have hc : ∀ j, Continuous (c j) := fun j =>
    continuous_const.inner (JE.continuous.comp (continuous_sE hX))
  have hJs : Continuous fun y => ‖JE (sE hX y)‖ ^ 2 :=
    (JE.continuous.comp (continuous_sE hX)).norm.pow 2
  -- the one-particle bound on each slice, rearranged
  have hpt : ∀ y, ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * c j y ^ 2 + Λ * ‖JE (sE hX y)‖ ^ 2 ≤
      ‖(sE hX y).snd‖ ^ 2 + v (dE (sE hX y)) := fun y => by
    have h := hbd (n + 1) (sE hX y)
    have e : ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * c j y ^ 2 + Λ * ‖JE (sE hX y)‖ ^ 2 =
        ∑ j ∈ Finset.range (n + 1), lam j * c j y ^ 2 +
          Λ * (‖JE (sE hX y)‖ ^ 2 - ∑ j ∈ Finset.range (n + 1), c j y ^ 2) := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
    rw [e]; exact h
  have hLi : ∀ j, Integrable (fun y => (lam j - Λ) * c j y ^ 2) (volume.restrict (Cube' n)) :=
    fun j => integrableOn_cube'_of_continuous (g := fun y => (lam j - Λ) * c j y ^ 2)
      (continuous_const.mul ((hc j).pow 2))
  have hS : Integrable (fun y => ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * c j y ^ 2)
      (volume.restrict (Cube' n)) := integrable_finsetSum _ fun j _ => hLi j
  have hint := integral_mono (hS.add ((int_JE_sq hX).const_mul Λ))
    ((int_snd_sq hX).add (int_v_dE v hX)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add hS ((int_JE_sq hX).const_mul Λ), integral_finsetSum _ fun j _ => hLi j,
    integral_const_mul] at hint
  simp only [integral_const_mul] at hint
  rw [← integral_sq_eq_slices hX] at hint
  have hE := integral_slice_energy v hX hXN
  -- occupations
  have hocc : ∀ j, ((n : ℝ) + 1) * ∫ y in Cube' n, c j y ^ 2 ≤ ∫ x, X x * X x ∂μN n := fun j => by
    have e : ∀ y, c j y = ∫ t, iccExt (evE (φ j)) t * X (Fin.insertNth 0 t y) ∂vol01 :=
      fun y => by simp only [c, ← hJ j, inner_JE_sE]
    simp only [e]
    exact occ_le hX (continuous_iccExt _) (norm_orbital hJ (fun k => b.orthonormal.1 k) j)
  have hterm : ∀ j ∈ Finset.range (n + 1), (lam j - Λ) * ∫ x, X x * X x ∂μN n ≤
      (lam j - Λ) * (((n : ℝ) + 1) * ∫ y in Cube' n, c j y ^ 2) := fun j hj =>
    mul_le_mul_of_nonpos_left (hocc j)
      (sub_nonpos.2 (hmono (by simp at hj; omega)))
  have hsum := Finset.sum_le_sum hterm
  simp only [← Finset.sum_mul] at hsum
  have hN : ((n : ℝ) + 1) * ((∑ j ∈ Finset.range (n + 1), (lam j - Λ) * ∫ y in Cube' n, c j y ^ 2) +
      Λ * ∫ x, X x * X x ∂μN n) ≤ kinN X + v (rhoE .fer X) := by
    rw [← hE]; exact mul_le_mul_of_nonneg_left hint (by positivity)
  have hexp : ((n : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * ∫ y in Cube' n, c j y ^ 2 =
      ∑ j ∈ Finset.range (n + 1), (lam j - Λ) * (((n : ℝ) + 1) * ∫ y in Cube' n, c j y ^ 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hΛ : ∑ j ∈ Finset.range (n + 1), (lam j - Λ) =
      ∑ j ∈ Finset.range (n + 1), lam j - ((n : ℝ) + 1) * Λ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  rw [hΛ] at hsum
  nlinarith [hsum, hN, hexp]

include hbd in
/-- **Lower bound for smooth bosonic states**: `N λ₀ ∫ X² ≤ T(X) + v(ρ_X)`. -/
theorem lower_smooth_bos {X : Cfg n → ℝ} (hX : X ∈ DomC .bos n) (hXN : X ∈ DomN .bos n) :
    ((n : ℝ) + 1) * lam 0 * ∫ x, X x * X x ∂μN n ≤ kinN X + v (rhoE .bos X) := by
  have hJs : Continuous fun y => ‖JE (sE hX y)‖ ^ 2 :=
    (JE.continuous.comp (continuous_sE hX)).norm.pow 2
  have hpt : ∀ y, lam 0 * ‖JE (sE hX y)‖ ^ 2 ≤ ‖(sE hX y).snd‖ ^ 2 + v (dE (sE hX y)) :=
    fun y => by simpa using hbd 0 (sE hX y)
  have hint := integral_mono ((int_JE_sq hX).const_mul (lam 0))
    ((int_snd_sq hX).add (int_v_dE v hX)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_const_mul, ← integral_sq_eq_slices hX] at hint
  rw [← integral_slice_energy v hX hXN, mul_assoc]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

end lower

/-! ### Passing to all `H¹` states -/

/-- If `b_M² ≤ a c_M` and `c_M → 0`, then `b_M → 0`. -/
lemma tendsto_of_sq_le {a : ℝ} {b c : ℕ → ℝ} (hbc : ∀ M, b M ^ 2 ≤ a * c M)
    (hc : Tendsto c atTop (𝓝 0)) : Tendsto b atTop (𝓝 0) := by
  have hac : Tendsto (fun M => a * c M) atTop (𝓝 0) := by simpa using hc.const_mul a
  have hs : Tendsto (fun M => √(a * c M)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hac
    rw [Real.sqrt_zero] at h
    exact h
  refine squeeze_zero_norm (fun M => ?_) hs
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (hbc M)

lemma sq_le_of_quad {a b c : ℝ} (h : ∀ s : ℝ, 0 ≤ a + 2 * s * b + s ^ 2 * c) : b ^ 2 ≤ a * c := by
  have := discrim_le_zero (a := c) (b := 2 * b) (c := a) fun s => by nlinarith [h s]
  rw [discrim] at this; nlinarith

variable {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN τ n)
include hΦ

omit hΦ in
lemma truncC_eq_sub (M : ℕ) : truncC M Φ = Φ + (-1 : ℝ) • (Φ - truncC M Φ) := by
  funext x; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

/-- **Kinetic energies of the truncations converge.** -/
lemma tendsto_kinN_truncC : Tendsto (fun M => kinN (truncC M Φ)) atTop (𝓝 (kinN Φ)) := by
  have hY : ∀ M, H1NW (Φ - truncC M Φ) := fun M => h1NW_of_mem (sub_mem hΦ (truncC_memN hΦ M))
  have hP := h1NW_of_mem hΦ
  have hk := tendsto_kinN_sub_truncC hΦ
  have hb : Tendsto (fun M => kinN2 Φ (Φ - truncC M Φ)) atTop (𝓝 0) :=
    tendsto_of_sq_le (fun M => sq_le_of_quad fun s => by
      rw [← kinN_expand hP (hY M) s]; exact kinN_nonneg _) hk
  have e : ∀ M, kinN (truncC M Φ) =
      kinN Φ + 2 * (-1) * kinN2 Φ (Φ - truncC M Φ) + (-1) ^ 2 * kinN (Φ - truncC M Φ) := fun M => by
    rw [← kinN_expand hP (hY M), ← truncC_eq_sub]
  have h := ((tendsto_const_nhds (x := kinN Φ)).add (hb.const_mul (2 * -1))).add
    (hk.const_mul ((-1 : ℝ) ^ 2))
  rw [mul_zero, mul_zero, add_zero, add_zero] at h
  exact h.congr fun M => (e M).symm

/-- **`L²` norms of the truncations converge.** -/
lemma tendsto_sq_truncC :
    Tendsto (fun M => ∫ x, truncC M Φ x * truncC M Φ x ∂μN n) atTop
      (𝓝 (∫ x, Φ x * Φ x ∂μN n)) := by
  set Y := fun M => Φ - truncC M Φ
  have hYm : ∀ M, MemLp (Y M) 2 (μN n) := fun M => (sub_mem hΦ (truncC_memN hΦ M)).1
  have hP := hΦ.1
  have hI : ∀ M, Integrable (fun x => Φ x * Y M x) (μN n) := fun M => hP.integrable_mul (hYm M)
  have hII : Integrable (fun x => Φ x * Φ x) (μN n) := hP.integrable_mul hP
  have hYY : ∀ M, Integrable (fun x => Y M x * Y M x) (μN n) := fun M =>
    (hYm M).integrable_mul (hYm M)
  have hquad : ∀ M (s : ℝ), ∫ x, (Φ x + s * Y M x) * (Φ x + s * Y M x) ∂μN n =
      ∫ x, Φ x * Φ x ∂μN n + 2 * s * ∫ x, Φ x * Y M x ∂μN n +
        s ^ 2 * ∫ x, Y M x * Y M x ∂μN n := fun M s => by
    have hf : (fun x => (Φ x + s * Y M x) * (Φ x + s * Y M x)) = fun x =>
        (Φ x * Φ x + (2 * s) * (Φ x * Y M x)) + s ^ 2 * (Y M x * Y M x) := by
      funext x; ring
    have h1 : Integrable (fun x => Φ x * Φ x + 2 * s * (Φ x * Y M x)) (μN n) :=
      hII.add ((hI M).const_mul (2 * s))
    have h2 : Integrable (fun x => s ^ 2 * (Y M x * Y M x)) (μN n) := (hYY M).const_mul _
    have h3 : Integrable (fun x => 2 * s * (Φ x * Y M x)) (μN n) := (hI M).const_mul _
    rw [hf, integral_add h1 h2, integral_add hII h3, integral_const_mul, integral_const_mul]
  have hc : Tendsto (fun M => ∫ x, Y M x * Y M x ∂μN n) atTop (𝓝 0) := by
    simpa [Y, sq] using tendsto_sq_sub_truncC hΦ
  have hb : Tendsto (fun M => ∫ x, Φ x * Y M x ∂μN n) atTop (𝓝 0) :=
    tendsto_of_sq_le (fun M => sq_le_of_quad fun s => by
        rw [← hquad]; exact integral_nonneg fun x => mul_self_nonneg _) hc
  have e : ∀ M, ∫ x, truncC M Φ x * truncC M Φ x ∂μN n =
      ∫ x, Φ x * Φ x ∂μN n + 2 * (-1) * ∫ x, Φ x * Y M x ∂μN n +
        (-1) ^ 2 * ∫ x, Y M x * Y M x ∂μN n := fun M => by
    rw [← hquad]; congr 1; funext x; simp only [Y, Pi.sub_apply]; ring
  have h := ((tendsto_const_nhds (x := ∫ x, Φ x * Φ x ∂μN n)).add (hb.const_mul (2 * -1))).add
    (hc.const_mul ((-1 : ℝ) ^ 2))
  rw [mul_zero, mul_zero, add_zero, add_zero] at h
  exact h.congr fun M => (e M).symm

/-- **Potential energies of the truncations converge.** -/
lemma tendsto_v_truncC (v : PotH) :
    Tendsto (fun M => v (rhoE τ (truncC M Φ))) atTop (𝓝 (v (rhoE τ Φ))) := by
  have hT : ∀ M, truncC M Φ ∈ DomN τ n := truncC_memN hΦ
  have hS : Tendsto (fun M => SHN (truncC M Φ - Φ)) atTop (𝓝 0) := by
    have e : ∀ M, SHN (truncC M Φ - Φ) = ((n : ℝ) + 1) * ∫ x, (Φ - truncC M Φ) x ^ 2 ∂μN n +
        kinN (Φ - truncC M Φ) := fun M => by
      have h1 : truncC M Φ - Φ = (-1 : ℝ) • (Φ - truncC M Φ) := by
        funext x; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [SHN, h1, kinN_smul (h1NW_of_mem (sub_mem hΦ (hT M)))]
      congr 2
      · congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
      · ring
    simp only [e]
    simpa using ((tendsto_sq_sub_truncC hΦ).const_mul ((n : ℝ) + 1)).add (tendsto_kinN_sub_truncC hΦ)
  -- `SHN (X_M + Φ)` stays bounded
  have hB : ∃ B, ∀ M, SHN (truncC M Φ + Φ) ≤ B := by
    have hk := tendsto_kinN_truncC hΦ
    have hl := tendsto_sq_truncC hΦ
    obtain ⟨B1, hB1⟩ := hk.bddAbove_range
    obtain ⟨B2, hB2⟩ := hl.bddAbove_range
    refine ⟨2 * (((n : ℝ) + 1) * B2 + B1) + 2 * SHN Φ, fun M => ?_⟩
    have h := SHN_add_le (h1NW_of_mem (hT M)) (h1NW_of_mem hΦ)
    have h1 : SHN (truncC M Φ) ≤ ((n : ℝ) + 1) * B2 + B1 := by
      have a1 := hB1 ⟨M, rfl⟩
      have a2 := hB2 ⟨M, rfl⟩
      simp only [SHN, sq]
      nlinarith
    linarith
  obtain ⟨B, hB⟩ := hB
  have hB0 : 0 ≤ B := le_trans (SHN_nonneg _) (hB 0)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm (a := fun M =>
    ‖v‖ * (8 * √(SHN (truncC M Φ - Φ) * B))) (fun M => ?_) ?_)
  · rw [norm_norm, ← map_sub, rhoE_sub_eq (hT M) hΦ]
    refine (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (norm_rhoE2_le (sub_mem (hT M) hΦ) (add_mem (hT M) hΦ)).trans ?_
    gcongr
    · exact SHN_nonneg _
    · exact hB M
  · have hSB : Tendsto (fun M => SHN (truncC M Φ - Φ) * B) atTop (𝓝 0) := by
      simpa using hS.mul_const B
    have := (Real.continuous_sqrt.tendsto 0).comp hSB
    simpa using (this.const_mul 8).const_mul ‖v‖

omit hΦ

variable (v : PotH) {φ : ℕ → H1E} {lam : ℕ → ℝ} {b : HilbertBasis ℕ ℝ HL}
  (hJ : ∀ k, JE (φ k) = b k)
  (hbd : ∀ (N : ℕ) (ψ : H1E), ∑ j ∈ Finset.range N, lam j * ⟪b j, JE ψ⟫_ℝ ^ 2 +
    lam N * (‖JE ψ‖ ^ 2 - ∑ j ∈ Finset.range N, ⟪b j, JE ψ⟫_ℝ ^ 2) ≤ ‖ψ.snd‖ ^ 2 + v (dE ψ))

include hJ hbd in
/-- **Lower bound for free fermions**: every `H¹` state has `T + v(ρ) ≥ Σ_{j ≤ n} λ_j ∫ Φ²`. -/
theorem lower_fer (hmono : Monotone lam) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN .fer n) :
    (∑ j ∈ Finset.range (n + 1), lam j) * ∫ x, Φ x * Φ x ∂μN n ≤ kinN Φ + v (rhoE .fer Φ) :=
  le_of_tendsto_of_tendsto ((tendsto_sq_truncC hΦ).const_mul _)
    ((tendsto_kinN_truncC hΦ).add (tendsto_v_truncC hΦ v))
    (Eventually.of_forall fun M => lower_smooth_fer v hJ hbd hmono (truncC_mem hΦ M)
      (truncC_memN hΦ M))

include hbd in
/-- **Lower bound for free bosons**: every `H¹` state has `T + v(ρ) ≥ N λ₀ ∫ Φ²`. -/
theorem lower_bos {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomN .bos n) :
    ((n : ℝ) + 1) * lam 0 * ∫ x, Φ x * Φ x ∂μN n ≤ kinN Φ + v (rhoE .bos Φ) :=
  le_of_tendsto_of_tendsto ((tendsto_sq_truncC hΦ).const_mul _)
    ((tendsto_kinN_truncC hΦ).add (tendsto_v_truncC hΦ v))
    (Eventually.of_forall fun M => lower_smooth_bos v hbd (truncC_mem hΦ M) (truncC_memN hΦ M))

/-! ### Non-interacting ground states -/

/-- `∫ det f · det f' = Σ_{σ,τ} sgn σ sgn τ Π_i ∫ f_{σ i} f'_{τ i}`. -/
lemma integral_slater_mul {f f' : Fin (n + 1) → ℝ → ℝ} (hf : ∀ j, Continuous (f j))
    (hf' : ∀ j, Continuous (f' j)) :
    ∫ x, slater f x * slater f' x ∂μN n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ τ : Equiv.Perm (Fin (n + 1)),
        sgn σ * sgn τ * ∏ i, ∫ t, f (σ i) t * f' (τ i) t ∂vol01 := by
  have e : ∀ x : Cfg n, slater f x * slater f' x =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ τ : Equiv.Perm (Fin (n + 1)),
        sgn σ * sgn τ * ∏ i, (f (σ i) (x i) * f' (τ i) (x i)) := fun x => by
    rw [slater_eq_sum, slater_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  have hc : ∀ σ τ : Equiv.Perm (Fin (n + 1)), Continuous fun x : Cfg n =>
      sgn σ * sgn τ * ∏ i, (f (σ i) (x i) * f' (τ i) (x i)) := fun σ τ =>
    continuous_const.mul (continuous_finsetProd (s := Finset.univ)
      (f := fun i (x : Cfg n) => f (σ i) (x i) * f' (τ i) (x i)) fun i _ =>
        ((hf (σ i)).comp (continuous_apply i)).mul ((hf' (τ i)).comp (continuous_apply i)))
  simp only [e]
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ => integrableN (hc σ τ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ fun τ _ => integrableN (hc σ τ)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_prod_cube (fun i t => f (σ i) t * f' (τ i) t)]

lemma QNH_free (τ : Stat) (v : PotH) (Φ : Cfg n → ℝ) :
    QNH τ 0 v Φ = kinN Φ + v (rhoE τ Φ) := by
  simp only [QNH, Pi.zero_apply, zero_mul, integral_zero, add_zero]

/-- **Non-interacting fermions with Neumann walls** (`v ∈ H⁻¹`): with the Neumann orbitals
`φ_k` and eigenvalues `λ_k` of `-d²/dx² + v`, the ground-state energy is `Σ_{j<N} λ_j`, the
Slater determinant of `φ₀, …, φ_{N-1}` is a ground state, and `λ_{N-1} < λ_N`. -/
theorem gs_free_fer (v : PotH) :
    ∃ (φ : ℕ → H1E) (lam : ℕ → ℝ), Monotone lam ∧ Tendsto lam atTop atTop ∧
      (∀ a b, ⟪JE (φ a), JE (φ b)⟫_ℝ = if a = b then 1 else 0) ∧
      (∀ k g, ⟪(φ k).snd, g.snd⟫_ℝ + v (dE2 (φ k) g) = lam k * ⟪JE (φ k), JE g⟫_ℝ) ∧
      gsEH .fer (0 : Cfg n → ℝ) v = ∑ j ∈ Finset.range (n + 1), lam j ∧
      IsGSNH .fer 0 v (slN fun j : Fin (n + 1) => φ j) ∧ lam n < lam (n + 1) := by
  obtain ⟨φ, lam, b, hm, ht, hJ, heig, hbd⟩ := exists_neuOrbitals v
  have hw : Continuous (0 : Cfg n → ℝ) := continuous_const
  have hon : ∀ a b, ⟪JE (φ a), JE (φ b)⟫_ℝ = if a = b then 1 else 0 := fun a c => by
    rw [hJ, hJ]; exact orthonormal_iff_ite.1 b.orthonormal a c
  have hlam : ∀ k, ‖(φ k).snd‖ ^ 2 + v (dE (φ k)) = lam k := fun k => by
    have := heig k (φ k)
    rw [real_inner_self_eq_norm_sq, dE2_self, real_inner_self_eq_norm_sq, hJ,
      b.orthonormal.1 k, one_pow, mul_one] at this
    exact this
  -- every normalised state has energy at least `Σ λ_j`
  have hlow : ∀ Ψ ∈ DomN .fer n, ∫ x, Ψ x ^ 2 ∂μN n = 1 →
      ∑ j ∈ Finset.range (n + 1), lam j ≤ QNH .fer 0 v Ψ := fun Ψ hΨ hn => by
    have h := lower_fer v hJ hbd hm hΨ
    simp only [← sq, hn, mul_one] at h
    rw [QNH_free]; exact h
  -- a Slater determinant of orthonormal orbitals with energy `Σ λ` is a ground state
  have hgs : ∀ e : Fin (n + 1) → H1E, (∀ a c, ⟪JE (e a), JE (e c)⟫_ℝ = if a = c then 1 else 0) →
      QNH .fer 0 v (slN e) = ∑ j ∈ Finset.range (n + 1), lam j → IsGSNH .fer 0 v (slN e) :=
    fun e he hE => ⟨slN_memN e, by simpa only [sq] using integral_slN_sq he,
      fun Ψ hΨ hn => hE ▸ hlow Ψ hΨ hn⟩
  set e : Fin (n + 1) → H1E := fun j => φ j
  have he : ∀ a c, ⟪JE (e a), JE (e c)⟫_ℝ = if a = c then 1 else 0 := fun a c => by
    simp only [e, hon, Fin.val_inj]
  have hE : QNH .fer 0 v (slN e) = ∑ j ∈ Finset.range (n + 1), lam j := by
    rw [QNH_slN he, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => hlam j
  have hGS := hgs e he hE
  refine ⟨φ, lam, hm, ht, hon, heig, ?_, hGS, ?_⟩
  · rw [gsEH_of_isGSNH hw hGS, hE]
  -- the gap
  by_contra hgap
  have heq : lam n = lam (n + 1) := le_antisymm (hm (Nat.le_succ n)) (not_lt.1 hgap)
  set idx : Fin (n + 1) → ℕ := fun j => if j = Fin.last n then n + 1 else j
  have hidx : ∀ a c, idx a = idx c ↔ a = c := fun a c => by
    have ha := a.2; have hc := c.2
    simp only [idx]
    by_cases h1 : a = Fin.last n <;> by_cases h2 : c = Fin.last n
    · simp [h1, h2]
    · have : (c : ℕ) ≠ n := fun h => h2 (Fin.ext (by simp [h]))
      simp only [h1, h2, ↓reduceIte]; constructor <;> intro h <;> [omega; exact absurd h.symm h2]
    · have : (a : ℕ) ≠ n := fun h => h1 (Fin.ext (by simp [h]))
      simp only [h1, h2, ↓reduceIte]; constructor <;> intro h <;> [omega; exact h.elim]
    · simp only [h1, h2, ↓reduceIte, Fin.val_inj]
  set e' : Fin (n + 1) → H1E := fun j => φ (idx j)
  have he' : ∀ a c, ⟪JE (e' a), JE (e' c)⟫_ℝ = if a = c then 1 else 0 := fun a c => by
    simp only [e', hon, hidx]
  have hE' : QNH .fer 0 v (slN e') = ∑ j ∈ Finset.range (n + 1), lam j := by
    rw [QNH_slN he', ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [e', idx, Fin.castSucc_ne_last, ↓reduceIte, hlam, Fin.val_castSucc, Fin.val_last,
      heq]
  have hGS' := hgs e' he' hE'
  -- the two determinants are orthogonal
  have horth : ∫ x, slN e x * slN e' x ∂μN n = 0 := by
    have h0 : ∫ x, slater (orbs e) x * slater (orbs e') x ∂μN n = 0 := by
      rw [integral_slater_mul (f := orbs e) (f' := orbs e') (fun j => continuous_orbF (e j))
        (fun j => continuous_orbF (e' j))]
      refine Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun τ _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ (τ.symm (Fin.last n)))]
      · ring
      · simp only [orbs, integral_orbF_mul, Equiv.apply_symm_apply, e', e, idx, ↓reduceIte, hon]
        have := (σ (τ.symm (Fin.last n))).2
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        omega
    simp only [slN, Pi.smul_apply, smul_eq_mul]
    have : (fun x => (√(Nat.factorial (n + 1) : ℝ))⁻¹ * slater (orbs e) x *
        ((√(Nat.factorial (n + 1) : ℝ))⁻¹ * slater (orbs e') x)) = fun x =>
        ((√(Nat.factorial (n + 1) : ℝ))⁻¹ * (√(Nat.factorial (n + 1) : ℝ))⁻¹) *
          (slater (orbs e) x * slater (orbs e') x) := by funext x; ring
    rw [this, integral_const_mul, h0, mul_zero]
  have hn1 := integral_slN_sq he
  rcases gsNH_unique hw hGS hGS' with h | h
  · have : ∫ x, slN e x * slN e' x ∂μN n = ∫ x, slN e x * slN e x ∂μN n :=
      integral_congr_ae (h.mono fun x hx => by simp only [hx])
    rw [horth, hn1] at this; exact absurd this (by norm_num)
  · have : ∫ x, slN e x * slN e' x ∂μN n = -∫ x, slN e x * slN e x ∂μN n := by
      rw [← integral_neg]
      exact integral_congr_ae (h.mono fun x hx => by simp [hx])
    rw [horth, hn1] at this; exact absurd this (by norm_num)

/-- **Non-interacting bosons with Neumann walls** (`v ∈ H⁻¹`): the ground-state energy is
`N λ₀` and the product state `φ₀^{⊗N}` is a ground state. -/
theorem gs_free_bos (v : PotH) :
    ∃ (φ₀ : H1E) (lam₀ : ℝ), ‖JE φ₀‖ = 1 ∧
      (∀ g, ⟪φ₀.snd, g.snd⟫_ℝ + v (dE2 φ₀ g) = lam₀ * ⟪JE φ₀, JE g⟫_ℝ) ∧
      gsEH .bos (0 : Cfg n → ℝ) v = ((n : ℝ) + 1) * lam₀ ∧ IsGSNH .bos 0 v (prN (n := n) φ₀) := by
  obtain ⟨φ, lam, b, hm, ht, hJ, heig, hbd⟩ := exists_neuOrbitals v
  have hw : Continuous (0 : Cfg n → ℝ) := continuous_const
  have h1 : ‖JE (φ 0)‖ = 1 := by rw [hJ]; exact b.orthonormal.1 0
  have hlam : ‖(φ 0).snd‖ ^ 2 + v (dE (φ 0)) = lam 0 := by
    have := heig 0 (φ 0)
    rw [real_inner_self_eq_norm_sq, dE2_self, real_inner_self_eq_norm_sq, h1, one_pow,
      mul_one] at this
    exact this
  have hE : QNH .bos 0 v (prN (n := n) (φ 0)) = ((n : ℝ) + 1) * lam 0 := by
    rw [QNH_prN h1, hlam]
  have hGS : IsGSNH .bos 0 v (prN (n := n) (φ 0)) :=
    ⟨prN_memN _, by simpa only [sq] using integral_prN_sq (n := n) h1, fun Ψ hΨ hn => by
      have h := lower_bos v hbd hΨ
      simp only [← sq, hn, mul_one] at h
      rw [hE, QNH_free]; exact h⟩
  exact ⟨φ 0, lam 0, h1, heig 0, by rw [gsEH_of_isGSNH hw hGS, hE], hGS⟩

end DFT.Continuum.Line
