/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import Mathlib.Algebra.QuadraticDiscriminant
import DFT.Continuum.Line.Neumann.Slices

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
lemma tendsto_of_sq_le {a : ℝ} {b c : ℕ → ℝ} (ha : 0 ≤ a) (hbc : ∀ M, b M ^ 2 ≤ a * c M)
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
    tendsto_of_sq_le (kinN_nonneg Φ) (fun M => sq_le_of_quad fun s => by
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
    tendsto_of_sq_le (integral_nonneg fun x => mul_self_nonneg (Φ x))
      (fun M => sq_le_of_quad fun s => by
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

end DFT.Continuum.Line
