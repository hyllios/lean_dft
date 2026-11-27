/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureNFer
import DFT.Continuum.Line.MeasurePotential.MeasureNHK

/-!
# Hohenberg–Kohn for interacting particles in measure potentials, along continuous directions

For `N` interacting bosons or fermions (continuous `w`) in a measure potential `ν`, a continuous
perturbation `ν + v dx` that keeps a ground state is a constant (**`hk_cont_dir`**). With the first
half of Hohenberg–Kohn: if `ν` and `ν + v dx` have ground states with the same density, then `v` is
constant (**`hk_cont_pert`**). So every measure potential is determined by its ground-state density
within its class `ν + C([0, 1])`.

The proof: subtracting the two Euler–Lagrange equations gives `∫ (Σₖ v(xₖ) - c) Φ Ψ = 0` for all
`Ψ ∈ H¹₀`, so `(Σₖ v(xₖ) - c) Φ = 0` a.e. (`sep_lineW`); unique continuation for ground states of
measure potentials (`gsN_ne_zero_bos`, `gsN_ne_zero_fer`) gives `Σₖ v(xₖ) = c`, hence `v` is
constant (`rigidL_line`).

The general case, `ν - ν'` an arbitrary measure, needs in addition that `ν - ν'` is absolutely
continuous; see the formalization log.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ} {w : Cfg n → ℝ}

/-- A continuous potential `v` as a functional: `h ↦ ∫ v h`. -/
noncomputable def vCLM (v : C01) : PotM :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ t, iccExt v t * iccExt h t ∂vol01
      map_add' := fun h h' => by
        have := int_ext_add_smul v h h' 1 1
        simpa using this
      map_smul' := fun c h => by simpa using int_ext_smul v h c }
    ‖v‖ fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have hb : ∀ (r : C01) (x : ℝ), |iccExt r x| ≤ ‖r‖ := fun r x => ext_le_norm r x
      calc ‖∫ t, iccExt v t * iccExt h t ∂vol01‖ ≤ ‖v‖ * ‖h‖ * vol01.real univ :=
            norm_integral_le_of_norm_le_const (ae_of_all _ fun t => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul (hb v t) (hb h t) (abs_nonneg _) (norm_nonneg _))
        _ = ‖v‖ * ‖h‖ := by simp

lemma vCLM_apply (v h : C01) : vCLM v h = ∫ t, iccExt v t * iccExt h t ∂vol01 := rfl

lemma gsN_ne_zero (hw : Continuous w) {τ : Stat} {ν : PotM} {Φ : Cfg n → ℝ}
    (h : IsGSN τ w ν Φ) : ∀ᵐ x ∂μN n, Φ x ≠ 0 := by
  cases τ with
  | bos => exact gsN_ne_zero_bos hw h
  | fer => exact gsN_ne_zero_fer hw h

/-- **Rigidity along continuous directions**: if `Φ` is a ground state of both `ν` and
`ν + v dx`, with `v` continuous, then `v` is constant. -/
theorem hk_cont_dir (hw : Continuous w) {τ : Stat} {ν : PotM} {v : C01} {Φ : Cfg n → ℝ}
    (h : IsGSN τ w ν Φ) (h' : IsGSN τ w (ν + vCLM v) Φ) : ∃ k : ℝ, v = k • one := by
  set c := QMN τ w (ν + vCLM v) Φ - QMN τ w ν Φ
  have hsep : ∀ Ψ ∈ DomW τ n,
      ∫ x, ((settingW τ n w hw).L v x - c) * Φ x * Ψ x ∂μN n = 0 := fun Ψ hΨ => by
    have e1 := euler_lagrangeN hw h hΨ
    have e2 := euler_lagrangeN hw h' hΨ
    rw [add_apply, vCLM_apply, int_rhoHat2 hw h.1 hΨ] at e2
    have hpf : pf (settingW τ n w hw) v Φ Ψ = ∫ x, (settingW τ n w hw).L v x * (Φ x * Ψ x) ∂μN n :=
      rfl
    have i1 : Integrable (fun x => (settingW τ n w hw).L v x * (Φ x * Ψ x)) (μN n) :=
      (settingW τ n w hw).int_L v Φ Ψ h.1 hΨ
    have i2 : Integrable (fun x => c * (Φ x * Ψ x)) (μN n) := (int_mul_L2 h.1.1 hΨ.1).const_mul c
    have e : ∫ x, ((settingW τ n w hw).L v x - c) * Φ x * Ψ x ∂μN n =
        pf (settingW τ n w hw) v Φ Ψ - c * ∫ x, Φ x * Ψ x ∂μN n := by
      rw [hpf, ← integral_const_mul, ← integral_sub i1 i2]
      congr 1; funext x; ring
    rw [e]; simp only [c]; linarith
  have h0 := sep_lineW w hw v c Φ h.1 hsep
  have hL : (settingW τ n w hw).L v =ᵐ[μN n] fun _ => c := by
    filter_upwards [h0, gsN_ne_zero hw h] with x hx hne
    simp only [Pi.zero_apply, mul_eq_zero] at hx
    rcases hx with hx | hx
    · linarith
    · exact absurd hx hne
  exact rigidL_lineW (s := τ.toSym) w hw v c hL

/-- **Hohenberg–Kohn within `ν + C([0, 1])`**: if `ν` and `ν + v dx` (`v` continuous) have
normalised ground states with the same density, for interacting bosons or fermions, then `v` is
constant. -/
theorem hk_cont_pert (hw : Continuous w) {τ : Stat} {ν : PotM} {v : C01} {Φ Φ' : Cfg n → ℝ}
    (h : IsGSN τ w ν Φ) (h' : IsGSN τ w (ν + vCLM v) Φ') (hρ : rhoHat τ Φ = rhoHat τ Φ') :
    ∃ k : ℝ, v = k • one :=
  hk_cont_dir hw h (isGSN_of_same_dens h h' hρ).1

/-! ### Pointwise Cauchy–Schwarz for the continuous densities

A first ingredient for the general case (`ν - ν'` an arbitrary measure): the mixed density is
controlled pointwise by the densities. -/

lemma rhoHat_nonneg (τ : Stat) (Φ : Cfg n → ℝ) (t : Icc (0 : ℝ) 1) : 0 ≤ rhoHat τ Φ t := by
  rw [rhoHat_apply]; positivity

/-- **`ρ̂(A, B)² ≤ ρ̂(A) ρ̂(B)` pointwise.** -/
theorem rhoHat2_sq_le (hw : Continuous w) {τ : Stat} {A B : Cfg n → ℝ} (hA : A ∈ DomW τ n)
    (hB : B ∈ DomW τ n) (t : Icc (0 : ℝ) 1) :
    rhoHat2 τ A B t ^ 2 ≤ rhoHat τ A t * rhoHat τ B t := by
  have h : ∀ s : ℝ, 0 ≤ rhoHat τ B t * (s * s) + 2 * rhoHat2 τ A B t * s + rhoHat τ A t :=
    fun s => by
      have := rhoHat_nonneg τ (A + s • B) t
      rw [rhoHat_expand hw hA hB s] at this
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, one_mul] at this
      linarith
  have := discrim_le_zero h
  simp only [discrim] at this
  nlinarith

/-- `|ρ̂(A, B)| ≤ √(ρ̂(A) ρ̂(B))`. -/
theorem abs_rhoHat2_le (hw : Continuous w) {τ : Stat} {A B : Cfg n → ℝ} (hA : A ∈ DomW τ n)
    (hB : B ∈ DomW τ n) (t : Icc (0 : ℝ) 1) :
    |rhoHat2 τ A B t| ≤ √(rhoHat τ A t * rhoHat τ B t) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (rhoHat2_sq_le hw hA hB t)

/-- **The density is controlled in sup norm by the `H¹` norm**: `ρ̂_X ≤ a N ∫ X² + T(X)/a`. -/
theorem rhoHat_le {τ : Stat} {X : Cfg n → ℝ} (hX : X ∈ DomW τ n) {a : ℝ} (ha : 0 < a)
    (t : Icc (0 : ℝ) 1) :
    rhoHat τ X t ≤ a * ((n + 1) * ∫ x, X x ^ 2 ∂μN n) + kinW X / a := by
  rw [rhoHat_apply]
  have h := sq_le_H10 (h10_gN (τ := τ) X) ha t.2
  rw [integral_gN_sq hX] at h
  have hk : kinM (gN τ X) / a ≤ kinW X / a := div_le_div_of_nonneg_right (kinM_gN_le hX) ha.le
  linarith

/-- The mixed density is controlled by `H¹` norms:
`|ρ̂(A, B)| ≤ √((a N ∫ A² + T(A)/a)(a N ∫ B² + T(B)/a))`. -/
theorem abs_rhoHat2_le_H1 (hw : Continuous w) {τ : Stat} {A B : Cfg n → ℝ} (hA : A ∈ DomW τ n)
    (hB : B ∈ DomW τ n) {a : ℝ} (ha : 0 < a) (t : Icc (0 : ℝ) 1) :
    |rhoHat2 τ A B t| ≤ √((a * ((n + 1) * ∫ x, A x ^ 2 ∂μN n) + kinW A / a) *
      (a * ((n + 1) * ∫ x, B x ^ 2 ∂μN n) + kinW B / a)) :=
  (abs_rhoHat2_le hw hA hB t).trans (Real.sqrt_le_sqrt (mul_le_mul (rhoHat_le hA ha t)
    (rhoHat_le hB ha t) (rhoHat_nonneg τ B t) ((rhoHat_nonneg τ A t).trans (rhoHat_le hA ha t))))

end DFT.Continuum.Line
