/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.UCP

/-!
# `N` particles in a measure potential: the energy

A measure potential `ν ∈ C([0, 1])*` acts on an `N`-particle state through its density, which must
then be a continuous function. For `Φ ∈ H¹₀`, `√ρ_Φ` has an `H¹₀` representative `g` with
`∫ g'² ≤ T(Φ)` (`sqrt_dens_H1W`, Hoffmann-Ostenhof), so `ρ̂_Φ = g²` is a continuous version of the
density.

* `gN`, `rhoHat`: the continuous density `ρ̂_Φ ∈ C([0, 1])`; `rhoHat_spec`: `∫ v ρ̂_Φ = ∫ v ρ_Φ`
  for continuous `v`; `pot_eq_of_integral`, `rhoHat_unique`: it is the only such continuous
  function. `integral_gN_sq`: `∫ ρ̂ = N ∫ Φ²`; `kinM_gN_le`: `∫ (√ρ̂)'² ≤ T(Φ)`.
* `QMN`: the energy `T(Φ) + ∫ w Φ² + ν(ρ̂_Φ)`; `IsGSN`: normalised minimisers; `VRepMeasN`:
  densities of ground states of measure potentials.
* **`abs_nu_rhoHat_le`** (form bound): `|ν(ρ̂_Φ)| ≤ ½ T(Φ) + C_ν N ∫ Φ²`; `QMN_ge`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ}

/-! ### Continuous functions on `[0, 1]` are determined by their integrals -/

lemma pot_eq_of_integral {p q : C01}
    (h : ∀ v : C01, ∫ t, SturmLiouville.iccExt v t * SturmLiouville.iccExt p t ∂vol01 = ∫ t, SturmLiouville.iccExt v t * SturmLiouville.iccExt q t ∂vol01) :
    p = q := by
  have hIoo : EqOn (SturmLiouville.iccExt p) (SturmLiouville.iccExt q) (Ioo 0 1) := eqOn_of_integral_pot (continuous_iccExt p)
    (continuous_iccExt q) fun u => h u
  have hIcc : EqOn (SturmLiouville.iccExt p) (SturmLiouville.iccExt q) (Icc 0 1) :=
    hIoo.of_subset_closure (continuous_iccExt p).continuousOn (continuous_iccExt q).continuousOn
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
  ext t
  have := hIcc t.2
  simpa [SturmLiouville.iccExt, projIcc_of_mem _ t.2] using this

/-! ### The continuous density -/

variable (τ : Stat)

open Classical in
/-- A continuous square root of the density: `g ∈ H¹₀` with `g² = ρ_Φ` a.e. and
`∫ g'² ≤ T(Φ)`. -/
noncomputable def gN (Φ : Cfg n → ℝ) : ℝ → ℝ :=
  if h : Φ ∈ DomW τ n then (sqrt_dens_H1W h).choose else 0

variable {τ}

lemma gN_spec {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) :
    H10 (gN τ Φ) ∧ (∀ᵐ t ∂vol01, gN τ Φ t ^ 2 = rhoN Φ t) ∧ kinM (gN τ Φ) ≤ kinW Φ := by
  simp only [gN, h, ↓reduceDIte]; exact (sqrt_dens_H1W h).choose_spec

lemma h10_gN (Φ : Cfg n → ℝ) : H10 (gN τ Φ) := by
  by_cases h : Φ ∈ DomW τ n
  · exact (gN_spec h).1
  · simp only [gN, h, ↓reduceDIte]
    exact ⟨AbsolutelyContinuousOnInterval.congr (f := fun _ => (0 : ℝ))
      (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
      (fun _ _ => rfl), rfl, rfl, by simp⟩

variable (τ)

/-- **The continuous density** `ρ̂_Φ = g²`. -/
noncomputable def rhoHat (Φ : Cfg n → ℝ) : C01 := sqP (h10_gN (τ := τ) Φ)

variable {τ}

lemma rhoHat_apply (Φ : Cfg n → ℝ) (t : Icc (0 : ℝ) 1) : rhoHat τ Φ t = gN τ Φ t ^ 2 := rfl

lemma ext_rhoHat {Φ : Cfg n → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    SturmLiouville.iccExt (rhoHat τ Φ) t = gN τ Φ t ^ 2 := by
  simp [SturmLiouville.iccExt, projIcc_of_mem _ ht, rhoHat_apply]

lemma ae_ext_rhoHat {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) :
    ∀ᵐ t ∂vol01, SturmLiouville.iccExt (rhoHat τ Φ) t = rhoN Φ t := by
  filter_upwards [(gN_spec h).2.1, ae_restrict_mem measurableSet_Ioo] with t h1 ht
  rw [ext_rhoHat (Ioo_subset_Icc_self ht), h1]

/-- `ρ̂_Φ` has the integrals of the density. -/
lemma rhoHat_spec {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) (v : C01) :
    ∫ t, SturmLiouville.iccExt v t * SturmLiouville.iccExt (rhoHat τ Φ) t ∂vol01 = ∫ t, SturmLiouville.iccExt v t * rhoN Φ t ∂vol01 :=
  integral_congr_ae ((ae_ext_rhoHat h).mono fun t ht => by simp only [ht])

/-- `ρ̂_Φ` is the only continuous function with the integrals of the density. -/
lemma rhoHat_unique {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) {p : C01}
    (hp : ∀ v : C01, ∫ t, SturmLiouville.iccExt v t * SturmLiouville.iccExt p t ∂vol01 = ∫ t, SturmLiouville.iccExt v t * rhoN Φ t ∂vol01) :
    rhoHat τ Φ = p :=
  pot_eq_of_integral fun v => by rw [rhoHat_spec h, hp]

lemma integral_gN_sq {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) :
    ∫ t, gN τ Φ t ^ 2 ∂vol01 = (n + 1) * ∫ x, Φ x ^ 2 ∂μN n := by
  rw [← integral_rhoN h.1]
  exact integral_congr_ae (gN_spec h).2.1

lemma kinM_gN_le {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) : kinM (gN τ Φ) ≤ kinW Φ := (gN_spec h).2.2

/-! ### The energy -/

variable (τ)

/-- The energy `T(Φ) + ∫ w Φ² + ν(ρ̂_Φ)` of an `N`-particle state in a measure potential. -/
noncomputable def QMN (w : Cfg n → ℝ) (ν : PotM) (Φ : Cfg n → ℝ) : ℝ :=
  h0W n w Φ Φ + ν (rhoHat τ Φ)

/-- `Φ` is a normalised ground state of `T + w + ν` among `H¹₀` states of statistics `τ`. -/
def IsGSN (w : Cfg n → ℝ) (ν : PotM) (Φ : Cfg n → ℝ) : Prop :=
  Φ ∈ DomW τ n ∧ ∫ x, Φ x ^ 2 ∂μN n = 1 ∧
    ∀ Ψ ∈ DomW τ n, ∫ x, Ψ x ^ 2 ∂μN n = 1 → QMN τ w ν Φ ≤ QMN τ w ν Ψ

/-- `ρ` is the density of an `N`-particle ground state of a measure potential `μ₊ - μ₋`. -/
def VRepMeasN (n : ℕ) (w : Cfg n → ℝ) (ρ : C01) : Prop :=
  ∃ (μp μm : Measure ℝ) (_ : IsMeas01 μp) (_ : IsMeas01 μm) (Φ : Cfg n → ℝ),
    IsGSN τ w (nuOf μp μm) Φ ∧ rhoHat τ Φ = ρ

variable {τ}

lemma h0W_self (w : Cfg n → ℝ) (Φ : Cfg n → ℝ) :
    h0W n w Φ Φ = kinW Φ + ∫ x, w x * (Φ x * Φ x) ∂μN n := rfl

/-! ### The form bound -/

/-- **Form bound**: `|ν(ρ̂_Φ)| ≤ ½ T(Φ) + C_ν N ∫ Φ²`. -/
theorem abs_nu_rhoHat_le (ν : PotM) {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) :
    |ν (rhoHat τ Φ)| ≤ kinW Φ / 2 + cM ν * ((n + 1) * ∫ x, Φ x ^ 2 ∂μN n) := by
  have := abs_nu_sq_le ν (h10_gN (τ := τ) Φ)
  rw [integral_gN_sq h] at this
  exact this.trans (by linarith [kinM_gN_le h])

/-- The energy is bounded below on normalised states, and controls the kinetic energy. -/
theorem QMN_ge {w : Cfg n → ℝ} (hw : Continuous w) (ν : PotM) :
    ∃ C, ∀ Φ ∈ DomW τ n, ∫ x, Φ x ^ 2 ∂μN n = 1 → kinW Φ / 2 - C ≤ QMN τ w ν Φ := by
  obtain ⟨B, hB⟩ := ae_bound_cont (n := n) hw
  refine ⟨cM ν * (n + 1) + B, fun Φ h hn => ?_⟩
  have h1 := abs_nu_rhoHat_le ν h
  rw [hn, mul_one] at h1
  have h2 : |∫ x, w x * (Φ x * Φ x) ∂μN n| ≤ B := by
    have hi := int_mul_L2 h.1 h.1
    calc |∫ x, w x * (Φ x * Φ x) ∂μN n| ≤ ∫ x, B * (Φ x * Φ x) ∂μN n := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le (hi.const_mul B) ?_
          filter_upwards [hB] with x hx
          rw [norm_mul, Real.norm_eq_abs (Φ x * Φ x), abs_of_nonneg (mul_self_nonneg _)]
          exact mul_le_mul_of_nonneg_right hx (mul_self_nonneg _)
      _ = B := by
          rw [integral_const_mul]
          have : ∫ x, Φ x * Φ x ∂μN n = 1 := by rw [← hn]; simp_rw [sq]
          rw [this, mul_one]
  rw [QMN, h0W_self]
  linarith [neg_abs_le (ν (rhoHat τ Φ)), neg_abs_le (∫ x, w x * (Φ x * Φ x) ∂μN n)]

end DFT.Continuum.Line
