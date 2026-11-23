/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.General.HK

/-!
# Pure and ensemble `v`-representability, abstractly

* `PureDens`, `EnsDens`, `PureVRep`, `EnsVRep`: densities of normalised ground states and of finite
  ground-state ensembles;
* `pureDens_of_ensDens`: if all normalised ground states of `v` have the same density, every
  ensemble density of `v` is a pure one;
* `dens_eq_of_ae_smul`: normalised states that are a.e. proportional have the same density.
-/

namespace DFT.Continuum

open MeasureTheory

/-! ### Pure and ensemble densities, abstractly -/

section general

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {P : Type*} [AddCommGroup P] [Module ℝ P]
  (S : Setting μ P)

/-- `ρ` is the density of a normalised ground state of `H(v)`. -/
def PureDens (v : P) (ρ : P → ℝ) : Prop :=
  ∃ ψ, IsGS S v ψ ∧ ip (μ := μ) ψ ψ = 1 ∧ dens S ψ = ρ

/-- `ρ` is the density of a ground-state ensemble of `H(v)`: a finite convex combination of
densities of normalised ground states. -/
def EnsDens (v : P) (ρ : P → ℝ) : Prop :=
  ∃ (m : ℕ) (lam : Fin m → ℝ) (ψ : Fin m → X → ℝ), (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
    (∀ i, IsGS S v (ψ i) ∧ ip (μ := μ) (ψ i) (ψ i) = 1) ∧ ρ = ∑ i, lam i • dens S (ψ i)

/-- Pure-state `v`-representability. -/
def PureVRep (ρ : P → ℝ) : Prop := ∃ v, PureDens S v ρ

/-- Ensemble `v`-representability. -/
def EnsVRep (ρ : P → ℝ) : Prop := ∃ v, EnsDens S v ρ

variable {S}

lemma ensDens_of_pureDens {v : P} {ρ : P → ℝ} (h : PureDens S v ρ) : EnsDens S v ρ := by
  obtain ⟨ψ, hψ, h1, rfl⟩ := h
  exact ⟨1, fun _ => 1, fun _ => ψ, fun _ => zero_le_one, by simp, fun _ => ⟨hψ, h1⟩, by simp⟩

/-- If all normalised ground states of `v` have the same density, every ensemble density of `v`
is a pure one. -/
theorem pureDens_of_ensDens {v : P} {ρ : P → ℝ}
    (huniq : ∀ ψ φ, IsGS S v ψ → ip (μ := μ) ψ ψ = 1 → IsGS S v φ → ip (μ := μ) φ φ = 1 →
      dens S ψ = dens S φ)
    (h : EnsDens S v ρ) : PureDens S v ρ := by
  obtain ⟨m, lam, ψ, -, hsum, hψ, rfl⟩ := h
  cases m with
  | zero => simp at hsum
  | succ m =>
    refine ⟨ψ 0, (hψ 0).1, (hψ 0).2, ?_⟩
    have e : ∀ i, lam i • dens S (ψ i) = lam i • dens S (ψ 0) := fun i => by
      rw [huniq (ψ i) (ψ 0) (hψ i).1 (hψ i).2 (hψ 0).1 (hψ 0).2]
    rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_smul, hsum, one_smul]

/-- Two normalised states that are a.e. proportional have the same density. -/
lemma dens_eq_of_ae_smul {ψ φ : X → ℝ} {c : ℝ} (h : ψ =ᵐ[μ] c • φ)
    (hψ : ip (μ := μ) ψ ψ = 1) (hφ : ip (μ := μ) φ φ = 1) : dens S ψ = dens S φ := by
  have hsq : (fun x => ψ x * ψ x) =ᵐ[μ] fun x => c * c * (φ x * φ x) := by
    filter_upwards [h] with x hx
    rw [hx]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hc : c * c = 1 := by
    have : ip (μ := μ) ψ ψ = c * c * ip (μ := μ) φ φ := by
      simp only [ip]; rw [integral_congr_ae hsq, integral_const_mul]
    rw [hψ, hφ, mul_one] at this; exact this.symm
  funext w
  simp only [dens, pf]
  rw [integral_congr_ae (by filter_upwards [hsq] with x hx; exact congrArg (S.L w x * ·) hx),
    show (fun x => S.L w x * (c * c * (φ x * φ x))) = fun x => S.L w x * (φ x * φ x) from
      funext fun x => by rw [hc, one_mul]]

end general

end DFT.Continuum
