/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.General.HK
import Mathlib.Data.EReal.Operations

/-!
# The Lieb functional on a general configuration space

Lieb's convex-analysis formulation of DFT, for the general setting of `Continuum/General/HK`.
Densities are
linear functionals on one-body potentials (`ρ_ψ(w) = ∫ (L w) ψ²`). With values in `EReal`:

* `gsE v = inf {⟨ψ, H(v) ψ⟩ : ψ normalised}` (the ground-state energy, possibly `-∞`);
* `liebF ρ = sup_v (gsE v - ρ(v))` (the Lieb functional, possibly `+∞`).

Results:

* `liebF_le_h0`: `F(ρ_ψ) ≤ h₀(ψ, ψ)` (Lieb lies below the constrained search).
* `gsE_le_liebF_add`, `gsE_eq_iInf`: the variational principle `E(v) = inf_ψ (F(ρ_ψ) + ρ_ψ(v))`, and
  `E(v) ≤ F(ρ) + ρ(v)` for every `ρ`.
* `liebF_convex`: `F` is convex.
* `liebF_of_isNGS`, `subgrad_of_isNGS`: at the density of a ground state of `v`, `F` equals the
  constrained search and `-v` is a subgradient of `F`.
* `isNGS_of_subgrad`: conversely, a subgradient at a constrained-search minimiser gives a ground
  state.
* `subgrad_unique`: **Hohenberg–Kohn in Lieb's form.** Under separation, rigidity and unique
  continuation, the subgradients of `F` at a ground-state density are `-v` up to constants.
-/

namespace DFT

namespace Continuum

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {P : Type*} [AddCommGroup P] [Module ℝ P]
  (S : Setting μ P)

/-- Normalised states. -/
def Nst : Set (X → ℝ) := {ψ | ψ ∈ S.D ∧ ip (μ := μ) ψ ψ = 1}

/-- `ψ` is a normalised ground state of `H(v)`. -/
def IsNGS (v : P) (ψ : X → ℝ) : Prop :=
  ψ ∈ Nst S ∧ ∀ φ ∈ Nst S, Q S v ψ ≤ Q S v φ

/-- The ground-state energy. -/
noncomputable def gsE (v : P) : EReal := ⨅ ψ ∈ Nst S, ((Q S v ψ : ℝ) : EReal)

/-- The Lieb functional. -/
noncomputable def liebF (ρ : P → ℝ) : EReal := ⨆ v, gsE S v - ((ρ v : ℝ) : EReal)

section ereal

lemma sub_coe_le {x : EReal} {r c : ℝ} :
    x - (r : EReal) ≤ (c : EReal) ↔ x ≤ ((c + r : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma coe_le_sub_coe {x : EReal} {r c : ℝ} :
    (c : EReal) ≤ x - (r : EReal) ↔ ((c + r : ℝ) : EReal) ≤ x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma le_add_coe_of_sub_le {x y : EReal} {r : ℝ} (h : x - (r : EReal) ≤ y) :
    x ≤ y + (r : EReal) := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top =>
    induction y using EReal.rec with
    | bot => simp at h
    | top => simp
    | coe y => simp at h
  | coe x =>
    induction y using EReal.rec with
    | bot =>
      exfalso
      rw [← EReal.coe_sub] at h
      exact EReal.coe_ne_bot _ (le_bot_iff.mp h)
    | top => simp
    | coe y =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith

end ereal

variable {S}

lemma Q_eq (v : P) (ψ : X → ℝ) : Q S v ψ = S.h0 ψ ψ + dens S ψ v := rfl

lemma gsE_le {v : P} {ψ : X → ℝ} (hψ : ψ ∈ Nst S) : gsE S v ≤ ((Q S v ψ : ℝ) : EReal) :=
  biInf_le _ hψ

lemma gsE_of_isNGS {v : P} {ψ : X → ℝ} (h : IsNGS S v ψ) : gsE S v = ((Q S v ψ : ℝ) : EReal) :=
  le_antisymm (gsE_le h.1) (le_iInf₂ fun φ hφ => EReal.coe_le_coe_iff.mpr (h.2 φ hφ))

lemma le_liebF (v : P) (ρ : P → ℝ) : gsE S v - ((ρ v : ℝ) : EReal) ≤ liebF S ρ :=
  le_iSup (fun v => gsE S v - ((ρ v : ℝ) : EReal)) v

/-- **Lieb lies below the constrained search**: `F(ρ_ψ) ≤ h₀(ψ, ψ)` for normalised `ψ`. -/
theorem liebF_le_h0 {ψ : X → ℝ} (hψ : ψ ∈ Nst S) :
    liebF S (dens S ψ) ≤ ((S.h0 ψ ψ : ℝ) : EReal) := by
  refine iSup_le fun v => ?_
  rw [sub_coe_le]
  exact gsE_le hψ

/-- `E(v) ≤ F(ρ) + ρ(v)` for every density functional `ρ` (when `F(ρ)` is finite). -/
theorem gsE_le_liebF_add {v : P} {ρ : P → ℝ} {c : ℝ} (hc : liebF S ρ ≤ (c : EReal)) :
    gsE S v ≤ ((c + ρ v : ℝ) : EReal) :=
  sub_coe_le.mp ((le_liebF v ρ).trans hc)

/-- **The variational principle**: `E(v) = inf_ψ (F(ρ_ψ) + ρ_ψ(v))` over normalised states. -/
theorem gsE_eq_iInf (v : P) :
    gsE S v = ⨅ ψ ∈ Nst S, liebF S (dens S ψ) + ((dens S ψ v : ℝ) : EReal) := by
  apply le_antisymm
  · refine le_iInf₂ fun ψ hψ => ?_
    exact le_add_coe_of_sub_le (le_liebF v (dens S ψ))
  · refine le_iInf₂ fun ψ hψ => ?_
    refine (biInf_le _ hψ).trans ?_
    calc liebF S (dens S ψ) + ((dens S ψ v : ℝ) : EReal)
        ≤ ((S.h0 ψ ψ : ℝ) : EReal) + ((dens S ψ v : ℝ) : EReal) :=
          add_le_add (liebF_le_h0 hψ) le_rfl
      _ = ((Q S v ψ : ℝ) : EReal) := by rw [Q_eq, EReal.coe_add]

/-- **Convexity of the Lieb functional.** -/
theorem liebF_convex {ρ₁ ρ₂ : P → ℝ} {a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : liebF S ρ₁ ≤ (a : EReal)) (hb : liebF S ρ₂ ≤ (b : EReal)) :
    liebF S (fun v => t * ρ₁ v + (1 - t) * ρ₂ v) ≤ ((t * a + (1 - t) * b : ℝ) : EReal) := by
  refine iSup_le fun v => ?_
  have h1 := sub_coe_le.mp ((le_liebF v ρ₁).trans ha)
  have h2 := sub_coe_le.mp ((le_liebF v ρ₂).trans hb)
  rw [sub_coe_le]
  induction h : gsE S v using EReal.rec with
  | bot => exact bot_le
  | top => rw [h] at h1; exact absurd h1 (by simp)
  | coe e =>
    rw [h, EReal.coe_le_coe_iff] at h1 h2
    rw [EReal.coe_le_coe_iff]
    nlinarith

/-- **At a ground-state density, `F` is the constrained search.** -/
theorem liebF_of_isNGS {v : P} {ψ : X → ℝ} (h : IsNGS S v ψ) :
    liebF S (dens S ψ) = ((S.h0 ψ ψ : ℝ) : EReal) := by
  refine le_antisymm (liebF_le_h0 h.1) ?_
  refine le_trans ?_ (le_liebF v (dens S ψ))
  rw [gsE_of_isNGS h, Q_eq, ← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- **`-v` is a subgradient of `F` at the density of a ground state of `v`.** -/
theorem subgrad_of_isNGS {v : P} {ψ : X → ℝ} (h : IsNGS S v ψ) (ρ : P → ℝ) :
    ((S.h0 ψ ψ + dens S ψ v - ρ v : ℝ) : EReal) ≤ liebF S ρ := by
  refine le_trans ?_ (le_liebF v ρ)
  rw [gsE_of_isNGS h, Q_eq, ← EReal.coe_sub]

/-- **Converse**: if `ψ` attains the constrained search at its density, `F(ρ_ψ) = h₀(ψ, ψ)`, and
`-v` is a subgradient of `F` at `ρ_ψ` (tested on normalised states), then `ψ` is a ground state of
`v`. -/
theorem isNGS_of_subgrad {v : P} {ψ : X → ℝ} (hψ : ψ ∈ Nst S)
    (hsub : ∀ φ ∈ Nst S,
      ((S.h0 ψ ψ + dens S ψ v - dens S φ v : ℝ) : EReal) ≤ liebF S (dens S φ)) :
    IsNGS S v ψ := by
  refine ⟨hψ, fun φ hφ => ?_⟩
  have h := (hsub φ hφ).trans (liebF_le_h0 hφ)
  rw [EReal.coe_le_coe_iff] at h
  rw [Q_eq, Q_eq]
  linarith

lemma ip_smul_self (c : ℝ) (φ : X → ℝ) :
    ip (μ := μ) (c • φ) (c • φ) = c * c * ip (μ := μ) φ φ := by
  simp only [ip, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]; congr 1; funext x; ring

lemma Q_smul_self (v : P) (c : ℝ) {φ : X → ℝ} (hφ : φ ∈ S.D) :
    Q S v (c • φ) = c * c * Q S v φ := by
  have hcφ : c • φ ∈ S.D := S.D.smul_mem c hφ
  simp only [Q, pf, Pi.smul_apply, smul_eq_mul]
  rw [S.h0_smul c φ hφ _ hcφ, S.h0_symm φ hφ _ hcφ, S.h0_smul c φ hφ _ hφ]
  have : ∫ x, S.L v x * (c * φ x * (c * φ x)) ∂μ = c * c * ∫ x, S.L v x * (φ x * φ x) ∂μ := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [this]; ring

/-- Normalised minimisers are ground states, provided `h₀` is nonnegative on null states. -/
theorem isGS_of_isNGS (hnull : ∀ φ ∈ S.D, ip (μ := μ) φ φ = 0 → 0 ≤ S.h0 φ φ)
    {v : P} {ψ : X → ℝ} (h : IsNGS S v ψ) : IsGS S v ψ := by
  obtain ⟨⟨hD, hn⟩, hmin⟩ := h
  refine ⟨hD, by rw [hn]; norm_num, fun φ hφ => ?_⟩
  rw [hn, mul_one]
  rcases (show 0 ≤ ip (μ := μ) φ φ from integral_nonneg fun x => mul_self_nonneg (φ x)).lt_or_eq
    with hp | hp
  · -- normalise `φ`
    set c := (Real.sqrt (ip (μ := μ) φ φ))⁻¹
    have hs : 0 < Real.sqrt (ip (μ := μ) φ φ) := Real.sqrt_pos.mpr hp
    have hc2 : c * c * ip (μ := μ) φ φ = 1 := by
      simp only [c]; field_simp; rw [Real.sq_sqrt hp.le]
    have hcφ : c • φ ∈ S.D := S.D.smul_mem c hφ
    have hipc := ip_smul_self (μ := μ) c φ
    have hQc := Q_smul_self (S := S) v c hφ
    have h1 := hmin (c • φ) ⟨hcφ, by rw [hipc, hc2]⟩
    rw [hQc] at h1
    -- `Q ψ ≤ c² Q φ` with `c² ip φ = 1`
    have hcc : 0 < c * c := by positivity
    calc Q S v ψ * ip (μ := μ) φ φ ≤ c * c * Q S v φ * ip (μ := μ) φ φ :=
          mul_le_mul_of_nonneg_right h1 hp.le
      _ = Q S v φ * (c * c * ip (μ := μ) φ φ) := by ring
      _ = Q S v φ := by rw [hc2, mul_one]
  · -- a null state: its potential energy vanishes
    rw [← hp, mul_zero]
    have hint : Integrable (fun x => φ x * φ x) μ := S.int_sq φ φ hφ hφ
    have hae : (fun x => φ x * φ x) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (φ x)) hint).1 hp.symm
    have hpf : pf S v φ φ = 0 := by
      simp only [pf]
      rw [integral_eq_zero_of_ae]
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      rw [hx, mul_zero]
    simp only [Q, hpf, add_zero]
    exact hnull φ hφ hp.symm

/-- **Hohenberg–Kohn in Lieb's form.** Let `ψ` be a normalised ground state of `v` satisfying unique
continuation. If `-v'` is also a subgradient of `F` at `ρ_ψ` (tested on normalised states), then
`v - v'` is a multiple of `one`: the subdifferential of the Lieb functional at a v-representable
density is a single potential, up to constants. -/
theorem subgrad_unique (hsep : Sep S) {one : P} (hrig : RigidL S one)
    (hnull : ∀ φ ∈ S.D, ip (μ := μ) φ φ = 0 → 0 ≤ S.h0 φ φ) {v v' : P} {ψ : X → ℝ}
    (h : IsNGS S v ψ) (hucp : ∀ᵐ x ∂μ, ψ x ≠ 0)
    (hsub : ∀ φ ∈ Nst S,
      ((S.h0 ψ ψ + dens S ψ v' - dens S φ v' : ℝ) : EReal) ≤ liebF S (dens S φ)) :
    ∃ k : ℝ, v - v' = k • one :=
  strong_hk_of_ucp hsep hrig (isGS_of_isNGS hnull h)
    (isGS_of_isNGS hnull (isNGS_of_subgrad h.1 hsub)) hucp

end Continuum

end DFT
