/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Lattice.Basic.GroundState
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Hohenberg–Kohn on a general configuration space (conditional form)

The lattice proofs, rewritten for a configuration space `(X, μ)` that may be continuous. States are
real functions `ψ : X → ℝ` in a form domain `D`; the potential-free Hamiltonian (kinetic energy plus
interaction) is a symmetric bilinear form `h₀` on `D`; a one-body potential `w` from a vector space
`P` acts by multiplication with `L w`. For `N` particles in `ℝ³`, `X = ℝ^{3N}` and
`L w (x₁, …, x_N) = Σᵢ w(xᵢ)`; on the lattice, `X` is the finite set of configurations and
`L w (c) = Σᵢ wᵢ nᵢ(c)`. The density is the functional `w ↦ ∫ (L w) ψ²`.

The analysis enters through three named hypotheses:

* `Sep`: the form domain separates functions (the fundamental lemma of the calculus of variations);
* `RigidL`: a one-body potential whose coupling is constant almost everywhere is a constant;
* unique continuation for the ground state: `ψ ≠ 0` almost everywhere.

Main results:

* `euler_lagrange`: a ground state satisfies the weak Schrödinger equation.
* `weak_hk`: two ground states with the same density are ground states of both potentials.
* `strong_hk_of_ucp`: two potentials sharing a ground state with `ψ ≠ 0` a.e. differ by a constant.
* `hk_of_ucp`: **Hohenberg–Kohn.** If the ground states of `v` and `v'` have the same density
  and one of them satisfies unique continuation, then `v - v'` is constant.
-/

namespace DFT

namespace Continuum

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- A quantum system on the configuration space `(X, μ)` with one-body potentials in `P`. -/
structure Setting (μ : Measure X) (P : Type*) [AddCommGroup P] [Module ℝ P] where
  /-- The form domain. -/
  D : Submodule ℝ (X → ℝ)
  /-- The potential-free energy form (kinetic energy plus interaction), bilinear on `D`. -/
  h0 : (X → ℝ) → (X → ℝ) → ℝ
  h0_add : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, h0 (a + b) c = h0 a c + h0 b c
  h0_smul : ∀ r : ℝ, ∀ a ∈ D, ∀ c ∈ D, h0 (r • a) c = r * h0 a c
  h0_symm : ∀ ψ ∈ D, ∀ φ ∈ D, h0 ψ φ = h0 φ ψ
  /-- The coupling of one-body potentials to configurations. -/
  L : P →ₗ[ℝ] (X → ℝ)
  int_L : ∀ w ψ φ, ψ ∈ D → φ ∈ D → Integrable (fun x => L w x * (ψ x * φ x)) μ
  int_sq : ∀ ψ φ, ψ ∈ D → φ ∈ D → Integrable (fun x => ψ x * φ x) μ

variable (S : Setting μ P)

/-- The `L²` inner product. -/
noncomputable def ip (ψ φ : X → ℝ) : ℝ := ∫ x, ψ x * φ x ∂μ

/-- The potential energy form of `w`. -/
noncomputable def pf (w : P) (ψ φ : X → ℝ) : ℝ := ∫ x, S.L w x * (ψ x * φ x) ∂μ

/-- The energy `⟨ψ, H(w) ψ⟩`. -/
noncomputable def Q (w : P) (ψ : X → ℝ) : ℝ := S.h0 ψ ψ + pf S w ψ ψ

/-- The density of `ψ`, as a functional on one-body potentials. -/
noncomputable def dens (ψ : X → ℝ) (w : P) : ℝ := pf S w ψ ψ

/-- `ψ` is a ground state of `H(w)`: a nonzero minimiser of the Rayleigh quotient on `D`. -/
def IsGS (w : P) (ψ : X → ℝ) : Prop :=
  ψ ∈ S.D ∧ 0 < ip (μ := μ) ψ ψ ∧
    ∀ φ ∈ S.D, Q S w ψ * ip (μ := μ) φ φ ≤ Q S w φ * ip (μ := μ) ψ ψ

/-- The form domain separates the functions `(L w - c) ψ` (fundamental lemma of the calculus of
variations). -/
def Sep : Prop :=
  ∀ (w : P) (c : ℝ) (ψ : X → ℝ), ψ ∈ S.D →
    (∀ φ ∈ S.D, ∫ x, (S.L w x - c) * ψ x * φ x ∂μ = 0) →
      (fun x => (S.L w x - c) * ψ x) =ᵐ[μ] 0

/-- Rigidity: a one-body potential whose coupling is a.e. constant is a multiple of `one`. -/
def RigidL (one : P) : Prop :=
  ∀ (w : P) (c : ℝ), (S.L w =ᵐ[μ] fun _ => c) → ∃ k : ℝ, w = k • one

section expand

variable {g : X → ℝ} {ψ φ : X → ℝ}

/-- Expansion of a weighted quadratic form along `ψ + s φ`. -/
lemma integral_expand (hψψ : Integrable (fun x => g x * (ψ x * ψ x)) μ)
    (hψφ : Integrable (fun x => g x * (ψ x * φ x)) μ)
    (hφφ : Integrable (fun x => g x * (φ x * φ x)) μ) (s : ℝ) :
    ∫ x, g x * ((ψ + s • φ) x * (ψ + s • φ) x) ∂μ =
      ∫ x, g x * (ψ x * ψ x) ∂μ + 2 * s * ∫ x, g x * (ψ x * φ x) ∂μ +
        s ^ 2 * ∫ x, g x * (φ x * φ x) ∂μ := by
  have hpt : (fun x => g x * ((ψ + s • φ) x * (ψ + s • φ) x)) =
      fun x => (g x * (ψ x * ψ x) + (2 * s) * (g x * (ψ x * φ x))) +
        s ^ 2 * (g x * (φ x * φ x)) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hpt, integral_add (f := fun x => g x * (ψ x * ψ x) + 2 * s * (g x * (ψ x * φ x)))
    (hψψ.add (hψφ.const_mul _)) (hφφ.const_mul _),
    integral_add (f := fun x => g x * (ψ x * ψ x)) hψψ (hψφ.const_mul _), integral_const_mul,
    integral_const_mul]

end expand

variable {S}

lemma ip_comm (ψ φ : X → ℝ) : ip (μ := μ) ψ φ = ip (μ := μ) φ ψ := by
  simp only [ip, mul_comm]

lemma pf_comm (w : P) (ψ φ : X → ℝ) : pf S w ψ φ = pf S w φ ψ := by
  simp only [pf, mul_comm (ψ _)]

lemma ip_expand {ψ φ : X → ℝ} (hψ : ψ ∈ S.D) (hφ : φ ∈ S.D) (s : ℝ) :
    ip (μ := μ) (ψ + s • φ) (ψ + s • φ) =
      ip (μ := μ) ψ ψ + 2 * s * ip (μ := μ) ψ φ + s ^ 2 * ip (μ := μ) φ φ := by
  have h := integral_expand (μ := μ) (g := fun _ => 1) (ψ := ψ) (φ := φ)
    (by simpa using S.int_sq ψ ψ hψ hψ) (by simpa using S.int_sq ψ φ hψ hφ)
    (by simpa using S.int_sq φ φ hφ hφ) s
  simpa [ip] using h

lemma pf_expand (w : P) {ψ φ : X → ℝ} (hψ : ψ ∈ S.D) (hφ : φ ∈ S.D) (s : ℝ) :
    pf S w (ψ + s • φ) (ψ + s • φ) =
      pf S w ψ ψ + 2 * s * pf S w ψ φ + s ^ 2 * pf S w φ φ :=
  integral_expand (S.int_L w ψ ψ hψ hψ) (S.int_L w ψ φ hψ hφ) (S.int_L w φ φ hφ hφ) s

lemma h0_expand {ψ φ : X → ℝ} (hψ : ψ ∈ S.D) (hφ : φ ∈ S.D) (s : ℝ) :
    S.h0 (ψ + s • φ) (ψ + s • φ) = S.h0 ψ ψ + 2 * s * S.h0 ψ φ + s ^ 2 * S.h0 φ φ := by
  have hsφ : s • φ ∈ S.D := S.D.smul_mem s hφ
  have hψs : ψ + s • φ ∈ S.D := S.D.add_mem hψ hsφ
  rw [S.h0_add ψ hψ (s • φ) hsφ _ hψs, S.h0_smul s φ hφ _ hψs, S.h0_symm ψ hψ _ hψs,
    S.h0_symm φ hφ _ hψs, S.h0_add ψ hψ (s • φ) hsφ _ hψ, S.h0_smul s φ hφ _ hψ,
    S.h0_add ψ hψ (s • φ) hsφ _ hφ, S.h0_smul s φ hφ _ hφ, S.h0_symm φ hφ ψ hψ]
  ring

/-- **Euler–Lagrange equation.** A ground state of `H(w)` with energy `E = ⟨ψ,Hψ⟩/⟨ψ,ψ⟩` satisfies
the weak Schrödinger equation `h₀(ψ, φ) + ⟨w ψ, φ⟩ = E ⟨ψ, φ⟩` for every `φ` in the form domain. -/
theorem euler_lagrange {w : P} {ψ : X → ℝ} (hψ : IsGS S w ψ) {φ : X → ℝ} (hφ : φ ∈ S.D) :
    S.h0 ψ φ + pf S w ψ φ = Q S w ψ / ip (μ := μ) ψ ψ * ip (μ := μ) ψ φ := by
  obtain ⟨hD, hpos, hmin⟩ := hψ
  set p := ip (μ := μ) ψ ψ
  set q := Q S w ψ
  have key : ∀ s : ℝ, 0 ≤ (2 * (p * (S.h0 ψ φ + pf S w ψ φ) - q * ip (μ := μ) ψ φ)) * s +
      (p * Q S w φ - q * ip (μ := μ) φ φ) * s ^ 2 := by
    intro s
    have h := hmin (ψ + s • φ) (S.D.add_mem hD (S.D.smul_mem s hφ))
    rw [ip_expand hD hφ, Q, h0_expand hD hφ, pf_expand w hD hφ] at h
    have hq : q = S.h0 ψ ψ + pf S w ψ ψ := rfl
    have hp : ip (μ := μ) ψ ψ = p := rfl
    rw [hp] at h
    simp only [Q, hq] at h ⊢
    nlinarith [h]
  have h0 := lin_coeff_zero key
  field_simp
  linarith

/-- **Weak Hohenberg–Kohn.** If `ψ` and `ψ'` are ground states of `v` and `v'` with the same norm
and the same density, then `ψ` is also a ground state of `v'`. -/
theorem weak_hk {v v' : P} {ψ ψ' : X → ℝ} (hψ : IsGS S v ψ) (hψ' : IsGS S v' ψ')
    (hn : ip (μ := μ) ψ ψ = ip (μ := μ) ψ' ψ') (hd : dens S ψ = dens S ψ') : IsGS S v' ψ := by
  obtain ⟨hD, hpos, hmin⟩ := hψ
  obtain ⟨hD', hpos', hmin'⟩ := hψ'
  have hdv : pf S v ψ ψ = pf S v ψ' ψ' := congrFun hd v
  have hdv' : pf S v' ψ ψ = pf S v' ψ' ψ' := congrFun hd v'
  have h1 := hmin ψ' hD'
  have h2 := hmin' ψ hD
  rw [← hn] at h1 h2
  have h1' : Q S v ψ ≤ Q S v ψ' := le_of_mul_le_mul_right h1 hpos
  have h2' : Q S v' ψ' ≤ Q S v' ψ := le_of_mul_le_mul_right h2 hpos
  have heq : Q S v' ψ = Q S v' ψ' := by
    simp only [Q] at h1' h2' ⊢
    linarith
  refine ⟨hD, hpos, fun φ hφ => ?_⟩
  rw [heq, hn]
  exact hmin' φ hφ

/-- **Strong Hohenberg–Kohn, conditional on unique continuation.** If `v` and `v'` share a ground
state `ψ` that vanishes only on a null set, then `v - v'` is a multiple of `one`. -/
theorem strong_hk_of_ucp (hsep : Sep S) {one : P} (hrig : RigidL S one) {v v' : P}
    {ψ : X → ℝ} (hψ : IsGS S v ψ) (hψ' : IsGS S v' ψ) (hucp : ∀ᵐ x ∂μ, ψ x ≠ 0) :
    ∃ k : ℝ, v - v' = k • one := by
  have hD := hψ.1
  set c := Q S v ψ / ip (μ := μ) ψ ψ - Q S v' ψ / ip (μ := μ) ψ ψ
  set g : X → ℝ := fun x => (S.L (v - v') x - c) * ψ x
  have hzero : ∀ φ ∈ S.D, ∫ x, (S.L (v - v') x - c) * ψ x * φ x ∂μ = 0 := by
    intro φ hφ
    have e1 := euler_lagrange hψ hφ
    have e2 := euler_lagrange hψ' hφ
    have hsplit : ∫ x, (S.L (v - v') x - c) * ψ x * φ x ∂μ =
        (pf S v ψ φ - pf S v' ψ φ) - c * ip (μ := μ) ψ φ := by
      have hpt : (fun x => (S.L (v - v') x - c) * ψ x * φ x) = fun x =>
          (S.L v x * (ψ x * φ x) - S.L v' x * (ψ x * φ x)) - c * (ψ x * φ x) := by
        funext x; simp only [map_sub, Pi.sub_apply]; ring
      rw [hpt, integral_sub (f := fun x => S.L v x * (ψ x * φ x) - S.L v' x * (ψ x * φ x))
        ((S.int_L v ψ φ hD hφ).sub (S.int_L v' ψ φ hD hφ))
        ((S.int_sq ψ φ hD hφ).const_mul c), integral_sub (f := fun x => S.L v x * (ψ x * φ x))
        (S.int_L v ψ φ hD hφ) (S.int_L v' ψ φ hD hφ), integral_const_mul]
      rfl
    rw [hsplit]
    simp only [c]
    linarith
  have hg : g =ᵐ[μ] 0 := hsep (v - v') c ψ hD hzero
  have hL : S.L (v - v') =ᵐ[μ] fun _ => c := by
    filter_upwards [hg, hucp] with x hx hx0
    simp only [g, Pi.zero_apply, mul_eq_zero] at hx
    rcases hx with h | h
    · linarith
    · exact absurd h hx0
  exact hrig _ c hL

/-- **Hohenberg–Kohn, conditional on unique continuation.** If the ground states `ψ` of `v` and
`ψ'` of `v'` have the same norm and the same density, and `ψ` vanishes only on a null set, then
`v - v'` is a multiple of `one`. -/
theorem hk_of_ucp (hsep : Sep S) {one : P} (hrig : RigidL S one) {v v' : P}
    {ψ ψ' : X → ℝ} (hψ : IsGS S v ψ) (hψ' : IsGS S v' ψ')
    (hn : ip (μ := μ) ψ ψ = ip (μ := μ) ψ' ψ') (hd : dens S ψ = dens S ψ')
    (hucp : ∀ᵐ x ∂μ, ψ x ≠ 0) : ∃ k : ℝ, v - v' = k • one :=
  strong_hk_of_ucp hsep hrig hψ (weak_hk hψ hψ' hn hd) hucp

end Continuum

end DFT
