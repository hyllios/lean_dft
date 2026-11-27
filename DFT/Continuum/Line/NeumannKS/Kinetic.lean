/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Neumann.Free
import DFT.Continuum.Line.NeumannKS.Diff

/-!
# The Kohn–Sham kinetic energy with Neumann walls (Corso's Lemma 6.2)

`T_KS(ρ)` is the infimum of the kinetic energy over Slater determinants of `N` orthonormal `H¹`
orbitals with density `ρ` (`tksNH`). On the `v`-representable densities:

* **`tksNH_eq_liebNH`**: `T_KS = F₀`, the Lieb functional without interaction;
* **`tksNH_attained`**: the infimum is attained by the Slater determinant of the `N` lowest
  orbitals of `-d²/dx² + v_s(ρ)`, and only by it (up to sign);
* **`hasDerivAt_tksNH`**: `T_KS` is Gateaux differentiable, `dT_KS(ρ) = -v_s(ρ)`.

For bosons the non-interacting functional is explicit (**`liebNH_bos_free`**): it is the von
Weizsäcker functional `∫ ((√ρ)')²`, attained by the product of `√(ρ/N)`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology
open scoped InnerProductSpace

variable {n : ℕ}

/-- `N` orbitals in `H1E`, orthonormal in `L²(0, 1)`. -/
def IsOrthoE (e : Fin (n + 1) → H1E) : Prop :=
  ∀ a b, ⟪JE (e a), JE (e b)⟫_ℝ = if a = b then 1 else 0

/-- **The Kohn–Sham kinetic energy** `T_KS(ρ) = inf {T(Φ) : Φ a Slater determinant, ρ_Φ = ρ}`. -/
noncomputable def tksNH (ρ : H1E) : EReal :=
  ⨅ (e : Fin (n + 1) → H1E) (_ : IsOrthoE e ∧ rhoE .fer (slN e) = ρ), (kinN (slN e) : EReal)

lemma intEN_zero (Φ : Cfg n → ℝ) : intEN 0 Φ = kinN Φ := by
  simp [intEN]

lemma liebNH_le_tksNH (ρ : H1E) : liebNH .fer (0 : Cfg n → ℝ) ρ ≤ tksNH (n := n) ρ :=
  le_iInf₂ fun e ⟨he, hρ⟩ => by
    refine (liebNH_le_levyNH (w := (0 : Cfg n → ℝ)) continuous_const ρ).trans ?_
    refine (iInf₂_le (slN e) ⟨slN_memN e, by simpa only [sq] using integral_slN_sq he, hρ⟩).trans ?_
    rw [intEN_zero]

section fer

variable {vs : PotH} {Ψs : Cfg n → ℝ} (hΨs : IsGSNH .fer 0 vs Ψs)
include hΨs

/-- **`T_KS` is attained by the lowest orbitals of `v_s`, and only by them.** -/
theorem tksNH_attained :
    ∃ (φ : ℕ → H1E) (lam : ℕ → ℝ), Monotone lam ∧
      (∀ k g, ⟪(φ k).snd, g.snd⟫_ℝ + vs (dE2 (φ k) g) = lam k * ⟪JE (φ k), JE g⟫_ℝ) ∧
      IsOrthoE (fun j : Fin (n + 1) => φ j) ∧
      rhoE .fer (slN fun j : Fin (n + 1) => φ j) = rhoE .fer Ψs ∧
      tksNH (n := n) (rhoE .fer Ψs) = (kinN (slN fun j : Fin (n + 1) => φ j) : EReal) ∧
      tksNH (n := n) (rhoE .fer Ψs) = liebNH .fer (0 : Cfg n → ℝ) (rhoE .fer Ψs) ∧
      ∀ e, IsOrthoE e → rhoE .fer (slN e) = rhoE .fer Ψs →
        tksNH (n := n) (rhoE .fer Ψs) = (kinN (slN e) : EReal) →
          slN e =ᵐ[μN n] (slN fun j : Fin (n + 1) => φ j) ∨
            slN e =ᵐ[μN n] (-1 : ℝ) • (slN fun j : Fin (n + 1) => φ j) := by
  have hw : Continuous (0 : Cfg n → ℝ) := continuous_const
  obtain ⟨φ, lam, hm, -, hon, heig, -, hGS, -⟩ := gs_free_fer (n := n) vs
  set e0 : Fin (n + 1) → H1E := fun j => φ j
  have he0 : IsOrthoE e0 := fun a c => by simp only [e0, hon, Fin.val_inj]
  have hρ0 : rhoE .fer (slN e0) = rhoE .fer Ψs := rhoE_gsNH_unique hw hΨs hGS
  have hlieb : liebNH .fer (0 : Cfg n → ℝ) (rhoE .fer Ψs) = (kinN (slN e0) : EReal) := by
    rw [← hρ0, liebNH_eq_of_isGSNH hw hGS, intEN_zero]
  have hT : tksNH (n := n) (rhoE .fer Ψs) = (kinN (slN e0) : EReal) :=
    le_antisymm (iInf₂_le e0 ⟨he0, hρ0⟩) (hlieb ▸ liebNH_le_tksNH _)
  refine ⟨φ, lam, hm, heig, he0, hρ0, hT, hT.trans hlieb.symm, fun e he hρ hTe => ?_⟩
  have hk : kinN (slN e) = kinN (slN e0) := EReal.coe_injective (hTe.symm.trans hT)
  have hn : ∫ x, slN e x ^ 2 ∂μN n = 1 := by simpa only [sq] using integral_slN_sq he
  rw [← hρ0] at hρ
  have := (levyNH_attained_iff hw hGS (slN_memN e) hn hρ).1 (by rw [intEN_zero, intEN_zero, hk])
  exact this

/-- **`T_KS = F₀` on `v`-representable densities.** -/
theorem tksNH_eq_liebNH :
    tksNH (n := n) (rhoE .fer Ψs) = liebNH .fer (0 : Cfg n → ℝ) (rhoE .fer Ψs) := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := tksNH_attained hΨs
  exact h

/-- **Differentiability of `T_KS`** (Corso's Lemma 6.2): `dT_KS(ρ) = -v_s(ρ)` along every `δ` of
mass zero. -/
theorem hasDerivAt_tksNH {δ : H1E} (hδ : ellE δ = 0) :
    HasDerivAt (fun ε : ℝ => (tksNH (n := n) (rhoE .fer Ψs + ε • δ)).toReal) (-vs δ) 0 := by
  have hw : Continuous (0 : Cfg n → ℝ) := continuous_const
  refine (hasDerivAt_liebNH hw hΨs hδ).2.congr_of_eventuallyEq ?_
  filter_upwards [eventually_vrepNH hw hΨs hδ] with ε hε
  obtain ⟨v', Ψ', hΨ', hρ'⟩ := hε
  rw [← hρ', tksNH_eq_liebNH hΨ']

end fer

/-! ### Bosons: the von Weizsäcker functional -/

/-- A continuous function without zeros on `[0, 1]` has a constant sign there. -/
lemma const_sign_of_ne_zero {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (h0 : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) :
    (∀ t ∈ Icc (0 : ℝ) 1, 0 < f t) ∨ (∀ t ∈ Icc (0 : ℝ) 1, f t < 0) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rcases (h0 0 h01).lt_or_gt with hneg | hpos
  · refine Or.inr fun t ht => ?_
    by_contra hc; push Not at hc
    obtain ⟨c, hc, hfc⟩ := isPreconnected_Icc.intermediate_value h01 ht hf ⟨hneg.le, hc⟩
    exact h0 c hc hfc
  · refine Or.inl fun t ht => ?_
    by_contra hc; push Not at hc
    obtain ⟨c, hc, hfc⟩ := isPreconnected_Icc.intermediate_value ht h01 hf ⟨hc, hpos.le⟩
    exact h0 c hc hfc

/-- **For bosons, the non-interacting functional is von Weizsäcker's**: at a `v`-representable
density, `F₀(ρ) = ∫ ((√ρ)')²`, attained by the product state of an orbital with square `ρ/N`. -/
theorem liebNH_bos_free {vs : PotH} {Ψs : Cfg n → ℝ} (hΨs : IsGSNH .bos 0 vs Ψs) :
    ∃ φ₀ : H1E, IsGSNH .bos 0 vs (prN (n := n) φ₀) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, orbF φ₀ t ^ 2 = fnE (rhoE .bos Ψs) t / ((n : ℝ) + 1)) ∧
      liebNH .bos (0 : Cfg n → ℝ) (rhoE .bos Ψs) =
        ((∫ t, deriv (fun s => √(fnE (rhoE .bos Ψs) s)) t ^ 2 ∂vol01 : ℝ) : EReal) := by
  have hw : Continuous (0 : Cfg n → ℝ) := continuous_const
  obtain ⟨φ₀, -, h1, -, -, hGS⟩ := gs_free_bos (n := n) vs
  have hNp : (0 : ℝ) < n + 1 := by positivity
  set ρ := rhoE .bos Ψs
  have hρ : rhoE .bos (prN (n := n) φ₀) = ρ := rhoE_gsNH_unique hw hΨs hGS
  have hfρ : ∀ t ∈ Icc (0 : ℝ) 1, fnE ρ t = ((n : ℝ) + 1) * orbF φ₀ t ^ 2 := fun t ht => by
    rw [← hρ, rhoE_prN h1, fnE_smul' _ _ ht, fnE_dE _ ht, orbF_eq _ ht, sq]
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, orbF φ₀ t ^ 2 = fnE ρ t / ((n : ℝ) + 1) := fun t ht => by
    rw [hfρ t ht]; field_simp
  refine ⟨φ₀, hGS, hsq, ?_⟩
  -- the orbital has a constant sign, since `ρ > 0`
  obtain ⟨hpos, -⟩ := vrepNH_nec hw ⟨vs, Ψs, hΨs, rfl⟩
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, orbF φ₀ t ≠ 0 := fun t ht h0 => by
    have := hpos t ht; rw [hfρ t ht, h0] at this; simp at this
  obtain ⟨s, hs, hsg⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1, 0 < s * orbF φ₀ t := by
    rcases const_sign_of_ne_zero (continuous_orbF φ₀).continuousOn hne with h | h
    · exact ⟨1, by norm_num, fun t ht => by simpa using h t ht⟩
    · exact ⟨-1, by norm_num, fun t ht => by have := h t ht; linarith⟩
  -- `√ρ = √N · s · φ₀` on `[0, 1]`
  have hroot : EqOn (fun t => √(fnE ρ t)) (fun t => (√((n : ℝ) + 1) * s) * orbF φ₀ t)
      (Icc 0 1) := fun t ht => by
    simp only
    rw [hfρ t ht, Real.sqrt_mul hNp.le, mul_assoc]
    congr 1
    have h2 : orbF φ₀ t ^ 2 = (s * orbF φ₀ t) ^ 2 := by rw [mul_pow, hs, one_mul]
    rw [h2, Real.sqrt_sq (hsg t ht).le]
  have hl : liebNH .bos (0 : Cfg n → ℝ) ρ = (kinN (prN (n := n) φ₀) : EReal) := by
    rw [← hρ, liebNH_eq_of_isGSNH hw hGS, intEN_zero]
  rw [hl, kinN_prN h1, ← kinM_orbF]
  congr 1
  rw [kinM, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [H1N.deriv_eq_of_eqOn hroot ht, deriv_const_mul_field', mul_pow, mul_pow,
    Real.sq_sqrt hNp.le, hs, mul_one]
