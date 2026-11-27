/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeumannKS.Exact
import DFT.Continuum.Line.NeumannKS.Kinetic

/-!
# The exact Kohn–Sham scheme and the Aufbau principle with Neumann walls (Corso's Theorem 2.15)

For `N` fermions with a continuous interaction `w` in `v ∈ H⁻¹`, let
`E_Hxc(ρ) = F_LL,w(ρ) - T_KS(ρ)` (`hxcLL`) and, for a Slater determinant `Φ` of orthonormal
`H¹` orbitals, `E_KS(Φ) = T(Φ) + E_Hxc(ρ_Φ) + v(ρ_Φ)` (`ksEnergy`).

**`ks_aufbau`**: `E_KS(Φ) ≥ E_w(v)` for every Slater determinant; equality holds for the Slater
determinant of the `N` lowest orbitals of `-d²/dx² + v_KS`, where `v_KS = v + v_Hxc(ρ₀)`
(`ks_exact`), whose density is the interacting ground-state density `ρ₀`; and only for it, up to
sign.

The proof: `T(Φ) ≥ T_KS(ρ_Φ)`, so `E_KS(Φ) ≥ F_LL,w(ρ_Φ) + v(ρ_Φ) = Q(Ψ_m) ≥ E_w(v)` with `Ψ_m`
a minimiser of the constrained search (`exists_levy_min`). In the equality case `Ψ_m` is a
ground state, so `ρ_Φ = ρ₀` (nondegeneracy), and `T(Φ) = T_KS(ρ₀)`, so `Φ` is the determinant
of the lowest orbitals of `v_KS` (`tksNH_attained`).
-/

namespace DFT.Continuum.Line

open MeasureTheory Set SturmLiouville Real Filter Topology
open scoped InnerProductSpace

variable {n : ℕ} {w : Cfg n → ℝ}

/-- `E_Hxc = F_LL,w - T_KS`. -/
noncomputable def hxcLL (w : Cfg n → ℝ) (ρ : H1E) : ℝ :=
  (levyNH .fer w ρ).toReal - (tksNH (n := n) ρ).toReal

/-- **The Kohn–Sham energy** of the Slater determinant of orthonormal orbitals `e`. -/
noncomputable def ksEnergy (w : Cfg n → ℝ) (v : PotH) (e : Fin (n + 1) → H1E) : ℝ :=
  kinN (slN e) + hxcLL w (rhoE .fer (slN e)) + v (rhoE .fer (slN e))

/-- On a Slater density, `T_KS ≤ T(Φ)` as real numbers. -/
lemma tksNH_toReal_le {e : Fin (n + 1) → H1E} (he : IsOrthoE e) :
    (tksNH (n := n) (rhoE .fer (slN e))).toReal ≤ kinN (slN e) := by
  have hle : tksNH (n := n) (rhoE .fer (slN e)) ≤ (kinN (slN e) : EReal) := iInf₂_le e ⟨he, rfl⟩
  have hlow : ((gsEH .fer (0 : Cfg n → ℝ) 0 - (0 : PotH) (rhoE .fer (slN e)) : ℝ) : EReal) ≤
      tksNH (n := n) (rhoE .fer (slN e)) :=
    (le_iSup (fun v' : PotH => ((gsEH .fer (0 : Cfg n → ℝ) v' - v' (rhoE .fer (slN e)) : ℝ) :
      EReal)) 0).trans (liebNH_le_tksNH _)
  have hbot : tksNH (n := n) (rhoE .fer (slN e)) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  have htop : tksNH (n := n) (rhoE .fer (slN e)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal htop hbot]
  exact hle

/-- The constrained search at a Slater density, through a minimiser. -/
lemma levy_slater (hw : Continuous w) {e : Fin (n + 1) → H1E} (he : IsOrthoE e) :
    ∃ Ψm ∈ DomN .fer n, ∫ x, Ψm x ^ 2 ∂μN n = 1 ∧ rhoE .fer Ψm = rhoE .fer (slN e) ∧
      (levyNH .fer w (rhoE .fer (slN e))).toReal = intEN w Ψm := by
  obtain ⟨Ψm, hΨm, hn, hρ, hmin⟩ := exists_levy_min hw (slN_memN e)
    (by simpa only [sq] using integral_slN_sq he) rfl
  exact ⟨Ψm, hΨm, hn, hρ, by rw [levyNH_eq_of_min hΨm hn hρ hmin, EReal.toReal_coe]⟩

/-- **The exact Kohn–Sham scheme and the Aufbau principle** (Neumann walls, `H⁻¹` potentials,
continuous interaction, fermions; Corso's Theorem 2.15). -/
theorem ks_aufbau (hw : Continuous w) {v : PotH} {Ψ : Cfg n → ℝ} (hΨ : IsGSNH .fer w v Ψ) :
    ∃ (vKS : PotH) (φ : ℕ → H1E) (lam : ℕ → ℝ),
      (∀ δ : H1E, ellE δ = 0 →
        HasDerivAt (fun ε : ℝ => hxcNH .fer w (rhoE .fer Ψ + ε • δ)) (vKS δ - v δ) 0) ∧
      Monotone lam ∧
      (∀ k g, ⟪(φ k).snd, g.snd⟫_ℝ + vKS (dE2 (φ k) g) = lam k * ⟪JE (φ k), JE g⟫_ℝ) ∧
      IsOrthoE (fun j : Fin (n + 1) => φ j) ∧
      rhoE .fer (slN fun j : Fin (n + 1) => φ j) = rhoE .fer Ψ ∧
      ksEnergy w v (fun j : Fin (n + 1) => φ j) = gsEH .fer w v ∧
      (∀ e, IsOrthoE e → gsEH .fer w v ≤ ksEnergy w v e) ∧
      ∀ e, IsOrthoE e → ksEnergy w v e = gsEH .fer w v →
        slN e =ᵐ[μN n] (slN fun j : Fin (n + 1) => φ j) ∨
          slN e =ᵐ[μN n] (-1 : ℝ) • (slN fun j : Fin (n + 1) => φ j) := by
  obtain ⟨vKS, Ψs, hΨs, hρs, hder, -⟩ := ks_exact hw hΨ
  obtain ⟨φ, lam, hm, heig, he0, hρ0, hT0, -, huniq⟩ := tksNH_attained hΨs
  rw [hρs] at hρ0 hT0
  -- the energy bound for every determinant
  have hbound : ∀ e, IsOrthoE e → ∃ Ψm ∈ DomN .fer n, ∫ x, Ψm x ^ 2 ∂μN n = 1 ∧
      rhoE .fer Ψm = rhoE .fer (slN e) ∧ QNH .fer w v Ψm ≤ ksEnergy w v e := fun e he => by
    obtain ⟨Ψm, hΨm, hn, hρ, hlev⟩ := levy_slater hw he
    refine ⟨Ψm, hΨm, hn, hρ, ?_⟩
    have := tksNH_toReal_le he
    simp only [ksEnergy, hxcLL, hlev, QNH_eq_intEN, hρ]
    linarith
  have hlow : ∀ e, IsOrthoE e → gsEH .fer w v ≤ ksEnergy w v e := fun e he => by
    obtain ⟨Ψm, hΨm, hn, -, hle⟩ := hbound e he
    exact (gsEH_le hw hΨm hn).trans hle
  refine ⟨vKS, φ, lam, hder, hm, heig, he0, hρ0, ?_, hlow, fun e he heq => ?_⟩
  · -- the lowest orbitals of `v_KS` reach `E_w(v)`
    have hlev : (levyNH .fer w (rhoE .fer (slN fun j : Fin (n + 1) => φ j))).toReal = intEN w Ψ := by
      rw [hρ0, levyNH_eq_of_isGSNH hw hΨ, EReal.toReal_coe]
    have htks : (tksNH (n := n) (rhoE .fer (slN fun j : Fin (n + 1) => φ j))).toReal = kinN (slN fun j : Fin (n + 1) => φ j) := by
      rw [hρ0, hT0, EReal.toReal_coe]
    rw [ksEnergy, hxcLL, hlev, htks, hρ0]
    rw [gsEH_of_isGSNH hw hΨ, QNH_eq_intEN]
    ring
  · -- equality forces the lowest orbitals
    obtain ⟨Ψm, hΨm, hn, hρm, hle⟩ := hbound e he
    have hGSm : IsGSNH .fer w v Ψm := isGSNH_of_le hw hΨm hn (hle.trans heq.le)
    have hρe : rhoE .fer (slN e) = rhoE .fer Ψ := hρm.symm.trans (rhoE_gsNH_unique hw hΨ hGSm)
    -- `T(Φ) = T_KS(ρ₀)`
    obtain ⟨Ψm', hΨm', hn', hρm', hlev⟩ := levy_slater (w := w) hw he
    have hq := gsEH_le (v := v) hw hΨm' hn'
    have htks := tksNH_toReal_le he
    have hk : kinN (slN e) = (tksNH (n := n) (rhoE .fer (slN e))).toReal := by
      have h1 : ksEnergy w v e = kinN (slN e) + (intEN w Ψm' -
          (tksNH (n := n) (rhoE .fer (slN e))).toReal) + v (rhoE .fer (slN e)) := by
        simp only [ksEnergy, hxcLL, hlev]
      rw [QNH_eq_intEN, hρm'] at hq
      linarith
    have hT : tksNH (n := n) (rhoE .fer Ψ) = (kinN (slN e) : EReal) := by
      rw [← hρe, hk, EReal.coe_toReal]
      · rw [hρe, hT0]; exact EReal.coe_ne_top _
      · rw [hρe, hT0]; exact EReal.coe_ne_bot _
    exact huniq e he (hρe.trans hρs.symm) (by rw [hρs]; exact hT)

end DFT.Continuum.Line
