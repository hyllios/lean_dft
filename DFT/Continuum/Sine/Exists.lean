/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Free.FreeFermions
import DFT.Continuum.Sine.Min

/-!
# Energies and norms in sine coefficients

* `hasSum_ip`, `ip_eq_tsum`, `Q_eq_Fn`: for `φ ∈ Dom`, the norm and the energy are `Σ cN²` and the
  coefficient-space energy `Fn V` of the sine coefficients.
* `exists_dom_pos`, `exists_adm`: a normalised admissible coefficient sequence exists for both
  statistics (from the free-particle ground states).
-/

namespace DFT.Continuum.Sine

open MeasureTheory Set Filter Topology Box SturmLiouville Line Real
open scoped ENNReal

variable {n : ℕ}

/-- Parseval: `⟨φ, φ⟩ = Σ_m cN_m(φ)²`. -/
lemma hasSum_ip {φ : Cfg n → ℝ} (hφ : Continuous φ) :
    HasSum (fun m => cN m φ ^ 2) (ip (μ := μN n) φ φ) := by
  rw [ip, muN_eq]; exact hasSum_sq_cube hφ

lemma ip_eq_tsum {φ : Cfg n → ℝ} (hφ : Continuous φ) :
    ip (μ := μN n) φ φ = ∑' m, cN m φ ^ 2 := (hasSum_ip hφ).tsum_eq.symm

/-- The sine coefficients of a state in the domain are admissible. -/
lemma Dir_cN {τ : Stat} {φ : Cfg n → ℝ} (hφ : φ ∈ Dom τ n) : Dir τ.toSym fun m => cN m φ :=
  ⟨(hasSum_ip hφ.1.continuous).summable, by simpa [lam] using (hasSum_kin hφ).summable,
    cN_InS hφ⟩

/-- **The energy in the sine basis**: `⟨φ, H φ⟩ = Σ λ_m c_m² + Σ c_m (K c)_m`. -/
lemma Q_eq_Fn {τ : Stat} {w : Cfg n → ℝ} (hw : Continuous w) (v : C01) {φ : Cfg n → ℝ}
    (hφ : φ ∈ Dom τ n) :
    Q (setting τ n w hw) v φ = Fn (fun x => LN n v x + w x) fun m => cN m φ := by
  have hc := hφ.1.continuous
  have hVc : Continuous fun x => LN n v x + w x := (continuous_LN v).add hw
  rw [Fn, Bf_cN hVc hc]
  have hk : ∑' m, lam m * cN m φ ^ 2 = ∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n := by
    simpa [lam] using (hasSum_kin hφ).tsum_eq
  rw [hk]
  have hsplit : ∫ x, (LN n v x + w x) * (φ x * φ x) ∂μN n =
      ∫ x, LN n v x * (φ x * φ x) ∂μN n + ∫ x, w x * (φ x * φ x) ∂μN n := by
    rw [← integral_add (f := fun x => LN n v x * (φ x * φ x)) (g := fun x => w x * (φ x * φ x))
      (integrableN ((continuous_LN v).mul (hc.mul hc)))
      (integrableN (hw.mul (hc.mul hc)))]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hsplit]
  change ∫ x, ∑ k, dk k φ x * dk k φ x ∂μN n + ∫ x, w x * (φ x * φ x) ∂μN n +
    ∫ x, LN n v x * (φ x * φ x) ∂μN n = _
  ring

/-- A nonzero state of either statistics. -/
lemma exists_dom_pos (τ : Stat) : ∃ Ψ ∈ Dom τ n, 0 < ip (μ := μN n) Ψ Ψ := by
  cases τ
  · obtain ⟨Ψ, hΨ, -⟩ := prodS_isGS (n := n) 0
    exact ⟨Ψ, hΨ.1, hΨ.2.1⟩
  · obtain ⟨Ψ, -, hΨ, -⟩ := slater_isGS (n := n) 0
    exact ⟨Ψ, hΨ.1, hΨ.2.1⟩

/-- Normalised admissible sequences exist. -/
lemma exists_adm (τ : Stat) : ∃ c : (Fin (n + 1) → ℕ) → ℝ, Adm τ.toSym c := by
  obtain ⟨Ψ, hΨ, hpos⟩ := exists_dom_pos (n := n) τ
  set a := (√(ip (μ := μN n) Ψ Ψ))⁻¹
  refine ⟨fun m => a * cN m Ψ, Dir_smul (Dir_cN hΨ) a, ?_⟩
  simp only [mul_pow]
  rw [tsum_mul_left, ← ip_eq_tsum hΨ.1.continuous, inv_pow, Real.sq_sqrt hpos.le,
    inv_mul_cancel₀ hpos.ne']


end DFT.Continuum.Sine
