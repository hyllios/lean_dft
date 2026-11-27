/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.Applications.HardCoreW

/-!
# The Tonks–Girardeau gas on `H¹₀`

* `isGS_W_of_isGS`: a `C²` ground state is an `H¹₀` ground state, since the two settings have the
  same ground-state energy (`gsE_le_QW`).
* **`tonks_girardeau_W`**: for every continuous `v`, Girardeau's sign times the Slater determinant
  of the `N` lowest orbitals of `-d²/dx² + v` is the hard-core ground state on `H¹₀` with no further
  interaction. Its modulus is the modulus of the determinant, its norm is `N!`, its density is
  `N!` times the free-fermion density `Σ_j φ_j²`, and every other ground state is a multiple of it.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {hw : Continuous w}

/-- **A `C²` ground state is an `H¹₀` ground state.** -/
theorem isGS_W_of_isGS {v : Pot} {Φ : Cfg n → ℝ} (h : IsGS (setting τ n w hw) v Φ) :
    IsGS (settingW τ n w hw) v Φ := by
  have hp := h.2.1
  set c := (√(ip (μ := μN n) Φ Φ))⁻¹
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hp).ne'
  have hcc : c * c * ip (μ := μN n) Φ Φ = 1 := by
    simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  have hG := isGS_smul h hc0
  have hN : c • Φ ∈ Nst (setting τ n w hw) := ⟨hG.1, by rw [ip_smul_self, hcc]⟩
  have hmin : ∀ χ ∈ Nst (setting τ n w hw), Q (setting τ n w hw) v (c • Φ) ≤
      Q (setting τ n w hw) v χ := fun χ hχ => by
    have := hG.2.2 χ hχ.1
    rwa [show ip (μ := μN n) χ χ = 1 from hχ.2, show ip (μ := μN n) (c • Φ) (c • Φ) = 1 from hN.2,
      mul_one, mul_one] at this
  have hNW : IsNGS (settingW τ n w hw) v (c • Φ) := by
    refine ⟨⟨Dom_le_DomW hN.1, hN.2⟩, fun Ψ hΨ => ?_⟩
    have h1 : ((Q (setting τ n w hw) v (c • Φ) : ℝ) : EReal) ≤ gsE (setting τ n w hw) v :=
      le_iInf₂ fun χ hχ => EReal.coe_le_coe_iff.2 (hmin χ hχ)
    rw [QW_eq_Q v hN.1]
    exact EReal.coe_le_coe_iff.1 (h1.trans (gsE_le_QW v hΨ))
  have := isGS_smul (isGS_W_of_isNGS_W hNW) (inv_ne_zero hc0)
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

/-- **The Tonks–Girardeau gas on `H¹₀`.** For every continuous potential `v` there are `N`
orthonormal `C²` orbitals `φ_j` (the lowest eigenfunctions of `-d²/dx² + v`) such that
`A · det φ_j(x_i)` is the ground state of `N` hard-core bosons with no further interaction. Its
modulus is `|det φ_j(x_i)|`, its norm is `N!`, its density is `N!` times the free-fermion density
`Σ_j φ_j²`, and every other ground state is a multiple of it. -/
theorem tonks_girardeau_W (v : Pot) : ∃ φ : Fin (n + 1) → ℝ → ℝ, (∀ j, φ j ∈ SturmLiouville.Dom) ∧
    (∀ a b, ∫ t, φ a t * φ b t ∂μ1 = if a = b then 1 else 0) ∧
    IsGS (settingHCW n (fun _ => 0) continuous_const) v (mulA (slater φ)) ∧
    (∀ x, |mulA (slater φ) x| = |slater φ x|) ∧
    ip (μ := μN n) (mulA (slater φ)) (mulA (slater φ)) = (Nat.factorial (n + 1) : ℝ) ∧
    (∀ u, dens (settingHCW n (fun _ => 0) continuous_const) (mulA (slater φ)) u =
      (Nat.factorial (n + 1) : ℝ) * ∫ t, ext u t * ∑ j, φ j t ^ 2 ∂μ1) ∧
    ∀ Ψ, IsGS (settingHCW n (fun _ => 0) continuous_const) v Ψ →
      ∃ c : ℝ, Ψ =ᵐ[μN n] c • mulA (slater φ) := by
  obtain ⟨φ, lam, Λ, hφ, hode, hon, hle, hbound⟩ := Spectral.exists_orbitals v n
  have hnorm : ∀ j, ∫ x, φ j x * φ j x ∂μ1 = 1 := fun j => by rw [hon]; simp
  have hD := slater_mem hφ
  have hQ := Q_slater hφ hode
  have hpos := ip_slater_pos hφ hon
  have hlow : ∀ φ' ∈ DomF n, (∑ j, lam j) * ip (μ := μN n) φ' φ' ≤ Q (freeS .fer n) v φ' :=
    fun φ' h => lower_bound_fer h v hφ hbound hle hnorm
  have hGS : IsGS (freeS .fer n) v (slater φ) := ⟨hD, hpos, fun φ' hφ' => by
    rw [hQ]; nlinarith [mul_le_mul_of_nonneg_left (hlow φ' hφ') hpos.le]⟩
  have hDW : slater φ ∈ DomW .fer n := Dom_le_DomW hD
  have hG := (isGS_mulA_W_iff (w := fun _ => 0) (hw := continuous_const) hDW v).2
    (isGS_W_of_isGS hGS)
  have hc : ∀ j, Continuous (φ j) := fun j => (hφ j).1.continuous
  refine ⟨φ, hφ, hon, hG, fun x => ?_, ?_, fun u => ?_, fun Ψ hΨ => ?_⟩
  · rw [← sq_eq_sq_iff_abs_eq_abs, sq_mulA hD]
  · rw [ip_mulA_W]; exact integral_slater_sq hc hon
  · rw [dens_mulA_W]; exact integral_LN_slater hc hon u
  · obtain ⟨Φ, hΦ, -, huniq⟩ := exists_unique_gs_hcW (n := n) continuous_const v
    obtain ⟨a, ha⟩ := huniq Ψ hΨ
    obtain ⟨b, hb⟩ := huniq _ hG
    have hb0 : b ≠ 0 := by
      rintro rfl
      have h0 : ip (μ := μN n) (mulA (slater φ)) (mulA (slater φ)) = 0 :=
        integral_eq_zero_of_ae (by filter_upwards [hb] with x hx; simp [hx])
      exact hG.2.1.ne' h0
    refine ⟨a / b, ?_⟩
    filter_upwards [ha, hb] with x h1 h2
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h1, h2]; field_simp

end DFT.Continuum.Line
