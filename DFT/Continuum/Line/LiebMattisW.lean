/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.RefState
import DFT.Continuum.Line.Nondeg

/-!
# The Lieb–Mattis theorem on `H¹₀` for continuous potentials

For `N = n + 1` spin-½ particles on `[0, 1]` with a spin-independent Hamiltonian
`-Δ + Σ_k v(x_k) + w`, `v` continuous and `w` continuous and invariant under relabelling, let
`E(a, b)` be the ground-state energy of the sector with `a` spins up and `b = N - a` down (spatial
states of Young symmetry `(a, b)` with finite kinetic energy). **Lieb–Mattis**:

`E(a, b) < E(a + 1, b - 1)` whenever `a ≥ b ≥ 1` (**`lieb_mattis_W`**).

The proof. Let `Ψ` be a ground state of type `(a + 1, b - 1)` with energy `E'`. Its lowering
`f = altY a Ψ` is nonzero (`integral_mul_altY_lower_pos`) and an eigenstate of type `(a, b)` with
energy `E'` (`Q_altY_W`), so `E(a, b) ≤ E'`. If equality held, `f` would be a ground state of type
`(a, b)`, so `f = ±PhiY f` (`gs_sign_WY`): `±f` has the chamber sign, and `±f φ₀ ≥ 0` a.e., strictly
positive on a box, for the highest-weight reference state `φ₀` (`Line/RefState`). Hence
`⟨f, φ₀⟩ ≠ 0`. But `⟨f, φ₀⟩ = |YG a| ⟨Ψ, φ₀⟩` and `|YG (a+1)| ⟨Ψ, φ₀⟩ = ⟨Ψ, altY (a+1) φ₀⟩ = 0`
by Fock's condition.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {w : Cfg n → ℝ} {hw : Continuous w} {v : Pot}

/-- **The Lieb–Mattis theorem on `H¹₀`**, continuous `v` and relabelling-invariant continuous `w`:
`E(a, b) < E(a + 1, b - 1)` for `a + b = N`, `a ≥ b ≥ 1`. -/
theorem lieb_mattis_W (hws : ∀ σ x, w (pm σ x) = w x) {a b : ℕ} (hab : a + b = n + 1)
    (hb1 : 1 ≤ b) (hba : b ≤ a) {Φ Ψ : Cfg n → ℝ}
    (hΦ : IsGS (settingWS (ymix a) w hw) v Φ) (hΨ : IsGS (settingWS (ymix (a + 1)) w hw) v Ψ) :
    Q (settingWS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ <
      Q (settingWS (ymix (a + 1)) w hw) v Ψ / ip (μ := μN n) Ψ Ψ := by
  set E := Q (settingWS (ymix a) w hw) v Φ / ip (μ := μN n) Φ Φ
  set E' := Q (settingWS (ymix (a + 1)) w hw) v Ψ / ip (μ := μN n) Ψ Ψ
  set f := altY a Ψ
  have hΨ1 : H1W Ψ := h1W_of_mem hΨ.1
  have hfD : f ∈ DomWS (ymix (n := n) a) := altY_memWS hΨ1
  -- the lowered state is nonzero
  have hΨf := integral_mul_altY_lower_pos hab hb1 hba hΨ.1.1 (antiY_of_mem hΨ.1) hΨ.2.1
  have hfpos : 0 < ip (μ := μN n) f f := by
    rcases (ip_nonneg (μ := μN n) f).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := ae_zero_of_ip_zero (S := settingWS (ymix a) w hw) hfD h.symm
      have : ∫ x, Ψ x * altY a Ψ x ∂μN n = 0 := integral_eq_zero_of_ae (by
        filter_upwards [hz] with x hx
        change Ψ x * f x = 0
        rw [hx, Pi.zero_apply, mul_zero])
      linarith
  -- it is an eigenstate with energy `E'`
  have hQf : Q (settingWS (ymix a) w hw) v f = E' * ip (μ := μN n) f f := Q_altY_W hw hws hΨ
  have hle : E * ip (μ := μN n) f f ≤ Q (settingWS (ymix a) w hw) v f := le_Q_of_isGS hΦ hfD
  have hEE : E ≤ E' := by nlinarith
  refine lt_of_le_of_ne hEE fun hEq => ?_
  -- equality makes `f` a ground state
  have hfGS : IsGS (settingWS (ymix a) w hw) v f := by
    refine ⟨hfD, hfpos, fun φ hφ => ?_⟩
    have h1 := le_Q_of_isGS hΦ hφ
    have h0 : 0 ≤ ip (μ := μN n) φ φ := ip_nonneg φ
    rw [hQf, ← hEq]
    nlinarith
  -- `⟨f, φ₀⟩ = 0`
  have hφ0L : MemLp (phi0 (n := n) a) 2 (μN n) := memLp_cont (continuous_phi0 a)
  have hzero : ∫ x, f x * phi0 a x ∂μN n = 0 := by
    have h1 : ∫ x, f x * phi0 a x ∂μN n = ∫ x, Ψ x * altY a (phi0 a) x ∂μN n :=
      integral_altY_mul hΨ.1.1 hφ0L
    have h2 : ∫ x, Ψ x * altY a (phi0 a) x ∂μN n = cardY n a * ∫ x, Ψ x * phi0 a x ∂μN n := by
      rw [← integral_const_mul]
      exact integral_congr_ae (by
        filter_upwards [altY_ae_of_antiY (antiY_phi0 (n := n) a)] with x hx
        rw [hx]; ring)
    have h3 := integral_mul_altY_of_antiY hΨ.1.1 (antiY_of_mem hΨ.1) hφ0L (a := a + 1)
    have h4 : ∫ x, Ψ x * altY (a + 1) (phi0 a) x ∂μN n = 0 := by
      simp only [altY_phi0 hab hb1 hba, mul_zero, integral_zero]
    rw [h4] at h3
    have hc := (cardY_pos (n := n) (a := a + 1)).ne'
    have hΨφ : ∫ x, Ψ x * phi0 a x ∂μN n = 0 := by
      rcases mul_eq_zero.1 h3.symm with h | h
      · exact absurd h hc
      · exact h
    rw [h1, h2, hΨφ, mul_zero]
  -- the sign of `f φ₀`
  obtain ⟨ε, hε, hfε⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ f =ᵐ[μN n] fun x => ε * PhiY a f x := by
    rcases gs_sign_WY hfGS with h | h
    · exact ⟨1, Or.inl rfl, by filter_upwards [h] with x hx; rw [hx, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by filter_upwards [h] with x hx; rw [hx]; simp⟩
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  set F : Cfg n → ℝ := fun x => ε * (f x * phi0 a x)
  have hFint : Integrable F (μN n) := (int_mul_L2 hfD.1 hφ0L).const_mul ε
  -- pointwise: `ε f φ₀ = |f| P(sorted x)` off a null set
  have hpt : ∀ᵐ x ∂μN n, ∃ σ : Equiv.Perm (Fin (n + 1)), YG a σ ∧ pm σ x ∈ RY a n ∧
      F x = |f x| * Pst a (pm σ x) := by
    filter_upwards [ae_cube, ae_injective, hfε, PhiBY_ae_eq_abs hfD] with x hx hinj h1 h2
    obtain ⟨σ, hσ, hσR⟩ := exists_YG_sort (a := a) hx hinj
    refine ⟨σ, hσ, hσR, ?_⟩
    have hs := (sorted_Y (Ψ := f) hx hinj hσ hσR 0).2.2.2.2
    have hPhi := (PhiY_sgnY (a := a) (Ψ := f) hx hinj 0).1
    have hφ : phi0 a x = sgn σ * Pst a (pm σ x) := by
      have := phi0_pm a hσ x
      rw [phi0_eq_Pst hσR (hinj.comp σ.injective)] at this
      rw [this, ← mul_assoc, sgn_mul_self, one_mul]
    have hfx : f x = ε * sgn σ * |f x| := by
      conv_lhs => rw [h1, hPhi, h2, hs]
      ring
    simp only [F]
    rw [hφ]
    conv_lhs => rw [hfx]
    linear_combination (|f x| * Pst a (pm σ x)) * (sgn σ * sgn σ) * hεε +
      |f x| * Pst a (pm σ x) * sgn_mul_self σ
  have hFnn : ∀ᵐ x ∂μN n, 0 ≤ F x := by
    filter_upwards [hpt] with x hx
    obtain ⟨σ, -, -, hF⟩ := hx
    rw [hF]; exact mul_nonneg (abs_nonneg _) (Pst_nonneg a _)
  -- strictly positive on the box
  set B := boxB (n := n) a
  have hBR : B ⊆ RY a n := boxB_sub_RY hab hba
  have hFpos : ∀ᵐ x ∂(μN n).restrict B, 0 < F x := by
    have h : ∀ᵐ x ∂(μN n).restrict B, (∃ σ : Equiv.Perm (Fin (n + 1)), YG a σ ∧
        pm σ x ∈ RY a n ∧ F x = |f x| * Pst a (pm σ x)) ∧ f x ≠ 0 ∧
        Function.Injective x ∧ x ∈ B := by
      refine (ae_restrict_iff' (isOpen_boxB a).measurableSet).2 ?_
      filter_upwards [hpt, gs_ne_zero_WY hfGS, ae_injective] with x hx hne hinj hxB
      exact ⟨hx, hne, hinj, hxB⟩
    filter_upwards [h] with x hx
    obtain ⟨⟨σ, hσ, hσR, hF⟩, hne, hinj, hxB⟩ := hx
    have hσ1 : σ = 1 := YG_eq_of_mem_RY (hBR hxB).1 hinj hσ (YG_one a) hσR
      (by rw [pm_one]; exact hBR hxB)
    rw [hF, hσ1, pm_one]
    exact mul_pos (abs_pos.2 hne) (Pst_pos_boxB hxB)
  have hBmeas : (μN n) B ≠ 0 := by
    rw [Measure.restrict_apply (isOpen_boxB a).measurableSet,
      inter_eq_left.2 (show B ⊆ Cube n from fun x hx => (hBR hx).1)]
    exact (measure_boxB_pos a).ne'
  have hIB : 0 < ∫ x in B, F x ∂μN n := by
    rcases (setIntegral_nonneg_ae (isOpen_boxB a).measurableSet
      (hFnn.mono fun x hx _ => hx)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hFnn)
        hFint.integrableOn).1 h.symm
      have hF : ∀ᵐ x ∂(μN n).restrict B, False := by
        filter_upwards [hz, hFpos] with x h1 h2
        simp only [Pi.zero_apply] at h1; linarith
      have hμ := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hF)
      exact hBmeas (by simpa using congrArg (fun ν : Measure (Cfg n) => ν univ) hμ)
  have hI : 0 < ∫ x, F x ∂μN n :=
    lt_of_lt_of_le hIB (setIntegral_le_integral hFint hFnn)
  have : ∫ x, F x ∂μN n = ε * ∫ x, f x * phi0 a x ∂μN n := integral_const_mul _ _
  rw [this, hzero, mul_zero] at hI
  exact lt_irrefl _ hI

end DFT.Continuum.Line
