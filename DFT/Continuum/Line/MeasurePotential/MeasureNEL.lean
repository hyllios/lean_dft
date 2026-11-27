/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureN

/-!
# The Euler–Lagrange equation for `N` particles in a measure potential

* `int_rhoHat`: `∫ v ρ̂_Φ = ∫ Σ_k v(x_k) Φ²` for continuous `v`.
* `rhoHat2`: the mixed continuous density `ρ̂(Φ, Ψ)`, by polarisation; `int_rhoHat2`.
* `rhoHat_expand`: `ρ̂(Φ + sΨ) = ρ̂(Φ) + 2s ρ̂(Φ, Ψ) + s² ρ̂(Ψ)`; `QMN_expand`.
* `rhoHat_smul`, `QMN_smul`; `QMN_null`: `QMN ≥ 0` on null states.
* `EN_mul_le`: a normalised ground state with energy `E` has `E ∫ χ² ≤ QMN χ` on `H¹₀`.
* **`euler_lagrangeN`**: `h₀(Φ, Ψ) + ν(ρ̂(Φ, Ψ)) = E ∫ Φ Ψ` for all `Ψ ∈ H¹₀`.
* `rhoHat_abs`, **`isGSN_abs`**: for bosons, `|Φ|` is a ground state whenever `Φ` is.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ}

/-- `ρ̂_Φ` has the integrals `∫ Σ_k v(x_k) Φ²`. -/
lemma int_rhoHat (hw : Continuous w) {Φ : Cfg n → ℝ} (h : Φ ∈ DomW τ n) (v : Pot) :
    ∫ t, ext v t * ext (rhoHat τ Φ) t ∂μ1 = pf (settingW τ n w hw) v Φ Φ := by
  rw [rhoHat_spec h, ← dens_eq_rhoNW (w := w) (hw := hw) h]; rfl

lemma integrable_ext_mul (v p : Pot) : Integrable (fun t => ext v t * ext p t) μ1 := by
  have hb : ∀ (r : Pot) (x : ℝ), |ext r x| ≤ ‖r‖ := fun r x => by
    simpa [SturmLiouville.ext] using r.norm_coe_le_norm _
  exact Integrable.of_bound ((continuous_ext v).mul (continuous_ext _)).aestronglyMeasurable
    (‖v‖ * ‖p‖) (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hb v t) (hb _ t) (abs_nonneg _)
        (norm_nonneg _))

/-- Integrals against `v` are linear in the continuous function. -/
lemma int_ext_add_smul (v p q : Pot) (a b : ℝ) :
    ∫ t, ext v t * ext (a • p + b • q) t ∂μ1 =
      a * ∫ t, ext v t * ext p t ∂μ1 + b * ∫ t, ext v t * ext q t ∂μ1 := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_ext_mul v p).const_mul a) ((integrable_ext_mul v q).const_mul b)]
  congr 1; funext t
  simp only [SturmLiouville.ext, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]; ring

variable (τ) in
/-- The mixed continuous density `ρ̂(Φ, Ψ) = (ρ̂(Φ + Ψ) - ρ̂(Φ - Ψ)) / 4`. -/
noncomputable def rhoHat2 (Φ Ψ : Cfg n → ℝ) : Pot :=
  (1 / 4 : ℝ) • (rhoHat τ (Φ + Ψ) - rhoHat τ (Φ - Ψ))

lemma int_rhoHat2 (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) (hΨ : Ψ ∈ DomW τ n)
    (v : Pot) : ∫ t, ext v t * ext (rhoHat2 τ Φ Ψ) t ∂μ1 = pf (settingW τ n w hw) v Φ Ψ := by
  have e : rhoHat2 τ Φ Ψ = (1 / 4 : ℝ) • rhoHat τ (Φ + Ψ) + (-(1 / 4) : ℝ) • rhoHat τ (Φ - Ψ) := by
    rw [rhoHat2, smul_sub, sub_eq_add_neg, neg_smul]
  rw [e, int_ext_add_smul, int_rhoHat hw (add_mem hΦ hΨ), int_rhoHat hw (sub_mem hΦ hΨ)]
  have h1 := pf_expand (S := settingW τ n w hw) v hΦ hΨ 1
  have h2 := pf_expand (S := settingW τ n w hw) v hΦ hΨ (-1)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at h1 h2
  rw [h1, h2]; ring

/-- **`ρ̂(Φ + sΨ) = ρ̂(Φ) + 2s ρ̂(Φ, Ψ) + s² ρ̂(Ψ)`.** -/
lemma rhoHat_expand (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    (hΨ : Ψ ∈ DomW τ n) (s : ℝ) :
    rhoHat τ (Φ + s • Ψ) = (1 : ℝ) • rhoHat τ Φ + (2 * s) • rhoHat2 τ Φ Ψ +
      (s ^ 2) • rhoHat τ Ψ := by
  refine pot_eq_of_integral fun v => ?_
  have hsΨ : s • Ψ ∈ DomW τ n := Submodule.smul_mem _ s hΨ
  rw [int_rhoHat hw (add_mem hΦ hsΨ), pf_expand (S := settingW τ n w hw) v hΦ hΨ s]
  rw [show (1 : ℝ) • rhoHat τ Φ + (2 * s) • rhoHat2 τ Φ Ψ + s ^ 2 • rhoHat τ Ψ =
      (1 : ℝ) • ((1 : ℝ) • rhoHat τ Φ + (2 * s) • rhoHat2 τ Φ Ψ) + (s ^ 2) • rhoHat τ Ψ by
    simp, int_ext_add_smul, int_ext_add_smul, int_rhoHat hw hΦ, int_rhoHat2 hw hΦ hΨ,
    int_rhoHat hw hΨ]
  ring

lemma QMN_expand (hw : Continuous w) (ν : PotM) {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n)
    (hΨ : Ψ ∈ DomW τ n) (s : ℝ) :
    QMN τ w ν (Φ + s • Ψ) = QMN τ w ν Φ +
      2 * s * (h0W n w Φ Ψ + ν (rhoHat2 τ Φ Ψ)) + s ^ 2 * QMN τ w ν Ψ := by
  have h := h0_expand (S := settingW τ n w hw) hΦ hΨ s
  change h0W n w (Φ + s • Ψ) (Φ + s • Ψ) = h0W n w Φ Φ + 2 * s * h0W n w Φ Ψ +
    s ^ 2 * h0W n w Ψ Ψ at h
  simp only [QMN, h, rhoHat_expand hw hΦ hΨ s, map_add, map_smul, smul_eq_mul]
  ring

lemma int_ext_smul (v p : Pot) (a : ℝ) :
    ∫ t, ext v t * ext (a • p) t ∂μ1 = a * ∫ t, ext v t * ext p t ∂μ1 := by
  rw [← integral_const_mul]; congr 1; funext t
  simp only [SturmLiouville.ext, ContinuousMap.smul_apply, smul_eq_mul]; ring

lemma rhoHat_smul (hw : Continuous w) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) (c : ℝ) :
    rhoHat τ (c • Ψ) = c ^ 2 • rhoHat τ Ψ :=
  pot_eq_of_integral fun v => by
    rw [int_rhoHat hw (Submodule.smul_mem _ c hΨ), int_ext_smul, int_rhoHat hw hΨ]
    simp only [pf, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext x; ring

lemma QMN_smul (hw : Continuous w) (ν : PotM) {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) (c : ℝ) :
    QMN τ w ν (c • Ψ) = c ^ 2 * QMN τ w ν Ψ := by
  have h := (settingW τ n w hw).h0_smul c Ψ hΨ (c • Ψ) (Submodule.smul_mem _ c hΨ)
  have h' := (settingW τ n w hw).h0_symm Ψ hΨ (c • Ψ) (Submodule.smul_mem _ c hΨ)
  have h'' := (settingW τ n w hw).h0_smul c Ψ hΨ Ψ hΨ
  change h0W n w (c • Ψ) (c • Ψ) = c * h0W n w Ψ (c • Ψ) at h
  change h0W n w Ψ (c • Ψ) = h0W n w (c • Ψ) Ψ at h'
  change h0W n w (c • Ψ) Ψ = c * h0W n w Ψ Ψ at h''
  simp only [QMN, h, h', h'', rhoHat_smul hw hΨ, map_smul, smul_eq_mul]; ring

/-- On null states the energy is nonnegative. -/
lemma QMN_null (hw : Continuous w) (ν : PotM) {χ : Cfg n → ℝ} (hχ : χ ∈ DomW τ n)
    (h0 : ∫ x, χ x ^ 2 ∂μN n = 0) : 0 ≤ QMN τ w ν χ := by
  have hip : ip (μ := μN n) χ χ = 0 := by rw [← h0]; simp only [ip, sq]
  have hz : rhoHat τ χ = 0 := by
    refine pot_eq_of_integral fun v => ?_
    rw [int_rhoHat hw hχ]
    have hzz : (fun x => χ x * χ x) =ᵐ[μN n] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (χ x)) (int_mul_L2 hχ.1 hχ.1)).1
        hip
    simp only [pf]
    rw [integral_congr_ae (hzz.mono fun x hx => by simp only [hx, Pi.zero_apply, mul_zero] :
      (fun x => (settingW τ n w hw).L v x * (χ x * χ x)) =ᵐ[μN n] fun _ => (0 : ℝ))]
    simp [SturmLiouville.ext]
  rw [QMN, hz, map_zero, add_zero]
  exact h0W_null (s := τ.toSym) hw hχ hip

/-- A normalised ground state with energy `E` has `E ∫ χ² ≤ QMN χ` on `H¹₀`. -/
lemma EN_mul_le (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN τ w ν Φ)
    {χ : Cfg n → ℝ} (hχ : χ ∈ DomW τ n) : QMN τ w ν Φ * ∫ x, χ x ^ 2 ∂μN n ≤ QMN τ w ν χ := by
  set m := ∫ x, χ x ^ 2 ∂μN n
  have hm : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  rcases hm.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact QMN_null hw ν hχ h0.symm
  · set c := 1 / √m
    have hc2 : c ^ 2 = 1 / m := by rw [div_pow, Real.sq_sqrt hm, one_pow]
    have hn : ∫ x, (c • χ) x ^ 2 ∂μN n = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, integral_const_mul, hc2]
      exact one_div_mul_cancel hpos.ne'
    have := h.2.2 _ (Submodule.smul_mem _ c hχ) hn
    rw [QMN_smul hw ν hχ, hc2] at this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos] at this
    linarith [mul_comm (QMN τ w ν Φ) m]

/-- **The Euler–Lagrange equation** for a normalised `N`-particle ground state of a measure
potential, with energy `E = QMN Φ`. -/
theorem euler_lagrangeN (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN τ w ν Φ)
    {Ψ : Cfg n → ℝ} (hΨ : Ψ ∈ DomW τ n) :
    h0W n w Φ Ψ + ν (rhoHat2 τ Φ Ψ) = QMN τ w ν Φ * ∫ x, Φ x * Ψ x ∂μN n := by
  have hΦ := h.1
  have hsq : ∀ s : ℝ, ∫ x, (Φ + s • Ψ) x ^ 2 ∂μN n =
      1 + 2 * s * ∫ x, Φ x * Ψ x ∂μN n + s ^ 2 * ∫ x, Ψ x ^ 2 ∂μN n := fun s => by
    have := integral_expand (μ := μN n) (g := fun _ => (1 : ℝ)) (ψ := Φ) (φ := Ψ)
      (by simpa using int_mul_L2 hΦ.1 hΦ.1) (by simpa using int_mul_L2 hΦ.1 hΨ.1)
      (by simpa using int_mul_L2 hΨ.1 hΨ.1) s
    simp only [one_mul] at this
    simp only [sq]; rw [this, ← h.2.1]; simp only [sq]
  have key := eq_zero_of_quad (a := h0W n w Φ Ψ + ν (rhoHat2 τ Φ Ψ) -
      QMN τ w ν Φ * ∫ x, Φ x * Ψ x ∂μN n)
    (c := QMN τ w ν Ψ - QMN τ w ν Φ * ∫ x, Ψ x ^ 2 ∂μN n) fun s => by
    have h1 := EN_mul_le hw h (add_mem hΦ (Submodule.smul_mem _ s hΨ))
    rw [hsq, QMN_expand hw ν hΦ hΨ] at h1
    linarith
  linarith

/-- For bosons, `ρ̂_{|Φ|} = ρ̂_Φ`. -/
lemma rhoHat_abs (hw : Continuous w) {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW .bos n) :
    rhoHat .bos (fun x => |Φ x|) = rhoHat .bos Φ :=
  pot_eq_of_integral fun v => by
    rw [int_rhoHat (w := w) hw (abs_mem_DomW hΦ), int_rhoHat (w := w) hw hΦ]
    simp only [pf, abs_mul_abs_self]

/-- **For bosons, `|Φ|` is a ground state whenever `Φ` is.** -/
theorem isGSN_abs (hw : Continuous w) {ν : PotM} {Φ : Cfg n → ℝ} (h : IsGSN .bos w ν Φ) :
    IsGSN .bos w ν (fun x => |Φ x|) := by
  have hD := abs_mem_DomW h.1
  have hn : ∫ x, |Φ x| ^ 2 ∂μN n = 1 := by simpa [sq_abs] using h.2.1
  have hQ : QMN .bos w ν (fun x => |Φ x|) ≤ QMN .bos w ν Φ := by
    simp only [QMN, h0W_self, rhoHat_abs hw h.1, abs_mul_abs_self]
    linarith [kinW_abs_le h.1]
  exact ⟨hD, hn, fun Ψ hΨ hΨn => hQ.trans (h.2.2 Ψ hΨ hΨn)⟩

end DFT.Continuum.Line
