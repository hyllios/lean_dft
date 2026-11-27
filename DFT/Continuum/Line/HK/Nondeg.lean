/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.General.VRep
import DFT.Continuum.Line.HK.UcpBos
import DFT.Continuum.Line.HK.UcpY

/-!
# Nondegeneracy of `H¹₀` ground states for continuous potentials

For bosons, fermions and every spin sector `ymix a` on the line, with continuous `v` and `w`, the
ground state is unique up to a constant factor (a.e.).

Abstractly (any setting satisfying unique continuation):

* `gs_eq_or_neg`: if `ψ` and `φ` are ground states with `φ² = ψ²` a.e., then `ψ = ±φ` a.e.
  (`(φ + ψ)(φ - ψ) = 0`, and each factor is a ground state or zero);
* `gs_unique_of_sign`: if every ground state has a fixed sign on a set `R` of positive measure,
  any two ground states are proportional (`ψ - cφ` with `∫_R (ψ - cφ) = 0` cannot be a ground
  state, so it vanishes).

On the line: `|Ψ|` (bosons) and the chamber state `PhiY` (spin sectors) are ground states with the
same square as `Ψ`, and nonnegative on the cube, resp. on the Young chamber `RY`.

* **`gs_unique_W_bos`**, **`gs_unique_WY`**, **`gs_unique_W_fer`**, **`gs_unique_W`**,
  **`gs_unique_SD`**;
* **`exists_unique_gs_W_cont`**, **`exists_unique_gs_WY`**: existence and uniqueness;
* **`ensDens_iff_W_cont`**, **`ensVRep_iff_W_cont`**, **`ensDens_iff_WY`**: ensemble densities
  are pure densities (every ground-state ensemble has the density of the ground state).
-/

namespace DFT.Continuum

open MeasureTheory Set

section general

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {P : Type*} [AddCommGroup P] [Module ℝ P]
  {S : Setting μ P} {v : P}

/-- A state of zero norm vanishes a.e. -/
lemma ae_zero_of_ip_zero {χ : X → ℝ} (hχ : χ ∈ S.D) (h : ip (μ := μ) χ χ = 0) :
    χ =ᵐ[μ] 0 := by
  have h2 := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (χ x))
    (S.int_sq χ χ hχ hχ)).1 h
  filter_upwards [h2] with _ hx
  simpa using hx

lemma ip_nonneg (χ : X → ℝ) : 0 ≤ ip (μ := μ) χ χ := integral_nonneg fun _ => mul_self_nonneg _

/-- **Two ground states with the same square agree up to sign**, given unique continuation. -/
theorem gs_eq_or_neg {ψ φ : X → ℝ} (hψ : IsGS S v ψ) (hφ : IsGS S v φ)
    (hsq : ∀ᵐ x ∂μ, φ x * φ x = ψ x * ψ x) (hucp : ∀ χ, IsGS S v χ → ∀ᵐ x ∂μ, χ x ≠ 0) :
    ψ =ᵐ[μ] φ ∨ ψ =ᵐ[μ] -φ := by
  have hu : φ + (1 : ℝ) • ψ ∈ S.D := S.D.add_mem hφ.1 (S.D.smul_mem 1 hψ.1)
  have hd : φ + (-1 : ℝ) • ψ ∈ S.D := S.D.add_mem hφ.1 (S.D.smul_mem (-1) hψ.1)
  rcases (ip_nonneg (μ := μ) (φ + (1 : ℝ) • ψ)).lt_or_eq with hu0 | hu0
  · rcases (ip_nonneg (μ := μ) (φ + (-1 : ℝ) • ψ)).lt_or_eq with hd0 | hd0
    · exfalso
      have g1 := hucp _ (isGS_add_smul hφ hψ 1 hu0)
      have g2 := hucp _ (isGS_add_smul hφ hψ (-1) hd0)
      have hF : ∀ᵐ x ∂μ, False := by
        filter_upwards [g1, g2, hsq] with x h1 h2 h3
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul] at h1 h2
        have : (φ x + ψ x) * (φ x + -ψ x) = 0 := by linear_combination h3
        exact mul_ne_zero h1 h2 this
      have hμ : μ = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hF)
      have := hψ.2.1
      simp [ip, hμ] at this
    · left
      filter_upwards [ae_zero_of_ip_zero hd hd0.symm] with x hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
      linarith
  · right
    filter_upwards [ae_zero_of_ip_zero hu hu0.symm] with x hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.neg_apply] at hx ⊢
    linarith

/-- **Sign-definite ground states are unique up to a factor.** -/
theorem gs_unique_of_sign {R : Set X} (hRpos : μ R ≠ 0)
    (hint : ∀ χ ∈ S.D, IntegrableOn χ R μ) (hucp : ∀ χ, IsGS S v χ → ∀ᵐ x ∂μ, χ x ≠ 0)
    (hsign : ∀ χ, IsGS S v χ →
      (∀ᵐ x ∂μ.restrict R, χ x = |χ x|) ∨ (∀ᵐ x ∂μ.restrict R, χ x = -|χ x|))
    {ψ φ : X → ℝ} (hψ : IsGS S v ψ) (hφ : IsGS S v φ) : ∃ c : ℝ, ψ =ᵐ[μ] c • φ := by
  -- a ground state has nonzero integral over `R`
  have hI : ∀ χ, IsGS S v χ → ∫ x in R, χ x ∂μ ≠ 0 := by
    intro χ hχ h0
    have habs : ∫ x in R, |χ x| ∂μ = 0 := by
      rcases hsign χ hχ with h | h
      · rw [← h0]; exact integral_congr_ae (by filter_upwards [h] with x hx; rw [← hx])
      · rw [← neg_eq_zero, ← integral_neg, ← h0]
        exact integral_congr_ae (by filter_upwards [h] with x hx; exact hx.symm)
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg (χ x))
      (hint χ hχ.1).abs).1 habs
    have hF : ∀ᵐ x ∂μ.restrict R, False := by
      filter_upwards [hz, ae_restrict_of_ae (hucp χ hχ)] with x h1 h2
      exact h2 (abs_eq_zero.1 h1)
    have hμ : μ.restrict R = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hF)
    exact hRpos (by simpa using congrArg (fun ν : Measure X => ν univ) hμ)
  refine ⟨(∫ x in R, ψ x ∂μ) / ∫ x in R, φ x ∂μ, ?_⟩
  set c := (∫ x in R, ψ x ∂μ) / ∫ x in R, φ x ∂μ
  have hχD : ψ + (-c) • φ ∈ S.D := S.D.add_mem hψ.1 (S.D.smul_mem (-c) hφ.1)
  have hIχ : ∫ x in R, (ψ + (-c) • φ) x ∂μ = 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (hint ψ hψ.1) ((hint φ hφ.1).const_mul _), integral_const_mul]
    simp only [c]
    field_simp [hI φ hφ]
    ring
  rcases (ip_nonneg (μ := μ) (ψ + (-c) • φ)).lt_or_eq with hpos | h0
  · exact absurd hIχ (hI _ (isGS_add_smul hψ hφ (-c) hpos))
  · filter_upwards [ae_zero_of_ip_zero hχD h0.symm] with x hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx ⊢
    linarith

end general

namespace Line

open SturmLiouville

variable {n : ℕ} {w : Cfg n → ℝ} {hw : Continuous w} {v : C01}

lemma integrableOn_of_memLp {f : Cfg n → ℝ} (hf : MemLp f 2 (μN n)) (R : Set (Cfg n)) :
    IntegrableOn f R (μN n) :=
  (hf.integrable one_le_two).integrableOn

/-! ### Bosons -/

/-- A bosonic ground state is `|Ψ|` or `-|Ψ|` a.e. -/
theorem gs_sign_W_bos {Ψ : Cfg n → ℝ} (hΨ : IsGS (settingW .bos n w hw) v Ψ) :
    (∀ᵐ x ∂μN n, Ψ x = |Ψ x|) ∨ (∀ᵐ x ∂μN n, Ψ x = -|Ψ x|) := by
  rcases gs_eq_or_neg (φ := fun x => |Ψ x|) hΨ (isGS_abs hΨ)
    (ae_of_all _ fun x => abs_mul_abs_self (Ψ x)) (fun _ h => gs_ne_zero_W_bos h) with h | h
  · exact Or.inl h
  · exact Or.inr h

lemma measure_cube_ne_zero : (μN n) univ ≠ 0 := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_cube]; exact one_ne_zero

/-- **Nondegeneracy for bosons**, continuous `v` and `w`. -/
theorem gs_unique_W_bos {Ψ Φ : Cfg n → ℝ} (hΨ : IsGS (settingW .bos n w hw) v Ψ)
    (hΦ : IsGS (settingW .bos n w hw) v Φ) : ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ :=
  gs_unique_of_sign (S := settingW .bos n w hw) (R := univ) measure_cube_ne_zero
    (fun χ hχ => integrableOn_of_memLp hχ.1 _)
    (fun _ h => gs_ne_zero_W_bos h)
    (fun χ hχ => by
      rw [Measure.restrict_univ]
      exact gs_sign_W_bos hχ) hΨ hΦ

/-! ### Spin sectors and fermions -/

section young

variable {a : ℕ}

/-- On the Young chamber, the chamber state is `|Ψ|`. -/
lemma PhiY_eq_abs_RY (Ψ : Cfg n → ℝ) :
    ∀ᵐ x ∂μN n, x ∈ RY a n → PhiY a Ψ x = |Ψ x| := by
  filter_upwards [ae_cube, ae_injective] with x hx hinj hxR
  have h1 : pm 1 x ∈ RY a n := by rw [pm_one]; exact hxR
  rw [(sorted_Y (Ψ := Ψ) hx hinj (YG_one a) h1 0).1, pm_one, sgn_one, one_mul]
  simp only [uY, indicator_of_mem hxR]

/-- A ground state of mixed symmetry is `PhiY` or `-PhiY` a.e. -/
theorem gs_sign_WY {Ψ : Cfg n → ℝ} (hΨ : IsGS (settingWS (ymix a) w hw) v Ψ) :
    Ψ =ᵐ[μN n] PhiY a Ψ ∨ Ψ =ᵐ[μN n] -PhiY a Ψ :=
  gs_eq_or_neg hΨ (isGS_PhiY hΨ)
    (by filter_upwards [abs_PhiY hΨ.1] with x hx
        rw [← abs_mul_abs_self, hx, abs_mul_abs_self])
    (fun _ h => gs_ne_zero_WY h)

lemma RY_nonempty : (RY a n).Nonempty := by
  refine ⟨fun i => ((i : ℝ) + 1) / ((n : ℝ) + 2), ?_, fun i j hij _ => ?_⟩
  · intro i _
    have hi : (i : ℝ) < n + 1 := by exact_mod_cast i.isLt
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
  · have : (i : ℝ) < j := by exact_mod_cast hij
    exact div_lt_div_of_pos_right (by linarith) (by positivity)

lemma measure_RY_ne_zero : (μN n) (RY a n) ≠ 0 := by
  rw [Measure.restrict_apply measurableSet_RY,
    inter_eq_left.2 (show RY a n ⊆ Cube n from fun x hx => hx.1)]
  exact (isOpen_RY.measure_pos volume RY_nonempty).ne'

/-- **Nondegeneracy in a spin sector**, continuous `v` and `w`. -/
theorem gs_unique_WY {Ψ Φ : Cfg n → ℝ} (hΨ : IsGS (settingWS (ymix a) w hw) v Ψ)
    (hΦ : IsGS (settingWS (ymix a) w hw) v Φ) : ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ := by
  refine gs_unique_of_sign (S := settingWS (ymix a) w hw) (measure_RY_ne_zero (a := a))
    (fun χ hχ => integrableOn_of_memLp hχ.1 _)
    (fun _ h => gs_ne_zero_WY h) (fun χ hχ => ?_) hΨ hΦ
  have hR := (ae_restrict_iff' measurableSet_RY).2 (PhiY_eq_abs_RY (a := a) χ)
  rcases gs_sign_WY hχ with h | h
  · left
    filter_upwards [hR, ae_restrict_of_ae h] with x h1 h2
    rw [h2, h1, abs_abs]
  · right
    filter_upwards [hR, ae_restrict_of_ae h] with x h1 h2
    rw [h2, Pi.neg_apply, h1, abs_neg, abs_abs]

end young

/-- **Nondegeneracy for fermions**, continuous `v` and `w`. -/
theorem gs_unique_W_fer {Ψ Φ : Cfg n → ℝ} (hΨ : IsGS (settingW .fer n w hw) v Ψ)
    (hΦ : IsGS (settingW .fer n w hw) v Φ) : ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ :=
  gs_unique_WY (isGS_fer_Y hΨ) (isGS_fer_Y hΦ)

/-- **Nondegeneracy on `H¹₀`**, bosons or fermions, continuous `v` and `w`. -/
theorem gs_unique_W {τ : Stat} {Ψ Φ : Cfg n → ℝ} (hΨ : IsGS (settingW τ n w hw) v Ψ)
    (hΦ : IsGS (settingW τ n w hw) v Φ) : ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ := by
  cases τ
  · exact gs_unique_W_bos hΨ hΦ
  · exact gs_unique_W_fer hΨ hΦ

/-- **Existence and uniqueness of the ground state on `H¹₀`**, continuous `v` and `w`. -/
theorem exists_unique_gs_W_cont {τ : Stat} (hw : Continuous w) (v : C01) :
    ∃ Φ, IsGS (settingW τ n w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (settingW τ n w hw) v Ψ → ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ := by
  obtain ⟨Φ, hΦ, h1⟩ := exists_isGS_W_cont (τ := τ) hw v
  exact ⟨Φ, hΦ, h1, fun Ψ hΨ => gs_unique_W hΨ hΦ⟩

/-- **Existence and uniqueness of the ground state in a spin sector**, continuous `v` and `w`. -/
theorem exists_unique_gs_WY (a : ℕ) (hw : Continuous w) (v : C01) :
    ∃ Φ, IsGS (settingWS (ymix a) w hw) v Φ ∧ ip (μ := μN n) Φ Φ = 1 ∧
      ∀ Ψ, IsGS (settingWS (ymix a) w hw) v Ψ → ∃ c : ℝ, Ψ =ᵐ[μN n] c • Φ := by
  obtain ⟨Φ, hΦ⟩ := exists_isNGS_WY_cont a hw v
  exact ⟨Φ, isGS_W_of_isNGS_W hΦ, hΦ.1.2, fun Ψ hΨ => gs_unique_WY hΨ (isGS_W_of_isNGS_W hΦ)⟩

/-! ### Ensembles give nothing new -/

/-- **Ensemble densities are pure densities** on `H¹₀`, continuous `v` and `w`. -/
theorem ensDens_iff_W_cont {τ : Stat} (v : C01) (ρ : C01 → ℝ) :
    EnsDens (settingW τ n w hw) v ρ ↔ PureDens (settingW τ n w hw) v ρ :=
  ⟨pureDens_of_ensDens fun _ _ hψ hψ1 hφ hφ1 => by
      obtain ⟨c, hc⟩ := gs_unique_W hψ hφ
      exact dens_eq_of_ae_smul hc hψ1 hφ1,
    ensDens_of_pureDens⟩

/-- **Ensemble `v`-representability equals pure-state `v`-representability** on `H¹₀`. -/
theorem ensVRep_iff_W_cont {τ : Stat} (ρ : C01 → ℝ) :
    EnsVRep (settingW τ n w hw) ρ ↔ PureVRep (settingW τ n w hw) ρ :=
  ⟨fun ⟨v, h⟩ => ⟨v, (ensDens_iff_W_cont v ρ).1 h⟩, fun ⟨v, h⟩ => ⟨v, ensDens_of_pureDens h⟩⟩

/-- **Ensemble densities are pure densities** in each spin sector. -/
theorem ensDens_iff_WY {a : ℕ} (v : C01) (ρ : C01 → ℝ) :
    EnsDens (settingWS (ymix a) w hw) v ρ ↔ PureDens (settingWS (ymix a) w hw) v ρ :=
  ⟨pureDens_of_ensDens fun _ _ hψ hψ1 hφ hφ1 => by
      obtain ⟨c, hc⟩ := gs_unique_WY hψ hφ
      exact dens_eq_of_ae_smul hc hψ1 hφ1,
    ensDens_of_pureDens⟩

end Line

end DFT.Continuum
