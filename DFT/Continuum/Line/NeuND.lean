/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.NeuPos
import DFT.Continuum.Line.Nondeg

/-!
# Nondegeneracy of Neumann ground states of `H⁻¹` potentials

For bosons or fermions, every `H⁻¹` potential and every continuous interaction, the Neumann
ground state is unique up to sign (**`gsNH_unique`**), so its density is unique
(**`rhoE_gsNH_unique`**).

* `isGSNH_comb`: a nonzero combination of ground states, normalised, is a ground state.
* `gsNH_sign_bos`: a bosonic ground state has a strict sign a.e. (combine `Ψ` with `|Ψ|`).
* `gsNH_sign_fer`: a fermionic ground state has a strict sign on the chamber (combine with the
  chamber state).
* Two ground states of the same sign differ by a ground state of strict sign, unless they are
  equal. Since both are normalised, that is impossible.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box Real Filter Topology

variable {n : ℕ} {τ : Stat} {w : Cfg n → ℝ} {v : PotH}

/-! ### Combinations of ground states -/

lemma isGSNH_neg {Φ : Cfg n → ℝ} (h : IsGSNH τ w v Φ) : IsGSNH τ w v ((-1 : ℝ) • Φ) := by
  refine ⟨Submodule.smul_mem _ _ h.1, ?_, fun Ψ hΨ hΨn => ?_⟩
  · simpa [Pi.smul_apply, smul_eq_mul, neg_sq] using h.2.1
  · rw [QNH_smul v h.1]; simpa using h.2.2 Ψ hΨ hΨn

/-- **Combinations of ground states**: if `∫ (Φ + sΨ)² > 0`, the normalised combination is a
ground state. -/
theorem isGSNH_comb (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : IsGSNH τ w v Φ)
    (hΨ : IsGSNH τ w v Ψ) (s : ℝ) (hpos : 0 < ∫ x, (Φ + s • Ψ) x ^ 2 ∂μN n) :
    IsGSNH τ w v ((1 / √(∫ x, (Φ + s • Ψ) x ^ 2 ∂μN n)) • (Φ + s • Ψ)) := by
  set I := ∫ x, (Φ + s • Ψ) x ^ 2 ∂μN n
  set c := 1 / √I
  have hc2 : c ^ 2 = 1 / I := by rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
  have hE : QNH τ w v Φ = QNH τ w v Ψ :=
    le_antisymm (hΦ.2.2 Ψ hΨ.1 hΨ.2.1) (hΨ.2.2 Φ hΦ.1 hΦ.2.1)
  have hel := euler_lagrangeNH hw hΦ hΨ.1
  have hQ := QNH_expand hw v hΦ.1 hΨ.1 s
  have hsq : I = 1 + 2 * s * ∫ x, Φ x * Ψ x ∂μN n + s ^ 2 := by
    have := integral_expand (μ := μN n) (g := fun _ => (1 : ℝ)) (ψ := Φ) (φ := Ψ)
      (by simpa using int_mul_L2 hΦ.1.1 hΦ.1.1) (by simpa using int_mul_L2 hΦ.1.1 hΨ.1.1)
      (by simpa using int_mul_L2 hΨ.1.1 hΨ.1.1) s
    simp only [one_mul] at this
    have h1 : ∫ x, Φ x * Φ x ∂μN n = 1 := by rw [← hΦ.2.1]; simp only [sq]
    have h2 : ∫ x, Ψ x * Ψ x ∂μN n = 1 := by rw [← hΨ.2.1]; simp only [sq]
    simp only [I, sq]; rw [this, h1, h2]; ring
  have hQχ : QNH τ w v (Φ + s • Ψ) = QNH τ w v Φ * I := by
    rw [hQ, hel, ← hE, hsq]; ring
  have hD : Φ + s • Ψ ∈ DomN τ n := add_mem hΦ.1 (Submodule.smul_mem _ s hΨ.1)
  refine ⟨Submodule.smul_mem _ c hD, ?_, fun Ξ hΞ hΞn => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, mul_pow, integral_const_mul, hc2]
    exact one_div_mul_cancel hpos.ne'
  · rw [QNH_smul v hD, hQχ, hc2, mul_comm (QNH τ w v Φ) I, ← mul_assoc,
      one_div_mul_cancel hpos.ne', one_mul]
    exact hΦ.2.2 Ξ hΞ hΞn

lemma integral_sq_eq_zero {f : Cfg n → ℝ} (hf : MemLp f 2 (μN n))
    (h : ∫ x, f x ^ 2 ∂μN n = 0) : ∀ᵐ x ∂μN n, f x = 0 := by
  have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) (int_sq hf)).1 h
  filter_upwards [this] with x hx
  exact pow_eq_zero_iff two_ne_zero |>.1 hx

/-- Two normalised states cannot have `Φ² < Ψ²` almost everywhere. -/
lemma not_ae_sq_lt {Φ Ψ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n)) (hΨ : MemLp Ψ 2 (μN n))
    (hn : ∫ x, Φ x ^ 2 ∂μN n = ∫ x, Ψ x ^ 2 ∂μN n) (h : ∀ᵐ x ∂μN n, Φ x ^ 2 < Ψ x ^ 2) :
    False := by
  have hi : Integrable (fun x => Ψ x ^ 2 - Φ x ^ 2) (μN n) := (int_sq hΨ).sub (int_sq hΦ)
  have h0 : ∫ x, (Ψ x ^ 2 - Φ x ^ 2) ∂μN n = 0 := by
    rw [integral_sub (int_sq hΨ) (int_sq hΦ), hn, sub_self]
  have hz := (integral_eq_zero_iff_of_nonneg_ae (h.mono fun x hx => show (0 : ℝ) ≤ Ψ x ^ 2 - Φ x ^ 2 from
    (sub_pos.2 hx).le) hi).1 h0
  have : ∀ᵐ x ∂μN n, False := by
    filter_upwards [hz, h] with x h1 h2
    have : Ψ x ^ 2 - Φ x ^ 2 = 0 := h1
    linarith
  exact measure_cube_ne_zero (n := n) (by simpa using ae_iff.1 this)

/-! ### Bosons -/

/-- **A bosonic ground state has a strict sign almost everywhere.** -/
theorem gsNH_sign_bos (hw : Continuous w) {Ψ : Cfg n → ℝ} (hΨ : IsGSNH .bos w v Ψ) :
    (∀ᵐ x ∂μN n, 0 < Ψ x) ∨ (∀ᵐ x ∂μN n, Ψ x < 0) := by
  have hP := isGSNH_abs hΨ
  have hucp := gsNH_ne_zero_bos hw hΨ
  set P : Cfg n → ℝ := fun x => |Ψ x|
  have hD : P + (1 : ℝ) • Ψ ∈ DomN .bos n := add_mem hP.1 (Submodule.smul_mem _ _ hΨ.1)
  rcases (integral_nonneg (μ := μN n) (f := fun x => (P + (1 : ℝ) • Ψ) x ^ 2)
    fun x => sq_nonneg _).lt_or_eq with hpos | h0
  · left
    have hG := isGSNH_comb hw hP hΨ 1 hpos
    filter_upwards [gsNH_ne_zero_bos hw hG] with x hx
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_mul, P] at hx
    by_contra hc
    push Not at hc
    exact hx (by rw [abs_of_nonpos hc]; ring)
  · right
    filter_upwards [integral_sq_eq_zero hD.1 h0.symm, hucp] with x hx hne
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_mul, P] at hx
    rcases lt_or_gt_of_ne hne with h | h
    · exact h
    · rw [abs_of_pos h] at hx; linarith

/-- Two positive bosonic ground states coincide. -/
lemma gsNH_eq_of_pos_bos (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : IsGSNH .bos w v Φ)
    (hΨ : IsGSNH .bos w v Ψ) (hΦp : ∀ᵐ x ∂μN n, 0 < Φ x) (hΨp : ∀ᵐ x ∂μN n, 0 < Ψ x) :
    Ψ =ᵐ[μN n] Φ := by
  have hD : Φ + (-1 : ℝ) • Ψ ∈ DomN .bos n := add_mem hΦ.1 (Submodule.smul_mem _ _ hΨ.1)
  rcases (integral_nonneg (μ := μN n) (f := fun x => (Φ + (-1 : ℝ) • Ψ) x ^ 2)
    fun x => sq_nonneg _).lt_or_eq with hpos | h0
  · exfalso
    have hG := isGSNH_comb hw hΦ hΨ (-1) hpos
    have hc : 0 < 1 / √(∫ x, (Φ + (-1 : ℝ) • Ψ) x ^ 2 ∂μN n) := by positivity
    have hn : ∫ x, Φ x ^ 2 ∂μN n = ∫ x, Ψ x ^ 2 ∂μN n := by rw [hΦ.2.1, hΨ.2.1]
    rcases gsNH_sign_bos hw hG with h | h
    · refine not_ae_sq_lt hΨ.1.1 hΦ.1.1 hn.symm ?_
      filter_upwards [h, hΦp, hΨp] with x h1 h2 h3
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h1
      have h1' := pos_of_mul_pos_right h1 hc.le
      have : 0 < Φ x - Ψ x := by linarith
      nlinarith
    · refine not_ae_sq_lt hΦ.1.1 hΨ.1.1 hn ?_
      filter_upwards [h, hΦp, hΨp] with x h1 h2 h3
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h1
      have h1' := neg_of_mul_neg_right h1 hc.le
      have : Φ x - Ψ x < 0 := by linarith
      nlinarith
  · filter_upwards [integral_sq_eq_zero hD.1 h0.symm] with x hx
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hx
    linarith

/-! ### Fermions -/

lemma PhiBY_eq_abs_RY (Ψ : Cfg n → ℝ) :
    ∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → PhiBY (n + 1) Ψ x = |Ψ x| := by
  filter_upwards [ae_cube, ae_injective] with x hx hinj hxR
  have h1 : pm 1 x ∈ RY (n + 1) n := by rw [pm_one]; exact hxR
  rw [(sorted_Y (Ψ := Ψ) hx hinj (YG_one (n + 1)) h1 0).2.2.1, pm_one]
  simp only [uY, indicator_of_mem hxR]

/-- **A fermionic ground state has a strict sign on the chamber.** -/
theorem gsNH_sign_fer (hw : Continuous w) {Ψ : Cfg n → ℝ} (hΨ : IsGSNH .fer w v Ψ) :
    (∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → 0 < Ψ x) ∨
      (∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → Ψ x < 0) := by
  have hP := isGSNH_PhiY hΨ
  have hucp := gsNH_ne_zero_fer hw hΨ
  set P := PhiY (n + 1) Ψ
  have hD : P + (1 : ℝ) • Ψ ∈ DomN .fer n := add_mem hP.1 (Submodule.smul_mem _ _ hΨ.1)
  rcases (integral_nonneg (μ := μN n) (f := fun x => (P + (1 : ℝ) • Ψ) x ^ 2)
    fun x => sq_nonneg _).lt_or_eq with hpos | h0
  · left
    have hG := isGSNH_comb hw hP hΨ 1 hpos
    filter_upwards [gsNH_ne_zero_fer hw hG, PhiY_eq_abs_RY (a := n + 1) Ψ] with x hx hR hxR
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_mul, P, hR hxR] at hx
    by_contra hc
    push Not at hc
    exact hx (by rw [abs_of_nonpos hc]; ring)
  · right
    filter_upwards [integral_sq_eq_zero hD.1 h0.symm, hucp, PhiY_eq_abs_RY (a := n + 1) Ψ]
      with x hx hne hR hxR
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_mul, P, hR hxR] at hx
    rcases lt_or_gt_of_ne hne with h | h
    · exact h
    · rw [abs_of_pos h] at hx; linarith

/-- On the chamber, `Φ² < Ψ²` propagates to the whole cube. -/
lemma ae_sq_lt_of_RY {Φ Ψ : Cfg n → ℝ} (hΦ : Φ ∈ DomN .fer n) (hΨ : Ψ ∈ DomN .fer n)
    (h : ∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → |Φ x| < |Ψ x|) : ∀ᵐ x ∂μN n, Φ x ^ 2 < Ψ x ^ 2 := by
  have hR : ∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → PhiBY (n + 1) Φ x < PhiBY (n + 1) Ψ x := by
    filter_upwards [h, PhiBY_eq_abs_RY Φ, PhiBY_eq_abs_RY Ψ] with x h1 h2 h3 hx
    rw [h2 hx, h3 hx]; exact h1 hx
  have hR' : ∀ᵐ x ∂volume.restrict (RY (n + 1) n), PhiBY (n + 1) Φ x < PhiBY (n + 1) Ψ x := by
    refine (ae_restrict_iff' measurableSet_RY).2 ?_
    have := (ae_restrict_iff' measurableSet_cube).1 hR
    filter_upwards [this] with x hx hxR using hx hxR.1 hxR
  have hall := ae_of_ae_RY (a := n + 1) (p := fun x => PhiBY (n + 1) Φ x < PhiBY (n + 1) Ψ x)
    (fun σ hσ x => by simp only [PhiBY_pm _ hσ]) hR'
  filter_upwards [hall, PhiBY_ae_eq_absN hΦ, PhiBY_ae_eq_absN hΨ] with x h1 h2 h3
  rw [h2, h3] at h1
  rw [← sq_abs (Φ x), ← sq_abs (Ψ x)]
  exact pow_lt_pow_left₀ h1 (abs_nonneg _) two_ne_zero

/-- Two fermionic ground states positive on the chamber coincide. -/
lemma gsNH_eq_of_pos_fer (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : IsGSNH .fer w v Φ)
    (hΨ : IsGSNH .fer w v Ψ) (hΦp : ∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → 0 < Φ x)
    (hΨp : ∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → 0 < Ψ x) : Ψ =ᵐ[μN n] Φ := by
  have hD : Φ + (-1 : ℝ) • Ψ ∈ DomN .fer n := add_mem hΦ.1 (Submodule.smul_mem _ _ hΨ.1)
  rcases (integral_nonneg (μ := μN n) (f := fun x => (Φ + (-1 : ℝ) • Ψ) x ^ 2)
    fun x => sq_nonneg _).lt_or_eq with hpos | h0
  · exfalso
    have hG := isGSNH_comb hw hΦ hΨ (-1) hpos
    have hn : ∫ x, Φ x ^ 2 ∂μN n = ∫ x, Ψ x ^ 2 ∂μN n := by rw [hΦ.2.1, hΨ.2.1]
    rcases gsNH_sign_fer hw hG with h | h
    · refine not_ae_sq_lt hΨ.1.1 hΦ.1.1 hn.symm (ae_sq_lt_of_RY hΨ.1 hΦ.1 ?_)
      filter_upwards [h, hΦp, hΨp] with x h1 h2 h3 hx
      have h1 := h1 hx
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h1
      have : 0 < Φ x - Ψ x := by
        have hc : 0 < 1 / √(∫ x, (Φ + (-1 : ℝ) • Ψ) x ^ 2 ∂μN n) := by positivity
        have h1' := pos_of_mul_pos_right h1 hc.le
        linarith
      rw [abs_of_pos (h3 hx), abs_of_pos (h2 hx)]; linarith
    · refine not_ae_sq_lt hΦ.1.1 hΨ.1.1 hn (ae_sq_lt_of_RY hΦ.1 hΨ.1 ?_)
      filter_upwards [h, hΦp, hΨp] with x h1 h2 h3 hx
      have h1 := h1 hx
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h1
      have : Φ x - Ψ x < 0 := by
        have hc : 0 < 1 / √(∫ x, (Φ + (-1 : ℝ) • Ψ) x ^ 2 ∂μN n) := by positivity
        have h1' := neg_of_mul_neg_right h1 hc.le
        linarith
      rw [abs_of_pos (h3 hx), abs_of_pos (h2 hx)]; linarith
  · filter_upwards [integral_sq_eq_zero hD.1 h0.symm] with x hx
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hx
    linarith

/-! ### Uniqueness -/

/-- **Nondegeneracy**: two Neumann ground states of an `H⁻¹` potential agree up to sign. -/
theorem gsNH_unique (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : IsGSNH τ w v Φ)
    (hΨ : IsGSNH τ w v Ψ) : Ψ =ᵐ[μN n] Φ ∨ Ψ =ᵐ[μN n] (-1 : ℝ) • Φ := by
  have hneg : ∀ {f : Cfg n → ℝ}, (-1 : ℝ) • ((-1 : ℝ) • f) = f := fun {f} => by
    rw [smul_smul]; norm_num
  cases τ with
  | bos =>
    have key : ∀ {A B : Cfg n → ℝ}, IsGSNH .bos w v A → IsGSNH .bos w v B →
        (∀ᵐ x ∂μN n, 0 < A x) → (B =ᵐ[μN n] A ∨ B =ᵐ[μN n] (-1 : ℝ) • A) := by
      intro A B hA hB hAp
      rcases gsNH_sign_bos hw hB with h | h
      · exact Or.inl (gsNH_eq_of_pos_bos hw hA hB hAp h)
      · right
        have h' : ∀ᵐ x ∂μN n, 0 < ((-1 : ℝ) • B) x := h.mono fun x hx => by
          simp only [Pi.smul_apply, smul_eq_mul]; linarith
        have := gsNH_eq_of_pos_bos hw hA (isGSNH_neg hB) hAp h'
        filter_upwards [this] with x hx
        simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
        linarith
    rcases gsNH_sign_bos hw hΦ with h | h
    · exact key hΦ hΨ h
    · have h' : ∀ᵐ x ∂μN n, 0 < ((-1 : ℝ) • Φ) x := h.mono fun x hx => by
        simp only [Pi.smul_apply, smul_eq_mul]; linarith
      rcases key (isGSNH_neg hΦ) hΨ h' with h1 | h1
      · exact Or.inr h1
      · left; rwa [hneg] at h1
  | fer =>
    have key : ∀ {A B : Cfg n → ℝ}, IsGSNH .fer w v A → IsGSNH .fer w v B →
        (∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → 0 < A x) →
        (B =ᵐ[μN n] A ∨ B =ᵐ[μN n] (-1 : ℝ) • A) := by
      intro A B hA hB hAp
      rcases gsNH_sign_fer hw hB with h | h
      · exact Or.inl (gsNH_eq_of_pos_fer hw hA hB hAp h)
      · right
        have h' : ∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → 0 < ((-1 : ℝ) • B) x :=
          h.mono fun x hx hxR => by
            simp only [Pi.smul_apply, smul_eq_mul]; linarith [hx hxR]
        have := gsNH_eq_of_pos_fer hw hA (isGSNH_neg hB) hAp h'
        filter_upwards [this] with x hx
        simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
        linarith
    rcases gsNH_sign_fer hw hΦ with h | h
    · exact key hΦ hΨ h
    · have h' : ∀ᵐ x ∂μN n, x ∈ RY (n + 1) n → 0 < ((-1 : ℝ) • Φ) x :=
        h.mono fun x hx hxR => by
          simp only [Pi.smul_apply, smul_eq_mul]; linarith [hx hxR]
      rcases key (isGSNH_neg hΦ) hΨ h' with h1 | h1
      · exact Or.inr h1
      · left; rwa [hneg] at h1

/-- **The ground-state density is unique.** -/
theorem rhoE_gsNH_unique (hw : Continuous w) {Φ Ψ : Cfg n → ℝ} (hΦ : IsGSNH τ w v Φ)
    (hΨ : IsGSNH τ w v Ψ) : rhoE τ Ψ = rhoE τ Φ := by
  have hsq : ∀ᵐ x ∂μN n, Ψ x * Ψ x = Φ x * Φ x := by
    rcases gsNH_unique hw hΦ hΨ with h | h
    · filter_upwards [h] with x hx; rw [hx]
    · filter_upwards [h] with x hx; rw [hx]; simp
  exact eq_of_int fun u => by
    rw [int_rhoE hΨ.1, int_rhoE hΦ.1]
    exact integral_congr_ae (by filter_upwards [hsq] with x hx; rw [hx])

end DFT.Continuum.Line
