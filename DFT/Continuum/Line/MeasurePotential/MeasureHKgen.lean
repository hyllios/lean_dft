/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/
import DFT.Continuum.Line.MeasurePotential.MeasureNGS
import DFT.Continuum.Line.MeasurePotential.MeasureNHKc
import DFT.Continuum.Line.MeasurePotential.MeasurePair

/-!
# Toward the general interacting Hohenberg–Kohn theorem: limits of truncations

Step (D) of the argument in the formalization log.

* `kinW_congr`, `kinW_eq_tsum`: the kinetic energy of an `H¹₀` state is `Σ λ c²`.
* **`tendsto_kinW_sub_trunc`**: the sine truncations converge in `H¹`.
* `kinW_mul_le`: `T(ζ Y) ≤ 2 sup ζ² T(Y) + 2 N sup |∇ζ|² ∫ Y²`.
-/

namespace DFT.Continuum.Line

open MeasureTheory Set Box SturmLiouville Real Filter Topology Sine

variable {n : ℕ} {τ : Stat}

lemma kinW_congr {Φ Ψ : Cfg n → ℝ} (hΦ : H1W Φ) (h : Φ =ᵐ[μN n] Ψ) : kinW Φ = kinW Ψ := by
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  have hd : dW k Ψ =ᵐ[μN n] dW k Φ := dW_ae_eq ((dW_spec (hΦ.2 k)).congr h)
  filter_upwards [hd] with x hx
  rw [hx]

/-- The coefficients of an `H¹₀` state are a `Dir` sequence. -/
lemma dir_cNW {s : SymT n} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomWS s) : Dir s fun m => cN m Φ :=
  ⟨(parsevalW hΦ.1).summable, summable_of_sum_le (fun m => mul_nonneg (lam_nonneg m)
    (sq_nonneg _)) (sum_lam_le (h1W_of_mem hΦ)), fun _ hσ m => cN_pmWS hΦ hσ m⟩

lemma ae_eq_serW {Φ : Cfg n → ℝ} (hΦ : MemLp Φ 2 (μN n))
    (hs : Summable fun m => cN m Φ ^ 2) : Φ =ᵐ[μN n] serW fun m => cN m Φ :=
  ae_eq_of_cN_eq hΦ memLp_serW fun m => (cN_serW hs m).symm

/-- **The kinetic energy in coefficients**: `T(Φ) = Σ λ_m c_m²`. -/
theorem kinW_eq_tsum {s : SymT n} {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomWS s) :
    kinW Φ = ∑' m, lam m * cN m Φ ^ 2 := by
  rw [kinW_congr (h1W_of_mem hΦ) (ae_eq_serW hΦ.1 (dir_cNW hΦ).sq), kinW_serW (dir_cNW hΦ)]

lemma trunc_memW {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) (M : ℕ) : trunc M Φ ∈ DomW τ n :=
  Dom_le_DomW (trunc_mem hΦ M)

/-- **The truncations converge in `H¹`**: `T(Φ - P_M Φ) → 0`. -/
theorem tendsto_kinW_sub_trunc {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) :
    Tendsto (fun M => kinW (Φ - trunc M Φ)) atTop (𝓝 0) := by
  have hD : ∀ M, Φ - trunc M Φ ∈ DomW τ n := fun M => sub_mem hΦ (trunc_memW hΦ M)
  have hc : ∀ M m, cN m (Φ - trunc M Φ) = if m ∈ boxI n M then 0 else cN m Φ := fun M m => by
    rw [cN_sub hΦ.1 (trunc_memW hΦ M).1, cN_trunc]
    split_ifs <;> ring
  have hk := (dir_cNW hΦ).kin
  have e : ∀ M, kinW (Φ - trunc M Φ) =
      ∑' m, lam m * cN m Φ ^ 2 - ∑ m ∈ boxI n M, lam m * cN m Φ ^ 2 := fun M => by
    rw [kinW_eq_tsum (hD M)]
    simp only [hc]
    have hfin : Summable fun m => if m ∈ boxI n M then lam m * cN m Φ ^ 2 else 0 :=
      summable_of_ne_finset_zero (s := boxI n M) fun m hm => by simp [hm]
    have htsum : ∑' m, (if m ∈ boxI n M then lam m * cN m Φ ^ 2 else 0) =
        ∑ m ∈ boxI n M, lam m * cN m Φ ^ 2 := by
      rw [tsum_eq_sum (s := boxI n M) fun m hm => by simp [hm]]
      exact Finset.sum_congr rfl fun m hm => by simp [hm]
    have h1 : (fun m => lam m * (if m ∈ boxI n M then 0 else cN m Φ) ^ 2) =
        fun m => lam m * cN m Φ ^ 2 - if m ∈ boxI n M then lam m * cN m Φ ^ 2 else 0 := by
      funext m; split_ifs <;> simp
    rw [h1, hk.tsum_sub hfin, htsum]
  simp only [e]
  have h := hk.hasSum.comp tendsto_boxI
  have := (tendsto_const_nhds (x := ∑' m, lam m * cN m Φ ^ 2)).sub h
  rwa [sub_self] at this

/-- `∫ (Φ - P_M Φ)² → 0`. -/
theorem tendsto_sq_sub_trunc {Φ : Cfg n → ℝ} (hΦ : Φ ∈ DomW τ n) :
    Tendsto (fun M => ∫ x, (Φ - trunc M Φ) x ^ 2 ∂μN n) atTop (𝓝 0) :=
  tendsto_trunc hΦ.1

/-- **The kinetic energy of a product with a `C¹` function**. -/
theorem kinW_mul_le {Y : Cfg n → ℝ} (hY : H1W Y) {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ) {Z Z' : ℝ}
    (hZ : ∀ x, |ζ x| ≤ Z) (hZ' : ∀ k x, |dk k ζ x| ≤ Z') :
    kinW (fun x => ζ x * Y x) ≤ 2 * Z ^ 2 * kinW Y + 2 * (n + 1) * Z' ^ 2 * ∫ x, Y x ^ 2 ∂μN n := by
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0)
  have hk : ∀ k, ∫ x, dW k (fun x => ζ x * Y x) x * dW k (fun x => ζ x * Y x) x ∂μN n ≤
      2 * Z ^ 2 * ∫ x, dW k Y x * dW k Y x ∂μN n + 2 * Z' ^ 2 * ∫ x, Y x ^ 2 ∂μN n := fun k => by
    have hW := (dW_spec (hY.2 k)).mul_C1 hY.1 hζ
    have hd := dW_ae_eq hW
    have hmG := (dW_spec (hY.2 k)).1
    have i1 : Integrable (fun x => dW k Y x * dW k Y x) (μN n) := int_mul_L2 hmG hmG
    have i2 : Integrable (fun x => Y x ^ 2) (μN n) := int_sq hY.1
    have hdk := continuous_dk_of_C1 hζ k
    have i0 : Integrable (fun x => (ζ x * dW k Y x + dk k ζ x * Y x) *
        (ζ x * dW k Y x + dk k ζ x * Y x)) (μN n) := int_mul_L2 hW.1 hW.1
    rw [integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx]),
      ← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _) (i2.const_mul _)]
    refine integral_mono i0 ((i1.const_mul _).add (i2.const_mul _)) fun x => ?_
    have h1 : (ζ x) ^ 2 ≤ Z ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ x) 2
    have h2 : (dk k ζ x) ^ 2 ≤ Z' ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ' k x) 2
    nlinarith [sq_nonneg (ζ x * dW k Y x - dk k ζ x * Y x), mul_le_mul_of_nonneg_right h1
      (mul_self_nonneg (dW k Y x)), mul_le_mul_of_nonneg_right h2 (sq_nonneg (Y x))]
  calc kinW (fun x => ζ x * Y x)
      ≤ ∑ k : Fin (n + 1), (2 * Z ^ 2 * ∫ x, dW k Y x * dW k Y x ∂μN n +
          2 * Z' ^ 2 * ∫ x, Y x ^ 2 ∂μN n) := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, kinW]
        push_cast; ring

/-! ### Bilinearity of the mixed density -/

lemma int_ext_sub (v p q : C01) :
    ∫ t, iccExt v t * iccExt (p - q) t ∂vol01 = ∫ t, iccExt v t * iccExt p t ∂vol01 - ∫ t, iccExt v t * iccExt q t ∂vol01 := by
  have := int_ext_add_smul v p q 1 (-1)
  simp only [one_smul, neg_smul, one_mul, neg_one_mul, ← sub_eq_add_neg] at this
  linarith

section bilin

variable {w : Cfg n → ℝ} (hw : Continuous w)
include hw

lemma pf_sub_left {A A' B : Cfg n → ℝ} (hA : A ∈ DomW τ n) (hA' : A' ∈ DomW τ n)
    (hB : B ∈ DomW τ n) (v : C01) :
    pf (settingW τ n w hw) v (A - A') B = pf (settingW τ n w hw) v A B -
      pf (settingW τ n w hw) v A' B := by
  simp only [pf]
  rw [← integral_sub ((settingW τ n w hw).int_L v A B hA hB)
    ((settingW τ n w hw).int_L v A' B hA' hB)]
  congr 1; funext x; simp only [Pi.sub_apply]; ring

lemma rhoHat2_sub_left {A A' B : Cfg n → ℝ} (hA : A ∈ DomW τ n) (hA' : A' ∈ DomW τ n)
    (hB : B ∈ DomW τ n) : rhoHat2 τ (A - A') B = rhoHat2 τ A B - rhoHat2 τ A' B :=
  pot_eq_of_integral fun v => by
    rw [int_ext_sub, int_rhoHat2 hw (sub_mem hA hA') hB, int_rhoHat2 hw hA hB,
      int_rhoHat2 hw hA' hB, pf_sub_left hw hA hA' hB]

lemma rhoHat2_sub_right {A B B' : Cfg n → ℝ} (hA : A ∈ DomW τ n) (hB : B ∈ DomW τ n)
    (hB' : B' ∈ DomW τ n) : rhoHat2 τ A (B - B') = rhoHat2 τ A B - rhoHat2 τ A B' :=
  pot_eq_of_integral fun v => by
    rw [int_ext_sub, int_rhoHat2 hw hA (sub_mem hB hB'), int_rhoHat2 hw hA hB,
      int_rhoHat2 hw hA hB']
    simp only [pf]
    rw [← integral_sub ((settingW τ n w hw).int_L v A B hA hB)
      ((settingW τ n w hw).int_L v A B' hA hB')]
    congr 1; funext x; simp only [Pi.sub_apply]; ring

lemma rhoHat_sub {A A' : Cfg n → ℝ} (hA : A ∈ DomW τ n) (hA' : A' ∈ DomW τ n) :
    rhoHat τ A - rhoHat τ A' = rhoHat2 τ (A - A') (A + A') :=
  pot_eq_of_integral fun v => by
    rw [int_ext_sub, int_rhoHat hw hA, int_rhoHat hw hA', int_rhoHat2 hw (sub_mem hA hA')
      (add_mem hA hA')]
    simp only [pf]
    rw [← integral_sub ((settingW τ n w hw).int_L v A A hA hA)
      ((settingW τ n w hw).int_L v A' A' hA' hA')]
    congr 1; funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring

end bilin

/-! ### The `H¹` size and its properties -/

/-- `S(X) = N ∫ X² + T(X)`. -/
noncomputable def SH (X : Cfg n → ℝ) : ℝ := (n + 1) * ∫ x, X x ^ 2 ∂μN n + kinW X

lemma SH_nonneg (X : Cfg n → ℝ) : 0 ≤ SH X := by
  have := kinW_nonneg X
  have : 0 ≤ ∫ x, X x ^ 2 ∂μN n := integral_nonneg fun _ => sq_nonneg _
  unfold SH; positivity

lemma abs_rhoHat2_le_SH {w : Cfg n → ℝ} (hw : Continuous w) {A B : Cfg n → ℝ}
    (hA : A ∈ DomW τ n) (hB : B ∈ DomW τ n) (t : Icc (0 : ℝ) 1) :
    |rhoHat2 τ A B t| ≤ √(SH A * SH B) := by
  have := abs_rhoHat2_le_H1 hw hA hB one_pos t
  simpa [SH, one_mul, div_one] using this

lemma kinW_add_le {X Y : Cfg n → ℝ} (hX : H1W X) (hY : H1W Y) :
    kinW (X + Y) ≤ 2 * kinW X + 2 * kinW Y := by
  simp only [kinW, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have hd := dW_add_H hX hY k
  have hmX := memLp_dW_H hX k
  have hmY := memLp_dW_H hY k
  rw [integral_congr_ae (by filter_upwards [hd] with x hx; rw [hx]), ← integral_const_mul,
    ← integral_const_mul, ← integral_add ((int_mul_L2 hmX hmX).const_mul 2)
    ((int_mul_L2 hmY hmY).const_mul 2)]
  refine integral_mono (int_mul_L2 (hmX.add hmY) (hmX.add hmY))
    (((int_mul_L2 hmX hmX).const_mul 2).add ((int_mul_L2 hmY hmY).const_mul 2)) fun x => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (dW k X x - dW k Y x)]

lemma SH_add_le {X Y : Cfg n → ℝ} (hX : H1W X) (hY : H1W Y) :
    SH (X + Y) ≤ 2 * SH X + 2 * SH Y := by
  have hk := kinW_add_le hX hY
  have h2 : ∫ x, (X + Y) x ^ 2 ∂μN n ≤ 2 * ∫ x, X x ^ 2 ∂μN n + 2 * ∫ x, Y x ^ 2 ∂μN n := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((int_sq hX.1).const_mul 2) ((int_sq hY.1).const_mul 2)]
    refine integral_mono (int_sq (hX.1.add hY.1)) (((int_sq hX.1).const_mul 2).add
      ((int_sq hY.1).const_mul 2)) fun x => ?_
    simp only [Pi.add_apply]; nlinarith [sq_nonneg (X x - Y x)]
  unfold SH
  nlinarith [show (0 : ℝ) ≤ n + 1 by positivity]

lemma SH_neg {X : Cfg n → ℝ} (hX : H1W X) : SH (-X) = SH X := by
  have hk : kinW (-X) = kinW X := by
    have := kinW_congr (Φ := (-1 : ℝ) • X) (Ψ := -X) ⟨hX.1.const_smul _, fun k =>
      ⟨_, (dW_spec (hX.2 k)).const_mul (-1)⟩⟩ (ae_of_all _ fun x => by simp)
    rw [← this]
    simp only [kinW]
    refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
    filter_upwards [dW_smul_H hX (-1) k] with x hx
    rw [hx]; simp
  simp only [SH, hk, Pi.neg_apply, neg_sq]

lemma SH_mul_le {Y : Cfg n → ℝ} (hY : H1W Y) {ζ : Cfg n → ℝ} (hζ : ContDiff ℝ 1 ζ) {Z Z' : ℝ}
    (hZ : ∀ x, |ζ x| ≤ Z) (hZ' : ∀ k x, |dk k ζ x| ≤ Z') :
    SH (fun x => ζ x * Y x) ≤ (2 * Z ^ 2 + 2 * Z' ^ 2 + Z ^ 2) * SH Y := by
  have hk := kinW_mul_le hY hζ hZ hZ'
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0)
  have h2 : ∫ x, (ζ x * Y x) ^ 2 ∂μN n ≤ Z ^ 2 * ∫ x, Y x ^ 2 ∂μN n := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
      ((int_sq hY.1).const_mul _) (ae_of_all _ fun x => ?_)
    have hz : ζ x ^ 2 ≤ Z ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ x) 2
    change (ζ x * Y x) ^ 2 ≤ Z ^ 2 * Y x ^ 2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hz (sq_nonneg _)
  have hK := kinW_nonneg Y
  have hI : 0 ≤ ∫ x, Y x ^ 2 ∂μN n := integral_nonneg fun _ => sq_nonneg _
  have hN : (0 : ℝ) ≤ n + 1 := by positivity
  unfold SH
  nlinarith [sq_nonneg Z', mul_nonneg hN hI, mul_nonneg (sq_nonneg Z') (mul_nonneg hN hI)]

/-! ### The pair-density operator of an `H¹₀` state, and its continuity -/

lemma dk_FF {f : ℝ → ℝ} (hf : Differentiable ℝ f) (k : Fin (n + 1)) (x : Cfg n) :
    dk k (FF f) x = deriv f (x k) := by
  have h : HasFDerivAt (FF (n := n) f)
      (∑ j : Fin (n + 1), deriv f (x j) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (n + 1) => ℝ) j) x := by
    have hj : ∀ j : Fin (n + 1), HasFDerivAt (fun y : Cfg n => f (y j))
        (deriv f (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j) x :=
      fun j => (hf (x j)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply j x)
    have := HasFDerivAt.sum (u := Finset.univ) fun j _ => hj j
    convert this using 1
    funext y; simp [FF]
  rw [dk, h.fderiv]
  simp [Pi.single_apply]

variable {w : Cfg n → ℝ}

/-- The pair-density operator `T_Y f = ρ̂(Y, F_f Y) - f ρ̂_Y`. -/
noncomputable def TG (τ : Stat) (Y : Cfg n → ℝ) {f : ℝ → ℝ} (hf : Continuous f) : C01 :=
  rhoHat2 τ Y (fun x => FF f x * Y x) - fP hf * rhoHat τ Y

/-- **`T` is continuous in `H¹`**: `‖T_A f - T_B f‖ ≤ √(S(A-B) S(FA)) + √(S(B) S(F(A-B)))
+ sup|f| √(S(A-B) S(A+B))`. -/
theorem norm_TG_sub_le (hw : Continuous w) {A B : Cfg n → ℝ} (hA : A ∈ DomW τ n)
    (hB : B ∈ DomW τ n) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {Cf : ℝ} (hCf : ∀ t, |f t| ≤ Cf) :
    ‖TG τ A hf.continuous - TG τ B hf.continuous‖ ≤
      √(SH (A - B) * SH (fun x => FF f x * A x)) +
        √(SH B * SH (fun x => FF f x * (A - B) x)) + Cf * √(SH (A - B) * SH (A + B)) := by
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hAB := sub_mem hA hB
  have hFA := mem_FF_mul hA hf
  have hFB := mem_FF_mul hB hf
  have hFAB := mem_FF_mul hAB hf
  have e1 : (fun x => FF f x * A x) - (fun x => FF f x * B x) =
      fun x => FF f x * (A - B) x := by funext x; simp only [Pi.sub_apply]; ring
  have e : TG τ A hf.continuous - TG τ B hf.continuous =
      rhoHat2 τ (A - B) (fun x => FF f x * A x) +
        rhoHat2 τ B (fun x => FF f x * (A - B) x) -
          fP hf.continuous * rhoHat2 τ (A - B) (A + B) := by
    simp only [TG]
    rw [← rhoHat_sub hw hA hB, ← e1, rhoHat2_sub_right hw hB hFA hFB,
      rhoHat2_sub_left hw hA hB hFA]
    ring
  rw [e]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    Real.norm_eq_abs]
  have h1 := abs_rhoHat2_le_SH hw hAB hFA t
  have h2 := abs_rhoHat2_le_SH hw hB hFAB t
  have h3 := abs_rhoHat2_le_SH hw hAB (add_mem hA hB) t
  have hft : |fP hf.continuous t| ≤ Cf := by simpa [fP] using hCf t
  calc _ ≤ |rhoHat2 τ (A - B) (fun x => FF f x * A x) t| +
        |rhoHat2 τ B (fun x => FF f x * (A - B) x) t| +
          |fP hf.continuous t| * |rhoHat2 τ (A - B) (A + B) t| := by
        rw [← abs_mul]
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by gcongr

/-! ### Helpers for the limit of the truncations -/

/-- If `K ≤ ε A + B / ε` for all `ε > 0` (`A, B ≥ 0`), then `K ≤ 2 √(A B)`. -/
lemma le_two_sqrt_of_forall {K A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ ε > 0, K ≤ ε * A + B / ε) : K ≤ 2 * √(A * B) := by
  rcases hA.eq_or_lt with hA0 | hApos
  · -- `A = 0`: `K ≤ B / ε` for all `ε`
    rw [← hA0, zero_mul, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have := h ((B + 1) / δ) (by positivity)
    rw [← hA0, mul_zero, zero_add, div_div_eq_mul_div] at this
    have hlt : B * δ / (B + 1) < δ := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  rcases hB.eq_or_lt with hB0 | hBpos
  · rw [← hB0, mul_zero, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have := h (δ / (A + 1)) (by positivity)
    rw [← hB0, zero_div, add_zero] at this
    have hlt : δ / (A + 1) * A < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  · set ε := √(B / A)
    have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
    have h1 := h ε hε
    have e1 : ε * A = √(A * B) := by
      simp only [ε]
      rw [← Real.sqrt_sq hApos.le, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hApos.le]
      congr 1; field_simp
    have e2 : B / ε = √(A * B) := by
      rw [div_eq_iff hε.ne', ← e1]
      simp only [ε]
      rw [mul_comm (√(B / A)) A, mul_assoc, Real.mul_self_sqrt (by positivity)]
      field_simp
    linarith

/-- **Cauchy–Schwarz on the cube of the other particles.** -/
lemma integral_abs_mul_le {a b : (Fin n → ℝ) → ℝ} (ha : Continuous a) (hb : Continuous b) :
    ∫ y in Cube' n, |a y * b y| ≤ √((∫ y in Cube' n, a y ^ 2) * ∫ y in Cube' n, b y ^ 2) := by
  have hA : 0 ≤ ∫ y in Cube' n, a y ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ ∫ y in Cube' n, b y ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have := le_two_sqrt_of_forall (K := 2 * ∫ y in Cube' n, |a y * b y|) hA hB fun ε hε => by
    have i1 : IntegrableOn (fun y => |a y * b y|) (Cube' n) := integrableOn_cube' (by fun_prop)
    have i2 : IntegrableOn (fun y => a y ^ 2) (Cube' n) := integrableOn_cube' (by fun_prop)
    have i3 : IntegrableOn (fun y => b y ^ 2) (Cube' n) := integrableOn_cube' (by fun_prop)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_div,
      ← integral_add (i2.const_mul ε) (i3.div_const ε)]
    refine integral_mono (i1.const_mul 2) ((i2.const_mul ε).add (i3.div_const ε)) fun y => ?_
    have h := sq_nonneg (ε * |a y| - |b y|)
    rw [abs_mul]
    have e : ε * a y ^ 2 + b y ^ 2 / ε - 2 * (|a y| * |b y|) =
        (ε * |a y| - |b y|) ^ 2 / ε := by
      field_simp; rw [← sq_abs (a y), ← sq_abs (b y)]; ring
    have : 0 ≤ (ε * |a y| - |b y|) ^ 2 / ε := by positivity
    linarith
  linarith

lemma abs_smd_le {d : ℕ} (m : Fin d → ℕ) (x : Fin d → ℝ) : |smd m x| ≤ √2 ^ d := by
  rw [smd, Finset.abs_prod]
  calc ∏ j, |sn (m j + 1) (x j)| ≤ ∏ _j : Fin d, √2 :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => by
          rw [sn, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
          exact mul_le_of_le_one_right (Real.sqrt_nonneg 2) (abs_sin_le_one _)
    _ = √2 ^ d := by simp

lemma abs_trunc_le (M : ℕ) (Φ : Cfg n → ℝ) :
    ∃ C, ∀ x, |trunc M Φ x| ≤ C :=
  ⟨∑ m ∈ boxI n M, |cN m Φ| * √2 ^ (n + 1), fun x => by
    rw [trunc]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_smd_le m x) (abs_nonneg _)⟩

lemma Dom_sq_pm {X : Cfg n → ℝ} (hX : X ∈ Dom τ n) (σ : Equiv.Perm (Fin (n + 1))) (x : Cfg n) :
    X (pm σ x) ^ 2 = X x ^ 2 := by
  rw [hX.2.1 σ x, mul_pow, sq (ch τ σ), ch_mul_self, one_mul]

/-! ### The pair density of an `H¹₀` state against a measure is absolutely continuous -/

section absc

variable {m : ℕ} {w : Cfg (m + 1) → ℝ}

lemma integrable_rX (ρ : Measure ℝ) [IsMeas01 ρ] {X : Cfg (m + 1) → ℝ} (hX : Continuous X)
    {CX : ℝ} (hCX : ∀ x, |X x| ≤ CX) : Integrable (rX ρ X) vol01 := by
  have hF : ∀ j : Fin (m + 1), Integrable (fun p : ℝ × ℝ => hP X j p.1 p.2) (ρ.prod vol01) :=
    fun j => integrable_bdd_cont (C := CX ^ 2) (continuous_hP hX j) fun p => abs_hP_le hCX j _ _
  exact (integrable_finsetSum _ fun j _ => (hF j).integral_prod_right).const_mul _

/-- `∫ |X² - X'²|(t, y) dy ≤ √(S(X - X') S(X + X')) / N` for continuous states. -/
lemma integral_abs_sq_sub_le_SH (hw : Continuous w) {X X' : Cfg (m + 1) → ℝ}
    (hX : X ∈ Dom τ (m + 1)) (hX' : X' ∈ Dom τ (m + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ y in Cube' (m + 1), |X (Fin.cons t y) ^ 2 - X' (Fin.cons t y) ^ 2| ≤
      √(SH (X - X') * SH (X + X')) / ((m + 1 : ℕ) + 1) := by
  have hN : (0 : ℝ) < (m + 1 : ℕ) + 1 := by positivity
  have hd : X - X' ∈ Dom τ (m + 1) := sub_mem hX hX'
  have hs : X + X' ∈ Dom τ (m + 1) := add_mem hX hX'
  have hXc := hX.1.continuous
  have hX'c := hX'.1.continuous
  have e : ∀ y : Fin (m + 1) → ℝ, |X (Fin.cons t y) ^ 2 - X' (Fin.cons t y) ^ 2| =
      |(X - X') (Fin.cons t y) * (X + X') (Fin.cons t y)| := fun y => by
    simp only [Pi.sub_apply, Pi.add_apply]; ring_nf
  simp only [e]
  refine (integral_abs_mul_le (a := fun y => (X - X') (Fin.cons t y))
    (b := fun y => (X + X') (Fin.cons t y)) (by fun_prop) (by fun_prop)).trans ?_
  have hm : ∀ {Y : Cfg (m + 1) → ℝ}, Y ∈ Dom τ (m + 1) →
      ∫ y in Cube' (m + 1), Y (Fin.cons t y) ^ 2 ≤ SH Y / ((m + 1 : ℕ) + 1) := fun {Y} hY => by
    have h1 := rhoHat_eq_marg hw (Dom_le_DomW hY) hY.1.continuous (Dom_sq_pm hY) ⟨t, ht⟩
    have h2 := rhoHat_le (Dom_le_DomW hY) one_pos ⟨t, ht⟩
    rw [le_div_iff₀ hN]
    simp only [SH, one_mul, div_one] at h2 ⊢
    push_cast at h1 h2 ⊢
    linarith
  have hA := hm hd
  have hB := hm hs
  have h0A : 0 ≤ ∫ y in Cube' (m + 1), (fun y => (X - X') (Fin.cons t y)) y ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have h0B : 0 ≤ ∫ y in Cube' (m + 1), (fun y => (X + X') (Fin.cons t y)) y ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  calc √((∫ y in Cube' (m + 1), (fun y => (X - X') (Fin.cons t y)) y ^ 2) *
        ∫ y in Cube' (m + 1), (fun y => (X + X') (Fin.cons t y)) y ^ 2)
      ≤ √(SH (X - X') / ((m + 1 : ℕ) + 1) * (SH (X + X') / ((m + 1 : ℕ) + 1))) :=
        Real.sqrt_le_sqrt (mul_le_mul hA hB h0B (h0A.trans hA))
    _ = √(SH (X - X') * SH (X + X')) / ((m + 1 : ℕ) + 1) := by
        rw [div_mul_div_comm, Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hN.le]

lemma abs_FF_le {f : ℝ → ℝ} {Cf : ℝ} (hCf : ∀ t, |f t| ≤ Cf) (x : Cfg (m + 1)) :
    |FF f x| ≤ ((m + 1 : ℕ) + 1) * Cf := by
  rw [FF]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |f (x k)| ≤ ∑ _k : Fin (m + 1 + 1), Cf := Finset.sum_le_sum fun k _ => hCf _
    _ = _ := by simp

/-- The `L¹` distance between `L¹` classes of integrable functions. -/
lemma dist_toL1 {F G : ℝ → ℝ} (hF : Integrable F vol01) (hG : Integrable G vol01) :
    dist (hF.toL1 F) (hG.toL1 G) = ∫ u, |F u - G u| ∂vol01 := by
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hF.toL1 F) (hG.toL1 G), hF.coeFn_toL1, hG.coeFn_toL1]
    with u h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]

/-- **The pair density of an `H¹₀` state against a finite measure is absolutely continuous**:
there is `R ∈ L¹` with `∫ T_Φ f dρ = ∫ f R` for every bounded `C¹` function `f` with bounded
derivative. -/
theorem exists_pair_density (hw : Continuous w) {Φ : Cfg (m + 1) → ℝ}
    (hΦ : Φ ∈ DomW τ (m + 1)) (ρ : Measure ℝ) [IsMeas01 ρ] :
    ∃ R : ℝ → ℝ, Integrable R vol01 ∧ ∀ (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (Cf Cd : ℝ),
      (∀ t, |f t| ≤ Cf) → (∀ t, |deriv f t| ≤ Cd) →
        intCLM ρ (TG τ Φ hf.continuous) = ∫ u, f u * R u ∂vol01 := by
  set N : ℝ := (m + 1 : ℕ) + 1
  have hN : 0 < N := by positivity
  set P : ℕ → Cfg (m + 1) → ℝ := fun M => trunc M Φ
  have hPD : ∀ M, P M ∈ Dom τ (m + 1) := fun M => trunc_mem hΦ M
  have hPW : ∀ M, P M ∈ DomW τ (m + 1) := fun M => Dom_le_DomW (hPD M)
  have hH : ∀ {Y}, Y ∈ DomW τ (m + 1) → H1W Y := fun hY => h1W_of_mem hY
  set sM : ℕ → ℝ := fun M => SH (Φ - P M)
  have hs : Tendsto sM atTop (𝓝 0) := by
    have h1 := (tendsto_sq_sub_trunc hΦ).const_mul ((m + 1 : ℕ) + 1 : ℝ)
    have h2 := tendsto_kinW_sub_trunc hΦ
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr fun M => ?_
    simp only [sM, SH, P]
  have hs0 : ∀ M, 0 ≤ sM M := fun M => SH_nonneg _
  obtain ⟨Sinf, hSinf⟩ := hs.bddAbove_range
  have hSb : ∀ M, sM M ≤ Sinf := fun M => hSinf ⟨M, rfl⟩
  have hΦH := hH hΦ
  have hSP : ∀ M, SH (P M) ≤ 2 * SH Φ + 2 * sM M := fun M => by
    have e : P M = Φ + -(Φ - P M) := by abel
    rw [e]
    have := SH_add_le hΦH (hH (neg_mem (sub_mem hΦ (hPW M))))
    rwa [SH_neg (hH (sub_mem hΦ (hPW M)))] at this
  have hSdiff : ∀ M M', SH (P M - P M') ≤ 2 * sM M' + 2 * sM M := fun M M' => by
    have e : P M - P M' = (Φ - P M') + -(Φ - P M) := by abel
    rw [e]
    have := SH_add_le (hH (sub_mem hΦ (hPW M'))) (hH (neg_mem (sub_mem hΦ (hPW M))))
    rwa [SH_neg (hH (sub_mem hΦ (hPW M)))] at this
  set B2 := 8 * SH Φ + 8 * Sinf
  have hSsum : ∀ M M', SH (P M + P M') ≤ B2 := fun M M' => by
    have := SH_add_le (hH (hPW M)) (hH (hPW M'))
    have := hSP M; have := hSP M'; have := hSb M; have := hSb M'
    simp only [B2]; linarith
  have hB2 : 0 ≤ B2 := (SH_nonneg _).trans (hSsum 0 0)
  -- the densities of the truncations
  choose CP hCP using fun M => abs_trunc_le (n := m + 1) M Φ
  have hPc : ∀ M, Continuous (P M) := fun M => continuous_trunc M Φ
  set r : ℕ → ℝ → ℝ := fun M => rX ρ (P M)
  have hr : ∀ M, Integrable (r M) vol01 := fun M => integrable_rX ρ (hPc M) (hCP M)
  set C0 := N * (m + 1) * ρ.real univ / N
  have hC0 : 0 ≤ C0 := by positivity
  have hdist : ∀ M M', ∫ u, |r M u - r M' u| ∂vol01 ≤ C0 * √(SH (P M - P M') * SH (P M + P M')) :=
    fun M M' => by
      have hC : ∀ x, |P M x| ≤ max (CP M) (CP M') := fun x => (hCP M x).trans (le_max_left _ _)
      have hC' : ∀ x, |P M' x| ≤ max (CP M) (CP M') := fun x =>
        (hCP M' x).trans (le_max_right _ _)
      have := integral_abs_rX_sub_le ρ (hPc M) (hPc M') hC hC'
        (fun t ht => integral_abs_sq_sub_le_SH hw (hPD M) (hPD M') ht)
      refine this.trans (le_of_eq ?_)
      simp only [C0, N]; ring
  -- the `L¹` classes form a Cauchy sequence
  set R1 : ℕ → (ℝ →₁[vol01] ℝ) := fun M => (hr M).toL1 (r M)
  have hcauchy : CauchySeq R1 := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    set η := (ε / (C0 + 1)) ^ 2 / (4 * (B2 + 1))
    have hη : 0 < η := by positivity
    have hηε : C0 * √(4 * η * B2) < ε := by
      have h1 : 4 * η * B2 ≤ (ε / (C0 + 1)) ^ 2 := by
        have : 4 * η * (B2 + 1) = (ε / (C0 + 1)) ^ 2 := by simp only [η]; field_simp
        nlinarith
      have h2 : √(4 * η * B2) ≤ ε / (C0 + 1) := by
        calc √(4 * η * B2) ≤ √((ε / (C0 + 1)) ^ 2) := Real.sqrt_le_sqrt h1
          _ = ε / (C0 + 1) := Real.sqrt_sq (by positivity)
      calc C0 * √(4 * η * B2) ≤ C0 * (ε / (C0 + 1)) := mul_le_mul_of_nonneg_left h2 hC0
        _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    obtain ⟨M0, hM0⟩ := Metric.tendsto_atTop.1 hs η hη
    refine ⟨M0, fun M hM => ?_⟩
    rw [dist_toL1]
    have h1 : sM M < η := by
      have := hM0 M hM; rw [Real.dist_eq, sub_zero, abs_of_nonneg (hs0 M)] at this; exact this
    have h2 : sM M0 < η := by
      have := hM0 M0 le_rfl; rw [Real.dist_eq, sub_zero, abs_of_nonneg (hs0 M0)] at this
      exact this
    refine (hdist M M0).trans_lt (lt_of_le_of_lt ?_ hηε)
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC0
    have := hSdiff M M0
    calc SH (P M - P M0) * SH (P M + P M0) ≤ (4 * η) * B2 :=
          mul_le_mul (by linarith) (hSsum M M0) (SH_nonneg _) (by positivity)
      _ = 4 * η * B2 := by ring
  obtain ⟨R', hR'⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hRi : Integrable (R' : ℝ → ℝ) vol01 := L1.integrable_coeFn R'
  have hconv : Tendsto (fun M => ∫ u, |r M u - R' u| ∂vol01) atTop (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.1 hR')
    refine this.congr fun M => ?_
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (R1 M) R', (hr M).coeFn_toL1] with u h1 h2
    rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs]
  refine ⟨R', hRi, fun f hf Cf Cd hCf hCd => ?_⟩
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hfc := hf.continuous
  -- the identity for the truncations
  have hTM : ∀ M, intCLM ρ (TG τ (P M) hfc) = ∫ u, f u * r M u ∂vol01 := fun M => by
    have e : TG τ (P M) hfc = TXP (hPc M) hfc := by
      rw [TG, rhoHat2_FF hw (hPW M) (hPc M) (Dom_sq_pm (hPD M)) hf]; ring
    rw [e]
    exact intCLM_TXP ρ (hPc M) (hCP M) hfc hCf
  -- the left side converges
  set cF := 2 * (N * Cf) ^ 2 + 2 * Cd ^ 2 + (N * Cf) ^ 2
  have hFmul : ∀ {Y}, Y ∈ DomW τ (m + 1) → SH (fun x => FF f x * Y x) ≤ cF * SH Y :=
    fun hY => SH_mul_le (hH hY) (contDiff_FF hf) (fun x => abs_FF_le hCf x)
      (fun k x => by rw [dk_FF (hf.differentiable one_ne_zero)]; exact hCd _)
  have hL : Tendsto (fun M => intCLM ρ (TG τ (P M) hfc)) atTop
      (𝓝 (intCLM ρ (TG τ Φ hfc))) := by
    have hg : Tendsto (fun M => √(sM M * SH (fun x => FF f x * Φ x)) +
        √((2 * SH Φ + 2 * sM M) * (cF * sM M)) +
          Cf * √(sM M * (6 * SH Φ + 4 * sM M))) atTop (𝓝 0) := by
      have a1 : Tendsto (fun M => √(sM M * SH (fun x => FF f x * Φ x))) atTop (𝓝 0) := by
        simpa using (hs.mul_const _).sqrt
      have a2 : Tendsto (fun M => √((2 * SH Φ + 2 * sM M) * (cF * sM M))) atTop (𝓝 0) := by
        simpa using (((tendsto_const_nhds.add (hs.const_mul 2)).mul (hs.const_mul cF))).sqrt
      have a3 : Tendsto (fun M => Cf * √(sM M * (6 * SH Φ + 4 * sM M))) atTop (𝓝 0) := by
        simpa using ((hs.mul (tendsto_const_nhds.add (hs.const_mul 4))).sqrt).const_mul Cf
      simpa using (a1.add a2).add a3
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_)
      (by simpa using hg.const_mul ‖intCLM ρ‖)
    have hlip := (intCLM ρ).le_opNorm (TG τ (P M) hfc - TG τ Φ hfc)
    rw [map_sub] at hlip
    refine hlip.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_sub_rev]
    refine (norm_TG_sub_le hw hΦ (hPW M) hf hCf).trans ?_
    have hD := sub_mem hΦ (hPW M)
    have e1 : SH (P M) ≤ 2 * SH Φ + 2 * sM M := hSP M
    have e2 : SH (fun x => FF f x * (Φ - P M) x) ≤ cF * sM M := hFmul hD
    have e3 : SH (Φ + P M) ≤ 6 * SH Φ + 4 * sM M := by
      have := SH_add_le hΦH (hH (hPW M)); linarith
    refine add_le_add (add_le_add le_rfl ?_) ?_
    · exact Real.sqrt_le_sqrt (mul_le_mul e1 e2 (SH_nonneg _) (by linarith [SH_nonneg Φ, hs0 M]))
    · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left e3 (hs0 M)))
        hCf0
  -- the right side converges
  have hR : Tendsto (fun M => ∫ u, f u * r M u ∂vol01) atTop (𝓝 (∫ u, f u * R' u ∂vol01)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) (by simpa using hconv.const_mul Cf)
    have i1 : Integrable (fun u => f u * r M u) vol01 :=
      (hr M).bdd_mul hfc.aestronglyMeasurable (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs]; exact hCf u)
    have i2 : Integrable (fun u => f u * R' u) vol01 :=
      hRi.bdd_mul hfc.aestronglyMeasurable (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs]; exact hCf u)
    rw [← integral_sub i1 i2, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono (i1.sub i2).norm
      (((hr M).sub hRi).abs.const_mul Cf) fun u => ?_)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (hCf u) (abs_nonneg _)
  exact tendsto_nhds_unique (hL.congr hTM) hR

end absc

end DFT.Continuum.Line
